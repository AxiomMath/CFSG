module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.CxHyp12
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3EngB
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOdd

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup Relation Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Induction.Hyp CFSG.EvenSporadicStandard.Induction.Fi.Eng
  CFSG.QuasithinUnique.Id2519

section Square

variable {H : Type} [Group H] [Finite H]

theorem false_of_square_swap {X Kh J : Subgroup H} {t s : H} (hJ : IsCompIn J X) (hsX : s ∈ X)
    (htX : t ∈ X) (hst : s * s = t) (hJne : J ≠ CFSG.conjugate J t)
    (hKh : Kh = J ⊔ CFSG.conjugate J t) (hs : s ∈ normalizer (Kh : Set H)) : False := by
  have hJt : IsCompIn (CFSG.conjugate J t) X := hJ.map_conj (X.inv_mem htX)
  have hJs : IsCompIn (CFSG.conjugate J s) X := hJ.map_conj (X.inv_mem hsX)
  have hcs : CFSG.conjugate Kh s = Kh :=
    Solomon78.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ hs)
  have hle : CFSG.conjugate J s ≤ J ⊔ CFSG.conjugate J t := by
    rw [← hKh, ← hcs]
    exact Subgroup.map_mono (hKh ▸ le_sup_left)
  have hss : CFSG.conjugate (CFSG.conjugate J s) s = CFSG.conjugate J t := by
    rw [conjugate_conjugate', hst]
  rcases hJs.eq_or_eq_of_le_sup hJ hJt hle with h | h
  · apply hJne
    rw [← hss, h, h]
  · have h1 : CFSG.conjugate (CFSG.conjugate J t) s = CFSG.conjugate J t := by
      rw [← h, hss, h]
    have h2 : CFSG.conjugate (CFSG.conjugate J s) s⁻¹ = J := by
      rw [conjugate_conjugate', mul_inv_cancel, CFSG.QuasithinUnique.BenderBranch.conjugate_one]
    apply hJne
    calc J = CFSG.conjugate (CFSG.conjugate J s) s⁻¹ := h2.symm
      _ = CFSG.conjugate (CFSG.conjugate J t) s⁻¹ := by rw [h]
      _ = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate J t) s) s⁻¹ := by rw [h1]
      _ = CFSG.conjugate (CFSG.conjugate J t) (s * s⁻¹) := by rw [conjugate_conjugate']
      _ = CFSG.conjugate J t := by
        rw [mul_inv_cancel, CFSG.QuasithinUnique.BenderBranch.conjugate_one]

theorem isCompIn_of_square_swap
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hZ : center H = ⊥) {u₀ t s : H}
    (hu₀ : orderOf u₀ = 2) (hB : BTheoremAt u₀) {K₀ : Subgroup H}
    (hKq : CFSG.IsQuasisimple ↥K₀) (hK₀X : K₀ ≤ centralizer ({u₀} : Set H))
    (ht2 : orderOf t = 2) (hst : s * s = t) (hsX : s ∈ centralizer ({u₀} : Set H))
    (htX : t ∈ centralizer ({u₀} : Set H)) (hK₀t : K₀ ≤ centralizer ({t} : Set H))
    (hK₀s : K₀ ≤ centralizer ({s} : Set H))
    (hnt : (K₀.subgroupOf (centralizer ({u₀} : Set H) ⊓ centralizer ({t} : Set H))).Normal)
    (h12 : ∀ M : Subgroup H, IsCompIn M (centralizer ({u₀} : Set H)) → K₀ ≤ M →
      CFSG.conjugate M t = M → M = K₀) :
    IsCompIn K₀ (centralizer ({u₀} : Set H)) := by
  classical
  set X : Subgroup H := centralizer ({u₀} : Set H) with hX
  set Kh : Subgroup H := ⨆ g ∈ oddLayer X, CFSG.conjugate K₀ g with hKh
  have hK₀Kh : K₀ ≤ Kh :=
    le_iSup₂_of_le (f := fun g (_ : g ∈ oddLayer X) => CFSG.conjugate K₀ g) 1 (one_mem _)
      (by rw [CFSG.QuasithinUnique.BenderBranch.conjugate_one])
  have dich : (IsCompIn Kh X ∧ t ∈ normalizer (Kh : Set H)) ∨
      ∃ J, IsCompIn J X ∧ J ≠ CFSG.conjugate J t ∧ Kh = J ⊔ CFSG.conjugate J t := by
    rcases layer_dichotomy_of_quasisimple_Q hkp hZ htX ht2 hu₀ (B := K₀) hK₀X hK₀t hKq hnt with
      ⟨hA, hxn⟩ | ⟨J, hJ, hJne, hJeq, -⟩
    · exact Or.inl ⟨hB _ hA, hxn⟩
    · exact Or.inr ⟨J, hB J hJ, hJne, hJeq⟩
  rcases dich with ⟨hAt, htn⟩ | ⟨J, hJ, hJne, hJeq⟩
  · have hct : CFSG.conjugate Kh t = Kh :=
      Solomon78.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ htn)
    exact h12 Kh hAt hK₀Kh hct ▸ hAt
  · exfalso
    have hsK₀ : s ∈ normalizer (K₀ : Set H) := by
      refine Subgroup.centralizer_le_normalizer (K₀ : Set H) (mem_centralizer_iff.2 fun k hk => ?_)
      exact mem_centralizer_singleton_iff.1 (hK₀s hk)
    have hsn : s ∈ normalizer (Kh : Set H) := mem_normalizer_iSup_oddLayer hsX hsK₀
    exact false_of_square_swap hJ hsX htX hst hJne hJeq hsn

theorem z4_data {K L T : Subgroup H} {s : H} (hdata : Sol78Link5bData K L T s) (hs2 : s ^ 2 ≠ 1) :
    ∃ t s' : H, orderOf t = 2 ∧ s' * s' = t ∧ t ∈ centralizer (L : Set H) ∧
      ∃ m : ℕ, s' = s ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hdata.s_two
    ⟨s ^ 2, Subgroup.pow_mem _ (mem_zpowers s) 2⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hs2 (orderOf_eq_one_iff.1 (by simpa using hk))
  have hr2 : orderOf ((s ^ 2) ^ (orderOf (s ^ 2) / 2)) = 2 :=
    orderOf_pow_orderOf_div (by rw [hk]; positivity) (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hrT : (s ^ 2) ^ (orderOf (s ^ 2) / 2) ∈ T := T.pow_mem hdata.s_sq _
  refine ⟨(s ^ 2) ^ (orderOf (s ^ 2) / 2), s ^ (orderOf (s ^ 2) / 2), hr2, ?_, ?_, _, rfl⟩
  · rw [← pow_two]
    exact pow_right_comm s _ _
  · exact mem_centralizer_iff.2 fun l hl => (mem_centralizer_iff.1 (hdata.L_comp.1 hl) _ hrT).symm

end Square

section Certificates


theorem fiOuterInvolution_of_engine (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) (rf : FiV3RowFacts) (lx : OddLieCompNotSporadic)
    (hfix : Fi24InFixesElem) : FiOuterInvolution := by
  intro lit H _ _ ih N hN hidx hkp hN22 hN23 hN24 hnb _ K L T s hKL hKne hKq hKcq hcov hSol hdata
    hT hnot hKs hs2
  exfalso
  have hKz : center ↥K = ⊥ := pf.mult23 _ hKq hKcq
  have hKsp : IsSporadic ↥K .Fi23 := isSporadic_of_center_eq_bot hKz hKcq
  have hinL : InL L := ⟨T, hT, hdata.T_two, hdata.L_comp⟩
  have hisL : IsLS [.Fi24Prime] ↥L := isLS_iff.2 ⟨.Fi24Prime, List.mem_singleton.2 rfl, hcov⟩
  have hcore := hyp31Core_of_rowFacts pf rf lx lit ih hN hidx hkp hN24
  have hcyc := (hcore.type_max L hinL hisL).2
  obtain ⟨t, s', ht2, hss, htL, m, hsm⟩ := z4_data hdata hs2
  have hKs' : ∀ k ∈ K, k * s' = s' * k := fun k hk => by
    rw [hsm]
    exact ((Commute.pow_right (show Commute k s from hKs k hk) m)).eq
  obtain ⟨K₀, u₀, hu₀K, hTr, hK₀, hloc⟩ := exists_fiLoc_pair_of_isSporadic_fi23 hKsp hKL
  have hu₀2 : orderOf u₀ = 2 := hTr.2.1
  obtain ⟨-, -, hK₀L, -, hK₀q, -⟩ := id hloc
  have hut₀ : u₀ * t = t * u₀ := mem_centralizer_iff.1 htL u₀ (hKL hu₀K)
  have hK₀X : K₀ ≤ centralizer ({u₀} : Set H) := by
    rw [hK₀]
    exact inf_le_right
  have hK₀t : K₀ ≤ centralizer ({t} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL k (hK₀L hk))
  have hK₀s' : K₀ ≤ centralizer ({s'} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (by
      rw [hK₀] at hk
      exact hKs' k hk.1)
  have hsX : s' ∈ centralizer ({u₀} : Set H) :=
    mem_centralizer_singleton_iff.2 (hKs' u₀ hu₀K).symm
  have htX : t ∈ centralizer ({u₀} : Set H) := mem_centralizer_singleton_iff.2 hut₀.symm
  have hnt := normal_of_fiIn24_layer hcov hloc htL ht2 hSol
  have hB : BTheoremAt u₀ := lit.bthm H ih.uHered hkp hN.oddCore_eq_bot u₀ hu₀2
  have h12 : ∀ M : Subgroup H, IsCompIn M (centralizer ({u₀} : Set H)) → K₀ ≤ M →
      CFSG.conjugate M t = M → M = K₀ := fun M hM hle hMt => by
    rw [hK₀] at hle ⊢
    exact Cx.hyp12_core pf hyp12 lo atl lit ih hN hidx hkp hcov hSol ht2 htL hKL hKsp hu₀K hTr hM
      hle hMt
  have hcomp : IsCompIn K₀ (centralizer ({u₀} : Set H)) :=
    isCompIn_of_square_swap hkp hN.center_eq_bot hu₀2 hB hK₀q hK₀X ht2 hss hsX htX hK₀t hK₀s'
      hnt h12
  have hyp35 : K₀ = componentProduct K₀ u₀ := by
    have hdq := lemma36DataQ_fi24in hfix
    obtain ⟨-, huK₀, -, -, hKq₀, hAs, hA, hrank⟩ := hdq.data H L K₀ u₀ hcov hloc
    have hcycall := cyclic_sylow_all_of_exists hcyc
    have hCt := hSol.centralizer_le_normalizer htL ht2
    exact componentProduct_eq_of_isCompIn_Q hdq.bound hCt htL ht2 (hK₀L huK₀) hK₀L hKq₀ hcomp
      (lam_isSolvable hcycall hAs)
      (fun E hE h2 _ => lam_elemAbelian_card_le_pow hcycall hA hE h2) hrank
  have hfi : fiIn24 H L K₀ u₀ := fiInBase_iff.2 ⟨hloc, hnb⟩
  have hglob : SolomonGlobalQ H L K₀ t u₀ :=
    { standardL := hSol
      cyclicSylow := hcyc
      t_order := ht2
      t_mem := htL
      u_comm_t := hut₀
      hyp35 := hyp35 }
  exact sol78Closing_fi24in_proved H N L K₀ t u₀ .Fi24Prime (List.mem_singleton.2 rfl) hN hidx hkp
    hcov hglob hfi

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.V3
