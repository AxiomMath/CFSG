module

public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic
public import CFSG.HardMathSupport.Lang.AnisoE8.D8Family
public import CFSG.HardMathSupport.Lang.AnisoE8.Closing
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LieType.SeitzGeneration.OrthManyMaster
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Planes

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.ComponentClassification
open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.HardMathSupport.Lang.AnisoE8 CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.StandardType.TableBExcTwo

@[expose] def e8w (l : List (Fin 8)) : List (Fin (Tag.rank .E8)) := l.map e8Node

@[expose] def e8Word : List (Fin (Tag.rank .E8)) := e8w [0, 2, 3, 1, 4, 3, 2, 0]

@[expose] def e8FramePerm : Fin 8 → Fin 8 := ![0, 2, 1, 3, 4, 7, 6, 5]

theorem e8FramePerm_swap (i : Fin 8) : e8FramePerm (e8FramePerm i) = i := by
  revert i
  decide

theorem wordReflect_e8Word_frame : ∀ i : Fin 8,
    CatLeafProof.wordReflect .E8 e8Word (frameE8Root i) = frameE8Root (e8FramePerm i) := by decide

section Roots


theorem e8Frame_isRoot : ∀ i, IsRoot .E8 (frameE8Root i) := by
  intro i
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  revert i
  decide +kernel

theorem e8Frame_facts : ∀ i j : Fin 8, i ≠ j → frameE8Root i ≠ frameE8Root j ∧
    frameE8Root i ≠ -frameE8Root j ∧ iform (frameE8Root i) (frameE8Root j) = 0 ∧
      ¬ IsRoot .E8 (frameE8Root i + frameE8Root j) ∧
        ¬ IsRoot .E8 (frameE8Root i + -frameE8Root j) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  decide +kernel

end Roots

section Frame


@[expose] noncomputable def e8FrameGroup (K : Type) [Field K] : Subgroup (adjointGroup .E8 K) :=
  ⨆ i, rootPairE8 K (frameE8Root i)

variable {K : Type} [Field K]

theorem rootPairE8_wordReflect_le {M : Subgroup (adjointGroup .E8 K)}
    (ω : List (Fin (Tag.rank .E8))) (hω : ∀ i ∈ ω, weylElement .E8 K i ∈ M)
    {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) (h : rootPairE8 K γ ≤ M) :
    rootPairE8 K (CatLeafProof.wordReflect .E8 ω γ) ≤ M := by
  have hn : weylWordElt .E8 K ω ∈ M := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hω i hi
  have hmap := map_conj_weylWordElt_rootPair (K := K) ω hγ
  change (e8Datum K).rootGroup (CatLeafProof.wordReflect .E8 ω γ) ⊔
    (e8Datum K).rootGroup (-CatLeafProof.wordReflect .E8 ω γ) ≤ M
  rw [← hmap]
  rintro _ ⟨y, hy, rfl⟩
  exact M.mul_mem (M.mul_mem hn (h hy)) (M.inv_mem hn)

theorem weylElement_mem_d8 (i : Fin (Tag.rank .E8)) (hi : i ≠ 0) :
    weylElement .E8 K i ∈ ⨆ k, e8D8Chain K k := by
  obtain ⟨k, hk, rfl⟩ : ∃ k : Fin 8, k ≠ 0 ∧ e8D8Node k = i := by
    revert i
    decide
  have hU : e8D8Chain K k = rankOne (e8Datum K).rootGroup (e8D8Node k) := by
    unfold e8D8Chain
    rw [ite_eq_right_iff.2 (fun h => absurd h hk)]
  exact Subgroup.mem_iSup_of_mem k (by
    rw [hU]
    exact Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .E8) _)

theorem rootPairE8_theta_le_d8 : rootPairE8 K e8D8Root ≤ ⨆ k, e8D8Chain K k := by
  have hU : e8D8Chain K 0 = (e8Datum K).rootGroup e8D8Root ⊔ (e8Datum K).rootGroup (-e8D8Root) := by
    simp [e8D8Chain]
  exact (le_of_eq hU.symm).trans (le_iSup (e8D8Chain K) 0)

theorem rootPairE8_simple_le_d8 (j : Fin 8) (hj : j ≠ 0) :
    rootPairE8 K (Pi.single (e8Node j) 1) ≤ ⨆ k, e8D8Chain K k := by
  obtain ⟨k, hk, hkj⟩ : ∃ k : Fin 8, k ≠ 0 ∧ e8D8Node k = e8Node j := by
    revert j
    decide
  have hU : e8D8Chain K k = rankOne (e8Datum K).rootGroup (e8D8Node k) := by
    unfold e8D8Chain
    rw [ite_eq_right_iff.2 (fun h => absurd h hk)]
  rw [← hkj]
  exact (le_of_eq hU.symm).trans (le_iSup (e8D8Chain K) k)

theorem rootPairE8_wordReflect_le_d8 (ω : List (Fin (Tag.rank .E8))) (hω : ∀ i ∈ ω, i ≠ 0)
    {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ)
    (h : rootPairE8 K γ ≤ ⨆ k, e8D8Chain K k) :
    rootPairE8 K (CatLeafProof.wordReflect .E8 ω γ) ≤ ⨆ k, e8D8Chain K k :=
  rootPairE8_wordReflect_le ω (fun i hi => weylElement_mem_d8 i (hω i hi)) hγ h

theorem rootPairE8_frame_le_d8 (i : Fin 8) :
    rootPairE8 K (frameE8Root i) ≤ ⨆ k, e8D8Chain K k := by
  fin_cases i
  · have h := rootPairE8_wordReflect_le_d8 (K := K)
      (e8w [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7]) (by decide) isRoot_e8D8Root
      rootPairE8_theta_le_d8
    have e : CatLeafProof.wordReflect .E8 (e8w [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7]) e8D8Root =
        frameE8Root 0 := by decide
    rwa [e] at h
  · have e : frameE8Root 1 = e8D8Root := by decide
    show rootPairE8 K (frameE8Root 1) ≤ _
    rw [e]
    exact rootPairE8_theta_le_d8
  · have h := rootPairE8_wordReflect_le_d8 (K := K)
      (e8w [5, 6, 4, 5, 3, 4, 2, 3]) (by decide) (γ := Pi.single (e8Node 1) 1) (isRoot_single _ _)
      (rootPairE8_simple_le_d8 1 (by decide))
    have e : CatLeafProof.wordReflect .E8 (e8w [5, 6, 4, 5, 3, 4, 2, 3]) (Pi.single (e8Node 1) 1) =
        frameE8Root 2 := by decide
    rwa [e] at h
  · have h := rootPairE8_wordReflect_le_d8 (K := K)
      (e8w [3, 4, 2, 3]) (by decide) (γ := Pi.single (e8Node 1) 1) (isRoot_single _ _)
      (rootPairE8_simple_le_d8 1 (by decide))
    have e : CatLeafProof.wordReflect .E8 (e8w [3, 4, 2, 3]) (Pi.single (e8Node 1) 1) =
        frameE8Root 3 := by decide
    rwa [e] at h
  · have e : frameE8Root 4 = Pi.single (e8Node 6) 1 := by decide
    show rootPairE8 K (frameE8Root 4) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 6 (by decide)
  · have e : frameE8Root 5 = Pi.single (e8Node 4) 1 := by decide
    show rootPairE8 K (frameE8Root 5) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 4 (by decide)
  · have e : frameE8Root 6 = Pi.single (e8Node 2) 1 := by decide
    show rootPairE8 K (frameE8Root 6) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 2 (by decide)
  · have e : frameE8Root 7 = Pi.single (e8Node 1) 1 := by decide
    show rootPairE8 K (frameE8Root 7) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 1 (by decide)

theorem e8FrameGroup_le_d8 : e8FrameGroup K ≤ ⨆ k, e8D8Chain K k :=
  iSup_le fun i => rootPairE8_frame_le_d8 i

theorem e8FrameGroup_le_conj_d8 : e8FrameGroup K ≤
    (⨆ k, e8D8Chain K k).map (MulAut.conj (weylWordElt .E8 K e8Word)).toMonoidHom := by
  refine iSup_le fun i => ?_
  have h := map_conj_weylWordElt_rootPair (K := K) e8Word (e8Frame_isRoot (e8FramePerm i))
  rw [wordReflect_e8Word_frame, e8FramePerm_swap] at h
  change (e8Datum K).rootGroup (frameE8Root i) ⊔ (e8Datum K).rootGroup (-frameE8Root i) ≤ _
  rw [← h]
  exact Subgroup.map_mono (rootPairE8_frame_le_d8 _)

end Frame

section Native


section Closing

variable {K : Type} [Field K]

theorem eq_top_of_e8D8Chain_le_of_conj_le (M : Subgroup (adjointGroup .E8 K))
    (hX : ⨆ k, e8D8Chain K k ≤ M)
    (hn : (⨆ k, e8D8Chain K k).map (MulAut.conj (weylWordElt .E8 K e8Word)).toMonoidHom ≤ M) :
    M = ⊤ := by
  refine eq_top_of_d8Chain_le_of_delta_le M hX ?_
  have hroot : IsRoot .E8 (CatLeafProof.wordReflect .E8 e8Word e8Delta) :=
    isRoot_wordReflect _ isRoot_e8Delta
  have h := map_conj_weylWordElt_rootPair (K := K) e8Word hroot
  have e2 : CatLeafProof.wordReflect .E8 e8Word (CatLeafProof.wordReflect .E8 e8Word e8Delta) =
      e8Delta := by decide
  rw [e2] at h
  have hX' : rootPairE8 K (CatLeafProof.wordReflect .E8 e8Word e8Delta) ≤ ⨆ k, e8D8Chain K k := by
    have h' := rootPairE8_wordReflect_le_d8 (K := K)
      (e8w [4, 3, 2, 1, 3, 4, 5, 6, 7]) (by decide) isRoot_e8D8Root
      rootPairE8_theta_le_d8
    have e : CatLeafProof.wordReflect .E8 (e8w [4, 3, 2, 1, 3, 4, 5, 6, 7]) e8D8Root =
        CatLeafProof.wordReflect .E8 e8Word e8Delta := by decide
    rwa [e] at h'
  change (e8Datum K).rootGroup e8Delta ⊔ (e8Datum K).rootGroup (-e8Delta) ≤ M
  rw [← h]
  exact (Subgroup.map_mono hX').trans hn

end Closing

section SylowFrame

variable {K : Type} [Field K]

theorem exists_sl2_hom_rootPairE8 {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) :
    ∃ ρ : SL(2, K) →* adjointGroup .E8 K, Function.Injective ρ ∧ ρ.range = rootPairE8 K γ := by
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras K
  choose ρF hρFi hρFr _ using exists_rankOne_param hE
  induction hγ with
  | basis j => exact ⟨ρF j, hρFi j, hρFr j⟩
  | reflect i hv ih =>
    obtain ⟨ρ, hρi, hρr⟩ := ih
    refine ⟨(MulAut.conj (weylElement .E8 K i)).toMonoidHom.comp ρ,
      (MulAut.conj _).injective.comp hρi, ?_⟩
    rw [MonoidHom.range_comp, hρr]
    exact map_conj_weylElement_rootPair_adj i hv

theorem e8Frame_hom : ∃ ρ : Fin 8 → SL(2, K) →* adjointGroup .E8 K,
    (∀ i, Function.Injective (ρ i)) ∧ (∀ i, (ρ i).range = rootPairE8 K (frameE8Root i)) ∧
      ∀ i j, i ≠ j → ∀ x y, Commute (ρ i x) (ρ j y) := by
  choose ρ hρi hρr using fun i => exists_sl2_hom_rootPairE8 (K := K) (e8Frame_isRoot i)
  refine ⟨ρ, hρi, hρr, fun i j hij x y => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := e8Frame_facts i j hij
  have hc := commutes_rootPair_of_noG2 (K := K) noG2_E8 (e8Frame_isRoot i) (e8Frame_isRoot j)
    h1 h2 h3 h4 h5
  have hx : ρ i x ∈ rootPairE8 K (frameE8Root i) := by
    rw [← hρr i]
    exact ⟨x, rfl⟩
  have hy : ρ j y ∈ rootPairE8 K (frameE8Root j) := by
    rw [← hρr j]
    exact ⟨y, rfl⟩
  exact hc _ hx _ hy

section Card

variable [Finite K]

theorem factorization_card_E8_of_dvd_add_one {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup .E8 K)).factorization p = 8 * (Nat.card K + 1).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 2 ≤ Nat.card K :=
    Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hsq : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    have h : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hpq
    push_cast at h
    linear_combination ((Nat.card K : ZMod p) - 1) * h
  have hne1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    have h2 : p ∣ Nat.card K - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h1, Nat.cast_one, sub_self]
    exact hpq1 h2
  have hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
    have hd : orderOf ((Nat.card K : ℕ) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne1
    · exact h
  have h1 := ordProj_card_adjointGroup_E (τ := .E8) (Or.inr (Or.inr rfl)) (K := K) hp (by omega)
    hpK
  have h2 := prod_ordProj_pow_sub_one hp (by omega) hpK hq2 hord (degreesE .E8) (by
    intro d hd hde
    refine ⟨?_, ?_⟩
    · rintro rfl
      simp [degreesE] at hd
    · simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
      intro hdv
      have hle : p ≤ d / 2 := Nat.le_of_dvd (by omega) hdv
      have hd15 : d / 2 ≤ 15 := by
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      have hp15 : p ≤ 15 := by omega
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        interval_cases p <;> first | omega | (exfalso; revert hp; norm_num))
  rw [h2] at h1
  have h3 : (degreesE .E8).filter (fun d => 2 ∣ d) = degreesE .E8 := by
    simp [degreesE]
  rw [h3] at h1
  have h4 : (degreesE .E8).length = 8 := rfl
  rw [h4, ← pow_mul] at h1
  have h5 := Nat.pow_right_injective hp.two_le h1
  have e2 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    zify [Nat.one_le_pow 2 (m + 1) (by omega)]
    ring
  have hq21 : Nat.card K - 1 ≠ 0 := by
    intro h
    apply hpq1
    rw [h]
    exact dvd_zero p
  have hq22 : Nat.card K + 1 ≠ 0 := by omega
  rw [h5, show Nat.card K ^ 2 = Nat.card K ^ 2 from rfl, e2,
    Nat.factorization_mul hq21 hq22, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpq1,
    zero_add, mul_comm]

end Card

end SylowFrame

section ClassicalD8

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem iSup_d8Chain_le_closure_centralizers_two {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    (E : Subgroup (adjointGroup .E8 K)) (hE : E ≤ ⨆ k, e8D8Chain K k)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ⨆ k, e8D8Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
      rw [hZ]
    exact hd.trans this
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus 8 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : spinGroup (quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE', hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, card_map_eq_of_disjoint_ker π (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := orthogonalPlusPlanes 8 p K (by norm_num) hp hp5 hpK Ebar hEbarea hcardEbar
  have hG := closure_centralizers_of_quotient π hπsurj hZ.le hπcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg

end ClassicalD8

@[expose] def E8TwoSylow : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 11 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K

@[expose] def E8TwoD8 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 11 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E : Subgroup (adjointGroup .E8 K), E ≤ ⨆ k, e8D8Chain K k → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 →
        ⨆ k, e8D8Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x}

@[expose] def E8TwoNative : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 11 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

theorem e8TwoNative_of_interfaces (h1 : E8TwoSylow) (h2 : E8TwoD8) : E8TwoNative := by
  intro K _ _ p hpF hp11 hpq E₀ hE₀p hE₀c
  obtain ⟨g, hg⟩ := h1 K p hp11 hpq E₀ hE₀p hE₀c
  exact closure_centralizers_eq_top_of_two_conj (p := p) (⨆ k, e8D8Chain K k) (e8FrameGroup K)
    (weylWordElt .E8 K e8Word) e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => h2 K p hp11 hpq E hE hEp hEc) E₀ hE₀p hE₀c ⟨g, hg⟩

theorem e8TwoSylow : E8TwoSylow := by
  intro K _ _ p hpF hp11 hpq E₀ hE₀p hE₀c
  obtain ⟨ρ, hρi, hρr, hρc⟩ := e8Frame_hom (K := K)
  have hcomm : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    exact hρc i j hij x y
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow ρ hρi hcomm (by omega) hpq
    (by rw [factorization_card_E8_of_dvd_add_one hpF.out hp11 hpq])
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le ρ hcomm Q).trans ?_)⟩
  simp only [e8FrameGroup, hρr]
  exact le_rfl

theorem e8TwoD8 : E8TwoD8 := by
  intro K _ _ p hpF hp11 hpq E hE hEp hEc
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  exact iSup_d8Chain_le_closure_centralizers_two hpF.out (by omega) hpq Ψ hker hrange E hE hEp hEc

theorem e8TwoNative : E8TwoNative := e8TwoNative_of_interfaces e8TwoSylow e8TwoD8

end Native

section Glue


@[expose] def SeitzExcHighE8TwoGeEleven : Prop :=
  SeitzExcHighForAt IsE8Index fun d p => 11 ≤ p ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 2 d p

theorem seitzExcHighE8Two_of_native (h : E8TwoNative) : SeitzExcHighE8TwoGeEleven := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp11, -, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp hord
  exact CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.planeGen_of_native_closure e
    center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => h K p hp11 hpq E₀ hE₀p hE₀c) hE hcard hin

theorem seitzExcHighE8Two_of_ge_eleven : SeitzExcHighE8TwoGeEleven :=
  seitzExcHighE8Two_of_native e8TwoNative


@[expose] def SeitzExcHighE8TwoLtEleven : Prop :=
  SeitzExcHighForAt IsE8Index fun d p => p < 11 ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 2 d p

theorem seitzExcHighE8Two_of_ge_eleven_of_lt
    (h : SeitzExcHighE8TwoLtEleven) : SeitzExcHighE8Two :=
  SeitzExcHighForAt.union (fun d p _ _ hQ => (Nat.lt_or_ge p 11).elim (fun h' => Or.inr ⟨h', hQ⟩)
    (fun h' => Or.inl ⟨h', hQ⟩)) seitzExcHighE8Two_of_ge_eleven h

end Glue

end CFSG.LieType.SeitzGeneration.ExcHigh
