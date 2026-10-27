module

public import CFSG.GH74.GLS.C3.Layer1.EvenCore
public import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

theorem pf_eq_five_of_A5 {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel K .PSL 2 p f) (e : K ≃* alternatingGroup (Fin 5)) : p ^ f = 5 := by
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨eF⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hK : Nat.card K = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have hq1 : 1 < p ^ f := by
      have : 1 < Nat.card F := Finite.one_lt_card
      rwa [hcard] at this
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hq1
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p, f, hp, hp.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.2 hf0, hcard⟩
    have hPSL := CFSG.GorensteinWalter.psl2_card_formula F hodd
    have heq : Nat.card K = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Nat.card_congr (eF.trans (IVK.L2.equivPSL F)).toEquiv
    rw [hK] at heq
    rw [hcard] at hPSL
    have h120 : (p ^ f) * ((p ^ f) ^ 2 - 1) / 2 = 60 := by
      rw [← hPSL]
      exact heq.symm
    generalize p ^ f = q at hq1 h120 ⊢
    have hq5 : q ≤ 5 := by
      by_contra h
      push Not at h
      have : 6 * (6 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
        apply Nat.mul_le_mul h
        exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1
      omega
    interval_cases q <;> simp at h120 ⊢
  all_goals exact absurd h0 (by norm_num)

structure SporAutCfg {G : Type} [Group G] [Finite G] (N H K Q : Subgroup G) (x : G) : Prop where
  socle : IsSimpleSocle H N
  hKH : K ≤ H
  K5 : Nonempty (↥K ≃* alternatingGroup (Fin 5))
  index_two : Nat.card ↥N = 2 * Nat.card ↥H
  sporadic : NativeSporadic.IsSporadic ↥H .M12 ∨ NativeSporadic.IsSporadic ↥H .J2
  sylowQ : IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N)
  rankQ : 2 ≤ pRank 2 ↥Q
  hxQ : x ∈ Q
  hx2 : orderOf x = 2
  comp : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ N) K

@[expose] def B_spor_J2_table : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G),
    NativeSporadic.IsSporadic ↥H .J2 → K ≤ H → Nonempty (↥K ≃* alternatingGroup (Fin 5)) →
    2 ≤ pRank 2 ↥(centralizer (K : Set G) ⊓ H) →
      (∀ S : Subgroup G, IsSylowOf 2 S (normalizer (K : Set G) ⊓ H) →
        IsElementaryAbelian 2 ↥S ∧ Nat.card ↥S = 2 ^ 4) ∧
      (∀ y ∈ centralizer (K : Set G) ⊓ H, orderOf y = 2 →
        ¬ ∃ S : Subgroup G, IsSylowOf 2 S H ∧ y ∈ S ∧ ∀ s ∈ S, s * y = y * s)

@[expose] def B_spor_outer_invol : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N H K Q : Subgroup G) (x : G), SporAutCfg N H K Q x →
    ∃ u ∈ N, u ∉ H ∧ orderOf u = 2 ∧ u * x = x * u

@[expose] def B_spor_fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N H K Q : Subgroup G) (x y : G), SporAutCfg N H K Q x →
    y ∈ N → orderOf y = 2 → (∀ n ∈ N, n * x * n⁻¹ ≠ y) →
    (∃ f : ↥(centralizer ({y} : Set G) ⊓ N) →* ↥(centralizer ({x} : Set G) ⊓ N),
      Function.Injective f) →
    ∃ n ∈ N, n * y * n⁻¹ ∈ Q

section Small

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem no_normal_index_two (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∀ M : Subgroup G, M.Normal → M.index ≠ 2 := by
  intro M hM hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with rfl | rfl
  · have hcard : Nat.card G = 2 := by simpa [Subgroup.index_bot] using hidx
    obtain ⟨a, b, hab⟩ := hnab
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hcard
    exact hab ((IsCyclic.commGroup (α := G)).mul_comm a b)
  · simp at hidx

omit [Finite G] in
theorem mem_normalizer_of_standard {K : Subgroup G} (hK : IsStandardSubgroup K) {a c h : G}
    (ha2 : orderOf a = 2) (haC : a ∈ centralizer (K : Set G)) (hcC : c ∈ centralizer (K : Set G))
    (hach : a = h⁻¹ * c * h) : h ∈ normalizer (K : Set G) := by
  by_contra hh
  have hnC : h ∉ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
    rw [hK.2.2.2.1]
    exact hh
  have hodd := hK.2.2.1 h hnC
  have haI : a ∈ centralizer (K : Set G) ⊓ conjugate (centralizer (K : Set G)) h := by
    refine ⟨haC, Subgroup.mem_map.2 ⟨c, hcC, ?_⟩⟩
    simp [hach]
  have hdvd : 2 ∣ Nat.card ↥(centralizer (K : Set G) ⊓ conjugate (centralizer (K : Set G)) h) := by
    have := Subgroup.orderOf_dvd_natCard _ haI
    rwa [ha2] at this
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem x_mem_Q {x : G} {K T Q : Subgroup G} (hs : EvenSel x K T Q) : x ∈ Q := by
  rw [hs.hQ]
  refine ⟨?_, ?_⟩
  · exact C3.Layer1.Back.mem_of_isSylowOf_of_central hs.sylowT
      (mem_centralizer_singleton_iff.2 rfl)
      (fun _ hs' => mem_centralizer_singleton_iff.1 hs') hs.terminal.1
  · refine ⟨mem_centralizer_singleton_iff.2 rfl, ?_⟩
    refine C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ (by
      intro k hk
      exact (TwoThin.pPrimeCoreOf_le K) hk)
    intro k hk
    exact (mem_centralizer_singleton_iff.1 (hs.K_le_C hk)).symm

end Small

section Glue

variable {G : Type} [Group G] [Finite G]

theorem false_of_outer_cfg (hout : B_spor_outer_invol) (hfus : B_spor_fusion)
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {x : G} {K Q N H : Subgroup G} (hK : IsStandardSubgroup K)
    (hCxN : centralizer ({x} : Set G) ≤ N) (hMN : normalizer (K : Set G) ≤ N)
    (hQC : Q ≤ centralizer (K : Set G)) (hcfg : SporAutCfg N H K Q x) : False := by
  have hx2 := hcfg.hx2
  have hxN : x ∈ N := hCxN (mem_centralizer_singleton_iff.2 rfl)
  have hHN : H ≤ N := hcfg.socle.le
  have hidx : H.relIndex N = 2 := by
    have h1 := Subgroup.relIndex_mul_card H N
    rw [inf_eq_left.2 hHN, hcfg.index_two] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥H)) h1
  obtain ⟨u, huN, huH, hu2, hux⟩ := hout G N H K Q x hcfg
  obtain ⟨g, hgN, hg⟩ := EvenSporTransfer.exists_not_fused_of_index_two
    (no_normal_index_two hsimple hnab) hcfg.socle.normal hidx hxN hx2 huN huH hu2 hux hCxN
  have hy2 : orderOf (g⁻¹ * x * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    simpa [MulAut.conj_apply] using this.trans hx2
  have hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ g⁻¹ * x * g := by
    intro n hn h
    apply hg n⁻¹ (N.inv_mem hn)
    simpa using h.symm
  have hφ : ∀ z : ↥(centralizer ({g⁻¹ * x * g} : Set G) ⊓ N),
      g * (z : G) * g⁻¹ ∈ centralizer ({x} : Set G) ⊓ N := by
    intro z
    have hzc : (z : G) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * (z : G) :=
      mem_centralizer_singleton_iff.1 z.2.1
    have hc : g * (z : G) * g⁻¹ ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * (z : G) * g⁻¹ * x = g * ((z : G) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * (z : G)) * g⁻¹ := by rw [hzc]
        _ = x * (g * (z : G) * g⁻¹) := by group
    exact ⟨hc, hCxN hc⟩
  let φ : ↥(centralizer ({g⁻¹ * x * g} : Set G) ⊓ N) →* G :=
    (MulAut.conj g).toMonoidHom.comp (Subgroup.subtype _)
  have hφ' : ∀ z, φ z ∈ centralizer ({x} : Set G) ⊓ N := fun z => by
    simpa [φ, MulAut.conj_apply] using hφ z
  have hemb : ∃ f : ↥(centralizer ({g⁻¹ * x * g} : Set G) ⊓ N) →*
      ↥(centralizer ({x} : Set G) ⊓ N), Function.Injective f := by
    refine ⟨φ.codRestrict _ hφ', fun a b hab => ?_⟩
    have h1 : φ a = φ b := congrArg Subtype.val hab
    exact Subtype.ext ((MulAut.conj g).injective h1)
  obtain ⟨n, hnN, hnQ⟩ := hfus G N H K Q x (g⁻¹ * x * g) hcfg hgN hy2 hynot hemb
  have hach : n * (g⁻¹ * x * g) * n⁻¹ = (g * n⁻¹)⁻¹ * x * (g * n⁻¹) := by group
  have hord : orderOf (n * (g⁻¹ * x * g) * n⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) (g⁻¹ * x * g)
    simpa [MulAut.conj_apply] using this.trans hy2
  have hhM : g * n⁻¹ ∈ normalizer (K : Set G) :=
    mem_normalizer_of_standard hK hord (hQC hnQ) (hQC hcfg.hxQ) hach
  have hgN' : g ∈ N := by
    have := N.mul_mem (hMN hhM) hnN
    simpa [mul_assoc] using this
  exact hg g hgN' rfl

theorem false_of_J2 (hJ2 : B_spor_J2_table)
    {x : G} {K T Q H : Subgroup G} (hs : EvenSel x K T Q)
    (hH : NativeSporadic.IsSporadic ↥H .J2) (hKH : K ≤ H)
    (hK5 : Nonempty (↥K ≃* alternatingGroup (Fin 5)))
    (hMH : normalizer (K : Set G) ≤ H) (hCxH : centralizer ({x} : Set G) ≤ H) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := hK5
  have hxQ : x ∈ Q := x_mem_Q hs
  have hx2 : orderOf x = 2 := hs.terminal.1
  have hQC : Q ≤ centralizer (K : Set G) := hs.sylowQ.le
  have hCK : centralizer (K : Set G) ≤ H := (Subgroup.centralizer_le_normalizer _).trans hMH
  have hrk : 2 ≤ pRank 2 ↥(centralizer (K : Set G) ⊓ H) :=
    hs.rankQ.trans (C3.Layer1.Back.pRank_mono' (le_inf hQC (hQC.trans hCK)))
  obtain ⟨hSyl, hcent⟩ := hJ2 G H K hH hKH ⟨e5⟩ hrk
  have hMeq : normalizer (K : Set G) ⊓ H = normalizer (K : Set G) := inf_eq_left.2 hMH
  have hTea : IsElementaryAbelian 2 ↥T ∧ Nat.card ↥T = 2 ^ 4 :=
    hSyl T (by rw [hMeq]; exact hs.sylowTM)
  obtain ⟨hTe, hTcard⟩ := hTea
  have hTM : T ≤ normalizer (K : Set G) := hs.sylowTM.le
  have hTC : T ≤ centralizer ({x} : Set G) := hs.sylowT.le
  rcases hs.violation with ⟨p, f, hp, hp2, hL, hne⟩ | hB
  · exact hne (Or.inl (pf_eq_five_of_A5 hp hp2 hL e5))
  · apply hB
    intro p f hp hp2 hL
    have h5 := pf_eq_five_of_A5 hp hp2 hL e5
    refine ⟨?_, ?_, Or.inl ⟨h5, ?_⟩⟩
    ·
      have hE : IsElementaryAbelian 2 ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
        IsElementaryAbelian.subgroupOf hTC
      have hcard : Nat.card ↥(T.subgroupOf (centralizer ({x} : Set G))) = 2 ^ 4 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv]
        exact hTcard
      exact CFSG.LieType.SteinbergBR.le_pRank_of_card Nat.one_lt_two _ hE hcard
    ·
      rintro ⟨-, S, hxS, hSc⟩
      have hSC : (S : Subgroup G) ≤ H := fun s hs' =>
        hCxH (mem_centralizer_singleton_iff.2 (hSc s hs'))
      have hSyl' : IsSylowOf 2 (S : Subgroup G) H := by
        rw [isSylowOf_iff]
        refine ⟨hSC, S.isPGroup', fun hdvd => S.not_dvd_index ?_⟩
        rw [← Subgroup.relIndex_mul_index hSC]
        exact Dvd.dvd.mul_right hdvd _
      exact hcent x ⟨hQC hxQ, hCK (hQC hxQ)⟩ hx2 ⟨S, hSyl', hxS, hSc⟩
    ·
      obtain ⟨P, hP⟩ := hs.sylowTM.exists_sylow_eq_subgroupOf
      refine ⟨P, ?_, ?_⟩
      · rw [hP]
        exact IsElementaryAbelian.subgroupOf hTM
      · rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv]
        exact hTcard

end Glue

theorem b_even_N_spor_of_tables (hJ2 : B_spor_J2_table) (hout : B_spor_outer_invol)
    (hfus : B_spor_fusion) : B_even_N_spor := by
  intro G _ _ hG hE hV x K T Q N H hs hstd hgam hMN hN hKH hsoc hK5 hcase
  have hMleN : normalizer (K : Set G) ≤ N := hMN.le
  have hxQ : x ∈ Q := x_mem_Q hs
  have hx2 : orderOf x = 2 := hs.terminal.1
  have hQC : Q ≤ centralizer (K : Set G) := hs.sylowQ.le
  have hCxM : centralizer ({x} : Set G) ≤ normalizer (K : Set G) :=
    EvenCore.centralizer_le_normalizer_of_mem hgam hxQ hx2
  have hCxN : centralizer ({x} : Set G) ≤ N := hCxM.trans hMleN
  have hCKN : centralizer (K : Set G) ≤ N :=
    (Subgroup.centralizer_le_normalizer _).trans hMleN
  have hcomp : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ N) K := by
    rw [inf_eq_left.2 hCxN]
    exact hs.twoTerminal.1.2.2
  have hsylow : IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N) := by
    rw [inf_eq_left.2 hCKN]
    exact hs.sylowQ
  rcases hcase with ⟨hM12, hcard⟩ | ⟨hJ2', hNH | hcard⟩
  · exact false_of_outer_cfg hout hfus hG.kproper.1 hG.kproper.2.1 hstd hCxN hMleN hQC
      ⟨hsoc, hKH.le, hK5, hcard, Or.inl hM12, hsylow, hs.rankQ, hxQ, hx2, hcomp⟩
  · subst hNH
    exact false_of_J2 hJ2 hs hJ2' hKH.le hK5 hMleN hCxN
  · exact false_of_outer_cfg hout hfus hG.kproper.1 hG.kproper.2.1 hstd hCxN hMleN hQC
      ⟨hsoc, hKH.le, hK5, hcard, Or.inr hJ2', hsylow, hs.rankQ, hxQ, hx2, hcomp⟩

end CFSG.GH74.GLS
