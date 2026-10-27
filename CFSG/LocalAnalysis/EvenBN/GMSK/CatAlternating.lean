module

public import CFSG.LocalAnalysis.SteinbergBTAlternatingInvolutionFixedSupportSL2
public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.SteinbergCDEvenOrderFourTools
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Alternating

open Equiv Subgroup
open CFSG.LocalAnalysis.SteinbergBT (swap_mul_swap_comm_of_ne exists_even_orderOf_eq_four_fin_six
  three_le_card_of_ne mul_comm_of_conj_eq)

section TwoGroups

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_mul_self {a : G} (ha : a * a = 1) : IsPGroup 2 (zpowers a) := by
  have h : orderOf a ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact ha)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

theorem exists_isPGroup_two_le_of_commute [Finite G] {H : Subgroup G} {a b : G} (haH : a ∈ H)
    (hbH : b ∈ H) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) :
    ∃ Q : Subgroup G, Q ≤ H ∧ IsPGroup 2 Q ∧ 3 ≤ Nat.card Q := by
  refine ⟨zpowers a ⊔ zpowers b, sup_le ((zpowers_le).mpr haH) ((zpowers_le).mpr hbH),
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self ha)
      (isPGroup_zpowers_of_mul_self hb) ?_,
    three_le_card_of_ne _ (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers b)) ha1 hb1
      hne⟩
  rw [zpowers_le, mem_normalizer_iff]
  have hc : ∀ k : ℤ, a * b ^ k * a⁻¹ = b ^ k := fun k => by
    rw [(Commute.zpow_right hab k).eq, mul_inv_cancel_right]
  intro x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hc k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : a * x * a⁻¹ = a * b ^ k * a⁻¹ := by rw [hc k]; exact hk.symm
    simpa using h1.symm

theorem mul_mul_self_of_commute {p q : G} (hpq : p * q = q * p) (hp : p * p = 1)
    (hq : q * q = 1) : (p * q) * (p * q) = 1 := by
  calc (p * q) * (p * q) = p * (q * p) * q := by group
    _ = p * (p * q) * q := by rw [hpq]
    _ = (p * p) * (q * q) := by group
    _ = 1 := by rw [hp, hq, one_mul]

end TwoGroups

section AltSix

variable {G : Type*} [Group G]

theorem card_le_factorial_index (hG : IsSimpleGroup G) {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card G ≤ H.index.factorial := by
  have hcore : H.normalCore = ⊥ := by
    have := hG
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have := H.index_normalCore_le_factorial_index
  rwa [hcore, Subgroup.index_bot] at this

theorem eq_top_of_lt_of_index_le_six [Finite G] (hG : IsSimpleGroup G) (hcard : 120 < Nat.card G)
    {H N : Subgroup G} (hHN : H < N) (hidx : H.index ≤ 6) : N = ⊤ := by
  by_contra hN
  have h1 := card_le_factorial_index hG hN
  have h2 := Subgroup.card_lt_of_lt hHN
  have h3 := H.card_mul_index
  have h4 := N.card_mul_index
  have hNpos : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have h5 : N.index < H.index := by
    by_contra h6
    push Not at h6
    have : Nat.card H * H.index ≤ Nat.card H * N.index := Nat.mul_le_mul_left _ h6
    nlinarith
  have h6 : N.index ≤ 5 := by omega
  have : N.index.factorial ≤ (5 : ℕ).factorial := Nat.factorial_le h6
  have : (5 : ℕ).factorial = 120 := rfl
  omega

theorem eq_one_of_forall_fixed_of_card_sixty [Finite G] (hG : IsSimpleGroup G)
    (hcardG : Nat.card G = 360) {S : Subgroup G} (hS : IsSimpleGroup S) (hcardS : Nat.card S = 60)
    (α : MulAut G) (hα : ∀ s ∈ S, α s = s) : α = 1 := by
  classical
  have hidx : S.index = 6 := by
    have := S.card_mul_index
    rw [hcardS, hcardG] at this
    omega
  have hSG : S ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top, hcardG] at hcardS
    omega
  have hN : Subgroup.normalizer (S : Set G) = S := by
    by_contra hne
    have hlt : S < Subgroup.normalizer (S : Set G) :=
      lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)
    have htop := eq_top_of_lt_of_index_le_six hG (by omega) hlt hidx.le
    have : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
    · rw [h, Subgroup.card_bot] at hcardS
      omega
    · exact hSG h
  have hα' : ∀ t, α t ∈ S → t ∈ S := fun t ht => by
    have h1 : α (α t) = α t := hα _ ht
    rw [α.injective h1] at ht
    exact ht
  let f : G ⧸ S → G ⧸ S := Quotient.map' α fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul, hα _ h]
    exact h
  have hf : ∀ g : G, f (g : G ⧸ S) = ((α g : G) : G ⧸ S) := fun g => rfl
  have hfS : ∀ (s : S) (x : G ⧸ S), f (s • x) = s • f x := by
    intro s x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change f ((s : G) • (g : G ⧸ S)) = (s : G) • f g
      rw [MulAction.Quotient.smul_mk, hf, hf, smul_eq_mul, map_mul, hα _ s.2,
        MulAction.Quotient.smul_mk, smul_eq_mul]
  have hfinj : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        rw [hf, hf, QuotientGroup.eq, ← map_inv, ← map_mul] at hxy
        exact QuotientGroup.eq.mpr (hα' _ hxy)
  have hf1 : f ((1 : G) : G ⧸ S) = ((1 : G) : G ⧸ S) := by rw [hf, map_one]
  have hcardX : Nat.card (G ⧸ S) = 6 := by rw [← Subgroup.index_eq_card, hidx]
  have hfix : ∀ x : G ⧸ S, f x = x := by
    intro x
    by_cases hx1 : x = ((1 : G) : G ⧸ S)
    · rw [hx1, hf1]
    set T := MulAction.stabilizer S x with hTdef
    have hT : T ≠ ⊤ := by
      intro hT
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have hle : S ≤ S.map (MulAut.conj g).toMonoidHom := by
        intro s hs
        have h1 : (⟨s, hs⟩ : S) ∈ T := hT ▸ Subgroup.mem_top _
        have h2 : s ∈ MulAction.stabilizer G ((g : G) : G ⧸ S) := h1
        rwa [show ((g : G) : G ⧸ S) = g • ((1 : G) : G ⧸ S) by
          rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one],
          MulAction.stabilizer_smul_eq_stabilizer_map_conj,
          MulAction.stabilizer_quotient] at h2
      have heq : S = S.map (MulAut.conj g).toMonoidHom := Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
      have hgN : g ∈ Subgroup.normalizer (S : Set G) := by
        rw [Subgroup.mem_normalizer_iff'']
        intro h
        conv_lhs => rw [heq]
        rw [Subgroup.mem_map_equiv]
        simp [MulAut.conj_symm_apply]
      rw [hN] at hgN
      exact hx1 (QuotientGroup.eq.mpr (by simpa using inv_mem hgN))
    have horb_base : ((1 : G) : G ⧸ S) ∉ MulAction.orbit S x := by
      rintro ⟨s, hs⟩
      apply hx1
      have h1 : x = s⁻¹ • ((1 : G) : G ⧸ S) := by rw [← hs, inv_smul_smul]
      rw [h1]
      change ((s⁻¹ : S) : G) • ((1 : G) : G ⧸ S) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      exact QuotientGroup.eq.mpr (by simp)
    have hTidx : T.index = (MulAction.orbit S x).ncard := MulAction.index_stabilizer S x
    have horb_lt : (MulAction.orbit S x).ncard < 6 := by
      rw [← hcardX, ← Set.ncard_univ]
      exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset (Set.subset_univ _)).mpr
        ⟨_, Set.mem_univ _, horb_base⟩) (Set.toFinite _)
    have hT5 : T.index = 5 := by
      have h1 := card_le_factorial_index hS hT
      rw [hcardS] at h1
      by_contra h3
      have h4 : T.index ≤ 4 := by omega
      have := Nat.factorial_le h4
      have : (4 : ℕ).factorial = 24 := rfl
      omega
    have hfx1 : f x ≠ ((1 : G) : G ⧸ S) := fun h => hx1 (hfinj (h.trans hf1.symm))
    have hfx_orb : f x ∈ MulAction.orbit S x := by
      by_contra hfx
      have := Set.ncard_le_ncard (Set.subset_univ
        (insert (f x) (insert ((1 : G) : G ⧸ S) (MulAction.orbit S x)))) (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem (by simp [hfx1, hfx]) (Set.toFinite _),
        Set.ncard_insert_of_notMem horb_base (Set.toFinite _), ← hTidx, hT5, Set.ncard_univ,
        hcardX] at this
      omega
    obtain ⟨s, hs⟩ := hfx_orb
    change s • x = f x at hs
    have hstab : MulAction.stabilizer S (f x) = T := by
      ext t
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← hfS]
      exact hfinj.eq_iff
    have hconj : T.map (MulAut.conj s).toMonoidHom = T := by
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hs, hstab]
    have hsN : s ∈ Subgroup.normalizer (T : Set S) := by
      rw [Subgroup.mem_normalizer_iff'']
      intro t
      conv_lhs => rw [← hconj]
      rw [Subgroup.mem_map_equiv]
      simp [MulAut.conj_symm_apply]
    have hTN : Subgroup.normalizer (T : Set S) = T := by
      by_contra hne
      have hlt : T < Subgroup.normalizer (T : Set S) :=
        lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)
      have hNtop : Subgroup.normalizer (T : Set S) ≠ ⊤ := by
        intro htop
        have : T.Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h | h
        · rw [h, Subgroup.index_bot, hcardS] at hT5
          omega
        · exact hT h
      have h1 := card_le_factorial_index hS hNtop
      have h2 := Subgroup.card_lt_of_lt hlt
      have h3 := T.card_mul_index
      have h4 := (Subgroup.normalizer (T : Set S)).card_mul_index
      rw [hcardS, hT5] at *
      have h5 : (Subgroup.normalizer (T : Set S)).index ≤ 4 := by
        by_contra h6
        push Not at h6
        nlinarith
      have := Nat.factorial_le h5
      have : (4 : ℕ).factorial = 24 := rfl
      omega
    rw [hTN] at hsN
    rw [← hs]
    exact hsN
  have hc : ∀ g : G, (α g)⁻¹ * g ∈ S := fun g =>
    QuotientGroup.eq.mp ((hf g).symm.trans (hfix g))
  have hcore : S.normalCore = ⊥ := by
    have := hG
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ S.normalCore_le)) hSG
  refine MulEquiv.ext fun g => ?_
  have hmem : (α g)⁻¹ * g ∈ S.normalCore := by
    intro b
    have h1 : b * ((α g)⁻¹ * g) * b⁻¹ =
        ((α b⁻¹)⁻¹ * b⁻¹)⁻¹ * ((α (g * b⁻¹))⁻¹ * (g * b⁻¹)) := by
      rw [map_mul, map_inv]
      group
    rw [h1]
    exact mul_mem (inv_mem (hc _)) (hc _)
  rw [hcore, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem

end AltSix

end CFSG.LocalAnalysis.EvenBN.GMSK.Alternating

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Equiv Subgroup Alternating
open CFSG.LocalAnalysis.SteinbergBT (swap_mul_swap_comm_of_ne exists_even_orderOf_eq_four_fin_six
  three_le_card_of_ne mul_comm_of_conj_eq)

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification in
theorem alternating_involution_normal_even_SL2_fixed_support_rankOne_selector {n m : ℕ} (hn : 2 ≤ n)
    (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n) (hm : 5 ≤ m) (hm6 : m ≠ 6) {D : Type*}
    [Group D] [Finite D] (η : D ≃* alternatingGroup (Fin m)) (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (φ : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) (hr : FixedRootRankOne α S) :
    m = 7 ∧ n = 2 ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      ∃ σ : Perm (Fin m),
        (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = σ * g * σ⁻¹) ∧
        (∀ τ : Perm (Fin m),
          (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = τ * g * τ⁻¹) →
            τ = σ) ∧
        (∃ a b : Fin m, a ≠ b ∧ σ = swap a b) ∧ Nat.card {x // σ x = x} = 5 ∧
        S.map ((alternatingGroup (Fin m)).subtype.comp (η : D →* alternatingGroup (Fin m))) =
          (alternatingGroup {x // σ x = x}).map Perm.ofSubtype := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hSs : IsSimpleGroup S := by
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have := Fintype.ofFinite K
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isSimpleGroup h2K (by
      rw [← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
    exact φ.isSimpleGroup
  have hSnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
    exact ⟨φ.symm a, φ.symm b, fun h => hab (by
      have h1 := congrArg φ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1)⟩
  have hm' : m = 5 ∨ 7 ≤ m := by omega
  have hmemC : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ α d = d := fun d => Iff.rfl
  let β : MulAut (alternatingGroup (Fin m)) := η.symm.trans (α.trans η)
  have hβ : ∀ g, β g = η (α (η.symm g)) := fun g => rfl
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hm' β
  have hσ' : ∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = σ * g * σ⁻¹ :=
    fun g => hσ g
  have hinj := Quasithin.SteinbergCB.conjPerm_injective (n := m) (by omega)
  have hconj : ∀ τ : Perm (Fin m),
      (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = τ * g * τ⁻¹) →
        Quasithin.SteinbergCB.conjPerm m τ = β := fun τ hτ =>
    MulEquiv.ext fun g => Subtype.ext (by rw [Quasithin.SteinbergCB.conjPerm_apply, hβ, hτ])
  have huniq : ∀ τ : Perm (Fin m),
      (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = τ * g * τ⁻¹) →
        τ = σ := fun τ hτ => hinj ((hconj τ hτ).trans (hconj σ hσ').symm)
  have hα2 : ∀ d, α (α d) = d := by
    have h : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    intro d
    have := congrArg (fun γ : MulAut D => γ d) h
    simpa [sq] using this
  have hσσ : σ * σ = 1 := by
    apply hinj
    rw [map_mul, hconj σ hσ', map_one]
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.mul_apply, hβ, hβ, MulEquiv.symm_apply_apply, hα2, MulEquiv.apply_symm_apply,
      MulAut.one_apply]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hβ1 : β = 1 := by rw [← hconj σ hσ', h1, map_one]
    have hα1 : α ≠ 1 := fun h => by
      rw [h, orderOf_one] at hα
      omega
    apply hα1
    refine MulEquiv.ext fun d => ?_
    have := congrArg (fun γ : MulAut (alternatingGroup (Fin m)) => γ (η d)) hβ1
    simp only [hβ, MulEquiv.symm_apply_apply, MulAut.one_apply] at this
    exact η.injective this
  have hσ2 : orderOf σ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  have hσinv : ∀ x, σ (σ x) = x := fun x => by rw [← Perm.mul_apply, hσσ, Perm.one_apply]
  let ι : D →* Perm (Fin m) :=
    (alternatingGroup (Fin m)).subtype.comp (η : D →* alternatingGroup (Fin m))
  have hι : Function.Injective ι := (alternatingGroup (Fin m)).subtype_injective.comp η.injective
  have hιA : ∀ d, ι d ∈ alternatingGroup (Fin m) := fun d => (η d).2
  have hfix : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ σ * ι d = ι d * σ := by
    intro d
    rw [hmemC]
    have h := hσ' (η d)
    rw [MulEquiv.symm_apply_apply] at h
    constructor
    · intro hd
      rw [hd] at h
      exact (mul_comm_of_conj_eq h.symm)
    · intro hd
      apply η.injective
      apply Subtype.ext
      rw [h]
      change σ * ι d * σ⁻¹ = ι d
      rw [hd, mul_inv_cancel_right]
  set S' := S.map ι with hS'def
  set M := alternatingGroup (Fin m) ⊓ centralizer ({σ} : Set (Perm (Fin m))) with hMdef
  have hS'M : S' ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hιA s, mem_centralizer_singleton_iff.2 ((hfix s).1 (hSα hs)).symm⟩
  have hS'n : (S'.subgroupOf M).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    have hgA : (g : Perm (Fin m)) ∈ alternatingGroup (Fin m) := (mem_inf.1 g.2).1
    have hgC : (g : Perm (Fin m)) ∈ centralizer ({σ} : Set (Perm (Fin m))) := (mem_inf.1 g.2).2
    have hcg : ι (η.symm ⟨g, hgA⟩) = g := by
      change ((η (η.symm ⟨g, hgA⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = g
      rw [MulEquiv.apply_symm_apply]
    have hcC : η.symm ⟨g, hgA⟩ ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) :=
      (hfix _).2 (by rw [hcg]; exact (mem_centralizer_singleton_iff.1 hgC).symm)
    have hmem := hSn.conj_mem ⟨s, hSα hs⟩ (mem_subgroupOf.2 hs) ⟨_, hcC⟩
    rw [mem_subgroupOf] at hmem
    refine ⟨_, hmem, ?_⟩
    change ι (η.symm ⟨g, hgA⟩ * s * (η.symm ⟨g, hgA⟩)⁻¹) =
      (g : Perm (Fin m)) * x * (g : Perm (Fin m))⁻¹
    rw [map_mul, map_mul, map_inv, hcg, hsx]
  have hMN : (M.subgroupOf (centralizer ({σ} : Set (Perm (Fin m))))).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨?_, ?_⟩
    · exact (inferInstance : (alternatingGroup (Fin m)).Normal).conj_mem _ hxA _
    · exact mul_mem (mul_mem g.2 hxC) (inv_mem g.2)
  have hS'q : CFSG.Assembly.IsQuasisimple S' := by
    have : IsSimpleGroup S := hSs
    have hSq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1
    rw [AssemblyBPredicates.isQuasisimple_iff_native]
    exact (isQuasisimple_congr (S.equivMapOfInjective ι hι)).1 hSq
  have hcomp : CFSG.Assembly.IsComponentOf S'
      (⊤ ⊓ normalizer ((zpowers σ : Subgroup (Perm (Fin m))) : Set (Perm (Fin m)))) := by
    rw [top_inf_eq, ← centralizer_singleton_eq_normalizer_zpowers hσ2]
    exact ⟨hS'M.trans inf_le_right, CFSG.Assembly.IsSubnormal.step hS'M hS'n
      (CFSG.Assembly.IsSubnormal.step inf_le_right hMN (CFSG.Assembly.IsSubnormal.refl _)),
      hS'q⟩
  obtain ⟨hF5', hS'eq⟩ := ordinary_permutation_local_component_fixed_support (T := ⊤) le_top
    Nat.prime_two le_top (isPGroup_zpowers_of_orderOf_eq_two hσ2) hcomp
  have hS'mem : ∀ g, g ∈ S' ↔ (∀ x, ¬ σ x = x → g x = x) ∧ Perm.sign g = 1 := by
    intro g
    classical
    rw [hS'eq, SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff]
    simp only [mem_fixedPoints_zpowers_iff]
  have hS'alt : S' = (alternatingGroup {x // σ x = x}).map Perm.ofSubtype := by
    ext g
    rw [hS'mem, SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff]
  have hF5 : 5 ≤ Nat.card {x // σ x = x} := by
    rwa [← Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixedPoints_zpowers_iff)]
  have hF : Nat.card {x // σ x = x} = 5 := by
    by_contra hne
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 6) (β := {x // σ x = x})
      (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
    let ι6 : Fin 6 ↪ Fin m := e.trans (Function.Embedding.subtype _)
    obtain ⟨g₀, hg₀4, hg₀2, hg₀s⟩ := exists_even_orderOf_eq_four_fin_six
    have hghom : g₀.viaFintypeEmbedding ι6 = Perm.extendDomainHom ι6.toEquivRange g₀ := rfl
    have hgord : orderOf (g₀.viaFintypeEmbedding ι6) = 4 := by
      rw [hghom, orderOf_injective _ (Perm.extendDomainHom_injective _) g₀]
      exact SteinbergCD.orderOf_eq_four hg₀4 hg₀2
    have hgS' : g₀.viaFintypeEmbedding ι6 ∈ S' := by
      rw [hS'mem]
      refine ⟨fun x hx => ?_, ?_⟩
      · apply Perm.viaFintypeEmbedding_apply_notMem_range
        rintro ⟨i, rfl⟩
        exact hx (e i).2
      · rw [Perm.viaFintypeEmbedding_sign]
        exact hg₀s
    obtain ⟨s, hs, hsg⟩ := hgS'
    have hsord : orderOf (⟨s, hs⟩ : S) = 4 := by
      rw [Subgroup.orderOf_mk, ← orderOf_injective ι hι s, hsg, hgord]
    exact SteinbergCD.SL_two_orderOf_ne_four h2K (φ ⟨s, hs⟩) (by rw [MulEquiv.orderOf_eq, hsord])
  have hS60 : Nat.card S = 60 := by
    rw [Nat.card_congr (S.equivMapOfInjective ι hι).toEquiv, ← hS'def, hS'alt,
      Subgroup.card_map_of_injective Perm.ofSubtype_injective]
    have : Nontrivial {x // σ x = x} := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    have h := two_mul_card_alternatingGroup (α := {x // σ x = x})
    rw [Fintype.card_perm, ← Nat.card_eq_fintype_card (α := {x // σ x = x}), hF,
      ← Nat.card_eq_fintype_card, show Nat.factorial 5 = 120 by decide] at h
    omega
  have hn2 : n = 2 := by
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have h := Nat.card_congr φ.toEquiv
    rw [hS60, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK] at h
    by_contra hne
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 h63
    omega
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have hab : a ≠ σ a := fun h => ha h.symm
  have hrest : ∀ c, c ≠ a → c ≠ σ a → σ c = c := by
    intro c hca hcb
    by_contra hc
    have hda : σ c ≠ a := fun h => hcb (by rw [← h, hσinv])
    have hdb : σ c ≠ σ a := fun h => hca (σ.injective h)
    have hdc : σ c ≠ c := hc
    have hxA : swap a (σ a) * swap c (σ c) ∈ alternatingGroup (Fin m) := by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hdc.symm]
      decide
    have hyA : swap a c * swap (σ a) (σ c) ∈ alternatingGroup (Fin m) := by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hca.symm, Perm.sign_swap hdb.symm]
      decide
    have hxσ : σ * (swap a (σ a) * swap c (σ c)) = swap a (σ a) * swap c (σ c) * σ := by
      refine mul_comm_of_conj_eq ?_
      rw [show σ * (swap a (σ a) * swap c (σ c)) * σ⁻¹ =
          (σ * swap a (σ a) * σ⁻¹) * (σ * swap c (σ c) * σ⁻¹) by group,
        ← swap_apply_apply, ← swap_apply_apply, hσinv, hσinv, swap_comm (σ a), swap_comm (σ c)]
    have hyσ : σ * (swap a c * swap (σ a) (σ c)) = swap a c * swap (σ a) (σ c) * σ := by
      refine mul_comm_of_conj_eq ?_
      rw [show σ * (swap a c * swap (σ a) (σ c)) * σ⁻¹ =
          (σ * swap a c * σ⁻¹) * (σ * swap (σ a) (σ c) * σ⁻¹) by group,
        ← swap_apply_apply, ← swap_apply_apply, hσinv, hσinv]
      exact swap_mul_swap_comm_of_ne ha hcb.symm hda hdc
    have hfixF : ∀ z, σ z = z → z ≠ a ∧ z ≠ σ a ∧ z ≠ c ∧ z ≠ σ c := by
      intro z hz
      refine ⟨fun h => ha (h ▸ hz), fun h => ?_, fun h => hc (h ▸ hz), fun h => ?_⟩
      · rw [h, hσinv] at hz
        exact hab hz
      · rw [h, hσinv] at hz
        exact hdc hz.symm
    have hcent : ∀ w : Perm (Fin m), (∀ z, σ z = z → w z = z) → ∀ t ∈ S', t * w = w * t := by
      intro w hw t ht
      refine (Perm.Disjoint.commute fun z => ?_).eq
      by_cases hz : σ z = z
      · exact Or.inr (hw z hz)
      · exact Or.inl ((hS'mem t).1 ht |>.1 z hz)
    have hxF : ∀ z, σ z = z → (swap a (σ a) * swap c (σ c)) z = z := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hfixF z hz
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
    have hyF : ∀ z, σ z = z → (swap a c * swap (σ a) (σ c)) z = z := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hfixF z hz
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4, swap_apply_of_ne_of_ne h1 h3]
    have hpre : ∀ w (hw : w ∈ alternatingGroup (Fin m)), σ * w = w * σ →
        (∀ z, σ z = z → w z = z) →
        η.symm ⟨w, hw⟩ ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D) := by
      intro w hw hwσ hwF
      have hιw : ι (η.symm ⟨w, hw⟩) = w := by
        change ((η (η.symm ⟨w, hw⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = w
        rw [MulEquiv.apply_symm_apply]
      refine mem_inf.2 ⟨(hfix _).2 (by rw [hιw]; exact hwσ), mem_centralizer_iff.2 fun t ht => ?_⟩
      apply hι
      rw [map_mul, map_mul, hιw]
      exact hcent w hwF (ι t) ⟨t, ht, rfl⟩
    have hx1 : swap a (σ a) * swap c (σ c) ≠ 1 := by
      intro h
      have h1 := congrArg (fun w : Perm (Fin m) => w a) h
      simp only [Perm.mul_apply, Perm.one_apply] at h1
      rw [swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left] at h1
      exact hab h1.symm
    have hy1 : swap a c * swap (σ a) (σ c) ≠ 1 := by
      intro h
      have h1 := congrArg (fun w : Perm (Fin m) => w a) h
      simp only [Perm.mul_apply, Perm.one_apply] at h1
      rw [swap_apply_of_ne_of_ne hab hda.symm, swap_apply_left] at h1
      exact hca h1
    have hxy : swap a (σ a) * swap c (σ c) ≠ swap a c * swap (σ a) (σ c) := by
      intro h
      have h1 := congrArg (fun w : Perm (Fin m) => w a) h
      simp only [Perm.mul_apply] at h1
      rw [swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left,
        swap_apply_of_ne_of_ne hab hda.symm, swap_apply_left] at h1
      exact hcb h1.symm
    have hxx : (swap a (σ a) * swap c (σ c)) * (swap a (σ a) * swap c (σ c)) = 1 :=
      mul_mul_self_of_commute (swap_mul_swap_comm_of_ne hca.symm hda.symm hcb.symm hdb.symm)
        (swap_mul_self _ _) (swap_mul_self _ _)
    have hyy : (swap a c * swap (σ a) (σ c)) * (swap a c * swap (σ a) (σ c)) = 1 :=
      mul_mul_self_of_commute (swap_mul_swap_comm_of_ne hab hda.symm hcb hdc.symm)
        (swap_mul_self _ _) (swap_mul_self _ _)
    have hxa : (swap a (σ a) * swap c (σ c)) a = σ a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left]
    have hxb : (swap a (σ a) * swap c (σ c)) (σ a) = a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcb.symm hdb.symm, swap_apply_right]
    have hxc : (swap a (σ a) * swap c (σ c)) c = σ c := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hda hdb]
    have hxd : (swap a (σ a) * swap c (σ c)) (σ c) = c := by
      rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hca hcb]
    have hxyc : (swap a (σ a) * swap c (σ c)) * (swap a c * swap (σ a) (σ c)) =
        (swap a c * swap (σ a) (σ c)) * (swap a (σ a) * swap c (σ c)) := by
      refine mul_comm_of_conj_eq ?_
      rw [show (swap a (σ a) * swap c (σ c)) * (swap a c * swap (σ a) (σ c)) *
          (swap a (σ a) * swap c (σ c))⁻¹ =
          ((swap a (σ a) * swap c (σ c)) * swap a c * (swap a (σ a) * swap c (σ c))⁻¹) *
          ((swap a (σ a) * swap c (σ c)) * swap (σ a) (σ c) * (swap a (σ a) * swap c (σ c))⁻¹)
          by group, ← swap_apply_apply, ← swap_apply_apply, hxa, hxc, hxb, hxd]
      exact swap_mul_swap_comm_of_ne ha hcb.symm hda hdc
    have hιpre : ∀ w (hw : w ∈ alternatingGroup (Fin m)), ι (η.symm ⟨w, hw⟩) = w := fun w hw => by
      change ((η (η.symm ⟨w, hw⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = w
      rw [MulEquiv.apply_symm_apply]
    obtain ⟨Q, hQ, hQp, hQ3⟩ := exists_isPGroup_two_le_of_commute (hpre _ hxA hxσ hxF)
      (hpre _ hyA hyσ hyF)
      (hι (by rw [map_mul, hιpre, map_one, hxx]))
      (hι (by rw [map_mul, hιpre, map_one, hyy]))
      (hι (by rw [map_mul, map_mul, hιpre, hιpre, hxyc]))
      (fun h => hx1 (by
        have := congrArg (fun d => ι d) h
        simpa [ι] using this))
      (fun h => hy1 (by
        have := congrArg (fun d => ι d) h
        simpa [ι] using this))
      (fun h => hxy (by
        have := congrArg (fun d => ι d) h
        simpa [ι] using this))
    have := (hr Q hQ hQp).1
    omega
  have hσswap : σ = swap a (σ a) := by
    ext z
    by_cases hza : z = a
    · rw [hza, swap_apply_left]
    by_cases hzb : z = σ a
    · rw [hzb, swap_apply_right, hσinv]
    · rw [swap_apply_of_ne_of_ne hza hzb, hrest z hza hzb]
  have hm7 : m = 7 := by
    have h1 := Perm.card_fixedPoints σ
    rw [Perm.sum_cycleType, Fintype.card_fin] at h1
    have h2 : σ.support.card = 2 := by
      rw [hσswap]
      exact Perm.card_support_swap hab
    have h3 : Fintype.card (Function.fixedPoints σ) = 5 := by
      rw [← hF, Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    have h4 : σ.support.card ≤ m := by
      have := Finset.card_le_univ σ.support
      rwa [Fintype.card_fin] at this
    omega
  have hout : α ∉ (MulAut.conj : D →* MulAut D).range := by
    rintro ⟨d, hd⟩
    have hτ : ∀ g : alternatingGroup (Fin m),
        (η (α (η.symm g)) : Perm (Fin m)) = ι d * g * (ι d)⁻¹ := by
      intro g
      rw [← hd, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    have hsign : Perm.sign σ = 1 := by
      rw [← huniq (ι d) hτ]
      exact hιA d
    rw [hσswap, Perm.sign_swap hab] at hsign
    exact absurd hsign (by decide)
  exact ⟨hm7, hn2, hout, σ, hσ', huniq, ⟨a, σ a, hab, hσswap⟩, hF, hS'alt⟩


theorem alternating_six_fixed_SL2_false {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K]
    (hK : Nat.card K = 2 ^ n) {D : Type*} [Group D] [Finite D]
    (η : D ≃* alternatingGroup (Fin 6)) (α : MulAut D) (hα : orderOf α = 2) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (φ : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hD : IsSimpleGroup D := η.isSimpleGroup
  have hcardD : Nat.card D = 360 := by
    rw [Nat.card_congr η.toEquiv, Nat.card_eq_fintype_card]
    have h := two_mul_card_alternatingGroup (α := Fin 6)
    rw [Fintype.card_perm, Fintype.card_fin, show Nat.factorial 6 = 720 by decide] at h
    omega
  have hcardS : Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
  have hle : Nat.card S ≤ 360 := hcardD ▸ Subgroup.card_le_card_group S
  have hn2 : n = 2 := by
    by_contra hne
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 h63
    omega
  subst hn2
  have := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    sl2_isSimpleGroup (two_eq_zero_of_card (by norm_num) hK2) (by rw [hK2]; norm_num)
  have hα1 := eq_one_of_forall_fixed_of_card_sixty hD hcardD φ.isSimpleGroup
    (by rw [hcardS]; norm_num) α fun s hs => hSα hs
  rw [hα1, orderOf_one] at hα
  omega

theorem fixedRootSelector_alternating :
    FixedRootSelector fun D _ => ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)) := by
  intro D _ _ _ ⟨m, hm, ⟨η⟩⟩ n hn K _ _ hK α hα S hSα hSn ⟨φ⟩ hr
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  by_cases hm6 : m = 6
  · subst hm6
    exact (alternating_six_fixed_SL2_false hn K hK' η α hα S hSα φ).elim
  · obtain ⟨hm7, hn2, -⟩ :=
      alternating_involution_normal_even_SL2_fixed_support_rankOne_selector hn K hK' hm hm6 η α
        hα S hSα hSn φ hr
    subst hm7
    subst hn2
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨η⟩))⟩)))

end CFSG.LocalAnalysis.EvenBN.GMSK
