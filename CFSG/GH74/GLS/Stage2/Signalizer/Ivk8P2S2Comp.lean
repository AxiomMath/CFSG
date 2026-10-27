module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74.GLS

section CaseA

theorem pPrimeCoreOf_eq_inf {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.IsSubnormal) : pPrimeCoreOf 2 N = N ⊓ pPrimeCore 2 X := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ 2} hN
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore] at h
  exact h

theorem normal_centralizer_of_normal {X : Type*} [Group X] (O : Subgroup X) [O.Normal] :
    (centralizer (O : Set X)).Normal := ⟨fun v hv g o ho => by
  have ho' : g⁻¹ * o * g ∈ O := by
    have := (inferInstance : O.Normal).conj_mem o ho g⁻¹
    simpa using this
  have h1 := (mem_centralizer_iff.mp hv) _ ho'
  calc o * (g * v * g⁻¹) = g * ((g⁻¹ * o * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * o * g)) * g⁻¹ := by rw [h1]
    _ = g * v * g⁻¹ * o := by group⟩

theorem perfect_le_centralizer_of_decomp {X : Type} [Group X] [Finite X] {O : Subgroup X}
    [O.Normal] (hO : Odd (Nat.card O)) {L : Subgroup X} (hLp : ⁅L, L⁆ = L)
    (hdec : ∀ l ∈ L, ∃ v ∈ centralizer (O : Set X), ∃ o ∈ O, l = v * o) :
    L ≤ centralizer (O : Set X) := by
  set C : Subgroup X := centralizer (O : Set X) with hC
  have hCn : C.Normal := normal_centralizer_of_normal O
  set ρ : X →* X ⧸ C := QuotientGroup.mk' C with hρ
  have hle : L.map ρ ≤ O.map ρ := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨v, hv, o, ho, rfl⟩ := hdec l hl
    refine ⟨o, ho, ?_⟩
    have hv1 : ρ v = 1 := (QuotientGroup.eq_one_iff v).mpr hv
    rw [map_mul, hv1, one_mul]
  have hsolvO : Group.IsSolvable (O.map ρ) := by
    have : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hO
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective O)
  have hsolvL : Group.IsSolvable (L.map ρ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hperf : ⁅L.map ρ, L.map ρ⁆ = L.map ρ := by rw [← Subgroup.map_commutator, hLp]
  have hbot : L.map ρ = ⊥ := by
    by_contra hne
    have : Nontrivial (L.map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hpf : Group.IsPerfect (L.map ρ) := Subgroup.isPerfect_iff.mpr hperf
    exact Group.IsPerfect.not_isSolvable (L.map ρ) hsolvL
  intro l hl
  have h1 : ρ l ∈ L.map ρ := ⟨l, hl, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff l).mp h1



theorem keyA {X : Type} [Group X] [Finite X] {L : Subgroup X} (hL : IsPComponent 2 L)
    (hnq : ¬ pPrimeCoreOf 2 L ≤ centralizer (L : Set X)) {v : X}
    (hv : v ∈ centralizer (pPrimeCore 2 X : Set X)) :
    v ∈ normalizer (L : Set X) ∧ (∀ k ∈ L, k * v * k⁻¹ * v⁻¹ ∈ pPrimeCoreOf 2 L) ∧
      ∀ x ∈ pPrimeCoreOf 2 L, v * x * v⁻¹ ∈ pPrimeCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL' := hL
  set O := pPrimeCore 2 X with hO
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  set V : Subgroup X := centralizer (O : Set X) with hV
  have hVn : V.Normal := normal_centralizer_of_normal O
  obtain ⟨K, hK, hLsub, hLK, -⟩ := hL
  have hWL : pPrimeCoreOf 2 L = L ⊓ O := pPrimeCoreOf_eq_inf hLsub
  have hVbn : (V.map π).Normal := hVn.map π (QuotientGroup.mk'_surjective O)
  have hdich := CFSG.LocalCores.component_subnormal_subgroup hK hVbn.isSubnormal
  have hKV : ¬ K ≤ V.map π := by
    intro hKV
    apply hnq
    have hdec : ∀ l ∈ L, ∃ v' ∈ centralizer (O : Set X), ∃ o ∈ O, l = v' * o := by
      intro l hl
      have h1 : π l ∈ V.map π := hKV (hLK ▸ Subgroup.mem_map_of_mem π hl)
      obtain ⟨v', hv', hv'eq⟩ := h1
      refine ⟨v', hv', v'⁻¹ * l, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv]
      have : π v' = π l := hv'eq
      rw [this, inv_mul_cancel]
    have hLp : ⁅L, L⁆ = L :=
      Subgroup.isPerfect_iff.mp
        (CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 L hL')
    have hOodd : Odd (Nat.card O) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
    have hLC := perfect_le_centralizer_of_decomp hOodd hLp hdec
    intro w hw
    rw [hWL] at hw
    rw [mem_centralizer_iff]
    intro l hl
    exact (mem_centralizer_iff.mp (hLC hl) w hw.2).symm
  have hcomm : ⁅K, V.map π⁆ = ⊥ := hdich.resolve_left hKV
  have hKc : K ≤ centralizer ((V.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hπv : π v ∈ V.map π := Subgroup.mem_map_of_mem π hv
  have hπvc : ∀ y ∈ K, y * π v = π v * y := fun y hy =>
    (mem_centralizer_iff.mp (hKc hy) (π v) hπv).symm
  have hπvN : π v ∈ normalizer ((L.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
    rw [hLK]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro y hy
    exact hπvc y hy
  have hvN : v ∈ normalizer (L : Set X) :=
    CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hL' hπvN
  refine ⟨hvN, fun k hk => ?_, fun x hx => ?_⟩
  swap
  · rw [hWL] at hx ⊢
    exact ⟨(mem_normalizer_iff.mp hvN x).mp hx.1,
      (inferInstance : O.Normal).conj_mem x hx.2 v⟩
  rw [hWL]
  refine ⟨?_, ?_⟩
  · have h1 : v * k⁻¹ * v⁻¹ ∈ L := (mem_normalizer_iff.mp hvN k⁻¹).mp (L.inv_mem hk)
    have := L.mul_mem hk h1
    simpa [mul_assoc] using this
  · show k * v * k⁻¹ * v⁻¹ ∈ O
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
    have hkK : π k ∈ K := hLK ▸ Subgroup.mem_map_of_mem π hk
    have hc := hπvc (π k) hkK
    simp only [map_mul, map_inv]
    calc π k * π v * (π k)⁻¹ * (π v)⁻¹ = (π v * π k) * (π k)⁻¹ * (π v)⁻¹ := by rw [← hc]
      _ = 1 := by group

theorem two_le_pRank_of_two_involutions {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {z u : G} (hz : orderOf z = 2) (hu : orderOf u = 2) (hzu : z ≠ u) (hc : z * u = u * z)
    (hzK : z ∈ K) (huK : u ∈ K) : 2 ≤ CFSG.pRank 2 ↥K := by
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hu2 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have hZ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hz2
  have hU := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hu2
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers u, a * b = b * a := by
    rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    exact ((Commute.zpow_zpow (show Commute z u from hc) m n)).eq
  have hA := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hZ hU hcomm
  obtain ⟨j, hj⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_two hA
  have hAK : zpowers z ⊔ zpowers u ≤ K := sup_le (zpowers_le.2 hzK) (zpowers_le.2 huK)
  have huz : u ∉ zpowers z := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : z ^ n = z ^ (n % 2) := by
      rw [← zpow_mod_orderOf, hz]
      norm_num
    rcases Int.emod_two_eq_zero_or_one n with h0 | h0
    · rw [h0, zpow_zero] at h1
      rw [h1] at hn
      have : orderOf u = 1 := by rw [← hn]; exact orderOf_one
      omega
    · rw [h0, zpow_one] at h1
      rw [h1] at hn
      exact hzu hn
  have hlt : zpowers z < zpowers z ⊔ zpowers u :=
    lt_of_le_of_ne le_sup_left
      (fun heq => huz (heq ▸ (le_sup_right : zpowers u ≤ _) (mem_zpowers u)))
  have h1 := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hz, hj] at h1
  have hj2 : 2 ≤ j := by
    by_contra hlt2
    interval_cases j <;> simp at h1
  have h2 := CFSG.GH74.Uniqueness.SU.SU1.le_pRank (p := 2) one_lt_two hAK hA hj
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two]
  omega

end CaseA

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
