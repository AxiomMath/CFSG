module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.GroupTheory.SubnormalJoin
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43H
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43N
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsSingle
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

section Group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_conjugate_eq {K : Subgroup G} {g : G} (h : conjugate K g = K) :
    g ∈ normalizer (K : Set G) := by
  have h1 : g⁻¹ ∈ normalizer (K : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  simpa using inv_mem h1

omit [Finite G] in
theorem mem_conjugate_iff_held {K : Subgroup G} {g y : G} :
    y ∈ conjugate K g ↔ g * y * g⁻¹ ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro hy
    exact ⟨_, hy, by simp [mul_assoc]⟩

theorem even_card_heP : Even (Nat.card heP) := by
  rw [card_heP]
  decide

theorem exists_mul_ne_heP :
    ∃ x y : ↥heP, x * y ≠ y * x := by
  obtain ⟨u, v, huv⟩ := exists_mul_ne_held
  refine ⟨heEquivP u, heEquivP v, fun h => huv (heEquivP.injective ?_)⟩
  rw [map_mul, map_mul, h]

omit [Finite G] in
theorem exists_held_of_subgroupOf {M : Subgroup G} {a : G} (haM : a ∈ M)
    (hCM : centralizer ({a} : Set G) ≤ M) {Q : Type*} [Mul Q] {L : Subgroup ↥M}
    (hLC : L ≤ centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M))))
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* Q) :
    ∃ L' : Subgroup G, L' ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (L'.subgroupOf (centralizer ({a} : Set G))) ∧
      Nonempty (↥L' ⧸ pPrimeCore 2 ↥L' ≃* Q) := by
  have hmapC : (centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map M.subtype =
      centralizer ({a} : Set G) :=
    (map_centralizer_subtype M ⟨a, haM⟩).trans (inf_eq_right.mpr hCM)
  refine ⟨L.map M.subtype, hmapC ▸ map_mono hLC, ?_,
    ⟨(Sol78.coreQuotCongr (L.equivMapOfInjective M.subtype M.subtype_injective)).symm.trans e⟩⟩
  rw [← hmapC]
  exact (CatFactsSp4.isPComponent_map_subgroupOf_iff 2 M.subtype M.subtype_injective hLC).mpr hL

theorem exists_held_of_mem_coreActionKernel
    {M K : Subgroup G} {a : G}
    (haa : a * a = 1) (hCM : centralizer ({a} : Set G) ≤ M)
    (hKc : IsPComponent 2 (K.subgroupOf M))
    (e : ↥K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He) (haK : a ∈ coreActionKernel K) :
    ∃ L : Subgroup G, L ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set G))) ∧
      Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) := by
  have : IsSimpleGroup heP := heP_simple
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set C : Subgroup G := centralizer ({a} : Set G) with hC
  set H : Subgroup G := K ⊓ C with hH
  have hsub : (H.subgroupOf C).IsSubnormal := by
    have h := (hKc.choose_spec.2.1).comap (Subgroup.inclusion hCM)
    convert h using 1
    ext x
    simp only [hH, mem_subgroupOf, mem_inf, mem_comap, coe_inclusion]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  let ψ : ↥H →* ↥heP := (heModelL e).comp (Subgroup.inclusion inf_le_left)
  have hψs : Function.Surjective ψ := by
    intro p
    obtain ⟨k, hk⟩ := heModelL_surjective e p
    have h1 : (k : G)⁻¹ * (a * k * a⁻¹) ∈ (pPrimeCore 2 ↥K).map K.subtype := by
      have h2 := (mem_coreActionKernel.mp haK).2 k k.2
      rw [hai] at h2 ⊢
      simpa only [mul_assoc] using h2
    obtain ⟨o, ho, hko⟩ := exists_commute_mul_mem (odd_card_map_pPrimeCore K) haa h1
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    refine ⟨⟨k * o', mem_inf.mpr ⟨mul_mem k.2 o'.2,
      mem_centralizer_singleton_iff.mpr hko.symm⟩⟩, ?_⟩
    change heModelL e (k * o') = p
    rw [map_mul, (heModelL_eq_one_iff e o').mpr ho', mul_one, hk]
  have hodd : Odd (Nat.card ψ.ker) := by
    have hle : ψ.ker.map H.subtype ≤ oddIn K := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (heModelL_eq_one_iff e _).mp (MonoidHom.mem_ker.mp hy), rfl⟩
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact (odd_card_map_pPrimeCore K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  obtain ⟨L, hLH, hL, ⟨eL⟩⟩ := exists_isPComponent_of_surjective exists_mul_ne_heP
    even_card_heP (inf_le_right : H ≤ C) hsub ψ hψs hodd
  exact ⟨L, hLH.trans inf_le_right, hL, ⟨eL.trans heEquivP.symm⟩⟩

end Group

section InGroup

variable {X : Type} [Group X] [Finite X]

theorem exists_held_of_conjugate_ne_in {K : Subgroup X} {a : X} (haa : a * a = 1)
    (hKc : IsPComponent 2 K) (e : ↥K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (hne : conjugate K a ≠ K) :
    ∃ L : Subgroup X, L ≤ centralizer ({a} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) ∧
      Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup heP := heP_simple
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set K₂ : Subgroup X := conjugate K a with hK₂
  have hconj : ∀ {y : X}, y ∈ K → a * y * a⁻¹ ∈ K₂ := fun {y} hy => by
    rw [mem_conjugate_iff_held, hai]
    simpa only [mul_assoc, haa, mul_one, ← mul_assoc a a, one_mul] using hy
  have hK₂c : IsPComponent 2 K₂ :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj a⁻¹) hKc
  obtain ⟨h21, -, hcomm⟩ :=
    CatalogueBPrimeJoin.mutual_normalization_core_commutation 2 K K₂ hKc hK₂c (Ne.symm hne)
  have hK₂ker : K₂ ≤ coreActionKernel K := by
    intro y hy
    refine mem_coreActionKernel.mpr ⟨h21 hy, fun j hj => ?_⟩
    have h1 := (mem_inf.mp (hcomm (commutator_mem_commutator (inv_mem hj) (inv_mem hy)))).1
    rwa [commutatorElement_def, inv_inv, inv_inv] at h1
  set N : Subgroup X := K ⊔ K₂ with hN
  set C : Subgroup X := centralizer ({a} : Set X) with hC
  set H : Subgroup X := N ⊓ C with hH
  have hNK : N ≤ normalizer (K : Set X) := sup_le le_normalizer h21
  have hNP : N ≤ K ⊔ coreActionKernel K := sup_le le_sup_left (hK₂ker.trans le_sup_right)
  have hHN : ∀ y : ↥H, (y : X) ∈ normalizer (K : Set X) := fun y => hNK (mem_inf.mp y.2).1
  let ψ₀ : ↥H →* ↥heP :=
    { toFun := fun y => ⟨heN e y, (heN_mem_heP_iff (hHN y)).mpr (hNP (mem_inf.mp y.2).1)⟩
      map_one' := Subtype.ext ((heN_eq_one_iff (one_mem _)).mpr (one_mem _))
      map_mul' := fun y z => Subtype.ext (heN_mul (hHN y) (hHN z)) }
  have hψs : Function.Surjective ψ₀ := by
    intro q
    obtain ⟨k, hk, hkp⟩ := exists_heL_eq (e := e) q.2
    have hk₂ : a * k * a⁻¹ ∈ K₂ := hconj hk
    have h1 : (k * (a * k * a⁻¹))⁻¹ * (a * (k * (a * k * a⁻¹)) * a⁻¹) ∈
        (pPrimeCore 2 ↥K).map K.subtype := by
      have h2 : a * (k * (a * k * a⁻¹)) * a⁻¹ = a * k * a⁻¹ * k := by
        simp only [hai, mul_assoc, haa, mul_one]
      have h3 : (k * (a * k * a⁻¹))⁻¹ * (a * k * a⁻¹ * k) = ⁅(a * k * a⁻¹)⁻¹, k⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      have h4 : ⁅(a * k * a⁻¹)⁻¹, k⁻¹⁆ ∈ ⁅K, K₂⁆ := by
        rw [Subgroup.commutator_comm]
        exact commutator_mem_commutator (inv_mem hk₂) (inv_mem hk)
      rw [h2, h3]
      exact (mem_inf.mp (hcomm h4)).1
    obtain ⟨o, ho, hco⟩ := exists_commute_mul_mem (odd_card_map_pPrimeCore K) haa h1
    have hoK : o ∈ K := map_subtype_le _ ho
    have hyN : k * (a * k * a⁻¹) * o ∈ N :=
      mul_mem (mul_mem (mem_sup_left hk) (mem_sup_right hk₂)) (mem_sup_left hoK)
    refine ⟨⟨_, mem_inf.mpr ⟨hyN, mem_centralizer_singleton_iff.mpr hco.symm⟩⟩, ?_⟩
    apply Subtype.ext
    change heN e (k * (a * k * a⁻¹) * o) = _
    rw [heN_mul (mul_mem (le_normalizer hk) (h21 hk₂)) (le_normalizer hoK),
      heN_mul (le_normalizer hk) (h21 hk₂), heN_eq_heL hk, hkp,
      (heN_eq_one_iff (h21 hk₂)).mpr (hK₂ker hk₂), heN_eq_heL hoK, (heL_eq_one_iff hoK).mpr ho,
      mul_one, mul_one]
  have hodd : Odd (Nat.card ψ₀.ker) := by
    set O₁ : Subgroup X := oddIn K with hO₁
    set O₂ : Subgroup X := conjugate O₁ a with hO₂
    have hO₂K₂ : O₂ ≤ K₂ := map_mono (map_subtype_le _)
    have hO₂N : O₂ ≤ normalizer (O₁ : Set X) := fun y hy =>
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 ↥K)
        (h21 (hO₂K₂ hy))
    have hO₂odd : Odd (Nat.card O₂) := by
      rw [hO₂, conjugate, Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective]
      exact odd_card_map_pPrimeCore K
    have hle : ψ₀.ker.map H.subtype ≤ O₁ ⊔ O₂ := by
      rintro _ ⟨y, hy, rfl⟩
      have hy1 : heN e (y : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ : ∃ k₁ ∈ K, ∃ k₂ ∈ K₂, k₁ * k₂ = (y : X) := by
        have h1 : (y : X) ∈ ((K ⊔ K₂ : Subgroup X) : Set X) := (mem_inf.mp y.2).1
        rw [coe_mul_of_right_le_normalizer_left K K₂ h21] at h1
        obtain ⟨k₁, hk₁, k₂, hk₂, h⟩ := h1
        exact ⟨k₁, hk₁, k₂, hk₂, h⟩
      have hk₁O : k₁ ∈ O₁ := by
        rw [← hkk, heN_mul (le_normalizer hk₁) (h21 hk₂), heN_eq_heL hk₁,
          (heN_eq_one_iff (h21 hk₂)).mpr (hK₂ker hk₂), mul_one] at hy1
        exact (heL_eq_one_iff hk₁).mp hy1
      have hya : a * (y : X) * a⁻¹ = y := by
        rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).2, mul_inv_cancel_right]
      have hk₂' : a * k₂ * a⁻¹ ∈ K := mem_conjugate_iff_held.mp hk₂
      have hk₁' : a * k₁ * a⁻¹ ∈ K₂ := hconj hk₁
      have h3 : heN e (y : X) = heL e (a * k₂ * a⁻¹) := by
        rw [← hya, ← hkk, show a * (k₁ * k₂) * a⁻¹ = a * k₁ * a⁻¹ * (a * k₂ * a⁻¹) by group,
          heN_mul (h21 hk₁') (le_normalizer hk₂'), (heN_eq_one_iff (h21 hk₁')).mpr (hK₂ker hk₁'),
          one_mul, heN_eq_heL hk₂']
      have hk₂O : a * k₂ * a⁻¹ ∈ O₁ := (heL_eq_one_iff hk₂').mp (h3 ▸ hy1)
      have hk₂O₂ : k₂ ∈ O₂ := mem_conjugate_iff_held.mpr hk₂O
      show (y : X) ∈ O₁ ⊔ O₂
      rw [← hkk]
      exact mul_mem (mem_sup_left hk₁O) (mem_sup_right hk₂O₂)
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact (odd_card_sup_held hO₂N (odd_card_map_pPrimeCore K) hO₂odd).of_dvd_nat
      (Subgroup.card_dvd_of_le hle)
  have hsub : (H.subgroupOf C).IsSubnormal := by
    rw [hH, inf_subgroupOf_right]
    exact (CFSG.GroupTheory.isSubnormal_sup hKc.choose_spec.2.1 hK₂c.choose_spec.2.1).subgroupOf
  obtain ⟨L, hLH, hL, ⟨eL⟩⟩ := exists_isPComponent_of_surjective exists_mul_ne_heP
    even_card_heP (inf_le_right : H ≤ C) hsub ψ₀ hψs hodd
  exact ⟨L, hLH.trans inf_le_right, hL, ⟨eL.trans heEquivP.symm⟩⟩

end InGroup

theorem exists_held_of_not_mem_normalizer {G : Type} [Group G] [Finite G]
    {M K : Subgroup G} {a : G} (haM : a ∈ M) (haa : a * a = 1)
    (hCM : centralizer ({a} : Set G) ≤ M) (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M))
    (e : ↥K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (haK : a ∉ normalizer (K : Set G)) :
    ∃ L : Subgroup G, L ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set G))) ∧
      Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) := by
  have haa' : (⟨a, haM⟩ : ↥M) * ⟨a, haM⟩ = 1 := Subtype.ext haa
  have hne : conjugate (K.subgroupOf M) ⟨a, haM⟩ ≠ K.subgroupOf M := by
    intro h
    apply haK
    have h1 := congrArg (map M.subtype) h
    rw [map_conjugate_subtype, map_subgroupOf_subtype hKM] at h1
    exact mem_normalizer_of_conjugate_eq h1
  obtain ⟨L, hLC, hL, ⟨eL⟩⟩ := exists_held_of_conjugate_ne_in haa' hKc
    ((Sol78.coreQuotCongr (subgroupOfEquivOfLe hKM)).trans e) hne
  exact exists_held_of_subgroupOf haM hCM hLC hL eL

end CFSG.ComponentClassification.GrSLit.GrS4
