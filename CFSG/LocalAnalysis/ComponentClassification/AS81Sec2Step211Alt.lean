module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Action

variable {G : Type} [Group G]

@[expose] def sec2PlanesP (E F : Subgroup G) : Set (Subgroup G) :=
  {V | V ∈ planes E F ∧ V ≤ sec2P E}

theorem normalizer_sec2P_le_conjSetStab (E F : Subgroup G) :
    normalizer (sec2P E : Set G) ≤ Sec2.conjSetStab (sec2PlanesP E F) :=
  Sec2.le_conjSetStab fun _ hn _ hV => rightConjugate_mem_planes_sec2P hV.1 hV.2 hn

@[expose] noncomputable def sec2PlanesActionFin (E F : Subgroup G)
    (e : ↥(sec2PlanesP E F) ≃ Fin 6) : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 6) :=
  (Equiv.permCongrHom e).toMonoidHom.comp
    (Sec2.conjPermHom (normalizer_sec2P_le_conjSetStab E F))

theorem coe_symm_sec2PlanesActionFin_apply (E F : Subgroup G) (e : ↥(sec2PlanesP E F) ≃ Fin 6)
    (n : ↥(normalizer (sec2P E : Set G))) (i : Fin 6) :
    ((e.symm (sec2PlanesActionFin E F e n i) : ↥(sec2PlanesP E F)) : Subgroup G) =
      rightConjugate (e.symm i : Subgroup G) (n : G)⁻¹ := by
  simp only [sec2PlanesActionFin, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact Sec2.conjPermHom_apply _ n (e.symm i)

theorem sec2PlanesActionFin_apply_eq_iff (E F : Subgroup G) (e : ↥(sec2PlanesP E F) ≃ Fin 6)
    (n : ↥(normalizer (sec2P E : Set G))) (i : Fin 6) :
    sec2PlanesActionFin E F e n i = i ↔ (n : G) ∈ normalizer ((e.symm i : Subgroup G) : Set G) := by
  constructor
  · intro h
    have h1 := coe_symm_sec2PlanesActionFin_apply E F e n i
    rw [h] at h1
    exact (normalizer _).inv_mem_iff.mp ((rightConjugate_eq_self_iff _ _).mp h1.symm)
  · intro h
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_sec2PlanesActionFin_apply]
    exact (rightConjugate_eq_self_iff _ _).mpr (inv_mem h)

end Action

theorem isThreeCycle_of_pow_three_of_fix {σ : Equiv.Perm (Fin 6)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    {a b : Fin 6} (hab : a ≠ b) (ha : σ a = a) (hb : σ b = b) : σ.IsThreeCycle := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_three)
  have hsum := Equiv.Perm.sum_cycleType σ
  have hsub : σ.support ⊆ Finset.univ \ {a, b} := fun y hy => by
    rw [Equiv.Perm.mem_support] at hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    exact ⟨fun h => hy (h ▸ ha), fun h => hy (h ▸ hb)⟩
  have hcard : σ.support.card ≤ 4 := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hab] at h
    exact h
  rw [hn, hord, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hn0 : n = 0 := by omega
  rw [Equiv.Perm.IsThreeCycle, hn, hn0, hord]
  rfl

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) (e : ↥(sec2PlanesP E F) ≃ Fin 6)

include h11 hE16 hF hL hodd hx hxS h4

theorem isMultiplyPretransitive_two_range :
    MulAction.IsMultiplyPretransitive (sec2PlanesActionFin E F e).range (Fin 6) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  have hEpl : E ∈ sec2PlanesP E F := ⟨⟨1, Or.inl (rightConjugate_one E).symm⟩, le_sec2P_of_frame hF⟩
  have hto : ∀ i : Fin 6, ∃ n : ↥(normalizer (sec2P E : Set G)),
      sec2PlanesActionFin E F e n i = e ⟨E, hEpl⟩ := by
    intro i
    obtain ⟨n, hn, hnE⟩ := exists_mem_normalizer_rightConjugate_eq h11 hE16 hF hL hodd hx hxS h4
      (e.symm i).2.1 (e.symm i).2.2 hEpl.1 hEpl.2
    refine ⟨⟨n⁻¹, inv_mem hn⟩, ?_⟩
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_sec2PlanesActionFin_apply, Equiv.symm_apply_apply]
    simpa using hnE
  intro a b c d hab hcd
  obtain ⟨n, hn⟩ := hto a
  obtain ⟨m, hm⟩ := hto c
  set i := sec2PlanesActionFin E F e n b
  set j := sec2PlanesActionFin E F e m d
  have hi : i ≠ e ⟨E, hEpl⟩ := fun h =>
    hab ((sec2PlanesActionFin E F e n).injective (hn.trans h.symm))
  have hj : j ≠ e ⟨E, hEpl⟩ := fun h =>
    hcd ((sec2PlanesActionFin E F e m).injective (hm.trans h.symm))
  have hVi : ((e.symm i : ↥(sec2PlanesP E F)) : Subgroup G) ≠ E := fun h =>
    hi (by rw [← Equiv.apply_symm_apply e i]; exact congrArg e (Subtype.ext h))
  have hVj : ((e.symm j : ↥(sec2PlanesP E F)) : Subgroup G) ≠ E := fun h =>
    hj (by rw [← Equiv.apply_symm_apply e j]; exact congrArg e (Subtype.ext h))
  obtain ⟨h, hh, hhV⟩ := exists_mem_normalizer_rightConjugate_eq_of_ne h11 hE16 hF hL hodd hx hxS
    (e.symm i).2.1 (e.symm i).2.2 hVi (e.symm j).2.1 (e.symm j).2.2 hVj
  set k : ↥(normalizer (sec2P E : Set G)) :=
    ⟨h⁻¹, inv_mem (Sec2.normalizer_le_normalizer_sec2P E hh)⟩
  have hkE : sec2PlanesActionFin E F e k (e ⟨E, hEpl⟩) = e ⟨E, hEpl⟩ := by
    rw [sec2PlanesActionFin_apply_eq_iff, Equiv.symm_apply_apply]
    exact inv_mem hh
  have hki : sec2PlanesActionFin E F e k i = j := by
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_sec2PlanesActionFin_apply]
    change rightConjugate _ (h⁻¹)⁻¹ = _
    rw [inv_inv]
    exact hhV
  refine ⟨⟨sec2PlanesActionFin E F e (m⁻¹ * k * n), ⟨_, rfl⟩⟩, ?_, ?_⟩
  · show sec2PlanesActionFin E F e (m⁻¹ * k * n) a = c
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hn, hkE, map_inv,
      Equiv.Perm.inv_eq_iff_eq, hm]
  · show sec2PlanesActionFin E F e (m⁻¹ * k * n) b = d
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hki, map_inv,
      Equiv.Perm.inv_eq_iff_eq]

theorem isThreeCycle_sec2PlanesActionFin_sec2U {u : G}
    (huA : u ∈ A ⊓ normalizer (sec2S A R E F : Set G)) (hu3 : orderOf u = 3)
    (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e) :
    ∃ hu : u ∈ normalizer (sec2P E : Set G),
      (sec2PlanesActionFin E F e ⟨u, hu⟩).IsThreeCycle := by
  obtain ⟨huEn, huF, -, -⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  have huP := Sec2.normalizer_le_normalizer_sec2P E huEn
  refine ⟨huP, ?_⟩
  have hEpl : E ∈ sec2PlanesP E F :=
    ⟨⟨1, Or.inl (rightConjugate_one E).symm⟩, le_sec2P_of_frame hF⟩
  have hF0pl : sec2F0 A E x ∈ sec2PlanesP E F :=
    ⟨sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4, sec2F0_le_sec2P hF x⟩
  have hF0E : sec2F0 A E x ≠ E := by
    have h := rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS (Subgroup.one_mem _)
    rwa [rightConjugate_one] at h
  have h3 : sec2PlanesActionFin E F e ⟨u, huP⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨u, huP⟩ : ↥(normalizer (sec2P E : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simp [← hu3, pow_orderOf_eq_one])
    rw [this, map_one]
  have hfixE : sec2PlanesActionFin E F e ⟨u, huP⟩ (e ⟨E, hEpl⟩) = e ⟨E, hEpl⟩ := by
    rw [sec2PlanesActionFin_apply_eq_iff, Equiv.symm_apply_apply]
    exact huEn
  have hfixF0 : sec2PlanesActionFin E F e ⟨u, huP⟩ (e ⟨_, hF0pl⟩) = e ⟨_, hF0pl⟩ := by
    rw [sec2PlanesActionFin_apply_eq_iff, Equiv.symm_apply_apply]
    exact mem_normalizer_sec2F0_of_mem h11 hE16 hF hL hodd (Subgroup.mem_inf.mp huA).1 huEn huF
      hx hxS
  have h1 : sec2PlanesActionFin E F e ⟨u, huP⟩ ≠ 1 := by
    obtain ⟨V, hV, hVP, huV⟩ :=
      exists_not_mem_normalizer_of_sec2U h11 hE16 hF hL hodd hx hxS h4 huA hu3 huE
    intro h
    have := (sec2PlanesActionFin_apply_eq_iff E F e ⟨u, huP⟩ (e ⟨V, hV, hVP⟩)).mp (by
      rw [h, Equiv.Perm.one_apply])
    rw [Equiv.symm_apply_apply] at this
    exact huV this
  have hne : e ⟨E, hEpl⟩ ≠ e ⟨_, hF0pl⟩ := fun h =>
    hF0E (congrArg Subtype.val (e.injective h)).symm
  exact isThreeCycle_of_pow_three_of_fix h3 h1 hne hfixE hfixF0

theorem alternatingGroup_le_range :
    alternatingGroup (Fin 6) ≤ (sec2PlanesActionFin E F e).range := by
  obtain ⟨u, huA, hu3, huE⟩ := exists_sec2U hF hL hodd
  obtain ⟨hu, h3c⟩ :=
    isThreeCycle_sec2PlanesActionFin_sec2U h11 hE16 hF hL hodd hx hxS h4 e huA hu3 huE
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (MulAction.isPreprimitive_of_is_two_pretransitive
      (isMultiplyPretransitive_two_range h11 hE16 hF hL hodd hx hxS h4 e)) h3c ⟨_, rfl⟩

omit [Finite G] h11 hE16 hF hL hodd
  hx hxS h4 in
theorem mem_alternatingGroup_of_mem_sec2K {k : ↥(normalizer (sec2P E : Set G))}
    (hk : (k : G) ∈ sec2K E) : sec2PlanesActionFin E F e k ∈ alternatingGroup (Fin 6) := by
  set H := ((alternatingGroup (Fin 6)).comap (sec2PlanesActionFin E F e)).map
    (normalizer (sec2P E : Set G)).subtype with hH
  have hle : sec2K E ≤ H := by
    unfold sec2K oUpperTwo
    refine (closure_le _).mpr fun y hy => ?_
    obtain ⟨hyN, hyo⟩ := hy
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, Equiv.Perm.mem_alternatingGroup]
    have hodd' : Odd (orderOf (sec2PlanesActionFin E F e ⟨y, hyN⟩)) :=
      hyo.of_dvd_nat ((orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk]))
    have hpow : Equiv.Perm.sign (sec2PlanesActionFin E F e ⟨y, hyN⟩) ^
        orderOf (sec2PlanesActionFin E F e ⟨y, hyN⟩) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (sec2PlanesActionFin E F e ⟨y, hyN⟩)) with h | h
    · exact h
    · rw [h, hodd'.neg_one_pow] at hpow
      exact absurd hpow (by decide)
  obtain ⟨k', hk', hkk'⟩ := hle hk
  rw [show k = k' from Subtype.ext hkk'.symm]
  exact hk'

theorem exists_mem_sec2K_eq_of_mem_alternatingGroup {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ alternatingGroup (Fin 6)) :
    ∃ k : ↥(normalizer (sec2P E : Set G)), (k : G) ∈ sec2K E ∧ sec2PlanesActionFin E F e k = σ := by
  set T := ((sec2K E).subgroupOf (normalizer (sec2P E : Set G))).map (sec2PlanesActionFin E F e)
    with hT
  suffices hle : alternatingGroup (Fin 6) ≤ T by
    obtain ⟨k, hk, hkσ⟩ := hle hσ
    exact ⟨k, mem_subgroupOf.mp hk, hkσ⟩
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, closure_le]
  intro τ hτ
  obtain ⟨n, hn⟩ := alternatingGroup_le_range h11 hE16 hF hL hodd hx hxS h4 e
    (Equiv.Perm.IsThreeCycle.mem_alternatingGroup hτ)
  have hτ3 : orderOf τ = 3 := Equiv.Perm.IsThreeCycle.orderOf hτ
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  set n₁ := n ^ 2 ^ a with hn₁
  have hn₁odd : Odd (orderOf n₁) := by
    refine hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    rw [hn₁, ← pow_mul, ← ham, pow_orderOf_eq_one]
  have hmemK : ∀ k : ↥(normalizer (sec2P E : Set G)), Odd (orderOf k) →
      k ∈ (sec2K E).subgroupOf (normalizer (sec2P E : Set G)) := fun k hk =>
    mem_subgroupOf.mpr (subset_closure ⟨k.2, by rwa [Subgroup.orderOf_coe]⟩)
  have hρ : sec2PlanesActionFin E F e n₁ = τ ^ 2 ^ a := by rw [hn₁, map_pow, hn]
  have h3 : ¬ 3 ∣ 2 ^ a := fun h => by
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    norm_num at this
  have hmod : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by omega
  rcases hmod with h | h
  · refine ⟨n₁, hmemK n₁ hn₁odd, ?_⟩
    rw [hρ, ← pow_mod_orderOf, hτ3, h, pow_one]
  · refine ⟨n₁⁻¹, hmemK n₁⁻¹ (by rwa [orderOf_inv]), ?_⟩
    rw [map_inv, hρ, ← pow_mod_orderOf, hτ3, h, inv_eq_iff_mul_eq_one, ← pow_succ]
    have h1 := pow_orderOf_eq_one τ
    rwa [hτ3] at h1

end Frame

end CFSG.ComponentClassification.AS81
