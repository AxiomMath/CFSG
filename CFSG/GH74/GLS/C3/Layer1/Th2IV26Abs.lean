module

public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.GH74.GLS.Th2.IV26

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Sandwich

variable {C : Type} [Group C] [Finite C]

theorem exists_component_of_image
    (hB : ∀ J : Subgroup C, IsPComponent 2 J → IsComponent J)
    {Z : Subgroup C} (hZ : Z.IsSubnormal)
    (hZc : IsComponent (Z.map (QuotientGroup.mk' (pPrimeCore 2 C)))) :
    ∃ J : Subgroup C, IsComponent J ∧ J ≤ Z ∧
      ∀ z ∈ Z, ∃ j ∈ J, ∃ o ∈ pPrimeCore 2 C, z = j * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  obtain ⟨J, hJp, hJmap⟩ := exists_isPComponent_of_isComponent 2 hZc
  have hJc : IsComponent J := hB J hJp
  have hJZ : J ≤ Z := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hJc hZ with h | h
    · exact h
    · exfalso
      have h1 : ⁅J.map π, Z.map π⁆ = ⊥ := by
        rw [← Subgroup.map_commutator, h, Subgroup.map_bot]
      rw [hJmap] at h1
      have hperf : ⁅Z.map π, Z.map π⁆ = Z.map π := Subgroup.isPerfect_iff.mp hZc.1.1
      exact ne_bot_of_isComponent hZc (by rw [← hperf]; exact h1)
  refine ⟨J, hJc, hJZ, fun z hz => ?_⟩
  have hz' : π z ∈ J.map π := by rw [hJmap]; exact Subgroup.mem_map_of_mem _ hz
  obtain ⟨j, hj, hjz⟩ := Subgroup.mem_map.1 hz'
  refine ⟨j, hj, j⁻¹ * z, ?_, by group⟩
  have h1 : π (j⁻¹ * z) = 1 := by rw [map_mul, map_inv, hjz, inv_mul_cancel]
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem le_of_perfect_of_le_mul {J P O : Subgroup C} (hJ : IsComponent J) [hOn : O.Normal]
    (hOs : Group.IsSolvable O) (hP : ⁅P, P⁆ = P)
    (hPJ : ∀ p ∈ P, ∃ j ∈ J, ∃ o ∈ O, p = j * o) : P ≤ J := by
  have hJO : ⁅J, O⁆ = ⊥ := (CFSG.LocalCores.component_solvable_centralizer hOs hOn.isSubnormal).1 J hJ
  have hcomm : ∀ j ∈ J, ∀ o ∈ O, j * o = o * j := by
    intro j hj o ho
    have := Subgroup.commutator_mem_commutator hj ho
    rw [hJO, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  set A : Subgroup C := J ⊔ O with hA
  have hJA : J ≤ A := le_sup_left
  have hOA : O ≤ A := le_sup_right
  have hPA : P ≤ A := fun p hp => by
    obtain ⟨j, hj, o, ho, rfl⟩ := hPJ p hp
    exact A.mul_mem (hJA hj) (hOA ho)
  have hJnorm : (J.subgroupOf A).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨j₁, hj₁, o₁, ho₁, hgeq⟩ := Subgroup.mem_sup_of_normal_right.1 g.2
    have h : o₁ * (a : C) = (a : C) * o₁ := (hcomm _ ha o₁ ho₁).symm
    have : ((g * a * g⁻¹ : ↥A) : C) = j₁ * (a : C) * j₁⁻¹ := by
      push_cast
      rw [← hgeq]
      calc j₁ * o₁ * (a : C) * (j₁ * o₁)⁻¹ = j₁ * (o₁ * (a : C)) * (o₁⁻¹ * j₁⁻¹) := by group
        _ = j₁ * ((a : C) * o₁) * (o₁⁻¹ * j₁⁻¹) := by rw [h]
        _ = j₁ * (a : C) * j₁⁻¹ := by group
    rw [this]
    exact J.mul_mem (J.mul_mem hj₁ ha) (J.inv_mem hj₁)
  have hNn : (O.subgroupOf A).Normal := inferInstance
  have hOsolv : Group.IsSolvable ↥(O.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hOA).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hOA).injective
  have : Group.IsPerfect ↥(P.subgroupOf A) := by
    have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPA).symm.surjective
  have hkerS : Group.IsSolvable ↥(QuotientGroup.mk' (O.subgroupOf A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hOsolv
  have key := CFSG.ComponentClassification.SolvableKernelContainment.perfect_containment (QuotientGroup.mk' (O.subgroupOf A))
    (perfectSubgroup := P.subgroupOf A) (containingSubgroup := J.subgroupOf A) (by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨j, hj, o, ho, hpeq⟩ := hPJ (p : C) hp
      refine ⟨⟨j, hJA hj⟩, Subgroup.mem_subgroupOf.mpr hj, ?_⟩
      have hoA : (⟨o, hOA ho⟩ : ↥A) ∈ O.subgroupOf A := ho
      have : p = ⟨j, hJA hj⟩ * ⟨o, hOA ho⟩ := Subtype.ext hpeq
      simp only [QuotientGroup.mk'_apply]
      rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hoA, mul_one])
  intro p hp
  have := key (Subgroup.mem_subgroupOf.mpr hp : (⟨p, hPA hp⟩ : ↥A) ∈ P.subgroupOf A)
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite C] in
theorem commutator_mul_commuting {a b r s : C} (hrb : r * b = b * r)
    (hrs : r * s = s * r) (hsa : s * a = a * s) :
    ⁅a * r, b * s⁆ = ⁅a, b⁆ := by
  have hrb' : r * b⁻¹ = b⁻¹ * r := by
    calc r * b⁻¹ = b⁻¹ * (b * r) * b⁻¹ := by group
      _ = b⁻¹ * (r * b) * b⁻¹ := by rw [hrb]
      _ = b⁻¹ * r := by group
  have hsa' : s * a⁻¹ = a⁻¹ * s := by
    calc s * a⁻¹ = a⁻¹ * (a * s) * a⁻¹ := by group
      _ = a⁻¹ * (s * a) * a⁻¹ := by rw [hsa]
      _ = a⁻¹ * s := by group
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * r * (b * s) * (r⁻¹ * a⁻¹) * (s⁻¹ * b⁻¹)
      = a * (r * b) * s * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by group
    _ = a * (b * r) * s * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by rw [hrb]
    _ = a * b * (r * s) * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by group
    _ = a * b * (s * r) * r⁻¹ * a⁻¹ * s⁻¹ * b⁻¹ := by rw [hrs]
    _ = a * b * s * a⁻¹ * s⁻¹ * b⁻¹ := by group
    _ = a * b * (s * a⁻¹) * s⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * s) * s⁻¹ * b⁻¹ := by rw [hsa']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem isComponent_of_sandwich
    (hB : ∀ J : Subgroup C, IsPComponent 2 J → IsComponent J)
    {K Z R : Subgroup C} (hKperf : ⁅K, K⁆ = K) (hZ : Z.IsSubnormal) (hKZ : K ≤ Z)
    (hR : R ≤ pPrimeCore 2 C) (hZKR : ∀ z ∈ Z, ∃ k ∈ K, ∃ r ∈ R, z = k * r)
    (hKq : IsQuasisimple ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 C)))) :
    IsComponent K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 C with hO
  set π := QuotientGroup.mk' O with hπ
  have hZK : Z.map π = K.map π := by
    refine le_antisymm ?_ (Subgroup.map_mono hKZ)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := hZKR z hz
    refine ⟨k, hk, ?_⟩
    have hr1 : π r = 1 := (QuotientGroup.eq_one_iff r).2 (hR hr)
    rw [map_mul, hr1, mul_one]
  have hZc : IsComponent (Z.map π) :=
    ⟨by rw [hZK]; exact hKq, hZ.map (QuotientGroup.mk'_surjective O)⟩
  obtain ⟨J, hJc, hJZ, hdec⟩ := exists_component_of_image hB hZ hZc
  have hOsolv : Group.IsSolvable O := isSolvable_pPrimeCore_two
  have hKJ : K ≤ J := le_of_perfect_of_le_mul hJc hOsolv hKperf (fun k hk => hdec k (hKZ hk))
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJc.1.1
  have hJO : ⁅J, O⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hOsolv (inferInstance : O.Normal).isSubnormal).1 J hJc
  have hcomm : ∀ j ∈ J, ∀ o ∈ O, j * o = o * j := by
    intro j hj o ho
    have := Subgroup.commutator_mem_commutator hj ho
    rw [hJO, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  have hJK : J ≤ K := by
    rw [← hJperf, Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨j, hj, j', hj', rfl⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := hZKR j (hJZ hj)
    obtain ⟨k', hk', r', hr', rfl⟩ := hZKR j' (hJZ hj')
    have hrJ : r ∈ J := by
      have := J.mul_mem (J.inv_mem (hKJ hk)) hj
      simpa using this
    have hr'J : r' ∈ J := by
      have := J.mul_mem (J.inv_mem (hKJ hk')) hj'
      simpa using this
    have hrO : r ∈ O := hR hr
    have hr'O : r' ∈ O := hR hr'
    have e := commutator_mul_commuting (a := k) (b := k') (r := r) (s := r')
      (hcomm k' (hKJ hk') r hrO).symm (hcomm r hrJ r' hr'O) (hcomm k (hKJ hk) r' hr'O).symm
    show ⁅k * r, k' * r'⁆ ∈ K
    rw [e]
    exact Subgroup.commutator_mem_commutator hk hk' |> fun h => by rwa [hKperf] at h
  exact (le_antisymm hKJ hJK) ▸ hJc

theorem isQuasisimple_map_of_isQuasisimple {K : Subgroup C} (hK : IsQuasisimple ↥K) :
    IsQuasisimple ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 C))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 C with hO
  set π := QuotientGroup.mk' O with hπ
  have hrange : ((π.comp K.subtype)).range = K.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rcases quasisimple_homomorphic_images hK (π.comp K.subtype) with h | h
  · exfalso
    rw [hrange] at h
    have hKO : K ≤ O := by
      intro k hk
      have : π k ∈ K.map π := Subgroup.mem_map_of_mem _ hk
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff k).1 this
    have hOsolv : Group.IsSolvable ↥O := isSolvable_pPrimeCore_two
    have hsolv : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKO)
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
    have : Group.IsPerfect ↥K := hK.1
    exact Group.IsPerfect.not_isSolvable ↥K hsolv
  · rw [hrange] at h
    exact h

theorem isQuasisimple_map_of_hat {K₀ : Type} [Group K₀] [Finite K₀]
    (hK₀ : IsQuasisimple (K₀ ⧸ pPrimeCore 2 K₀)) (g : K₀ →* C) (hsub : g.range.IsSubnormal)
    (hperf : ⁅g.range, g.range⁆ = g.range) (hne : g.range ≠ ⊥) :
    IsQuasisimple ↥(g.range.map (QuotientGroup.mk' (pPrimeCore 2 C))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 C with hO
  set π := QuotientGroup.mk' O with hπ
  set g' : K₀ →* C ⧸ O := π.comp g with hg'
  have hrange : g'.range = g.range.map π := by
    rw [hg', MonoidHom.range_comp]
  have hcore : pPrimeCore 2 (C ⧸ O) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hrsub : g'.range.IsSubnormal := by
    rw [hrange]
    exact hsub.map (QuotientGroup.mk'_surjective O)
  have hker : pPrimeCore 2 K₀ ≤ g'.ker := by
    set N : Subgroup (C ⧸ O) := (pPrimeCore 2 K₀).map g' with hN
    have hNle : N ≤ g'.range := by
      rintro _ ⟨k, -, rfl⟩
      exact ⟨k, rfl⟩
    have hNnorm : (N.subgroupOf g'.range).Normal := by
      refine ⟨fun n hn r => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨k₀, hk₀, hk₀n⟩ := hn
      obtain ⟨k, hk⟩ := r.2
      refine ⟨k * k₀ * k⁻¹, Subgroup.Normal.conj_mem inferInstance k₀ hk₀ k, ?_⟩
      simp only [map_mul, map_inv, hk₀n, hk]
      rfl
    have hNsub : N.IsSubnormal := Subgroup.IsSubnormal.trans hNle hNnorm.isSubnormal hrsub
    have hNodd : Odd (Nat.card N) := by
      have h1 : Nat.card N ∣ Nat.card (pPrimeCore 2 K₀) := Subgroup.card_map_dvd _ _
      exact Odd.of_dvd_nat (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card) h1
    have hNbot : N = ⊥ := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hcore hNsub hNodd
    intro k hk
    have : g' k ∈ N := Subgroup.mem_map_of_mem _ hk
    rw [hNbot, Subgroup.mem_bot] at this
    exact this
  let f : K₀ ⧸ pPrimeCore 2 K₀ →* C ⧸ O := QuotientGroup.lift (pPrimeCore 2 K₀) g' hker
  have hfrange : f.range = g'.range := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(k : K₀ ⧸ pPrimeCore 2 K₀), rfl⟩
  rcases quasisimple_homomorphic_images hK₀ f with h | h
  · exfalso
    rw [hfrange, hrange] at h
    have hKO : g.range ≤ O := by
      intro c hc
      have : π c ∈ g.range.map π := Subgroup.mem_map_of_mem _ hc
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff c).1 this
    have hOsolv : Group.IsSolvable ↥O := isSolvable_pPrimeCore_two
    have hsolv : Group.IsSolvable ↥g.range :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKO)
    have : Nontrivial ↥g.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥g.range := Subgroup.isPerfect_iff.2 hperf
    exact Group.IsPerfect.not_isSolvable ↥g.range hsolv
  · rw [hfrange, hrange] at h
    exact h

end Sandwich

end CFSG.GH74.GLS.Th2.IV26
