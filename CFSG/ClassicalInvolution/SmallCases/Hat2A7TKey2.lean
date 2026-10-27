module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TSwap
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TKey

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Conj

variable {F : Type} [Group F]

theorem map_conj_inv_map_conj (L : Subgroup F) (g : F) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = L :=
  map_conj_map_conj_inv L g

omit [Group F] in
theorem cliqueInv_map_conj_mem {F : Type} [Group F] {K : Subgroup F} {u : F} (hu : u ∈ cliqueInv K)
    (g : F) : g * u * g⁻¹ ∈ cliqueInv (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨N, hN, hKN⟩ := hu
  refine ⟨N.map (MulAut.conj g).toMonoidHom, ?_, commOrEq_map_conj' hKN g⟩
  have h1 := hN.conj g
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1

theorem cliqueGrp_map_conj (K : Subgroup F) (g : F) :
    cliqueGrp (K.map (MulAut.conj g).toMonoidHom) =
      (cliqueGrp K).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun u hu => ?_
    have h := cliqueInv_map_conj_mem hu g⁻¹
    rw [map_conj_inv_map_conj] at h
    refine ⟨g⁻¹ * u * g⁻¹⁻¹, Subgroup.subset_closure ?_, ?_⟩
    · simpa using h
    · show g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u
      group
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    exact Subgroup.subset_closure (cliqueInv_map_conj_mem hu g)

end Conj

section Key2

variable {F : Type} [Group F] [Finite F]
variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)

omit [Finite F] in
include hZ IH in
theorem mem_normalizer_map_of_centralizes {K : Subgroup F} (hK : IsMember K) {a : F}
    (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F}
    (hbC : ∀ x ∈ cliqueGrp K, (g * a * g⁻¹) * x = x * (g * a * g⁻¹)) {x : F}
    (hx : x ∈ cliqueGrp K) :
    x ∈ Subgroup.normalizer (((cliqueGrp K).map (MulAut.conj g).toMonoidHom : Subgroup F) :
      Set F) := by
  have hc : g⁻¹ * x * g ∈ Subgroup.centralizer ({a} : Set F) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hbC x hx
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [← h1]
      _ = a * (g⁻¹ * x * g) := by group
  have hH : g⁻¹ * x * g ∈ Subgroup.normalizer (cliqueGrp K : Set F) :=
    centralizer_le_normalizer hZ IH hK ha ha1 (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have h2 := mem_normalizer_map_conj hH g
  have h3 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [h3] at h2

include hZ IH in
theorem mem_normalizer_of_not_commute {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    {a : F} (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F}
    (hc : ∀ x ∈ cliqueGrp K, (g * a * g⁻¹) * x = x * (g * a * g⁻¹))
    (hne : ∃ x ∈ cliqueGrp K, ∃ y ∈ (cliqueGrp K).map (MulAut.conj g).toMonoidHom,
      x * y ≠ y * x) :
    g ∈ Subgroup.normalizer (cliqueGrp K : Set F) := by
  have hKm : IsMember K := ⟨z, hK⟩
  obtain ⟨a'', ha'', y, hy, hne⟩ := hne
  have ha''1 : a'' ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have hK' : IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := by
    have h1 := hK.conj g
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  have hA' := cliqueGrp_map_conj K g
  have key := mem_normalizer_of_swap hZ IH hK' (a := g * a'' * g⁻¹) (g := g⁻¹)
    (by rw [hA']; exact ⟨a'', ha'', rfl⟩)
    (by
      intro h
      apply ha''1
      have : a'' = g⁻¹ * (g * a'' * g⁻¹) * g := by group
      rw [this, h]
      group)
    (by
      have : g⁻¹ * (g * a'' * g⁻¹) * g⁻¹⁻¹ = a'' := by group
      rw [this, hA']
      exact mem_normalizer_map_of_centralizes hZ IH hKm ha ha1 hc ha'')
    (by
      intro h
      apply hne
      have : g⁻¹ * (g * a'' * g⁻¹) * g⁻¹⁻¹ = a'' := by group
      rw [this] at h
      rw [hA'] at h
      exact h y hy)
  rw [hA'] at key
  have hle : cliqueGrp K ≤ (cliqueGrp K).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have h1 := (Subgroup.mem_normalizer_iff.mp key (g * x * g⁻¹)).mp ⟨x, hx, rfl⟩
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h1
  have hcard : Nat.card ((cliqueGrp K).map (MulAut.conj g).toMonoidHom) =
      Nat.card (cliqueGrp K) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : cliqueGrp K = (cliqueGrp K).map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  exact map_conj_eq_iff_mem_normalizer.mp heq.symm

include hZ IH in
theorem mem_normalizer_of_conj_mem_of_noBadPair {K : Subgroup F} {z : F}
    (hK : IsClassical2A7 ⊤ K z)
    (hnb : ∀ g : F, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      CommOrEq K (K.map (MulAut.conj g).toMonoidHom))
    {a : F} (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F}
    (hb : g * a * g⁻¹ ∈ Subgroup.normalizer (cliqueGrp K : Set F)) :
    g ∈ Subgroup.normalizer (cliqueGrp K : Set F) := by
  have hKm : IsMember K := ⟨z, hK⟩
  by_cases hc : ∀ x ∈ cliqueGrp K, (g * a * g⁻¹) * x = x * (g * a * g⁻¹)
  swap
  · exact mem_normalizer_of_swap hZ IH hK ha ha1 hb hc
  have hz : z ∈ cliqueGrp K := Subgroup.subset_closure (mem_cliqueInv_self hK)
  by_cases hcomm : ∀ x ∈ cliqueGrp K, ∀ y ∈ (cliqueGrp K).map (MulAut.conj g).toMonoidHom,
      x * y = y * x
  ·
    have h1 := hcomm z hz (g * z * g⁻¹) ⟨z, hz, rfl⟩
    exact mem_normalizer_of_commOrEq hZ IH hKm (hnb g h1.symm)
  · push Not at hcomm
    exact mem_normalizer_of_not_commute hZ IH hK ha ha1 hc hcomm

include hZ IH in
theorem bad_pair_centralizes {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {g : F}
    (hg : (g * z * g⁻¹) * z = z * (g * z * g⁻¹))
    (hbad : ¬ CommOrEq K (K.map (MulAut.conj g).toMonoidHom)) :
    (∀ x ∈ cliqueGrp K, (g * z * g⁻¹) * x = x * (g * z * g⁻¹)) ∧
      ∀ x ∈ cliqueGrp K, ∀ y ∈ (cliqueGrp K).map (MulAut.conj g).toMonoidHom, x * y = y * x := by
  have hKm : IsMember K := ⟨z, hK⟩
  have hz : z ∈ cliqueGrp K := Subgroup.subset_closure (mem_cliqueInv_self hK)
  have hz1 : z ≠ 1 := by
    intro h
    have := hK.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hu : g * z * g⁻¹ ∈ Subgroup.normalizer (cliqueGrp K : Set F) :=
    centralizer_le_normalizer hZ IH hKm hz hz1 hg
  have hc : ∀ x ∈ cliqueGrp K, (g * z * g⁻¹) * x = x * (g * z * g⁻¹) := by
    by_contra hcon
    exact hbad (commOrEq_of_mem_normalizer hZ IH hK
      (mem_normalizer_of_swap hZ IH hK hz hz1 hu hcon))
  refine ⟨hc, ?_⟩
  by_contra hcomm
  push Not at hcomm
  exact hbad (commOrEq_of_mem_normalizer hZ IH hK
    (mem_normalizer_of_not_commute hZ IH hK hz hz1 hc hcomm))

end Key2

end CFSG.ClassicalInvolution.Hat2A7T
