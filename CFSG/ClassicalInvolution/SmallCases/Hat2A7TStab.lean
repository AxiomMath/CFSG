module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TClique

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Stab

variable {F : Type} [Group F]

@[expose] def cliqueSet (K : Subgroup F) : Set (Subgroup F) :=
  {N | IsMember N ∧ CommOrEq K N}

omit [Group F] in
theorem commOrEq_map_conj' {F : Type} [Group F] {L M : Subgroup F} (h : CommOrEq L M) (g : F) :
    CommOrEq (L.map (MulAut.conj g).toMonoidHom) (M.map (MulAut.conj g).toMonoidHom) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · refine Or.inr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    have := h a ha b hb
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [this]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem map_conj_one' (L : Subgroup F) : L.map (MulAut.conj (1 : F)).toMonoidHom = L := by
  ext x
  simp

theorem map_conj_map_conj_inv (L : Subgroup F) (g : F) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = L := by
  rw [map_map_conj, inv_mul_cancel, map_conj_one']

variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)

include hZ IH in
theorem conj_mem_cliqueInv {K : Subgroup F} (hK : IsMember K) {g : F}
    (h : CommOrEq K (K.map (MulAut.conj g).toMonoidHom)) {u : F} (hu : u ∈ cliqueInv K) :
    g * u * g⁻¹ ∈ cliqueInv K := by
  obtain ⟨N, hN, hKN⟩ := hu
  have hN' : IsClassical2A7 ⊤ (N.map (MulAut.conj g).toMonoidHom) (g * u * g⁻¹) := by
    have h1 := hN.conj g
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  refine ⟨_, hN', commOrEq_trans hZ IH hK (isMember_map_conj hK g) ⟨_, hN'⟩ h
    (commOrEq_map_conj' hKN g)⟩

include hZ IH in
theorem mem_normalizer_of_commOrEq {K : Subgroup F} (hK : IsMember K) {g : F}
    (h : CommOrEq K (K.map (MulAut.conj g).toMonoidHom)) :
    g ∈ Subgroup.normalizer (cliqueGrp K : Set F) := by
  have hg : (cliqueGrp K).map (MulAut.conj g).toMonoidHom ≤ cliqueGrp K := by
    rintro _ ⟨x, hx, rfl⟩
    have key : ∀ y ∈ cliqueGrp K, g * y * g⁻¹ ∈ cliqueGrp K := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem u hu => exact Subgroup.subset_closure (conj_mem_cliqueInv hZ IH hK h hu)
      | one => simp
      | mul x y _ _ hx hy =>
        have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ hx
    exact key x hx
  have hg' : (cliqueGrp K).map (MulAut.conj g⁻¹).toMonoidHom ≤ cliqueGrp K := by
    have h' : CommOrEq K (K.map (MulAut.conj g⁻¹).toMonoidHom) := by
      have h2 := commOrEq_map_conj' h g⁻¹
      rw [map_map_conj, inv_mul_cancel, map_conj_one'] at h2
      exact h2.symm
    rintro _ ⟨x, hx, rfl⟩
    have key : ∀ y ∈ cliqueGrp K, g⁻¹ * y * g⁻¹⁻¹ ∈ cliqueGrp K := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem u hu => exact Subgroup.subset_closure (conj_mem_cliqueInv hZ IH hK h' hu)
      | one => simp
      | mul x y _ _ hx hy =>
        have : g⁻¹ * (x * y) * g⁻¹⁻¹ = (g⁻¹ * x * g⁻¹⁻¹) * (g⁻¹ * y * g⁻¹⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        have : g⁻¹ * x⁻¹ * g⁻¹⁻¹ = (g⁻¹ * x * g⁻¹⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ hx
    exact key x hx
  rw [← map_conj_eq_iff_mem_normalizer]
  apply le_antisymm hg
  intro x hx
  refine ⟨g⁻¹ * x * g⁻¹⁻¹, hg' ⟨x, hx, rfl⟩, ?_⟩
  show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
  group

include hZ IH in
theorem commOrEq_of_mem_normalizer {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {g : F}
    (hg : g ∈ Subgroup.normalizer (cliqueGrp K : Set F)) :
    CommOrEq K (K.map (MulAut.conj g).toMonoidHom) := by
  have hz : z ∈ cliqueGrp K := Subgroup.subset_closure (mem_cliqueInv_self hK)
  have hz1 : z ≠ 1 := by
    intro h
    have := hK.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hgz : g * z * g⁻¹ ∈ cliqueGrp K := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  exact commOrEq_conj_of_mem_cliqueGrp hZ IH ⟨z, hK⟩ hz hz1 hgz

include hZ IH in
theorem centralizer_le_normalizer {K : Subgroup F} (hK : IsMember K) {a : F}
    (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F} (hg : g * a = a * g) :
    g ∈ Subgroup.normalizer (cliqueGrp K : Set F) :=
  mem_normalizer_of_commOrEq hZ IH hK (commOrEq_conj_of_mem_centralizer hZ IH hK ha ha1 hg)

include hZ IH in
theorem conj_mem_cliqueSet {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {g : F}
    (hg : g ∈ Subgroup.normalizer (cliqueGrp K : Set F)) {N : Subgroup F}
    (hN : N ∈ cliqueSet K) : N.map (MulAut.conj g).toMonoidHom ∈ cliqueSet K :=
  ⟨isMember_map_conj hN.1 g, commOrEq_trans hZ IH ⟨z, hK⟩ (isMember_map_conj ⟨z, hK⟩ g)
    (isMember_map_conj hN.1 g) (commOrEq_of_mem_normalizer hZ IH hK hg)
    (commOrEq_map_conj' hN.2 g)⟩

end Stab

end CFSG.ClassicalInvolution.Hat2A7T
