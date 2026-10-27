module

public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionSupport
public import CFSG.CharacterTheory.Wreathed.CompatibleBoundaryCountKernel

public section

namespace CFSG.Wreathed.TorusSplitting

variable {G : Type*} [Group G]

open BaseFourCentralizerStructure

@[expose] def normalizerConj (H : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H ≃* H where
  toFun h := ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg h).mp h.2⟩
  invFun h := ⟨g⁻¹ * h * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * h * g)).mpr (by
    simp [mul_assoc])⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem ambientOddCore_conj_mem (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {k : G} (hk : k ∈ ambientOddCore H) :
    g * k * g⁻¹ ∈ ambientOddCore H := by
  obtain ⟨k', hk', rfl⟩ := hk
  have hmap := CFSG.Wreathed.ReducedInvolution.oddCore_map_mulEquiv (normalizerConj H hg)
  have h : normalizerConj H hg k' ∈ CFSG.oddCore H := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hk'
  exact ⟨_, h, rfl⟩

theorem map_commutator_of_surjective {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (hf : Function.Surjective f) : (commutator P).map f = commutator Q := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective f hf]

theorem centralizes_derived_iff {K A B : Subgroup G} [(A.subgroupOf K).Normal] {P : Type*}
    [Group P] (ζ : K ⧸ A.subgroupOf K ≃* P) (Z : Subgroup P)
    (hZ : Subgroup.centralizer (commutator P : Set P) = Z)
    (hB : ∀ k : K, (k : G) ∈ B ↔ ζ (QuotientGroup.mk k) ∈ Z) :
    ∀ k ∈ K, (∀ x ∈ ⁅K, K⁆, k * x * k⁻¹ * x⁻¹ ∈ A) ↔ k ∈ B := by
  intro k hk
  have hcomm := map_commutator_of_surjective ζ.toMonoidHom ζ.surjective
  have hcommK := map_commutator_of_surjective (QuotientGroup.mk' (A.subgroupOf K))
    (QuotientGroup.mk'_surjective _)
  have hK' : (commutator K).map K.subtype = ⁅K, K⁆ :=
    CFSG.Wreathed.CompatibleFamilies.map_commutator_subtype K
  have hq : ∀ x : K, (k * (x : G) * k⁻¹ * (x : G)⁻¹ ∈ A ↔
      (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ A.subgroupOf K) * QuotientGroup.mk x =
        QuotientGroup.mk x * QuotientGroup.mk ⟨k, hk⟩) := by
    intro x
    have h1 : k * (x : G) * k⁻¹ * (x : G)⁻¹ ∈ A ↔
        (⟨k, hk⟩ * x * (⟨k, hk⟩ : K)⁻¹ * x⁻¹ : K) ∈ A.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      rfl
    rw [h1, ← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    constructor
    · intro h
      calc (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ A.subgroupOf K) * QuotientGroup.mk x =
          (QuotientGroup.mk ⟨k, hk⟩ * QuotientGroup.mk x * (QuotientGroup.mk ⟨k, hk⟩)⁻¹ *
            (QuotientGroup.mk x)⁻¹) * (QuotientGroup.mk x * QuotientGroup.mk ⟨k, hk⟩) := by
              group
        _ = QuotientGroup.mk x * QuotientGroup.mk ⟨k, hk⟩ := by rw [h, one_mul]
    · intro h
      rw [h]
      group
  rw [hB ⟨k, hk⟩, ← hZ, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [← hcomm] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← hcommK] at hy'
    obtain ⟨x', hx', rfl⟩ := hy'
    have hx : (x' : G) ∈ ⁅K, K⁆ := hK' ▸ Subgroup.mem_map_of_mem K.subtype hx'
    have h2 := (hq x').mp (h x' hx)
    change ζ (QuotientGroup.mk x') * ζ (QuotientGroup.mk ⟨k, hk⟩) =
      ζ (QuotientGroup.mk ⟨k, hk⟩) * ζ (QuotientGroup.mk x')
    rw [← map_mul, ← map_mul, h2]
  · intro h x hx
    have hxK : x ∈ K := (Subgroup.commutator_le.mpr fun a ha b hb =>
      K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)) hx
    rw [← hK'] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hmem : ζ (QuotientGroup.mk x') ∈ commutator P := by
      rw [← hcomm, ← hcommK]
      exact ⟨_, ⟨x', hx', rfl⟩, rfl⟩
    have h2 := h _ hmem
    refine (hq x').mpr (ζ.injective ?_)
    rw [map_mul, map_mul]
    exact h2.symm

theorem mem_ker_iff_of_compatible {K A B : Subgroup G} [(A.subgroupOf K).Normal]
    {X Y : Type*} [Group X] [Group Y] {φ : Y →* MulAut X}
    (ζ : K ⧸ A.subgroupOf K ≃* X ⋊[φ] Y) (ω : K →* Y)
    (hω : ∀ k : K, SemidirectProduct.rightHom (ζ (QuotientGroup.mk k)) = ω k)
    (hB : ∀ k : K, (k : G) ∈ B ↔
      ζ (QuotientGroup.mk k) ∈ (SemidirectProduct.inl : X →* X ⋊[φ] Y).range) (k : K) :
    (k : G) ∈ B ↔ ω k = 1 := by
  rw [hB k, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, hω k]

end CFSG.Wreathed.TorusSplitting
