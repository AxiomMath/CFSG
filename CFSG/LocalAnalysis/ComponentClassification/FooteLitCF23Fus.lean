module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup

theorem oneClass_of_small {J : Type} [Group J] [Finite J] (hZ : Odd (Nat.card (center J)))
    (hsmall : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (J ⧸ center J) .PSL 2 p f) ∨
      Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7))) : OneClass J := by
  have hs : IsSmallAltOrL2 (J ⧸ center J) := by
    rcases hsmall with h | h
    · exact Or.inr h
    · exact Or.inl ⟨7, Or.inr (Or.inr rfl), h⟩
  have hZ1 : ∀ z ∈ center J, z * z = 1 → z = 1 := by
    intro z hz hz2
    have h1 : orderOf (⟨z, hz⟩ : center J) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [pow_two]; exact hz2))
    have h2 := orderOf_dvd_natCard (⟨z, hz⟩ : center J)
    have h3 : orderOf (⟨z, hz⟩ : center J) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hZ)
    have := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
    exact this
  have himg : ∀ x : J, orderOf x = 2 → orderOf (QuotientGroup.mk x : J ⧸ center J) = 2 := by
    intro x hx
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    refine orderOf_eq_prime (by rw [pow_two, ← QuotientGroup.mk_mul, hx2]; rfl) fun h1 => ?_
    have hxZ : x ∈ center J := (QuotientGroup.eq_one_iff x).mp h1
    have := hZ1 x hxZ hx2
    rw [this, orderOf_one] at hx
    omega
  intro x y hx hy
  obtain ⟨g, hg⟩ := cfSmallInv (J ⧸ center J) hs _ _ (himg x hx) (himg y hy)
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have hz : y⁻¹ * (g'⁻¹ * x * g') ∈ center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg, inv_mul_cancel]
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hy2 : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
  set z := y⁻¹ * (g'⁻¹ * x * g') with hzdef
  have hyz : g'⁻¹ * x * g' = y * z := by rw [hzdef, mul_inv_cancel_left]
  have hzc : ∀ w : J, w * z = z * w := fun w => (mem_center_iff.mp hz w)
  have hz2 : z * z = 1 := by
    have h1 : (y * z) * (y * z) = 1 := by
      rw [← hyz, show g'⁻¹ * x * g' * (g'⁻¹ * x * g') = g'⁻¹ * (x * x) * g' by group, hx2]
      group
    calc z * z = (y * y) * (z * z) := by rw [hy2, one_mul]
      _ = (y * z) * (y * z) := by
        rw [show (y * z) * (y * z) = y * (z * y) * z by group, ← hzc y]
        group
      _ = 1 := h1
  refine ⟨g', ?_⟩
  rw [hyz, hZ1 z hz hz2, mul_one]

theorem concl_of_witness {G : Type*} [Group G] {N J : Subgroup G} {α : G} (hJN : J ≤ N)
    (hJα : J ≤ centralizer ({α} : Set G)) (hone : OneClass J) {ζ₀ γ₀ : G} (hζ₀ : ζ₀ ∈ J)
    (hζ₀2 : orderOf ζ₀ = 2) (hγ₀ : γ₀ ∈ N) (h : γ₀⁻¹ * α * γ₀ = α * ζ₀) :
    ∀ ζ ∈ J, orderOf ζ = 2 → ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  intro ζ hζ hζ2
  obtain ⟨j, hj⟩ := hone ⟨ζ₀, hζ₀⟩ ⟨ζ, hζ⟩ (by rw [Subgroup.orderOf_mk, hζ₀2])
    (by rw [Subgroup.orderOf_mk, hζ2])
  have hj' : (j : G)⁻¹ * ζ₀ * j = ζ := congrArg Subtype.val hj
  have hjα : (j : G) * α = α * j := mem_centralizer_singleton_iff.mp (hJα j.2)
  have hjα' : (j : G)⁻¹ * α = α * (j : G)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hjα, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨γ₀ * j, N.mul_mem hγ₀ (hJN j.2), ?_⟩
  calc (γ₀ * j)⁻¹ * α * (γ₀ * j) = (j : G)⁻¹ * (γ₀⁻¹ * α * γ₀) * j := by group
    _ = (j : G)⁻¹ * α * ζ₀ * j := by rw [h]; group
    _ = α * ((j : G)⁻¹ * ζ₀ * j) := by rw [hjα']; group
    _ = α * ζ := by rw [hj']

theorem isComponentOf_image {G : Type*} [Group G] {N J : Subgroup G} {α : G} (hαN : α ∈ N)
    (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    {M : Type*} [Group M] {P : Subgroup M} (θ : N ≃* P) :
    Assembly.IsComponentOf ((J.subgroupOf N).map (P.subtype.comp θ.toMonoidHom))
      (P ⊓ centralizer ({((θ ⟨α, hαN⟩ : P) : M)} : Set M)) := by
  obtain ⟨hle, hcomp⟩ := isComponent_inner hαN hJN hJα hJ
  have hc :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).2 hcomp
  set f : ↥N →* M := P.subtype.comp θ.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.injective
  have h := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff hf).2 hc
  have hmap : (centralizer ({⟨α, hαN⟩} : Set N)).map f =
      P ⊓ centralizer ({((θ ⟨α, hαN⟩ : P) : M)} : Set M) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_inf.mpr ⟨(θ x).2, ?_⟩
      rw [mem_centralizer_singleton_iff] at hx ⊢
      have := congrArg f hx
      rw [map_mul, map_mul] at this
      exact this
    · intro hy
      obtain ⟨hyP, hy⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_map.mpr ⟨θ.symm ⟨y, hyP⟩, ?_, by simp [hfdef]⟩
      rw [mem_centralizer_singleton_iff] at hy ⊢
      apply hf
      simp only [map_mul, hfdef, MonoidHom.coe_comp, Function.comp_apply, coe_subtype,
        MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hy
  rw [hmap] at h
  exact h

end CFSG.ComponentClassification.GSThmB.CF23I
