module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootLeviBase

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace LeviAux

theorem mem_normalizer_of_forall {G : Type*} [Group G] (H : Subgroup G) {g : G}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  exact fun x => ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

section Torus

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem hG_inv_mul_xG_mul (a : Fin TwistTag.E6.foldedTag.rank)
    (u : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    (hG σ a u)⁻¹ * xG σ a c * hG σ a u =
      xG σ a ((((u⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
        orbitField TwistTag.E6 K σ.toRingHom a)) ^ 2 * c) := by
  have h := hG_mul_xG_mul_inv σ a u ((((u⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    orbitField TwistTag.E6 K σ.toRingHom a)) ^ 2 * c)
  have e : (u : orbitField TwistTag.E6 K σ.toRingHom a) ^ 2 *
      ((((u⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
        orbitField TwistTag.E6 K σ.toRingHom a)) ^ 2 * c) = c := by
    have hu := u.ne_zero
    rw [Units.val_inv_eq_inv_val]
    field_simp
  rw [e] at h
  calc (hG σ a u)⁻¹ * xG σ a c * hG σ a u
      = (hG σ a u)⁻¹ * (hG σ a u * xG σ a ((((u⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
        orbitField TwistTag.E6 K σ.toRingHom a)) ^ 2 * c) * (hG σ a u)⁻¹) * hG σ a u := by rw [h]
    _ = _ := by group

theorem hG_inv_mul_yG_mul (a : Fin TwistTag.E6.foldedTag.rank)
    (u : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    (hG σ a u)⁻¹ * yG σ a c * hG σ a u =
      yG σ a ((u : orbitField TwistTag.E6 K σ.toRingHom a) ^ 2 * c) := by
  have h := hG_mul_yG_mul_inv σ a u ((u : orbitField TwistTag.E6 K σ.toRingHom a) ^ 2 * c)
  have e : ((((u⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
      orbitField TwistTag.E6 K σ.toRingHom a)) ^ 2 *
        ((u : orbitField TwistTag.E6 K σ.toRingHom a) ^ 2 * c)) = c := by
    have hu := u.ne_zero
    rw [Units.val_inv_eq_inv_val]
    field_simp
  rw [e] at h
  calc (hG σ a u)⁻¹ * yG σ a c * hG σ a u
      = (hG σ a u)⁻¹ * (hG σ a u * yG σ a ((u : orbitField TwistTag.E6 K σ.toRingHom a) ^ 2 * c) *
        (hG σ a u)⁻¹) * hG σ a u := by rw [h]
    _ = _ := by group

local notation "Xpos" => twE6RootSubgroup K σ e6HighestRoot

local notation "Xneg" => twE6RootSubgroup K σ (-e6HighestRoot)

theorem torus_mul_X0_mul_inv (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ)
    (c : orbitField TwistTag.E6 K σ.toRingHom a2) :
    (n0G σ * hG σ a2 u * (n0G σ)⁻¹) * (n0G σ * xG σ a2 c * (n0G σ)⁻¹) *
        (n0G σ * hG σ a2 u * (n0G σ)⁻¹)⁻¹ =
      n0G σ * xG σ a2 ((u : orbitField TwistTag.E6 K σ.toRingHom a2) ^ 2 * c) * (n0G σ)⁻¹ := by
  rw [← hG_mul_xG_mul_inv σ a2 u c]
  group

theorem torus_mul_X0m_mul_inv (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ)
    (c : orbitField TwistTag.E6 K σ.toRingHom a2) :
    (n0G σ * hG σ a2 u * (n0G σ)⁻¹) * (n0G σ * yG σ a2 c * (n0G σ)⁻¹) *
        (n0G σ * hG σ a2 u * (n0G σ)⁻¹)⁻¹ =
      n0G σ * yG σ a2 ((((u⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
        orbitField TwistTag.E6 K σ.toRingHom a2)) ^ 2 * c) * (n0G σ)⁻¹ := by
  rw [← hG_mul_yG_mul_inv σ a2 u c]
  group

theorem torus_mem_normalizer_X0 (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
    n0G σ * hG σ a2 u * (n0G σ)⁻¹ ∈ Subgroup.normalizer (Xpos : Set (twistedE6RootGroup K σ)) := by
  refine mem_normalizer_of_forall _ (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, rfl⟩ := (mem_X0_iff' σ x).1 hx
    rw [torus_mul_X0_mul_inv]
    exact (mem_X0_iff' σ _).2 ⟨_, rfl⟩
  · obtain ⟨c, rfl⟩ := (mem_X0_iff' σ x).1 hx
    have e : (n0G σ * hG σ a2 u * (n0G σ)⁻¹)⁻¹ * (n0G σ * xG σ a2 c * (n0G σ)⁻¹) *
        (n0G σ * hG σ a2 u * (n0G σ)⁻¹) =
          n0G σ * ((hG σ a2 u)⁻¹ * xG σ a2 c * hG σ a2 u) * (n0G σ)⁻¹ := by group
    rw [e, hG_inv_mul_xG_mul]
    exact (mem_X0_iff' σ _).2 ⟨_, rfl⟩

theorem torus_mem_normalizer_X0m (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
    n0G σ * hG σ a2 u * (n0G σ)⁻¹ ∈ Subgroup.normalizer (Xneg : Set (twistedE6RootGroup K σ)) := by
  refine mem_normalizer_of_forall _ (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, rfl⟩ := (mem_X0m_iff' σ x).1 hx
    rw [torus_mul_X0m_mul_inv]
    exact (mem_X0m_iff' σ _).2 ⟨_, rfl⟩
  · obtain ⟨c, rfl⟩ := (mem_X0m_iff' σ x).1 hx
    have e : (n0G σ * hG σ a2 u * (n0G σ)⁻¹)⁻¹ * (n0G σ * yG σ a2 c * (n0G σ)⁻¹) *
        (n0G σ * hG σ a2 u * (n0G σ)⁻¹) =
          n0G σ * ((hG σ a2 u)⁻¹ * yG σ a2 c * hG σ a2 u) * (n0G σ)⁻¹ := by group
    rw [e, hG_inv_mul_yG_mul]
    exact (mem_X0m_iff' σ _).2 ⟨_, rfl⟩

theorem torus_mem_SL2 (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
    n0G σ * hG σ a2 u * (n0G σ)⁻¹ ∈ twE6LongRootSL2 Xpos Xneg := by
  have hx : ∀ c : orbitField TwistTag.E6 K σ.toRingHom a2,
      n0G σ * xG σ a2 c * (n0G σ)⁻¹ ∈ twE6LongRootSL2 Xpos Xneg := fun c =>
    Subgroup.subset_closure (Or.inl ((mem_X0_iff' σ _).2 ⟨c, rfl⟩))
  have hy : ∀ c : orbitField TwistTag.E6 K σ.toRingHom a2,
      n0G σ * yG σ a2 c * (n0G σ)⁻¹ ∈ twE6LongRootSL2 Xpos Xneg := fun c =>
    Subgroup.subset_closure (Or.inr ((mem_X0m_iff' σ _).2 ⟨c, rfl⟩))
  rw [hG_eq]
  have e : ∀ (P Q : twistedE6RootGroup K σ), n0G σ * (P * Q⁻¹) * (n0G σ)⁻¹ =
      (n0G σ * P * (n0G σ)⁻¹) * (n0G σ * Q * (n0G σ)⁻¹)⁻¹ := fun P Q => by group
  have e3 : ∀ (P Q R : twistedE6RootGroup K σ), n0G σ * (P * Q * R) * (n0G σ)⁻¹ =
      (n0G σ * P * (n0G σ)⁻¹) * (n0G σ * Q * (n0G σ)⁻¹) * (n0G σ * R * (n0G σ)⁻¹) :=
    fun P Q R => by group
  rw [e, e3, e3]
  exact mul_mem (mul_mem (mul_mem (hx _) (hy _)) (hx _))
    (inv_mem (mul_mem (mul_mem (hx _) (hy _)) (hx _)))

end Torus

end LeviAux

section Public

theorem n0G_conj_hG_mem_twE6LongRootTorus (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
    n0G σ * hG σ a2 u * (n0G σ)⁻¹ ∈ twE6LongRootTorus (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨LeviAux.torus_mem_SL2 σ u, LeviAux.torus_mem_normalizer_X0 σ u⟩,
    LeviAux.torus_mem_normalizer_X0m σ u⟩

end Public

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
