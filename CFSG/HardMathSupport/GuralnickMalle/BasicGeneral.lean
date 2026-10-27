module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

@[expose] def fixSubGen (ρ : Representation K G V) (A : Subgroup G) : Submodule K V where
  carrier := {w | ∀ a ∈ A, ρ a w = w}
  add_mem' {v w} hv hw a ha := by rw [map_add, hv a ha, hw a ha]
  zero_mem' a _ := map_zero _
  smul_mem' c v hv a ha := by rw [map_smul, hv a ha]

theorem mem_fixSubGen {ρ : Representation K G V} {A : Subgroup G} {w : V} :
    w ∈ fixSubGen ρ A ↔ ∀ a ∈ A, ρ a w = w :=
  Iff.rfl

theorem fixSubGen_antitone {ρ : Representation K G V} {A B : Subgroup G} (h : A ≤ B) :
    fixSubGen ρ B ≤ fixSubGen ρ A :=
  fun _ hw a ha => hw a (h ha)

theorem fixSubGen_sup (ρ : Representation K G V) (A B : Subgroup G) :
    fixSubGen ρ (A ⊔ B) = fixSubGen ρ A ⊓ fixSubGen ρ B := by
  refine le_antisymm (le_inf (fixSubGen_antitone le_sup_left)
    (fixSubGen_antitone le_sup_right)) ?_
  rintro w ⟨hA, hB⟩ x hx
  let S : Subgroup G :=
    { carrier := {g | ρ g w = w}
      mul_mem' := fun {g h} hg hh => by
        change ρ (g * h) w = w
        rw [map_mul, Module.End.mul_apply, hh, hg]
      one_mem' := by change ρ 1 w = w; rw [map_one, Module.End.one_apply]
      inv_mem' := fun {g} hg => by
        change ρ g⁻¹ w = w
        conv_lhs => rw [← hg]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] }
  have : A ⊔ B ≤ S := sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  exact this hx

@[expose] noncomputable def weight1Gen (ρ : Representation K G V) (A : Subgroup G) : ℕ :=
  Nat.card A * Nat.card (fixSubGen ρ A)

theorem weight1Gen_pos [Finite G] [Finite V] (ρ : Representation K G V) (A : Subgroup G) :
    0 < weight1Gen ρ A := by
  rw [weight1Gen]
  exact Nat.mul_pos Nat.card_pos Nat.card_pos

theorem sup_fixSubGen_le (ρ : Representation K G V) (A B : Subgroup G) :
    fixSubGen ρ A ⊔ fixSubGen ρ B ≤ fixSubGen ρ (A ⊓ B) :=
  sup_le (fixSubGen_antitone inf_le_left) (fixSubGen_antitone inf_le_right)

section FiniteV

variable [Finite V]

theorem card_inf_mul_card_sup (X Y : Submodule K V) :
    Nat.card ↥(X ⊓ Y) * Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
  have hc : ∀ S : Submodule K V, Nat.card S = Nat.card K ^ Module.finrank K S :=
    fun S => Module.natCard_eq_pow_finrank
  rw [hc, hc, hc, hc, ← pow_add, ← pow_add]
  congr 1
  omega

theorem card_sup_fixSubGen_le (ρ : Representation K G V) (A B : Subgroup G) :
    Nat.card ↥(fixSubGen ρ A ⊔ fixSubGen ρ B) ≤ Nat.card (fixSubGen ρ (A ⊓ B)) :=
  Nat.card_le_card_of_injective (Submodule.inclusion (sup_fixSubGen_le ρ A B))
    (Submodule.inclusion_injective (sup_fixSubGen_le ρ A B))

theorem card_mul_card_fixSubGen_le (ρ : Representation K G V) (A B : Subgroup G) :
    Nat.card (fixSubGen ρ A) * Nat.card (fixSubGen ρ B) ≤
      Nat.card (fixSubGen ρ (A ⊔ B)) * Nat.card (fixSubGen ρ (A ⊓ B)) := by
  have hsup := card_sup_fixSubGen_le ρ A B
  have hcc := card_inf_mul_card_sup (fixSubGen ρ A) (fixSubGen ρ B)
  rw [fixSubGen_sup ρ A B]
  calc Nat.card (fixSubGen ρ A) * Nat.card (fixSubGen ρ B)
      = Nat.card ↥(fixSubGen ρ A ⊓ fixSubGen ρ B) *
          Nat.card ↥(fixSubGen ρ A ⊔ fixSubGen ρ B) := hcc.symm
    _ ≤ Nat.card ↥(fixSubGen ρ A ⊓ fixSubGen ρ B) *
          Nat.card (fixSubGen ρ (A ⊓ B)) := Nat.mul_le_mul_left _ hsup

end FiniteV

theorem fixSubGen_map_conj (ρ : Representation K G V) (A : Subgroup G) (g : G) :
    fixSubGen ρ (A.map (MulAut.conj g).toMonoidHom) = (fixSubGen ρ A).map (ρ g) := by
  ext w
  constructor
  · intro hw
    refine Submodule.mem_map.2 ⟨ρ (g⁻¹) w, ?_, ?_⟩
    · intro a ha
      have h1 : ρ (g * a * g⁻¹) w = w :=
        hw ((MulAut.conj g).toMonoidHom a) (Subgroup.mem_map.2 ⟨a, ha, rfl⟩)
      calc ρ a (ρ (g⁻¹) w) = ρ (a * g⁻¹) w := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (g⁻¹ * (g * a * g⁻¹)) w := by
              rw [show a * g⁻¹ = g⁻¹ * (g * a * g⁻¹) by group]
        _ = ρ (g⁻¹) (ρ (g * a * g⁻¹) w) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (g⁻¹) w := by rw [h1]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
  · rintro ⟨u, hu, hw⟩ x hx
    rw [← hw]
    obtain ⟨a, ha, hx'⟩ := Subgroup.mem_map.1 hx
    rw [← hx']
    calc ρ ((MulAut.conj g).toMonoidHom a) (ρ g u)
        = ρ ((MulAut.conj g).toMonoidHom a * g) u := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * a) u := by
          rw [show (MulAut.conj g).toMonoidHom a * g = g * a by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group]
      _ = ρ g (ρ a u) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ g u := by rw [hu a ha]

theorem card_fixSubGen_map_conj (ρ : Representation K G V) (A : Subgroup G) (g : G) :
    Nat.card (fixSubGen ρ (A.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (fixSubGen ρ A) := by
  have hinj : Function.Injective (ρ g) := by
    intro u v huv
    have h1 : ρ (g⁻¹) (ρ g u) = ρ (g⁻¹) (ρ g v) := congrArg (ρ (g⁻¹)) huv
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h1
    exact h1
  rw [fixSubGen_map_conj ρ A g]
  exact (Nat.card_congr
    (Submodule.equivMapOfInjective (ρ g) hinj (fixSubGen ρ A)).toEquiv).symm

theorem weight1Gen_map_conj (ρ : Representation K G V) (A : Subgroup G) (g : G) :
    weight1Gen ρ (A.map (MulAut.conj g).toMonoidHom) = weight1Gen ρ A := by
  rw [weight1Gen, weight1Gen, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    card_fixSubGen_map_conj ρ A g]

end CFSG.HardMathSupport.GuralnickMalle
