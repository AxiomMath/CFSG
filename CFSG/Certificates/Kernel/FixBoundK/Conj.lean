module

public import CFSG.Monster.VisQuot.FixModOmega

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot

@[expose] def FixBoundAt (P : Subgroup AutPerm) : Prop :=
  ∀ X : Submodule (ZMod 2) C, ΩC ∈ X → X ≤ fixModΩ P →
    Nat.card X * Nat.card P * 2 ^ 11 * Nat.card ↥(compatC X ⊓ fixModΩ P) ≤
      2 ^ 14 * Nat.card ↥(commΩ P ⊔ X ⊔ (compatC X ⊓ fixModΩ P))

theorem fixBound_iff : FixBound ↔ ∀ P : Subgroup AutPerm,
    (∀ p ∈ P, (p : Equiv.Perm (Fin 24)) ∈ CFSG.Monster.B.TwoA.Census.sylowSub) →
    CFSG.Open.IsElemAbelian 2 P → FixBoundAt P := Iff.rfl

abbrev conjSub (g : AutPerm) (P : Subgroup AutPerm) : Subgroup AutPerm :=
  P.map (MulAut.conj g).toMonoidHom

abbrev permL (g : AutPerm) : C →ₗ[ZMod 2] C := (permC g : C →ₗ[ZMod 2] C)

theorem mem_conjSub {g : AutPerm} {P : Subgroup AutPerm} {q : AutPerm} :
    q ∈ conjSub g P ↔ ∃ p ∈ P, g * p * g⁻¹ = q := by
  simp [conjSub, MulAut.conj_apply]

theorem permC_conj (g p : AutPerm) (c : C) :
    permC (g * p * g⁻¹) (permC g c) = permC g (permC p c) := by
  rw [permC_mul, ← permC_mul g⁻¹ g, inv_mul_cancel, permC_one, permC_mul]

theorem permC_conj_sub (g p : AutPerm) (c : C) :
    permC (g * p * g⁻¹) (permC g c) - permC g c = permC g (permC p c - c) := by
  rw [permC_conj, map_sub]

theorem permC_mem_ΩLine_iff (g : AutPerm) (v : C) : permC g v ∈ ΩLine ↔ v ∈ ΩLine := by
  rw [mem_ΩLine_iff, mem_ΩLine_iff, map_eq_zero_iff _ (permC g).injective, ← permC_ΩC g,
    (permC g).injective.eq_iff, permC_ΩC]

theorem mem_map_permL {g : AutPerm} {V : Submodule (ZMod 2) C} {c : C} :
    c ∈ V.map (permL g) ↔ (permC g).symm c ∈ V :=
  Submodule.mem_map_equiv V

theorem card_map_permL (g : AutPerm) (V : Submodule (ZMod 2) C) :
    Nat.card ↥(V.map (permL g)) = Nat.card V :=
  (Nat.card_congr (V.equivMapOfInjective _ (permC g).injective).toEquiv).symm

theorem map_permL_inf (g : AutPerm) (V W : Submodule (ZMod 2) C) :
    (V ⊓ W).map (permL g) = V.map (permL g) ⊓ W.map (permL g) :=
  Submodule.map_inf _ (permC g).injective

theorem fixModΩ_conj (g : AutPerm) (P : Subgroup AutPerm) :
    fixModΩ (conjSub g P) = (fixModΩ P).map (permL g) := by
  ext c
  rw [mem_map_permL, mem_fixModΩ, mem_fixModΩ]
  constructor
  · intro h p hp
    have h1 := h (g * p * g⁻¹) (mem_conjSub.2 ⟨p, hp, rfl⟩)
    rw [← (permC g).apply_symm_apply c, permC_conj_sub, permC_mem_ΩLine_iff] at h1
    exact h1
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := mem_conjSub.1 hq
    rw [← (permC g).apply_symm_apply c, permC_conj_sub, permC_mem_ΩLine_iff]
    exact h p hp

theorem commΩ_conj (g : AutPerm) (P : Subgroup AutPerm) :
    commΩ (conjSub g P) = (commΩ P).map (permL g) := by
  have hΩ : permL g ΩC = ΩC := permC_ΩC g
  rw [commΩ, commΩ, Submodule.map_span, Set.image_insert_eq, hΩ]
  congr 2
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨q, hq, c, rfl⟩
    obtain ⟨p, hp, rfl⟩ := mem_conjSub.1 hq
    refine ⟨permC p ((permC g).symm c) - (permC g).symm c, ⟨p, hp, _, rfl⟩, ?_⟩
    change permC g _ = _
    rw [← permC_conj_sub, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, ⟨p, hp, c, rfl⟩, rfl⟩
    exact ⟨g * p * g⁻¹, mem_conjSub.2 ⟨p, hp, rfl⟩, permC g c, (permC_conj_sub g p c).symm⟩

theorem coe_permC_mul (g : AutPerm) (u v : C) :
    (permC g u : Fin 24 → ZMod 2) * (permC g v : Fin 24 → ZMod 2) =
      permWord g ((u : Fin 24 → ZMod 2) * (v : Fin 24 → ZMod 2)) := by
  funext i
  rfl

theorem permWord_mem_iff (g : AutPerm) (x : Fin 24 → ZMod 2) : permWord g x ∈ C ↔ x ∈ C :=
  ((mem_AutPerm_iff_permWord.1 g.2 x).symm)

theorem compatC_map (g : AutPerm) (X : Submodule (ZMod 2) C) :
    compatC (X.map (permL g)) = (compatC X).map (permL g) := by
  ext c
  rw [mem_map_permL, mem_compatC, mem_compatC]
  constructor
  · intro h b hb
    have h1 := h (permC g b) (Submodule.mem_map_of_mem hb)
    rw [← (permC g).apply_symm_apply c, coe_permC_mul, permWord_mem_iff] at h1
    exact h1
  · intro h b hb
    obtain ⟨b', hb', e⟩ := Submodule.mem_map.1 hb
    rw [← e, ← (permC g).apply_symm_apply c]
    change (permC g _ : Fin 24 → ZMod 2) * (permC g b' : Fin 24 → ZMod 2) ∈ C
    rw [coe_permC_mul, permWord_mem_iff]
    exact h b' hb'

theorem card_conjSub (g : AutPerm) (P : Subgroup AutPerm) : Nat.card (conjSub g P) = Nat.card P :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem fixBoundAt_conj (g : AutPerm) {P : Subgroup AutPerm} (h : FixBoundAt P) :
    FixBoundAt (conjSub g P) := by
  intro X' hΩ hX'
  obtain ⟨X, rfl⟩ : ∃ X : Submodule (ZMod 2) C, X.map (permL g) = X' :=
    ⟨X'.comap (permL g), Submodule.map_comap_eq_of_surjective (permC g).surjective X'⟩
  rw [fixModΩ_conj] at hX' ⊢
  have hXF : X ≤ fixModΩ P := (Submodule.map_le_map_iff_of_injective (permC g).injective _ _).1 hX'
  have hsΩ : (permC g).symm ΩC = ΩC := by rw [LinearEquiv.symm_apply_eq, permC_ΩC]
  have hΩX : ΩC ∈ X := by
    have := mem_map_permL.1 hΩ
    rwa [hsΩ] at this
  have hb := h X hΩX hXF
  rw [commΩ_conj, compatC_map, ← map_permL_inf, ← Submodule.map_sup, ← Submodule.map_sup,
    card_map_permL, card_map_permL, card_map_permL, card_conjSub]
  exact hb

end CFSG.KC.FixBoundK
