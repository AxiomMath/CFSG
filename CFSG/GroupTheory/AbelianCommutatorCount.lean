module

public import Mathlib.GroupTheory.Index
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_stable_card_mul_le {L V K : Subgroup G}
    (hL : ∀ x ∈ L, ∀ y ∈ L, Commute x y) (hVL : V ≤ L) (hKL : K ≤ L) {g : G}
    (hg : L.map (MulAut.conj g).toMonoidHom = L) (hK : ∀ x ∈ K, Commute g x) :
    ∃ X : Subgroup G, V ≤ X ∧ X.map (MulAut.conj g).toMonoidHom = X ∧
      Nat.card X * Nat.card K ≤ Nat.card V * Nat.card L := by
  classical
  letI : CommGroup ↥L :=
    { (inferInstance : Group ↥L) with
      mul_comm := fun x y => Subtype.ext (hL x x.2 y y.2).eq }
  let c : ↥L →* ↥L :=
    { toFun := fun x => ⟨(MulAut.conj g) (x : G), by
        have hx := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom x.2
        rwa [hg] at hx⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  let φ : ↥L →* ↥L := c * (MonoidHom.id ↥L)⁻¹
  have hφ : ∀ x : ↥L, (φ x : G) = g * (x : G) * g⁻¹ * (x : G)⁻¹ := fun x => by
    simp [φ, c, MulAut.conj_apply, mul_assoc]
  let kL : Subgroup ↥L := K.comap L.subtype
  have hcardK : Nat.card K = Nat.card kL := Nat.card_congr
    ⟨fun x => ⟨⟨x.1, hKL x.2⟩, x.2⟩, fun x => ⟨x.1.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hKker : kL ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]; apply Subtype.ext; rw [hφ]
    have hxg : g * (x : G) * g⁻¹ = (x : G) := by
      rw [(hK (x : G) hx).eq]; group
    rw [hxg, mul_inv_cancel]; rfl
  let R : Subgroup G := φ.range.map L.subtype
  let X : Subgroup G := V ⊔ R
  have hRL : R ≤ L := Subgroup.map_subtype_le φ.range
  have hVR : ∀ x ∈ V, ∀ y ∈ R, Commute x y := fun x hx y hy =>
    hL x (hVL hx) y (hRL hy)
  have hcφ : ∀ x : ↥L, c (φ x) = φ (c x) := fun x => by
    apply Subtype.ext
    change g * (φ x : G) * g⁻¹ = g * (c x : G) * g⁻¹ * (c x : G)⁻¹
    rw [hφ x]
    simp [c, MulAut.conj_apply, mul_assoc]
  have hVmap : V.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨v, hv, rfl⟩
    have hmem : (MulAut.conj g) v * v⁻¹ ∈ R :=
      Subgroup.mem_map_of_mem L.subtype (show φ ⟨v, hVL hv⟩ ∈ φ.range from ⟨_, rfl⟩)
    change (MulAut.conj g) v ∈ X
    rw [show (MulAut.conj g) v = (MulAut.conj g) v * v⁻¹ * v by group]
    simpa [X, sup_comm] using (Subgroup.mul_mem_sup hmem hv : _ ∈ R ⊔ V)
  have hRmap : R.map (MulAut.conj g).toMonoidHom ≤ R := by
    rintro _ ⟨r, hr, rfl⟩
    rcases Subgroup.mem_map.1 hr with ⟨y, hy, rfl⟩
    rcases MonoidHom.mem_range.1 hy with ⟨x, rfl⟩
    change (MulAut.conj g) ((φ x : ↥L) : G) ∈ R
    have h : (MulAut.conj g) ((φ x : ↥L) : G) = ((φ (c x) : ↥L) : G) := by
      rw [← hcφ x]; rfl
    rw [h]
    exact Subgroup.mem_map_of_mem L.subtype (show φ (c x) ∈ φ.range from ⟨_, rfl⟩)
  have hXmap_le : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [show X = V ⊔ R from rfl, Subgroup.map_sup]
    exact sup_le hVmap (hRmap.trans le_sup_right)
  have hXmap : X.map (MulAut.conj g).toMonoidHom = X := by
    refine Subgroup.eq_of_le_of_card_ge hXmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hcardR : Nat.card R = Nat.card φ.range :=
    Subgroup.card_map_of_injective (K := φ.range) L.subtype_injective
  have hsup_le : Nat.card X ≤ Nat.card V * Nat.card R := by
    have hcard := (card_sup_mul_card_inf_of_commute V R
      (fun x hx y hy => (hVR x hx y hy).eq)).1
    have hpos : 0 < Nat.card ↥(V ⊓ R) := Nat.card_pos
    calc
      Nat.card X = Nat.card ↥(V ⊔ R) := rfl
      _ ≤ Nat.card ↥(V ⊔ R) * Nat.card ↥(V ⊓ R) := Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card V * Nat.card R := hcard
  refine ⟨X, le_sup_left, hXmap, ?_⟩
  calc
    Nat.card X * Nat.card K = Nat.card X * Nat.card kL := by rw [hcardK]
    _ ≤ (Nat.card V * Nat.card R) * Nat.card φ.ker :=
      Nat.mul_le_mul hsup_le (Subgroup.card_le_of_le hKker)
    _ = Nat.card V * (Nat.card φ.range * Nat.card φ.ker) := by rw [hcardR, Nat.mul_assoc]
    _ = Nat.card V * (Nat.card φ.ker * Nat.card φ.range) := by
      rw [Nat.mul_comm (Nat.card φ.range) (Nat.card φ.ker)]
    _ = Nat.card V * Nat.card ↥L := by rw [Subgroup.card_ker_mul_card_range φ]
    _ = Nat.card V * Nat.card L := rfl

end CFSG.GroupTheory
