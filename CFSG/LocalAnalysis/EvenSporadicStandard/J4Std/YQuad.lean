module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.J4Std.YExists

variable {G : Type*} [Group G]

structure CentralSq (P Z : Subgroup G) : Prop where
  le : Z ≤ P
  central : ∀ p ∈ P, ∀ u ∈ Z, p * u = u * p
  sq_self : ∀ u ∈ Z, u * u = 1
  sq_mem : ∀ p ∈ P, p * p ∈ Z

namespace CentralSq

variable {P Z : Subgroup G} (h : CentralSq P Z)
include h

theorem comm {u v : G} (hu : u ∈ Z) (hv : v ∈ Z) : u * v = v * u :=
  h.central u (h.le hu) v hv

theorem exists_swap {a b : G} (ha : a ∈ P) (hb : b ∈ P) : ∃ k ∈ Z, b * a = a * b * k := by
  have h1 := h.sq_mem (a * b) (P.mul_mem ha hb)
  have h2 := h.sq_mem a ha
  have h3 := h.sq_mem b hb
  generalize hs1 : a * b * (a * b) = s1 at h1
  generalize hs2 : a * a = s2 at h2
  generalize hs3 : b * b = s3 at h3
  have ea : a⁻¹ = s2⁻¹ * a := by rw [← hs2]; group
  have eb : b⁻¹ = s3⁻¹ * b := by rw [← hs3]; group
  have e : b * a = a⁻¹ * s1 * b⁻¹ := by rw [← hs1]; group
  have hk : s2⁻¹ * s1 * s3⁻¹ ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem h2) h1) (Z.inv_mem h3)
  refine ⟨s2⁻¹ * s1 * s3⁻¹, hk, ?_⟩
  have ca1 := h.central a ha s1 h1
  have ca3 := h.central a ha s3⁻¹ (Z.inv_mem h3)
  have cab := h.central (a * b) (P.mul_mem ha hb) _ hk
  calc b * a = a⁻¹ * s1 * b⁻¹ := e
    _ = (s2⁻¹ * a) * s1 * (s3⁻¹ * b) := by rw [ea, eb]
    _ = s2⁻¹ * (a * s1) * (s3⁻¹ * b) := by group
    _ = s2⁻¹ * (s1 * a) * (s3⁻¹ * b) := by rw [ca1]
    _ = s2⁻¹ * s1 * (a * s3⁻¹) * b := by group
    _ = s2⁻¹ * s1 * (s3⁻¹ * a) * b := by rw [ca3]
    _ = (s2⁻¹ * s1 * s3⁻¹) * (a * b) := by group
    _ = a * b * (s2⁻¹ * s1 * s3⁻¹) := cab.symm

theorem sq_mul_of_swap {a b k : G} (hb : b ∈ P) (hk : k ∈ Z) (e : b * a = a * b * k) :
    (a * b) * (a * b) = (a * a) * (b * b) * k := by
  have hkb := h.central b hb k hk
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b * k) * b := by rw [e]
    _ = (a * a) * b * (k * b) := by group
    _ = (a * a) * b * (b * k) := by rw [hkb]
    _ = (a * a) * (b * b) * k := by group

end CentralSq

section Aux

variable {Z : Subgroup G}

theorem aux_poly3 {A : Type*} [CommGroup A] (hsq : ∀ x : A, x * x = 1) (sx sy sw k1 k2 k3 : A) :
    sx * sy * k1 * sw * (k3 * k2) * (sx * sy * k1) * (sx * sw * k2) * (sy * sw * k3) * sx * sy *
      sw = 1 := by
  calc sx * sy * k1 * sw * (k3 * k2) * (sx * sy * k1) * (sx * sw * k2) * (sy * sw * k3) * sx * sy *
        sw = (sx * sx) * (sx * sx) * ((sy * sy) * (sy * sy)) * ((sw * sw) * (sw * sw)) *
          (k1 * k1) * (k2 * k2) * (k3 * k3) := by ac_rfl
    _ = 1 := by simp [hsq]

theorem Z_poly3 (hcomm : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hsq : ∀ u ∈ Z, u * u = 1)
    {sx sy sw k1 k2 k3 : G} (hsx : sx ∈ Z) (hsy : sy ∈ Z) (hsw : sw ∈ Z) (hk1 : k1 ∈ Z)
    (hk2 : k2 ∈ Z) (hk3 : k3 ∈ Z) :
    sx * sy * k1 * sw * (k3 * k2) * (sx * sy * k1) * (sx * sw * k2) * (sy * sw * k3) * sx * sy *
      sw = 1 := by
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have := aux_poly3 (A := Z) (fun x => Subtype.ext (hsq x x.2)) ⟨sx, hsx⟩ ⟨sy, hsy⟩ ⟨sw, hsw⟩
    ⟨k1, hk1⟩ ⟨k2, hk2⟩ ⟨k3, hk3⟩
  simpa using congrArg Subtype.val this

theorem Z_aux1 (hcomm : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hsq : ∀ u ∈ Z, u * u = 1)
    {a b c : G} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) : b * c * a * b * c = a := by
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hs : ∀ x : Z, x * x = 1 := fun x => Subtype.ext (hsq x x.2)
  have key : ∀ x y w : Z, y * w * x * y * w = x := by
    intro x y w
    calc y * w * x * y * w = x * (y * y) * (w * w) := by ac_rfl
      _ = x := by simp [hs]
  simpa using congrArg Subtype.val (key ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩)

theorem Z_aux2 (hcomm : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hsq : ∀ u ∈ Z, u * u = 1)
    {a b c : G} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) :
    a * b * c * (a * b) * (a * c) = a := by
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hs : ∀ x : Z, x * x = 1 := fun x => Subtype.ext (hsq x x.2)
  have key : ∀ x y w : Z, x * y * w * (x * y) * (x * w) = x := by
    intro x y w
    calc x * y * w * (x * y) * (x * w) = (x * x) * x * ((y * y) * (w * w)) := by ac_rfl
      _ = x := by simp [hs]
  simpa using congrArg Subtype.val (key ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩)

end Aux

namespace CentralSq

variable {P Z : Subgroup G} (h : CentralSq P Z)
include h

theorem poly3 {x y w : G} (hx : x ∈ P) (hy : y ∈ P) (hw : w ∈ P) :
    x * y * w * (x * y * w) * (x * y * (x * y)) * (x * w * (x * w)) * (y * w * (y * w)) *
      (x * x) * (y * y) * (w * w) = 1 := by
  obtain ⟨k1, hk1, e1⟩ := h.exists_swap hx hy
  obtain ⟨k2, hk2, e2⟩ := h.exists_swap hx hw
  obtain ⟨k3, hk3, e3⟩ := h.exists_swap hy hw
  have c2y := h.central y hy k2 hk2
  have e4 : w * (x * y) = (x * y) * w * (k3 * k2) := by
    calc w * (x * y) = (w * x) * y := by group
      _ = (x * w * k2) * y := by rw [e2]
      _ = x * w * (k2 * y) := by group
      _ = x * w * (y * k2) := by rw [c2y]
      _ = x * (w * y) * k2 := by group
      _ = x * (y * w * k3) * k2 := by rw [e3]
      _ = (x * y) * w * (k3 * k2) := by group
  have s1 := h.sq_mul_of_swap hy hk1 e1
  have s2 := h.sq_mul_of_swap hw hk2 e2
  have s3 := h.sq_mul_of_swap hw hk3 e3
  have s4 := h.sq_mul_of_swap hw (Z.mul_mem hk3 hk2) e4
  have hxx := h.sq_mem x hx
  have hyy := h.sq_mem y hy
  have hww := h.sq_mem w hw
  rw [s4, s1, s2, s3]
  generalize x * x = sx at *
  generalize y * y = sy at *
  generalize w * w = sw at *
  exact Z_poly3 (fun u hu v hv => h.comm hu hv) h.sq_self hxx hyy hww hk1 hk2 hk3

end CentralSq

section Triple

variable {Z : Subgroup G}

theorem typ_iff_of_triple (hcomm : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hsq : ∀ u ∈ Z, u * u = 1)
    (Q : G → G) (hQ : ∀ x ∈ Z, x ≠ 1 → Q x = 1 ∨ Q x = x)
    (hpol : ∀ x ∈ Z, ∀ y ∈ Z, ∀ w ∈ Z,
      Q (x * y * w) * Q (x * y) * Q (x * w) * Q (y * w) * Q x * Q y * Q w = 1)
    {a b c : G} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) (ha1 : a ≠ 1) (hab1 : a * b ≠ 1)
    (hac1 : a * c ≠ 1) (habc1 : a * b * c ≠ 1)
    (h1 : Q b = b ↔ Q a = a) (h2 : Q c = c ↔ Q a = a) (h3 : Q (b * c) = b * c ↔ Q a = a)
    (h4 : Q (a * c) = a * c ↔ Q (a * b) = a * b)
    (h5 : Q (a * b * c) = a * b * c ↔ Q (a * b) = a * b)
    (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hbc1 : b * c ≠ 1) :
    Q a = a ↔ Q (a * b) = a * b := by
  have hab : a * b ∈ Z := Z.mul_mem ha hb
  have hac : a * c ∈ Z := Z.mul_mem ha hc
  have habc : a * b * c ∈ Z := Z.mul_mem hab hc
  have hbc : b * c ∈ Z := Z.mul_mem hb hc
  have hone : ∀ x ∈ Z, x ≠ 1 → ¬ Q x = x → Q x = 1 := fun x hx hx1 hn =>
    (hQ x hx hx1).resolve_right hn
  have hp := hpol a ha b hb c hc
  by_cases hA : Q a = a <;> by_cases hB : Q (a * b) = a * b
  · exact ⟨fun _ => hB, fun _ => hA⟩
  · exfalso
    have e1 : Q (a * b) = 1 := hone _ hab hab1 hB
    have e2 : Q (a * c) = 1 := hone _ hac hac1 (fun h => hB (h4.1 h))
    have e3 : Q (a * b * c) = 1 := hone _ habc habc1 (fun h => hB (h5.1 h))
    rw [e1, e2, e3, h1.2 hA, h2.2 hA, h3.2 hA, hA, one_mul, one_mul, one_mul] at hp
    exact ha1 ((Z_aux1 hcomm hsq ha hb hc).symm.trans hp)
  · exfalso
    have e1 : Q a = 1 := hone _ ha ha1 hA
    have e2 : Q b = 1 := hone _ hb hb1 (fun h => hA (h1.1 h))
    have e3 : Q c = 1 := hone _ hc hc1 (fun h => hA (h2.1 h))
    have e4 : Q (b * c) = 1 := hone _ hbc hbc1 (fun h => hA (h3.1 h))
    rw [e1, e2, e3, e4, h4.2 hB, h5.2 hB, hB] at hp
    simp only [mul_one] at hp
    exact ha1 ((Z_aux2 hcomm hsq ha hb hc).symm.trans hp)
  · exact ⟨fun h => absurd h hA, fun h => absurd h hB⟩

end Triple

end CFSG.EvenSporadicStandard.J4Std.YExists
