module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB

namespace Up34Chev2

section Embed

private theorem comm_of_central_mul {C : Type} [Group C] {x w g u : C} (hu : u = x * w)
    (hz : g * u = u * g) (hgw : g * w = w * g) : g * x = x * g := by
  subst hu
  apply mul_right_cancel (b := w)
  calc g * x * w = g * (x * w) := mul_assoc _ _ _
    _ = x * w * g := hz
    _ = x * (w * g) := mul_assoc _ _ _
    _ = x * (g * w) := by rw [hgw]
    _ = x * g * w := (mul_assoc _ _ _).symm

variable {C : Type} [Group C]

private theorem commuteOfEq {a b : C} (h : a * b = b * a) : Commute a b := h

theorem card_mul_dvd_card_centerQuotient [Finite C] (X Y Z : Subgroup C)
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) (hXZ : ∀ a ∈ X, ∀ b ∈ Z, a * b = b * a)
    (hYZ : ∀ a ∈ Y, ∀ b ∈ Z, a * b = b * a)
    (cX : ∀ a ∈ X, (∀ b ∈ X, a * b = b * a) → a = 1)
    (cY : ∀ a ∈ Y, (∀ b ∈ Y, a * b = b * a) → a = 1)
    (cZ : ∀ a ∈ Z, (∀ b ∈ Z, a * b = b * a) → a = 1) :
    Nat.card X * Nat.card Y * Nat.card Z ∣ Nat.card (C ⧸ Subgroup.center C) := by
  classical
  let φ₁ : ↥X × ↥Y →* C := MonoidHom.noncommCoprod X.subtype Y.subtype
    (fun x y => commuteOfEq (hXY x x.2 y y.2))
  let φ : (↥X × ↥Y) × ↥Z →* C := MonoidHom.noncommCoprod φ₁ Z.subtype (fun p z =>
    commuteOfEq (by
      change (p.1 : C) * (p.2 : C) * (z : C) = (z : C) * ((p.1 : C) * (p.2 : C))
      exact (Commute.mul_left (commuteOfEq (hXZ _ p.1.2 _ z.2))
        (commuteOfEq (hYZ _ p.2.2 _ z.2))).eq))
  have hφ : ∀ p : (↥X × ↥Y) × ↥Z, φ p = (p.1.1 : C) * (p.1.2 : C) * (p.2 : C) := fun p => rfl
  let ψ : (↥X × ↥Y) × ↥Z →* C ⧸ Subgroup.center C :=
    (QuotientGroup.mk' (Subgroup.center C)).comp φ
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨x, y⟩, z⟩ h
    have hc : φ ((x, y), z) ∈ Subgroup.center C := (QuotientGroup.eq_one_iff _).1 h
    rw [hφ] at hc
    have hz := Subgroup.mem_center_iff.1 hc
    simp only at hz
    have hxy : (x : C) * (y : C) = (y : C) * (x : C) := hXY _ x.2 _ y.2
    have hx1 : (x : C) = 1 := by
      refine cX x x.2 fun g hg => ?_
      have hgy : g * (y : C) = (y : C) * g := hXY g hg _ y.2
      have hgz : g * (z : C) = (z : C) * g := hXZ g hg _ z.2
      have hgw : g * ((y : C) * (z : C)) = ((y : C) * (z : C)) * g := by
        rw [← mul_assoc, hgy, mul_assoc, hgz, mul_assoc]
      exact (comm_of_central_mul (w := (y : C) * (z : C)) (by rw [mul_assoc]) (hz g) hgw).symm
    have hy1 : (y : C) = 1 := by
      refine cY y y.2 fun g hg => ?_
      have hgx : g * (x : C) = (x : C) * g := (hXY _ x.2 g hg).symm
      have hgz : g * (z : C) = (z : C) * g := hYZ g hg _ z.2
      have hgw : g * ((x : C) * (z : C)) = ((x : C) * (z : C)) * g := by
        rw [← mul_assoc, hgx, mul_assoc, hgz, mul_assoc]
      exact (comm_of_central_mul (w := (x : C) * (z : C)) (x := (y : C))
        (by rw [hxy, mul_assoc]) (hz g) hgw).symm
    have hz1 : (z : C) = 1 := by
      refine cZ z z.2 fun g hg => ?_
      have hgx : g * (x : C) = (x : C) * g := (hXZ _ x.2 g hg).symm
      have hgy : g * (y : C) = (y : C) * g := (hYZ _ y.2 g hg).symm
      have hgw : g * ((x : C) * (y : C)) = ((x : C) * (y : C)) * g := by
        rw [← mul_assoc, hgx, mul_assoc, hgy, mul_assoc]
      have hxyz : (x : C) * (y : C) * (z : C) = (z : C) * ((x : C) * (y : C)) :=
        (Commute.mul_left (commuteOfEq (hXZ _ x.2 _ z.2))
          (commuteOfEq (hYZ _ y.2 _ z.2))).eq
      exact (comm_of_central_mul (w := (x : C) * (y : C)) (x := (z : C)) hxyz (hz g) hgw).symm
    exact Prod.ext (Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)) (Subtype.ext hz1)
  have hdvd : Nat.card ((↥X × ↥Y) × ↥Z) ∣ Nat.card (C ⧸ Subgroup.center C) :=
    Subgroup.card_dvd_of_injective ψ hinj
  rwa [Nat.card_prod, Nat.card_prod] at hdvd

end Embed

section Bad

variable {G : Type} [Group G]

@[expose] def Bad3 (P : Subgroup G) : Prop :=
  ∃ X Y Z : Subgroup G, X ≤ P ∧ Y ≤ P ∧ Z ≤ P ∧
    (∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) ∧ (∀ a ∈ X, ∀ b ∈ Z, a * b = b * a) ∧
    (∀ a ∈ Y, ∀ b ∈ Z, a * b = b * a) ∧
    (∀ a ∈ X, (∀ b ∈ X, a * b = b * a) → a = 1) ∧
    (∀ a ∈ Y, (∀ b ∈ Y, a * b = b * a) → a = 1) ∧
    (∀ a ∈ Z, (∀ b ∈ Z, a * b = b * a) → a = 1) ∧
    ¬ (Nat.card X * Nat.card Y * Nat.card Z ∣ 20160)

theorem centerless_map_conj {X : Subgroup G} (g : G)
    (cX : ∀ a ∈ X, (∀ b ∈ X, a * b = b * a) → a = 1) :
    ∀ a ∈ X.map (MulAut.conj g).toMonoidHom,
      (∀ b ∈ X.map (MulAut.conj g).toMonoidHom, a * b = b * a) → a = 1 := by
  rintro _ ⟨x, hx, rfl⟩ h
  have : x = 1 := cX x hx fun b hb => by
    have := h _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    have h2 : g * (x * b) * g⁻¹ = g * (b * x) * g⁻¹ := by
      calc g * (x * b) * g⁻¹ = g * x * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * x * g⁻¹) := this
        _ = g * (b * x) * g⁻¹ := by group
    simpa using h2
  rw [this]
  simp

theorem Bad3.map_conj {P : Subgroup G} (h : Bad3 P) (g : G) :
    Bad3 (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hXY, hXZ, hYZ, cX, cY, cZ, hn⟩ := h
  have hcomm : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ∀ b ∈ B.map (MulAut.conj g).toMonoidHom,
        a * b = b * a := by
    rintro A B hAB _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hAB x hx y hy]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  have hcard : ∀ A : Subgroup G, Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    fun A => Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨X.map (MulAut.conj g).toMonoidHom, Y.map (MulAut.conj g).toMonoidHom,
    Z.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hX, Subgroup.map_mono hY,
    Subgroup.map_mono hZ, hcomm hXY, hcomm hXZ, hcomm hYZ, centerless_map_conj g cX,
    centerless_map_conj g cY, centerless_map_conj g cZ, ?_⟩
  rw [hcard, hcard, hcard]
  exact hn

theorem not_isLThreeFour_of_bad3 {R : Subgroup G} [Finite R] (hB : Bad3 R)
    (h : IsLThreeFour (↥R ⧸ Subgroup.center ↥R)) : False := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hXY, hXZ, hYZ, cX, cY, cZ, hn⟩ := hB
  let X' : Subgroup ↥R := X.subgroupOf R
  let Y' : Subgroup ↥R := Y.subgroupOf R
  let Z' : Subgroup ↥R := Z.subgroupOf R
  have hmem : ∀ {A : Subgroup G} (a : ↥R), a ∈ A.subgroupOf R ↔ (a : G) ∈ A := fun a =>
    Subgroup.mem_subgroupOf
  have hcomm : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ a ∈ A.subgroupOf R, ∀ b ∈ B.subgroupOf R, a * b = b * a := by
    intro A B hAB a ha b hb
    exact Subtype.ext (hAB _ ha _ hb)
  have hcl : ∀ {A : Subgroup G}, A ≤ R → (∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) →
      ∀ a ∈ A.subgroupOf R, (∀ b ∈ A.subgroupOf R, a * b = b * a) → a = 1 := by
    intro A hA cA a ha hab
    apply Subtype.ext
    refine cA _ ha fun b hb => ?_
    have := hab ⟨b, hA hb⟩ hb
    exact congrArg Subtype.val this
  have hcardA : ∀ {A : Subgroup G}, A ≤ R → Nat.card (A.subgroupOf R) = Nat.card A :=
    fun {A} hA => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hdvd := card_mul_dvd_card_centerQuotient X' Y' Z' (hcomm hXY) (hcomm hXZ) (hcomm hYZ)
    (hcl hX cX) (hcl hY cY) (hcl hZ cZ)
  rw [hcardA hX, hcardA hY, hcardA hZ, card_eq_of_isLThreeFour h] at hdvd
  exact hn hdvd

end Bad

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
