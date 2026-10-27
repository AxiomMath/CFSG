module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

section Model

theorem r10_invol (g : UT3 F4c) (h : g * g = 1) : g.a = 0 ∨ g.b = 0 := by
  revert g
  decide +kernel

theorem r10_X_sq (g : UT3 F4c) (h : g.a = 0) : g * g = 1 := by
  revert g
  decide +kernel

theorem r10_Y_sq (g : UT3 F4c) (h : g.b = 0) : g * g = 1 := by
  revert g
  decide +kernel

theorem r10_X_comm (g h : UT3 F4c) (hg : g.a = 0) (hh : h.a = 0) : g * h = h * g := by
  revert g h
  decide +kernel

theorem r10_Y_comm (g h : UT3 F4c) (hg : g.b = 0) (hh : h.b = 0) : g * h = h * g := by
  revert g h
  decide +kernel

theorem r10_center (c : UT3 F4c) (h : ∀ y, c * y = y * c) : c.a = 0 ∧ c.b = 0 := by
  revert c
  decide +kernel

theorem r10_dec_XY (g : UT3 F4c) : g = ⟨0, g.b, g.c⟩ * ⟨g.a, 0, 0⟩ := by
  revert g
  decide +kernel

theorem r10_dec_YX (g : UT3 F4c) : g = ⟨g.a, 0, 0⟩ * ⟨0, g.b, g.c + g.a * g.b⟩ := by
  revert g
  decide +kernel

theorem r10_cent_X (x s : UT3 F4c) (hxa : x.a = 0) (hxb : x.b ≠ 0) (h : s * x = x * s) :
    s.a = 0 := by
  revert x s
  decide +kernel

theorem r10_cent_Y (x s : UT3 F4c) (hxb : x.b = 0) (hxa : x.a ≠ 0) (h : s * x = x * s) :
    s.b = 0 := by
  revert x s
  decide +kernel

theorem r10_comm_iff (x y : UT3 F4c) : x * y = y * x ↔ x.a * y.b = y.a * x.b := by
  constructor
  · intro h
    have h3 := congrArg UT3.c h
    simp only [UT3.mul_def] at h3
    linear_combination h3
  · intro h
    refine UT3.ext ?_ ?_ ?_ <;> simp only [UT3.mul_def]
    · ring
    · ring
    · linear_combination h

theorem r10_cent_pair_F4 : ∀ a₁ b₁ a₂ b₂ a b : F4c, a₁ * b₂ ≠ a₂ * b₁ → a * b₁ = a₁ * b →
    a * b₂ = a₂ * b → a = 0 ∧ b = 0 := by
  decide +kernel

theorem r10_cent_pair (d₁ d₂ c : UT3 F4c) (h : d₁ * d₂ ≠ d₂ * d₁) (h1 : c * d₁ = d₁ * c)
    (h2 : c * d₂ = d₂ * c) : c.a = 0 ∧ c.b = 0 := by
  rw [Ne, r10_comm_iff] at h
  rw [r10_comm_iff] at h1 h2
  exact r10_cent_pair_F4 d₁.a d₁.b d₂.a d₂.b c.a c.b h h1 h2

theorem r10_card_a : Nat.card {u : UT3 F4c // u.a = 0} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem r10_card_b : Nat.card {u : UT3 F4c // u.b = 0} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem r10_card_ab : Nat.card {u : UT3 F4c // u.a = 0 ∧ u.b = 0} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem r10_surj_X_aux : ∀ x : UT3 F4c, x.a = 0 → x.b ≠ 0 → ∀ c : F4c,
    ∃ y : UT3 F4c, y.b = 0 ∧ x * y * x⁻¹ * y⁻¹ = ⟨0, 0, c⟩ := by
  decide +kernel

theorem r10_surj_Y_aux : ∀ y : UT3 F4c, y.b = 0 → y.a ≠ 0 → ∀ c : F4c,
    ∃ x : UT3 F4c, x.a = 0 ∧ y * x * y⁻¹ * x⁻¹ = ⟨0, 0, c⟩ := by
  decide +kernel

theorem r10_comm_gen (c : F4c) :
    (⟨c, 0, 0⟩ * ⟨0, 1, 0⟩ * (⟨c, 0, 0⟩ : UT3 F4c)⁻¹ * (⟨0, 1, 0⟩ : UT3 F4c)⁻¹ : UT3 F4c) =
      ⟨0, 0, c⟩ := by
  revert c
  decide +kernel

end Model

section Bundle

variable {G : Type} [Group G]

structure SL34Data (R Z X Y : Subgroup G) : Prop where
  X_le : X ≤ R
  Y_le : Y ≤ R
  Z_le_R : Z ≤ R
  Z_central : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z
  comm_Z : ∀ z ∈ Z, ∃ r ∈ R, ∃ s ∈ R, r * s * r⁻¹ * s⁻¹ = z
  Z_le_X : Z ≤ X
  Z_le_Y : Z ≤ Y
  card_Z : Nat.card Z = 4
  card_X : Nat.card X = 16
  card_Y : Nat.card Y = 16
  inf_XY : X ⊓ Y = Z
  X_comm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a
  Y_comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a
  X_sq : ∀ a ∈ X, a * a = 1
  Y_sq : ∀ a ∈ Y, a * a = 1
  invol : ∀ g ∈ R, g * g = 1 → g ∈ X ∨ g ∈ Y
  dec_XY : ∀ g ∈ R, ∃ x ∈ X, ∃ y ∈ Y, g = x * y
  dec_YX : ∀ g ∈ R, ∃ y ∈ Y, ∃ x ∈ X, g = y * x
  surj_X : ∀ x ∈ X, x ∉ Z → ∀ z ∈ Z, ∃ y ∈ Y, x * y * x⁻¹ * y⁻¹ = z
  surj_Y : ∀ y ∈ Y, y ∉ Z → ∀ z ∈ Z, ∃ x ∈ X, y * x * y⁻¹ * x⁻¹ = z
  cent_X : ∀ a ∈ X, a ∉ Z → ∀ s ∈ R, s * a = a * s → s ∈ X
  cent_Y : ∀ a ∈ Y, a ∉ Z → ∀ s ∈ R, s * a = a * s → s ∈ Y
  cent_pair : ∀ d₁ ∈ R, ∀ d₂ ∈ R, d₁ * d₂ ≠ d₂ * d₁ → ∀ c ∈ R, c * d₁ = d₁ * c →
    c * d₂ = d₂ * c → c ∈ Z

end Bundle

section Transport

variable {G : Type} [Group G] {R : Subgroup G}

open scoped Classical in
@[expose] noncomputable def r10Phi (R : Subgroup G) (e : ↥R ≃* UT3 F4c) (g : G) : UT3 F4c :=
  if hg : g ∈ R then e ⟨g, hg⟩ else 1

theorem r10Phi_of_mem (e : ↥R ≃* UT3 F4c) {g : G} (hg : g ∈ R) :
    r10Phi R e g = e ⟨g, hg⟩ := dif_pos hg

theorem r10Phi_mul (e : ↥R ≃* UT3 F4c) {g h : G} (hg : g ∈ R) (hh : h ∈ R) :
    r10Phi R e (g * h) = r10Phi R e g * r10Phi R e h := by
  rw [r10Phi_of_mem e (R.mul_mem hg hh), r10Phi_of_mem e hg, r10Phi_of_mem e hh,
    ← map_mul]
  rfl

theorem r10Phi_one (e : ↥R ≃* UT3 F4c) : r10Phi R e 1 = 1 := by
  rw [r10Phi_of_mem e R.one_mem]
  exact map_one e

theorem r10Phi_inv (e : ↥R ≃* UT3 F4c) {g : G} (hg : g ∈ R) :
    r10Phi R e g⁻¹ = (r10Phi R e g)⁻¹ := by
  have h := r10Phi_mul e (R.inv_mem hg) hg
  rw [inv_mul_cancel, r10Phi_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem r10Phi_inj (e : ↥R ≃* UT3 F4c) {g h : G} (hg : g ∈ R) (hh : h ∈ R)
    (hgh : r10Phi R e g = r10Phi R e h) : g = h := by
  rw [r10Phi_of_mem e hg, r10Phi_of_mem e hh] at hgh
  exact congrArg Subtype.val (e.injective hgh)

theorem r10Phi_surj (e : ↥R ≃* UT3 F4c) (u : UT3 F4c) : ∃ g ∈ R, r10Phi R e g = u := by
  refine ⟨((e.symm u : ↥R) : G), (e.symm u).2, ?_⟩
  rw [r10Phi_of_mem e (e.symm u).2]
  exact e.apply_symm_apply u

theorem r10Phi_comm (e : ↥R ≃* UT3 F4c) {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    r10Phi R e (x * y * x⁻¹ * y⁻¹) =
      r10Phi R e x * r10Phi R e y * (r10Phi R e x)⁻¹ * (r10Phi R e y)⁻¹ := by
  rw [r10Phi_mul e (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy),
    r10Phi_mul e (R.mul_mem hx hy) (R.inv_mem hx), r10Phi_mul e hx hy,
    r10Phi_inv e hx, r10Phi_inv e hy]

noncomputable def r10Sub (e : ↥R ≃* UT3 F4c) (P : UT3 F4c → Prop)
    (hmul : ∀ u v, P u → P v → P (u * v)) (hone : P 1) (hinv : ∀ u, P u → P u⁻¹) :
    Subgroup G where
  carrier := {g | g ∈ R ∧ P (r10Phi R e g)}
  mul_mem' := fun {g h} hg hh =>
    ⟨R.mul_mem hg.1 hh.1, by rw [r10Phi_mul e hg.1 hh.1]; exact hmul _ _ hg.2 hh.2⟩
  one_mem' := ⟨R.one_mem, by rw [r10Phi_one]; exact hone⟩
  inv_mem' := fun {g} hg => ⟨R.inv_mem hg.1, by rw [r10Phi_inv e hg.1]; exact hinv _ hg.2⟩

theorem card_r10Sub (e : ↥R ≃* UT3 F4c) (P : UT3 F4c → Prop) {hmul hone hinv} :
    Nat.card (r10Sub e P hmul hone hinv) = Nat.card {u : UT3 F4c // P u} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => (⟨r10Phi R e g, g.2.2⟩ : {u : UT3 F4c // P u})) ⟨?_, ?_⟩)
  · intro g h hgh
    exact Subtype.ext (r10Phi_inj e g.2.1 h.2.1 (congrArg Subtype.val hgh))
  · rintro ⟨u, hu⟩
    obtain ⟨g, hgR, hg⟩ := r10Phi_surj e u
    exact ⟨⟨g, hgR, hg ▸ hu⟩, Subtype.ext hg⟩

end Transport

section Build

variable {G : Type} [Group G] {R : Subgroup G}

theorem r10_mul_a (u v : UT3 F4c) : (u * v).a = u.a + v.a := rfl

theorem r10_mul_b (u v : UT3 F4c) : (u * v).b = u.b + v.b := rfl

theorem r10_inv_a (u : UT3 F4c) : u⁻¹.a = -u.a := rfl

theorem r10_inv_b (u : UT3 F4c) : u⁻¹.b = -u.b := rfl

theorem r10_one_a : (1 : UT3 F4c).a = 0 := rfl

theorem r10_one_b : (1 : UT3 F4c).b = 0 := rfl

noncomputable def r10X (e : ↥R ≃* UT3 F4c) : Subgroup G :=
  r10Sub e (fun u => u.a = 0)
    (fun u v hu hv => by rw [r10_mul_a, hu, hv, add_zero]) r10_one_a
    (fun u hu => by rw [r10_inv_a, hu, neg_zero])

noncomputable def r10Y (e : ↥R ≃* UT3 F4c) : Subgroup G :=
  r10Sub e (fun u => u.b = 0)
    (fun u v hu hv => by rw [r10_mul_b, hu, hv, add_zero]) r10_one_b
    (fun u hu => by rw [r10_inv_b, hu, neg_zero])

noncomputable def r10Z (e : ↥R ≃* UT3 F4c) : Subgroup G :=
  r10Sub e (fun u => u.a = 0 ∧ u.b = 0)
    (fun u v hu hv => ⟨by rw [r10_mul_a, hu.1, hv.1, add_zero],
      by rw [r10_mul_b, hu.2, hv.2, add_zero]⟩)
    ⟨r10_one_a, r10_one_b⟩
    (fun u hu => ⟨by rw [r10_inv_a, hu.1, neg_zero], by rw [r10_inv_b, hu.2, neg_zero]⟩)

theorem card_r10X (e : ↥R ≃* UT3 F4c) : Nat.card (r10X e) = 16 := by
  unfold r10X
  rw [card_r10Sub]
  exact r10_card_a

theorem card_r10Y (e : ↥R ≃* UT3 F4c) : Nat.card (r10Y e) = 16 := by
  unfold r10Y
  rw [card_r10Sub]
  exact r10_card_b

theorem card_r10Z (e : ↥R ≃* UT3 F4c) : Nat.card (r10Z e) = 4 := by
  unfold r10Z
  rw [card_r10Sub]
  exact r10_card_ab

theorem r10_Z_coords (e : ↥R ≃* UT3 F4c) {Z : Subgroup G} (hZR : Z ≤ R)
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) {z : G} (hz : z ∈ Z) :
    (r10Phi R e z).a = 0 ∧ (r10Phi R e z).b = 0 := by
  refine r10_center (r10Phi R e z) (fun y => ?_)
  obtain ⟨g, hgR, hg⟩ := r10Phi_surj e y
  rw [← hg, ← r10Phi_mul e (hZR hz) hgR, ← r10Phi_mul e hgR (hZR hz), hZc z hz g hgR]

variable [Finite G]

theorem r10_Z_eq (e : ↥R ≃* UT3 F4c) {Z : Subgroup G} (hZR : Z ≤ R)
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) (hZ4 : Nat.card Z = 4) : Z = r10Z e := by
  refine Subgroup.eq_of_le_of_card_ge (fun z hz => ⟨hZR hz, r10_Z_coords e hZR hZc hz⟩) ?_
  rw [card_r10Z, hZ4]

theorem sl34Data_of_iso (e : ↥R ≃* UT3 F4c) {Z : Subgroup G} (hZR : Z ≤ R)
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) (hZ4 : Nat.card Z = 4) :
    SL34Data R Z (r10X e) (r10Y e) := by
  have hZeq := r10_Z_eq e hZR hZc hZ4
  have hZmem : ∀ g : G, g ∈ Z ↔ g ∈ R ∧ ((r10Phi R e g).a = 0 ∧ (r10Phi R e g).b = 0) := by
    intro g
    rw [hZeq]
    exact Iff.rfl
  have hne : ∀ {a b : G}, a ∈ R → b ∈ R →
      r10Phi R e a * r10Phi R e b = r10Phi R e b * r10Phi R e a → a * b = b * a := by
    intro a b ha hb h
    refine r10Phi_inj e (R.mul_mem ha hb) (R.mul_mem hb ha) ?_
    rw [r10Phi_mul e ha hb, r10Phi_mul e hb ha]
    exact h
  have hne' : ∀ {a b : G}, a ∈ R → b ∈ R → a * b = b * a →
      r10Phi R e a * r10Phi R e b = r10Phi R e b * r10Phi R e a := by
    intro a b ha hb h
    rw [← r10Phi_mul e ha hb, ← r10Phi_mul e hb ha, h]
  have hsq : ∀ {a : G}, a ∈ R → r10Phi R e a * r10Phi R e a = 1 → a * a = 1 := by
    intro a ha h
    refine r10Phi_inj e (R.mul_mem ha ha) R.one_mem ?_
    rw [r10Phi_mul e ha ha, r10Phi_one]
    exact h
  refine
    { X_le := fun g hg => hg.1
      Y_le := fun g hg => hg.1
      Z_le_R := hZR
      Z_central := hZc
      comm_Z := ?_
      Z_le_X := fun z hz => ⟨hZR hz, (r10_Z_coords e hZR hZc hz).1⟩
      Z_le_Y := fun z hz => ⟨hZR hz, (r10_Z_coords e hZR hZc hz).2⟩
      card_Z := hZ4
      card_X := card_r10X e
      card_Y := card_r10Y e
      inf_XY := ?_
      X_comm := fun a ha b hb => hne ha.1 hb.1 (r10_X_comm _ _ ha.2 hb.2)
      Y_comm := fun a ha b hb => hne ha.1 hb.1 (r10_Y_comm _ _ ha.2 hb.2)
      X_sq := fun a ha => hsq ha.1 (r10_X_sq _ ha.2)
      Y_sq := fun a ha => hsq ha.1 (r10_Y_sq _ ha.2)
      invol := ?_
      dec_XY := ?_
      dec_YX := ?_
      surj_X := ?_
      surj_Y := ?_
      cent_X := ?_
      cent_Y := ?_
      cent_pair := ?_ }
  · intro z hz
    have hz' := r10_Z_coords e hZR hZc hz
    have hzu : r10Phi R e z = ⟨0, 0, (r10Phi R e z).c⟩ := UT3.ext hz'.1 hz'.2 rfl
    let c := (r10Phi R e z).c
    let r : ↥R := e.symm ⟨c, 0, 0⟩
    let s : ↥R := e.symm ⟨0, 1, 0⟩
    refine ⟨(r : G), r.2, (s : G), s.2, ?_⟩
    have hz2 : (⟨z, hZR hz⟩ : ↥R) = r * s * r⁻¹ * s⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, r10_comm_gen, ← r10Phi_of_mem e (hZR hz), hzu]
    exact (congrArg Subtype.val hz2).symm
  · ext g
    rw [Subgroup.mem_inf, hZmem]
    constructor
    · rintro ⟨⟨hg, ha⟩, ⟨-, hb⟩⟩
      exact ⟨hg, ha, hb⟩
    · rintro ⟨hg, ha, hb⟩
      exact ⟨⟨hg, ha⟩, ⟨hg, hb⟩⟩
  · intro g hg hg2
    have h1 : r10Phi R e g * r10Phi R e g = 1 := by
      rw [← r10Phi_mul e hg hg, hg2, r10Phi_one]
    rcases r10_invol _ h1 with h | h
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, h⟩
  · intro g hg
    obtain ⟨x, hxR, hx⟩ := r10Phi_surj e (⟨0, (r10Phi R e g).b, (r10Phi R e g).c⟩ : UT3 F4c)
    obtain ⟨y, hyR, hy⟩ := r10Phi_surj e (⟨(r10Phi R e g).a, 0, 0⟩ : UT3 F4c)
    refine ⟨x, ⟨hxR, by rw [hx]⟩, y, ⟨hyR, by rw [hy]⟩, ?_⟩
    refine r10Phi_inj e hg (R.mul_mem hxR hyR) ?_
    rw [r10Phi_mul e hxR hyR, hx, hy]
    exact r10_dec_XY _
  · intro g hg
    obtain ⟨y, hyR, hy⟩ := r10Phi_surj e (⟨(r10Phi R e g).a, 0, 0⟩ : UT3 F4c)
    obtain ⟨x, hxR, hx⟩ := r10Phi_surj e
      (⟨0, (r10Phi R e g).b, (r10Phi R e g).c + (r10Phi R e g).a * (r10Phi R e g).b⟩ : UT3 F4c)
    refine ⟨y, ⟨hyR, by rw [hy]⟩, x, ⟨hxR, by rw [hx]⟩, ?_⟩
    refine r10Phi_inj e hg (R.mul_mem hyR hxR) ?_
    rw [r10Phi_mul e hyR hxR, hx, hy]
    exact r10_dec_YX _
  · intro x hx hxZ z hz
    have hxb : (r10Phi R e x).b ≠ 0 := fun hb => hxZ ((hZmem x).2 ⟨hx.1, hx.2, hb⟩)
    have hz' := (hZmem z).1 hz
    have hzu : r10Phi R e z = ⟨0, 0, (r10Phi R e z).c⟩ := UT3.ext hz'.2.1 hz'.2.2 rfl
    obtain ⟨y', hy'b, hy'⟩ := r10_surj_X_aux _ hx.2 hxb (r10Phi R e z).c
    obtain ⟨y, hyR, hy⟩ := r10Phi_surj e y'
    refine ⟨y, ⟨hyR, by rw [hy]; exact hy'b⟩, ?_⟩
    refine r10Phi_inj e (R.mul_mem (R.mul_mem (R.mul_mem hx.1 hyR) (R.inv_mem hx.1))
      (R.inv_mem hyR)) hz'.1 ?_
    rw [r10Phi_comm e hx.1 hyR, hy, hy', hzu]
  · intro y hy hyZ z hz
    have hya : (r10Phi R e y).a ≠ 0 := fun ha => hyZ ((hZmem y).2 ⟨hy.1, ha, hy.2⟩)
    have hz' := (hZmem z).1 hz
    have hzu : r10Phi R e z = ⟨0, 0, (r10Phi R e z).c⟩ := UT3.ext hz'.2.1 hz'.2.2 rfl
    obtain ⟨x', hx'a, hx'⟩ := r10_surj_Y_aux _ hy.2 hya (r10Phi R e z).c
    obtain ⟨x, hxR, hx⟩ := r10Phi_surj e x'
    refine ⟨x, ⟨hxR, by rw [hx]; exact hx'a⟩, ?_⟩
    refine r10Phi_inj e (R.mul_mem (R.mul_mem (R.mul_mem hy.1 hxR) (R.inv_mem hy.1))
      (R.inv_mem hxR)) hz'.1 ?_
    rw [r10Phi_comm e hy.1 hxR, hx, hx', hzu]
  · intro a ha haZ s hs hsa
    refine ⟨hs, r10_cent_X _ _ ha.2 ?_ (hne' hs ha.1 hsa)⟩
    intro hb
    exact haZ ((hZmem a).2 ⟨ha.1, ha.2, hb⟩)
  · intro a ha haZ s hs hsa
    refine ⟨hs, r10_cent_Y _ _ ha.2 ?_ (hne' hs ha.1 hsa)⟩
    intro hb
    exact haZ ((hZmem a).2 ⟨ha.1, hb, ha.2⟩)
  · intro d₁ hd₁ d₂ hd₂ hd c hc hc1 hc2
    refine (hZmem c).2 ⟨hc, r10_cent_pair (r10Phi R e d₁) (r10Phi R e d₂) (r10Phi R e c) ?_
      (hne' hc hd₁ hc1) (hne' hc hd₂ hc2)⟩
    intro h
    exact hd (hne hd₁ hd₂ h)

end Build

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
