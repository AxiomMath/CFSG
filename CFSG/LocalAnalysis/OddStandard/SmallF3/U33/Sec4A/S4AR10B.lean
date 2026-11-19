module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

section Symm

variable {G : Type} [Group G] {R Z X Y : Subgroup G}

theorem SL34Data.symm (h : SL34Data R Z X Y) : SL34Data R Z Y X where
  X_le := h.Y_le
  Y_le := h.X_le
  Z_le_R := h.Z_le_R
  Z_central := h.Z_central
  comm_Z := h.comm_Z
  Z_le_X := h.Z_le_Y
  Z_le_Y := h.Z_le_X
  card_Z := h.card_Z
  card_X := h.card_Y
  card_Y := h.card_X
  inf_XY := by rw [inf_comm]; exact h.inf_XY
  X_comm := h.Y_comm
  Y_comm := h.X_comm
  X_sq := h.Y_sq
  Y_sq := h.X_sq
  invol := fun g hg hg2 => (h.invol g hg hg2).symm
  dec_XY := h.dec_YX
  dec_YX := h.dec_XY
  surj_X := h.surj_Y
  surj_Y := h.surj_X
  cent_X := h.cent_Y
  cent_Y := h.cent_X
  cent_pair := h.cent_pair

theorem SL34Data.le_or_le (h : SL34Data R Z X Y) {E : Subgroup G} (hER : E ≤ R)
    (hE2 : ∀ e ∈ E, e * e = 1) : E ≤ X ∨ E ≤ Y := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hEX, hEY⟩ := hcon
  obtain ⟨e₁, he₁E, he₁X⟩ := Set.not_subset.mp hEX
  obtain ⟨e₂, he₂E, he₂Y⟩ := Set.not_subset.mp hEY
  have he₁Y : e₁ ∈ Y := (h.invol e₁ (hER he₁E) (hE2 e₁ he₁E)).resolve_left he₁X
  have he₂X : e₂ ∈ X := (h.invol e₂ (hER he₂E) (hE2 e₂ he₂E)).resolve_right he₂Y
  have hm : e₁ * e₂ ∈ E := E.mul_mem he₁E he₂E
  rcases h.invol (e₁ * e₂) (hER hm) (hE2 _ hm) with hX | hY
  · apply he₁X
    have := X.mul_mem hX (X.inv_mem he₂X)
    rwa [mul_inv_cancel_right] at this
  · apply he₂Y
    have := Y.mul_mem (Y.inv_mem he₁Y) hY
    rwa [inv_mul_cancel_left] at this

theorem SL34Data.eq_of_E16 [Finite G] (h : SL34Data R Z X Y) {E : Subgroup G} (hER : E ≤ R)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE16 : Nat.card E = 16) : E = X ∨ E = Y := by
  rcases h.le_or_le hER hE2 with hX | hY
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hX (by rw [h.card_X, hE16]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hY (by rw [h.card_Y, hE16]))

theorem SL34Data.X_ne_Y [Finite G] (h : SL34Data R Z X Y) : X ≠ Y := by
  intro hXY
  have h1 := h.inf_XY
  rw [← hXY, inf_idem] at h1
  have h2 := h.card_X
  rw [h1, h.card_Z] at h2
  omega

theorem r10_conj3 {ρ : G} (hρ3 : ρ * ρ * ρ = 1) (g : G) :
    ρ * (ρ * (ρ * g * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = g := by
  calc ρ * (ρ * (ρ * g * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = (ρ * ρ * ρ) * g * (ρ * ρ * ρ)⁻¹ := by group
    _ = g := by rw [hρ3]; group

theorem r10_conj_eq [Finite G] (h : SL34Data R Z X Y) {ρ : G}
    (hρR : ∀ r ∈ R, ρ * r * ρ⁻¹ ∈ R) {E : Subgroup G} (hER : E ≤ R)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE16 : Nat.card E = 16) :
    E.map (MulAut.conj ρ).toMonoidHom = X ∨ E.map (MulAut.conj ρ).toMonoidHom = Y := by
  refine h.eq_of_E16 ?_ ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply] using hρR e (hER he)
  · rintro _ ⟨e, he, rfl⟩
    have := hE2 e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc ρ * e * ρ⁻¹ * (ρ * e * ρ⁻¹) = ρ * (e * e) * ρ⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj ρ).injective, hE16]

theorem r10_rho_inv [Finite G] (h : SL34Data R Z X Y) {ρ : G} (hρ3 : ρ * ρ * ρ = 1)
    (hρR : ∀ r ∈ R, ρ * r * ρ⁻¹ ∈ R) :
    (∀ x ∈ X, ρ * x * ρ⁻¹ ∈ X) ∧ (∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y) := by
  have hmem : ∀ (E : Subgroup G) {g : G}, g ∈ E →
      ρ * g * ρ⁻¹ ∈ E.map (MulAut.conj ρ).toMonoidHom := fun E g hg => ⟨g, hg, rfl⟩
  have hXne := h.X_ne_Y
  have hcX := r10_conj_eq h hρR h.X_le h.X_sq h.card_X
  have hcY := r10_conj_eq h hρR h.Y_le h.Y_sq h.card_Y
  have hinj : X.map (MulAut.conj ρ).toMonoidHom ≠ Y.map (MulAut.conj ρ).toMonoidHom :=
    fun hh => hXne (Subgroup.map_injective (MulAut.conj ρ).injective hh)
  rcases hcX with hXX | hXY <;> rcases hcY with hYX | hYY
  · exact absurd (hXX.trans hYX.symm) hinj
  · refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have := hmem X hx
      rwa [hXX] at this
    · have := hmem Y hy
      rwa [hYY] at this
  · exfalso
    have hXY' : X ≤ Y := by
      intro x hx
      have h1 := hmem X hx
      rw [hXY] at h1
      have h2 := hmem Y h1
      rw [hYX] at h2
      have h3 := hmem X h2
      rw [hXY] at h3
      rwa [r10_conj3 hρ3 x] at h3
    exact hXne (Subgroup.eq_of_le_of_card_ge hXY' (by rw [h.card_X, h.card_Y]))
  · exact absurd (hXY.trans hYY.symm) hinj

theorem r10_transitive [Finite G] (h : SL34Data R Z X Y) {ρ : G} (hρ3 : ρ * ρ * ρ = 1)
    (hρY : ∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y) (hρZ : ∀ z ∈ Z, ρ * z * ρ⁻¹ ∈ Z)
    (hfix : ∀ r ∈ R, ρ * r = r * ρ → r = 1) {y₁ : G} (hy₁ : y₁ ∈ Y) (hy₁Z : y₁ ∉ Z) {y : G}
    (hy : y ∈ Y) :
    ∃ z ∈ Z, y = z ∨ y = y₁ * z ∨ y = ρ * y₁ * ρ⁻¹ * z ∨
      y = ρ * (ρ * y₁ * ρ⁻¹) * ρ⁻¹ * z := by
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, y₂ = ρ * y₁ * ρ⁻¹ := ⟨_, rfl⟩
  obtain ⟨y₃, hy₃⟩ : ∃ y₃, y₃ = ρ * y₂ * ρ⁻¹ := ⟨_, rfl⟩
  rw [← hy₂, ← hy₃]
  have hYinv : ∀ a ∈ Y, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (h.Y_sq a ha)
  have hy₂Y : y₂ ∈ Y := by rw [hy₂]; exact hρY _ hy₁
  have hy₃Y : y₃ ∈ Y := by rw [hy₃]; exact hρY _ hy₂Y
  have hc3 : ρ * y₃ * ρ⁻¹ = y₁ := by
    rw [hy₃, hy₂]
    exact r10_conj3 hρ3 y₁
  have hy₃Z : y₃ ∉ Z := fun hz => hy₁Z (by have := hρZ _ hz; rwa [hc3] at this)
  have hy₂Z : y₂ ∉ Z := fun hz => hy₃Z (by rw [hy₃]; exact hρZ _ hz)
  have hN : y₁ * y₂ * y₃ = 1 := by
    have hconj : ρ * (y₁ * y₂ * y₃) * ρ⁻¹ = y₁ * y₂ * y₃ := by
      calc ρ * (y₁ * y₂ * y₃) * ρ⁻¹
          = (ρ * y₁ * ρ⁻¹) * (ρ * y₂ * ρ⁻¹) * (ρ * y₃ * ρ⁻¹) := by group
        _ = y₂ * y₃ * y₁ := by rw [← hy₂, ← hy₃, hc3]
        _ = y₁ * y₂ * y₃ := by
            have := h.Y_comm y₁ hy₁ (y₂ * y₃) (Y.mul_mem hy₂Y hy₃Y)
            calc y₂ * y₃ * y₁ = y₁ * (y₂ * y₃) := this.symm
              _ = y₁ * y₂ * y₃ := (mul_assoc _ _ _).symm
    exact hfix _ (h.Y_le (Y.mul_mem (Y.mul_mem hy₁ hy₂Y) hy₃Y))
      (mul_inv_eq_iff_eq_mul.mp hconj)
  have e12 : y₁ * y₂ = y₃ := by
    have : y₁ * y₂ = y₃⁻¹ := mul_eq_one_iff_eq_inv.mp hN
    rw [this, hYinv y₃ hy₃Y]
  have e13 : y₁ * y₃ = y₂ := by
    rw [← e12, ← mul_assoc, h.Y_sq y₁ hy₁, one_mul]
  have e21 : y₂ * y₁ = y₃ := by rw [h.Y_comm y₂ hy₂Y y₁ hy₁, e12]
  have e31 : y₃ * y₁ = y₂ := by rw [h.Y_comm y₃ hy₃Y y₁ hy₁, e13]
  have e23 : y₂ * y₃ = y₁ := by
    calc y₂ * y₃ = y₂ * (y₁ * y₂) := by rw [e12]
      _ = (y₂ * y₁) * y₂ := (mul_assoc _ _ _).symm
      _ = (y₁ * y₂) * y₂ := by rw [h.Y_comm y₂ hy₂Y y₁ hy₁]
      _ = y₁ * (y₂ * y₂) := mul_assoc _ _ _
      _ = y₁ := by rw [h.Y_sq y₂ hy₂Y, mul_one]
  have e32 : y₃ * y₂ = y₁ := by rw [h.Y_comm y₃ hy₃Y y₂ hy₂Y, e23]
  obtain ⟨u, hu⟩ : ∃ u : Fin 4 → G, u = ![1, y₁, y₂, y₃] := ⟨_, rfl⟩
  have huY : ∀ i, u i ∈ Y := by
    intro i
    fin_cases i <;> simp [hu] <;> assumption
  have huY2 : ∀ i, u i * u i = 1 := fun i => h.Y_sq _ (huY i)
  have key : ∀ i j : Fin 4, u j * u i ∈ Z → i = j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [hu, e12, e13, e23, e21, e31, e32,
      hy₁Z, hy₂Z, hy₃Z] at hij)
  let Φ : Fin 4 × ↥Z → ↥Y := fun p => ⟨u p.1 * (p.2 : G), Y.mul_mem (huY p.1) (h.Z_le_Y p.2.2)⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨i, z⟩ ⟨j, z'⟩ hΦ
    have h1 : u i * (z : G) = u j * (z' : G) := congrArg Subtype.val hΦ
    have h2 : u j * u i = (z' : G) * (z : G)⁻¹ := by
      apply eq_mul_inv_of_mul_eq
      calc u j * u i * (z : G) = u j * (u i * (z : G)) := mul_assoc _ _ _
        _ = u j * (u j * (z' : G)) := by rw [h1]
        _ = (z' : G) := by rw [← mul_assoc, huY2, one_mul]
    have hij : u j * u i ∈ Z := by
      rw [h2]
      exact Z.mul_mem z'.2 (Z.inv_mem z.2)
    have hij' : i = j := key i j hij
    subst hij'
    have : (z : G) = z' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have hcard : Nat.card ↥Y ≤ Nat.card (Fin 4 × ↥Z) := by
    rw [Nat.card_prod, h.card_Y, h.card_Z]
    simp
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨⟨i, z⟩, hiz⟩ := hbij.2 ⟨y, hy⟩
  have hy' : y = u i * (z : G) := (congrArg Subtype.val hiz).symm
  refine ⟨z, z.2, ?_⟩
  fin_cases i <;> simp [hu] at hy'
  · exact Or.inl hy'
  · exact Or.inr (Or.inl hy')
  · exact Or.inr (Or.inr (Or.inl hy'))
  · exact Or.inr (Or.inr (Or.inr hy'))

end Symm

section K

variable {G : Type} [Group G] {R Z X Y : Subgroup G} {t ρ : G}

structure R10Hyp (R Z X Y : Subgroup G) (t ρ : G) : Prop where
  sl : SL34Data R Z X Y
  comm_le : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ Z
  t_orbit : ∀ r ∈ R, ∃ z ∈ Z, r * t * r⁻¹ = t * z
  t_cent_X : ∀ a ∈ X, a * t = t * a → a ∈ Z
  t_cent_Y : ∀ a ∈ Y, a * t = t * a → a ∈ Z
  rho_cube : ρ * ρ * ρ = 1
  rho_R : ∀ r ∈ R, ρ * r * ρ⁻¹ ∈ R
  rho_Z : ∀ z ∈ Z, ρ * z * ρ⁻¹ ∈ Z
  rho_X : ∀ x ∈ X, ρ * x * ρ⁻¹ ∈ X
  rho_Y : ∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y
  rho_fix : ∀ r ∈ R, ρ * r = r * ρ → r = 1
  rho_t : ρ * t = t * ρ

theorem R10Hyp.symm (H : R10Hyp R Z X Y t ρ) : R10Hyp R Z Y X t ρ where
  sl := H.sl.symm
  comm_le := H.comm_le
  t_orbit := H.t_orbit
  t_cent_X := H.t_cent_Y
  t_cent_Y := H.t_cent_X
  rho_cube := H.rho_cube
  rho_R := H.rho_R
  rho_Z := H.rho_Z
  rho_X := H.rho_Y
  rho_Y := H.rho_X
  rho_fix := H.rho_fix
  rho_t := H.rho_t

@[expose] def r10Z1 (t x : G) : G := t⁻¹ * (x * t * x⁻¹)

@[expose] def r10Th (x g : G) : G := x * g * x⁻¹ * g⁻¹

@[expose] def r10Kz (t x g : G) : G := r10Z1 t x * r10Th x g

theorem r10Z1_mem (H : R10Hyp R Z X Y t ρ) {x : G} (hx : x ∈ R) : r10Z1 t x ∈ Z := by
  obtain ⟨z, hz, hxz⟩ := H.t_orbit x hx
  have : r10Z1 t x = z := by
    unfold r10Z1
    rw [hxz, inv_mul_cancel_left]
  rw [this]
  exact hz

theorem r10Th_mem (H : R10Hyp R Z X Y t ρ) {x g : G} (hx : x ∈ R) (hg : g ∈ R) :
    r10Th x g ∈ Z := H.comm_le x hx g hg

theorem r10_comm_tg (H : R10Hyp R Z X Y t ρ) {x g : G} (hx : x ∈ R) (hg : g ∈ R) :
    x * (t * g) = (t * g) * x ↔ r10Kz t x g = 1 := by
  have h1 : r10Z1 t x ∈ Z := r10Z1_mem H hx
  have h2 : r10Th x g ∈ Z := r10Th_mem H hx hg
  have hc : r10Z1 t x * r10Th x g * g = g * (r10Z1 t x * r10Th x g) :=
    H.sl.Z_central _ (Z.mul_mem h1 h2) g hg
  have key : x * (t * g) * x⁻¹ = t * g * (r10Z1 t x * r10Th x g) := by
    have e1 : x * t * x⁻¹ = t * r10Z1 t x := by
      unfold r10Z1
      rw [mul_inv_cancel_left]
    have e2 : x * g * x⁻¹ = r10Th x g * g := by
      unfold r10Th
      group
    calc x * (t * g) * x⁻¹ = (x * t * x⁻¹) * (x * g * x⁻¹) := by group
      _ = t * r10Z1 t x * (r10Th x g * g) := by rw [e1, e2]
      _ = t * (r10Z1 t x * r10Th x g * g) := by group
      _ = t * (g * (r10Z1 t x * r10Th x g)) := by rw [hc]
      _ = t * g * (r10Z1 t x * r10Th x g) := by group
  unfold r10Kz
  constructor
  · intro hcomm
    have h3 : t * g * (r10Z1 t x * r10Th x g) = t * g := by
      rw [← key, hcomm]
      group
    exact mul_left_cancel (a := t * g) (by rw [h3, mul_one])
  · intro h3
    have : x * (t * g) * x⁻¹ = t * g := by rw [key, h3, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp this

theorem r10Th_mul (H : R10Hyp R Z X Y t ρ) {x g h : G} (hx : x ∈ R) (hg : g ∈ R) (hh : h ∈ R) :
    r10Th x (g * h) = r10Th x g * r10Th x h := by
  have hθ : r10Th x h ∈ Z := r10Th_mem H hx hh
  have hc : g * r10Th x h * g⁻¹ = r10Th x h := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (H.sl.Z_central _ hθ g hg).symm
  calc r10Th x (g * h) = r10Th x g * (g * r10Th x h * g⁻¹) := by unfold r10Th; group
    _ = r10Th x g * r10Th x h := by rw [hc]

theorem r10Th_one {x g : G} (h : x * g = g * x) : r10Th x g = 1 := by
  unfold r10Th
  have : x * g * x⁻¹ = g := mul_inv_eq_iff_eq_mul.mpr h
  rw [this, mul_inv_cancel]

theorem r10Kz_mul (H : R10Hyp R Z X Y t ρ) {x g h : G} (hx : x ∈ R) (hg : g ∈ R) (hh : h ∈ R) :
    r10Kz t x (g * h) = r10Kz t x g * r10Th x h := by
  unfold r10Kz
  rw [r10Th_mul H hx hg hh, mul_assoc]

theorem r10_rel_ext (H : R10Hyp R Z X Y t ρ) {x : G} (hx : x ∈ X) {y₀ : G} (hy₀ : y₀ ∈ Y)
    (hrel : x * (t * y₀) = (t * y₀) * x) {z : G} (hz : z ∈ Z) {x' : G} (hx' : x' ∈ X) :
    x * (t * (x' * (y₀ * z))) = (t * (x' * (y₀ * z))) * x := by
  have hxR := H.sl.X_le hx
  have hy₀R := H.sl.Y_le hy₀
  have hzR := H.sl.Z_le_R hz
  have hx'R := H.sl.X_le hx'
  have hk0 : r10Kz t x y₀ = 1 := (r10_comm_tg H hxR hy₀R).mp hrel
  have h1 : r10Th x z = 1 := r10Th_one (H.sl.Z_central z hz x hxR).symm
  have h2 : r10Th x x' = 1 := r10Th_one (H.sl.X_comm x hx x' hx')
  have e : r10Kz t x (x' * (y₀ * z)) = r10Kz t x y₀ := by
    rw [r10Kz_mul H hxR hx'R (R.mul_mem hy₀R hzR), r10Th_mul H hxR hy₀R hzR]
    unfold r10Kz
    rw [h1, h2]
    simp
  rw [r10_comm_tg H hxR (R.mul_mem hx'R (R.mul_mem hy₀R hzR)), e, hk0]

theorem r10_rel_conj (H : R10Hyp R Z X Y t ρ) {x g : G} (h : x * (t * g) = (t * g) * x) :
    (ρ * x * ρ⁻¹) * (t * (ρ * g * ρ⁻¹)) = (t * (ρ * g * ρ⁻¹)) * (ρ * x * ρ⁻¹) := by
  have ht : ρ⁻¹ * t * ρ = t := by
    calc ρ⁻¹ * t * ρ = ρ⁻¹ * (t * ρ) := mul_assoc _ _ _
      _ = ρ⁻¹ * (ρ * t) := by rw [H.rho_t]
      _ = t := inv_mul_cancel_left _ _
  have htt : ρ * t * ρ⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr H.rho_t
  calc (ρ * x * ρ⁻¹) * (t * (ρ * g * ρ⁻¹)) = ρ * (x * (ρ⁻¹ * t * ρ) * g) * ρ⁻¹ := by group
    _ = ρ * (x * (t * g)) * ρ⁻¹ := by rw [ht]; group
    _ = ρ * ((t * g) * x) * ρ⁻¹ := by rw [h]
    _ = (ρ * t * ρ⁻¹) * (ρ * g * ρ⁻¹) * (ρ * x * ρ⁻¹) := by group
    _ = (t * (ρ * g * ρ⁻¹)) * (ρ * x * ρ⁻¹) := by rw [htt]

theorem r10_conj_not_mem (H : R10Hyp R Z X Y t ρ) {g : G} (hg : g ∉ Z) : ρ * g * ρ⁻¹ ∉ Z := by
  intro h1
  apply hg
  have h2 := H.rho_Z _ h1
  have h3 := H.rho_Z _ h2
  rwa [r10_conj3 H.rho_cube] at h3

variable [Finite G]

theorem r10_K (H : R10Hyp R Z X Y t ρ) {y : G} (hy : y ∈ Y) (hyZ : y ∉ Z) {x' : G}
    (hx' : x' ∈ X) : ∃ x ∈ X, x ∉ Z ∧ x * (t * (x' * y)) = (t * (x' * y)) * x := by
  obtain ⟨x₁, hx₁X, hx₁Z⟩ : ∃ x₁ ∈ X, x₁ ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hle : X ≤ Z := fun a ha => hcon a ha
    have := Subgroup.card_le_of_le hle
    rw [H.sl.card_X, H.sl.card_Z] at this
    omega
  have hx₁R := H.sl.X_le hx₁X
  have hz₁ : r10Z1 t x₁ ∈ Z := r10Z1_mem H hx₁R
  obtain ⟨y₁, hy₁Y, hy₁⟩ := H.sl.surj_X x₁ hx₁X hx₁Z (r10Z1 t x₁)⁻¹ (Z.inv_mem hz₁)
  have hy₁R := H.sl.Y_le hy₁Y
  have hk1 : r10Kz t x₁ y₁ = 1 := by
    unfold r10Kz r10Th
    rw [hy₁]
    exact mul_inv_cancel _
  have hrel₁ : x₁ * (t * y₁) = (t * y₁) * x₁ := (r10_comm_tg H hx₁R hy₁R).mpr hk1
  have hy₁Z : y₁ ∉ Z := by
    intro hyz
    have h1 : r10Th x₁ y₁ = 1 := r10Th_one (H.sl.Z_central y₁ hyz x₁ hx₁R).symm
    have h2 : r10Z1 t x₁ = 1 := by
      have : r10Kz t x₁ y₁ = r10Z1 t x₁ := by
        unfold r10Kz
        rw [h1, mul_one]
      rw [← this]
      exact hk1
    apply hx₁Z
    refine H.t_cent_X x₁ hx₁X ?_
    have h3 : x₁ * t * x₁⁻¹ = t := by
      have h4 : t⁻¹ * (x₁ * t * x₁⁻¹) = 1 := h2
      exact (inv_mul_eq_one.mp h4).symm
    exact mul_inv_eq_iff_eq_mul.mp h3
  obtain ⟨z, hzZ, hyz⟩ := r10_transitive H.sl H.rho_cube H.rho_Y H.rho_Z H.rho_fix hy₁Y hy₁Z hy
  rcases hyz with hyz | hyz | hyz | hyz
  · exact absurd (by rw [hyz]; exact hzZ) hyZ
  · refine ⟨x₁, hx₁X, hx₁Z, ?_⟩
    rw [hyz]
    exact r10_rel_ext H hx₁X hy₁Y hrel₁ hzZ hx'
  · refine ⟨ρ * x₁ * ρ⁻¹, H.rho_X _ hx₁X, r10_conj_not_mem H hx₁Z, ?_⟩
    rw [hyz]
    exact r10_rel_ext H (H.rho_X _ hx₁X) (H.rho_Y _ hy₁Y) (r10_rel_conj H hrel₁) hzZ hx'
  · refine ⟨ρ * (ρ * x₁ * ρ⁻¹) * ρ⁻¹, H.rho_X _ (H.rho_X _ hx₁X),
      r10_conj_not_mem H (r10_conj_not_mem H hx₁Z), ?_⟩
    rw [hyz]
    exact r10_rel_ext H (H.rho_X _ (H.rho_X _ hx₁X)) (H.rho_Y _ (H.rho_Y _ hy₁Y))
      (r10_rel_conj H (r10_rel_conj H hrel₁)) hzZ hx'

end K

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
