module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Mat

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3Sh

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab Matrix
open scoped MatrixGroups

variable {X : Type} [Group X] {F₁ F₂ : Type} [Field F₁] [Field F₂] (Sh : Shape X F₁ F₂)

theorem mem_sup_or (c : X) : c ∈ Sh.I₁ ⊔ Sh.I₂ ∨ c * Sh.t ∈ Sh.I₁ ⊔ Sh.I₂ := by
  have := Sh.normal₁
  have := Sh.normal₂
  have hc : c ∈ ((Sh.I₁ ⊔ Sh.I₂ ⊔ Subgroup.zpowers Sh.t : Subgroup X) : Set X) := by
    rw [Sh.gen]; exact Subgroup.mem_top c
  rw [Subgroup.normal_mul] at hc
  obtain ⟨h, hh, u, hu, hc'⟩ := hc
  have hc'' : h * u = c := hc'
  rcases mem_zpowers_of_sq Sh.t_sq hu with rfl | rfl
  · left; rwa [← hc'', mul_one]
  · right; rwa [← hc'', mul_assoc, Sh.t_sq, mul_one]

theorem eq_one_or_eq_z_of_commute {a : X} (ha : a ∈ Sh.I₁) (h : ∀ x ∈ Sh.I₁, a * x = x * a) :
    a = 1 ∨ a = Sh.z := by
  have hcen : Sh.e₁ ⟨a, ha⟩ ∈ Subgroup.center SL(2, F₁) := by
    rw [Subgroup.mem_center_iff]
    intro A
    obtain ⟨x, rfl⟩ := Sh.e₁.surjective A
    rw [← map_mul, ← map_mul]
    exact congrArg Sh.e₁ (Subtype.ext (h x x.2).symm)
  rcases eq_one_or_neg_one_of_mem_center hcen with h1 | h1
  · exact Or.inl (congrArg Subtype.val (Sh.e₁.injective (h1.trans (map_one _).symm)))
  · exact Or.inr (congrArg Subtype.val (Sh.e₁.injective (h1.trans Sh.e₁_z.symm)))

theorem mem_I₂_of_commute {c : X} (hc : ∀ a ∈ Sh.I₁, c * a = a * c) : c ∈ Sh.I₂ := by
  rcases mem_sup_or Sh c with h | h
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute Sh.comm h
    have ha' : ∀ x ∈ Sh.I₁, a * x = x * a := fun x hx => by
      have h1 := hc x hx
      have h2 := Sh.comm x hx b hb
      calc a * x = a * b * x * b⁻¹ := by rw [mul_assoc a b x, ← h2]; group
        _ = x * (a * b) * b⁻¹ := by rw [h1]
        _ = x * a := by group
    rcases eq_one_or_eq_z_of_commute Sh ha ha' with rfl | rfl
    · rwa [one_mul]
    · exact mul_mem Sh.z_mem₂ hb
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute Sh.comm h
    have hcC : c ∈ Subgroup.centralizer (Sh.I₁ : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => (hc x hx).symm
    have hbC : b ∈ Subgroup.centralizer (Sh.I₁ : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => Sh.comm x hx b hb
    refine Sh.act₁.t_not_mem_sup (L := Subgroup.centralizer (Sh.I₁ : Set X))
      (fun x _ y hy => Subgroup.mem_centralizer_iff.mp hy x ‹_›) Sh.ns₁ ?_
    have hca : c⁻¹ * a = a * c⁻¹ := by
      have := hc a ha
      calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * a) * c⁻¹ := by rw [this]
        _ = a * c⁻¹ := by group
    have ht : Sh.t = a * (c⁻¹ * b) := by
      calc Sh.t = c⁻¹ * (c * Sh.t) := by group
        _ = c⁻¹ * a * b := by rw [← hab, mul_assoc]
        _ = a * (c⁻¹ * b) := by rw [hca, mul_assoc]
    rw [ht]
    exact mul_mem (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (mul_mem (inv_mem hcC) hbC))

theorem e₂_commute {b : X} (hb : b ∈ Sh.I₂) {Y : SL(2, F₂)} (h : b * (Sh.e₂.symm Y : X) =
    (Sh.e₂.symm Y : X) * b) : Sh.e₂ ⟨b, hb⟩ * Y = Y * Sh.e₂ ⟨b, hb⟩ := by
  rw [← Sh.e₂.apply_symm_apply Y, ← map_mul, ← map_mul]
  exact congrArg Sh.e₂ (Subtype.ext h)

theorem commute_of_conj {b : X} (hb : b ∈ Sh.I₂) {Y : SL(2, F₂)}
    (h : Sh.t * (Sh.e₂.symm Y : X) * Sh.t⁻¹ = b⁻¹ * (Sh.e₂.symm Y : X) * b) :
    ((Matrix.SpecialLinearGroup.toGL (Sh.e₂ ⟨b, hb⟩) * Sh.g₂ : GL (Fin 2) F₂) :
      Matrix (Fin 2) (Fin 2) F₂) * (Y : Matrix (Fin 2) (Fin 2) F₂) =
    (Y : Matrix (Fin 2) (Fin 2) F₂) * ((Matrix.SpecialLinearGroup.toGL (Sh.e₂ ⟨b, hb⟩) *
      Sh.g₂ : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) := by
  obtain ⟨y, hy, hey⟩ := Sh.act₂ (Sh.e₂.symm Y)
  have hy' : y = (⟨b, hb⟩ : Sh.I₂)⁻¹ * Sh.e₂.symm Y * ⟨b, hb⟩ := Subtype.ext (by
    rw [hy, h]; simp)
  rw [hy', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at hey
  set B := Sh.e₂ ⟨b, hb⟩
  set T := Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := F₂)
  have hG : T (B⁻¹ * Y * B) = Sh.g₂ * T Y * Sh.g₂⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hey
  have hP : T B * Sh.g₂ * T Y = T Y * (T B * Sh.g₂) := by
    rw [map_mul, map_mul, map_inv] at hG
    calc T B * Sh.g₂ * T Y = T B * (Sh.g₂ * T Y * Sh.g₂⁻¹) * Sh.g₂ := by group
      _ = T B * ((T B)⁻¹ * T Y * T B) * Sh.g₂ := by rw [← hG]
      _ = T Y * (T B * Sh.g₂) := by group
  have := congrArg (fun u : GL (Fin 2) F₂ => (u : Matrix (Fin 2) (Fin 2) F₂)) hP
  simpa [T, Units.val_mul, Matrix.mul_assoc] using this

theorem not_commute_ij (h3 : (3 : F₂) = 0) (h2 : (2 : F₂) ≠ 0) {a b c : X} (ha : a ∈ Sh.I₁)
    (hb : b ∈ Sh.I₂) (hab : a * b = c * Sh.t)
    (hi : c * (Sh.e₂.symm (SL3.i₀ F₂) : X) = (Sh.e₂.symm (SL3.i₀ F₂) : X) * c)
    (hj : c * (Sh.e₂.symm (SL3.j₀ h3) : X) = (Sh.e₂.symm (SL3.j₀ h3) : X) * c) : False := by
  have ht' : Sh.t⁻¹ = Sh.t := inv_eq_of_mul_eq_one_right Sh.t_sq
  have hc : c = a * b * Sh.t⁻¹ := by rw [hab]; group
  have key : ∀ Y : SL(2, F₂), c * (Sh.e₂.symm Y : X) = (Sh.e₂.symm Y : X) * c →
      Sh.t * (Sh.e₂.symm Y : X) * Sh.t⁻¹ = b⁻¹ * (Sh.e₂.symm Y : X) * b := fun Y hY => by
    set q : X := (Sh.e₂.symm Y : X)
    have haq : a * q = q * a := Sh.comm a ha q (Sh.e₂.symm Y).2
    have hcq : c * q * c⁻¹ = q := by rw [hY]; group
    calc Sh.t * q * Sh.t⁻¹ = Sh.t⁻¹ * q * Sh.t := by rw [ht']
      _ = (a * b)⁻¹ * (c * q * c⁻¹) * (a * b) := by rw [hc]; group
      _ = b⁻¹ * (a⁻¹ * (q * a)) * b := by rw [hcq]; group
      _ = b⁻¹ * q * b := by rw [← haq, inv_mul_cancel_left]
  apply Sh.ns₂
  obtain ⟨r, hr⟩ := SL3.isSquare_det_of_commute h2 _ (commute_of_conj Sh hb (key _ hi))
    (commute_of_conj Sh hb (key _ hj))
  refine ⟨r, ?_⟩
  rw [map_mul, Units.val_mul, det_toGL, one_mul] at hr
  exact hr

theorem mem_I₁_of_commute_ij (h3 : (3 : F₂) = 0) (h2 : (2 : F₂) ≠ 0) {c : X}
    (hi : c * (Sh.e₂.symm (SL3.i₀ F₂) : X) = (Sh.e₂.symm (SL3.i₀ F₂) : X) * c)
    (hj : c * (Sh.e₂.symm (SL3.j₀ h3) : X) = (Sh.e₂.symm (SL3.j₀ h3) : X) * c) : c ∈ Sh.I₁ := by
  rcases mem_sup_or Sh c with h | h
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute Sh.comm h
    have hb' : ∀ q ∈ Sh.I₂, a * b * q = q * (a * b) → b * q = q * b := fun q hq hq' => by
      calc b * q = a⁻¹ * (a * b * q) := by group
        _ = a⁻¹ * (q * (a * b)) := by rw [hq']
        _ = q * b := by rw [← mul_assoc, Sh.comm _ (inv_mem ha) q hq]; group
    rcases SL3.eq_one_or_eq_neg_one_of_commute h2 h3
      (e₂_commute Sh hb (hb' _ (Sh.e₂.symm _).2 hi))
      (e₂_commute Sh hb (hb' _ (Sh.e₂.symm _).2 hj)) with h1 | h1
    · have : b = 1 := congrArg Subtype.val (Sh.e₂.injective (h1.trans (map_one _).symm))
      rwa [this, mul_one]
    · have : b = Sh.z := congrArg Subtype.val (Sh.e₂.injective (h1.trans Sh.e₂_z.symm))
      rw [this]
      exact mul_mem ha Sh.z_mem₁
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute Sh.comm h
    exact not_commute_ij Sh h3 h2 ha hb hab hi hj

end CFSG.ClassicalInvolution.Q3.TA3.Q3Sh
