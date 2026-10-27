module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open scoped commutatorElement

namespace Sp4Core

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_add_ne_zero (h4 : 4 ≤ Nat.card F) (y : F) :
    ∃ u v : F, u ≠ 0 ∧ v ≠ 0 ∧ u + v = y := by
  classical
  have := Fintype.ofFinite F
  have hex : ∃ v : F, v ≠ 0 ∧ v ≠ y := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, y} := fun x _ => by
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp [hcon x hx0]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    have h2 : ({0, y} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v, hv0, hvy⟩ := hex
  refine ⟨y + v, v, ?_, hv0, ?_⟩
  · intro h
    apply hvy
    have h1 : y = -v := eq_neg_of_add_eq_zero_left h
    rw [CharTwo.neg_eq] at h1
    exact h1.symm
  · have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination v * h2

theorem exists_sq_add_sq (h4 : 4 ≤ Nat.card F) (w : F) :
    ∃ u v : F, u ≠ 0 ∧ v ≠ 0 ∧ u ^ 2 + v ^ 2 = w := by
  obtain ⟨z, hz⟩ := FiniteField.isSquare_of_char_two (F := F) (ringChar.eq F 2) w
  obtain ⟨u, v, hu, hv, huv⟩ := exists_add_ne_zero h4 z
  refine ⟨u, v, hu, hv, ?_⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [hz, ← huv]
  linear_combination (-(u * v)) * h2

theorem exists_sq (w : F) : ∃ z : F, z ^ 2 = w := by
  obtain ⟨z, hz⟩ := FiniteField.isSquare_of_char_two (F := F) (ringChar.eq F 2) w
  exact ⟨z, by rw [hz, sq]⟩

omit [Finite F] in
theorem tauS_mul_tauS_inv (b c d b' c' d' : F) :
    tauS b c d * (tauS b' c' d')⁻¹ = tauS (b + b') (c + c') (d + d') := by
  rw [tauS_inv, tauS_mul_tauS, CharTwo.neg_eq, CharTwo.neg_eq, CharTwo.neg_eq]

omit [Finite F] [CharP F 2] in
theorem lam_mul_lam (a a' : F) : lam a * lam a' = lam (a + a') := lam_mul a a'

omit [Finite F] in
theorem D0_mul (b c a b' c' a' : F) :
    tauS b c 0 * lam a * (tauS b' c' 0 * lam a') = tauS (b + b') (c + c') 0 * lam (a + a') := by
  calc tauS b c 0 * lam a * (tauS b' c' 0 * lam a')
      = tauS b c 0 * (lam a * tauS b' c' 0) * lam a' := by group
    _ = tauS b c 0 * (tauS b' c' 0 * lam a) * lam a' := by rw [lam_mul_tauS_zero]
    _ = (tauS b c 0 * tauS b' c' 0) * (lam a * lam a') := by group
    _ = tauS (b + b') (c + c') 0 * lam (a + a') := by
      rw [tauS_mul_tauS, lam_mul_lam, add_zero]

omit [Finite F] in
theorem isElemAbelian_of_D0 {R₀ : Subgroup (StatedSp 2 F)}
    (h0 : ∀ r ∈ R₀, ∃ b c a : F, r = tauS b c 0 * lam a) : IsElemAbelian 2 R₀ := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨b, c, a, hx'⟩ := h0 x x.2
    obtain ⟨b', c', a', hy'⟩ := h0 y y.2
    apply Subtype.ext
    show (x : StatedSp 2 F) * y = y * x
    rw [hx', hy', D0_mul, D0_mul, add_comm b, add_comm c, add_comm a]
  · obtain ⟨b, c, a, hx'⟩ := h0 x hx
    rw [hx', sq, D0_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, tauS_zero, lam_zero, mul_one]

omit [Finite F] in
theorem isElemAbelian_of_Sym {R₀ : Subgroup (StatedSp 2 F)}
    (h0 : ∀ r ∈ R₀, ∃ b c d : F, r = tauS b c d) : IsElemAbelian 2 R₀ := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨b, c, d, hx'⟩ := h0 x x.2
    obtain ⟨b', c', d', hy'⟩ := h0 y y.2
    apply Subtype.ext
    show (x : StatedSp 2 F) * y = y * x
    rw [hx', hy', tauS_mul_tauS, tauS_mul_tauS, add_comm b, add_comm c, add_comm d]
  · obtain ⟨b, c, d, hx'⟩ := h0 x hx
    rw [hx', sq, tauS_mul_tauS, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, tauS_zero]

omit [Finite F] [CharP F 2] in
theorem torus_conj_tauS (s : Fin 2 → Fˣ) (b c d : F) :
    SymplecticTorusWeyl.torusHom s * tauS b c d * (SymplecticTorusWeyl.torusHom s)⁻¹ =
      tauS ((s 0 : F) ^ 2 * b) ((s 0 : F) * (s 1 : F) * c) ((s 1 : F) ^ 2 * d) := by
  rw [mul_inv_eq_iff_eq_mul, torusHom_mul_tauS]

omit [Finite F] [CharP F 2] in
theorem torus_conj_lam (s : Fin 2 → Fˣ) (a : F) :
    SymplecticTorusWeyl.torusHom s * lam a * (SymplecticTorusWeyl.torusHom s)⁻¹ =
      lam ((s 0 : F) * (s 1 : F)⁻¹ * a) := by
  rw [mul_inv_eq_iff_eq_mul, torusHom_mul_lam]

omit [Finite F] [CharP F 2] in
theorem exists_coords {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) :
    ∃ b c d a : F, g = tauS b c d * lam a := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.mp hg
  exact ⟨C 0 0, C 0 1, C 1 1, a, by rw [tau_eq_tauS hC]⟩

omit [Finite F] [CharP F 2] in
theorem torusHom_mem_normalizer (s : Fin 2 → Fˣ) :
    SymplecticTorusWeyl.torusHom s ∈
      Subgroup.normalizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) := by
  have key : ∀ (s : Fin 2 → Fˣ) (g : StatedSp 2 F), g ∈ unipotent 2 F →
      SymplecticTorusWeyl.torusHom s * g * (SymplecticTorusWeyl.torusHom s)⁻¹ ∈ unipotent 2 F := by
    intro s g hg
    obtain ⟨b, c, d, a, rfl⟩ := exists_coords hg
    have : SymplecticTorusWeyl.torusHom s * (tauS b c d * lam a) *
        (SymplecticTorusWeyl.torusHom s)⁻¹ =
        (SymplecticTorusWeyl.torusHom s * tauS b c d * (SymplecticTorusWeyl.torusHom s)⁻¹) *
        (SymplecticTorusWeyl.torusHom s * lam a * (SymplecticTorusWeyl.torusHom s)⁻¹) := by group
    rw [this, torus_conj_tauS, torus_conj_lam]
    exact mul_mem (tauS_mem_unipotent _ _ _) (lam_mem_unipotent _)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key s g, fun hg => ?_⟩
  have := key s⁻¹ _ hg
  simpa [map_inv, mul_assoc] using this

theorem eq_unipotent_of_normalized (h4 : 4 ≤ Nat.card F) {R₀ : Subgroup (StatedSp 2 F)}
    (hRU : R₀ ≤ unipotent 2 F)
    (hN : ∀ n ∈ Subgroup.normalizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F)), ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀)
    (hnot : ¬ IsElemAbelian 2 R₀) : R₀ = unipotent 2 F := by
  have hT : ∀ (s : Fin 2 → Fˣ) (r : StatedSp 2 F), r ∈ R₀ →
      SymplecticTorusWeyl.torusHom s * r * (SymplecticTorusWeyl.torusHom s)⁻¹ ∈ R₀ :=
    fun s r hr => hN _ (torusHom_mem_normalizer s) r hr
  have hUc : ∀ g ∈ unipotent 2 F, ∀ r ∈ R₀, g * r * g⁻¹ ∈ R₀ :=
    fun g hg r hr => hN g (Subgroup.le_normalizer hg) r hr
  obtain ⟨b₀, c₀, d₀, a₀, hd₀, hr₀⟩ : ∃ b c d a : F, d ≠ 0 ∧ tauS b c d * lam a ∈ R₀ := by
    by_contra hcon
    push Not at hcon
    refine hnot (isElemAbelian_of_D0 fun r hr => ?_)
    obtain ⟨b, c, d, a, hrabcd⟩ := exists_coords (hRU hr)
    have hd : d = 0 := by
      by_contra hd
      exact hcon b c d a hd (hrabcd ▸ hr)
    exact ⟨b, c, a, by rw [hrabcd, hd]⟩
  obtain ⟨b₁, c₁, d₁, a₁, ha₁, hr₁⟩ : ∃ b c d a : F, a ≠ 0 ∧ tauS b c d * lam a ∈ R₀ := by
    by_contra hcon
    push Not at hcon
    refine hnot (isElemAbelian_of_Sym fun r hr => ?_)
    obtain ⟨b, c, d, a, hrabcd⟩ := exists_coords (hRU hr)
    have ha : a = 0 := by
      by_contra ha
      exact hcon b c d a ha (hrabcd ▸ hr)
    exact ⟨b, c, d, by rw [hrabcd, ha, lam_zero, mul_one]⟩
  have hline : ∀ w : F, tauS (w * b₀) (w * c₀) (w * d₀) ∈ R₀ := by
    have hconj : ∀ u : Fˣ, tauS ((u : F) ^ 2 * b₀) ((u : F) ^ 2 * c₀) ((u : F) ^ 2 * d₀) *
        lam a₀ ∈ R₀ := by
      intro u
      have := hT (fun _ => u) _ hr₀
      have e : SymplecticTorusWeyl.torusHom (fun _ : Fin 2 => u) * (tauS b₀ c₀ d₀ * lam a₀) *
          (SymplecticTorusWeyl.torusHom (fun _ : Fin 2 => u))⁻¹ =
          (SymplecticTorusWeyl.torusHom (fun _ : Fin 2 => u) * tauS b₀ c₀ d₀ *
            (SymplecticTorusWeyl.torusHom (fun _ : Fin 2 => u))⁻¹) *
          (SymplecticTorusWeyl.torusHom (fun _ : Fin 2 => u) * lam a₀ *
            (SymplecticTorusWeyl.torusHom (fun _ : Fin 2 => u))⁻¹) := by group
      rwa [e, torusHom_const_conj_tauS, torusHom_const_conj_lam] at this
    intro w
    obtain ⟨u, v, hu, hv, huv⟩ := exists_sq_add_sq h4 w
    have h1 := hconj (Units.mk0 u hu)
    have h2 := hconj (Units.mk0 v hv)
    have h3 := R₀.mul_mem h1 (R₀.inv_mem h2)
    have e : tauS (u ^ 2 * b₀) (u ^ 2 * c₀) (u ^ 2 * d₀) * lam a₀ *
        (tauS (v ^ 2 * b₀) (v ^ 2 * c₀) (v ^ 2 * d₀) * lam a₀)⁻¹ =
        tauS (u ^ 2 * b₀) (u ^ 2 * c₀) (u ^ 2 * d₀) *
          (tauS (v ^ 2 * b₀) (v ^ 2 * c₀) (v ^ 2 * d₀))⁻¹ := by group
    simp only [Units.val_mk0] at h3
    rw [e, tauS_mul_tauS_inv] at h3
    rw [← huv]
    simpa only [add_mul] using h3
  have hcomm : ∀ x ∈ R₀, ∀ a : F, ⁅lam a, x⁆ ∈ R₀ := by
    intro x hx a
    rw [commutatorElement_def]
    exact R₀.mul_mem (hUc _ (lam_mem_unipotent a) x hx) (R₀.inv_mem hx)
  have hZ1 : ∀ a : F, tauS (a ^ 2) a 0 ∈ R₀ := by
    intro a
    have h := hcomm _ (hline d₀⁻¹) a
    rw [commutatorElement_lam_tauS, inv_mul_cancel₀ hd₀, mul_one, mul_one] at h
    exact h
  have hZ2 : ∀ v : Fˣ, tauS 1 (v : F) 0 ∈ R₀ := by
    intro v
    have h := hT ![1, v] _ (hZ1 1)
    rw [torus_conj_tauS] at h
    simpa using h
  have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hZc : ∀ y : F, tauS 0 y 0 ∈ R₀ := by
    intro y
    obtain ⟨v, v', hv, hv', hvv⟩ := exists_add_ne_zero h4 y
    have h3 := R₀.mul_mem (hZ2 (Units.mk0 v hv)) (hZ2 (Units.mk0 v' hv'))
    simp only [Units.val_mk0, tauS_mul_tauS, h11, add_zero, hvv] at h3
    exact h3
  have hZb1 : tauS 1 0 0 ∈ R₀ := by
    have h3 := R₀.mul_mem (hZ2 1) (hZc 1)
    simp only [Units.val_one, tauS_mul_tauS, h11, add_zero] at h3
    exact h3
  have hZb : ∀ x : F, tauS x 0 0 ∈ R₀ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, tauS_zero]; exact R₀.one_mem
    · obtain ⟨z, hz⟩ := exists_sq x
      have hz0 : z ≠ 0 := fun h => hx (by rw [← hz, h]; ring)
      have h := hT ![Units.mk0 z hz0, 1] _ hZb1
      rw [torus_conj_tauS] at h
      simpa [hz] using h
  have hZ : ∀ x y : F, tauS x y 0 ∈ R₀ := by
    intro x y
    have h := R₀.mul_mem (hZb x) (hZc y)
    simpa [tauS_mul_tauS] using h
  have hD : ∀ z : F, tauS 0 0 z ∈ R₀ := by
    intro z
    have hw := hline (z * d₀⁻¹)
    have e : z * d₀⁻¹ * d₀ = z := by field_simp
    rw [e] at hw
    have h := R₀.mul_mem hw (R₀.inv_mem (hZ (z * d₀⁻¹ * b₀) (z * d₀⁻¹ * c₀)))
    rw [tauS_mul_tauS_inv, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero] at h
    exact h
  have hSym : ∀ x y z : F, tauS x y z ∈ R₀ := by
    intro x y z
    have h := R₀.mul_mem (hZ x y) (hD z)
    simpa [tauS_mul_tauS] using h
  have hlam1 : lam a₁ ∈ R₀ := by
    have h := R₀.mul_mem (R₀.inv_mem (hSym b₁ c₁ d₁)) hr₁
    simpa using h
  have hlamall : ∀ a : F, lam a ∈ R₀ := by
    intro a
    by_cases ha : a = 0
    · rw [ha, lam_zero]; exact R₀.one_mem
    · have h := hT ![Units.mk0 (a * a₁⁻¹) (mul_ne_zero ha (inv_ne_zero ha₁)), 1] _ hlam1
      rw [torusHom_first_conj_lam] at h
      simpa [inv_mul_cancel_right₀ ha₁] using h
  refine le_antisymm hRU (fun g hg => ?_)
  obtain ⟨b, c, d, a, rfl⟩ := exists_coords hg
  exact R₀.mul_mem (hSym b c d) (hlamall a)

end Sp4Core

end CFSG.QuasithinUnique.Lin2
