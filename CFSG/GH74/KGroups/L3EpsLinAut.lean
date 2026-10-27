module

public import CFSG.GH74.KGroups.L3EpsLinSyl
public import CFSG.GH74.KGroups.L3EpsAutDiag
public import CFSG.GH74.KGroups.L3EpsNoNormalThree

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

section Diag

variable {F : Type} [Field F]

theorem torus_eq_diagSL (x y : Fˣ) (a b c : F) (h : a * b * c = 1) (hx : (x : F) = a) (hy : (y : F) = b)
    (hc : (((x * y)⁻¹ : Fˣ) : F) = c) : (torus (x, y) : SL(3, F)) = diagSL a b c h := by
  apply Subtype.ext
  rw [coe_torus, coe_diagSL]
  congr 1
  ext k
  fin_cases k
  · simpa using hx
  · simpa using hy
  · simpa using hc

theorem proj_diagSL_mem_Jexp {r : ℕ} {a b c : F} (h : a * b * c = 1) (ha : a ^ r = 1) (hb : b ^ r = 1) :
    proj 3 F (diagSL a b c h) ∈ Jexp (F := F) r := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (h ▸ one_ne_zero))
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (h ▸ one_ne_zero))
  have hc0 : c ≠ 0 := right_ne_zero_of_mul (h ▸ one_ne_zero)
  let x : mu r F := ⟨Units.mk0 a ha0, mem_mu.2 (by ext; simpa using ha)⟩
  let y : mu r F := ⟨Units.mk0 b hb0, mem_mu.2 (by ext; simpa using hb)⟩
  refine ⟨(x, y), ?_⟩
  show proj 3 F (torus ((Units.mk0 a ha0), (Units.mk0 b hb0))) = proj 3 F (diagSL a b c h)
  congr 1
  refine torus_eq_diagSL _ _ _ _ _ h rfl rfl ?_
  have : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h
  simp [this]

theorem exists_diag_of_mem_Jexp {r : ℕ} {z : projectiveSL 3 F} (hz : z ∈ Jexp (F := F) r) :
    ∃ (a b c : F) (h : a * b * c = 1), a ^ r = 1 ∧ b ^ r = 1 ∧ c ^ r = 1 ∧ z = proj 3 F (diagSL a b c h) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := hz
  refine ⟨((x : Fˣ) : F), ((y : Fˣ) : F), ((((x : Fˣ) * (y : Fˣ))⁻¹ : Fˣ) : F), by
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one], ?_, ?_, ?_, rfl⟩
  · rw [← Units.val_pow_eq_pow_val, mem_mu.1 x.2, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, mem_mu.1 y.2, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, inv_pow, mul_pow, mem_mu.1 x.2, mem_mu.1 y.2]
    simp

theorem proj_diagSL_inj {r : ℕ} (hr3 : ¬ 3 ∣ r) {a b c a' b' c' : F} (h : a * b * c = 1)
    (h' : a' * b' * c' = 1) (ha : a ^ r = 1) (hb : b ^ r = 1) (ha' : a' ^ r = 1) (hb' : b' ^ r = 1)
    (he : proj 3 F (diagSL a b c h) = proj 3 F (diagSL a' b' c' h')) : a = a' ∧ b = b' ∧ c = c' := by
  have h0 := fun {a b c : F} (h : a * b * c = 1) =>
    (⟨left_ne_zero_of_mul (left_ne_zero_of_mul (h ▸ one_ne_zero)),
      right_ne_zero_of_mul (left_ne_zero_of_mul (h ▸ one_ne_zero)),
      right_ne_zero_of_mul (h ▸ one_ne_zero)⟩ : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0)
  obtain ⟨ha0, hb0, hc0⟩ := h0 h
  obtain ⟨ha0', hb0', hc0'⟩ := h0 h'
  let x : mu r F := ⟨Units.mk0 a ha0, mem_mu.2 (by ext; simpa using ha)⟩
  let y : mu r F := ⟨Units.mk0 b hb0, mem_mu.2 (by ext; simpa using hb)⟩
  let x' : mu r F := ⟨Units.mk0 a' ha0', mem_mu.2 (by ext; simpa using ha')⟩
  let y' : mu r F := ⟨Units.mk0 b' hb0', mem_mu.2 (by ext; simpa using hb')⟩
  have hx : thetaMu r (x, y) = proj 3 F (diagSL a b c h) := by
    show proj 3 F (torus ((Units.mk0 a ha0), (Units.mk0 b hb0))) = proj 3 F (diagSL a b c h)
    congr 1
    refine torus_eq_diagSL _ _ _ _ _ h rfl rfl ?_
    have : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h
    simp [this]
  have hx' : thetaMu r (x', y') = proj 3 F (diagSL a' b' c' h') := by
    show proj 3 F (torus ((Units.mk0 a' ha0'), (Units.mk0 b' hb0'))) = proj 3 F (diagSL a' b' c' h')
    congr 1
    refine torus_eq_diagSL _ _ _ _ _ h' rfl rfl ?_
    have : c' = (a' * b')⁻¹ := eq_inv_of_mul_eq_one_right h'
    simp [this]
  have hxy : (x, y) = (x', y') := thetaMu_injective hr3 (by rw [hx, hx', he])
  have e1 : a = a' := by
    have := congrArg (fun p : mu r F × mu r F => ((p.1 : Fˣ) : F)) hxy
    simpa [x, x'] using this
  have e2 : b = b' := by
    have := congrArg (fun p : mu r F × mu r F => ((p.2 : Fˣ) : F)) hxy
    simpa [y, y'] using this
  refine ⟨e1, e2, ?_⟩
  have h1 : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h
  have h2 : c' = (a' * b')⁻¹ := eq_inv_of_mul_eq_one_right h'
  rw [h1, h2, e1, e2]

end Diag

section Basic

variable {F : Type} [Field F]

theorem tauBar_conj_diag (a b c : F) (h : a * b * c = 1) (h' : b * a * c = 1) :
    (tauBar : projectiveSL 3 F) * proj 3 F (diagSL a b c h) * tauBar⁻¹ = proj 3 F (diagSL b a c h') := by
  have e := swapSL_mul_diagSL (F := F) a b c h h'
  have e2 : (tauBar : projectiveSL 3 F) * proj 3 F (diagSL a b c h) =
      proj 3 F (diagSL b a c h') * tauBar := by
    show proj 3 F swapSL * proj 3 F (diagSL a b c h) = proj 3 F (diagSL b a c h') * proj 3 F swapSL
    rw [← map_mul, ← map_mul, e]
  rw [e2, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_injective_of_center {X : Type*} [Group X] (h : ∀ x : X, (∀ y, y * x = x * y) → x = 1) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply h
  intro y
  have := congrArg (fun φ : MulAut X => φ y) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem conj_injective_projectiveSL :
    Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  apply conj_injective_of_center
  intro x hx
  have : x ∈ Subgroup.center (projectiveSL 3 F) := Subgroup.mem_center_iff.2 hx
  rw [center_projectiveSL_three_eq_bot (K := F), Subgroup.mem_bot] at this
  exact this

end Basic

section Aut

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem aut_preserves_P {r : ℕ} (A : Subgroup (MulAut (projectiveSL 3 F)))
    (hAP : A ⊓ inner (projectiveSL 3 F) = (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _))
    {α : MulAut (projectiveSL 3 F)} (hα : α ∈ A) {x : projectiveSL 3 F} (hx : x ∈ Pexp (F := F) r) :
    α x ∈ Pexp (F := F) r := by
  have h1 : MulAut.conj x ∈ A ⊓ inner (projectiveSL 3 F) := by
    rw [hAP]
    exact ⟨x, hx, rfl⟩
  have h2 : α * MulAut.conj x * α⁻¹ ∈ A ⊓ inner (projectiveSL 3 F) := by
    refine ⟨A.mul_mem (A.mul_mem hα h1.1) (A.inv_mem hα), ?_⟩
    rw [mulAut_conj_conj]
    exact ⟨α x, rfl⟩
  rw [mulAut_conj_conj, hAP] at h2
  obtain ⟨x', hx', hxx'⟩ := h2
  have := conj_injective_projectiveSL hxx'
  rw [← this]
  exact hx'

end Aut

section Unique

variable {F : Type} [Field F] [Finite F]

theorem card_fixed_le {r : ℕ} (hr3 : ¬ 3 ∣ r) (hmu : Nat.card (mu r F) = r) :
    Nat.card ↥(Jexp (F := F) r ⊓ Subgroup.centralizer ({tauBar} : Set (projectiveSL 3 F))) ≤ r := by
  let δ : mu r F →* projectiveSL 3 F :=
    (thetaMu r : mu r F × mu r F →* projectiveSL 3 F).comp
      ((MonoidHom.id (mu r F)).prod (MonoidHom.id (mu r F)))
  have hle : Jexp (F := F) r ⊓ Subgroup.centralizer ({tauBar} : Set (projectiveSL 3 F)) ≤ δ.range := by
    rintro z ⟨⟨⟨x, y⟩, rfl⟩, hz⟩
    have hz' : (tauBar : projectiveSL 3 F) * thetaMu r (x, y) = thetaMu r (x, y) * tauBar :=
      Subgroup.mem_centralizer_iff.1 hz _ (Set.mem_singleton _)
    have h2 : thetaMu r (y, x) = thetaMu r (x, y) := by
      rw [← tauBar_conj_theta, hz', mul_assoc, mul_inv_cancel, mul_one]
    have h3 := thetaMu_injective hr3 h2
    have hxy : y = x := congrArg Prod.fst h3
    subst hxy
    exact ⟨y, rfl⟩
  calc Nat.card ↥(Jexp (F := F) r ⊓ Subgroup.centralizer ({tauBar} : Set (projectiveSL 3 F)))
      ≤ Nat.card δ.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (mu r F) := Nat.card_le_card_of_surjective δ.rangeRestrict δ.rangeRestrict_surjective
    _ = r := hmu

omit [Finite F] in
theorem exists_conj_of_mem_Pexp {r : ℕ} {x : projectiveSL 3 F} (hx : x ∈ Pexp (F := F) r)
    (hxJ : x ∉ Jexp (F := F) r) : ∃ j ∈ Jexp (F := F) r, x = j * tauBar := by
  obtain ⟨j, hj, h | h⟩ := hx
  · exact absurd (h ▸ hj) hxJ
  · exact ⟨j, hj, h⟩

theorem Jexp_unique {r : ℕ} (hr3 : ¬ 3 ∣ r) (hmu : Nat.card (mu r F) = r) (hr4 : 4 ≤ r)
    {J' : Subgroup (projectiveSL 3 F)} (hJ'P : J' ≤ Pexp (F := F) r)
    (hab : ∀ x ∈ J', ∀ y ∈ J', x * y = y * x) (hcard : Nat.card J' = r ^ 2) :
    J' = Jexp (F := F) r := by
  by_contra hne
  have hJcard : Nat.card (Jexp (F := F) r) = r ^ 2 := card_Jexp hr3 hmu
  have hnle : ¬ J' ≤ Jexp (F := F) r := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hJcard, hcard]))
  obtain ⟨y₀, hy₀J', hy₀J⟩ := Set.not_subset.1 hnle
  obtain ⟨j₀, hj₀, rfl⟩ := exists_conj_of_mem_Pexp (hJ'P hy₀J') hy₀J
  have hfix : Jexp (F := F) r ⊓ J' ≤ Jexp (F := F) r ⊓ Subgroup.centralizer ({tauBar} : Set (projectiveSL 3 F)) := by
    intro z ⟨hzJ, hzJ'⟩
    refine ⟨hzJ, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have h1 := hab _ hy₀J' z hzJ'
    have h2 := Jexp_comm r j₀ hj₀ z hzJ
    have : j₀ * (tauBar * z) = j₀ * (z * tauBar) := by
      calc j₀ * (tauBar * z) = j₀ * tauBar * z := by rw [mul_assoc]
        _ = z * (j₀ * tauBar) := h1
        _ = z * j₀ * tauBar := by rw [mul_assoc]
        _ = j₀ * z * tauBar := by rw [← h2]
        _ = j₀ * (z * tauBar) := by rw [mul_assoc]
    exact mul_left_cancel this
  have hrel : (Jexp (F := F) r).relIndex J' ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨j₀ * tauBar, hy₀J', fun b hb => ?_⟩
    by_cases hbJ : b ∈ Jexp (F := F) r
    · exact Or.inr hbJ
    · left
      obtain ⟨j₁, hj₁, rfl⟩ := exists_conj_of_mem_Pexp (hJ'P hb) hbJ
      have h := tauBar_mul_self (F := F)
      have h2 : j₁ * tauBar * (j₀ * tauBar) = j₁ * (tauBar * j₀ * tauBar⁻¹) := by
        calc j₁ * tauBar * (j₀ * tauBar) = j₁ * (tauBar * j₀ * tauBar⁻¹) * (tauBar * tauBar) := by group
          _ = j₁ * (tauBar * j₀ * tauBar⁻¹) := by rw [h, mul_one]
      rw [h2]
      exact mul_mem hj₁ (tauBar_conj_mem_Jexp r hj₀)
  have hrel2 : (Jexp (F := F) r).relIndex J' ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
  have hmulcard := Subgroup.relIndex_mul_card (H := Jexp (F := F) r) (K := J')
  have hinfle : Nat.card ↥(Jexp (F := F) r ⊓ J') ≤ r :=
    (Subgroup.card_le_of_le hfix).trans (card_fixed_le hr3 hmu)
  have h3 : r ^ 2 ≤ 2 * r := by
    calc r ^ 2 = Nat.card J' := hcard.symm
      _ = (Jexp (F := F) r).relIndex J' * Nat.card ↥(Jexp (F := F) r ⊓ J') := hmulcard.symm
      _ ≤ 2 * r := Nat.mul_le_mul hrel2 hinfle
  nlinarith

end Unique

section PreserveJ

variable {F : Type} [Field F] [Finite F]

theorem aut_preserves_J {r : ℕ} (hr3 : ¬ 3 ∣ r) (hmu : Nat.card (mu r F) = r) (hr4 : 4 ≤ r)
    (A : Subgroup (MulAut (projectiveSL 3 F)))
    (hAP : A ⊓ inner (projectiveSL 3 F) = (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _))
    {α : MulAut (projectiveSL 3 F)} (hα : α ∈ A) {j : projectiveSL 3 F} (hj : j ∈ Jexp (F := F) r) :
    α j ∈ Jexp (F := F) r := by
  have hJ' : (Jexp (F := F) r).map α.toMonoidHom = Jexp (F := F) r := by
    refine Jexp_unique hr3 hmu hr4 ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact aut_preserves_P A hAP hα (Jexp_le_Pexp r hy)
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      show α y * α y' = α y' * α y
      rw [← map_mul, ← map_mul, Jexp_comm r y hy y' hy']
    · rw [Subgroup.card_map_of_injective α.injective, card_Jexp hr3 hmu]
  rw [← hJ']
  exact ⟨j, hj, rfl⟩

end PreserveJ

section Invol

variable {F : Type} [Field F]

@[expose] def eInv1 : projectiveSL 3 F := proj 3 F (diagSL 1 (-1) (-1) (by ring))
@[expose] def eInv2 : projectiveSL 3 F := proj 3 F (diagSL (-1) 1 (-1) (by ring))
@[expose] def eInv3 : projectiveSL 3 F := proj 3 F (diagSL (-1) (-1) 1 (by ring))

theorem eInv1_mem {r : ℕ} (hr2 : 2 ∣ r) : (eInv1 : projectiveSL 3 F) ∈ Jexp (F := F) r :=
  proj_diagSL_mem_Jexp _ (one_pow r) (Even.neg_one_pow (even_iff_two_dvd.2 hr2))

theorem eInv2_mem {r : ℕ} (hr2 : 2 ∣ r) : (eInv2 : projectiveSL 3 F) ∈ Jexp (F := F) r :=
  proj_diagSL_mem_Jexp _ (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (one_pow r)

theorem eInv3_mem {r : ℕ} (hr2 : 2 ∣ r) : (eInv3 : projectiveSL 3 F) ∈ Jexp (F := F) r :=
  proj_diagSL_mem_Jexp _ (Even.neg_one_pow (even_iff_two_dvd.2 hr2))
    (Even.neg_one_pow (even_iff_two_dvd.2 hr2))

theorem eInv1_mul_self : (eInv1 : projectiveSL 3 F) * eInv1 = 1 := by
  unfold eInv1
  rw [← map_mul, diagSL_mul, ← map_one (proj 3 F), ← diagSL_one (K := F) (by ring)]
  congr 1
  exact diagSL_congr (by simp) (by simp) (by simp)

theorem eInv2_mul_self : (eInv2 : projectiveSL 3 F) * eInv2 = 1 := by
  unfold eInv2
  rw [← map_mul, diagSL_mul, ← map_one (proj 3 F), ← diagSL_one (K := F) (by ring)]
  congr 1
  exact diagSL_congr (by simp) (by simp) (by simp)

theorem eInv3_mul_self : (eInv3 : projectiveSL 3 F) * eInv3 = 1 := by
  unfold eInv3
  rw [← map_mul, diagSL_mul, ← map_one (proj 3 F), ← diagSL_one (K := F) (by ring)]
  congr 1
  exact diagSL_congr (by simp) (by simp) (by simp)

theorem eInv1_mul_eInv2 : (eInv1 : projectiveSL 3 F) * eInv2 = eInv3 := by
  unfold eInv1 eInv2 eInv3
  rw [← map_mul, diagSL_mul]
  congr 1
  exact diagSL_congr (by simp) (by simp) (by simp)

theorem eInv_comm12 : (eInv1 : projectiveSL 3 F) * eInv2 = eInv2 * eInv1 := by
  unfold eInv1 eInv2
  rw [← map_mul, ← map_mul, diagSL_mul, diagSL_mul]
  congr 1
  exact diagSL_congr (by simp) (by simp) (by simp)

end Invol

section InvolCases

variable {F : Type} [Field F]

theorem proj_diagSL_congr {a b c a' b' c' : F} {h : a * b * c = 1} {h' : a' * b' * c' = 1} (ha : a = a')
    (hb : b = b') (hc : c = c') : proj 3 F (diagSL a b c h) = proj 3 F (diagSL a' b' c' h') := by
  congr 1
  exact diagSL_congr ha hb hc

theorem proj_diagSL_one : proj 3 F (diagSL (1 : F) 1 1 (by ring)) = 1 := by
  rw [diagSL_one (K := F) (by ring), map_one]

theorem eInv1_ne_one {r : ℕ} (hr3 : ¬ 3 ∣ r) (hr2 : 2 ∣ r) (h2 : (2 : F) ≠ 0) :
    (eInv1 : projectiveSL 3 F) ≠ 1 := by
  intro h
  rw [← proj_diagSL_one] at h
  have := (proj_diagSL_inj hr3 (r := r) (a := 1) (b := -1) (c := -1) (a' := 1) (b' := 1) (c' := 1) (by ring)
    (by ring) (one_pow r) (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (one_pow r) (one_pow r) h).2.1
  apply h2
  linear_combination -this

theorem eInv2_ne_one {r : ℕ} (hr3 : ¬ 3 ∣ r) (hr2 : 2 ∣ r) (h2 : (2 : F) ≠ 0) :
    (eInv2 : projectiveSL 3 F) ≠ 1 := by
  intro h
  rw [← proj_diagSL_one] at h
  have := (proj_diagSL_inj hr3 (r := r) (a := -1) (b := 1) (c := -1) (a' := 1) (b' := 1) (c' := 1) (by ring)
    (by ring) (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (one_pow r) (one_pow r) (one_pow r) h).1
  apply h2
  linear_combination -this

theorem eInv3_ne_one {r : ℕ} (hr3 : ¬ 3 ∣ r) (hr2 : 2 ∣ r) (h2 : (2 : F) ≠ 0) :
    (eInv3 : projectiveSL 3 F) ≠ 1 := by
  intro h
  rw [← proj_diagSL_one] at h
  have := (proj_diagSL_inj hr3 (r := r) (a := -1) (b := -1) (c := 1) (a' := 1) (b' := 1) (c' := 1) (by ring)
    (by ring) (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (Even.neg_one_pow (even_iff_two_dvd.2 hr2))
    (one_pow r) (one_pow r) h).1
  apply h2
  linear_combination -this

theorem eInv1_ne_eInv2 {r : ℕ} (hr3 : ¬ 3 ∣ r) (hr2 : 2 ∣ r) (h2 : (2 : F) ≠ 0) :
    (eInv1 : projectiveSL 3 F) ≠ eInv2 := by
  intro h
  have := (proj_diagSL_inj hr3 (r := r) (a := 1) (b := -1) (c := -1) (a' := -1) (b' := 1) (c' := -1) (by ring)
    (by ring) (one_pow r) (Even.neg_one_pow (even_iff_two_dvd.2 hr2))
    (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (one_pow r) h).1
  apply h2
  linear_combination this

theorem eInv1_ne_eInv3 {r : ℕ} (hr3 : ¬ 3 ∣ r) (hr2 : 2 ∣ r) (h2 : (2 : F) ≠ 0) :
    (eInv1 : projectiveSL 3 F) ≠ eInv3 := by
  intro h
  have := (proj_diagSL_inj hr3 (r := r) (a := 1) (b := -1) (c := -1) (a' := -1) (b' := -1) (c' := 1) (by ring)
    (by ring) (one_pow r) (Even.neg_one_pow (even_iff_two_dvd.2 hr2))
    (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) h).1
  apply h2
  linear_combination this

theorem eInv2_ne_eInv3 {r : ℕ} (hr3 : ¬ 3 ∣ r) (hr2 : 2 ∣ r) (h2 : (2 : F) ≠ 0) :
    (eInv2 : projectiveSL 3 F) ≠ eInv3 := by
  intro h
  have := (proj_diagSL_inj hr3 (r := r) (a := -1) (b := 1) (c := -1) (a' := -1) (b' := -1) (c' := 1) (by ring)
    (by ring) (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (one_pow r)
    (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) (Even.neg_one_pow (even_iff_two_dvd.2 hr2)) h).2.1
  apply h2
  linear_combination this

theorem Jexp_invol {r : ℕ} (hr3 : ¬ 3 ∣ r) {j : projectiveSL 3 F} (hj : j ∈ Jexp (F := F) r)
    (hjj : j * j = 1) : j = 1 ∨ j = eInv1 ∨ j = eInv2 ∨ j = eInv3 := by
  obtain ⟨a, b, c, h, ha, hb, hc, rfl⟩ := exists_diag_of_mem_Jexp hj
  have hsq : proj 3 F (diagSL (a * a) (b * b) (c * c) (by
      calc a * a * (b * b) * (c * c) = (a * b * c) * (a * b * c) := by ring
        _ = 1 := by rw [h, one_mul])) = proj 3 F (diagSL (1 : F) 1 1 (by ring)) := by
    rw [proj_diagSL_one, ← hjj, ← map_mul, diagSL_mul]
  have hinj := proj_diagSL_inj hr3 (r := r) _ _ (by rw [mul_pow, ha, one_mul]) (by rw [mul_pow, hb, one_mul])
    (one_pow r) (one_pow r) hsq
  obtain ⟨h1a, h1b, -⟩ := hinj
  rcases mul_self_eq_one_iff.1 h1a with rfl | rfl <;> rcases mul_self_eq_one_iff.1 h1b with rfl | rfl
  · left
    rw [← proj_diagSL_one]
    exact proj_diagSL_congr rfl rfl (by linear_combination h)
  · right; left
    exact proj_diagSL_congr rfl rfl (by linear_combination -h)
  · right; right; left
    exact proj_diagSL_congr rfl rfl (by linear_combination -h)
  · right; right; right
    exact proj_diagSL_congr rfl rfl (by linear_combination h)

end InvolCases

section PermPart

variable {X : Type*} [Group X] [Finite X]

theorem exists_fixing_subgroup (B : Subgroup (MulAut X)) (hB : IsPGroup 2 B) (Vs : Finset X)
    (hV3 : Vs.card ≤ 3) (hinv : ∀ α ∈ B, ∀ x ∈ Vs, α x ∈ Vs) :
    ∃ Y : Subgroup B, Y.index ≤ 2 ∧ ∀ α ∈ Y, ∀ x ∈ Vs, (α : MulAut X) x = x := by
  classical
  let S : SubMulAction B X :=
    { carrier := (Vs : Set X), smul_mem' := fun α x hx => hinv α α.2 x hx }
  let ψ : B →* Equiv.Perm S := MulAction.toPermHom B S
  refine ⟨ψ.ker, ?_, ?_⟩
  · rw [Subgroup.index_ker]
    have hrange : IsPGroup 2 ψ.range :=
      IsPGroup.of_surjective hB ψ.rangeRestrict ψ.rangeRestrict_surjective
    have h1 : Nat.card ψ.range ∣ ordProj[2] (Nat.card (Equiv.Perm S)) := card_dvd_ordProj hrange
    have h2 : Nat.card ψ.range ∣ Nat.factorial (Nat.card S) := by
      rw [Nat.card_perm] at h1
      exact h1.trans (Nat.ordProj_dvd _ 2)
    have hS3 : Nat.card S ≤ 3 := by
      have : Nat.card S = Vs.card := by
        calc Nat.card S = Nat.card {x : X // x ∈ Vs} :=
              Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
          _ = Vs.card := by simp
      omega
    have h3 : Nat.factorial (Nat.card S) ∣ 6 := (Nat.factorial_dvd_factorial hS3).trans (by decide)
    have h4 := h2.trans h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hrange
    rw [hk] at h4 ⊢
    by_contra hcon
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k ≤ 1 := by omega
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
    have := this.trans h4
    omega
  · intro α hα x hx
    have hα1 : ψ α = 1 := hα
    have := congrArg (fun π : Equiv.Perm S => ((π ⟨x, hx⟩ : S) : X)) hα1
    exact this

end PermPart

section Central

variable {F : Type} [Field F] [Finite F]

structure LinCtx (F : Type) [Field F] [Finite F] (r : ℕ) : Prop where
  hq4 : Nat.card F % 4 = 1
  hr : r = ordProj[2] (Nat.card F - 1)

theorem LinCtx.hF2 {r : ℕ} (hc : LinCtx F r) : Nat.card F % 2 = 1 := by
  have := hc.hq4
  omega

theorem LinCtx.hdvd {r : ℕ} (hc : LinCtx F r) : r ∣ Nat.card F - 1 := hc.hr ▸ Nat.ordProj_dvd _ 2

theorem LinCtx.r4 {r : ℕ} (hc : LinCtx F r) : 4 ∣ r := by
  have hq := hc.hq4
  have h2 := Finite.one_lt_card (α := F)
  have hne : Nat.card F - 1 ≠ 0 := by omega
  have hv : 2 ≤ (Nat.card F - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hne).1 (by
      have : 4 ∣ Nat.card F - 1 := by omega
      simpa using this)
  rw [hc.hr]
  exact (pow_dvd_pow 2 hv : 2 ^ 2 ∣ 2 ^ (Nat.card F - 1).factorization 2)

theorem LinCtx.r2 {r : ℕ} (hc : LinCtx F r) : 2 ∣ r := dvd_trans (by norm_num) hc.r4

theorem LinCtx.r3 {r : ℕ} (hc : LinCtx F r) : ¬ 3 ∣ r := by
  intro h3
  rw [hc.hr] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem LinCtx.r4' {r : ℕ} (hc : LinCtx F r) : 4 ≤ r :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (by rintro rfl; exact hc.r3 (dvd_zero 3))) hc.r4

theorem LinCtx.hmu {r : ℕ} (hc : LinCtx F r) : Nat.card (mu r F) = r := card_mu hc.hdvd

theorem LinCtx.hchar {r : ℕ} (hc : LinCtx F r) : ringChar F ≠ 2 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 := h2 ▸ ringChar.charP F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have := hc.hF2
  rw [hcard] at this
  have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
  have : 2 ^ (n : ℕ) % 2 = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hk, pow_succ]
    simp
  omega

theorem LinCtx.h2 {r : ℕ} (hc : LinCtx F r) : (2 : F) ≠ 0 := Ring.two_ne_zero hc.hchar

theorem LinCtx.exists_i {r : ℕ} (hc : LinCtx F r) : ∃ i : F, i * i = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have h := (FiniteField.isSquare_neg_one_iff (F := F)).2 (by
    rw [← Nat.card_eq_fintype_card]
    have := hc.hq4
    omega)
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi.symm⟩

theorem LinCtx.exists_moved {r : ℕ} (hc : LinCtx F r) :
    ∃ y ∈ Jexp (F := F) r, (tauBar : projectiveSL 3 F) * y * tauBar⁻¹ ≠ y := by
  obtain ⟨i, hi⟩ := hc.exists_i
  have h1 : i * 1 * (-i) = 1 := by linear_combination -hi
  have h1' : 1 * i * (-i) = 1 := by linear_combination -hi
  have hi4 : i ^ r = 1 := by
    obtain ⟨m, hm⟩ := hc.r4
    rw [hm, pow_mul]
    have : i ^ 4 = 1 := by
      calc i ^ 4 = (i * i) * (i * i) := by ring
        _ = 1 := by rw [hi]; ring
    rw [this, one_pow]
  refine ⟨proj 3 F (diagSL i 1 (-i) h1), proj_diagSL_mem_Jexp h1 hi4 (one_pow r), ?_⟩
  rw [tauBar_conj_diag i 1 (-i) h1 h1']
  intro h
  have h3 := (proj_diagSL_inj hc.r3 (r := r) h1' h1 (one_pow r) hi4 hi4 (one_pow r) h).1
  rw [← h3] at hi
  apply hc.h2
  linear_combination hi

end Central

section KeyUse

variable {F : Type} [Field F] [Finite F]

theorem central_in_Jexp {r : ℕ} (hc : LinCtx F r) {z : projectiveSL 3 F} (hzP : z ∈ Pexp (F := F) r)
    (hz : ∀ s ∈ Pexp (F := F) r, s * z = z * s) : z ∈ Jexp (F := F) r := by
  by_contra hzJ
  obtain ⟨j₀, hj₀, rfl⟩ := exists_conj_of_mem_Pexp hzP hzJ
  obtain ⟨y, hy, hyne⟩ := hc.exists_moved
  have h1 := hz y (Jexp_le_Pexp r hy)
  have h2 := Jexp_comm r j₀ hj₀ y hy
  have h3 : j₀ * (y * tauBar) = j₀ * (tauBar * y) := by
    calc j₀ * (y * tauBar) = j₀ * y * tauBar := by rw [mul_assoc]
      _ = y * j₀ * tauBar := by rw [h2]
      _ = y * (j₀ * tauBar) := by rw [mul_assoc]
      _ = j₀ * tauBar * y := h1
      _ = j₀ * (tauBar * y) := by rw [mul_assoc]
  have h4 : y * tauBar = tauBar * y := mul_left_cancel h3
  apply hyne
  rw [← h4]
  group

theorem centralizer_J_inner {r : ℕ} (hc : LinCtx F r) (A : Subgroup (MulAut (projectiveSL 3 F)))
    (hA : IsPGroup 2 A)
    (hAP : A ⊓ inner (projectiveSL 3 F) = (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _))
    {α : MulAut (projectiveSL 3 F)} (hα : α ∈ A) (hfix : ∀ j ∈ Jexp (F := F) r, α j = j) :
    ∃ w ∈ Jexp (F := F) r, α = MulAut.conj w := by
  have hr3 := hc.r3
  have hmu := hc.hmu
  have hr4 := hc.r4'
  have hconjA : ∀ x ∈ Pexp (F := F) r, MulAut.conj x ∈ A := fun x hx => by
    have : MulAut.conj x ∈ (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _) := ⟨x, hx, rfl⟩
    rw [← hAP] at this
    exact this.1
  have hατP := aut_preserves_P A hAP hα (tauBar_mem_Pexp r)
  have hατJ : α tauBar ∉ Jexp (F := F) r := by
    intro h
    have hinv := aut_preserves_J hr3 hmu hr4 A hAP (A.inv_mem hα) h
    have : α⁻¹ (α tauBar) = tauBar := by simp
    rw [this] at hinv
    exact tauBar_not_mem_Jexp hinv
  obtain ⟨j₀, hj₀, hαt⟩ := exists_conj_of_mem_Pexp hατP hατJ
  have hsq : (j₀ * tauBar) * (j₀ * tauBar) = 1 := by
    rw [← hαt, ← map_mul, tauBar_mul_self, map_one]
  obtain ⟨a, b, c, h, ha, hb, hcc, rfl⟩ := exists_diag_of_mem_Jexp hj₀
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (h ▸ one_ne_zero))
  have h' : b * a * c = 1 := by rw [mul_comm b a]; exact h
  have e1 : proj 3 F (diagSL a b c h) * tauBar * (proj 3 F (diagSL a b c h) * tauBar) =
      proj 3 F (diagSL (a * b) (b * a) (c * c) (by
        calc a * b * (b * a) * (c * c) = (a * b * c) * (a * b * c) := by ring
          _ = 1 := by rw [h, one_mul])) := by
    calc proj 3 F (diagSL a b c h) * tauBar * (proj 3 F (diagSL a b c h) * tauBar)
        = proj 3 F (diagSL a b c h) * (tauBar * proj 3 F (diagSL a b c h) * tauBar⁻¹) *
          (tauBar * tauBar) := by group
      _ = proj 3 F (diagSL a b c h) * proj 3 F (diagSL b a c h') * 1 := by
          rw [tauBar_conj_diag a b c h h', tauBar_mul_self]
      _ = _ := by rw [mul_one, ← map_mul, diagSL_mul]
  rw [e1, ← proj_diagSL_one (F := F)] at hsq
  obtain ⟨hab, -, hcc1⟩ := proj_diagSL_inj hr3 (r := r) _ _
    (by rw [mul_pow, ha, hb, one_mul]) (by rw [mul_pow, hb, ha, one_mul]) (one_pow r) (one_pow r) hsq
  have hc1 : c = 1 := by
    have : a * b * c = c := by rw [hab, one_mul]
    rw [← this]; exact h
  have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  subst hc1
  subst hb'
  have hh₁ : a * 1 * a⁻¹ = 1 := by field_simp
  have ha_inv : a⁻¹ ^ r = 1 := by rw [inv_pow, ha, inv_one]
  set h₁ : projectiveSL 3 F := proj 3 F (diagSL a 1 a⁻¹ hh₁) with hh₁def
  have hh₁J : h₁ ∈ Jexp (F := F) r := proj_diagSL_mem_Jexp hh₁ ha (one_pow r)
  have hcalc : h₁ * tauBar * h₁⁻¹ = proj 3 F (diagSL a a⁻¹ 1 h) * tauBar := by
    have hinv : h₁⁻¹ = proj 3 F (diagSL a⁻¹ 1 a⁻¹⁻¹ (by field_simp)) := by
      rw [hh₁def, ← map_inv, diagSL_inv']
      exact proj_diagSL_congr rfl inv_one rfl
    have hsw : tauBar * h₁⁻¹ * tauBar⁻¹ = proj 3 F (diagSL 1 a⁻¹ a⁻¹⁻¹ (by field_simp)) := by
      rw [hinv]
      exact tauBar_conj_diag _ _ _ _ _
    calc h₁ * tauBar * h₁⁻¹ = h₁ * (tauBar * h₁⁻¹ * tauBar⁻¹) * tauBar := by group
      _ = proj 3 F (diagSL a a⁻¹ 1 h) * tauBar := by
          rw [hsw, hh₁def, ← map_mul, diagSL_mul]
          congr 2
          exact diagSL_congr (by simp) (by simp) (by simp [ha0])
  have hαh : α tauBar = h₁ * tauBar * h₁⁻¹ := by rw [hαt, hcalc]
  set β : MulAut (projectiveSL 3 F) := MulAut.conj h₁⁻¹ * α with hβ
  have hβA : β ∈ A := A.mul_mem (hconjA _ (inv_mem (Jexp_le_Pexp r hh₁J))) hα
  have hβJ : ∀ j ∈ Jexp (F := F) r, β j = j := by
    intro j hj
    show h₁⁻¹ * α j * h₁⁻¹⁻¹ = j
    rw [hfix j hj, inv_inv]
    have := Jexp_comm r h₁ hh₁J j hj
    calc h₁⁻¹ * j * h₁ = h₁⁻¹ * (j * h₁) := by rw [mul_assoc]
      _ = h₁⁻¹ * (h₁ * j) := by rw [this]
      _ = j := by group
  have hβτ : β tauBar = tauBar := by
    show h₁⁻¹ * α tauBar * h₁⁻¹⁻¹ = tauBar
    rw [hαh, inv_inv]
    group
  have hβP : ∀ x ∈ Pexp (F := F) r, β x = x := by
    rintro x ⟨j, hj, hx | hx⟩
    · rw [hx]; exact hβJ j hj
    · rw [hx, map_mul, hβJ j hj, hβτ]
  obtain ⟨k, hk⟩ := hA ⟨β, hβA⟩
  have hβk : β ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨hP2, hPmax⟩ := Pexp_sylow (F := F) hc.hF2 hc.hq4 hc.hr
  obtain ⟨z, hzP, hzc, hβz⟩ := lin_key hc.hchar hP2 hPmax hβk hβP
  have hzJ := central_in_Jexp hc hzP hzc
  refine ⟨h₁ * z, mul_mem hh₁J hzJ, ?_⟩
  rw [map_mul]
  have : α = MulAut.conj h₁ * β := by
    rw [hβ, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [this, hβz]

end KeyUse

section Formula

variable {F : Type} [Field F] [Finite F]

theorem LinCtx.exists_regular {r : ℕ} (hc : LinCtx F r) :
    ∃ i : F, i * i = -1 ∧ i ^ r = 1 ∧ Function.Injective ![i, 1, -i] := by
  obtain ⟨i, hi⟩ := hc.exists_i
  have hi4 : i ^ r = 1 := by
    obtain ⟨m, hm⟩ := hc.r4
    rw [hm, pow_mul]
    have : i ^ 4 = 1 := by
      calc i ^ 4 = (i * i) * (i * i) := by ring
        _ = 1 := by rw [hi]; ring
    rw [this, one_pow]
  have h2 := hc.h2
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hne1 : i ≠ 1 := by
    intro h
    rw [h] at hi
    apply h2
    linear_combination hi
  have hne2 : i ≠ -i := by
    intro h
    apply hi0
    have : (2 : F) * i = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2
  have hne3 : (1 : F) ≠ -i := by
    intro h
    have hi' : i = -1 := by linear_combination h
    rw [hi'] at hi
    apply h2
    linear_combination hi
  refine ⟨i, hi, hi4, ?_⟩
  intro j k hjk
  fin_cases j <;> fin_cases k <;> simp at hjk ⊢
  · exact absurd hjk hne1
  · exact absurd hjk hne2
  · exact absurd hjk.symm hne1
  · exact absurd hjk hne3
  · exact absurd hjk.symm hne2
  · exact absurd hjk.symm hne3

omit [Finite F] in
theorem entryMap_neg_one (σ : F ≃+* F) (ε : ℕ) : entryMap σ ε (-1) = -1 := by
  unfold entryMap
  split_ifs <;> simp

theorem aut_formula {r : ℕ} (hc : LinCtx F r) (A : Subgroup (MulAut (projectiveSL 3 F)))
    (hAP : A ⊓ inner (projectiveSL 3 F) = (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _))
    {α : MulAut (projectiveSL 3 F)} (hα : α ∈ A) :
    ∃ (σ : F ≃+* F) (ε : ℕ) (π : Equiv.Perm (Fin 3)), ε ≤ 1 ∧
      ∀ (a b c : F) (h : a * b * c = 1),
        ∃ h' : entryMap σ ε (![a, b, c] (π 0)) * entryMap σ ε (![a, b, c] (π 1)) *
            entryMap σ ε (![a, b, c] (π 2)) = 1,
          α (proj 3 F (diagSL a b c h)) = proj 3 F (diagSL (entryMap σ ε (![a, b, c] (π 0)))
            (entryMap σ ε (![a, b, c] (π 1))) (entryMap σ ε (![a, b, c] (π 2))) h') := by
  obtain ⟨i, hi, hi4, hinj⟩ := hc.exists_regular
  have h1 : i * 1 * (-i) = 1 := by linear_combination -hi
  have htestJ : proj 3 F (diagSL i 1 (-i) h1) ∈ Jexp (F := F) r :=
    proj_diagSL_mem_Jexp h1 hi4 (one_pow r)
  have hαtest := aut_preserves_J hc.r3 hc.hmu hc.r4' A hAP hα htestJ
  obtain ⟨x, y, z, hxyz, -, -, -, hxyz'⟩ := exists_diag_of_mem_Jexp hαtest
  exact aut_diag_action α i 1 (-i) h1 hinj ⟨x, y, z, hxyz, hxyz'⟩

theorem aut_formula_ker {r : ℕ} (hc : LinCtx F r) (A : Subgroup (MulAut (projectiveSL 3 F)))
    (hAP : A ⊓ inner (projectiveSL 3 F) = (Pexp (F := F) r).map (MulAut.conj : projectiveSL 3 F →* _))
    {α : MulAut (projectiveSL 3 F)} (hα : α ∈ A) (hα1 : α eInv1 = eInv1) (hα2 : α eInv2 = eInv2) :
    ∃ (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧ ∀ (a b c : F) (h : a * b * c = 1),
      ∃ h' : entryMap σ ε a * entryMap σ ε b * entryMap σ ε c = 1,
        α (proj 3 F (diagSL a b c h)) =
          proj 3 F (diagSL (entryMap σ ε a) (entryMap σ ε b) (entryMap σ ε c) h') := by
  obtain ⟨σ, ε, π, hε, hform⟩ := aut_formula hc A hAP hα
  have hr3 := hc.r3
  have hr2 := hc.r2
  have h2 := hc.h2
  have hneg : ((-1 : F)) ^ r = 1 := Even.neg_one_pow (even_iff_two_dvd.2 hr2)
  have hentry1 : ∀ k : Fin 3, entryMap σ ε (![1, -1, -1] k) = ![1, -1, -1] k := by
    intro k
    fin_cases k <;> simp [entryMap_one, entryMap_neg_one]
  have hentry2 : ∀ k : Fin 3, entryMap σ ε (![-1, 1, -1] k) = ![-1, 1, -1] k := by
    intro k
    fin_cases k <;> simp [entryMap_one, entryMap_neg_one]
  have hπ0 : π 0 = 0 := by
    obtain ⟨h', he⟩ := hform 1 (-1) (-1) (by ring)
    have hfix : proj 3 F (diagSL (1 : F) (-1) (-1) (by ring)) = α (proj 3 F (diagSL (1 : F) (-1) (-1) (by ring))) :=
      hα1.symm
    rw [he] at hfix
    have hrr : ∀ k : Fin 3, (![1, -1, -1] k : F) ^ r = 1 := by
      intro k; fin_cases k <;> simp [hneg]
    have hent := (proj_diagSL_inj hr3 (r := r) _ _ (by rw [hentry1]; exact hrr (π 0))
      (by rw [hentry1]; exact hrr (π 1)) (one_pow r) hneg hfix.symm).1
    rw [hentry1] at hent
    by_contra hne
    have : (![1, -1, -1] : Fin 3 → F) (π 0) = -1 := by
      generalize π 0 = j at hne ⊢
      fin_cases j <;> simp at hne ⊢
    rw [this] at hent
    apply h2
    linear_combination -hent
  have hπ1 : π 1 = 1 := by
    obtain ⟨h', he⟩ := hform (-1) 1 (-1) (by ring)
    have hfix : proj 3 F (diagSL (-1 : F) 1 (-1) (by ring)) = α (proj 3 F (diagSL (-1 : F) 1 (-1) (by ring))) :=
      hα2.symm
    rw [he] at hfix
    have hrr : ∀ k : Fin 3, (![-1, 1, -1] k : F) ^ r = 1 := by
      intro k; fin_cases k <;> simp [hneg]
    have hent := (proj_diagSL_inj hr3 (r := r) _ _ (by rw [hentry2]; exact hrr (π 0))
      (by rw [hentry2]; exact hrr (π 1)) hneg (one_pow r) hfix.symm).2.1
    rw [hentry2] at hent
    by_contra hne
    have : (![-1, 1, -1] : Fin 3 → F) (π 1) = -1 := by
      generalize π 1 = j at hne ⊢
      fin_cases j <;> simp at hne ⊢
    rw [this] at hent
    apply h2
    linear_combination -hent
  have hπ2 : π 2 = 2 := by
    have hn0 : π 2 ≠ 0 := fun h => by
      have := π.injective (h.trans hπ0.symm)
      simp at this
    have hn1 : π 2 ≠ 1 := fun h => by
      have := π.injective (h.trans hπ1.symm)
      simp at this
    generalize π 2 = j at hn0 hn1 ⊢
    fin_cases j <;> simp at hn0 hn1 ⊢
  have hπ : π = 1 := by
    refine Equiv.ext (fun k => ?_)
    fin_cases k
    · simpa using hπ0
    · simpa using hπ1
    · simpa using hπ2
  subst hπ
  refine ⟨σ, ε, hε, fun a b c h => ?_⟩
  obtain ⟨h', he⟩ := hform a b c h
  have h'' : entryMap σ ε a * entryMap σ ε b * entryMap σ ε c = 1 := by simpa using h'
  refine ⟨h'', ?_⟩
  rw [he]
  exact proj_diagSL_congr (by simp) (by simp) (by simp)

end Formula

end CFSG.GH74.KGroups.L3Eps
