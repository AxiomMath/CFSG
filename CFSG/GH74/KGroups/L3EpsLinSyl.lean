module

public import CFSG.GH74.KGroups.L3EpsOrder
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Setup

variable {F : Type} [Field F]

@[expose] def swapSL : SL(3, F) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

theorem coe_swapSL :
    ((swapSL : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, 0, 0; 0, 0, -1] := rfl

theorem swapSL_mul_self : (swapSL : SL(3, F)) * swapSL = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_swapSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem swapSL_sq : (swapSL : SL(3, F)) ^ 2 = 1 := by rw [sq]; exact swapSL_mul_self

theorem swapSL_inv : (swapSL : SL(3, F))⁻¹ = swapSL := inv_eq_of_mul_eq_one_right swapSL_mul_self

theorem swapSL_mul_diagSL (a b c : F) (h : a * b * c = 1) (h' : b * a * c = 1) :
    (swapSL : SL(3, F)) * diagSL a b c h = diagSL b a c h' * swapSL := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_swapSL, coe_diagSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

end Setup

section Roots

variable {F : Type} [Field F]

abbrev mu (r : ℕ) (F : Type) [Field F] : Subgroup Fˣ := (powMonoidHom r : Fˣ →* Fˣ).ker

theorem mem_mu {r : ℕ} {x : Fˣ} : x ∈ mu r F ↔ x ^ r = 1 := by
  rw [MonoidHom.mem_ker]
  rfl

@[expose] def torus : Fˣ × Fˣ →* SL(3, F) where
  toFun xy := diagSL (xy.1 : F) (xy.2 : F) (((xy.1 * xy.2)⁻¹ : Fˣ) : F) (by
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  map_one' := by
    rw [← diagSL_one (K := F) (by ring)]
    exact diagSL_congr (by simp) (by simp) (by simp)
  map_mul' xy xy' := by
    rw [diagSL_mul]
    refine diagSL_congr (by simp) (by simp) ?_
    simp
    ring

theorem coe_torus (x y : Fˣ) :
    ((torus (x, y) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(x : F), (y : F), (((x * y)⁻¹ : Fˣ) : F)] := rfl

theorem torus_injective : Function.Injective (torus : Fˣ × Fˣ →* SL(3, F)) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h' := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_torus] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp at h0 h1
  rw [Units.ext h0, Units.ext h1]

end Roots

section TorusMu

variable {F : Type} [Field F]

@[expose] def torusMu (r : ℕ) : mu r F × mu r F →* SL(3, F) :=
  (torus : Fˣ × Fˣ →* SL(3, F)).comp ((mu r F).subtype.prodMap (mu r F).subtype)

theorem torusMu_injective (r : ℕ) : Function.Injective (torusMu r : mu r F × mu r F →* SL(3, F)) := by
  intro a b h
  have := torus_injective (F := F) h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst this)) (Subtype.ext (congrArg Prod.snd this))

@[expose] def thetaMu (r : ℕ) : mu r F × mu r F →* projectiveSL 3 F :=
  (proj 3 F).comp (torusMu r)

theorem thetaMu_injective {r : ℕ} (hr3 : ¬ 3 ∣ r) :
    Function.Injective (thetaMu r : mu r F × mu r F →* projectiveSL 3 F) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, y⟩ h
  have h1 : torusMu r (x, y) ∈ scalars 3 F := proj_eq_one_iff.1 h
  obtain ⟨c, hc3, hc⟩ := h1
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [torusMu, coe_torus, Matrix.scalar_apply] at h00 h11
  have hx : (x : Fˣ) = c := Units.ext h00
  have hy : (y : Fˣ) = c := Units.ext h11
  have hcr : c ^ r = 1 := by rw [← hx]; exact mem_mu.1 x.2
  have hgcd : Nat.gcd 3 r = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hr3
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc3, hcr⟩
    rwa [hgcd, pow_one] at this
  rw [Prod.mk_eq_one]
  exact ⟨Subtype.ext (hx.trans hc1), Subtype.ext (hy.trans hc1)⟩

end TorusMu

section JP

variable {F : Type} [Field F]

@[expose] def Jexp (r : ℕ) : Subgroup (projectiveSL 3 F) := (thetaMu r : mu r F × mu r F →* _).range

@[expose] def tauBar : projectiveSL 3 F := proj 3 F swapSL

theorem tauBar_mul_self : (tauBar : projectiveSL 3 F) * tauBar = 1 := by
  rw [tauBar, ← map_mul, swapSL_mul_self, map_one]

theorem tauBar_inv : (tauBar : projectiveSL 3 F)⁻¹ = tauBar :=
  inv_eq_of_mul_eq_one_right tauBar_mul_self

theorem tauBar_sq : (tauBar : projectiveSL 3 F) ^ 2 = 1 := by rw [sq]; exact tauBar_mul_self

theorem swapSL_mul_torus (x y : Fˣ) :
    (swapSL : SL(3, F)) * torus (x, y) = torus (y, x) * swapSL := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_swapSL, coe_torus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]

theorem tauBar_mul_theta (r : ℕ) (x y : mu r F) :
    (tauBar : projectiveSL 3 F) * thetaMu r (x, y) = thetaMu r (y, x) * tauBar := by
  have h : (swapSL : SL(3, F)) * torusMu r (x, y) = torusMu r (y, x) * swapSL :=
    swapSL_mul_torus (x : Fˣ) (y : Fˣ)
  show proj 3 F swapSL * proj 3 F (torusMu r (x, y)) = proj 3 F (torusMu r (y, x)) * proj 3 F swapSL
  rw [← map_mul, ← map_mul, h]

theorem tauBar_conj_theta (r : ℕ) (x y : mu r F) :
    (tauBar : projectiveSL 3 F) * thetaMu r (x, y) * tauBar⁻¹ = thetaMu r (y, x) := by
  rw [tauBar_mul_theta, mul_assoc, mul_inv_cancel, mul_one]

theorem tauBar_conj_mem_Jexp (r : ℕ) {j : projectiveSL 3 F} (hj : j ∈ Jexp (F := F) r) :
    (tauBar : projectiveSL 3 F) * j * tauBar⁻¹ ∈ Jexp r := by
  obtain ⟨⟨x, y⟩, rfl⟩ := hj
  rw [tauBar_conj_theta]
  exact ⟨(y, x), rfl⟩

@[expose] def Pexp (r : ℕ) : Subgroup (projectiveSL 3 F) where
  carrier := {x | ∃ j ∈ Jexp (F := F) r, x = j ∨ x = j * tauBar}
  one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
  mul_mem' := by
    rintro a b ⟨j₁, hj₁, ha⟩ ⟨j₂, hj₂, hb⟩
    have hc := tauBar_conj_mem_Jexp r hj₂
    have h := tauBar_mul_self (F := F)
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · exact ⟨j₁ * j₂, mul_mem hj₁ hj₂, Or.inl rfl⟩
    · exact ⟨j₁ * j₂, mul_mem hj₁ hj₂, Or.inr (by rw [mul_assoc])⟩
    · refine ⟨j₁ * (tauBar * j₂ * tauBar⁻¹), mul_mem hj₁ hc, Or.inr ?_⟩
      group
    · refine ⟨j₁ * (tauBar * j₂ * tauBar⁻¹), mul_mem hj₁ hc, Or.inl ?_⟩
      calc j₁ * tauBar * (j₂ * tauBar) = j₁ * (tauBar * j₂ * tauBar⁻¹) * (tauBar * tauBar) := by group
        _ = j₁ * (tauBar * j₂ * tauBar⁻¹) := by rw [h, mul_one]
  inv_mem' := by
    rintro a ⟨j, hj, ha⟩
    rcases ha with ha | ha <;> rw [ha]
    · exact ⟨j⁻¹, inv_mem hj, Or.inl rfl⟩
    · refine ⟨tauBar * j⁻¹ * tauBar⁻¹, tauBar_conj_mem_Jexp r (inv_mem hj), Or.inr ?_⟩
      calc (j * tauBar)⁻¹ = tauBar⁻¹ * j⁻¹ := _root_.mul_inv_rev _ _
        _ = tauBar * j⁻¹ := by rw [tauBar_inv]
        _ = tauBar * j⁻¹ * tauBar⁻¹ * tauBar := by group

end JP

section Props

variable {F : Type} [Field F]

theorem Jexp_comm (r : ℕ) : ∀ x ∈ Jexp (F := F) r, ∀ y ∈ Jexp (F := F) r, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem Jexp_pow (r : ℕ) : ∀ x ∈ Jexp (F := F) r, x ^ r = 1 := by
  rintro _ ⟨⟨x, y⟩, rfl⟩
  rw [← map_pow]
  have : ((x, y) : mu r F × mu r F) ^ r = 1 := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using mem_mu.1 x.2
    · simpa using mem_mu.1 y.2
  rw [this, map_one]

theorem card_Jexp [Finite F] {r : ℕ} (hr3 : ¬ 3 ∣ r) (hmu : Nat.card (mu r F) = r) :
    Nat.card (Jexp (F := F) r) = r ^ 2 := by
  have h := Nat.card_congr (MonoidHom.ofInjective (thetaMu_injective (F := F) hr3)).toEquiv
  rw [Jexp, ← h, Nat.card_prod, hmu, sq]

theorem tauBar_not_mem_Jexp {r : ℕ} : (tauBar : projectiveSL 3 F) ∉ Jexp (F := F) r := by
  rintro ⟨⟨x, y⟩, h⟩
  have h' : proj 3 F (torusMu r (x, y)) = proj 3 F swapSL := h
  rw [eq_comm, proj_eq_proj_iff] at h'
  obtain ⟨c, hc3, hc⟩ := h'
  have h00 := congrFun (congrFun hc 0) 0
  rw [swapSL_inv] at h00
  simp [torusMu, coe_torus, coe_swapSL, Matrix.mul_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply] at h00
  exact c.ne_zero h00.symm

theorem tauBar_mem_Pexp (r : ℕ) : (tauBar : projectiveSL 3 F) ∈ Pexp r :=
  ⟨1, one_mem _, Or.inr (by rw [one_mul])⟩

theorem Jexp_le_Pexp (r : ℕ) : Jexp (F := F) r ≤ Pexp r := fun j hj => ⟨j, hj, Or.inl rfl⟩

theorem card_Pexp [Finite F] (r : ℕ) : Nat.card (Pexp (F := F) r) = 2 * Nat.card (Jexp (F := F) r) := by
  let g : Jexp (F := F) r × Bool → Pexp (F := F) r := fun jb =>
    ⟨if jb.2 then (jb.1 : projectiveSL 3 F) * tauBar else (jb.1 : projectiveSL 3 F),
      ⟨jb.1, jb.1.2, by cases jb.2 <;> simp⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨j, b⟩ ⟨j', b'⟩ h
      have h' : (if b then (j : projectiveSL 3 F) * tauBar else (j : projectiveSL 3 F)) =
          if b' then (j' : projectiveSL 3 F) * tauBar else (j' : projectiveSL 3 F) :=
        congrArg Subtype.val h
      cases b <;> cases b'
      · simp at h'
        exact Prod.ext h' rfl
      · exfalso
        simp at h'
        apply tauBar_not_mem_Jexp (F := F) (r := r)
        have : (tauBar : projectiveSL 3 F) = (j' : projectiveSL 3 F)⁻¹ * j := by
          rw [h']; group
        rw [this]
        exact mul_mem (inv_mem j'.2) j.2
      · exfalso
        simp at h'
        apply tauBar_not_mem_Jexp (F := F) (r := r)
        have : (tauBar : projectiveSL 3 F) = (j : projectiveSL 3 F)⁻¹ * j' := by
          rw [← h']; group
        rw [this]
        exact mul_mem (inv_mem j.2) j'.2
      · simp at h'
        exact Prod.ext h' rfl
    · rintro ⟨x, j, hj, hx | hx⟩
      · exact ⟨(⟨j, hj⟩, false), Subtype.ext (by simp [g, hx])⟩
      · exact ⟨(⟨j, hj⟩, true), Subtype.ext (by simp [g, hx])⟩
  rw [← Nat.card_congr (Equiv.ofBijective g hg), Nat.card_prod, Nat.card_eq_fintype_card (α := Bool)]
  simp [mul_comm]

end Props

section Max

variable {F : Type} [Field F] [Finite F]

theorem card_mu {r : ℕ} (hr : r ∣ Nat.card F - 1) : Nat.card (mu r F) = r := by
  rw [mu, IsCyclic.card_powMonoidHom_ker, Nat.card_units]
  exact Nat.gcd_eq_right hr

theorem Pexp_sylow {r : ℕ} (hF2 : Nat.card F % 2 = 1) (hq4 : Nat.card F % 4 = 1)
    (hr : r = ordProj[2] (Nat.card F - 1)) :
    IsPGroup 2 (Pexp (F := F) r) ∧
      ∀ T : Subgroup (projectiveSL 3 F), IsPGroup 2 T → Pexp r ≤ T → T ≤ Pexp r := by
  have hrdvd : r ∣ Nat.card F - 1 := hr ▸ Nat.ordProj_dvd _ 2
  have hr3 : ¬ 3 ∣ r := by
    intro h3
    rw [hr] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hcard : Nat.card (Pexp (F := F) r) = ordProj[2] (Nat.card (projectiveSL 3 F)) := by
    rw [card_Pexp, card_Jexp hr3 (card_mu hrdvd), projectiveSL_card_two_part hF2,
      CFSG.LieType.Steinberg.ordProj_two_add_one_of_mod_four_eq_one hq4, ← hr]
    ring
  exact ⟨IsPGroup.of_card hcard, isMax_of_card hcard⟩

end Max

end CFSG.GH74.KGroups.L3Eps
