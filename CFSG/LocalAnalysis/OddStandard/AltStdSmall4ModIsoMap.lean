module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModT10
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceRegularSylow
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.ReduceModChar

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.ModIso

open Subgroup Matrix ModT10 T10
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

section Coords

@[expose] def vE (p : T10) : Fin 3 → ZMod 2 := ![p.x0, p.x1, p.x2]

@[expose] def vF (p : T10) : Fin 3 → ZMod 2 := ![p.x3, p.x4, p.x5]

@[expose] def uT (p : T10) : sylowT := tripleEquiv (p.a, p.b, p.c)

theorem coe_uT (p : T10) :
    (((uT p : sylowT) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      unitri p.a p.b p.c := rfl

theorem unitri_mulVec (a b c : ZMod 2) (v : Fin 3 → ZMod 2) :
    unitri a b c *ᵥ v = ![v 0 + a * v 1 + b * v 2, v 1 + c * v 2, v 2] := by
  funext i
  fin_cases i <;> simp [unitri, mulVec, dotProduct, Fin.sum_univ_three]

theorem vE_mul (p q : T10) : vE (p * q) =
    vE p + (unitri p.a p.b p.c *ᵥ vE q + p.s • (unitri p.a p.b p.c *ᵥ vF q)) := by
  rw [unitri_mulVec, unitri_mulVec]
  funext i
  fin_cases i <;> simp [vE, vF, mul_x0, mul_x1, mul_x2] <;> ring

theorem vF_mul (p q : T10) : vF (p * q) = vF p + unitri p.a p.b p.c *ᵥ vF q := by
  rw [unitri_mulVec]
  funext i
  fin_cases i <;> simp [vF, mul_x3, mul_x4, mul_x5] <;> ring

theorem uT_mul (p q : T10) : uT (p * q) = uT p * uT q :=
  Subtype.ext (Units.ext (by
    show unitri (p * q).a (p * q).b (p * q).c = unitri p.a p.b p.c * unitri q.a q.b q.c
    rw [unitri_mul, mul_a, mul_b, mul_c]))

theorem zmod2_cases (s : ZMod 2) : s = 0 ∨ s = 1 := by
  fin_cases s
  · left; rfl
  · right; rfl

end Coords

structure MapData {G : Type} [Group G] (T : Subgroup G) (z : G)
    (c : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G) (δ : sylowT →* G) : Prop where
  mem : ∀ v w, c v w ∈ T
  add : ∀ v w v' w', c (v + v') (w + w') = c v w * c v' w'
  surj : ∀ t ∈ T, ∃ v w, c v w = t
  inj : ∀ v w, c v w = 1 → v = 0 ∧ w = 0
  conj_z : ∀ v w, z * c v w * z⁻¹ = c (v + w) w
  conj_δ : ∀ (g : sylowT) v w, δ g * c v w * (δ g)⁻¹ =
    c (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
      (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w)
  comm : ∀ g, δ g * z = z * δ g
  z_sq : z * z = 1
  inter : ∀ (s : ZMod 2) (g : sylowT), z ^ s.val * δ g ∈ T → s = 0 ∧ g = 1

section Map

variable {G : Type} [Group G] {T : Subgroup G} {z : G}
  {c : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G} {δ : sylowT →* G}

@[expose] def wPart (z : G) (δ : sylowT →* G) (p : T10) : G := z ^ p.s.val * δ (uT p)

@[expose] def psiFun (c : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G) (z : G) (δ : sylowT →* G)
    (p : T10) : G :=
  c (vE p) (vF p) * wPart z δ p

variable (h : MapData T z c δ)
include h

theorem MapData.c_zero : c 0 0 = 1 := by
  have h1 := h.add 0 0 0 0
  simp only [add_zero] at h1
  exact (mul_eq_left.1 h1.symm)

theorem MapData.zpow_val_mul (s s' : ZMod 2) : z ^ s.val * z ^ s'.val = z ^ (s + s').val := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases s' with rfl | rfl
  · show z ^ 0 * z ^ 0 = z ^ 0
    rw [pow_zero, one_mul]
  · show z ^ 0 * z ^ 1 = z ^ 1
    rw [pow_zero, one_mul]
  · show z ^ 1 * z ^ 0 = z ^ 1
    rw [pow_zero, mul_one]
  · show z ^ 1 * z ^ 1 = z ^ 0
    rw [pow_one, h.z_sq, pow_zero]

theorem MapData.zpow_mul_c (s : ZMod 2) (v w : Fin 3 → ZMod 2) :
    z ^ s.val * c v w = c (v + s • w) w * z ^ s.val := by
  rcases zmod2_cases s with rfl | rfl
  · show z ^ 0 * c v w = c (v + (0 : ZMod 2) • w) w * z ^ 0
    rw [zero_smul, add_zero, pow_zero, one_mul, mul_one]
  · show z ^ 1 * c v w = c (v + (1 : ZMod 2) • w) w * z ^ 1
    rw [one_smul, pow_one, ← h.conj_z, inv_mul_cancel_right]

theorem MapData.δ_mul_c (g : sylowT) (v w : Fin 3 → ZMod 2) :
    δ g * c v w = c (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
      (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) * δ g := by
  rw [← h.conj_δ, inv_mul_cancel_right]

theorem MapData.δ_mul_zpow (g : sylowT) (k : ℕ) : δ g * z ^ k = z ^ k * δ g :=
  (Commute.pow_right (h.comm g : Commute (δ g) z) k).eq

theorem MapData.wPart_mul_c (p : T10) (v w : Fin 3 → ZMod 2) :
    wPart z δ p * c v w =
      c (unitri p.a p.b p.c *ᵥ v + p.s • (unitri p.a p.b p.c *ᵥ w)) (unitri p.a p.b p.c *ᵥ w) *
        wPart z δ p := by
  unfold wPart
  rw [mul_assoc, h.δ_mul_c, coe_uT, ← mul_assoc, h.zpow_mul_c, mul_assoc]

theorem MapData.wPart_mul (p q : T10) : wPart z δ p * wPart z δ q = wPart z δ (p * q) := by
  unfold wPart
  rw [mul_assoc, ← mul_assoc (δ (uT p)), h.δ_mul_zpow, mul_assoc, ← mul_assoc, h.zpow_val_mul,
    ← map_mul, ← uT_mul, mul_s]

theorem MapData.psiFun_mul (p q : T10) :
    psiFun c z δ (p * q) = psiFun c z δ p * psiFun c z δ q := by
  unfold psiFun
  rw [mul_assoc, ← mul_assoc (wPart z δ p), h.wPart_mul_c, mul_assoc, h.wPart_mul, ← mul_assoc,
    ← h.add, vE_mul, vF_mul]

@[expose] def psi (h : MapData T z c δ) : T10 →* G where
  toFun := psiFun c z δ
  map_one' := by
    show c (vE 1) (vF 1) * (z ^ (1 : T10).s.val * δ (uT 1)) = 1
    have h1 : uT 1 = 1 := Subtype.ext (Units.ext unitri_zero)
    have h2 : vE 1 = 0 := by funext i; fin_cases i <;> rfl
    have h3 : vF 1 = 0 := by funext i; fin_cases i <;> rfl
    rw [h1, h2, h3, h.c_zero, map_one, one_s, one_mul, ZMod.val_zero, pow_zero, one_mul]
  map_mul' := h.psiFun_mul

theorem MapData.psi_apply (p : T10) : psi h p = c (vE p) (vF p) * (z ^ p.s.val * δ (uT p)) := rfl

theorem MapData.psi_injective : Function.Injective (psi h) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  rw [h.psi_apply] at hp
  have h1 : z ^ p.s.val * δ (uT p) ∈ T := by
    have : z ^ p.s.val * δ (uT p) = (c (vE p) (vF p))⁻¹ := eq_inv_of_mul_eq_one_right hp
    rw [this]
    exact inv_mem (h.mem _ _)
  obtain ⟨hs, hu⟩ := h.inter _ _ h1
  rw [hs, hu, map_one, mul_one, ZMod.val_zero, pow_zero, mul_one] at hp
  obtain ⟨hE, hF⟩ := h.inj _ _ hp
  have habc : (p.a, p.b, p.c) = ((0 : ZMod 2), (0 : ZMod 2), (0 : ZMod 2)) := by
    apply tripleEquiv.injective
    rw [show tripleEquiv (p.a, p.b, p.c) = uT p from rfl, hu]
    exact Subtype.ext (Units.ext unitri_zero.symm)
  simp only [Prod.mk.injEq] at habc
  obtain ⟨ha, hb, hc⟩ := habc
  have e0 := congrFun hE 0
  have e1 := congrFun hE 1
  have e2 := congrFun hE 2
  have f0 := congrFun hF 0
  have f1 := congrFun hF 1
  have f2 := congrFun hF 2
  simp only [vE, vF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at e0 e1 e2 f0 f1 f2
  ext <;> assumption

@[expose] def ofVW (v w : Fin 3 → ZMod 2) : T10 := ⟨v 0, v 1, v 2, w 0, w 1, w 2, 0, 0, 0, 0⟩

theorem MapData.psi_ofVW (v w : Fin 3 → ZMod 2) : psi h (ofVW v w) = c v w := by
  rw [h.psi_apply]
  have h1 : uT (ofVW v w) = 1 := Subtype.ext (Units.ext unitri_zero)
  have h2 : vE (ofVW v w) = v := by funext i; fin_cases i <;> rfl
  have h3 : vF (ofVW v w) = w := by funext i; fin_cases i <;> rfl
  rw [h1, h2, h3, map_one, mul_one]
  show c v w * z ^ (0 : ZMod 2).val = c v w
  rw [ZMod.val_zero, pow_zero, mul_one]

theorem MapData.map_Qm : Qm.map (psi h) = T := by
  apply le_antisymm
  · rintro _ ⟨p, ⟨hs, ha, hb, hc⟩, rfl⟩
    rw [h.psi_apply]
    have h1 : uT p = 1 := by
      apply Subtype.ext
      apply Units.ext
      show unitri p.a p.b p.c = 1
      rw [ha, hb, hc, unitri_zero]
    rw [h1, hs, map_one, mul_one, ZMod.val_zero, pow_zero, mul_one]
    exact h.mem _ _
  · intro t ht
    obtain ⟨v, w, rfl⟩ := h.surj t ht
    exact ⟨ofVW v w, ⟨rfl, rfl, rfl, rfl⟩, h.psi_ofVW v w⟩

theorem MapData.psi_tm : psi h tm = z := by
  rw [h.psi_apply]
  have h1 : uT tm = 1 := Subtype.ext (Units.ext unitri_zero)
  have h2 : vE tm = 0 := by funext i; fin_cases i <;> rfl
  have h3 : vF tm = 0 := by funext i; fin_cases i <;> rfl
  rw [h1, h2, h3, h.c_zero, map_one, mul_one, one_mul]
  show z ^ (1 : ZMod 2).val = z
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

@[expose] def ofU (g : sylowT) : T10 :=
  ⟨0, 0, 0, 0, 0, 0, 0, (tripleEquiv.symm g).1, (tripleEquiv.symm g).2.1, (tripleEquiv.symm g).2.2⟩

theorem MapData.psi_ofU (g : sylowT) : psi h (ofU g) = δ g := by
  rw [h.psi_apply]
  have h1 : uT (ofU g) = g := tripleEquiv.apply_symm_apply g
  have h2 : vE (ofU g) = 0 := by funext i; fin_cases i <;> rfl
  have h3 : vF (ofU g) = 0 := by funext i; fin_cases i <;> rfl
  rw [h1, h2, h3, h.c_zero, one_mul]
  show z ^ (0 : ZMod 2).val * δ g = δ g
  rw [ZMod.val_zero, pow_zero, one_mul]

theorem MapData.map_Mm : Mm.map (psi h) = T ⊔ δ.range := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [h.psi_apply]
    have hs : p.s = 0 := hp
    rw [hs, ZMod.val_zero, pow_zero, one_mul]
    exact mul_mem (mem_sup_left (h.mem _ _)) (mem_sup_right ⟨_, rfl⟩)
  · refine sup_le ?_ ?_
    · have h1 := Subgroup.map_mono (f := psi h) Qm_le_Mm
      rwa [h.map_Qm] at h1
    · rintro _ ⟨g, rfl⟩
      exact ⟨ofU g, rfl, h.psi_ofU g⟩

theorem MapData.range_psi : (psi h).range = T ⊔ (zpowers z ⊔ δ.range) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [h.psi_apply]
    exact mul_mem (mem_sup_left (h.mem _ _)) (mem_sup_right (mul_mem
      (mem_sup_left (pow_mem (mem_zpowers z) _)) (mem_sup_right ⟨_, rfl⟩)))
  · refine sup_le ?_ (sup_le ?_ ?_)
    · have h1 := Subgroup.map_le_range (psi h) Qm
      rwa [h.map_Qm] at h1
    · rw [zpowers_le]
      exact ⟨tm, h.psi_tm⟩
    · rintro _ ⟨g, rfl⟩
      exact ⟨ofU g, h.psi_ofU g⟩

end Map

end CFSG.OddStandard.AltStdSmall4.ModIso
