module

public import CFSG.LocalAnalysis.SteinbergBNMiyamotoPrimaryLocalApplication

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Coordinates

@[simp] theorem miyamotoX_one_zero (a b c d : K) : miyamotoX h a b c d 1 0 = a := rfl

@[simp] theorem miyamotoX_two_one (a b c d : K) : miyamotoX h a b c d 2 1 = b := rfl

@[simp] theorem miyamotoX_two_zero (a b c d : K) : miyamotoX h a b c d 2 0 = c := rfl

@[simp] theorem miyamotoX_three_zero (a b c d : K) : miyamotoX h a b c d 3 0 = d := rfl

theorem miyamotoX_inj {a b c d a' b' c' d' : K} :
    miyamotoX h a b c d = miyamotoX h a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro e
    exact ⟨by simpa using congrFun (congrFun e 1) 0, by simpa using congrFun (congrFun e 2) 1,
      by simpa using congrFun (congrFun e 2) 0, by simpa using congrFun (congrFun e 3) 0⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem det_miyamotoX (a b c d : K) : (miyamotoX h a b c d).det = 1 := by
  simp [miyamotoX, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

@[expose] def miyamotoXGL (a b c d : K) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (miyamotoX h a b c d)
    (by rw [det_miyamotoX]; exact one_ne_zero)

@[simp] theorem coe_miyamotoXGL (a b c d : K) :
    ((miyamotoXGL h a b c d : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = miyamotoX h a b c d :=
  rfl

theorem eq_miyamotoXGL {g : GL (Fin 4) K} {a b c d : K}
    (hg : (g : Matrix (Fin 4) (Fin 4) K) = miyamotoX h a b c d) : g = miyamotoXGL h a b c d :=
  Units.ext hg

theorem miyamotoXGL_inj {a b c d a' b' c' d' : K} :
    miyamotoXGL h a b c d = miyamotoXGL h a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  rw [← miyamotoX_inj h, ← coe_miyamotoXGL, ← coe_miyamotoXGL, Units.val_inj]

theorem miyamotoXGL_zero : miyamotoXGL h (0 : K) 0 0 0 = 1 :=
  Units.ext (miyamotoX_zero h)

variable [CharP K 2]

theorem miyamotoXGL_mul {a b c d a' b' c' d' : K} (hb : h.bar b = b) :
    miyamotoXGL h a b c d * miyamotoXGL h a' b' c' d' =
      miyamotoXGL h (a + a') (b + b') (c + c' + b * a')
        (d + d' + (h.bar c + h.bar a * b) * a' + h.bar a * c') :=
  Units.ext (miyamotoX_mul h hb)

theorem miyamotoXGL_inv {a b c d : K} (hb : h.bar b = b) :
    (miyamotoXGL h a b c d)⁻¹ = miyamotoXGL h a b (c + b * a) (d + a * h.bar c + h.bar a * c) := by
  rw [inv_eq_iff_mul_eq_one, miyamotoXGL_mul h hb, ← miyamotoXGL_zero h, miyamotoXGL_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem miyamotoXGL_mul_eq {a b c d a' b' c' d' a'' b'' c'' d'' : K} (hb : h.bar b = b)
    (ha'' : a'' = a + a') (hb'' : b'' = b + b') (hc'' : c'' = c + c' + b * a')
    (hd'' : d'' = d + d' + (h.bar c + h.bar a * b) * a' + h.bar a * c') :
    miyamotoXGL h a b c d * miyamotoXGL h a' b' c' d' = miyamotoXGL h a'' b'' c'' d'' := by
  rw [miyamotoXGL_mul h hb, ha'', hb'', hc'', hd'']

theorem miyamotoXGL_commutator {a b c d a' b' c' d' : K} (hb : h.bar b = b)
    (hb' : h.bar b' = b') :
    ⁅miyamotoXGL h a b c d, miyamotoXGL h a' b' c' d'⁆ =
      miyamotoXGL h 0 0 (b * a' + b' * a)
        (h.bar a * c' + a * h.bar c' + h.bar a' * c + a' * h.bar c +
          (b + b') * (h.bar a * a' + a * h.bar a') + b' * (a * h.bar a) + b * (a' * h.bar a')) := by
  have h1 : h.bar (b + b') = b + b' := by rw [map_add, hb, hb']
  have h2 : h.bar (b + b' + b) = b + b' + b := by rw [map_add, h1, hb]
  rw [commutatorElement_def, miyamotoXGL_inv h hb, miyamotoXGL_inv h hb', miyamotoXGL_mul h hb,
    miyamotoXGL_mul h h1, miyamotoXGL_mul h h2, miyamotoXGL_inj]
  have hbb := h.bar_bar
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem miyamotoXGL_conj {a b c d a' b' c' d' : K} (hb : h.bar b = b) (hb' : h.bar b' = b') :
    (miyamotoXGL h a b c d)⁻¹ * miyamotoXGL h a' b' c' d' * miyamotoXGL h a b c d =
      miyamotoXGL h a' b' (c' + a * b' + a' * b)
        (d' + h.bar a * c' + a * h.bar c' + h.bar a' * c + a' * h.bar c +
          (h.bar a + h.bar a') * a * b') := by
  have h1 : h.bar (b + b') = b + b' := by rw [map_add, hb, hb']
  rw [miyamotoXGL_inv h hb, miyamotoXGL_mul h hb, miyamotoXGL_mul h h1, miyamotoXGL_inj]
  have hbb := h.bar_bar
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem miyamotoXGL_mul_self {a b c d : K} (hb : h.bar b = b) :
    miyamotoXGL h a b c d * miyamotoXGL h a b c d =
      miyamotoXGL h 0 0 (a * b) (a * h.bar a * b + h.bar a * c + a * h.bar c) := by
  rw [miyamotoXGL_mul h hb, miyamotoXGL_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem miyamotoXGL_eq_mul_root {a b c d : K} (hb : h.bar b = b) :
    miyamotoXGL h a b c d = miyamotoXGL h a 0 0 0 * miyamotoXGL h 0 b 0 0 *
      miyamotoXGL h 0 0 c 0 * miyamotoXGL h 0 0 0 (d + h.bar a * c) := by
  rw [miyamotoXGL_mul h (map_zero h.bar), miyamotoXGL_mul h (by simpa using hb),
    miyamotoXGL_mul h (by simpa using hb), miyamotoXGL_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

end Coordinates

section Subgroups

abbrev miyamotoP : Subgroup (GL (Fin 4) K) := miyamotoUnipotent h false false

abbrev miyamotoA1 : Subgroup (GL (Fin 4) K) := miyamotoUnipotent h true false

abbrev miyamotoA2 : Subgroup (GL (Fin 4) K) := miyamotoUnipotent h false true

abbrev miyamotoZ2 : Subgroup (GL (Fin 4) K) := miyamotoUnipotent h true true

theorem mem_miyamotoUnipotent {za zb : Bool} {g : GL (Fin 4) K} :
    g ∈ miyamotoUnipotent h za zb ↔ ∃ a b c d : K, (za = true → a = 0) ∧ (zb = true → b = 0) ∧
      h.bar b = b ∧ d + h.bar d + a * h.bar c + h.bar a * c = 0 ∧ g = miyamotoXGL h a b c d := by
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hb', hd, hg⟩
    exact ⟨a, b, c, d, ha, hb, hb', hd, eq_miyamotoXGL h hg⟩
  · rintro ⟨a, b, c, d, ha, hb, hb', hd, rfl⟩
    exact ⟨a, b, c, d, ha, hb, hb', hd, rfl⟩

theorem miyamotoXGL_mem_miyamotoUnipotent {za zb : Bool} {a b c d : K} :
    miyamotoXGL h a b c d ∈ miyamotoUnipotent h za zb ↔ (za = true → a = 0) ∧
      (zb = true → b = 0) ∧ h.bar b = b ∧ d + h.bar d + a * h.bar c + h.bar a * c = 0 := by
  rw [mem_miyamotoUnipotent]
  constructor
  · rintro ⟨a', b', c', d', ha, hb, hb', hd, e⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (miyamotoXGL_inj h).1 e
    exact ⟨ha, hb, hb', hd⟩
  · rintro ⟨ha, hb, hb', hd⟩
    exact ⟨a, b, c, d, ha, hb, hb', hd, rfl⟩

theorem miyamotoXGL_mem_P {a b c d : K} : miyamotoXGL h a b c d ∈ miyamotoP h ↔
    h.bar b = b ∧ d + h.bar d + a * h.bar c + h.bar a * c = 0 := by
  rw [miyamotoXGL_mem_miyamotoUnipotent]
  simp

theorem miyamotoXGL_mem_A2 {a b c d : K} : miyamotoXGL h a b c d ∈ miyamotoA2 h ↔
    b = 0 ∧ d + h.bar d + a * h.bar c + h.bar a * c = 0 := by
  rw [miyamotoXGL_mem_miyamotoUnipotent]
  constructor
  · rintro ⟨-, hb, -, hd⟩
    exact ⟨hb rfl, hd⟩
  · rintro ⟨rfl, hd⟩
    exact ⟨fun e => absurd e Bool.false_ne_true, fun _ => rfl, map_zero _, hd⟩

theorem mem_P {g : GL (Fin 4) K} : g ∈ miyamotoP h ↔ ∃ a b c d : K, h.bar b = b ∧
    d + h.bar d + a * h.bar c + h.bar a * c = 0 ∧ g = miyamotoXGL h a b c d := by
  rw [mem_miyamotoUnipotent]
  simp

theorem mem_A2 {g : GL (Fin 4) K} : g ∈ miyamotoA2 h ↔ ∃ a c d : K,
    d + h.bar d + a * h.bar c + h.bar a * c = 0 ∧ g = miyamotoXGL h a 0 c d := by
  rw [mem_miyamotoUnipotent]
  constructor
  · rintro ⟨a, b, c, d, -, hb, -, hd, rfl⟩
    obtain rfl := hb rfl
    exact ⟨a, c, d, hd, rfl⟩
  · rintro ⟨a, c, d, hd, rfl⟩
    exact ⟨a, 0, c, d, fun e => absurd e Bool.false_ne_true, fun _ => rfl, map_zero _, hd, rfl⟩

variable [CharP K 2]

theorem add_bar_eq_zero_iff {d : K} : d + h.bar d = 0 ↔ h.bar d = d := by
  constructor
  · intro hd
    linear_combination hd - d * CharTwo.two_eq_zero (R := K)
  · intro hd
    rw [hd, CharTwo.add_self_eq_zero]

theorem miyamotoXGL_mem_A1 {a b c d : K} : miyamotoXGL h a b c d ∈ miyamotoA1 h ↔
    a = 0 ∧ h.bar b = b ∧ h.bar d = d := by
  rw [miyamotoXGL_mem_miyamotoUnipotent]
  constructor
  · rintro ⟨ha, -, hb, hd⟩
    obtain rfl := ha rfl
    refine ⟨rfl, hb, (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩
  · rintro ⟨rfl, hb, hd⟩
    exact ⟨fun _ => rfl, fun e => absurd e Bool.false_ne_true, hb,
      by simpa using (add_bar_eq_zero_iff h).2 hd⟩

theorem miyamotoXGL_mem_Z2 {a b c d : K} : miyamotoXGL h a b c d ∈ miyamotoZ2 h ↔
    a = 0 ∧ b = 0 ∧ h.bar d = d := by
  rw [miyamotoXGL_mem_miyamotoUnipotent]
  constructor
  · rintro ⟨ha, hb, -, hd⟩
    obtain rfl := ha rfl
    obtain rfl := hb rfl
    exact ⟨rfl, rfl, (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩
  · rintro ⟨rfl, rfl, hd⟩
    exact ⟨fun _ => rfl, fun _ => rfl, map_zero _, by simpa using (add_bar_eq_zero_iff h).2 hd⟩

theorem mem_A1 {g : GL (Fin 4) K} : g ∈ miyamotoA1 h ↔ ∃ b c d : K, h.bar b = b ∧
    h.bar d = d ∧ g = miyamotoXGL h 0 b c d := by
  constructor
  · intro hg
    obtain ⟨a, b, c, d, -, -, -, -, rfl⟩ := (mem_miyamotoUnipotent h).1 hg
    obtain ⟨rfl, hb, hd⟩ := (miyamotoXGL_mem_A1 h).1 hg
    exact ⟨b, c, d, hb, hd, rfl⟩
  · rintro ⟨b, c, d, hb, hd, rfl⟩
    exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩

theorem mem_Z2 {g : GL (Fin 4) K} : g ∈ miyamotoZ2 h ↔ ∃ c d : K, h.bar d = d ∧
    g = miyamotoXGL h 0 0 c d := by
  constructor
  · intro hg
    obtain ⟨a, b, c, d, -, -, -, -, rfl⟩ := (mem_miyamotoUnipotent h).1 hg
    obtain ⟨rfl, rfl, hd⟩ := (miyamotoXGL_mem_Z2 h).1 hg
    exact ⟨c, d, hd, rfl⟩
  · rintro ⟨c, d, hd, rfl⟩
    exact (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, hd⟩

omit [CharP K 2] in
theorem miyamotoA1_le_P : miyamotoA1 h ≤ miyamotoP h := by
  intro g hg
  obtain ⟨a, b, c, d, -, -, hb, hd, rfl⟩ := (mem_miyamotoUnipotent h).1 hg
  exact (miyamotoXGL_mem_P h).2 ⟨hb, hd⟩

omit [CharP K 2] in
theorem miyamotoA2_le_P : miyamotoA2 h ≤ miyamotoP h := by
  intro g hg
  obtain ⟨a, b, c, d, -, -, hb, hd, rfl⟩ := (mem_miyamotoUnipotent h).1 hg
  exact (miyamotoXGL_mem_P h).2 ⟨hb, hd⟩

theorem miyamotoZ2_le_A1 : miyamotoZ2 h ≤ miyamotoA1 h := by
  intro g hg
  obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hg
  exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hd⟩

theorem miyamotoZ2_le_A2 : miyamotoZ2 h ≤ miyamotoA2 h := by
  intro g hg
  obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hg
  exact (miyamotoXGL_mem_A2 h).2 ⟨rfl, by simpa using (add_bar_eq_zero_iff h).2 hd⟩

theorem miyamotoA1_inf_miyamotoA2 : miyamotoA1 h ⊓ miyamotoA2 h = miyamotoZ2 h := by
  refine le_antisymm (fun g ⟨h1, h2⟩ => ?_) (le_inf (miyamotoZ2_le_A1 h) (miyamotoZ2_le_A2 h))
  obtain ⟨b, c, d, -, hd, rfl⟩ := (mem_A1 h).1 h1
  obtain ⟨rfl, -⟩ := (miyamotoXGL_mem_A2 h).1 h2
  exact (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, hd⟩

@[expose] def miyamotoZ (h : UnitaryFieldData 2 f K) : Subgroup (GL (Fin 4) K) where
  carrier := {g | ∃ d : K, h.bar d = d ∧ g = miyamotoXGL h 0 0 0 d}
  mul_mem' := by
    have : CharP K 2 := h.charP
    rintro _ _ ⟨d, hd, rfl⟩ ⟨d', hd', rfl⟩
    exact ⟨d + d', by rw [map_add, hd, hd'], miyamotoXGL_mul_eq h (map_zero _) (by ring)
      (by ring) (by ring) (by simp)⟩
  one_mem' := ⟨0, map_zero _, (miyamotoXGL_zero h).symm⟩
  inv_mem' := by
    have : CharP K 2 := h.charP
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨d, hd, by rw [miyamotoXGL_inv h (map_zero _)]; simp⟩

omit [CharP K 2] in
theorem mem_Z {g : GL (Fin 4) K} : g ∈ miyamotoZ h ↔ ∃ d : K, h.bar d = d ∧
    g = miyamotoXGL h 0 0 0 d :=
  Iff.rfl

omit [CharP K 2] in
theorem miyamotoXGL_mem_Z {a b c d : K} : miyamotoXGL h a b c d ∈ miyamotoZ h ↔
    a = 0 ∧ b = 0 ∧ c = 0 ∧ h.bar d = d := by
  constructor
  · rintro ⟨d', hd', e⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (miyamotoXGL_inj h).1 e
    exact ⟨rfl, rfl, rfl, hd'⟩
  · rintro ⟨rfl, rfl, rfl, hd⟩
    exact ⟨d, hd, rfl⟩

theorem miyamotoZ_le_Z2 : miyamotoZ h ≤ miyamotoZ2 h := by
  rintro _ ⟨d, hd, rfl⟩
  exact (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, hd⟩

theorem miyamotoZ_le_P : miyamotoZ h ≤ miyamotoP h :=
  ((miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A1 h)).trans (miyamotoA1_le_P h)

@[expose] def miyamotoRootA (h : UnitaryFieldData 2 f K) : Subgroup (GL (Fin 4) K) where
  carrier := {g | ∃ a : K, g = miyamotoXGL h a 0 0 0}
  mul_mem' := by
    have : CharP K 2 := h.charP
    rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
    exact ⟨a + a', miyamotoXGL_mul_eq h (map_zero _) rfl (by ring) (by ring) (by simp)⟩
  one_mem' := ⟨0, (miyamotoXGL_zero h).symm⟩
  inv_mem' := by
    have : CharP K 2 := h.charP
    rintro _ ⟨a, rfl⟩
    exact ⟨a, by rw [miyamotoXGL_inv h (map_zero _)]; simp⟩

@[expose] def miyamotoRootB (h : UnitaryFieldData 2 f K) : Subgroup (GL (Fin 4) K) where
  carrier := {g | ∃ b : K, h.bar b = b ∧ g = miyamotoXGL h 0 b 0 0}
  mul_mem' := by
    have : CharP K 2 := h.charP
    rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
    exact ⟨b + b', by rw [map_add, hb, hb'], miyamotoXGL_mul_eq h hb (by ring) rfl (by simp)
      (by simp)⟩
  one_mem' := ⟨0, map_zero _, (miyamotoXGL_zero h).symm⟩
  inv_mem' := by
    have : CharP K 2 := h.charP
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [miyamotoXGL_inv h hb]; simp⟩

@[expose] def miyamotoRootC (h : UnitaryFieldData 2 f K) : Subgroup (GL (Fin 4) K) where
  carrier := {g | ∃ c : K, g = miyamotoXGL h 0 0 c 0}
  mul_mem' := by
    have : CharP K 2 := h.charP
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', miyamotoXGL_mul_eq h (map_zero _) (by ring) (by ring) (by ring) (by simp)⟩
  one_mem' := ⟨0, (miyamotoXGL_zero h).symm⟩
  inv_mem' := by
    have : CharP K 2 := h.charP
    rintro _ ⟨c, rfl⟩
    exact ⟨c, by rw [miyamotoXGL_inv h (map_zero _)]; simp⟩

omit [CharP K 2] in
theorem miyamotoRootA_le_A2 : miyamotoRootA h ≤ miyamotoA2 h := by
  rintro _ ⟨a, rfl⟩
  exact (miyamotoXGL_mem_A2 h).2 ⟨rfl, by simp⟩

theorem miyamotoRootB_le_A1 : miyamotoRootB h ≤ miyamotoA1 h := by
  rintro _ ⟨b, hb, rfl⟩
  exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, map_zero _⟩

theorem miyamotoRootC_le_Z2 : miyamotoRootC h ≤ miyamotoZ2 h := by
  rintro _ ⟨c, rfl⟩
  exact (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, map_zero _⟩

theorem mem_P_iff_root {g : GL (Fin 4) K} : g ∈ miyamotoP h ↔ ∃ a b c e : K, h.bar b = b ∧
    h.bar e = e ∧ g = miyamotoXGL h a 0 0 0 * miyamotoXGL h 0 b 0 0 * miyamotoXGL h 0 0 c 0 *
      miyamotoXGL h 0 0 0 e := by
  constructor
  · intro hg
    obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
    refine ⟨a, b, c, d + h.bar a * c, hb, ?_, miyamotoXGL_eq_mul_root h hb⟩
    have hbb := h.bar_bar
    grind
  · rintro ⟨a, b, c, e, hb, he, rfl⟩
    have key : miyamotoXGL h a b c (e + h.bar a * c) = miyamotoXGL h a 0 0 0 *
        miyamotoXGL h 0 b 0 0 * miyamotoXGL h 0 0 c 0 * miyamotoXGL h 0 0 0 e := by
      rw [miyamotoXGL_eq_mul_root h hb]
      congr 2
      grind
    rw [← key, miyamotoXGL_mem_P]
    have hbb := h.bar_bar
    exact ⟨hb, by grind⟩

end Subgroups

section Torus

theorem miyamotoIHom_conj (p : Kˣ × Kˣ) (a b c d : K) :
    (miyamotoIHom h p)⁻¹ * miyamotoXGL h a b c d * miyamotoIHom h p =
      miyamotoXGL h ((p.1 : K) * (p.2 : K)⁻¹ * a) ((p.2 : K) * h.bar p.2 * b)
        ((p.1 : K) * h.bar p.2 * c) ((p.1 : K) * h.bar p.1 * d) := by
  rw [← map_inv]
  apply Units.ext
  simp only [Units.val_mul, coe_miyamotoXGL]
  change diagonal _ * miyamotoX h a b c d * diagonal _ = _
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : h.bar (p.1 : K) ≠ 0 := by simp
  have h2 : h.bar (p.2 : K) ≠ 0 := by simp
  fin_cases i <;> fin_cases j <;> simp [miyamotoX, map_mul, map_inv₀, h.bar_bar] <;> field_simp

end Torus

end CFSG.LocalAnalysis.EvenBN.U4
