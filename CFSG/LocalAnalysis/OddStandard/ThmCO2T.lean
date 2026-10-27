module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.OddStandard.ThmC.O2.TL

open CFSG.GH74.GLS.Bg.TwoGroups Subgroup

section Defs

variable (F : Type) [Field F]

@[expose] def zT : Subgroup (UT3 F) where
  carrier := {x | x.a = 0 ∧ x.b = 0}
  mul_mem' := by
    rintro x y ⟨hxa, hxb⟩ ⟨hya, hyb⟩
    exact ⟨by rw [UT3.mul_def]; simp [hxa, hya], by rw [UT3.mul_def]; simp [hxb, hyb]⟩
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' := by
    rintro x ⟨hxa, hxb⟩
    exact ⟨by rw [UT3.inv_def]; simp [hxa], by rw [UT3.inv_def]; simp [hxb]⟩

@[expose] def aT : Subgroup (UT3 F) where
  carrier := {x | x.b = 0}
  mul_mem' := by
    rintro x y hxb hyb
    exact (by rw [UT3.mul_def]; simp [show x.b = 0 from hxb, show y.b = 0 from hyb])
  one_mem' := rfl
  inv_mem' := by
    rintro x hxb
    exact (by rw [UT3.inv_def]; simp [show x.b = 0 from hxb])

@[expose] def bT : Subgroup (UT3 F) where
  carrier := {x | x.a = 0}
  mul_mem' := by
    rintro x y hxa hya
    exact (by rw [UT3.mul_def]; simp [show x.a = 0 from hxa, show y.a = 0 from hya])
  one_mem' := rfl
  inv_mem' := by
    rintro x hxa
    exact (by rw [UT3.inv_def]; simp [show x.a = 0 from hxa])

end Defs

variable {F : Type} [Field F] [CharP F 2]

section Aux

theorem ut_two_eq : (2 : F) = 0 := CharP.cast_eq_zero F 2

omit [CharP F 2] in
@[simp] theorem ut_mul_a (x y : UT3 F) : (x * y).a = x.a + y.a := rfl
omit [CharP F 2] in
@[simp] theorem ut_mul_b (x y : UT3 F) : (x * y).b = x.b + y.b := rfl
omit [CharP F 2] in
@[simp] theorem ut_mul_c (x y : UT3 F) : (x * y).c = x.c + y.c + x.a * y.b := rfl
omit [CharP F 2] in
@[simp] theorem ut_one_a : (1 : UT3 F).a = 0 := rfl
omit [CharP F 2] in
@[simp] theorem ut_one_b : (1 : UT3 F).b = 0 := rfl
omit [CharP F 2] in
@[simp] theorem ut_one_c : (1 : UT3 F).c = 0 := rfl
omit [CharP F 2] in
@[simp] theorem ut_inv_a (x : UT3 F) : x⁻¹.a = -x.a := rfl
omit [CharP F 2] in
@[simp] theorem ut_inv_b (x : UT3 F) : x⁻¹.b = -x.b := rfl
omit [CharP F 2] in
@[simp] theorem ut_inv_c (x : UT3 F) : x⁻¹.c = -x.c + x.a * x.b := rfl

omit [CharP F 2] in
theorem ut_mem_aT {x : UT3 F} : x ∈ aT F ↔ x.b = 0 := Iff.rfl
omit [CharP F 2] in
theorem ut_mem_bT {x : UT3 F} : x ∈ bT F ↔ x.a = 0 := Iff.rfl

theorem ut_sq (x : UT3 F) : x * x = ⟨0, 0, x.a * x.b⟩ := by
  have h2 := ut_two_eq (F := F)
  ext
  · simp only [ut_mul_a]; linear_combination x.a * h2
  · simp only [ut_mul_b]; linear_combination x.b * h2
  · simp only [ut_mul_c]; linear_combination x.c * h2

omit [CharP F 2] in
theorem ut_comm (x y : UT3 F) : x * y * x⁻¹ * y⁻¹ = ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  ext
  · simp only [ut_mul_a, ut_inv_a]; ring
  · simp only [ut_mul_b, ut_inv_b]; ring
  · simp only [ut_mul_c, ut_mul_a, ut_inv_a, ut_inv_b, ut_inv_c]; ring

omit [CharP F 2] in
theorem ut_comm_iff (x y : UT3 F) : x * y = y * x ↔ x.a * y.b = y.a * x.b := by
  constructor
  · intro h
    have := congrArg UT3.c h
    simp only [ut_mul_c] at this
    linear_combination this
  · intro h
    ext
    · simp only [ut_mul_a]; ring
    · simp only [ut_mul_b]; ring
    · simp only [ut_mul_c]; linear_combination h

theorem ut_comm2 (x y : UT3 F) : x * y * x⁻¹ * y⁻¹ = ⟨0, 0, x.a * y.b + y.a * x.b⟩ := by
  rw [ut_comm]
  ext
  · rfl
  · rfl
  · show x.a * y.b - y.a * x.b = x.a * y.b + y.a * x.b
    linear_combination (-(y.a * x.b)) * (ut_two_eq (F := F))

theorem zpowers_sq_cases {G : Type*} [Group G] (z : G) (hz : z * z = 1) (y : G)
    (hy : y ∈ zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

def utEquiv (F : Type) [Field F] : UT3 F ≃ F × F × F where
  toFun x := (x.a, x.b, x.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def zTEquiv (F : Type) [Field F] : zT F ≃ F where
  toFun x := x.1.c
  invFun c := ⟨⟨0, 0, c⟩, rfl, rfl⟩
  left_inv x := by
    obtain ⟨⟨a, b, c⟩, ha, hb⟩ := x
    have ha' : a = 0 := ha
    have hb' : b = 0 := hb
    subst ha' hb'
    rfl
  right_inv _ := rfl

def aTEquiv (F : Type) [Field F] : aT F ≃ F × F where
  toFun x := (x.1.a, x.1.c)
  invFun p := ⟨⟨p.1, 0, p.2⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨a, b, c⟩, hb⟩ := x
    have hb' : b = 0 := hb
    subst hb'
    rfl
  right_inv _ := rfl

def bTEquiv (F : Type) [Field F] : bT F ≃ F × F where
  toFun x := (x.1.b, x.1.c)
  invFun p := ⟨⟨0, p.1, p.2⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨a, b, c⟩, ha⟩ := x
    have ha' : a = 0 := ha
    subst ha'
    rfl
  right_inv _ := rfl

end Aux

omit [CharP F 2] in
theorem card_UT3 [Finite F] (hF : Nat.card F = 4) : Nat.card (UT3 F) = 64 := by
  rw [Nat.card_congr (utEquiv F), Nat.card_prod, Nat.card_prod, hF]
omit [CharP F 2] in
theorem card_zT [Finite F] (hF : Nat.card F = 4) : Nat.card (zT F) = 4 := by
  rw [Nat.card_congr (zTEquiv F), hF]
omit [CharP F 2] in
theorem card_aT [Finite F] (hF : Nat.card F = 4) : Nat.card (aT F) = 16 := by
  rw [Nat.card_congr (aTEquiv F), Nat.card_prod, hF]
omit [CharP F 2] in
theorem card_bT [Finite F] (hF : Nat.card F = 4) : Nat.card (bT F) = 16 := by
  rw [Nat.card_congr (bTEquiv F), Nat.card_prod, hF]
omit [CharP F 2] in
theorem zT_le_aT : zT F ≤ aT F := fun _ hx => hx.2
omit [CharP F 2] in
theorem zT_le_bT : zT F ≤ bT F := fun _ hx => hx.1
omit [CharP F 2] in
theorem aT_ne_bT : aT F ≠ bT F := by
  intro h
  have h1 : (⟨1, 0, 0⟩ : UT3 F) ∈ aT F := rfl
  rw [h] at h1
  exact one_ne_zero (ut_mem_bT.mp h1)
omit [CharP F 2] in
theorem mem_zT_iff (x : UT3 F) : x ∈ zT F ↔ ∀ y : UT3 F, x * y = y * x := by
  constructor
  · rintro ⟨hxa, hxb⟩ y
    rw [ut_comm_iff, hxa, hxb]
    ring
  · intro h
    have h1 := (ut_comm_iff _ _).mp (h ⟨1, 0, 0⟩)
    have h2 := (ut_comm_iff _ _).mp (h ⟨0, 1, 0⟩)
    dsimp only at h1 h2
    exact ⟨by linear_combination h2, by linear_combination -h1⟩
theorem zT_sq (z : UT3 F) (hz : z ∈ zT F) : z * z = 1 := by
  obtain ⟨hza, hzb⟩ := hz
  rw [ut_sq, hza]
  ext <;> simp
omit [CharP F 2] in
theorem comm_mem_zT (x y : UT3 F) : x * y * x⁻¹ * y⁻¹ ∈ zT F := by
  rw [ut_comm]
  exact ⟨rfl, rfl⟩
theorem sq_mem_zT (x : UT3 F) : x * x ∈ zT F := by
  rw [ut_sq]
  exact ⟨rfl, rfl⟩
omit [CharP F 2] in
theorem aT_abel (x y : UT3 F) (hx : x ∈ aT F) (hy : y ∈ aT F) : x * y = y * x := by
  rw [ut_comm_iff, ut_mem_aT.mp hx, ut_mem_aT.mp hy]
  ring
omit [CharP F 2] in
theorem bT_abel (x y : UT3 F) (hx : x ∈ bT F) (hy : y ∈ bT F) : x * y = y * x := by
  rw [ut_comm_iff, ut_mem_bT.mp hx, ut_mem_bT.mp hy]
  ring
theorem aT_sq (x : UT3 F) (hx : x ∈ aT F) : x * x = 1 := by
  rw [ut_sq, ut_mem_aT.mp hx]
  ext <;> simp
theorem bT_sq (x : UT3 F) (hx : x ∈ bT F) : x * x = 1 := by
  rw [ut_sq, ut_mem_bT.mp hx]
  ext <;> simp
omit [CharP F 2] in
theorem aT_inf_bT (x : UT3 F) (ha : x ∈ aT F) (hb : x ∈ bT F) : x ∈ zT F :=
  ⟨ut_mem_bT.mp hb, ut_mem_aT.mp ha⟩
omit [CharP F 2] in
theorem aT_norm (s a : UT3 F) (ha : a ∈ aT F) : s * a * s⁻¹ ∈ aT F := by
  rw [ut_mem_aT]
  simp only [ut_mul_b, ut_inv_b, ut_mem_aT.mp ha]
  ring
omit [CharP F 2] in
theorem bT_norm (s b : UT3 F) (hb : b ∈ bT F) : s * b * s⁻¹ ∈ bT F := by
  rw [ut_mem_bT]
  simp only [ut_mul_a, ut_inv_a, ut_mem_bT.mp hb]
  ring
theorem invol_T (x : UT3 F) (hx : x * x = 1) : x ∈ aT F ∨ x ∈ bT F := by
  rw [ut_sq] at hx
  have h : x.a * x.b = 0 := congrArg UT3.c hx
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr h
  · exact Or.inl h
omit [CharP F 2] in
theorem cent_aT (a : UT3 F) (ha : a ∈ aT F) (haz : a ∉ zT F) (s : UT3 F) (hs : s * a = a * s) :
    s ∈ aT F := by
  have hab : a.b = 0 := ha
  have haa : a.a ≠ 0 := fun h => haz ⟨h, hab⟩
  rw [ut_comm_iff, hab] at hs
  have h : a.a * s.b = 0 := by linear_combination -hs
  exact (mul_eq_zero.mp h).resolve_left haa
omit [CharP F 2] in
theorem cent_bT (b : UT3 F) (hb : b ∈ bT F) (hbz : b ∉ zT F) (s : UT3 F) (hs : s * b = b * s) :
    s ∈ bT F := by
  have hba : b.a = 0 := hb
  have hbb : b.b ≠ 0 := fun h => hbz ⟨hba, h⟩
  rw [ut_comm_iff, hba] at hs
  have h : s.a * b.b = 0 := by linear_combination hs
  exact (mul_eq_zero.mp h).resolve_right hbb
omit [CharP F 2] in
theorem cent_not_aT (s : UT3 F) (hs : s ∉ aT F) (a : UT3 F) (ha : a ∈ aT F)
    (h : a * s = s * a) : a ∈ zT F := by
  have hab : a.b = 0 := ha
  have hsb : s.b ≠ 0 := hs
  rw [ut_comm_iff, hab] at h
  have h' : a.a * s.b = 0 := by linear_combination h
  exact ⟨(mul_eq_zero.mp h').resolve_right hsb, hab⟩
omit [CharP F 2] in
theorem cent_not_bT (s : UT3 F) (hs : s ∉ bT F) (b : UT3 F) (hb : b ∈ bT F)
    (h : b * s = s * b) : b ∈ zT F := by
  have hba : b.a = 0 := hb
  have hsa : s.a ≠ 0 := hs
  rw [ut_comm_iff, hba] at h
  have h' : s.a * b.b = 0 := by linear_combination -h
  exact ⟨hba, (mul_eq_zero.mp h').resolve_left hsa⟩
omit [CharP F 2] in
theorem normal_dich_T (N : Subgroup (UT3 F)) (hN : N.Normal) : N ≤ zT F ∨ zT F ≤ N := by
  by_cases h : N ≤ zT F
  · exact Or.inl h
  · right
    obtain ⟨x, hxN, hxz⟩ := IsConcreteLE.not_le_iff_exists.mp h
    have key : ∀ s : UT3 F, x * s * x⁻¹ * s⁻¹ ∈ N := by
      intro s
      have h1 : s * x⁻¹ * s⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hxN) s
      have h2 : x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) := by simp only [mul_assoc]
      rw [h2]
      exact N.mul_mem hxN h1
    intro z hz
    obtain ⟨hza, hzb⟩ := hz
    obtain ⟨s, hs⟩ : ∃ s : UT3 F, x.a * s.b - s.a * x.b = z.c := by
      by_cases hxa : x.a = 0
      · have hxb : x.b ≠ 0 := fun hb => hxz ⟨hxa, hb⟩
        refine ⟨⟨-(z.c / x.b), 0, 0⟩, ?_⟩
        dsimp only
        rw [hxa]
        field_simp
        ring
      · refine ⟨⟨0, z.c / x.a, 0⟩, ?_⟩
        dsimp only
        field_simp
        ring
    have hz' : z = x * s * x⁻¹ * s⁻¹ := by
      rw [ut_comm]
      ext
      · exact hza
      · exact hzb
      · exact hs.symm
    rw [hz']
    exact key s
theorem elemAb_le_T (E : Subgroup (UT3 F)) (hsq : ∀ x ∈ E, x * x = 1)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : E ≤ aT F ∨ E ≤ bT F := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨x, hxE, hxa⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  obtain ⟨y, hyE, hyb⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.2
  have hxb : x.b ≠ 0 := hxa
  have hya : y.a ≠ 0 := hyb
  have hx0 : x.a = 0 := by
    have h := hsq x hxE
    rw [ut_sq] at h
    have h' : x.a * x.b = 0 := congrArg UT3.c h
    exact (mul_eq_zero.mp h').resolve_right hxb
  have hy0 : y.b = 0 := by
    have h := hsq y hyE
    rw [ut_sq] at h
    have h' : y.a * y.b = 0 := congrArg UT3.c h
    exact (mul_eq_zero.mp h').resolve_left hya
  have h := (ut_comm_iff x y).mp (hc x hxE y hyE)
  rw [hx0, hy0] at h
  have h3 : y.a * x.b = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h3 with h | h
  · exact hya h
  · exact hxb h
theorem extremal_T [Finite F] (hF : Nat.card F = 4) (z : UT3 F) (hz : z ∈ zT F) (hz1 : z ≠ 1)
    (a : UT3 F) (ha : a ∉ zT F) :
    ∃ s t : UT3 F, s * a * s⁻¹ * a⁻¹ ∈ zpowers z ∧ t * a * t⁻¹ * a⁻¹ ∈ zpowers z ∧
      s * t * s⁻¹ * t⁻¹ ∉ zpowers z := by
  classical
  obtain ⟨hza, hzb⟩ := hz
  have hzc : z.c ≠ 0 := by
    intro h
    apply hz1
    ext
    · exact hza
    · exact hzb
    · exact h
  have hzz : z * z = 1 := zT_sq z ⟨hza, hzb⟩
  have hzeq : (⟨0, 0, z.c⟩ : UT3 F) = z := by
    ext
    · exact hza.symm
    · exact hzb.symm
    · rfl
  obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : F, μ ≠ 0 ∧ μ ≠ 1 := by
    by_contra hcon
    let _ : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · have : x = 1 := by
          by_contra hx1
          exact hcon ⟨x, hx, hx1⟩
        simp [this]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
    rw [Finset.card_univ, hcard] at h1
    omega
  have key3 : (⟨0, 0, μ * z.c⟩ : UT3 F) ∉ zpowers z := by
    intro h
    rcases zpowers_sq_cases z hzz _ h with h | h
    · have h' : μ * z.c = 0 := congrArg UT3.c h
      exact (mul_ne_zero hμ0 hzc) h'
    · have h' : μ * z.c = z.c := congrArg UT3.c h
      apply hμ1
      have h'' : (μ - 1) * z.c = 0 := by linear_combination h'
      have := (mul_eq_zero.mp h'').resolve_right hzc
      linear_combination this
  obtain ⟨s, t, hs, ht, hst⟩ : ∃ s t : UT3 F, s.a * a.b + a.a * s.b = 0 ∧
      t.a * a.b + a.a * t.b = z.c ∧ s.a * t.b + t.a * s.b = μ * z.c := by
    by_cases hα : a.a = 0
    · have hβ : a.b ≠ 0 := fun h => ha ⟨hα, h⟩
      refine ⟨⟨μ * a.a, μ * a.b, 0⟩, ⟨z.c / a.b, 0, 0⟩, ?_, ?_, ?_⟩
      · dsimp only
        linear_combination (μ * a.a * a.b) * (ut_two_eq (F := F))
      · dsimp only
        field_simp
        ring
      · dsimp only
        field_simp
        ring
    · refine ⟨⟨μ * a.a, μ * a.b, 0⟩, ⟨0, z.c / a.a, 0⟩, ?_, ?_, ?_⟩
      · dsimp only
        linear_combination (μ * a.a * a.b) * (ut_two_eq (F := F))
      · dsimp only
        field_simp
        ring
      · dsimp only
        field_simp
        ring
  refine ⟨s, t, ?_, ?_, ?_⟩
  · rw [ut_comm2, hs]
    exact one_mem _
  · rw [ut_comm2, ht, hzeq]
    exact mem_zpowers z
  · rw [ut_comm2, hst]
    exact key3
omit [CharP F 2] in
theorem diag_pair (φ : MulAut (UT3 F)) (hz : ∀ z ∈ zT F, φ z = z)
    (ha : ∀ a ∈ aT F, φ a ∈ aT F) (hb : ∀ b ∈ bT F, φ b ∈ bT F)
    (x y : UT3 F) (hx : x.b = 0) (hy : y.a = 0) :
    (φ x).a * (φ y).b = x.a * y.b := by
  have h1 : φ (x * y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := hz _ (comm_mem_zT x y)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ut_comm, ut_comm] at h1
  have h2 : (φ x).b = 0 := ha x hx
  have h3 : (φ y).a = 0 := hb y hy
  have h4 : (φ x).a * (φ y).b - (φ y).a * (φ x).b = x.a * y.b - y.a * x.b := congrArg UT3.c h1
  rw [h2, h3, hx, hy] at h4
  linear_combination h4

omit [CharP F 2] in
theorem diag_scalar (φ : MulAut (UT3 F)) (hz : ∀ z ∈ zT F, φ z = z)
    (ha : ∀ a ∈ aT F, φ a ∈ aT F) (hb : ∀ b ∈ bT F, φ b ∈ bT F) :
    ∃ l : F, l ≠ 0 ∧ (∀ s, (φ s).a = l * s.a) ∧ (∀ s, (φ s).b = l⁻¹ * s.b) := by
  have hpair := diag_pair φ hz ha hb
  obtain ⟨l, hl⟩ : ∃ l : F, (φ ⟨1, 0, 0⟩).a = l := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : F, (φ ⟨0, 1, 0⟩).b = m := ⟨_, rfl⟩
  have h11 : l * m = 1 := by
    have h := hpair ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ rfl rfl
    rw [hl, hm] at h
    dsimp only at h
    linear_combination h
  have hl0 : l ≠ 0 := left_ne_zero_of_mul_eq_one h11
  have hm' : m = l⁻¹ := eq_inv_of_mul_eq_one_right h11
  have hAa : ∀ x : UT3 F, x.b = 0 → (φ x).a = l * x.a := by
    intro x hx
    have h := hpair x ⟨0, 1, 0⟩ hx rfl
    rw [hm] at h
    dsimp only at h
    linear_combination (-(φ x).a) * h11 + l * h
  have hBb : ∀ y : UT3 F, y.a = 0 → (φ y).b = m * y.b := by
    intro y hy
    have h := hpair ⟨1, 0, 0⟩ y rfl hy
    rw [hl] at h
    dsimp only at h
    linear_combination (-(φ y).b) * h11 + m * h
  have hdec : ∀ s : UT3 F, s = ⟨s.a, 0, 0⟩ * ⟨0, s.b, 0⟩ * ⟨0, 0, s.c - s.a * s.b⟩ := by
    intro s
    ext
    · simp
    · simp
    · simp only [ut_mul_c, ut_mul_a]
      ring
  have hφ : ∀ s : UT3 F, φ s = φ ⟨s.a, 0, 0⟩ * φ ⟨0, s.b, 0⟩ * φ ⟨0, 0, s.c - s.a * s.b⟩ := by
    intro s
    conv_lhs => rw [hdec s]
    rw [map_mul, map_mul]
  have hA : ∀ s : UT3 F, (φ s).a = l * s.a := by
    intro s
    have h1 : (φ ⟨s.a, 0, 0⟩).a = l * s.a := hAa _ rfl
    have h2 : (φ ⟨0, s.b, 0⟩).a = 0 := hb _ rfl
    have h3 : φ ⟨0, 0, s.c - s.a * s.b⟩ = ⟨0, 0, s.c - s.a * s.b⟩ := hz _ ⟨rfl, rfl⟩
    rw [hφ s]
    simp only [ut_mul_a, h1, h2, h3]
    ring
  have hB : ∀ s : UT3 F, (φ s).b = m * s.b := by
    intro s
    have h1 : (φ ⟨s.a, 0, 0⟩).b = 0 := ha _ rfl
    have h2 : (φ ⟨0, s.b, 0⟩).b = m * s.b := hBb _ rfl
    have h3 : φ ⟨0, 0, s.c - s.a * s.b⟩ = ⟨0, 0, s.c - s.a * s.b⟩ := hz _ ⟨rfl, rfl⟩
    rw [hφ s]
    simp only [ut_mul_b, h1, h2, h3]
    ring
  exact ⟨l, hl0, hA, fun s => by rw [hB s, hm']⟩

omit [CharP F 2] in
theorem diag_T [Finite F] (hF : Nat.card F = 4) (φ : MulAut (UT3 F))
    (hz : ∀ z ∈ zT F, φ z = z) (ha : ∀ a ∈ aT F, φ a ∈ aT F) (hb : ∀ b ∈ bT F, φ b ∈ bT F) :
    (∀ s, φ s * s⁻¹ ∈ zT F) ∨
      ((∀ s, φ s * s⁻¹ ∈ zT F → s ∈ zT F) ∧ ∀ s, φ (φ (φ s)) * s⁻¹ ∈ zT F) := by
  obtain ⟨l, hl0, hA, hB⟩ := diag_scalar φ hz ha hb
  by_cases hl1 : l = 1
  · left
    intro s
    refine ⟨?_, ?_⟩
    · show (φ s * s⁻¹).a = 0
      simp only [ut_mul_a, ut_inv_a, hA, hl1]
      ring
    · show (φ s * s⁻¹).b = 0
      simp only [ut_mul_b, ut_inv_b, hB, hl1, inv_one]
      ring
  · right
    refine ⟨?_, ?_⟩
    · intro s hs
      obtain ⟨h1, h2⟩ := hs
      simp only [ut_mul_a, ut_inv_a, hA] at h1
      simp only [ut_mul_b, ut_inv_b, hB] at h2
      have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
      have hl1'' : l⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hl1 (inv_eq_one.mp h))
      refine ⟨?_, ?_⟩
      · have h3 : (l - 1) * s.a = 0 := by linear_combination h1
        exact (mul_eq_zero.mp h3).resolve_left hl1'
      · have h3 : (l⁻¹ - 1) * s.b = 0 := by linear_combination h2
        exact (mul_eq_zero.mp h3).resolve_left hl1''
    · have hl3 : l ^ 3 = 1 := by
        let _ : Fintype F := Fintype.ofFinite F
        have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
        have h := FiniteField.pow_card_sub_one_eq_one l hl0
        rw [hcard] at h
        exact h
      have hl3' : l⁻¹ ^ 3 = 1 := by rw [inv_pow, hl3, inv_one]
      intro s
      refine ⟨?_, ?_⟩
      · show (φ (φ (φ s)) * s⁻¹).a = 0
        simp only [ut_mul_a, ut_inv_a, hA]
        linear_combination s.a * hl3
      · show (φ (φ (φ s)) * s⁻¹).b = 0
        simp only [ut_mul_b, ut_inv_b, hB]
        linear_combination s.b * hl3'

end CFSG.OddStandard.ThmC.O2.TL
