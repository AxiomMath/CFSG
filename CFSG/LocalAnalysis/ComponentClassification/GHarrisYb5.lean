module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb4

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

omit [Finite Y] in
theorem E_le_Y1 : D.E ≤ D.Y1 := by
  rintro _ ⟨e, he, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, SE.l_comm_E e he])

omit [Finite Y] in
theorem F_le_Y1 : D.F ≤ D.Y1 := by
  rintro _ ⟨f, hf, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, SE.l_comm_F f hf])

abbrev Et : Subgroup D.Xt := (D.E.subgroupOf D.Y1).map D.piX

abbrev Ft : Subgroup D.Xt := (D.F.subgroupOf D.Y1).map D.piX

omit [Finite Y] in
theorem lpow_mem_E {c : D.Y1} (hc : (c : Y) = 1 ∨ (c : Y) = D.l ∨ (c : Y) = D.z ∨
    (c : Y) = D.l * D.z) : (c : Y) ∈ D.E := by
  rcases hc with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact D.l_mem_E
  · exact D.z_mem_E
  · exact mul_mem D.l_mem_E D.z_mem_E

omit [Finite Y] in
theorem lpow_mem_F {c : D.Y1} (hc : (c : Y) = 1 ∨ (c : Y) = D.l ∨ (c : Y) = D.z ∨
    (c : Y) = D.l * D.z) : (c : Y) ∈ D.F := by
  rcases hc with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact D.l_mem_F
  · exact D.z_mem_F
  · exact mul_mem D.l_mem_F D.z_mem_F

theorem piX_mem_Et_iff (y : D.Y1) : D.piX y ∈ D.Et ↔ (y : Y) ∈ D.E := by
  constructor
  · rintro ⟨e, he, hey⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      D.mem_zpowers_l_iff] at hey
    have hc := D.lpow_mem_E hey
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    have := mul_mem (mem_subgroupOf.mp he) hc
    rwa [mul_inv_cancel_left] at this
  · intro hy
    exact ⟨y, mem_subgroupOf.mpr hy, rfl⟩

theorem piX_mem_Ft_iff (y : D.Y1) : D.piX y ∈ D.Ft ↔ (y : Y) ∈ D.F := by
  constructor
  · rintro ⟨f, hf, hfy⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      D.mem_zpowers_l_iff] at hfy
    have hc := D.lpow_mem_F hfy
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    have := mul_mem (mem_subgroupOf.mp hf) hc
    rwa [mul_inv_cancel_left] at this
  · intro hy
    exact ⟨y, mem_subgroupOf.mpr hy, rfl⟩


theorem exists_S1Y_of_mem (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    {w : D.Xt} (hw : w ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    ∃ s : D.S1Y, D.piX s = w := by
  rw [D.coe_sylowXt hO hz] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  exact ⟨⟨s, hs⟩, rfl⟩

theorem mem_Et_iff_tUT (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) {w : D.Xt}
    (hw : w ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    w ∈ D.Et ↔ (D.tUT hO hz ⟨w, hw⟩).b = 0 := by
  obtain ⟨s, rfl⟩ := D.exists_S1Y_of_mem hO hz hw
  rw [D.tUT_apply hO hz s, D.piX_mem_Et_iff, ← SE.predE_iff_toUT _ (D.preS1_lt s), ← D.toG_preS1,
    D.toG_mem_E_iff]

theorem mem_Ft_iff_tUT (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) {w : D.Xt}
    (hw : w ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    w ∈ D.Ft ↔ (D.tUT hO hz ⟨w, hw⟩).a = 0 := by
  obtain ⟨s, rfl⟩ := D.exists_S1Y_of_mem hO hz hw
  rw [D.tUT_apply hO hz s, D.piX_mem_Ft_iff, ← SE.predF_iff_toUT _ (D.preS1_lt s), ← D.toG_preS1,
    D.toG_mem_F_iff]

theorem Et_le (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.Et ≤ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [D.coe_sylowXt hO hz]
  obtain ⟨e, he, hey⟩ := mem_subgroupOf.mp hy
  have hS1 : (y : Y) ∈ D.S1 := by rw [← hey]; exact D.toG_mem_S1 (SE.Esub.mem_carrier.mp he).1
  exact mem_map_of_mem _ (mem_subgroupOf.mpr hS1)

theorem Ft_le (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.Ft ≤ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [D.coe_sylowXt hO hz]
  obtain ⟨f, hf, hfy⟩ := mem_subgroupOf.mp hy
  have hS1 : (y : Y) ∈ D.S1 := by rw [← hfy]; exact D.toG_mem_S1 (SE.Fsub.mem_carrier.mp hf).1
  exact mem_map_of_mem _ (mem_subgroupOf.mpr hS1)

theorem card_Et_Ft (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) :
    Nat.card D.Et = 16 ∧ Nat.card D.Ft = 16 := by
  classical
  set T := ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)
  have key : ∀ (H : Subgroup D.Xt) (hH : H ≤ T) (p : UT3 F4c → Prop) [DecidablePred p],
      (∀ w (hw : w ∈ T), w ∈ H ↔ p (D.tUT hO hz ⟨w, hw⟩)) →
      Nat.card H = (Finset.univ.filter p).card := by
    intro H hH p _ hp
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w => ⟨D.tUT hO hz ⟨w, hH w.2⟩, (hp w (hH w.2)).mp w.2⟩
        invFun := fun u => ⟨((D.tUT hO hz).symm u.1 : D.Xt), by
          rw [hp _ (Subtype.mem _)]; simpa using u.2⟩
        left_inv := fun w => Subtype.ext (by simp)
        right_inv := fun u => Subtype.ext (by simp only [Subtype.coe_eta,
          MulEquiv.apply_symm_apply]) }
  exact ⟨(key D.Et (D.Et_le hO hz) (fun u => u.b = 0) fun w hw => D.mem_Et_iff_tUT hO hz hw).trans
      SE.card_ut_b,
    (key D.Ft (D.Ft_le hO hz) (fun u => u.a = 0) fun w hw => D.mem_Ft_iff_tUT hO hz hw).trans
      SE.card_ut_a⟩

theorem eq_Et_or_Ft (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    {B : Subgroup D.Xt} (hB : B ≤ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt))
    (h2 : ∀ b ∈ B, b * b = 1) (hc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) (h16 : Nat.card B = 16) :
    B = D.Et ∨ B = D.Ft := by
  have hu : ∀ b (hb : b ∈ B), D.tUT hO hz ⟨b, hB hb⟩ * D.tUT hO hz ⟨b, hB hb⟩ = 1 := by
    intro b hb
    rw [← map_mul, show (⟨b, hB hb⟩ : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) *
      ⟨b, hB hb⟩ = 1 from Subtype.ext (h2 b hb), map_one]
  by_cases hall : ∀ b ∈ B, b ∈ D.Ft
  · right
    exact eq_of_le_of_card_ge (fun b hb => hall b hb) (by rw [h16, (D.card_Et_Ft hO hz).2])
  · left
    push Not at hall
    obtain ⟨b₀, hb₀, hb₀F⟩ := hall
    rw [D.mem_Ft_iff_tUT hO hz (hB hb₀)] at hb₀F
    refine eq_of_le_of_card_ge (fun b hb => ?_) (by rw [h16, (D.card_Et_Ft hO hz).1])
    rw [D.mem_Et_iff_tUT hO hz (hB hb)]
    by_contra hbE
    have hcomm : D.tUT hO hz ⟨b₀, hB hb₀⟩ * D.tUT hO hz ⟨b, hB hb⟩ =
        D.tUT hO hz ⟨b, hB hb⟩ * D.tUT hO hz ⟨b₀, hB hb₀⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc b₀ hb₀ b hb)
    rcases SE.ut_comm_inv _ _ (hu b₀ hb₀) (hu b hb) hcomm with h | h | h | h
    · rcases SE.ut_inv_cases _ (hu b₀ hb₀) with h' | h'
      · exact hb₀F h'
      · exact hbE h.2
    · exact hb₀F h.1
    · exact hb₀F h.1
    · exact hbE h.2

end GHSylow

end CFSG.ComponentClassification.GHarris
