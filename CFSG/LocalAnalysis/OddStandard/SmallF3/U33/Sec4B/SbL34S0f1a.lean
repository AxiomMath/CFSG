module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {H : Type*} [Group H]

theorem class_two_of_index_two (A : Subgroup H) (l : H) (hl : l * l = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAsq : ∀ a ∈ A, a * a = 1)
    (hAn : ∀ a ∈ A, l * a * l⁻¹ ∈ A) (hgen : ∀ h : H, h ∈ A ∨ ∃ a ∈ A, h = a * l) :
    ∀ x y z : H, (x * y * x⁻¹ * y⁻¹) * z * (x * y * x⁻¹ * y⁻¹)⁻¹ * z⁻¹ = 1 := by
  have hl' : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl
  have hσ_invol : ∀ a : H, l * (l * a * l⁻¹) * l⁻¹ = a := by
    intro a
    calc l * (l * a * l⁻¹) * l⁻¹
        = (l * l) * a * (l⁻¹ * l⁻¹) := by group
      _ = a := by simp [hl, hl']
  have hcomm : ∀ x y : H, x * y * x⁻¹ * y⁻¹ ∈ A ∧
      l * (x * y * x⁻¹ * y⁻¹) * l⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    intro x y
    rcases hgen x with hx | ⟨a, ha, rfl⟩
    · rcases hgen y with hy | ⟨b, hb, rfl⟩
      ·
        have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hAc x hx y hy]; group
        constructor <;> simp [h1]
      ·
        have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hAsq x hx)
        have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hAsq b hb)
        have hσx : l * x * l⁻¹ ∈ A := hAn x hx
        have h2 : x * (b * l) * x⁻¹ * (b * l)⁻¹ = x * (l * x * l⁻¹) := by
          conv_lhs => simp only [mul_inv_rev, hx', hb', hl']
          calc x * (b * l) * x * (l * b)
              = x * b * (l * x * l⁻¹) * (l * l) * b := by group
            _ = x * b * (l * x * l⁻¹) * b := by rw [hl, mul_one]
            _ = x * (b * (l * x * l⁻¹)) * b := by group
            _ = x * ((l * x * l⁻¹) * b) * b := by rw [hAc b hb (l * x * l⁻¹) hσx]
            _ = x * (l * x * l⁻¹) * (b * b) := by group
            _ = x * (l * x * l⁻¹) := by rw [hAsq b hb, mul_one]
        refine ⟨?_, ?_⟩
        · rw [h2]; exact A.mul_mem hx hσx
        · rw [h2]
          calc l * (x * (l * x * l⁻¹)) * l⁻¹
              = (l * x * l⁻¹) * (l * (l * x * l⁻¹) * l⁻¹) := by group
            _ = (l * x * l⁻¹) * x := by rw [hσ_invol x]
            _ = x * (l * x * l⁻¹) := by rw [hAc (l * x * l⁻¹) hσx x hx]
    · rcases hgen y with hy | ⟨b, hb, rfl⟩
      ·
        have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAsq a ha)
        have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hAsq y hy)
        have hσy : l * y * l⁻¹ ∈ A := hAn y hy
        have h3 : (a * l) * y * (a * l)⁻¹ * y⁻¹ = (l * y * l⁻¹) * y := by
          conv_lhs => simp only [mul_inv_rev, ha', hy', hl']
          calc a * l * y * (l * a) * y
              = a * (l * y * l⁻¹) * (l * l) * a * y := by group
            _ = a * (l * y * l⁻¹) * a * y := by rw [hl, mul_one]
            _ = (l * y * l⁻¹) * (a * a) * y := by
                  rw [hAc a ha (l * y * l⁻¹) hσy]; group
            _ = (l * y * l⁻¹) * y := by rw [hAsq a ha, mul_one]
        refine ⟨?_, ?_⟩
        · rw [h3]; exact A.mul_mem hσy hy
        · rw [h3]
          calc l * ((l * y * l⁻¹) * y) * l⁻¹
              = (l * (l * y * l⁻¹) * l⁻¹) * (l * y * l⁻¹) := by group
            _ = y * (l * y * l⁻¹) := by rw [hσ_invol y]
            _ = (l * y * l⁻¹) * y := by rw [hAc y hy (l * y * l⁻¹) hσy]
      ·
        have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAsq a ha)
        have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hAsq b hb)
        have hσa : l * a * l⁻¹ ∈ A := hAn a ha
        have hσb : l * b * l⁻¹ ∈ A := hAn b hb
        have h4 : (a * l) * (b * l) * (a * l)⁻¹ * (b * l)⁻¹
            = (a * (l * a * l⁻¹)) * ((l * b * l⁻¹) * b) := by
          conv_lhs => simp only [mul_inv_rev, ha', hb', hl']
          calc a * l * (b * l) * (l * a) * (l * b)
              = a * l * b * (l * l) * a * l * b := by group
            _ = a * l * b * a * l * b := by rw [hl, mul_one]
            _ = a * (l * b * l⁻¹) * (l * a * l⁻¹) * (l * l) * b := by group
            _ = a * (l * b * l⁻¹) * (l * a * l⁻¹) * b := by rw [hl, mul_one]
            _ = a * ((l * b * l⁻¹) * (l * a * l⁻¹)) * b := by group
            _ = a * ((l * a * l⁻¹) * (l * b * l⁻¹)) * b := by
                  rw [hAc (l * b * l⁻¹) hσb (l * a * l⁻¹) hσa]
            _ = (a * (l * a * l⁻¹)) * ((l * b * l⁻¹) * b) := by group
        refine ⟨?_, ?_⟩
        · rw [h4]; exact A.mul_mem (A.mul_mem ha hσa) (A.mul_mem hσb hb)
        · rw [h4]
          calc l * ((a * (l * a * l⁻¹)) * ((l * b * l⁻¹) * b)) * l⁻¹
              = (l * (a * (l * a * l⁻¹)) * l⁻¹)
                * (l * ((l * b * l⁻¹) * b) * l⁻¹) := by group
            _ = ((l * a * l⁻¹) * (l * (l * a * l⁻¹) * l⁻¹))
                * ((l * (l * b * l⁻¹) * l⁻¹) * (l * b * l⁻¹)) := by group
            _ = ((l * a * l⁻¹) * a) * (b * (l * b * l⁻¹)) := by
                  rw [hσ_invol a, hσ_invol b]
            _ = (a * (l * a * l⁻¹)) * ((l * b * l⁻¹) * b) := by
                  rw [hAc (l * a * l⁻¹) hσa a ha, hAc b hb (l * b * l⁻¹) hσb]
  have hcentral : ∀ c ∈ A, l * c * l⁻¹ = c → ∀ w : H, c * w = w * c := by
    intro c hc hfix w
    rcases hgen w with hw | ⟨b, hb, rfl⟩
    · exact hAc c hc w hw
    · have hcl : c * l = l * c := by
        have h : (l * c * l⁻¹) * l = c * l := congrArg (· * l) hfix
        rw [← h]
        group
      calc c * (b * l) = (c * b) * l := by group
        _ = (b * c) * l := by rw [hAc c hc b hb]
        _ = b * (c * l) := by group
        _ = b * (l * c) := by rw [hcl]
        _ = (b * l) * c := by group
  intro x y z
  obtain ⟨hcA, hcfix⟩ := hcomm x y
  have hcz : (x * y * x⁻¹ * y⁻¹) * z = z * (x * y * x⁻¹ * y⁻¹) :=
    hcentral _ hcA hcfix z
  rw [hcz]
  group

theorem class_two_mod_of_index_two (N : Subgroup H) [N.Normal] (A : Subgroup H) (l : H)
    (hl : l * l ∈ N) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hAsq : ∀ a ∈ A, a * a ∈ N) (hAn : ∀ a ∈ A, l * a * l⁻¹ ∈ A)
    (hgen : ∀ h : H, h ∈ A ∨ ∃ a ∈ A, h = a * l) :
    ∀ x y z : H, (x * y * x⁻¹ * y⁻¹) * z * (x * y * x⁻¹ * y⁻¹)⁻¹ * z⁻¹ ∈ N := by
  have hmain : ∀ x y z : H ⧸ N,
      (x * y * x⁻¹ * y⁻¹) * z * (x * y * x⁻¹ * y⁻¹)⁻¹ * z⁻¹ = 1 := by
    refine class_two_of_index_two (A.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N l)
      ?_ ?_ ?_ ?_ ?_
    ·
      have h : QuotientGroup.mk' N (l * l) = 1 := (QuotientGroup.eq_one_iff _).mpr hl
      simpa only [map_mul] using h
    ·
      intro a' ha' b' hb'
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
      have hmem : QuotientGroup.mk' N a * QuotientGroup.mk' N b * (QuotientGroup.mk' N a)⁻¹ *
          (QuotientGroup.mk' N b)⁻¹ = 1 := by
        have h : QuotientGroup.mk' N (a * b * a⁻¹ * b⁻¹) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (hAc a ha b hb)
        simpa only [map_mul, map_inv] using h
      have h2 : (QuotientGroup.mk' N a * QuotientGroup.mk' N b) *
          (QuotientGroup.mk' N b * QuotientGroup.mk' N a)⁻¹ = 1 := by
        rw [mul_inv_rev]
        calc (QuotientGroup.mk' N a * QuotientGroup.mk' N b) *
              ((QuotientGroup.mk' N a)⁻¹ * (QuotientGroup.mk' N b)⁻¹)
            = (QuotientGroup.mk' N a * QuotientGroup.mk' N b * (QuotientGroup.mk' N a)⁻¹) *
                (QuotientGroup.mk' N b)⁻¹ := by group
          _ = 1 := hmem
      exact mul_inv_eq_one.mp h2
    ·
      intro a' ha'
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      have h : QuotientGroup.mk' N (a * a) = 1 := (QuotientGroup.eq_one_iff _).mpr (hAsq a ha)
      simpa only [map_mul] using h
    ·
      intro a' ha'
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      have h : QuotientGroup.mk' N (l * a * l⁻¹) ∈ A.map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ (hAn a ha)
      simpa only [map_mul, map_inv] using h
    ·
      intro h'
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N h'
      rcases hgen h with hh | ⟨a, ha, rfl⟩
      · exact Or.inl (Subgroup.mem_map_of_mem _ hh)
      · exact Or.inr ⟨QuotientGroup.mk' N a, Subgroup.mem_map_of_mem _ ha, by rw [map_mul]⟩
  intro x y z
  have h := hmain (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) (QuotientGroup.mk' N z)
  have hq : ((x * y * x⁻¹ * y⁻¹) * z * (x * y * x⁻¹ * y⁻¹)⁻¹ * z⁻¹ : H ⧸ N) = 1 := by
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk'_apply] using h
  exact (QuotientGroup.eq_one_iff _).mp hq

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
