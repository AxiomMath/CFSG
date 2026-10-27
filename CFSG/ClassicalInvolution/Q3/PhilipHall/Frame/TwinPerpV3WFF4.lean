module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8ZA1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFQ8
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

section Klein

variable {Y : Type*} [Group Y]

theorem klein_closure {t s : Y} (ht : t * t = 1) (hs : s * s = 1) (hc : t * s = s * t) :
    ∀ g ∈ Subgroup.closure ({t, s} : Set Y), g = 1 ∨ g = t ∨ g = s ∨ g = t * s := by
  have hmt : ∀ g : Y, (g = 1 ∨ g = t ∨ g = s ∨ g = t * s) →
      (g * t = 1 ∨ g * t = t ∨ g * t = s ∨ g * t = t * s) := by
    rintro g (rfl | rfl | rfl | rfl)
    · right; left; simp
    · left; exact ht
    · right; right; right; exact hc.symm
    · right; right; left
      calc t * s * t = t * (s * t) := mul_assoc _ _ _
        _ = t * (t * s) := by rw [hc]
        _ = t * t * s := (mul_assoc _ _ _).symm
        _ = s := by rw [ht, one_mul]
  have hms : ∀ g : Y, (g = 1 ∨ g = t ∨ g = s ∨ g = t * s) →
      (g * s = 1 ∨ g * s = t ∨ g * s = s ∨ g * s = t * s) := by
    rintro g (rfl | rfl | rfl | rfl)
    · right; right; left; simp
    · right; right; right; rfl
    · left; exact hs
    · right; left
      calc t * s * s = t * (s * s) := mul_assoc _ _ _
        _ = t := by rw [hs, mul_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · right; left; rfl
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      right; right; left; rfl
  | one => left; rfl
  | mul x y _ _ hx hy =>
    rcases hy with rfl | rfl | rfl | rfl
    · rw [mul_one]; exact hx
    · exact hmt x hx
    · exact hms x hx
    · rw [← mul_assoc]; exact hms _ (hmt x hx)
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · left; simp
    · right; left; exact hti
    · right; right; left; exact hsi
    · right; right; right
      rw [mul_inv_rev, hti, hsi, hc.symm]

theorem fix_of_odd_klein {t s x : Y} (hxo : Odd (orderOf x)) (hxt : x * t = t * x) (ht : t * t = 1)
    (ht1 : t ≠ 1) (h : x * s * x⁻¹ = s ∨ x * s * x⁻¹ = t * s) : x * s * x⁻¹ = s := by
  rcases h with h | h
  · exact h
  · exfalso
    have hxt' : x * t * x⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr hxt
    have h2 : (x * x) * s * (x * x)⁻¹ = s := by
      calc (x * x) * s * (x * x)⁻¹ = x * (x * s * x⁻¹) * x⁻¹ := by group
        _ = x * (t * s) * x⁻¹ := by rw [h]
        _ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
        _ = t * (t * s) := by rw [hxt', h]
        _ = s := by rw [← mul_assoc, ht, one_mul]
    have hcm : Commute (x * x) s := mul_inv_eq_iff_eq_mul.mp h2
    obtain ⟨r, hr⟩ := exists_eq_pow_sq hxo
    have h3 : x * s = s * x := by
      have := (Commute.pow_left hcm r).eq
      rw [← hr] at this
      exact this
    have h4 : x * s * x⁻¹ = s := by rw [h3]; group
    rw [h4] at h
    exact ht1 (by
      have : t * s = 1 * s := by rw [← h, one_mul]
      exact (mul_right_cancel this))

end Klein

section Core

variable {Y : Type*} [Group Y] {t : Y}

theorem ne_one_ne_t_of_sq {b : Y} (hb : b * b = t) (ht1 : t ≠ 1) (ht : t * t = 1) : b ≠ 1 ∧ b ≠ t :=
  ⟨fun h => ht1 (by rw [← hb, h, one_mul]), fun h => by subst h; exact ht1 (hb.symm.trans ht)⟩

theorem frame_prod_ne {J₁ J₂ J₃ J₄ : Subgroup Y} {b₁ b₂ b₃ b₄ : Y} (hq₁ : Q8Facts J₁ t)
    (hb₁ : b₁ ∈ J₁) (hb₂ : b₂ ∈ J₂) (hb₃ : b₃ ∈ J₃) (hb₄ : b₄ ∈ J₄) (hb₁2 : b₁ * b₁ = t)
    (h12 : Commutes J₁ J₂) (h13 : Commutes J₁ J₃) (h14 : Commutes J₁ J₄) :
    b₁ * b₂ * b₃ * b₄ ≠ 1 ∧ b₁ * b₂ * b₃ * b₄ ≠ t := by
  have ht1 := hq₁.z_ne
  have ht := hq₁.z_sq
  obtain ⟨hb1, hb2⟩ := ne_one_ne_t_of_sq hb₁2 ht1 ht
  have hr : ∀ m ∈ J₁, m * (b₂ * b₃ * b₄) = (b₂ * b₃ * b₄) * m := by
    intro m hm
    have c2 := h12 m hm b₂ hb₂
    have c3 := h13 m hm b₃ hb₃
    have c4 := h14 m hm b₄ hb₄
    calc m * (b₂ * b₃ * b₄) = (m * b₂) * b₃ * b₄ := by group
      _ = b₂ * m * b₃ * b₄ := by rw [c2]
      _ = b₂ * (m * b₃) * b₄ := by group
      _ = b₂ * (b₃ * m) * b₄ := by rw [c3]
      _ = b₂ * b₃ * (m * b₄) := by group
      _ = b₂ * b₃ * (b₄ * m) := by rw [c4]
      _ = (b₂ * b₃ * b₄) * m := by group
  have e : b₁ * b₂ * b₃ * b₄ = b₁ * (b₂ * b₃ * b₄) := by group
  have hb₁i : b₁⁻¹ ∈ J₁ := J₁.inv_mem hb₁
  constructor
  · intro hs
    rw [e] at hs
    have hr' : b₂ * b₃ * b₄ = b₁⁻¹ := by
      calc b₂ * b₃ * b₄ = b₁⁻¹ * (b₁ * (b₂ * b₃ * b₄)) := by group
        _ = b₁⁻¹ := by rw [hs, mul_one]
    have hc : ∀ g ∈ J₁, b₁⁻¹ * g = g * b₁⁻¹ := fun g hg => by
      rw [← hr']; exact (hr g hg).symm
    rcases hq₁.center _ hb₁i hc with h | h
    · exact hb1 (inv_eq_one.mp h)
    · exact hb2 (by rw [← inv_inv b₁, h, inv_eq_of_mul_eq_one_right ht])
  · intro hs
    rw [e] at hs
    have hr' : b₂ * b₃ * b₄ = b₁⁻¹ * t := by
      calc b₂ * b₃ * b₄ = b₁⁻¹ * (b₁ * (b₂ * b₃ * b₄)) := by group
        _ = b₁⁻¹ * t := by rw [hs]
    have hmem : b₁⁻¹ * t ∈ J₁ := J₁.mul_mem hb₁i hq₁.z_mem
    have hc : ∀ g ∈ J₁, b₁⁻¹ * t * g = g * (b₁⁻¹ * t) := fun g hg => by
      rw [← hr']; exact (hr g hg).symm
    rcases hq₁.center _ hmem hc with h | h
    ·
      have : t = b₁ := by
        have h' : b₁⁻¹ * t = 1 := h
        calc t = b₁ * (b₁⁻¹ * t) := by group
          _ = b₁ := by rw [h', mul_one]
      exact hb2 this.symm
    ·
      have : b₁ = 1 := by
        have h' : b₁⁻¹ * t = t := h
        have : b₁⁻¹ = 1 := by
          calc b₁⁻¹ = b₁⁻¹ * t * t⁻¹ := by group
            _ = t * t⁻¹ := by rw [h']
            _ = 1 := by group
        exact inv_eq_one.mp this
      exact hb1 this

theorem f4_core {J₁ J₂ J₃ J₄ : Subgroup Y} {b₁ b₂ b₃ b₄ x : Y} (hq₃ : Q8Facts J₃ t)
    (hq₄ : Q8Facts J₄ t) (hb₁ : b₁ ∈ J₁) (hb₂ : b₂ ∈ J₂) (hb₃ : b₃ ∈ J₃) (hb₄ : b₄ ∈ J₄)
    (hb₃2 : b₃ * b₃ = t) (hb₄2 : b₄ * b₄ = t) (h13 : Commutes J₁ J₃) (h14 : Commutes J₁ J₄)
    (h23 : Commutes J₂ J₃) (h24 : Commutes J₂ J₄) (h34 : Commutes J₃ J₄)
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hx₃ : ∀ m ∈ J₃, x * m * x⁻¹ ∈ J₃) (hx₄ : ∀ m ∈ J₄, x * m * x⁻¹ ∈ J₄)
    (hx₁ : x * b₁ = b₁ * x) (hx₂ : x * b₂ = b₂ * x)
    (hs : x * (b₁ * b₂ * b₃ * b₄) * x⁻¹ = b₁ * b₂ * b₃ * b₄) :
    (∀ m ∈ J₃, x * m = m * x) ∧ (∀ m ∈ J₄, x * m = m * x) := by
  have hu₃ : x * b₃ * x⁻¹ ∈ J₃ := hx₃ b₃ hb₃
  have hu₄ : x * b₄ * x⁻¹ ∈ J₄ := hx₄ b₄ hb₄
  obtain ⟨u₃, hu₃def⟩ : ∃ u₃, u₃ = x * b₃ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨u₄, hu₄def⟩ : ∃ u₄, u₄ = x * b₄ * x⁻¹ := ⟨_, rfl⟩
  rw [← hu₃def] at hu₃
  rw [← hu₄def] at hu₄
  have hx₁' : x * b₁ * x⁻¹ = b₁ := mul_inv_eq_iff_eq_mul.mpr hx₁
  have hx₂' : x * b₂ * x⁻¹ = b₂ := mul_inv_eq_iff_eq_mul.mpr hx₂
  have e1 : x * (b₁ * b₂ * b₃ * b₄) * x⁻¹ = (x * b₁ * x⁻¹) * (x * b₂ * x⁻¹) * (x * b₃ * x⁻¹) *
      (x * b₄ * x⁻¹) := by group
  rw [e1, hx₁', hx₂', ← hu₃def, ← hu₄def] at hs
  have hu34 : u₃ * u₄ = b₃ * b₄ := by
    have : b₁ * b₂ * (u₃ * u₄) = b₁ * b₂ * (b₃ * b₄) := by
      calc b₁ * b₂ * (u₃ * u₄) = b₁ * b₂ * u₃ * u₄ := by group
        _ = b₁ * b₂ * b₃ * b₄ := hs
        _ = b₁ * b₂ * (b₃ * b₄) := by group
    exact mul_left_cancel this
  have hb₃i : b₃⁻¹ ∈ J₃ := J₃.inv_mem hb₃
  have hb₄i : b₄⁻¹ ∈ J₄ := J₄.inv_mem hb₄
  have hc34 : (u₃ * b₃⁻¹) * (u₄ * b₄⁻¹) = 1 := by
    have h1 : b₃⁻¹ * u₄ = u₄ * b₃⁻¹ := h34 _ hb₃i _ hu₄
    have hbb : b₃ * b₄ = b₄ * b₃ := h34 _ hb₃ _ hb₄
    calc (u₃ * b₃⁻¹) * (u₄ * b₄⁻¹) = u₃ * (b₃⁻¹ * u₄) * b₄⁻¹ := by group
      _ = u₃ * (u₄ * b₃⁻¹) * b₄⁻¹ := by rw [h1]
      _ = (u₃ * u₄) * (b₃⁻¹ * b₄⁻¹) := by group
      _ = (b₃ * b₄) * (b₃⁻¹ * b₄⁻¹) := by rw [hu34]
      _ = 1 := by
          have : b₃⁻¹ * b₄⁻¹ = (b₄ * b₃)⁻¹ := by group
          rw [this, ← hbb]; group
  have hc3 : u₃ * b₃⁻¹ ∈ J₃ := J₃.mul_mem hu₃ hb₃i
  have hc4 : u₄ * b₄⁻¹ ∈ J₄ := J₄.mul_mem hu₄ hb₄i
  have hc3eq : u₃ * b₃⁻¹ = (u₄ * b₄⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hc34
  have hc4eq : u₄ * b₄⁻¹ = (u₃ * b₃⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hc34
  have hz3 : u₃ * b₃⁻¹ = 1 ∨ u₃ * b₃⁻¹ = t := by
    refine hq₃.center _ hc3 fun g hg => ?_
    rw [hc3eq]
    exact (h34 g hg _ (J₄.inv_mem hc4)).symm
  have hz4 : u₄ * b₄⁻¹ = 1 ∨ u₄ * b₄⁻¹ = t := by
    refine hq₄.center _ hc4 fun g hg => ?_
    rw [hc4eq]
    exact (h34 _ (J₃.inv_mem hc3) g hg)
  have ht3 : t * b₃ = b₃ * t := hq₃.z_central b₃ hb₃
  have ht4 : t * b₄ = b₄ * t := hq₄.z_central b₄ hb₄
  constructor
  · refine hq₃.cent_of_fix hxo hxt hx₃ hb₃ hb₃2 ?_
    unfold ZFix
    rw [← hu₃def]
    have : u₃ = (u₃ * b₃⁻¹) * b₃ := by group
    rcases hz3 with h | h
    · left; rw [this, h, one_mul]
    · right; rw [this, h, ht3]
  · refine hq₄.cent_of_fix hxo hxt hx₄ hb₄ hb₄2 ?_
    unfold ZFix
    rw [← hu₄def]
    have : u₄ = (u₄ * b₄⁻¹) * b₄ := by group
    rcases hz4 with h | h
    · left; rw [this, h, one_mul]
    · right; rw [this, h, ht4]

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
