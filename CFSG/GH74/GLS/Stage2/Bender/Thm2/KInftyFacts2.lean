module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Bstar

variable {G : Type} [Group G]

@[expose] def Bstar (B : Subgroup G) (x : G) (hx : ∀ b ∈ B, b * x = x * b) : Subgroup G where
  carrier := {y | ∃ b ∈ B, ∃ j : ℤ, y = b * x ^ j}
  one_mem' := ⟨1, one_mem _, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨b₁, hb₁, j₁, rfl⟩ ⟨b₂, hb₂, j₂, rfl⟩
    refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, j₁ + j₂, ?_⟩
    have hc : x ^ j₁ * b₂ = b₂ * x ^ j₁ :=
      ((show Commute x b₂ from (hx b₂ hb₂).symm).zpow_left j₁).eq
    calc b₁ * x ^ j₁ * (b₂ * x ^ j₂) = b₁ * (x ^ j₁ * b₂) * x ^ j₂ := by group
      _ = b₁ * (b₂ * x ^ j₁) * x ^ j₂ := by rw [hc]
      _ = b₁ * b₂ * x ^ (j₁ + j₂) := by rw [zpow_add]; group
  inv_mem' := by
    rintro _ ⟨b, hb, j, rfl⟩
    refine ⟨b⁻¹, inv_mem hb, -j, ?_⟩
    have hc : x ^ (-j) * b⁻¹ = b⁻¹ * x ^ (-j) :=
      ((show Commute x b⁻¹ from Commute.inv_right (show Commute x b from (hx b hb).symm)).zpow_left (-j)).eq
    calc (b * x ^ j)⁻¹ = x ^ (-j) * b⁻¹ := by rw [mul_inv_rev, zpow_neg]
      _ = b⁻¹ * x ^ (-j) := hc

variable {B : Subgroup G} {x : G} {hx : ∀ b ∈ B, b * x = x * b}

theorem le_Bstar : B ≤ Bstar B x hx := fun b hb => ⟨b, hb, 0, by simp⟩

theorem x_mem_Bstar : x ∈ Bstar B x hx := ⟨1, one_mem _, 1, by simp⟩

theorem Bstar_le {P : Subgroup G} (hBP : B ≤ P) (hxP : x ∈ P) : Bstar B x hx ≤ P := by
  rintro _ ⟨b, hb, j, rfl⟩
  exact mul_mem (hBP hb) (zpow_mem hxP j)

theorem comm_mul_right_eq {a u c : G} (h : Commute u c) : ⁅a * u, c⁆ = ⁅a, c⁆ := by
  have h1 : u * c * u⁻¹ = c := by rw [h.eq]; group
  calc ⁅a * u, c⁆ = a * (u * c * u⁻¹) * a⁻¹ * c⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, c⁆ := by rw [h1]; simp only [commutatorElement_def]

theorem comm_mul_left_eq {a c u : G} (h : Commute u a) : ⁅a, c * u⁆ = ⁅a, c⁆ := by
  have h1 : u * a⁻¹ * u⁻¹ = a⁻¹ := by rw [h.inv_right.eq]; group
  calc ⁅a, c * u⁆ = a * c * (u * a⁻¹ * u⁻¹) * c⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, c⁆ := by rw [h1]; simp only [commutatorElement_def]

theorem Bstar_commutator {y₁ y₂ : G} (h₁ : y₁ ∈ Bstar B x hx) (h₂ : y₂ ∈ Bstar B x hx) :
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, ⁅y₁, y₂⁆ = ⁅b₁, b₂⁆ := by
  obtain ⟨b₁, hb₁, j₁, rfl⟩ := h₁
  obtain ⟨b₂, hb₂, j₂, rfl⟩ := h₂
  refine ⟨b₁, hb₁, b₂, hb₂, ?_⟩
  have hc1 : Commute (x ^ j₁) (b₂ * x ^ j₂) :=
    Commute.mul_right ((show Commute x b₂ from (hx b₂ hb₂).symm).zpow_left j₁) ((Commute.refl x).zpow_zpow j₁ j₂)
  have hc2 : Commute (x ^ j₂) b₁ := (show Commute x b₁ from (hx b₁ hb₁).symm).zpow_left j₂
  rw [comm_mul_right_eq hc1, comm_mul_left_eq hc2]

theorem Bstar_classTwo {P : Subgroup G} (hB : B ∈ classTwo P) (hxP : x ∈ P) :
    Bstar B x hx ∈ classTwo P := by
  refine ⟨Bstar_le hB.1 hxP, ?_⟩
  have hBB : ⁅B, B⁆ ≤ B := commutator_le_of_normalizes Subgroup.le_normalizer
  have h1 : ⁅Bstar B x hx, Bstar B x hx⁆ ≤ ⁅B, B⁆ := by
    rw [Subgroup.commutator_le]
    intro y₁ h₁ y₂ h₂
    obtain ⟨b₁, hb₁, b₂, hb₂, e⟩ := Bstar_commutator h₁ h₂
    rw [e]
    exact Subgroup.commutator_mem_commutator hb₁ hb₂
  have h2 : ⁅B, B⁆ ≤ centralizer ((Bstar B x hx : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, j, rfl⟩
    have hwB : w ∈ B := hBB hw
    have hbw : b * w = w * b :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hB.2 hw) b hb
    have hwxj : w * x ^ j = x ^ j * w := ((show Commute w x from hx w hwB).zpow_right j).eq
    calc b * x ^ j * w = b * (x ^ j * w) := by group
      _ = b * (w * x ^ j) := by rw [← hwxj]
      _ = (b * w) * x ^ j := by group
      _ = (w * b) * x ^ j := by rw [hbw]
      _ = w * (b * x ^ j) := by group
  rw [eq_bot_iff]
  calc ⁅⁅Bstar B x hx, Bstar B x hx⁆, Bstar B x hx⁆ ≤ ⁅⁅B, B⁆, Bstar B x hx⁆ :=
        Subgroup.commutator_mono h1 le_rfl
    _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h2
    _ ≤ ⊥ := le_rfl

theorem zOf_le_zOf_Bstar : zOf B ≤ zOf (Bstar B x hx) := by
  intro w hw
  refine ⟨le_Bstar hw.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨b, hb, j, rfl⟩
  have hbw : b * w = w * b := Subgroup.mem_centralizer_iff.mp hw.2 b hb
  have hwxj : w * x ^ j = x ^ j * w := ((show Commute w x from hx w hw.1).zpow_right j).eq
  calc b * x ^ j * w = b * (x ^ j * w) := by group
    _ = b * (w * x ^ j) := by rw [← hwxj]
    _ = (b * w) * x ^ j := by group
    _ = (w * b) * x ^ j := by rw [hbw]
    _ = w * (b * x ^ j) := by group

@[expose] def qCommSub (Z Q : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ centralizer (Z : Set G) ∧ ∀ q ∈ Q, ⁅y, q⁆ ∈ Z}
  one_mem' := ⟨one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun q hq => ?_⟩
    have e : ⁅a * b, q⁆ = (a * ⁅b, q⁆ * a⁻¹) * ⁅a, q⁆ := by simp only [commutatorElement_def]; group
    have hc : a * ⁅b, q⁆ * a⁻¹ = ⁅b, q⁆ := by
      have := Subgroup.mem_centralizer_iff.mp ha _ (hb' q hq)
      rw [← this]
      group
    rw [e, hc]
    exact mul_mem (hb' q hq) (ha' q hq)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun q hq => ?_⟩
    have e : ⁅a⁻¹, q⁆ = a⁻¹ * ⁅a, q⁆⁻¹ * a := by simp only [commutatorElement_def]; group
    have hc : a⁻¹ * ⁅a, q⁆⁻¹ * a = ⁅a, q⁆⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (inv_mem ha) _ (inv_mem (ha' q hq))
      rw [← this]
      group
    rw [e, hc]
    exact inv_mem (ha' q hq)

theorem mem_qCommSub {Z Q : Subgroup G} {y : G} :
    y ∈ qCommSub Z Q ↔ y ∈ centralizer (Z : Set G) ∧ ∀ q ∈ Q, ⁅y, q⁆ ∈ Z := Iff.rfl

theorem Bstar_mem_Kup {P Q : Subgroup G} (hB : B ∈ Kup P Q) (hxP : x ∈ P)
    (hxQ : ∀ q ∈ Q, ⁅x, q⁆ ∈ zOf B) : Bstar B x hx ∈ Kup P Q := by
  refine ⟨Bstar_classTwo hB.1 hxP, ?_⟩
  refine le_trans ?_ zOf_le_zOf_Bstar
  have hBW : B ≤ qCommSub (zOf B) Q := fun b hb => by
    refine mem_qCommSub.mpr ⟨?_, fun q hq => hB.2 (Subgroup.commutator_mem_commutator hb hq)⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp hw.2 b hb).symm
  have hxW : x ∈ qCommSub (zOf B) Q := by
    refine mem_qCommSub.mpr ⟨?_, hxQ⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hx w hw.1)
  have hle : Bstar B x hx ≤ qCommSub (zOf B) Q := by
    rintro _ ⟨b, hb, j, rfl⟩
    exact mul_mem (hBW hb) (zpow_mem hxW j)
  rw [Subgroup.commutator_le]
  intro y hy q hq
  exact (mem_qCommSub.mp (hle hy)).2 q hq

end Bstar

end CFSG.GH74.GLS.Stage2.Bender.Thm2
