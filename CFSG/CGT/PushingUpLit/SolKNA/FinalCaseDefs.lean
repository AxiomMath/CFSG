module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Open

variable {G : Type} [Group G]

abbrev zCenter (R : Subgroup G) : Subgroup G := R ⊓ Subgroup.centralizer (R : Set G)

structure FinalCase (G : Type) [Group G] [Finite G] (R : Subgroup G) (z : G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  two : IsPGroup 2 R
  ti : IsTI R
  max : IsMaximalTwoLocal (Subgroup.normalizer (R : Set G))
  fstar : generalizedFitting (Subgroup.normalizer (R : Set G)) =
    pCore 2 (Subgroup.normalizer (R : Set G))
  z_mem : z ∈ zCenter R
  z_ne : z ≠ 1
  cent_z : Subgroup.centralizer ({z} : Set G) = Subgroup.normalizer (R : Set G)
  Z_sq : ∀ x ∈ zCenter R, x * x = 1
  Z_card : 4 ≤ Nat.card ↥(zCenter R)
  P : ∀ h : G, conjSubgroup h R ≠ R →
    conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥ →
      conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G) ∧
        ∀ a ∈ zCenter R, ∀ b ∈ conjSubgroup h (zCenter R), a * b = b * a
  sq_mem : ∀ h : G, conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥ →
    ∃ y ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G), y * y = h * z * h⁻¹
  invol_mem : ∀ h : G, ∀ t ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G), t * t = 1 →
    t ∈ conjSubgroup h (zCenter R)

theorem conjSubgroup_normalizer (g : G) (H : Subgroup G) :
    conjSubgroup g (Subgroup.normalizer (H : Set G)) =
      Subgroup.normalizer (conjSubgroup g H : Set G) := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have key : ∀ w : G, (w ∈ conjSubgroup g H ↔ x * w * x⁻¹ ∈ conjSubgroup g H) ↔
      (g⁻¹ * w * g ∈ H ↔ (g⁻¹ * x * g) * (g⁻¹ * w * g) * (g⁻¹ * x * g)⁻¹ ∈ H) := by
    intro w
    simp only [mem_conjSubgroup]
    rw [show g⁻¹ * (x * w * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * w * g) * (g⁻¹ * x * g)⁻¹ by group]
  constructor
  · intro hx w
    rw [key w]
    exact hx _
  · intro hx y
    have := hx (g * y * g⁻¹)
    rw [key (g * y * g⁻¹), show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
    exact this

theorem conjSubgroup_centralizer (g : G) (H : Subgroup G) :
    conjSubgroup g (Subgroup.centralizer (H : Set G)) =
      Subgroup.centralizer (conjSubgroup g H : Set G) := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx w hw
    have h1 := hx (g⁻¹ * w * g) (mem_conjSubgroup.mp hw)
    calc w * x = g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = x * w := by group
  · intro hx y hy
    have hy' : g * y * g⁻¹ ∈ conjSubgroup g H := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hy
    have h1 := hx _ hy'
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * y := by group

theorem conjSubgroup_zCenter (g : G) (R : Subgroup G) :
    conjSubgroup g (zCenter R) = zCenter (conjSubgroup g R) := by
  rw [zCenter, zCenter, conjSubgroup_inf, conjSubgroup_centralizer]

theorem normalizer_le_normalizer_zCenter (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (zCenter R : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff, conjSubgroup_zCenter, conjSubgroup_eq_self_iff.mpr hm]

namespace FinalCase

variable [Finite G] {R : Subgroup G} {z : G} (F : FinalCase G R z)
include F

theorem isPGroup_Z : IsPGroup 2 (zCenter R) := F.two.to_le inf_le_left

theorem Z_ne_bot : zCenter R ≠ ⊥ := fun h => F.z_ne (by
  have := F.z_mem
  rw [h, Subgroup.mem_bot] at this
  exact this)

theorem normalizer_Z :
    Subgroup.normalizer (zCenter R : Set G) = Subgroup.normalizer (R : Set G) := by
  by_contra hne
  exact F.max.2 _ (lt_of_le_of_ne (normalizer_le_normalizer_zCenter R) (Ne.symm hne))
    ⟨zCenter R, F.Z_ne_bot, F.isPGroup_Z, rfl⟩

theorem inf_conj_eq_bot {h : G} (hh : conjSubgroup h R ≠ R) : R ⊓ conjSubgroup h R = ⊥ :=
  inf_conjSubgroup_eq_bot_of_isTI F.ti hh

theorem isTI_Z : IsTI (zCenter R) := by
  intro g
  by_cases hg : conjSubgroup g R = R
  · right
    rw [conjSubgroup_zCenter, hg, inf_idem]
  · left
    rw [eq_bot_iff, ← F.inf_conj_eq_bot hg]
    exact inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left)

theorem P_pair {a b : G} (hne : conjSubgroup b R ≠ conjSubgroup a R)
    (hT : conjSubgroup b R ⊓ Subgroup.normalizer (conjSubgroup a R : Set G) ≠ ⊥) :
    conjSubgroup b (zCenter R) ≤ Subgroup.normalizer (conjSubgroup a R : Set G) ∧
      ∀ x ∈ conjSubgroup a (zCenter R), ∀ y ∈ conjSubgroup b (zCenter R), x * y = y * x := by
  have hb : conjSubgroup b R = conjSubgroup a (conjSubgroup (a⁻¹ * b) R) := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  have hne' : conjSubgroup (a⁻¹ * b) R ≠ R := fun h => hne (by rw [hb, h])
  have hT' : conjSubgroup (a⁻¹ * b) R ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥ := by
    intro hbot
    apply hT
    rw [hb, ← conjSubgroup_normalizer, ← conjSubgroup_inf, hbot]
    exact Subgroup.map_bot _
  obtain ⟨h1, h2⟩ := F.P (a⁻¹ * b) hne' hT'
  have hbZ : conjSubgroup b (zCenter R) = conjSubgroup a (conjSubgroup (a⁻¹ * b) (zCenter R)) := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  refine ⟨?_, fun x hx y hy => ?_⟩
  · rw [hbZ, ← conjSubgroup_normalizer]
    exact Subgroup.map_mono h1
  · rw [mem_conjSubgroup] at hx
    rw [hbZ, mem_conjSubgroup] at hy
    have := h2 _ hx _ hy
    calc x * y = a * ((a⁻¹ * x * a) * (a⁻¹ * y * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * y * a) * (a⁻¹ * x * a)) * a⁻¹ := by rw [this]
      _ = y * x := by group

theorem conj_Z_le_normalizer {g : G}
    (hg : g * z * g⁻¹ ∈ Subgroup.normalizer (R : Set G)) :
    conjSubgroup g (zCenter R) ≤ Subgroup.normalizer (R : Set G) := by
  by_cases hR : conjSubgroup g R = R
  · calc conjSubgroup g (zCenter R) ≤ conjSubgroup g R := Subgroup.map_mono inf_le_left
      _ = R := hR
      _ ≤ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer
  · refine (F.P g hR ?_).1
    intro hbot
    have hz1 : g * z * g⁻¹ ∈ conjSubgroup g R := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
      exact (Subgroup.mem_inf.mp F.z_mem).1
    have hz : g * z * g⁻¹ ∈ conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G) :=
      Subgroup.mem_inf.mpr ⟨hz1, hg⟩
    rw [hbot, Subgroup.mem_bot] at hz
    apply F.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hz]; group

end FinalCase

end CFSG.CGT.PushingUpLit.SolKNA
