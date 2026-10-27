module

public import CFSG.CGT.PushingUpLit.SixThreeBasic
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.CGT.PushingUpLit.Defs

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

namespace SixThree

variable {G : Type} [Group G]

theorem oTwoIn_le (X : Subgroup G) : oTwoIn X ≤ X := Subgroup.map_subtype_le _

theorem isPGroup_oTwoIn (X : Subgroup G) : IsPGroup 2 (oTwoIn X) :=
  (pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype

theorem normalizer_le_normalizer_oTwoIn (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oTwoIn X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_oTwoIn hg hh, fun hh => ?_⟩
  have := conj_mem_oTwoIn (inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem le_normalizer_oTwoIn (X : Subgroup G) : X ≤ Subgroup.normalizer (oTwoIn X : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn X)

theorem le_oTwoIn_of_isPGroup {X N : Subgroup G} (hNX : N ≤ X) (hN : IsPGroup 2 N)
    (hn : X ≤ Subgroup.normalizer (N : Set G)) : N ≤ oTwoIn X := by
  have hnorm : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hp : IsPGroup 2 (N.subgroupOf X) := hN.comap_subtype
  have hle : N.subgroupOf X ≤ pCore 2 ↥X := le_sSup ⟨hnorm, hp⟩
  intro x hx
  exact ⟨⟨x, hNX hx⟩, hle (show (⟨x, hNX hx⟩ : ↥X) ∈ N.subgroupOf X from hx), rfl⟩

theorem commutator_oTwoIn_le (X : Subgroup G) : ⁅oTwoIn X, X⁆ ≤ oTwoIn X :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_oTwoIn X)

theorem map_shortU (Y : Subgroup G) : (shortU ↥Y).map Y.subtype = ⁅oTwoIn Y, Y⁆ := by
  unfold shortU oTwoIn inSubgroup
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem U_le_oTwoIn (Y : Subgroup G) : ⁅oTwoIn Y, Y⁆ ≤ oTwoIn Y := commutator_oTwoIn_le Y

@[expose] def shortCIn (Y : Subgroup G) : Subgroup G := (shortC ↥Y).map Y.subtype

theorem U_comm {Y : Subgroup G} [Finite G] (hY : IsShortGroup ↥Y) :
    ∀ u ∈ ⁅oTwoIn Y, Y⁆, ∀ w ∈ ⁅oTwoIn Y, Y⁆, u * w = w * u := by
  rw [← map_shortU]
  rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩
  have hup : shortU ↥Y ≤ pCore 2 ↥Y := Subgroup.commutator_le_left _ _
  obtain ⟨z, hz, hzu⟩ := hY.U_le_center hu
  have hwp : w ∈ pCore 2 ↥Y := hup hw
  have h1 : (⟨w, hwp⟩ : ↥(pCore 2 ↥Y)) * z = z * ⟨w, hwp⟩ := Subgroup.mem_center_iff.mp hz _
  have h2 : w * u = u * w := by
    have h3 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h3
    have h4 : (z : ↥Y) = u := hzu
    rw [h4] at h3
    exact h3
  exact congrArg Subtype.val h2.symm

theorem shortCIn_le_U (Y : Subgroup G) : shortCIn Y ≤ ⁅oTwoIn Y, Y⁆ := by
  rw [← map_shortU]
  exact Subgroup.map_mono inf_le_left

theorem shortCIn_le_centralizer (Y : Subgroup G) :
    shortCIn Y ≤ Subgroup.centralizer (Y : Set G) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := Subgroup.mem_center_iff.mp hc.2 ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem irreducible_ambient {Y N : Subgroup G} [Finite G] (hY : IsShortGroup ↥Y)
    (hNU : N ≤ ⁅oTwoIn Y, Y⁆) (hCN : shortCIn Y ≤ N) (hYN : Y ≤ Subgroup.normalizer (N : Set G)) :
    N = shortCIn Y ∨ N = ⁅oTwoIn Y, Y⁆ := by
  have hNY : N ≤ Y := hNU.trans ((U_le_oTwoIn Y).trans (oTwoIn_le Y))
  have hnorm : (N.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN
  have h1 : N.subgroupOf Y ≤ shortU ↥Y := by
    intro x hx
    have hxN : (x : G) ∈ N := hx
    have hxU : (x : G) ∈ (shortU ↥Y).map Y.subtype := by
      rw [map_shortU]
      exact hNU hxN
    obtain ⟨u, hu, hux⟩ := hxU
    have : u = x := Subtype.ext hux
    rwa [this] at hu
  have h2 : shortC ↥Y ≤ N.subgroupOf Y := by
    intro c hc
    exact hCN ⟨c, hc, rfl⟩
  rcases hY.irreducible _ hnorm h1 h2 with h | h
  · left
    have := congrArg (Subgroup.map Y.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hNY] at this
  · right
    have := congrArg (Subgroup.map Y.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hNY, map_shortU] at this

theorem commutator_eq_U [Finite G] {Y V : Subgroup G} (hY : IsShortGroup ↥Y)
    (hV : IsPGroup 2 V) (hVY : Y ≤ Subgroup.normalizer (V : Set G)) (hle : ⁅V, Y⁆ ≤ oTwoIn Y)
    (hne : ⁅V, Y⁆ ≠ ⊥) : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆ := by
  have hNo := SubTwo.noTwoQuotient_of_oResidualTwo hY.residual_eq
  set W := ⁅V, Y⁆ with hW
  have hW1 : ⁅W, Y⁆ = W := commutator_commutator_eq hNo hV hVY
  have hWU : W ≤ ⁅oTwoIn Y, Y⁆ :=
    calc W = ⁅W, Y⁆ := hW1.symm
      _ ≤ ⁅oTwoIn Y, Y⁆ := Subgroup.commutator_mono hle le_rfl
  have hWY : W ≤ Y := hle.trans (oTwoIn_le Y)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_right V Y
  have hCc : shortCIn Y ≤ Subgroup.centralizer (Y : Set G) := shortCIn_le_centralizer Y
  have hYC : Y ≤ Subgroup.normalizer (shortCIn Y : Set G) :=
    (Subgroup.le_centralizer_iff.mp hCc).trans (Subgroup.centralizer_le_normalizer _)
  have hD : Y ≤ Subgroup.normalizer ((W ⊔ shortCIn Y : Subgroup G) : Set G) :=
    le_trans (le_inf hYW hYC) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  rcases irreducible_ambient hY (sup_le hWU (shortCIn_le_U Y)) le_sup_right hD with h | h
  · exfalso
    apply hne
    have h3 : W ≤ Subgroup.centralizer (Y : Set G) := le_sup_left.trans (h.le.trans hCc)
    rw [← hW1]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h3
  · refine le_antisymm hWU ?_
    have hU1 : ⁅⁅oTwoIn Y, Y⁆, Y⁆ = ⁅oTwoIn Y, Y⁆ :=
      commutator_commutator_eq hNo (isPGroup_oTwoIn Y) (le_normalizer_oTwoIn Y)
    have hCW : shortCIn Y ≤ Subgroup.normalizer (W : Set G) := by
      refine hCc.trans ?_
      exact (Subgroup.centralizer_le hWY).trans (Subgroup.centralizer_le_normalizer _)
    have hbot : ⁅shortCIn Y, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCc
    calc ⁅oTwoIn Y, Y⁆ = ⁅⁅oTwoIn Y, Y⁆, Y⁆ := hU1.symm
      _ = ⁅shortCIn Y ⊔ W, Y⁆ := by rw [← h, sup_comm]
      _ ≤ ⁅shortCIn Y, Y⁆ ⊔ W :=
          CFSG.RankThree.PartTwo.Sec6.commutator_sup_le_of_le_normalizer hCW hYW
      _ = W := by rw [hbot, bot_sup_eq]

end SixThree

end CFSG.CGT.PushingUpLit
