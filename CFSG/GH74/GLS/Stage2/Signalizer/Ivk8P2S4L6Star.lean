module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Act

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
open scoped commutatorElement

@[expose] def KStarL34 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .PSL 3 2 2 → IsSimpleGroup Y →
    ∀ α : MulAut Y, α * α = 1 → α ≠ 1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P → P ≠ ⊥ → (∀ e ∈ P, e * α = α * e) →
        (∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) →
        p = 3 ∧ UnitaryFix α ∧ Nat.card ↥P = 9 ∧ α ∉ innSub Y

@[expose] def KNoOrder3L34 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .PSL 3 2 2 → IsSimpleGroup Y →
    ∀ t b : Y, t * t = 1 → t ≠ 1 → orderOf b = 3 → t * b ≠ b * t

variable {G : Type} [Group G]

theorem mem_normalizer_inf' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩, fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

theorem pbar_data [Finite G] {J : Subgroup G} (hq : IsQuasisimple ↥J)
    (hZ : Odd (Nat.card (center ↥J))) {z : G} (hzN : z ∈ normalizer (J : Set G)) (hz2 : z * z = 1)
    (hJz : ⁅J, zpowers z⁆ = J) {p : ℕ} {P : Subgroup G} (hPN : P ≤ normalizer (J : Set G))
    (hPp : IsPGroup p ↥P) (hPnc : ¬ P ≤ centralizer (J : Set G)) (hPz : ∀ x ∈ P, z * x = x * z)
    (hPnorm : ∀ y ∈ J, y * z = z * y → y ∈ normalizer (P : Set G)) :
    alphaZ J hzN * alphaZ J hzN = 1 ∧ alphaZ J hzN ≠ 1 ∧ IsPGroup p ↥(Pbar J P) ∧
      Pbar J P ≠ ⊥ ∧ (∀ e ∈ Pbar J P, e * alphaZ J hzN = alphaZ J hzN * e) ∧
      ∀ c ∈ fixSub (alphaZ J hzN),
        MulAut.conj c ∈ normalizer ((Pbar J P : Subgroup (MulAut (↥J ⧸ center ↥J))) : Set _) := by
  have hperf : Group.IsPerfect ↥J := hq.1
  have hα2 : alphaZ J hzN * alphaZ J hzN = 1 := by
    rw [← map_mul]
    have : (⟨z, hzN⟩ * ⟨z, hzN⟩ : ↥(normalizer (J : Set G))) = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hα1 : alphaZ J hzN ≠ 1 := by
    intro h
    have hzC : z ∈ centralizer (J : Set G) := (YCfg.yAct_eq_one_iff J ⟨z, hzN⟩).mp h
    have h1 : J ≤ centralizer ((zpowers z : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hzC)
    have h2 : ⁅J, zpowers z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [hJz] at h2
    have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this h2
  refine ⟨hα2, hα1, isPGroup_Pbar hPp, Pbar_ne_bot hPN hPnc,
    fun e he => comm_Pbar hzN hPz he, ?_⟩
  intro c hcfix
  obtain ⟨y, hyz, hyc⟩ := lift_fixed_of_card_odd J hzN hz2 hZ hcfix
  have hy : (y : G) ∈ normalizer (P : Set G) := hPnorm (y : G) y.2 hyz
  rw [← hyc]
  exact conj_mem_normalizer_Pbar hy

theorem star_J [Finite G] (hstar : KStarL34) {J : Subgroup G} (hq : IsQuasisimple ↥J)
    (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 2 2) (hZ : Odd (Nat.card (center ↥J))) {z : G}
    (hzN : z ∈ normalizer (J : Set G)) (hz2 : z * z = 1) (hJz : ⁅J, zpowers z⁆ = J) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPN : P ≤ normalizer (J : Set G))
    (hPp : IsPGroup p ↥P) (hPnc : ¬ P ≤ centralizer (J : Set G)) (hPz : ∀ x ∈ P, z * x = x * z)
    (hPnorm : ∀ y ∈ J, y * z = z * y → y ∈ normalizer (P : Set G)) :
    p = 3 ∧ UnitaryFix (alphaZ J hzN) ∧ Nat.card ↥(Pbar J P) = 9 ∧
      alphaZ J hzN ∉ innSub (↥J ⧸ center ↥J) := by
  obtain ⟨hs, -⟩ := Gen.quasisimple_quot hq
  obtain ⟨hα2, hα1, hPbp, hPb1, hcomm, hnorm⟩ :=
    pbar_data hq hZ hzN hz2 hJz hPN hPp hPnc hPz hPnorm
  exact hstar _ hLie hs _ hα2 hα1 p hp hp2 (Pbar J P) hPbp hPb1 hcomm hnorm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
