module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXExtraspecialOrthogonalAction
public import CFSG.RankThree.GroupTheory.SteinbergBYExtraspecialKernelFactors

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons.SteinbergCG

open Subgroup CFSG.RankThree.GroupTheory.SteinbergBY
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped IsMulCommutative

section CoreOrth

variable {H : Type*} [Group H] {z : CFSG.pCore 2 H}
  [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))]

@[expose] noncomputable def coreOrth (HQ : CommPairHyp (CFSG.pCore 2 H) z)
    (hz : center (CFSG.pCore 2 H) = zpowers z) : H →* orthogonalGroup (sqQuad HQ hz) :=
  (autLinHom.comp MulAut.conjNormal).codRestrict _ fun h =>
    autLin_mem_orthogonalGroup HQ hz (MulAut.conjNormal h)

theorem coreOrth_apply (HQ : CommPairHyp (CFSG.pCore 2 H) z)
    (hz : center (CFSG.pCore 2 H) = zpowers z) (h : H)
    (w : Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :
    ((coreOrth HQ hz h : orthogonalGroup (sqQuad HQ hz)) :
      Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) ≃ₗ[ZMod 2] _) w =
      Additive.ofMul (centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h) w.toMul) :=
  rfl

theorem coreOrth_eq_one_iff (HQ : CommPairHyp (CFSG.pCore 2 H) z)
    (hz : center (CFSG.pCore 2 H) = zpowers z) (h : H) :
    coreOrth HQ hz h = 1 ↔ centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h) = 1 := by
  constructor
  · intro h1
    ext v
    have h2 := LinearEquiv.congr_fun (congrArg Subtype.val h1) (Additive.ofMul v)
    rw [coreOrth_apply] at h2
    exact Additive.ofMul.injective h2
  · intro h1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    rw [coreOrth_apply, h1]
    rfl

theorem ker_coreOrth [Finite H] (hH : CFSG.IsCharacteristicP 2 H)
    (hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 H)) (HQ : CommPairHyp (CFSG.pCore 2 H) z)
    (hz : center (CFSG.pCore 2 H) = zpowers z) : (coreOrth HQ hz).ker = CFSG.pCore 2 H := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨ι, hι, hιh⟩, -⟩ :=
    extraspecial_centralizer_orthogonal_action hH hQ hz
  ext h
  rw [MonoidHom.mem_ker, coreOrth_eq_one_iff, ← hιh,
    ← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 H)]
  constructor
  · intro h1
    apply hι
    rw [map_one]
    exact Subtype.ext h1
  · intro h1
    rw [h1, map_one]
    rfl

theorem index_eq_card_range [Finite H] (hH : CFSG.IsCharacteristicP 2 H)
    (hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 H)) (HQ : CommPairHyp (CFSG.pCore 2 H) z)
    (hz : center (CFSG.pCore 2 H) = zpowers z) :
    (CFSG.pCore 2 H).index = Nat.card (coreOrth HQ hz).range := by
  have h := ker_coreOrth hH hQ HQ hz
  calc (CFSG.pCore 2 H).index = (coreOrth HQ hz).ker.index := by rw [h]
    _ = Nat.card (coreOrth HQ hz).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (coreOrth HQ hz)).toEquiv

end CoreOrth

theorem exists_center_eq_zpowers {Q : Type*} [Group Q] (h2 : Nat.card (center Q) = 2) :
    ∃ z : Q, center Q = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isCyclic_of_prime_card h2
  obtain ⟨⟨z, hzc⟩, hg⟩ := IsCyclic.exists_generator (α := center Q)
  refine ⟨z, le_antisymm (fun x hx => ?_) (zpowers_le.mpr hzc)⟩
  obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem finrank_quotient_center {Q : Type*} [Group Q] [Finite Q]
    [CFSG.IsElementaryAbelian 2 (Q ⧸ center Q)] (hQ : IsExtraspecialPGroup 2 Q) {w : ℕ}
    (hcard : Nat.card Q = 2 ^ (1 + 2 * w)) :
    Module.finrank (ZMod 2) (Additive (Q ⧸ center Q)) = 2 * w := by
  have h1 := card_eq_card_quotient_mul_card_subgroup (center Q)
  rw [hcard, hQ.2.2.2, pow_add, pow_one, mul_comm] at h1
  have hV : Nat.card (Q ⧸ center Q) = 2 ^ (2 * w) := (Nat.eq_of_mul_eq_mul_right two_pos h1).symm
  have : Finite (Additive (Q ⧸ center Q)) := inferInstanceAs (Finite (Q ⧸ center Q))
  have h2 : Nat.card (Additive (Q ⧸ center Q)) =
      Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive (Q ⧸ center Q)) :=
    Module.natCard_eq_pow_finrank
  rw [Nat.card_zmod, show Nat.card (Additive (Q ⧸ center Q)) = 2 ^ (2 * w) from hV] at h2
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

end CFSG.LocalAnalysis.GorensteinLyons.SteinbergCG
