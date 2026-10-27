module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ARank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx (B : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  hB : GLAIsBmax 3 B
  hxB : x ∈ B
  hx1 : x ≠ 1
  hL : GLAPComponent 3 (cx x) L
  hBL : B ≤ Subgroup.normalizer (L : Set G)
  hCyc : CycModSylow 3 L
  hXN : cx x ≤ Subgroup.normalizer (L : Set G)
  hZ : Subgroup.center (PQuot 3 L) = ⊥
  hC3 : I2023C3 x L
  hEss : ∃ T : Subgroup G, T ≤ cx x ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
    (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ IsEmpty (T ≃* QuaternionGroup 2)
  h81 : 3 ^ 4 ≤ Nat.card B

namespace Ctx

variable {B : Subgroup G} {x : G} {L : Subgroup G}

theorem hBel (hc : Ctx B x L) : IsElemAbelian 3 B := hc.hB.1

theorem hx3 (hc : Ctx B x L) : x ^ 3 = 1 := hc.hBel.2 x hc.hxB

theorem hBcx (hc : Ctx B x L) : B ≤ cx x := isElemAbelian_le_centralizer hc.hBel hc.hxB

theorem hLX (hc : Ctx B x L) : L ≤ cx x := hc.hL.1

theorem hxcent (hc : Ctx B x L) : x ∈ Subgroup.centralizer (L : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hc.hLX hl)

theorem hxker (hc : Ctx B x L) : x ∈ centModSubgroup 3 L :=
  centMod_iff.1 (centMod_of_mem_centralizer hc.hxcent)

theorem simple (hc : Ctx B x L) : IsSimpleGroup (PQuot 3 L) := by
  have hq := (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hc.hL).2
  let e : PQuot 3 L ≃* PQuot 3 L ⧸ Subgroup.center (PQuot 3 L) :=
    (QuotientGroup.quotientBot (G := PQuot 3 L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hc.hZ.symm)
  exact (MulEquiv.isSimpleGroup_congr e).2 hq

theorem hOL (hc : Ctx B x L) : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 (cx x) := by
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hc.hL.2.1]
  exact inf_le_right

theorem card_B (hc : Ctx B x L) (F : TD4Rank (PQuot 3 L)) : Nat.card B = 81 :=
  le_antisymm (card_le_81 hc.hCyc hc.hZ F hc.hBL hc.hBel) (by simpa using hc.h81)

theorem rank_eq (hc : Ctx B x L) (F : TD4Rank (PQuot 3 L)) :
    Nat.card (rhoSub L B hc.hBL).range = 27 ∧ Nat.card (rhoSub L B hc.hBL).ker = 3 ∧
      Nat.card ↥((rhoSub L B hc.hBL).range ⊓ innerAutS (PQuot 3 L)) = 9 := by
  obtain ⟨h1, h2, h3, h4⟩ := rank_bounds hc.hCyc hc.hZ F hc.hBL hc.hBel
  rw [hc.card_B F] at h1
  set r := Nat.card (rhoSub L B hc.hBL).range with hr
  set k := Nat.card (rhoSub L B hc.hBL).ker with hk
  set i := Nat.card ↥((rhoSub L B hc.hBL).range ⊓ innerAutS (PQuot 3 L)) with hi
  have hr27 : r ≤ 27 := by omega
  have hk3 : k = 3 := by
    interval_cases k <;> omega
  have hr27' : r = 27 := by
    rw [hk3] at h1
    omega
  exact ⟨hr27', hk3, by omega⟩

end Ctx

theorem mem_of_pow_coprime {H : Subgroup G} {t : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (h1 : t ^ a = 1) (h2 : t ^ b ∈ H) : t ∈ H := by
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (a : ℤ) * u + (b : ℤ) * v = 1 := by
    have h := Nat.gcd_eq_gcd_ab a b
    rw [Nat.Coprime.gcd_eq_one hab] at h
    exact ⟨Nat.gcdA a b, Nat.gcdB a b, by exact_mod_cast h.symm⟩
  have e : t = (t ^ a) ^ u * (t ^ b) ^ v := by
    rw [← zpow_natCast t a, ← zpow_natCast t b, ← zpow_mul, ← zpow_mul, ← zpow_add, huv, zpow_one]
  rw [e, h1, one_zpow, one_mul]
  exact Subgroup.zpow_mem _ h2 v

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
