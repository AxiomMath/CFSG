module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Common
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD2027
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict
public import CFSG.Quasithin.Background.A318PHeis
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionDFT

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.KD1426Common

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

variable {Y : Type} [Group Y] [Finite Y]

theorem card_inf_centralizer_le_nine {K B : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcore : GLAPPrimeCore 3 ↥K = ⊥)
    (hB : IsElemAbelian 3 B)
    (hH : ∀ E : Subgroup Y, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) = ⊥) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) ≤ 9 := by
  classical
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hCB : C ≤ B := inf_le_left
  have hCel : IsElemAbelian 3 C := hB.mono hCB
  by_contra hle
  have h10 : 9 < Nat.card ↥C := Nat.lt_of_not_le hle
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hCel.isPGroup.exists_card_eq
  have h9n : 3 ^ 2 < 3 ^ n := by
    rw [← hn]
    simpa using h10
  have hn3 : 3 ≤ n := by
    have h2 : 2 < n := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h9n
    omega
  have hdvd : 3 ^ 3 ∣ Nat.card ↥C := by
    rw [hn]
    exact pow_dvd_pow 3 hn3
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 3 (n := 3) hdvd
  set E : Subgroup Y := E₀.map C.subtype with hEdef
  have hEcard : Nat.card E = 27 := by
    rw [hEdef, Subgroup.card_map_of_injective C.subtype_injective, hE₀]
    norm_num
  have hEC : E ≤ C := hEdef ▸ Subgroup.map_subtype_le E₀
  have hEel : IsElemAbelian 3 E := hCel.mono hEC
  have hEB : E ≤ B := hEC.trans hCB
  have hEK : E ≤ Subgroup.centralizer (K : Set Y) := hEC.trans inf_le_right
  have hfix : K ⊓ Subgroup.centralizer (E : Set Y) = K :=
    inf_eq_left.mpr ((Subgroup.le_centralizer_iff (H := K) (K := E)).mpr hEK)
  have hbot := hH E hEB hEel hEcard
  rw [hfix, glaPLayer_eq_self hq hcore] at hbot
  have hKne : K ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (H := K)).mp (isQuasisimple_nontrivial hq)
  exact hKne hbot

open CFSG.Quasithin.A318P
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.GLTheoremA.KD2027Aux
open CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

theorem unitaryFieldData_of_card {p f : ℕ} {K : Type} [Field K]
    (hp : p.Prime) (hf : 1 ≤ f) (hcard : Nat.card K = (p ^ f) ^ 2) :
    UnitaryFieldData p f K :=
  ⟨hp, hf, by rw [hcard, ← pow_mul, Nat.mul_comm]⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
