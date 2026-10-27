module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXWRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXWSel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXWInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DXW

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.Ree

set_option linter.unusedSectionVars false


private theorem not_three_dvd_two_pow (a : ℕ) : ¬ 3 ∣ 2 ^ (2 * a + 1) - 1 := by
  have h41 : 4 ^ a % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hpow : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
    rw [pow_add, pow_one, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
    ring
  have hmod : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [hpow, Nat.mul_mod, h41]
  intro h
  have h0 : (2 ^ (2 * a + 1) - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have hle : 1 ≤ 2 ^ (2 * a + 1) % 3 := by rw [hmod]; norm_num
  have h1 : (2 ^ (2 * a + 1) - 1) % 3 = 1 := by
    rw [← Nat.mod_sub_of_le hle, hmod]
  exact absurd (h1 ▸ h0) (by norm_num)

private theorem center_reeGamma_eq_bot {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {a : ℕ} {S : Type} [Group S] (hSq : CFSG.Open.IsQuasisimple S)
    (e : S ⧸ Subgroup.center S ≃* ↥(ReeTag.F4.reeGamma K a)) :
    Subgroup.center ↥(ReeTag.F4.reeGamma K a) = ⊥ := by
  haveI : IsSimpleGroup (S ⧸ Subgroup.center S) := hSq.2
  have hnab : ∃ x y : S ⧸ Subgroup.center S, x * y ≠ y * x :=
    CFSG.StandardType.exists_mul_ne_mul_centerQuot_of_perfect hSq.1 inferInstance
  have hZ₀ : Subgroup.center (S ⧸ Subgroup.center S) = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_isSimpleGroup_of_nonabelian hnab
  rw [← Subgroup.map_center_eq e, hZ₀]
  simp

private theorem ree_sel_of_dvd {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S B B₀ T' : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S))
    (hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))
    (hQ : catalogIs (↥S ⧸ Subgroup.center ↥S) t263GRee) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hB₀ : T263HasB0 p S B B₀) (hBel : CFSG.Open.IsElemAbelian p B) (hxB₀ : x ∈ B₀)
    (hBT' : B ≤ Subgroup.normalizer (T' : Set Ω))
    (hxcomm : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥) (hT'S : T' ≤ S)
    (hT'2 : IsPGroup 2 ↥T') {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (hKcard : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (hpq : p ∣ 2 ^ (2 * a + 1) - 1)
    (eΓ : ↥S ⧸ Subgroup.center ↥S ≃* ↥(ReeTag.F4.reeGamma K a)) :
    ∃ J : Subgroup Ω, DX.SelComp p S B₀ T' x J := by
  haveI : Finite ↥(ReeTag.F4.reeGamma K a) := Finite.of_equiv _ eΓ.toEquiv
  have hx : x ∈ B := hB₀.1 hxB₀
  have hxp : x ^ p = 1 := hBel.2 x hx
  have hInn : InnDiagOn p (Subgroup.zpowers x) S :=
    S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hxB₀)
  have hin : InducesInnerMod p S x := inducesInnerMod_of_ree hp hp2 hSn hSq hSp hQ hxp hInn
  have hBab : ∀ c ∈ B, ∀ d ∈ B, c * d = d * c := fun c hc d hd => isElemAbelian_commute hBel hc hd
  have hS₁T' : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤ T' :=
    (DX.norm_data_dx hSn hBab hB₀.1 hxB₀ hBT').2.2
  have hS₁2 : IsPGroup 2 ↥(⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) :=
    hT'2.to_le hS₁T'
  have hB₀C : B₀ ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hBel (hB₀.1 hb) hx
  have hKC : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      Subgroup.centralizer ({x} : Set Ω) :=
    (Subgroup.commutator_mono hB₀C inf_le_right).trans
      (Subgroup.commutator_le_self (Subgroup.centralizer ({x} : Set Ω)))
  have hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω) := le_inf (hS₁T'.trans hT'S) hKC
  have h3 : 3 < p := by
    have hpne3 : p ≠ 3 := fun h => not_three_dvd_two_pow a (h ▸ hpq)
    have hpge : 2 ≤ p := hp.two_le
    omega
  obtain ⟨J, hJ | ⟨hp3, -⟩⟩ := DX.selComp_or_a5_of_modelSel hp hp2 hSn hSq hSp hSc hF2 hxp hxC
    hInn hin hxcomm hS₁S hS₁2 eΓ (modelSel_reeGamma hKcard ha hp h3 hpq)
  · exact ⟨J, hJ⟩
  · exact absurd hp3 (by omega)

private theorem ree_false_of_not_dvd {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S B B₀ T' : Subgroup Ω} (hSn : S.Normal)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hQ : catalogIs (↥S ⧸ Subgroup.center ↥S) t263GRee) (hB₀ : T263HasB0 p S B B₀)
    (hBel : CFSG.Open.IsElemAbelian p B)
    (hcase : p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀)
    (hT'S : T' ≤ S) (hT'2 : IsPGroup 2 ↥T') (hT'ne : T' ≠ ⊥)
    (hBT' : B ≤ Subgroup.normalizer (T' : Set Ω))
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (hKcard : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1)
    (eΓ : ↥S ⧸ Subgroup.center ↥S ≃* ↥(ReeTag.F4.reeGamma K a)) : False := by
  have hB₀el : CFSG.Open.IsElemAbelian p B₀ := isElemAbelian_mono hBel hB₀.1
  have hin₀ : ∀ b ∈ B₀, InducesInnerMod p S b := fun b hb =>
    inducesInnerMod_of_ree hp hp2 hSn hSq hSp hQ (hBel.2 b (hB₀.1 hb))
      (S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hb))
  have hEq : B₀ ⊓ Subgroup.centralizer (S : Set Ω) = B ⊓ Subgroup.centralizer (S : Set Ω) :=
    le_antisymm (inf_le_inf_right _ hB₀.1) (le_inf hB₀.2.2.2.2 inf_le_right)
  have hcard₀ : p * Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀ := by
    rw [hEq]; exact hcase
  exact t263_false_of_inner_rank hp hp2 hSn hSq hSp hB₀el hin₀ hcard₀ hT'S hT'2 hT'ne
    (hB₀.1.trans hBT') eΓ (center_reeGamma_eq_bot hSq eΓ)
    (fun E U hE hU hUne hEN => reeGamma_card_le_of_not_dvd hKcard ha hp hp2 hpq hE hU hUne hEN)

theorem t263SelW_ree : DX.T263SelW t263GRee := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T'
    hT'ne hT'2 hT'S hBT' hker x hxB₀ hxC hxcomm
  classical
  have hBel : CFSG.Open.IsElemAbelian p B := hB.1
  obtain ⟨a, K, _, _, _, ha, hKcard, ⟨eΓ⟩⟩ := K155X.l154_ree_gammaModel hQ
  by_cases hpq : p ∣ 2 ^ (2 * a + 1) - 1
  · exact Or.inr (ree_sel_of_dvd hp hp2 hSn hSq hSp hSc hF2 hQ hxC hB₀ hBel hxB₀ hBT' hxcomm hT'S
      hT'2 hKcard ha hpq eΓ)
  · exact (ree_false_of_not_dvd hp hp2 hSn hSq hSp hQ hB₀ hBel hcase hT'S hT'2 hT'ne hBT'
      hKcard ha hpq eΓ).elim

theorem t263Desc_ree : T263Desc t263GRee :=
  DX.t263Desc_of_selW t263SelW_ree

end CFSG.LocalAnalysis.GLTheoremA.T263.DXW
