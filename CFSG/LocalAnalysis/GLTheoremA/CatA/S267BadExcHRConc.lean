module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRTypes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267CenterMultiplier
import CFSG.LieType.Steinberg.CentralExt.E6E7Multiplier
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcAutRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Rank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelAGen concA_of_modelAGen)

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_adjointGroup {p : ℕ} (hp : p.Prime) {τ : Tag}
    {K : Type} [Field K] [Finite K] (hr : 3 ≤ τ.rank) (hS : S.Normal)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBle : Nat.card B ≤ p ^ (τ.rank + 1))
    (eX : ↥(adjointGroup τ K) ≃* PSimple p S) (hM : ModelAGen p τ.rank ↥(adjointGroup τ K)) :
    S267ConcA p S B := by
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  set eS : PSimple p S ≃* ↥S := (psimpleEquivCenterQuotOfCore hcore).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with heS
  set φ : ↥(adjointGroup τ K) →* Ω := S.subtype.comp (eX.trans eS).toMonoidHom with hφdef
  have hφ : Function.Injective φ := S.subtype_injective.comp (eX.trans eS).injective
  have hφS : φ.range = S := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (eX.trans eS).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact concA_of_modelAGen hp hr hS hcore hZ hB hBC hBle φ hφ hφS hM

theorem center_eq_bot_of_adjointGroup
    {p : ℕ} (hp : p.Prime)
    (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥) {τ : Tag} {K : Type} [Field K]
    [Finite K] (eX : ↥(adjointGroup τ K) ≃* PSimple p S)
    (hM : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient τ K))) :
    Subgroup.center ↥S = ⊥ :=
  center_eq_bot_of_multiplier hp hperf hcore (eX.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).symm) hM

theorem card_le_pow_add_two_of_hom {p r : ℕ} (hp : p.Prime) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {X C : Type}
    [Group X] [Finite X] [Group C] [IsCyclic C] (eX : X ≃* PSimple p S)
    (hZX : Subgroup.center X = ⊥) (Θ : MulAut X →* C)
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : X →* MulAut X).range)
    (hX : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card F ≤ p ^ r) :
    Nat.card B ≤ p ^ (r + 2) := by
  haveI : Finite (PSimple p S) := Finite.of_equiv X eX.toEquiv
  have hZ : Subgroup.center (PSimple p S) = ⊥ := by
    rw [← Subgroup.map_center_eq eX, hZX, Subgroup.map_bot]
  have hrk := pRank_mulAut_le_of_hom eX.symm Θ (f := p) hp hΘ
    (CFSG.LocalAnalysis.RankFourTheoremC.conj_injective_of_center_eq_bot hZ)
    (card_le_of_mulEquiv eX.symm hX) (fun h => absurd (dvd_refl p) h)
  rw [if_pos (dvd_refl p)] at hrk
  exact card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC hrk

theorem card_le_or_eq_of_le {p r : ℕ} (hp : p.Prime) (hB : IsElemAbelian p B)
    (hle : Nat.card B ≤ p ^ (r + 2)) :
    Nat.card B ≤ p ^ (r + 1) ∨ Nat.card B = p ^ (r + 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p B := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hB.2 x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  rw [hk] at hle ⊢
  have hk2 : k ≤ r + 2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  rcases (by omega : k ≤ r + 1 ∨ k = r + 2) with h | h
  · exact Or.inl (Nat.pow_le_pow_right hp.pos h)
  · exact Or.inr (by rw [h])

theorem card_le_pow_rank_add_two_F4
    {p : ℕ} (hp : p.Prime) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower} {K : Type} [Field K]
    [Finite K] [CharP K Q.p] (hKQ : Nat.card K = Q.card)
    (eX : ↥(adjointGroup .F4 K) ≃* PSimple p S)
    (hX : ∀ F : Subgroup ↥(adjointGroup .F4 K), IsElemAbelian p F → Nat.card F ≤ p ^ Tag.F4.rank) :
    Nat.card B ≤ p ^ (Tag.F4.rank + 2) := by
  haveI : Finite ↥(adjointGroup .F4 K) := generated_group_finite .F4 K
  obtain ⟨C, _, _, Θ, -, hker⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_cyclic_F4 Q K hKQ
  exact card_le_pow_add_two_of_hom hp hS hperf hB hBC eX center_adjointGroup_eq_bot Θ
    (fun x hx _ => by rw [hker] at hx; exact hx) hX

theorem card_le_pow_rank_E6_of_dvd_sub_one
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) (F : Subgroup ↥(adjointGroup .E6 K)) (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ Tag.E6.rank :=
  CFSG.StandardType.GGExcToralRankInput.card_le
    (CFSG.StandardType.TableBExc.ggExcToralRankInput_E6_of_ne_three hp (by omega) (by omega) hpq)
    (CFSG.StandardType.TableBExc.card_torusPow_E6 hp (by omega) hpq) hF

theorem five_le_card_of_dvd_sub_one {K : Type} [Finite K] [Nontrivial K] {p : ℕ} (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K - 1) : 5 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have := Nat.le_of_dvd (by omega) hpK
  omega

theorem not_dvd_of_dvd_three {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ∣ 3) : ¬ p ∣ n :=
  fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans hn)
    omega

section HeadE6

theorem concA_badExcCore_E6_of_dvd_sub_one_of_card_le {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hp5 : 5 ≤ p)
    (hdvd : p ∣ Q.card - 1) (hBle : Nat.card B ≤ p ^ (Tag.E6.rank + 1)) : S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E6] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K - 1 := by rwa [hK]
  obtain ⟨ζ, hζ⟩ := CFSG.StandardType.TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpK
  have hK5 := five_le_card_of_dvd_sub_one hp5 hpK
  set eX : ↥(adjointGroup .E6 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact not_dvd_of_dvd_three hp hp5 (Nat.gcd_dvd_left 3 _))
  exact concA_of_adjointGroup hp (by decide) hS hcore hZ hB hBC hBle eX
    (modelAGen_E6 hK2 hp hp5 hζ)

end HeadE6

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end

