module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2Spec
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Module
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Transport
public import CFSG.HardMathSupport.Timmesfeld.LieRank.U43
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverLower
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.HardMathSupport.Timmesfeld.LieRank
  CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

theorem lin_four_leg (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hZ : Nat.card (Subgroup.center L) = 3)
    (hm2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) {X : Type} [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel X t n p f) (ht : t = .PSL ∨ t = .PSU) (hn : 4 ≤ n)
    (hpn : 3 ∣ n) (ha : 3 ∣ (genericOrders t n p f).1) : False := by
  have hZp : IsPGroup 3 (Subgroup.center L) := IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num)
  have hb : ¬ 3 ∣ (genericOrders t n p f).2 := by
    rcases ht with rfl | rfl <;> simp [genericOrders]
  obtain ⟨hc, hd⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.not_three_dvd_exceptional_of_dvd_generic ha
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.rank_ge_of_model hGA hperf
    Nat.prime_three (by norm_num) hZp e hm ht hn ha hb hc hd
  omega

theorem six_le_pRank_of_lieModel_O7 {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) {X : Type} [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) (hm : CFSG.Blueprint.LieModel X .POmegaOdd 3 3 1)
    (hZ : Nat.card (Subgroup.center L) = 3) : 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨e0⟩ := nonempty_mulEquiv_openOmega_of_lieModel hm
  have e' : L ⧸ Subgroup.center L ≃* O7.Om7 := (e.trans e0).trans O7.ProjEquivOm7
  have hlow := CFSG.HardMathSupport.Timmesfeld.SporadicRank.lower_of_cover hq e'
    (by rw [hZ]; norm_num) (by rw [hZ]) O7.modSpec O7.noAlt_O7 O7.noFun_O7
  have hn : O7.modSpec.n = 5 := rfl
  omega

theorem five_le_pRank_of_lieModel_U43 {L : Type} [Group L] [Finite L] {X : Type} [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) (hm : CFSG.Blueprint.LieModel X .PSU 4 3 1)
    (h3 : 3 ∣ Nat.card (Subgroup.center L)) : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨e0⟩ := nonempty_mulEquiv_X₀_of_lieModel hm
  have e' := e.trans e0
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 3 h3
  have hzL : orderOf (z : L) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  let φ : L →* CFSG.LieType.Multipliers.U43.X₀ :=
    (e' : L ⧸ Subgroup.center L →* _).comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext x
    simp [φ]
  have hz3 : (z : L) ^ 3 = 1 := by rw [← hzL]; exact pow_orderOf_eq_one _
  exact five_le_pRank_of_cover φ hφ hker.le (Z := Subgroup.zpowers (z : L))
    (by rw [hker]; exact Subgroup.zpowers_le.mpr z.2)
    (fun w hw => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow])
    (by rw [Nat.card_zpowers, hzL])

section Exceptional


theorem four_le_pRank_of_lieModel_G2 {L : Type} [Group L] [Finite L] {X : Type} [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) (hm : CFSG.Blueprint.LieModel X .G2 0 3 1)
    (h3 : 3 ∣ Nat.card (Subgroup.center L)) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨e0⟩ := nonempty_mulEquiv_adjointGroup_G2_of_lieModel hm
  have e1 := e.trans e0
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e', -⟩ : ∃ e' : L ⧸ Subgroup.center L ≃* RG, True :=
    ⟨e1.trans (Subgroup.equivMapOfInjective _ (glHom (RingEquiv.refl (ZMod 3)))
      (glHom_injective _)), trivial⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 3 h3
  have hzL : orderOf (z : L) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  let φ : L →* RG := (e' : L ⧸ Subgroup.center L →* RG).comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext x
    simp [φ]
  exact four_le_pRank_of_cover_RG φ hφ hker.le (z := (z : L))
    (by rw [hker]; exact z.2) hzL

end Exceptional

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
