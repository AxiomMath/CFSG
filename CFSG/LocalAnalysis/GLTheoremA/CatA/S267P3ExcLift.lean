module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Excess
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankSL2
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM5Lemmas
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.Assembly.RankThreeEven CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank
open scoped MatrixGroups

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem P3Hyp.false_of_liftDatum (H : P3Hyp q S B) {X : Type} [Group X] (e : PSimple 3 S ≃* X)
    (hL : LiftDatum X 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e' : ↥S ⧸ Subgroup.center ↥S ≃* X := (psimpleEquivCenterQuot H).symm.trans e
  set π : ↥S →* X := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S)) with hπdef
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥S := by
    ext y
    rw [MonoidHom.mem_ker]
    change e' (QuotientGroup.mk' (Subgroup.center ↥S) y) = 1 ↔ _
    rw [map_eq_one_iff e' e'.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1
    (CFSG.LocalAnalysis.GLTheoremA.SFM5.isPGroup_center_of_glaPPrimeCore_eq_bot H.core)
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker, ha]
    exact Odd.pow (by decide)
  have hle := H.twoLocalRank_le
  by_cases hZ : Subgroup.center ↥S = ⊥
  ·
    have h4 : 3 + 1 + 0 ≤ localRank 3 ↥S :=
      hL.cover_localRank hπ hker.le hodd (A := ⊥) bot_le
        (fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]) (by rw [Subgroup.card_bot, pow_zero])
    have h4' : 4 ≤ GLATwoLocalRank 3 ↥S := h4
    have hCel : IsElemAbelian 3 (B ⊓ centModSubgroup 3 S) := H.elem.mono inf_le_left
    have hCK : B ⊓ centModSubgroup 3 S ≤ Subgroup.centralizer (S : Set Ω) := fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun s hs => (H.comm_of_mem_centMod hb.2 hs).symm
    have h5 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.le_twoLocalRank_of_central
      Nat.prime_three hCel hCK hZ (by norm_num) h4'
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card Nat.prime_three hCel
      (by rw [H.cent, pow_one])] at h5
    omega
  ·
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hZ (Subgroup.eq_bot_of_card_eq _ (by rw [ha, pow_zero]))
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥S)) 3
      (by rw [ha]; exact dvd_pow_self 3 ha0)
    have hzo : orderOf (z : ↥S) = 3 := by rw [Subgroup.orderOf_coe, hz]
    have h5 : 3 + 1 + 1 ≤ localRank 3 ↥S :=
      hL.cover_localRank hπ hker.le hodd (A := Subgroup.zpowers (z : ↥S))
        (by rw [hker, Subgroup.zpowers_le]; exact z.2)
        (fun x hx => by
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzo,
            pow_orderOf_eq_one, one_zpow])
        (by rw [Nat.card_zpowers, hzo, pow_one])
    have h5' : 5 ≤ GLATwoLocalRank 3 ↥S := h5
    have := CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le
      Nat.prime_three S
    omega

theorem P3Hyp.false_of_commuting_SL2 (H : P3Hyp q S B) {X : Type} [Group X]
    (e : PSimple 3 S ≃* X) {F : Type} [Field F] [Fintype F] (hF2 : ringChar F ≠ 2)
    (hF3 : ringChar F ≠ 3) (φ : Fin 4 → SL(2, F) →* X) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A) : False :=
  H.false_of_liftDatum e (liftDatum_of_commuting_SL2_odd hF2 hF3 (m := 3) φ hφ hcomm)

theorem P3Hyp.false_of_commuting_SL2_fixedField (H : P3Hyp q S B)
    {d : TauCeti.ValidLieTypeIndex} (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hchar : d.1.characteristic = q)
    (φ : Fin 4 → SL(2, d.fixedField) →* (TauCeti.CFSGIndex.lie d).Group)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, d.fixedField), φ i A * φ j B = φ j B * φ i A) :
    False := by
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  haveI : Fact d.characteristic.Prime := ⟨d.characteristic_prime⟩
  haveI : CharP d.fixedField d.characteristic :=
    charP_of_card_eq_prime_pow (f := d.fieldExponent) (by
      rw [← Nat.card_eq_fintype_card, TauCeti.ValidLieTypeIndex.card_fixedField,
        TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow])
  have hc : ringChar d.fixedField = q := (ringChar.eq _ _).trans hchar
  exact H.false_of_commuting_SL2 e (by rw [hc]; exact H.two) (by rw [hc]; exact H.three) φ hφ
    hcomm

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
