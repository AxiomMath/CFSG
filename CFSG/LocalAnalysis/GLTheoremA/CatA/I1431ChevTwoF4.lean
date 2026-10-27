module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_isComponent_of_le_layer)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Dickson.Bal207 (CompShape)
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType isoInvariant_f42CompType
  compShape_F4_two)
open CFSG.Blueprint.Chevalley

theorem card_ne_of_f42CompType {Q : Type} [Group Q] (h : F42CompType Q) :
    Nat.card Q ≠ 25920 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) (by rw [hF]; norm_num)
  have hZ := CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two (K := F) 3
  rw [Nat.card_congr e.toEquiv, hZ,
    show Nat.card (StatedSp 3 F ⧸ (⊥ : Subgroup (StatedSp 3 F))) = Nat.card (StatedSp 3 F) from
      Nat.card_congr QuotientGroup.quotientBot.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  decide

theorem nonempty_centerQuot_equiv_psimple {S : Type} [Group S] [Finite S] {J : Subgroup S}
    (hq : CFSG.Open.IsQuasisimple ↥J) (hn : Nontrivial (PSimple 3 J)) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* PSimple 3 J) := by
  have hPn : Nontrivial (PQuot 3 J) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple 3 J)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    rcases normal_le_center_or_eq_top' hq (GLAPPrimeCore 3 ↥J) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hPn
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [QuotientGroup.eq]
      rw [h]
      exact Subgroup.mem_top _
  exact psimple_equiv_of_central_surj hq _ (QuotientGroup.mk'_surjective _) hker

section F4


theorem u42FieldTwoAt_F4 : U42FieldTwoAt fun d => ∃ q, d = .F4 q := by
  intro Y _ _ _ _ _ ⟨d, hv⟩ ⟨q, hdq⟩ hc hf ⟨e⟩ α _ hP
  subst hdq
  have hq2 : q.card = 2 := hf
  have hp : q.p = 2 := by simpa using hc
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hp (GaloisField 2 1)
    (by rw [hK, hq2])
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 (GaloisField 2 1)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let e' : (Y ⧸ Subgroup.center Y) ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 1)) :=
    e.trans (eB.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  obtain ⟨hα3, hα1, J, hJ, hT⟩ := hP
  have hpow : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hne : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hsh : CompShape F42CompType α :=
    CompShape.of_congr isoInvariant_f42CompType e' (compShape_F4_two hK _ hpow hne)
  have hlay := hsh.layer _ hJ.1 (glaPComponent_perfect hJ)
  have hJc := (glaPComponent_isComponent_of_le_layer hJ hlay).1
  have h25920 : Nat.card (PSimple 3 J) = 25920 := I1431Z.card_eq_of_u4two hT
  haveI : Nontrivial (PSimple 3 J) := by
    rw [← Finite.one_lt_card_iff_nontrivial, h25920]
    norm_num
  obtain ⟨φ⟩ := nonempty_centerQuot_equiv_psimple hJc.2.2 inferInstance
  exact (card_ne_of_f42CompType (hsh.type J hJc)
    (by rw [Nat.card_congr φ.toEquiv, h25920])).elim

end F4

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
