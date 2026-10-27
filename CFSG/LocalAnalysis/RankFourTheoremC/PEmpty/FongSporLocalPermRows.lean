module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimpleSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSecSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.M24Surj
public import Certificates.Certificate40260

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint Subgroup

theorem secW_of_check {G : Type} [Group G] [DecidableEq G] (cn : G → G) (hcn : ∀ x, cn x = x)
    (a b : G) (c : PSec) (hp : c.base.p.Prime) (h : c.check cn a b = true) :
    SecW ↥(Subgroup.closure ({a, b} : Set G)) c.base.p := by
  unfold PSec.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hb, hs⟩ := h
  simp only [hcn] at hs
  obtain ⟨h1, h2, h3, h4⟩ := PSimple.sound c.simple _ _ _ hs
  exact secW_exists_of_parts a b c hp (PGen.holdsBase_of_checkBase a b c.base hb) ⟨h1, h2, h3, h4⟩

theorem genW_M24_7 : GenW ↥NativeSporadic.M24 7 :=
  genW_exists_of_holds PermGens.m24a PermGens.m24b m24_7_claims (by show Nat.Prime 7; norm_num)
    (PGen.holds_of_check _ _ _ Certificates.certificate40260.1)

theorem secW_M12_5 : SecW ↥NativeSporadic.M12 5 :=
  secW_of_check canonPerm canonPerm_eq PermGens.m12a PermGens.m12b m12_5_claims (by show Nat.Prime 5; norm_num)
    Certificates.certificate40260.2.1

theorem secW_M23_7 : SecW ↥NativeSporadic.M23 7 :=
  secW_of_check canonPerm canonPerm_eq PermGens.m23a PermGens.m23b m23_7_claims (by show Nat.Prime 7; norm_num)
    Certificates.certificate40260.2.2.1

theorem secW_M24_5 : SecW ↥NativeSporadic.M24 5 :=
  secW_of_check canonPerm canonPerm_eq PermGens.m24a PermGens.m24b m24_5_claims (by show Nat.Prime 5; norm_num)
    Certificates.certificate40260.2.2.2

theorem row_M24_7 :
    KFactSporLocalRow .M24 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have hW : GenW G 7 := GenW.of_mulEquiv (b.trans e.symm) genW_M24_7
  have hcard : Nat.card G = 244823040 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  exact (false_of_genW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl hK).elim

theorem row_M12_5 :
    KFactSporLocalRow .M12 5 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have hW : SecW G 5 := SecW.of_mulEquiv (b.trans e.symm) secW_M12_5
  have hcard : Nat.card G = 95040 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

theorem row_M23_7 :
    KFactSporLocalRow .M23 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have hW : SecW G 7 := SecW.of_mulEquiv (b.trans e.symm) secW_M23_7
  have hcard : Nat.card G = 10200960 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Schreier.m23_card
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

theorem row_M24_5 :
    KFactSporLocalRow .M24 5 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have hW : SecW G 5 := SecW.of_mulEquiv (b.trans e.symm) secW_M24_5
  have hcard : Nat.card G = 244823040 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
