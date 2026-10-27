module

public import Certificates.Certificate15104

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

theorem cz_jrel :
    ∀ v ∈ czJRelRels, (∀ l ∈ v, l.1 < 7) ∧ Sporadic.Bridge.wordProd
      (Sporadic.Bridge.VecSurj.img RuPi7.pi7RuSpec
        (Sporadic.Bridge.VecSurj.seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1 :=
  Certificates.certificate15104.1

theorem cz_jcard :
    Finite (CosetTable.PG 6 czRelsJW) ∧ Nat.card (CosetTable.PG 6 czRelsJW) ≤ 2048 :=
  Certificates.certificate15104.2.1

theorem cz_rigid_check : czRigidCheck = true :=
  Certificates.certificate15104.2.2.1

theorem cz_jident_check : czJIdentCheck = true :=
  Certificates.certificate15104.2.2.2.1

theorem cz_gamma :
    ∀ v ∈ c2RuRels, (∀ l ∈ v, l.1 < 7) ∧ Sporadic.Bridge.wordProd
      (Sporadic.Bridge.VecSurj.img RuPi7.pi7RuSpec
        (Sporadic.Bridge.VecSurj.seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1 :=
  Certificates.certificate15104.2.2.2.2.1

theorem card_eps1_le :
    Finite (CosetTable.PG 10 czEps1Rels) ∧ Nat.card (CosetTable.PG 10 czEps1Rels) ≤ 122880 :=
  Certificates.certificate15104.2.2.2.2.2.1

theorem card_eps2_le :
    Finite (CosetTable.PG 10 czEps2Rels) ∧ Nat.card (CosetTable.PG 10 czEps2Rels) ≤ 122880 :=
  Certificates.certificate15104.2.2.2.2.2.2.1

theorem card_eps3_le :
    Finite (CosetTable.PG 10 czEps3Rels) ∧ Nat.card (CosetTable.PG 10 czEps3Rels) ≤ 122880 :=
  Certificates.certificate15104.2.2.2.2.2.2.2.1

theorem cz_sub_index :
    (CosetTable.genSub {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk} sub9).FiniteIndex ∧
      (CosetTable.genSub {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk} sub9).index ≤ 5 :=
  Certificates.certificate15104.2.2.2.2.2.2.2.2.1

theorem cz_card_p12 :
    Finite (CosetTable.PG sub9.length p12Rels) ∧
      Nat.card (CosetTable.PG sub9.length p12Rels) ≤ 49152 :=
  Certificates.certificate15104.2.2.2.2.2.2.2.2.2.1

theorem cz_ru :
    ∀ v ∈ czRuRels, (∀ l ∈ v, l.1 < 7) ∧ Sporadic.Bridge.wordProd
      (Sporadic.Bridge.VecSurj.img RuPi7.pi7RuSpec
        (Sporadic.Bridge.VecSurj.seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1 :=
  Certificates.certificate15104.2.2.2.2.2.2.2.2.2.2.1

theorem cz_m1_index :
    (CosetTable.genSub {r : FreeGroup (Fin 7) | r ∈ RuPi7.pi7Rels.map FreeGroup.mk}
        (CosetTable.subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (CosetTable.genSub {r : FreeGroup (Fin 7) | r ∈ RuPi7.pi7Rels.map FreeGroup.mk}
        (CosetTable.subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 593775 :=
  Certificates.certificate15104.2.2.2.2.2.2.2.2.2.2.2

end CFSG.ComponentClassification.GMS78.RuCz
