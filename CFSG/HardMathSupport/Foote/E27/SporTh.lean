module

public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporTh27
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporThMat

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.Th Subgroup CFSG.RankThree.PartTwo.Sec4.Item434SporTh

section Certificates


theorem th_e81_cover : ∃ (Q : Subgroup (GL (Fin 248) (ZMod 2)))
    (z : GL (Fin 248) (ZMod 2)), Q ≤ J ∧ Nat.card Q = 3 ^ (Nat.card J).factorization 3 ∧
      z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ Q ∧ (∀ q ∈ Q, q * z = z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup (GL (Fin 248) (ZMod 2)), E ≤ J ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
          81 ≤ Nat.card E ∧ s ∈ E ∧ z ∈ E := by
  obtain ⟨Q, z, hQJ, hQ, hz3, hz1, hzQ, hzc, hgood⟩ := Certificates.certificate9521
  refine ⟨Q, z, hQJ, ?_, hz3, hz1, hzQ, hzc, fun s hs hs3 hsz => ?_⟩
  · rw [CFSG.RankThree.PartTwo.Sec4.Item434SporTh.factorization_J, hQ]
  · obtain ⟨E, hEQ, hE, hE81, hsE, hzE⟩ := hgood s hs hs3 hsz
    exact ⟨E, hEQ.trans hQJ, hE, hE81, hsE, hzE⟩

theorem E27Config.false_of_th {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K)
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Th) : False := by
  obtain ⟨Q, z', hQJ, hQ, -, -, -, hzc, hgood⟩ := th_e81_cover
  have h4 : 4 ≤ (Nat.card J).factorization 3 := by
    rw [CFSG.RankThree.PartTwo.Sec4.Item434SporTh.factorization_J]
    norm_num
  exact h.false_of_e81_cover hz (e.trans thEquivJ) hQJ hQ h4 hzc hgood

theorem E27Config.false_of_sporadic_th {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Th ≃*
      (TauCeti.CFSGIndex.sporadic .Th).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) : False :=
  h.false_of_th hz (e.trans hbr.some.symm)

end Certificates

end CFSG.HardMathSupport.Foote.E27
