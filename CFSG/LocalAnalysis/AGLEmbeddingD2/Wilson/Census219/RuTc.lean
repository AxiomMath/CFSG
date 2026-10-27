module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThree
public import Certificates.Certificate12615

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThetaSpor Subgroup Equiv

@[expose] noncomputable def ruTcQ : Subgroup (Perm (Fin 4060)) := closure (permsA 4060 ruTcD.gQ)

theorem ruTc_parts :
    tcOK 4060 6 ruKeys ruX ruTcD (ruTcCQ ()) (ruTcCK ()) (ruTcCS ()) = true ∧
    allLt ruTcD.gQ.size (fun l => (ruCCert ()).pts.toList.any (eqA 4060 ruTcD.gQ[l]!)) = true ∧
    allLt ruGs.size (fun k => allLt ruTcD.gQ.size fun l =>
      (ruTcCQ ()).pts.toList.any (eqA 4060 (conjA 4060 ruGs[k]! ruTcD.gQ[l]!))) = true := by
  have h := Certificates.certificate12615
  simp only [ruTcOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem ruKeys_lt : ∀ p ∈ ruKeys, p < 4060 := by decide

theorem ruTc_spec :
    permOfArr 4060 ruX ∈ ruTcQ ∧ CFSG.IsQuasisimple ↥ruTcQ ∧
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover ↥ruTcQ (alternatingGroup (Fin 6)) :=
  tcOK_spec ruKeys_lt (by norm_num) ruTc_parts.1

theorem card_ruTcQ : Nat.card ruTcQ = 1080 := by
  have h := (tcOK_parts ruTc_parts.1).1
  rw [ruTcQ, (enumOK_spec ruKeys_lt h).2.1, (tcOK_parts ruTc_parts.1).2.1]
  decide

theorem ruTc_le :
    ruTcQ ≤ closure (permsA 4060 ruGs) :=
  le_of_gens_mem ruKeys_lt ruCent_parts.2.2.2.2.2.1 (tcOK_parts ruTc_parts.1).1 ruTc_parts.2.1

theorem ruTc_normal :
    (ruTcQ.subgroupOf (closure (permsA 4060 ruGs))).Normal :=
  normal_kit ruKeys_lt ruCent_parts.2.2.2.2.2.1 (tcOK_parts ruTc_parts.1).1 ruTc_parts.2.1
    ruTc_parts.2.2

end CFSG.AGLEmbeddingD2.Wilson.Census219
