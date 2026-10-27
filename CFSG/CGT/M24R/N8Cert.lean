module

public import CFSG.CGT.M24R.N8Iso
public import Certificates.Certificate21192

public section

namespace CFSG.CGT.M24R

open CFSG.CGT.Timmesfeld75 CFSG.CosetTable

theorem finite_pg_relsN8Ten : Finite (PG 10 relsN8Ten) :=
  Certificates.certificate21192.1.1

theorem card_pg_relsN8Ten_le : Nat.card (PG 10 relsN8Ten) ≤ 322560 :=
  Certificates.certificate21192.1.2

theorem n8Statement : N8Statement := by
  intro G _ _ T T₁ hyp
  obtain ⟨-, hgl, hgen⟩ := Certificates.certificate21192
  have := finite_pg_relsN8Ten
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hyp.wc.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ T, a ^ 2 = 1 := hyp.wc.1.2
  obtain ⟨φ⟩ := hyp.quot
  obtain ⟨L, hLT, hTL⟩ := hyp.compl
  exact exists_mulEquiv_normalizer8 hcomm hsq hyp.card16 hyp.cent_eq φ hLT hTL hgl hgen
    card_pg_relsN8Ten_le

end CFSG.CGT.M24R
