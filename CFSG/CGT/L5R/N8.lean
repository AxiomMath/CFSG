module

public import CFSG.CGT.L5R.Interfaces
public import CFSG.CGT.M24R.N8Cert

public section

namespace CFSG.CGT.L5R

open CFSG.CGT.Timmesfeld75 CFSG.CosetTable CFSG.CGT.M24R

theorem card_normalizer_of_hypL {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
    (hyp : L52CtxHyp T T₁) : Nat.card (Subgroup.normalizer (T : Set G)) = 322560 := by
  obtain ⟨φ⟩ := hyp.quot
  have h1 : Nat.card (NQuot T) = 20160 := by
    rw [Nat.card_congr φ.toEquiv]
    have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
    rw [Nat.card_perm, Nat.card_fin] at h
    have : Nat.factorial 8 = 40320 := by decide
    omega
  have h2 : Nat.card (T.subgroupOf (Subgroup.normalizer (T : Set G))) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
      hyp.card16]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (T.subgroupOf (Subgroup.normalizer (T : Set G)))]
  change Nat.card (NQuot T) * _ = _
  rw [h1, h2]

theorem n8StatementL : N8StatementL := by
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

end CFSG.CGT.L5R
