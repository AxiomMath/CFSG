module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsA
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInv

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier

@[expose] noncomputable def ruThreeLine (j : Fin 13) : Equiv.Perm (Fin 4060) :=
  permOfArr 4060 ruThreeLines[(j : ℕ)]!

@[expose] noncomputable def ruThreeTransporter (j : Fin 13) : Equiv.Perm (Fin 4060) :=
  permOfArr 4060 ruThreeTransporters[(j : ℕ)]!

@[expose] noncomputable def ruThreeQ : Subgroup (Equiv.Perm (Fin 4060)) :=
  closure (permsA 4060 ruThreeQGens)

@[expose] noncomputable def ruThreeC0 : Subgroup (Equiv.Perm (Fin 4060)) :=
  closure (permsA 4060 ruThreeC0Gens)

theorem ruThreeKeys_lt : ∀ p ∈ ruThreeKeys, p < 4060 := by decide

theorem ruThree_size : 2 ≤ ruThreeArrs.size := by simp [ruThreeArrs]

theorem ruThree_nodup : ruThreeBase.Nodup := by decide

theorem rep_ruA0' : Rep 4060 (ruArr4060 0) ruA0 :=
  rep_of_validA ruThree_case0_check.2.2.1

theorem rep_ruA1' : Rep 4060 (ruArr4060 1) ruA1 :=
  rep_of_validA ruThree_case0_check.2.2.2.1

theorem mem_ruP_of_sift {g : Array ℕ}
    {G : Equiv.Perm (Fin 4060)} (hG : Rep 4060 g G)
    (h : siftA 4060 ruThreeLevels ruThreeBaseArr 0 g = true) : G ∈ ruP :=
  mem_closure_two_of_siftG (S := ruThreeArrs) (bs := ruThreeBase) (W := ruThreeWords)
    (by norm_num) ruThree_size ruThree_nodup rep_ruA0' rep_ruA1' ruThree_case0_check.1 hG h

theorem card_ruP_three : Nat.card ruP = 145926144000 := by
  have h := card_closure_two_of_chainOK (S := ruThreeArrs) (bs := ruThreeBase)
    (W := ruThreeWords) (by norm_num) ruThree_size ruThree_nodup rep_ruA0' rep_ruA1'
    ruThree_case0_check.1
  have e : rawOrbitSizes 4060 ruThreeArrs (ruThreeBase.map Fin.val).toArray =
      [4060, 2304, 650, 8, 3, 1, 1] := ruThree_case0_check.2.1
  exact h.trans (by rw [e]; norm_num)

theorem ruThreeQ_le_P :
    ruThreeQ ≤ ruP :=
  closure_le_of_siftG (fun _ hl => enumOK_gens_valid (linesOKG_parts ruThree_Q_check.1).1 hl)
    ruThree_Q_check.2.1 mem_ruP_of_sift

theorem ruThreeQ_sylow :
    ∃ S : Sylow 3 ruP, (S : Subgroup ruP) = ruThreeQ.subgroupOf ruP :=
  linesOKG_sylow_of_card (k := 3) (m := 5404672000) (by norm_num) ruThreeKeys_lt
    ruThree_Q_check.1 ruThreeQ_le_P (by rw [card_ruP_three]; norm_num) (by norm_num)
    (by norm_num)

theorem rep_ruThreeLine (j : Fin 13) :
    Rep 4060 ruThreeLines[(j : ℕ)]! (ruThreeLine j) :=
  linesOKG_rep ruThree_Q_check.1 j

theorem ruThreeLine_mem_Q (j : Fin 13) :
    ruThreeLine j ∈ ruThreeQ :=
  linesOKG_mem ruThreeKeys_lt ruThree_Q_check.1 j

theorem ruThreeLine_mem_P
    (j : Fin 13) : ruThreeLine j ∈ ruP :=
  ruThreeQ_le_P (ruThreeLine_mem_Q j)

theorem orderOf_ruThreeLine (j : Fin 13) :
    orderOf (ruThreeLine j) = 3 :=
  linesOKG_orderOf (by norm_num) ruThree_Q_check.1 j

theorem ruThreeQ_lines :
    {H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruThreeQ ∧ Nat.card H = 3} =
        Set.range (fun j : Fin 13 => zpowers (ruThreeLine j)) :=
  (linesOKG_lines (by norm_num) ruThreeKeys_lt ruThree_Q_check.1).1

theorem ruThreeTransporter_spec
    (j : Fin 13) : ruThreeTransporter j ∈ ruP ∧
      ruThreeTransporter j * ruThreeLine 0 * (ruThreeTransporter j)⁻¹ = ruThreeLine j := by
  have hrec : ∀ j : ℕ, ruThreeRec.getD j 0 % 13 = 0 := fun j => by
    have h0 : ruThreeRec.getD j 0 = 0 := by
      by_cases hj : j < 13
      · exact List.getD_replicate 0 hj
      · rw [List.getD_eq_default _ _ (by simp [ruThreeRec]; omega)]
    rw [h0]
  have h := trans_spec (R' := ruP) (fun hG hs => mem_ruP_of_sift hG hs)
    (linesOKG_valid ruThree_Q_check.1) ruThree_Q_check.2.2.1 j.2
  rw [hrec] at h
  exact h

@[expose] noncomputable def ruThreeX0 :
    ruP :=
  ⟨ruThreeLine 0, ruThreeLine_mem_P 0⟩

theorem orderOf_ruThreeX0 :
    orderOf ruThreeX0 = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_ruThreeLine 0

theorem zpowers_conj_eq_of_zpowers_eq {G : Type*} [Group G] {g r L : G}
    (h : zpowers L = zpowers (g * r * g⁻¹)) : zpowers (g⁻¹ * L * g) = zpowers r := by
  apply le_antisymm
  · rw [zpowers_le]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (h ▸ mem_zpowers L : L ∈ zpowers (g * r * g⁻¹))
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← hk, conj_zpow]
    group
  · rw [zpowers_le]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (h ▸ mem_zpowers _ : g * r * g⁻¹ ∈ zpowers L)
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    have := conj_zpow (a := g⁻¹) (b := L) (i := k)
    simp only [inv_inv] at this
    rw [this, hk]
    group

theorem exists_conj_ruThree
    (r : ruP) (hr : orderOf r = 3) : ∃ c : ruP, zpowers (c * ruThreeX0 * c⁻¹) = zpowers r := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨S, hS⟩ := ruThreeQ_sylow
  have hp : IsPGroup 3 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])
  obtain ⟨Q', hQ'⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ruP Q' S
  have hmem : MulAut.conj g • r ∈ (S : Subgroup ruP) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' (mem_zpowers r))
  rw [hS, Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at hmem
  have hσ3 : orderOf ((g * r * g⁻¹ : ruP) : Equiv.Perm (Fin 4060)) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hr]
  have hH : zpowers ((g * r * g⁻¹ : ruP) : Equiv.Perm (Fin 4060)) ∈
      {H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruThreeQ ∧ Nat.card H = 3} :=
    ⟨zpowers_le.2 hmem, by rw [Nat.card_zpowers, hσ3]⟩
  rw [ruThreeQ_lines] at hH
  obtain ⟨j, hj⟩ := hH
  obtain ⟨hhP, hh⟩ := ruThreeTransporter_spec j
  set hel : ruP := ⟨ruThreeTransporter j, hhP⟩ with hhel
  set lj : ruP := ⟨ruThreeLine j, ruThreeLine_mem_P j⟩ with hlj
  have hconj : hel * ruThreeX0 * hel⁻¹ = lj := Subtype.ext hh
  refine ⟨g⁻¹ * hel, ?_⟩
  have hy : (g⁻¹ * hel) * ruThreeX0 * (g⁻¹ * hel)⁻¹ = g⁻¹ * lj * g := by
    rw [← hconj]
    group
  rw [hy]
  apply zpowers_conj_eq_of_zpowers_eq
  apply Subgroup.map_injective ruP.subtype_injective
  simpa [MonoidHom.map_zpowers, hlj] using hj

theorem ruThreeC0_spec :
    ruThreeC0 = centralizer {ruThreeLine 0} ⊓ ruP ∧ Nat.card ruThreeC0 = 2160 :=
  case_centralizer2P (S := ruThreeArrs) (bs := ruThreeBase) (W := ruThreeWords) (by norm_num)
    ruThree_size ruThree_nodup rep_ruA0' rep_ruA1' ruThree_case0_check.1 (rep_ruThreeLine 0)
    ruThreeKeys_lt ruThree_case0_check.2.2.2.2.1

theorem ruThreeC0_le_P :
    ruThreeC0 ≤ ruP := by
  rw [ruThreeC0_spec.1]
  exact inf_le_right

theorem mem_centralizer_of_mem_ruThreeC0
    {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruThreeC0) :
    c * ruThreeLine 0 = ruThreeLine 0 * c := by
  rw [ruThreeC0_spec.1] at hc
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 hc).1

theorem card_centralizer_ruThreeX0 :
    Nat.card (centralizer ({ruThreeX0} : Set ruP)) = 2160 := by
  rw [FactsA.card_centralizer_subtype ruP ruThreeX0]
  have h : (ruP ⊓ centralizer ({(ruThreeX0 : Equiv.Perm (Fin 4060))} :
      Set (Equiv.Perm (Fin 4060))) : Subgroup (Equiv.Perm (Fin 4060))) = ruThreeC0 := by
    rw [inf_comm]
    exact ruThreeC0_spec.1.symm
  rw [h]
  exact ruThreeC0_spec.2

theorem ruThreeV_spec :
    ∃ V ∈ ruThreeC0, orderOf V = 2 ∧ ∃ p, V p = p := by
  have hlt : 1 < ruThreeC0Gens.size := by simp [ruThreeC0Gens]
  have hvalid := enumOK_gens_valid (centOKP_enum ruThree_case0_check.2.2.2.2.1) hlt
  have hrep := rep_of_validA hvalid
  have h := ruThree_case0_check.2.2.2.2.2.2
  simp only [ruThreeInvOK, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, p, hp, hpp⟩ := h
  refine ⟨permOfArr 4060 ruThreeC0Gens[1]!, subset_closure (mem_permsA hlt),
    orderOf_eq_two_of_invA hrep (by simp [invA, h1, h2]), ⟨p, hp⟩, ?_⟩
  apply Fin.ext
  exact (hrep.apply hp).symm.trans hpp

end CFSG.EvenSporadicStandard.RuStd.S2
