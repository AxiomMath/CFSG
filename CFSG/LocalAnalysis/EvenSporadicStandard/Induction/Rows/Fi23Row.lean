module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23InputsHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LTransfer

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem fi23_exists_normal_index_two {H : Type} [Group H] [Finite H] {L : Subgroup H} {t : H}
    {W : Subgroup H} (h : Sol78Lemma612Out H L t W) :
    ∃ M : Subgroup H, M.Normal ∧ M.index = 2 ∧ t ∉ M := by
  obtain ⟨N₀, -, hidx, htN₀⟩ := h.index_two
  have hW : IsPGroup 2 W := fun x => ⟨1, by
    have h2 := h.elemAbelian.2 x x.2
    rw [pow_one]
    exact Subtype.ext (by simpa using h2)⟩
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact exists_normal_index_two_of_weaklyClosed W hW hcomm
    (mem_normalizer_of_weaklyClosedInNormalizer h.weaklyClosed) N₀ hidx h.t_mem_W h.t_order htN₀

theorem fi23_le_of_normal_index_two {H : Type} [Group H] {N M : Subgroup H} (hN : FStarSimple N)
    (hM : M.Normal) (hM2 : M.index = 2) : N ≤ M := by
  have := hN.isSimpleGroup
  have hn : (M.subgroupOf N).Normal := hM.subgroupOf N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf N) with h | h
  · exfalso
    have hcard : Nat.card (H ⧸ M) = 2 := hM2
    have hcyc : IsCyclic (H ⧸ M) := isCyclic_of_prime_card hcard
    let _ : CommGroup (H ⧸ M) := IsCyclic.commGroup
    have hinj : Function.Injective ((QuotientGroup.mk' M).comp N.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      have hker : ((QuotientGroup.mk' M).comp N.subtype).ker = M.subgroupOf N := by
        ext x
        simp [Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
      rw [hker, h]
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    refine hab (hinj ?_)
    simp only [MonoidHom.comp_apply, map_mul]
    exact mul_comm _ _
  · exact Subgroup.subgroupOf_eq_top.1 h

theorem fi23_index_eq_two_of_le {H : Type} [Group H] [Finite H] {N M : Subgroup H}
    (hNM : N ≤ M) (hM2 : M.index = 2) (hidx : N.index ≤ 2) : N.index = 2 := by
  have hdvd : 2 ∣ N.index := hM2 ▸ Subgroup.index_dvd_of_le hNM
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  omega

section Certificates

theorem sol78ConclAt_fi23 (hmult : OddMultTrivial .Fi23) (h63 : Fi23Lemma63)
    (h65 : Balance.Sol78Lemma65KP) (hS2 : Fi23TwoSylow) {H : Type} [Group H] [Finite H]
    (hBal : Fi23BalanceAt H) (hE : Fi23Claim612EAt H) (hTail : Fi23TailAt H) :
    ∀ (N L K : Subgroup H) (t u : H), FStarSimple N →
      N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
        SolomonGlobalQ H L K t u → fiIn23 H L K u → t ∉ N ∧ N.index = 2 ∧ Sol78Concl N L := by
  intro N L K t u hN hidx hKP hcov hglob hfi
  obtain ⟨e⟩ := hcov.isSporadic_of_mult hmult
  have hS : ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2 :=
    hS2 H N L K t u hN hidx hKP hcov hglob hfi
  have hbal := hBal N L hN hidx hKP hglob.standardL hcov hS t hglob.t_mem hglob.t_order
  have hs : Setting612 H L t :=
    fi23_setting612 hmult hcov hglob.standardL hglob.t_mem hglob.t_order hbal
  have hT : Fi23Transposition L u := fi23Transposition_of_fiIn23 ⟨e⟩ hfi
  have hMax : NoBiggerFi H .Fi23 := hfi.2.2.2.2.2.2
  have hclaim := hE N L K t u hN hidx hKP hcov hglob hfi hT hMax hS
  obtain ⟨W, hW⟩ := fi23_exists_out_of_setting hN hs hT (h63 H L ⟨e⟩)
    (fun g => h63 H _ (fi23_isSporadic_map_conj ⟨e⟩ g)) hKP h65 hclaim
  obtain ⟨M, hMn, hM2, htM⟩ := fi23_exists_normal_index_two hW
  have hNM : N ≤ M := fi23_le_of_normal_index_two hN hMn hM2
  have htN : t ∉ N := fun h => htM (hNM h)
  exact ⟨htN, fi23_index_eq_two_of_le hNM hM2 hidx,
    ⟨e⟩, hTail N L K t u hN hidx hKP hcov hglob hfi hS htN⟩

end Certificates

end CFSG.EvenSporadicStandard.Induction
