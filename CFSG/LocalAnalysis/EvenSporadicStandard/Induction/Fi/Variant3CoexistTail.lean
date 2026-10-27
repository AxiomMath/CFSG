module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3TailGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3TailFi23
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Even

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

section Certificates


theorem fi23TailMax_of_hyp12 (hyp12 : Hyp12Fi) (hmult : OddMultTrivial .Fi23) :
    Fi23TailMaxHered := by
  intro H _ _ hH N L K t u hN hidx hkp hcov hglob hfi hS htN
  obtain ⟨e⟩ := hcov.isSporadic_of_mult hmult
  have hL : IsSporadic ↥L .Fi23 := ⟨e⟩
  obtain ⟨hKeq, hmax, hstar⟩ := fi23_cover_facts hL hfi
  have hZ := fi23_center_facts hL hfi
  have hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l :=
    AllInner.of_mulEquiv e.symm CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj
  have : N.Normal := hN.normal
  obtain ⟨f⟩ := fi23_pair_equiv hL hfi
  obtain ⟨huL, hu2, hKL, hKu, hKq, -⟩ := hfi
  have huK : u ∈ K := by
    rw [hKeq]
    exact ⟨huL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hLN : L ≤ N := le_of_isPerfect_of_index_le_two hidx hcov.1.1
  have hKN : K ≤ N := hKL.trans hLN
  have hC := fun {y : H} (hy : y ∈ centralizer (K : Set H)) =>
    exists_mul_of_mem_centralizer hglob.hyp35 hKL hu2 huK hKu hinn hZ hmax hstar hy
  have hO : ∀ c ∈ centralizer (L : Set H), c ∈ N → c * c = 1 → c = 1 :=
    fun c hc hcN hcc => eq_one_of_mul_self_eq_one hS hglob.t_mem hglob.t_order htN hc hcN hcc
  have hstd : SolStd (K.subgroupOf N) :=
    solStd_subgroupOf_tail hKN hKu huK hu2 huL hKq hglob.hyp35 (fun y hy => hC hy) hO
  have hNs : IsSimpleGroup ↥N := hN.isSimpleGroup
  have hna : ∃ a b : ↥N, a * b ≠ b * a := hN.nonabelian
  have hkpN : CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥N :=
    kProper_of_section hkp N (MonoidHom.id ↥N) Function.surjective_id
  let fK : ↥(K.subgroupOf N) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKN
  have hqK : CFSG.IsQuasisimple ↥(K.subgroupOf N) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv fK.symm hKq
  have heven : ¬ Odd (Nat.card ↥(center ↥(K.subgroupOf N))) := by
    rw [card_center_congr (fK.trans f), fi23D_card_center]
    exact Nat.not_odd_iff_even.2 even_two
  obtain ⟨g⟩ := fi23D_cq
  have hcq : IsSporadic (↥(K.subgroupOf N) ⧸ center ↥(K.subgroupOf N)) .Fi22 :=
    ⟨(cqEquivOfMulEquiv (fK.trans f)).trans g⟩
  obtain ⟨s'', hs'', hNs'⟩ := hyp12.even22 ↥N
    (hH.of_section (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup N)) ⊤
    (fStarSimple_top ↥N hna) (by simp) hkpN (K.subgroupOf N) hstd hqK hcq heven
  obtain ⟨g'⟩ := hNs'
  rcases List.mem_cons.1 hs'' with rfl | hs''
  ·
    exfalso
    have hcard : Nat.card ↥N = Nat.card ↥L := by
      rw [Nat.card_congr (Subgroup.topEquiv.symm.trans g').toEquiv, Nat.card_congr e.toEquiv]
    have hLN' : L = N := Subgroup.eq_of_le_of_card_ge hLN hcard.le
    apply htN
    apply hN.centralizer_le
    rw [← hLN']
    exact hglob.t_mem
  · rcases List.mem_singleton.1 hs'' with rfl
    exact ⟨Subgroup.topEquiv.symm.trans g'⟩

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.V3
