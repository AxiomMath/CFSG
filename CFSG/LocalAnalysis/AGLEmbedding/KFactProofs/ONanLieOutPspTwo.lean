module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPspTwoGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.RankThree.PartOne.S11c.Sec66Glue
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpMain

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.RankThree.PartOne.Sec66T (innerAut fixSub)
open CFSG.RankThree.PartOne.FieldFix (nonLocalized_of_map_eq)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup fieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem genFixes_psp_two {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : StatedClassicalModel T .PSp 2 2 p) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) : GenFixes p α := by
  have hf : 1 ≤ p := hp.pos
  have hn : 2 ≤ 2 := le_rfl
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp 2 K)) :=
    fun h => hαinn ((CFSG.RankThree.PartOne.Sec66T.mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p :=
    orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ (innerAut _).one_mem))
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hf hn hK
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup 2 K := by
    have hidx' : (spSemilinearAutGroup 2 K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two _ hidx'
      (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ spLinearAutGroup 2 K := by
    intro hD
    have hcop : Nat.gcd 2 (2 ^ p - 1) = 1 := by
      have h1 : (2 : ℕ) ^ p % 2 = 0 := by
        obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_le hf
        rw [hg, pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ p := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hα'inn (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨hpf, σ, hσord, -, hh, -, hαh⟩ := hdesc p hp _ hE hD hα'ord
  have hσp : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
  obtain ⟨-, hkcard, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      Nat.prime_two hp (by omega) hp2 hf hn hK σ hσord
  rw [Nat.div_self hp.pos, pow_one] at hkcard
  have h1 : fixSub (fieldAut 2 K σ) =
      (CFSG.RankThree.PartOne.KCSpComm.subfieldProj (r := 2) σ).range :=
    CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range (hp.odd_of_ne_two hp2) hσp
  have hNLK : NonLocalized (fixSub (fieldAut 2 K σ)) := by
    rw [h1]
    exact CFSG.SignalizerFunctorTheorem.NonLocal.nonLocalized_spSubfield hn σ
  set φ : T ≃* StatedProj (StatedSp 2 K) := e.trans (hh⁻¹ : MulAut (StatedProj (StatedSp 2 K)))
    with hφ
  have hφα : MulAut.congr φ α = fieldAut 2 K σ := by
    have : MulAut.congr φ α = hh⁻¹ * MulAut.congr e α * hh⁻¹⁻¹ := rfl
    rw [this, hαh]
    group
  have hNL : NonLocalized (fixSub α) :=
    nonLocalized_of_map_eq (φ := φ) ((CFSG.RankThree.PartOne.Sec66T.fixSub_congr φ α).symm.trans
      (by rw [hφα])) hNLK
  set k : Subfield K := descentField σ with hkdef
  have hk2 : Nat.card k = 2 := hkcard
  have : Fintype k := Fintype.ofFinite k
  have hkfc : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk2
  have hinjψ := CFSG.SignalizerFunctorTheorem.NonLocal.proj_subfieldSpHom_injective k hk2
  set ψ : StatedSp 2 k →* StatedProj (StatedSp 2 K) :=
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K).comp
      (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.subfieldSpHom 2 k) with hψ
  have hrange : ψ.range = fixSub (fieldAut 2 K σ) := by rw [h1]; rfl
  let Φ : ↥(fixSub α) ≃* Equiv.Perm (Fin 6) :=
    (CFSG.RankThree.PartOne.Sec66T.fixSubEquiv φ α).trans
      ((MulEquiv.subgroupCongr (by rw [hφα])).trans
        ((((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinjψ).symm)).trans
          (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm k hkfc)))
  have h5 : 5 ≤ Nat.card (Fin 6) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  refine genFixes_of_equiv hp5 α Φ (closure_involutions_perm 6)
    ⟨alternatingGroup (Fin 6), commutator_alternatingGroup_eq_self h5, ?_⟩ hNL
  intro hbot
  have := nat_card_alternatingGroup (α := Fin 6)
  rw [hbot, Subgroup.card_bot, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  revert this
  decide

theorem lieOut_of_psp_two {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)]
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 p) : LieOutConcl L x :=
  lieOutConcl_of_genFixes hx hp hxp (overgroupLocal_of_model_psp h)
    (genFixes_psp_two hp hp5 h (CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp)
      hαinn)

end CFSG.AGLEmbedding.LieOut
