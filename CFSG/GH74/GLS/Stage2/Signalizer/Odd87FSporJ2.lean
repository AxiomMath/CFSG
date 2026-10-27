module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSpor
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Model
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.Sporadic.SmallOddCore.J2
public import Certificates.Certificate5165

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native Certificates.Odd87F3 Certificates.Odd87F3.J2

theorem j2_F3S :
    (∀ p ∈ [3, 5, 7], F3S j2P (tp 315 (rowAt 0).rep) p) ∧
    (∀ p ∈ [3, 5, 7], F3S j2P (tp 315 (rowAt 1).rep) p) ∧
    (∀ p ∈ [3, 5, 7], F3S j2P (tp 315 (rowAt 2).rep) p) := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, -, hrows, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hQ : ValidSchreier j2Chain := j2Chain_valid.1
  have hTss : levelTables j2Chain = j2Tss :=
    CFSG.ComponentClassification.J2Cover.levelTables_eq j2ChainArrays
      (chainCheckFacts PairJ2.chain_check.1)
  have hNG : j2Chain.orderCertificate = 604800 := by
    rw [j2Chain.orderCertificate_eq_card hQ, ← j2P_eq_original, card_j2P]
  have hall : j2F3OK = true := Certificates.certificate5165
  simp only [j2F3OK, Bool.and_eq_true] at hall
  obtain ⟨⟨⟨hperm, h0⟩, h1⟩, h2⟩ := hall
  rw [List.all_eq_true] at hperm
  have hpr : ∀ p ∈ [3, 5, 7], p.Prime := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  have main : ∀ (i : Fin 3) (rs : List Row),
      (permOK 315 (rowAt i).rep && (rowAt i).centGens.all (permOK 315)) = true →
      rowsOKT 315 604800 j2Tss (rowAt i).centGens (rowAt i).rep rs = true →
      (∀ p ∈ [3, 5, 7], ∃ r ∈ rs, r.prime = p) →
      ∀ p ∈ [3, 5, 7], F3S j2P (tp 315 (rowAt i).rep) p := by
    intro i rs hpermi h hps
    rw [Bool.and_eq_true, List.all_eq_true] at hpermi
    have hrep : ∀ T ∈ (rowAt i).rep :: (rowAt i).centGens, Rep 315 T (tp 315 T) := by
      intro T hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact rep_tp hpermi.1
      · exact rep_tp (hpermi.2 T hT)
    have hmem : rowAt i ∈ j2Rows := List.getElem_mem _
    have hgT : List.Forall₂ (Rep 315) (rowAt i).centGens ((rowAt i).centGens.map (tp 315)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.2 fun T hT => hrep T (List.mem_cons_of_mem _ hT)
    have hgG : ∀ g ∈ (rowAt i).centGens.map (tp 315), g ∈ j2Chain.originalSubgroup := by
      intro g hg
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hg
      obtain ⟨-, -, -, h4, -⟩ := hrows (rowAt i) hmem
      rw [← j2P_eq_original]
      have : tp 315 T ∈ j2C (rowAt i) :=
        Subgroup.subset_closure ⟨T, by simpa using hT, rfl⟩
      rw [h4] at this
      exact this.1
    have := f3S_of_rowsOKT_primes hn j2Chain hQ hgT hgG (hrep _ List.mem_cons_self) hTss hNG h hps
      hpr
    rwa [← j2P_eq_original] at this
  exact ⟨main 0 rowsR1 (by simpa using hperm 0 (List.mem_finRange _)) h0 (by decide),
    main 1 rowsR2 (by simpa using hperm 1 (List.mem_finRange _)) h1 (by decide),
    main 2 rowsR3 (by simpa using hperm 2 (List.mem_finRange _)) h2 (by decide)⟩

theorem sporKL_J2 :
    SporKL .J2 := by
  intro Y _ _ hY p α Xh h
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j2P := (e : Y ≃* NativeSporadic.J2).trans j2PermEquiv
  obtain ⟨hF0, hF1, hF2⟩ := j2_F3S
  obtain ⟨-, -, -, -, hcover, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  refine false_of_F3_autModel j2_autModel e'
    [tp 315 (rowAt 0).rep, tp 315 (rowAt 1).rep, tp 315 (rowAt 2).rep] ?_ (ps := [3, 5, 7]) ?_ ?_ ?_
    h
  · intro t ht ho
    obtain ⟨r, hr, g, hg, hrt⟩ := hcover t ht ho
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.1 hr
    have hlen : j2Rows.length = 3 := by decide
    have hi3 : i < 3 := hlen ▸ hi
    have hreq : r = rowAt ⟨i, hi3⟩ := hir.symm
    refine ⟨tp 315 r.rep, ?_, g, hg, hrt⟩
    rw [hreq]
    interval_cases i <;> simp
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq hq2 hd
    rw [card_j2P] at hd
    have := prime_mem_of_dvd (by norm_num : (604800 : ℕ) ≠ 0)
      (by norm_num : Nat.primeFactorsList 604800 = [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7]) hq hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega
  · intro r hr q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hF0 q hq
    · exact hF1 q hq
    · exact hF2 q hq

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
