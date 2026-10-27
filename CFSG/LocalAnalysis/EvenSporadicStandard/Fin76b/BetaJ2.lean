module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaHom
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J2CentralizerD
public import Certificates.Certificate24600
public import Certificates.Certificate24601

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
open CFSG.EvenSporadicStandard.Fin76b.Beta

theorem sqW_iff {n : ℕ} {b : Array ℕ} {β : Equiv.Perm (Fin n)}
    (hb : CFSG.Monster.B.Co2.Rep n b β) {w : List (Array ℕ)} {g : Equiv.Perm (Fin n)}
    (hw : RepW n w g) : sqW n b w = true ↔ g * g = β := by
  rw [sqW, CFSG.Monster.B.Co2.allLt_iff]
  constructor
  · intro h
    ext x
    have h1 := h x.val x.isLt
    rw [beq_iff_eq, hw x, hb x] at h1
    have h2 := hw (g x)
    exact h2.symm.trans h1
  · intro h i hi
    rw [beq_iff_eq]
    have h2 := hw ⟨i, hi⟩
    have h3 := hw (g ⟨i, hi⟩)
    have h4 := hb ⟨i, hi⟩
    have h5 : g (g ⟨i, hi⟩) = β ⟨i, hi⟩ := by rw [← h]; rfl
    rw [show evR w i = ((g ⟨i, hi⟩ : Fin n) : ℕ) from h2, h3, h5]
    exact h4.symm

theorem card_centralizer_beta :
    Nat.card ↥(j2P ⊓ centralizer ({tp 315 (j2BetaTbl 7)} : Set (Equiv.Perm (Fin 315)))) =
      1080 := by
  classical
  have hperm := (betaHomCheck_permOK Certificates.certificate24601.1).2.2
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 315) [natArr (j2BetaTbl 7)]
      [tp 315 (j2BetaTbl 7)] :=
    List.Forall₂.cons (co2Rep_natArr_iff.2 (rep_tp hperm)) List.Forall₂.nil
  have hcount := card_eq_countW (f := commW 315 [natArr (j2BetaTbl 7)])
    (Pr := fun g => ∀ d ∈ [tp 315 (j2BetaTbl 7)], g * d = d * g) j2ChainArrays (by norm_num)
    PairJ2.chain_check.1 j2_groups (fun w g hw _ => commW_iff hgs hw)
  have hcnt : countW (commW 315 [natArr (j2BetaTbl 7)]) PairJ2.blocks [] = 1080 :=
    Certificates.certificate24600.1
  rw [show blocksOf 315 (rawLevels 315 j2StrongArrs PairJ2.baseArr) PairJ2.groups =
    PairJ2.blocks from rfl, hcnt, ← j2P_eq_original] at hcount
  rw [← hcount]
  refine Nat.card_congr ⟨fun x => ⟨⟨x.1, (mem_inf.mp x.2).1⟩, ?_⟩,
    fun x => ⟨x.1.1, mem_inf.mpr ⟨x.1.2, ?_⟩⟩, fun _ => rfl, fun _ => rfl⟩
  · intro d hd
    rw [List.mem_singleton.1 hd]
    exact mem_centralizer_singleton_iff.1 (mem_inf.mp x.2).2
  · exact mem_centralizer_singleton_iff.2 (x.2 _ (List.mem_singleton_self _))

theorem not_square_rep17 :
    ¬ ∃ s : ↥j2P, (s : Equiv.Perm (Fin 315)) * s = tp 315 (j2CentTbl 17) := by
  classical
  have hrep : CFSG.Monster.B.Co2.Rep 315 (natArr (j2CentTbl 17)) (tp 315 (j2CentTbl 17)) :=
    co2Rep_natArr_iff.2 (ctuc_j2_involution_centralizer_data.1 17 (by norm_num))
  have hcount := card_eq_countW (f := sqW 315 (natArr (j2CentTbl 17)))
    (Pr := fun g => g * g = tp 315 (j2CentTbl 17)) j2ChainArrays (by norm_num)
    PairJ2.chain_check.1 j2_groups (fun w g hw _ => sqW_iff hrep hw)
  have hcnt : countW (sqW 315 (natArr (j2CentTbl 17))) PairJ2.blocks [] = 0 :=
    Certificates.certificate24600.2
  rw [show blocksOf 315 (rawLevels 315 j2StrongArrs PairJ2.baseArr) PairJ2.groups =
    PairJ2.blocks from rfl, hcnt, ← j2P_eq_original] at hcount
  rintro ⟨s, hs⟩
  have hemp := Nat.card_eq_zero.1 hcount
  rcases hemp with hemp | hinf
  · exact hemp.false ⟨s, hs⟩
  · exact (not_infinite_iff_finite.2 inferInstance) hinf

theorem betaFor_j2P :
    ∃ (ht : tp 315 (j2CentTbl 31) ∈ j2P) (hb : tp 315 (j2BetaTbl 7) ∈ j2P),
      (⟨tp 315 (j2CentTbl 31), ht⟩ : ↥j2P) * ⟨tp 315 (j2BetaTbl 7), hb⟩ =
        ⟨tp 315 (j2BetaTbl 7), hb⟩ * ⟨tp 315 (j2CentTbl 31), ht⟩ ∧
        BetaFor ↥j2P ⟨tp 315 (j2BetaTbl 7), hb⟩ := by
  have hD := j2_groupData
  have hn : 315 < 2 ^ 32 := by norm_num
  obtain ⟨hchk, hmem⟩ := Certificates.certificate24601
  obtain ⟨ht, hd, hb⟩ := betaHomCheck_permOK hchk
  simp only [j2MemOK, Bool.and_eq_true] at hmem
  obtain ⟨⟨⟨hs8, hs9⟩, hs7⟩, heq⟩ := hmem
  have htX := (hD.sift _ _ (rep_tp ht)).1 hs8
  have hdX := (hD.sift _ _ (rep_tp hd)).1 hs9
  have hbX := (hD.sift _ _ (rep_tp hb)).1 hs7
  obtain ⟨hcomm, hβ⟩ := betaFor_of_check hn (X := j2P) (pg := piGens) piGens_even hchk htX hdX hbX
    card_centralizer_beta
  have hrep := ctuc_j2_involution_centralizer_data.1 31 (by norm_num)
  have htt : tp 315 (j2BetaTbl 8) = tp 315 (j2CentTbl 31) :=
    (tblEq_iff_eq (rep_tp ht) hrep).1 heq
  rw [← htt]
  exact ⟨htX, hbX, Subtype.ext hcomm, hβ⟩

theorem exists_conj_t0
    (ht0 : tp 315 (j2CentTbl 31) ∈ j2P) :
    ∀ t : ↥j2P, orderOf t = 2 → (∃ s : ↥j2P, s * s = t) →
      ∃ g : ↥j2P, t = g * ⟨tp 315 (j2CentTbl 31), ht0⟩ * g⁻¹ := by
  intro t ht2 ⟨s, hs⟩
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hPR : j2P ≤ j2R := le_sup_left
  obtain ⟨r, hr, g, hg, hv⟩ := hcover (t : Equiv.Perm (Fin 315)) (hPR t.2) (by
    rw [Subgroup.orderOf_coe]; exact ht2)
  have hrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) t.2) hg
    rwa [show g⁻¹ * (t : Equiv.Perm (Fin 315)) * g = tp 315 r.rep by rw [hv]; group] at this
  have hconj : (t : Equiv.Perm (Fin 315)) = g * tp 315 (j2CentTbl 31) * g⁻¹ := by
    have hr0 := hr
    simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h0 | h1 | h2
    · exfalso
      have hout : r.outer = true := by rw [h0]
      exact (hrows r hr0).2.2.1.1 hout hrP
    · exfalso
      have hrep : r.rep = j2CentTbl 17 := by rw [h1]
      rw [hrep] at hv
      refine not_square_rep17 ⟨⟨g⁻¹ * (s : Equiv.Perm (Fin 315)) * g,
        j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) s.2) hg⟩, ?_⟩
      have hss : (s : Equiv.Perm (Fin 315)) * s = t := by
        have := congrArg Subtype.val hs
        simpa using this
      show g⁻¹ * (s : Equiv.Perm (Fin 315)) * g * (g⁻¹ * (s : Equiv.Perm (Fin 315)) * g) =
        tp 315 (j2CentTbl 17)
      generalize tp 315 (j2CentTbl 17) = c at hv ⊢
      calc g⁻¹ * (s : Equiv.Perm (Fin 315)) * g * (g⁻¹ * (s : Equiv.Perm (Fin 315)) * g)
          = g⁻¹ * ((s : Equiv.Perm (Fin 315)) * s) * g := by group
        _ = g⁻¹ * (t : Equiv.Perm (Fin 315)) * g := by rw [hss]
        _ = c := by rw [hv]; group
    · have hrep : r.rep = j2CentTbl 31 := by rw [h2]
      rw [hrep] at hv
      exact hv
  exact ⟨⟨g, hg⟩, Subtype.ext hconj⟩

end CFSG.EvenSporadicStandard.Fin76b.J2
