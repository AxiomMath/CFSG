module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFCount

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.HNSchreier CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def fixc (w : Equiv.Perm X) : ℕ := Set.ncard {p : X | w p = p}

@[expose] noncomputable def Fcount (F : Set X) (v : Equiv.Perm X) : ℕ :=
  Set.ncard {p : X | p ∈ F ∧ v p = p}

@[expose] noncomputable def FStab (F : Set X) : Subgroup ↥JH where
  carrier := {c | permHom c '' F = F}
  mul_mem' := by
    intro c d hc hd
    simp only [Set.mem_ofPred_eq] at hc hd ⊢
    rw [map_mul]
    ext p
    simp only [Set.mem_image, Equiv.Perm.coe_mul, Function.comp_apply]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have : permHom d q ∈ permHom d '' F := ⟨q, hq, rfl⟩
      rw [hd] at this
      have : permHom c (permHom d q) ∈ permHom c '' F := ⟨_, this, rfl⟩
      rwa [hc] at this
    · intro hp
      rw [← hc] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [← hd] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact ⟨r, hr, rfl⟩
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one]
    ext p
    simp
  inv_mem' := by
    intro c hc
    simp only [Set.mem_ofPred_eq] at hc ⊢
    rw [map_inv]
    conv_lhs => rw [← hc]
    ext p
    simp [Set.mem_image]

theorem mem_FStab {F : Set X} {c : ↥JH} : c ∈ FStab F ↔ permHom c '' F = F := Iff.rfl


section Setup

attribute [local irreducible] pword pcomp pinvCand

variable
  {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}

theorem ptsOK_inj {G Ginv : Array (Array Nat)} {pts pos : Array Nat} {idx : Array (Array Nat)}
    (hP : hnfPtsOK G Ginv pts pos idx = true) :
    ∀ j < pts.size, ∀ j' < pts.size, pts[j]! = pts[j']! → j = j' := by
  intro j hj j' hj' h
  unfold hnfPtsOK at hP
  simp only [Bool.and_eq_true, beq_iff_eq] at hP
  have h1 := allBelowN_spec hP.2 hj
  have h2 := allBelowN_spec hP.2 hj'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2
  rw [← h1.1.2, ← h2.1.2, h]

theorem mem_FStab_of_inv_image_subset {F : Set X} {c : ↥JH} (h : permHom c⁻¹ '' F ⊆ F) :
    c ∈ FStab F := by
  have hF : F.Finite := Set.toFinite F
  have h1 : permHom c⁻¹ '' F = F :=
    Set.eq_of_subset_of_ncard_le h (by rw [Set.ncard_image_of_injective _ (permHom c⁻¹).injective])
      hF
  rw [mem_FStab]
  conv_lhs => rw [← h1]
  rw [Set.image_image]
  simp

theorem hnfRepWords_ok : ∀ i < 9, plettersOK 2 hnfRepWords[i]! = true := by decide

theorem hnfSetupCore_sound (h : TabHyp tA tAi tB tBi g1 g2)
    (hc : hnfSetupCore tA tAi tB tBi g1 g1i g2 g2i = true) :
    hnfG1 ∈ centralizer ({aJ} : Set ↥JH) ∧ hnfG2 ∈ centralizer ({aJ} : Set ↥JH) ∧
    ∃ F : Set X, hnfC0 ≤ FStab F ∧ ∀ i < 9,
      fixc (permHom aJ * permHom (hnfRep hnfRepWords[i]!)) = (hnfInvs[i]!).1 ∧
      Fcount F (permHom (hnfRep hnfRepWords[i]!)) = (hnfInvs[i]!).2 := by
  unfold hnfSetupCore at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨htab, hpts⟩, hcom1⟩, hcom2⟩, hinv⟩ := hc
  obtain ⟨hA, hAi, hB, hBi, hg1, hg1i, hg2, hg2i⟩ := h.prep htab
  have hcomm : ∀ {c : ↥JH} {tc : Array Nat}, PRep hnfN tc (permHom c) →
      peq hnfN (pcomp hnfN tc tA) (pcomp hnfN tA tc) = true →
        c ∈ centralizer ({aJ} : Set ↥JH) := by
    intro c tc htc hq
    have := (peq_iff (prep_pcomp htc hA) (prep_pcomp hA htc)).1 hq
    exact mem_centralizer_of_map_commute permHom permHom_injective this
  refine ⟨hcomm hg1 hcom1, hcomm hg2 hcom2, ?_⟩
  set G : Array (Array Nat) := #[tA, g1, g2] with hGdef
  set Ginv : Array (Array Nat) := #[tAi, g1i, g2i] with hGidef
  set pts := orbitPts G hnfSeedF with hptsdef
  set pos := hnfPos pts with hposdef
  set idx : Array (Array Nat) :=
    #[hnfIdx tAi pts pos, hnfIdx g1i pts pos, hnfIdx g2i pts pos] with hidxdef
  refine ⟨ptsSet hnfN pts, ?_, ?_⟩
  ·
    have hinvF : ∀ k < 3, ∀ (c : ↥JH), PRep hnfN Ginv[k]! (permHom c)⁻¹ →
        (∀ j < pts.size, pts[(idx[k]!)[j]!]! = (Ginv[k]!)[pts[j]!]! ∧ (idx[k]!)[j]! < pts.size) →
        c ∈ FStab (ptsSet hnfN pts) := by
      intro k hk c hcp hidx
      apply mem_FStab_of_inv_image_subset
      rintro _ ⟨p, ⟨j, hj, hjp⟩, rfl⟩
      obtain ⟨hpt, hlt⟩ := hidx j hj
      refine ⟨(idx[k]!)[j]!, hlt, ?_⟩
      rw [hpt]
      have hp := ptsOK_lt hpts hj
      have := hcp ⟨pts[j]!, hp⟩
      have hpe : p = ⟨pts[j]!, hp⟩ := Fin.ext hjp.symm
      rw [hpe]
      exact this
    have hidxall : ∀ k < 3, ∀ j < pts.size,
        pts[(idx[k]!)[j]!]! = (Ginv[k]!)[pts[j]!]! ∧ (idx[k]!)[j]! < pts.size := by
      intro k hk j hj
      have hP := hpts
      unfold hnfPtsOK at hP
      simp only [Bool.and_eq_true, beq_iff_eq] at hP
      have h1 := allBelowN_spec hP.2 hj
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      have h2 := allBelowN_spec h1.2 hk
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      exact ⟨h2.1.2, h2.1.1⟩
    unfold hnfC0
    rw [Subgroup.closure_le]
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl
    · exact hinvF 0 (by norm_num) _ (by rw [← hnfGen_zero]; exact hAi) (hidxall 0 (by norm_num))
    · exact hinvF 1 (by norm_num) _ (by rw [← hnfGen_one]; exact hg1i) (hidxall 1 (by norm_num))
    · exact hinvF 2 (by norm_num) _ (by rw [← hnfGen_two]; exact hg2i) (hidxall 2 (by norm_num))
  · intro i hi
    have hall := List.all_eq_true.1 hinv i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, beq_iff_eq] at hall
    have hrep := hnfRepTab_prep h htab (hnfRepWords_ok i hi)
    constructor
    · rw [← hall.1, hnfCountFix]
      exact (countFix_eq (prep_pcomp hA hrep)).symm
    · have hF := countFixOn_eq hrep (fun j hj => ptsOK_lt hpts hj) (ptsOK_inj hpts)
      rw [← hall.2, hnfCountFixOn, hF]
      rfl

end Setup

end CFSG.EvenSporadicStandard.Solomon78
