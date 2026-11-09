module

public import CFSG.Certificates.Kernel.LocalQTChainGSound
import all CFSG.Certificates.Kernel.LocalQTChainGSound
public import CFSG.Certificates.Kernel.LocalQTSimsSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S

variable {n : ℕ}

theorem chainFrom_intro (hn : n ≤ 32) (f : ℕ → Bool) : ∀ {prev : List ℕ} {C : List Lvl},
    ChainP n prev C → ∀ π : Perm (Fin n), (∀ σ, InC n C σ → f (P.code (π * σ)) = true) →
      chainFrom n C f (P.code π) = true
  | _, [], _, π, h => by
    have h0 : sift n [] (P.code (1 : Perm (Fin n))) = some 0 := by simp [sift, P.code_one]
    have := h 1 (by rw [InC, h0]; rfl)
    rw [mul_one] at this
    exact this
  | _, lv :: C, hC, π, h => by
    change P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
      (P.letB (P.mul n (P.code π) (getK lv.2.1 j)) (chainFrom n C f))) = true
    rw [P.allN_iff]
    intro j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq]
    intro e
    obtain ⟨⟨τ, hτ⟩, -⟩ := hC.1.1.2.1 j hj e
    rw [← hτ, P.code_mul hn]
    refine chainFrom_intro hn f hC.2 (π * τ) fun σ hσ => ?_
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
    have := h (τ * σ) (by rw [InC, sift_mul_rep hn hC hj τ hτ e hk]; rfl)
    rwa [mul_assoc]

theorem allChain_intro (hn : n ≤ 32) {C : List Lvl} (hC : ChainP n [] C) (f : ℕ → Bool)
    (h : ∀ σ, InC n C σ → f (P.code σ) = true) : allChain n C f = true := by
  have := chainFrom_intro hn f hC 1 fun σ hσ => by
    rw [one_mul]
    exact h σ hσ
  rw [← P.code_one] at this
  exact this

theorem grpC_of_gen (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (MG L : List (Perm (Fin n))) {W : List (List (List ℕ))} {d : ℕ}
    (h1 : ∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ MG})
    (hg : P.allL (L.map P.code) (inC n C (chainF C)) = true)
    (hw : wordsC n C (L.map P.code) W d = true) :
    grpC n C (chainF C) (L.map P.code) W d = true := by
  have hCP := chainP_of_ok hok hI
  have hC := chainP_lvOK hCP
  have hc : allChain n C (fun s => P.allL (L.map P.code) fun g =>
      inC n C (chainF C) (P.mul n s g)) = true := by
    refine allChain_intro hn hCP _ fun σ hσ => ?_
    rw [P.allL_map]
    intro γ hγ
    have hγ' : InC n C γ := (inC_iff hn hC γ).1 ((P.allL_map L _).1 hg γ hγ)
    rw [P.code_mul hn, inC_iff hn hC]
    exact (h1 _).2 (Subgroup.mul_mem _ ((h1 σ).1 hσ) ((h1 γ).1 hγ'))
  unfold grpC
  rw [hg, hw, hc]
  rfl

theorem grpC_of_grpC (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (MG L : List (Perm (Fin n))) {MW W : List (List (List ℕ))} {d : ℕ}
    (hM : grpC n C (chainF C) (MG.map P.code) MW d = true)
    (hg : P.allL (L.map P.code) (inC n C (chainF C)) = true)
    (hw : wordsC n C (L.map P.code) W d = true) :
    grpC n C (chainF C) (L.map P.code) W d = true :=
  grpC_of_gen hn hok hI MG L (grpC_sound hn hok hI MG hM).1 hg hw

theorem grpC_of_sims (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (MG : List (Perm (Fin n))) {W : List (List (List ℕ))} {d : ℕ}
    (h : CFSG.KC.LQT.PH.grpS n C (chainF C) (MG.map P.code) W d = true) :
    grpC n C (chainF C) (MG.map P.code) W d = true := by
  have h3 := h
  unfold CFSG.KC.LQT.PH.grpS at h3
  rw [P.andB_iff, P.andB_iff] at h3
  exact grpC_of_gen hn hok hI MG MG (grpS_sound hn hok hI MG h).1 h3.1 h3.2.1

end CFSG.KC.LQT.CM

end
