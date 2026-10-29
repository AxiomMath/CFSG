module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def klV0 : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

@[expose] def klF (i : Fin 5) : Fin 5 → ZMod 2 := fun j => if j = i then 0 else 1

theorem kl_isEven_v0 : IsEvenVec klV0 := by
  unfold IsEvenVec klV0
  decide +kernel

theorem kl_isEven_F (i : Fin 5) : IsEvenVec (klF i) := by
  revert i
  unfold IsEvenVec klF
  decide +kernel

theorem kl_weight_F (i : Fin 5) : vecWeight (klF i) = 4 := by
  revert i
  unfold vecWeight klF
  decide +kernel

theorem kl_eq_F_of_weight_four : ∀ v : Fin 5 → ZMod 2, vecWeight v = 4 → ∃ i, v = klF i := by
  unfold vecWeight klF
  decide +kernel

theorem kl_permVec_F (σ : Equiv.Perm (Fin 5)) (i : Fin 5) : permVec σ (klF i) = klF (σ i) := by
  revert σ i
  unfold permVec klF
  decide +kernel

theorem kl_F_injective : Function.Injective klF := by
  unfold Function.Injective klF
  decide +kernel

theorem kl_F_add_01 : klF 0 + klF 1 = klV0 := by
  unfold klF klV0
  decide +kernel

theorem kl_F_add_0123 : klF 0 + klF 1 + klF 2 + klF 3 = klF 4 := by
  unfold klF
  decide +kernel

theorem kl_isEven_of_weight_two : ∀ v : Fin 5 → ZMod 2, vecWeight v = 2 → IsEvenVec v := by
  unfold IsEvenVec vecWeight
  decide +kernel

theorem kl_weight_four_sum :
    ∀ v : Fin 5 → ZMod 2, vecWeight v = 4 → ∃ x y : Fin 5 → ZMod 2,
      vecWeight x = 2 ∧ vecWeight y = 2 ∧ v = x + y := by
  unfold vecWeight
  decide +kernel

theorem kl_alt_to_v0 : ∀ w : Fin 5 → ZMod 2, vecWeight w = 2 →
    ∃ σ ∈ alternatingGroup (Fin 5), permVec σ w = klV0 := by
  unfold vecWeight permVec klV0
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem kl_alt_trans_two : ∀ w w' : Fin 5 → ZMod 2, vecWeight w = 2 → vecWeight w' = 2 →
    ∃ σ ∈ alternatingGroup (Fin 5), permVec σ w = w' := by
  unfold vecWeight permVec
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem kl_alt_two_trans : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    ∃ σ ∈ alternatingGroup (Fin 5), σ a = c ∧ σ b = d := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem kl_H0_gen : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → v 0 = v 1 →
    ∃ x : Fin 5 → ZMod 2, IsEvenVec x ∧ ∃ σ ∈ alternatingGroup (Fin 5),
      permVec σ klV0 = klV0 ∧ v = x + permVec σ x := by
  unfold IsEvenVec permVec klV0
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem kl_outer_cases : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → v 0 ≠ v 1 →
    vecWeight v = 2 ∨ v = klF 0 ∨ v = klF 1 := by
  unfold IsEvenVec vecWeight klF
  decide +kernel

theorem kl_O6_trans : ∀ v w : Fin 5 → ZMod 2, vecWeight v = 2 → vecWeight w = 2 →
    v 0 ≠ v 1 → w 0 ≠ w 1 →
    ∃ σ ∈ alternatingGroup (Fin 5), permVec σ klV0 = klV0 ∧ permVec σ v = w := by
  unfold vecWeight permVec klV0
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem kl_O6_card :
    (Finset.univ.filter fun v : Fin 5 → ZMod 2 => vecWeight v = 2 ∧ v 0 ≠ v 1).card = 6 := by
  unfold vecWeight
  decide +kernel

theorem kl_three_weight_four : ∀ a b c : Fin 5 → ZMod 2, vecWeight a = 4 → vecWeight b = 4 →
    vecWeight c = 4 → a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0 := by
  unfold vecWeight
  decide +kernel

theorem kl_no_hyperplane (p : (Fin 5 → ZMod 2) → Prop)
    (h1 : ∀ v w, IsEvenVec v → IsEvenVec w → p v → p w → p (v + w))
    (h2 : ∀ v w, IsEvenVec v → IsEvenVec w → ¬ p v → ¬ p w → p (v + w))
    (h3 : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEvenVec v → p v → p (permVec σ v)) :
    ∀ v, IsEvenVec v → p v := by
  have hev0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  by_contra hcon
  push Not at hcon
  obtain ⟨v1, hv1, hn1⟩ := hcon
  obtain ⟨w0, hw0, hnw0⟩ : ∃ w0, vecWeight w0 = 2 ∧ ¬ p w0 := by
    rcases even_weight_cases_five v1 hv1 with h0 | h02 | h04
    · exact absurd (by simpa using h2 0 0 hev0 hev0 (h0 ▸ hn1) (h0 ▸ hn1)) (h0 ▸ hn1)
    · exact ⟨v1, h02, hn1⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := kl_weight_four_sum v1 h04
      by_cases hpx : p x
      · refine ⟨y, hy, fun hpy => hn1 ?_⟩
        rw [hxy]
        exact h1 x y (kl_isEven_of_weight_two x hx) (kl_isEven_of_weight_two y hy) hpx hpy
      · exact ⟨x, hx, hpx⟩
  have hall : ∀ w, vecWeight w = 2 → ¬ p w := by
    intro w hw hpw
    obtain ⟨σ, hσ, hσw⟩ := kl_alt_trans_two w w0 hw hw0
    exact hnw0 (hσw ▸ h3 σ hσ w (kl_isEven_of_weight_two w hw) hpw)
  have hA : vecWeight ![1, 1, 0, 0, 0] = 2 := by unfold vecWeight; decide +kernel
  have hB : vecWeight ![0, 1, 1, 0, 0] = 2 := by unfold vecWeight; decide +kernel
  have hC : vecWeight (![1, 1, 0, 0, 0] + ![0, 1, 1, 0, 0] : Fin 5 → ZMod 2) = 2 := by
    unfold vecWeight; decide +kernel
  exact hall _ hC (h2 _ _ (kl_isEven_of_weight_two _ hA) (kl_isEven_of_weight_two _ hB)
    (hall _ hA) (hall _ hB))

@[expose] def klP : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun v => (∑ i, v i = 0) ∧ v ≠ 0

theorem mem_klP {v : Fin 5 → ZMod 2} : v ∈ klP ↔ IsEvenVec v ∧ v ≠ 0 := by
  simp [klP, IsEvenVec]

@[expose] def klOrb (v : Fin 5 → ZMod 2) : Fin 5 :=
  if v = klV0 then 0
  else if vecWeight v = 2 then (if v 0 = v 1 then 1 else 2)
  else if v 0 = v 1 then 4 else 3

theorem kl_orb_same : ∀ v ∈ klP, ∀ w ∈ klP, klOrb v = klOrb w →
    ∃ σ ∈ alternatingGroup (Fin 5), permVec σ klV0 = klV0 ∧ permVec σ v = w := by
  unfold klP klOrb vecWeight permVec klV0
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

@[expose] def klFrame (W : Finset (Fin 5 → ZMod 2)) : Prop :=
  ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0

instance (W : Finset (Fin 5 → ZMod 2)) : Decidable (klFrame W) := by
  unfold klFrame
  infer_instance

theorem kl_union_core : ∀ J : Finset (Fin 5), (klP.filter fun v => klOrb v ∈ J).card = 5 →
    klFrame (klP.filter fun v => klOrb v ∈ J) → ∀ i, klF i ∈ klP.filter fun v => klOrb v ∈ J := by
  decide +kernel

theorem kl_frame_lemma (W : Finset (Fin 5 → ZMod 2)) (hc : W.card = 5)
    (hE : ∀ v ∈ W, IsEvenVec v) (h0 : ∀ v ∈ W, v ≠ 0)
    (hinv : ∀ σ ∈ alternatingGroup (Fin 5), permVec σ klV0 = klV0 →
      ∀ v ∈ W, permVec σ v ∈ W)
    (hfr : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0) :
    ∀ i, klF i ∈ W := by
  classical
  have hWP : ∀ v ∈ W, v ∈ klP := fun v hv => mem_klP.2 ⟨hE v hv, h0 v hv⟩
  have hW : W = klP.filter fun v => klOrb v ∈ W.image klOrb := by
    ext v
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · exact Finset.mem_filter.2 ⟨hWP v hv, Finset.mem_image.2 ⟨v, hv, rfl⟩⟩
    · obtain ⟨hvP, hvJ⟩ := Finset.mem_filter.1 hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.1 hvJ
      obtain ⟨σ, hσ, hσ0, hσw⟩ := kl_orb_same w (hWP w hw) v hvP hwv
      rw [← hσw]
      exact hinv σ hσ hσ0 w hw
  rw [hW] at hc hfr ⊢
  exact kl_union_core _ hc hfr

end CFSG.OddStandard.SmallF3.Omega
