module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma V5_add_self (v : Fin 5 → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma V5_eq_of_add_eq_zero {a b : Fin 5 → ZMod 2} (h : a + b = 0) : b = a := by
  have h2 : a + b = a + a := by rw [h, V5_add_self]
  exact add_left_cancel h2

private lemma isEvenVec_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

private instance instDecidableIsEvenVec (v : Fin 5 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private lemma IsEvenVec_add {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at hv hw ⊢
  change ∑ i, (v i + w i) = 0
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

private def p (a b : Fin 5) : Fin 5 → ZMod 2 := Pi.single a 1 + Pi.single b 1

private lemma p_even (a b : Fin 5) : IsEvenVec (p a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private lemma p_self (a : Fin 5) : p a a = 0 := by
  unfold p
  exact V5_add_self (Pi.single a 1)

private lemma p_comm (a b : Fin 5) : p a b = p b a := by
  unfold p
  rw [add_comm]

private lemma p_add (a b c : Fin 5) : p a b + p a c = p b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

private lemma permVec_add (σ : Equiv.Perm (Fin 5)) (v w : Fin 5 → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := rfl

private lemma permVec_single (σ : Equiv.Perm (Fin 5)) (a : Fin 5) :
    permVec σ (Pi.single a 1) = Pi.single (σ a) 1 := by
  funext j
  unfold permVec
  simp only [Function.comp_apply, Pi.single_apply]
  by_cases h : j = σ a
  · have h' : σ.symm j = a := (Equiv.symm_apply_eq σ).mpr h
    simp [h, h']
  · have h' : σ.symm j ≠ a := fun hh => h ((Equiv.symm_apply_eq σ).mp hh)
    simp [h, h']

private lemma permVec_p (σ : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    permVec σ (p a b) = p (σ a) (σ b) := by
  unfold p
  rw [permVec_add, permVec_single, permVec_single]

private lemma permVec_smul (σ : Equiv.Perm (Fin 5)) (c : ZMod 2) (v : Fin 5 → ZMod 2) :
    permVec σ (c • v) = c • permVec σ v := rfl

private def F (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (a b c : Fin 5) : Fin 5 → ZMod 2 := k (p a b) (p a c)

private lemma k_zero_right
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hadd₂ : ∀ v w w', IsEvenVec v → IsEvenVec w → IsEvenVec w' →
      k v (w + w') = k v w + k v w') :
    ∀ v, IsEvenVec v → k v 0 = 0 := by
  intro v hv
  have h := hadd₂ v 0 0 hv isEvenVec_zero isEvenVec_zero
  have h' : k v 0 = k v 0 + k v 0 := by simpa using h
  have h2 : k v 0 + k v 0 = k v 0 + 0 := by rw [h'.symm, add_zero]
  exact add_left_cancel h2

private lemma k_zero_left
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hadd₁ : ∀ v v' w, IsEvenVec v → IsEvenVec v' → IsEvenVec w →
      k (v + v') w = k v w + k v' w) :
    ∀ w, IsEvenVec w → k 0 w = 0 := by
  intro w hw
  have h := hadd₁ 0 0 w isEvenVec_zero isEvenVec_zero hw
  have h' : k 0 w = k 0 w + k 0 w := by simpa using h
  have h2 : k 0 w + k 0 w = k 0 w + 0 := by rw [h'.symm, add_zero]
  exact add_left_cancel h2

private lemma k_comm
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hadd₁ : ∀ v v' w, IsEvenVec v → IsEvenVec v' → IsEvenVec w →
      k (v + v') w = k v w + k v' w)
    (hadd₂ : ∀ v w w', IsEvenVec v → IsEvenVec w → IsEvenVec w' →
      k v (w + w') = k v w + k v w')
    (halt : ∀ v, IsEvenVec v → k v v = 0) :
    ∀ v w, IsEvenVec v → IsEvenVec w → k v w = k w v := by
  intro v w hv hw
  have hvw : IsEvenVec (v + w) := IsEvenVec_add hv hw
  have h1 := hadd₁ v w (v + w) hv hw hvw
  have h2 := hadd₂ v v w hv hv hw
  have h3 := hadd₂ w v w hw hv hw
  have h0 := halt (v + w) hvw
  rw [h1, h2, h3, halt v hv, halt w hw] at h0
  have h0' : k v w + k w v = 0 := by simpa using h0
  exact (V5_eq_of_add_eq_zero h0').symm

private lemma F_symm
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hk : ∀ v w, IsEvenVec v → IsEvenVec w → k v w = k w v) (a b c : Fin 5) :
    F k a b c = F k a c b := by
  unfold F
  exact hk (p a b) (p a c) (p_even a b) (p_even a c)

private lemma F_swap_ab
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hadd₂ : ∀ v w w', IsEvenVec v → IsEvenVec w → IsEvenVec w' →
      k v (w + w') = k v w + k v w')
    (halt : ∀ v, IsEvenVec v → k v v = 0) (a b c : Fin 5) :
    F k a b c = F k b a c := by
  have h1 : k (p a b) (p a c + p a b) =
      k (p a b) (p a c) + k (p a b) (p a b) :=
    hadd₂ (p a b) (p a c) (p a b) (p_even a b) (p_even a c) (p_even a b)
  have h2 : k (p a b) (p a b) = 0 := halt (p a b) (p_even a b)
  have h3 : p a c + p a b = p b c := by
    rw [p_add a c b, p_comm c b]
  calc
    F k a b c = k (p a b) (p a c + p a b) := by
      unfold F
      rw [h1, h2, add_zero]
    _ = k (p a b) (p b c) := by rw [h3]
    _ = F k b a c := by
      unfold F
      rw [p_comm b a]

private lemma permVec_F
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hequi : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v w, IsEvenVec v → IsEvenVec w →
      k (permVec σ v) (permVec σ w) = permVec σ (k v w))
    {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ alternatingGroup (Fin 5)) (a b c : Fin 5) :
    permVec σ (F k a b c) = F k (σ a) (σ b) (σ c) := by
  unfold F
  rw [← hequi σ hσ (p a b) (p a c) (p_even a b) (p_even a c)]
  rw [permVec_p, permVec_p]

private lemma F_eq_smul_of_maps
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hequi : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v w, IsEvenVec v → IsEvenVec w →
      k (permVec σ v) (permVec σ w) = permVec σ (k v w))
    (q : ZMod 2) (hu : F k 0 1 2 = q • p 3 4)
    {a b c d e : Fin 5} (σ : Equiv.Perm (Fin 5))
    (hσ : σ ∈ alternatingGroup (Fin 5))
    (h0 : σ 0 = a) (h1 : σ 1 = b) (h2 : σ 2 = c)
    (h3 : σ 3 = d) (h4 : σ 4 = e) :
    F k a b c = q • p d e := by
  have heq : F k a b c = permVec σ (F k 0 1 2) := by
    rw [permVec_F k hequi hσ 0 1 2, h0, h1, h2]
  calc
    F k a b c = permVec σ (F k 0 1 2) := heq
    _ = permVec σ (q • p 3 4) := by rw [hu]
    _ = q • permVec σ (p 3 4) := permVec_smul σ q (p 3 4)
    _ = q • p (σ 3) (σ 4) := by rw [permVec_p]
    _ = q • p d e := by rw [h3, h4]

private lemma exists_alt_triple :
    ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧
        σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  decide +kernel

private lemma exists_alt_013 :
    ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ 0 = 0 ∧ σ 1 = 1 ∧
      σ 2 = 3 ∧ σ 3 = 4 ∧ σ 4 = 2 := by
  decide +kernel

private lemma exists_alt_203 :
    ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ 0 = 2 ∧ σ 1 = 0 ∧
      σ 2 = 3 ∧ σ 3 = 4 ∧ σ 4 = 1 := by
  decide +kernel

private lemma exists_alt_213 :
    ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ 0 = 2 ∧ σ 1 = 1 ∧
      σ 2 = 3 ∧ σ 3 = 0 ∧ σ 4 = 4 := by
  decide +kernel

private lemma eq_smul_p34_of_coords :
    ∀ u : Fin 5 → ZMod 2, u 0 = u 1 → u 1 = u 2 → u 3 = u 4 →
      IsEvenVec u → u = u 3 • p 3 4 := by
  decide +kernel

private lemma even_decomp :
    ∀ v : Fin 5 → ZMod 2, IsEvenVec v → ∃ a b c d : Fin 5, v = p a b + p c d := by
  decide +kernel

theorem prince_bilinear_zero
    (k : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hev : ∀ v w, IsEvenVec v → IsEvenVec w → IsEvenVec (k v w))
    (hadd₁ : ∀ v v' w, IsEvenVec v → IsEvenVec v' → IsEvenVec w →
      k (v + v') w = k v w + k v' w)
    (hadd₂ : ∀ v w w', IsEvenVec v → IsEvenVec w → IsEvenVec w' →
      k v (w + w') = k v w + k v w')
    (halt : ∀ v, IsEvenVec v → k v v = 0)
    (hequi : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v w, IsEvenVec v → IsEvenVec w →
      k (permVec σ v) (permVec σ w) = permVec σ (k v w)) :
    ∀ v w, IsEvenVec v → IsEvenVec w → k v w = 0 := by
  have hk : ∀ v w, IsEvenVec v → IsEvenVec w → k v w = k w v :=
    k_comm k hadd₁ hadd₂ halt
  have hzeroL := k_zero_left k hadd₁
  have hzeroR := k_zero_right k hadd₂
  let σ3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2
  let τ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 3 4
  have hσ3 : σ3 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  have hτ : τ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  let u : Fin 5 → ZMod 2 := F k 0 1 2
  have hfix3 : permVec σ3 u = u := by
    have h1 : permVec σ3 (F k 0 1 2) = F k (σ3 0) (σ3 1) (σ3 2) :=
      permVec_F k hequi hσ3 0 1 2
    have h2 : F k (σ3 0) (σ3 1) (σ3 2) = F k 1 2 0 := by
      rw [show σ3 0 = 1 by decide +kernel, show σ3 1 = 2 by decide +kernel,
        show σ3 2 = 0 by decide +kernel]
    have h3 : F k 1 2 0 = F k 1 0 2 := F_symm k hk 1 2 0
    have h4 : F k 1 0 2 = F k 0 1 2 := F_swap_ab k hadd₂ halt 1 0 2
    change permVec σ3 (F k 0 1 2) = F k 0 1 2
    rw [h1, h2, h3, h4]
  have hfixτ : permVec τ u = u := by
    have h1 : permVec τ (F k 0 1 2) = F k (τ 0) (τ 1) (τ 2) :=
      permVec_F k hequi hτ 0 1 2
    have h2 : F k (τ 0) (τ 1) (τ 2) = F k 1 0 2 := by
      rw [show τ 0 = 1 by decide +kernel, show τ 1 = 0 by decide +kernel,
        show τ 2 = 2 by decide +kernel]
    have h3 : F k 1 0 2 = F k 0 1 2 := F_swap_ab k hadd₂ halt 1 0 2
    change permVec τ (F k 0 1 2) = F k 0 1 2
    rw [h1, h2, h3]
  have hu01 : u 0 = u 1 := by
    have h := congrFun hfix3 1
    have hs : σ3.symm 1 = 0 := by decide +kernel
    simpa [permVec, hs] using h
  have hu02 : u 0 = u 2 := by
    have h := congrFun hfix3 0
    have hs : σ3.symm 0 = 2 := by decide +kernel
    simpa [permVec, hs] using h.symm
  have hu12 : u 1 = u 2 := hu01.symm.trans hu02
  have hu34 : u 3 = u 4 := by
    have h := congrFun hfixτ 3
    have hs : τ.symm 3 = 4 := by decide +kernel
    simpa [permVec, hs] using h.symm
  have hu : u = u 3 • p 3 4 :=
    eq_smul_p34_of_coords u hu01 hu12 hu34 (hev (p 0 1) (p 0 2) (p_even 0 1) (p_even 0 2))
  let q : ZMod 2 := u 3
  have huq : F k 0 1 2 = q • p 3 4 := by
    change u = q • p 3 4
    simpa [q] using hu
  have hF013 : F k 0 1 3 = q • p 2 4 := by
    obtain ⟨σ, hsign, h0, h1, h2, h3, h4⟩ := exists_alt_013
    have hσ : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hsign
    have hF := F_eq_smul_of_maps k hequi q huq σ hσ h0 h1 h2 h3 h4
    simpa [p_comm 4 2] using hF
  have hF203 : F k 2 0 3 = q • p 1 4 := by
    obtain ⟨σ, hsign, h0, h1, h2, h3, h4⟩ := exists_alt_203
    have hσ : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hsign
    have hF := F_eq_smul_of_maps k hequi q huq σ hσ h0 h1 h2 h3 h4
    simpa [p_comm 4 1] using hF
  have hF213 : F k 2 1 3 = q • p 0 4 := by
    obtain ⟨σ, hsign, h0, h1, h2, h3, h4⟩ := exists_alt_213
    have hσ : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hsign
    exact F_eq_smul_of_maps k hequi q huq σ hσ h0 h1 h2 h3 h4
  have hx1 : k (p 0 1) (p 2 3) = q • p 2 3 := by
    have hsum2 : p 3 4 + p 2 4 = p 2 3 := by
      rw [p_comm 3 4, p_comm 2 4, p_comm 2 3]
      exact p_add 4 3 2
    calc
      k (p 0 1) (p 2 3) = k (p 0 1) (p 0 2 + p 0 3) := by rw [p_add 0 2 3]
      _ = k (p 0 1) (p 0 2) + k (p 0 1) (p 0 3) :=
        hadd₂ (p 0 1) (p 0 2) (p 0 3) (p_even 0 1) (p_even 0 2) (p_even 0 3)
      _ = F k 0 1 2 + F k 0 1 3 := rfl
      _ = q • p 3 4 + q • p 2 4 := by rw [huq, hF013]
      _ = q • (p 3 4 + p 2 4) := by rw [smul_add]
      _ = q • p 2 3 := by rw [hsum2]
  have hx2 : k (p 0 1) (p 2 3) = q • p 0 1 := by
    have hsum3 : p 1 4 + p 0 4 = p 0 1 := by
      rw [p_comm 1 4, p_comm 0 4, p_comm 0 1]
      exact p_add 4 1 0
    calc
      k (p 0 1) (p 2 3) = k (p 2 0 + p 2 1) (p 2 3) := by rw [p_add 2 0 1]
      _ = k (p 2 0) (p 2 3) + k (p 2 1) (p 2 3) :=
        hadd₁ (p 2 0) (p 2 1) (p 2 3) (p_even 2 0) (p_even 2 1) (p_even 2 3)
      _ = F k 2 0 3 + F k 2 1 3 := rfl
      _ = q • p 1 4 + q • p 0 4 := by rw [hF203, hF213]
      _ = q • (p 1 4 + p 0 4) := by rw [smul_add]
      _ = q • p 0 1 := by rw [hsum3]
  have hq : q = 0 := by
    have h : q • p 2 3 = q • p 0 1 := by rw [← hx1, hx2]
    by_contra hq0
    exact (by decide +kernel : p 2 3 ≠ p 0 1) ((smul_right_inj hq0).mp h)
  have hFzero : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c → F k a b c = 0 := by
    intro a b c hab hac hbc
    obtain ⟨σ, hsign, h0, h1, h2⟩ := exists_alt_triple a b c hab hac hbc
    have hσ : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hsign
    have hF := F_eq_smul_of_maps k hequi q huq σ hσ h0 h1 h2 rfl rfl
    rw [hF, hq, zero_smul]
  have hpair : ∀ a b c d : Fin 5, k (p a b) (p c d) = 0 := by
    intro a b c d
    by_cases hab : a = b
    · subst b
      rw [p_self]
      exact hzeroL (p c d) (p_even c d)
    by_cases hcd : c = d
    · subst d
      rw [p_self]
      exact hzeroR (p a b) (p_even a b)
    by_cases hac : a = c
    · subst c
      by_cases hbd : b = d
      · subst d
        exact halt (p a b) (p_even a b)
      · have h1 := hFzero a b d hab (by simpa using hcd) hbd
        simpa [F] using h1
    by_cases had : a = d
    · subst d
      by_cases hbc : b = c
      · subst c
        rw [p_comm b a]
        exact halt (p a b) (p_even a b)
      · have h1 := hFzero a b c hab hac hbc
        simpa [F, p_comm c a] using h1
    by_cases hbc : b = c
    · subst c
      rw [p_comm a b]
      have h1 := hFzero b a d (fun h => hab h.symm) hcd had
      simpa [F] using h1
    by_cases hbd : b = d
    · subst d
      rw [p_comm a b, p_comm c b]
      have h1 := hFzero b a c (fun h => hab h.symm) hbc hac
      simpa [F] using h1
    · have h1 := hFzero a b c hab hac hbc
      have h2 := hFzero a b d hab had hbd
      calc
        k (p a b) (p c d) = k (p a b) (p a c + p a d) := by rw [p_add a c d]
        _ = k (p a b) (p a c) + k (p a b) (p a d) :=
          hadd₂ (p a b) (p a c) (p a d) (p_even a b) (p_even a c) (p_even a d)
        _ = F k a b c + F k a b d := rfl
        _ = 0 + 0 := by rw [h1, h2]
        _ = 0 := zero_add 0
  intro v w hv hw
  obtain ⟨a, b, c, d, rfl⟩ := even_decomp v hv
  obtain ⟨e, f, g, h, rfl⟩ := even_decomp w hw
  have h1 : k (p a b + p c d) (p e f + p g h) =
      k (p a b) (p e f + p g h) + k (p c d) (p e f + p g h) :=
    hadd₁ (p a b) (p c d) (p e f + p g h) (p_even a b) (p_even c d)
      (IsEvenVec_add (p_even e f) (p_even g h))
  have h2 : k (p a b) (p e f + p g h) = k (p a b) (p e f) + k (p a b) (p g h) :=
    hadd₂ (p a b) (p e f) (p g h) (p_even a b) (p_even e f) (p_even g h)
  have h3 : k (p c d) (p e f + p g h) = k (p c d) (p e f) + k (p c d) (p g h) :=
    hadd₂ (p c d) (p e f) (p g h) (p_even c d) (p_even e f) (p_even g h)
  rw [h1, h2, h3, hpair a b e f, hpair a b g h, hpair c d e f, hpair c d g h]
  simp

end CFSG.OddStandard.SmallF3.Omega
