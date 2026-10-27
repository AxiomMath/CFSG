module

public import CFSG.Certificates.Kernel.Spor.Fi24OrbSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixCoset

public section

namespace CFSG.KC.Fi24OrbT

open CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbS CFSG.KC.Fi24FixC

section Forest

variable {FD S : ℕ → ℕ} {TG : ℕ → ℕ → ℕ} {n s0 r1 : ℕ}

@[expose] def rootOf (s0 r1 c : ℕ) : ℕ := if c = 2 then s0 else r1

theorem forest_up (hF : ∀ r, 1 ≤ r → r < n → ForP FD S TG n s0 r1 r) (P : ℕ → Prop)
    (hP : ∀ k p, k < 10 → k ≠ 8 → 1 ≤ p → p < n → (P (tk TG k p) ↔ P p)) :
    ∀ d r, fDep (FD r) = d → 1 ≤ r → r < n → P r → P (rootOf s0 r1 (fComp (FD r))) := by
  intro d
  induction d with
  | zero =>
    intro r hd h1 hn hr
    rcases (hF r h1 hn).2 with ⟨-, ⟨rfl, hc⟩ | ⟨rfl, hc⟩⟩ | ⟨-, -, he, -⟩
    · rw [hc]
      exact hr
    · rw [hc]
      exact hr
    · omega
  | succ d ih =>
    intro r hd h1 hn hr
    rcases (hF r h1 hn).2 with ⟨h0, -⟩ | ⟨hp1, hpn, he, hc, hk, hk8, ht⟩
    · omega
    · have hpr : P (fPar (FD r)) := by
        rw [← hP _ _ hk hk8 hp1 hpn, ht]
        exact hr
      have := ih (fPar (FD r)) (by omega) hp1 hpn hpr
      rwa [hc] at this

theorem forest_down (hF : ∀ r, 1 ≤ r → r < n → ForP FD S TG n s0 r1 r) (P : ℕ → Prop)
    (hP : ∀ k p, k < 10 → k ≠ 8 → 1 ≤ p → p < n → (P (tk TG k p) ↔ P p)) (c : ℕ)
    (hroot : P (rootOf s0 r1 c)) :
    ∀ d r, fDep (FD r) = d → 1 ≤ r → r < n → fComp (FD r) = c → P r := by
  intro d
  induction d with
  | zero =>
    intro r hd h1 hn hc
    rcases (hF r h1 hn).2 with ⟨-, ⟨rfl, hc2⟩ | ⟨rfl, hc1⟩⟩ | ⟨-, -, he, -⟩
    · rw [← hc, hc2] at hroot
      exact hroot
    · rw [← hc, hc1] at hroot
      exact hroot
    · omega
  | succ d ih =>
    intro r hd h1 hn hc
    rcases (hF r h1 hn).2 with ⟨h0, -⟩ | ⟨hp1, hpn, he, hcp, hk, hk8, ht⟩
    · omega
    · have hpr := ih (fPar (FD r)) (by omega) hp1 hpn (by rw [hcp, hc])
      rw [← ht, hP _ _ hk hk8 hp1 hpn]
      exact hpr

theorem forest_closed (hF : ∀ r, 1 ≤ r → r < n → ForP FD S TG n s0 r1 r) (P : ℕ → Prop)
    (hP : ∀ k p, k < 10 → k ≠ 8 → 1 ≤ p → p < n → (P (tk TG k p) ↔ P p)) {i : ℕ}
    (hi1 : 1 ≤ i) (hin : i < n) (hPi : P i) :
    ∀ r, 1 ≤ r → r < n → fComp (FD r) = fComp (FD i) → P r := by
  intro r h1 hn hc
  exact forest_down hF P hP (fComp (FD i)) (forest_up hF P hP _ i rfl hi1 hin hPi) _ r rfl h1 hn hc

end Forest

section Restrict

variable {K : Type*} [Field K] {D d : ℕ} (M : Matrix (Fin D) (Fin d) K) (hdD : d ≤ D)

@[expose] def top (X : Matrix (Fin D) (Fin d) K) : Matrix (Fin d) (Fin d) K :=
  fun i j => X (Fin.castLE hdD i) j

variable {M hdD}

theorem top_mul (hM : top hdD M = 1) (C : Matrix (Fin d) (Fin d) K) : top hdD (M * C) = C := by
  ext i j
  change (M * C) (Fin.castLE hdD i) j = C i j
  rw [Matrix.mul_apply]
  have h : ∀ l, M (Fin.castLE hdD i) l = (1 : Matrix (Fin d) (Fin d) K) i l := fun l => by
    rw [← hM]
    rfl
  simp only [h, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

noncomputable abbrev colSp (M : Matrix (Fin D) (Fin d) K) : Submodule K (Fin D → K) :=
  LinearMap.range M.mulVecLin

theorem eq_mul_top (hM : top hdD M = 1) {X : Matrix (Fin D) (Fin d) K}
    (hX : ∀ j, (fun i => X i j) ∈ colSp M) : X = M * top hdD X := by
  ext i j
  obtain ⟨c, hc⟩ := hX j
  have hcj : c = fun l => top hdD X l j := by
    funext l
    have := congrFun hc (Fin.castLE hdD l)
    simp only [Matrix.mulVecLin_apply] at this
    rw [Matrix.mulVec, dotProduct] at this
    have h : ∀ m, M (Fin.castLE hdD l) m = (1 : Matrix (Fin d) (Fin d) K) l m := fun m => by
      rw [← hM]
      rfl
    simp only [h, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at this
    exact this
  have := congrFun hc i
  simp only [Matrix.mulVecLin_apply] at this
  rw [← this, hcj, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem col_mem {g : GL (Fin D) K} (hg : g ∈ stab (colSp M)) (j : Fin d) :
    (fun i => ((g : Matrix (Fin D) (Fin D) K) * M) i j) ∈ colSp M := by
  rw [mem_stab] at hg
  rw [← hg]
  refine Submodule.mem_map.2 ⟨M.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩, ?_⟩
  funext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

@[expose] noncomputable def restr (hdD : d ≤ D) (M : Matrix (Fin D) (Fin d) K) (g : GL (Fin D) K) :
    Matrix (Fin d) (Fin d) K :=
  top hdD ((g : Matrix (Fin D) (Fin D) K) * M)

theorem mul_restr (hM : top hdD M = 1) {g : GL (Fin D) K} (hg : g ∈ stab (colSp M)) :
    (g : Matrix (Fin D) (Fin D) K) * M = M * restr hdD M g :=
  eq_mul_top hM (col_mem hg)

@[expose] noncomputable def restrMon (hM : top hdD M = 1) :
    stab (colSp M) →* Matrix (Fin d) (Fin d) K where
  toFun g := restr hdD M g
  map_one' := by
    change top hdD ((1 : Matrix (Fin D) (Fin D) K) * M) = 1
    rw [Matrix.one_mul, hM]
  map_mul' g h := by
    change top hdD (((g : GL (Fin D) K) * (h : GL (Fin D) K) : GL (Fin D) K).val * M) = _
    rw [Units.val_mul, Matrix.mul_assoc, mul_restr hM h.2, ← Matrix.mul_assoc, mul_restr hM g.2,
      Matrix.mul_assoc, top_mul hM]

@[expose] noncomputable def restrHom (hM : top hdD M = 1) : stab (colSp M) →* GL (Fin d) K :=
  (restrMon hM).toHomUnits

theorem restrHom_val (hM : top hdD M = 1) (g : stab (colSp M)) :
    ((restrHom hM g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = restr hdD M g := rfl

end Restrict

end CFSG.KC.Fi24OrbT

end
