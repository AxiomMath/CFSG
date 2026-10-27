module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Basic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma
import CFSG.LieType.Chevalley.C2E6RootOperators

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

section Entry

variable {K : Type} [Field K] [Finite K] {σ η : K ≃+* K} {p : ℕ}

noncomputable def coordOr (z : RootModule Tag.E6 K) (δ : Fin Tag.E6.rank → ℤ) : K :=
  by
    classical
    exact if h : IsRoot Tag.E6 δ then z (rootLabel h) else 0

section NoCert

private abbrev ev6 (i : Fin 6) : Fin Tag.E6.rank → ℤ := Pi.single i 1

private abbrev twE6wmPerm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

private def twE6wmMv : ℕ → (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)
  | 0 => fun v => reflect Tag.E6 (1 : Fin 6) v
  | 1 => fun v => reflect Tag.E6 (3 : Fin 6) v
  | 2 => fun v => reflect Tag.E6 (0 : Fin 6) (reflect Tag.E6 (5 : Fin 6) v)
  | 3 => fun v => reflect Tag.E6 (2 : Fin 6) (reflect Tag.E6 (4 : Fin 6) v)
  | _ => fun v => v

private def twE6wmApply (l : List ℕ) (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  l.foldl (fun w k => twE6wmMv k w) v

private def twE6wmHt (v : Fin Tag.E6.rank → ℤ) : ℤ :=
  v (0 : Fin 6) + v (1 : Fin 6) + v (2 : Fin 6) + v (3 : Fin 6) + v (4 : Fin 6) + v (5 : Fin 6)

private theorem twE6wm_check_fixed :
    ∀ g ∈ rootFinset Tag.E6, permLattice twE6wmPerm g = g →
      (g = ev6 1 ∨ g = -ev6 1 ∨ g = ev6 3 ∨ g = -ev6 3) ∨
        ∃ k : Fin 4, permLattice twE6wmPerm (twE6wmMv k g) = twE6wmMv k g ∧
          (twE6wmHt (twE6wmMv k g)).natAbs < (twE6wmHt g).natAbs := by
  decide +kernel

private theorem twE6wm_check_nonfixed :
    ∀ g ∈ rootFinset Tag.E6, ¬ permLattice twE6wmPerm g = g →
      (g = ev6 0 ∨ g = -ev6 0 ∨ g = ev6 2 ∨ g = -ev6 2 ∨ g = ev6 4 ∨ g = -ev6 4 ∨
          g = ev6 5 ∨ g = -ev6 5) ∨
        ∃ k : Fin 4, ¬ permLattice twE6wmPerm (twE6wmMv k g) = twE6wmMv k g ∧
          (twE6wmHt (twE6wmMv k g)).natAbs < (twE6wmHt g).natAbs := by
  decide +kernel

private theorem twE6wm_base_fixed :
    twE6wmApply [0] (-ev6 1) = ev6 1 ∧ twE6wmApply [0, 1] (ev6 3) = ev6 1 ∧
      twE6wmApply [1, 0, 1] (-ev6 3) = ev6 1 := by
  decide +kernel

private theorem twE6wm_base_nonfixed :
    twE6wmApply [2] (-ev6 0) = ev6 0 ∧ twE6wmApply [2, 3] (ev6 2) = ev6 0 ∧
      twE6wmApply [2, 3, 2] (-ev6 2) = ev6 0 ∧ twE6wmApply [1, 3, 1, 2, 3] (ev6 4) = ev6 0 ∧
      twE6wmApply [1, 3, 1, 2, 3, 2] (-ev6 4) = ev6 0 ∧
      twE6wmApply [3, 1, 2, 3, 1, 2, 3] (ev6 5) = ev6 0 ∧
      twE6wmApply [2, 3, 1, 2, 3, 1, 2, 3] (-ev6 5) = ev6 0 := by
  decide +kernel

private theorem twE6wm_nonroot_05 :
    (ev6 5 + -ev6 0 ≠ 0 ∧ ev6 5 + -ev6 0 ∉ rootFinset Tag.E6) ∧
      (-ev6 5 + ev6 0 ≠ 0 ∧ -ev6 5 + ev6 0 ∉ rootFinset Tag.E6) ∧
      (ev6 5 + ev6 0 ≠ 0 ∧ ev6 5 + ev6 0 ∉ rootFinset Tag.E6) := by
  decide +kernel

private theorem twE6wm_nonroot_24 :
    (ev6 4 + -ev6 2 ≠ 0 ∧ ev6 4 + -ev6 2 ∉ rootFinset Tag.E6) ∧
      (-ev6 4 + ev6 2 ≠ 0 ∧ -ev6 4 + ev6 2 ∉ rootFinset Tag.E6) ∧
      (ev6 4 + ev6 2 ≠ 0 ∧ ev6 4 + ev6 2 ∉ rootFinset Tag.E6) := by
  decide +kernel

end NoCert

private theorem twE6wm_weyl_eq (i : Fin 6) :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) =
      xE6 (ev6 i) 1 * xE6 (-ev6 i) (-1) * xE6 (ev6 i) 1 := by
  simp [CFSG.LieType.Steinberg.weylElement, xE6, ev6]

private theorem twE6wm_weyl_mem {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    {i : Fin 6} (hi : i ∈ ({1, 3} : Finset (Fin 6))) :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) ∈ R' := by
  have h1 : xE6 (ev6 i) 1 ∈ R' := hR'.fixedX i hi 1 (map_one σ) (map_one η)
  have h2 : xE6 (-ev6 i) (-1) ∈ R' :=
    hR'.fixedY i hi (-1) (by rw [map_neg, map_one]) (by rw [map_neg, map_one])
  rw [twE6wm_weyl_eq]
  exact R'.mul_mem (R'.mul_mem h1 h2) h1

private theorem twE6wm_isRoot_e (i : Fin 6) : IsRoot Tag.E6 (ev6 i) :=
  IsRoot.basis (τ := Tag.E6) i

private theorem twE6wm_single {R' : Subgroup ↥(adjointGroup Tag.E6 K)} {i : Fin 6}
    (hi : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) ∈ R')
    (α : Fin Tag.E6.rank → ℤ) : WeylMove R' α (reflect Tag.E6 i α) := by
  intro hα _
  obtain ⟨ε, hε, h1, h2⟩ := weyl_step_explicit (τ := Tag.E6) (K := K) i hα
  exact ⟨_, hi, ε, hε, h1, h2⟩

private theorem twE6wm_pair {R' : Subgroup ↥(adjointGroup Tag.E6 K)} {i j : Fin 6}
    (hij : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) *
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) j (1 : Kˣ) ∈ R')
    (α : Fin Tag.E6.rank → ℤ) : WeylMove R' α (reflect Tag.E6 i (reflect Tag.E6 j α)) := by
  intro hα _
  obtain ⟨ε₁, hε₁, h₁, k₁⟩ := weyl_step_explicit (τ := Tag.E6) (K := K) j hα
  obtain ⟨ε₂, hε₂, h₂, k₂⟩ :=
    weyl_step_explicit (τ := Tag.E6) (K := K) i (IsRoot.reflect (τ := Tag.E6) j hα)
  refine ⟨_, hij, ε₂ * ε₁, ?_, ?_, ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> simp
  · rw [map_mul, Module.End.mul_apply, h₁, map_smul, h₂, smul_smul]
    congr 1
    push_cast
    ring
  · intro z
    rw [map_mul, Module.End.mul_apply, k₂, k₁]
    push_cast
    ring

private theorem twE6wm_pair_identity {G : Type*} [Group G] {A B C D : G}
    (h1 : Commute C B) (h2 : Commute D A) (h3 : Commute C A) :
    A * C * (B * D) * (A * C) = A * B * A * (C * D * C) := by
  have e1 : C * D * A * C = A * C * D * C := by
    calc C * D * A * C = C * (D * A) * C := by simp only [mul_assoc]
      _ = C * (A * D) * C := by rw [h2.eq]
      _ = C * A * D * C := by simp only [mul_assoc]
      _ = A * C * D * C := by rw [h3.eq]
  calc A * C * (B * D) * (A * C) = A * (C * B) * D * (A * C) := by simp only [mul_assoc]
    _ = A * (B * C) * D * (A * C) := by rw [h1.eq]
    _ = A * B * (C * D * A * C) := by simp only [mul_assoc]
    _ = A * B * (A * C * D * C) := by rw [e1]
    _ = A * B * A * (C * D * C) := by simp only [mul_assoc]

private theorem twE6wm_commute (a b : K) {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hδ : IsRoot Tag.E6 δ) (hne : γ + δ ≠ 0) (hnr : γ + δ ∉ rootFinset Tag.E6) :
    Commute (xE6 γ a) (xE6 δ b) := by
  obtain ⟨D, hD, hG2⟩ := exists_adjData_valid_E (τ := Tag.E6) (Or.inl rfl)
  exact commute_xPar hD hG2 hγ hδ hne (fun h => hnr (mem_rootFinset.2 h)) a b

private theorem twE6wm_W_mul {R' : Subgroup ↥(adjointGroup Tag.E6 K)} {i j : Fin 6}
    (hAC : xE6 (ev6 i) (1 : K) * xE6 (ev6 j) (1 : K) ∈ R')
    (hBD : xE6 (-ev6 i) (-1 : K) * xE6 (-ev6 j) (-1 : K) ∈ R')
    (h1 : Commute (xE6 (ev6 j) (1 : K)) (xE6 (-ev6 i) (-1 : K)))
    (h2 : Commute (xE6 (-ev6 j) (-1 : K)) (xE6 (ev6 i) (1 : K)))
    (h3 : Commute (xE6 (ev6 j) (1 : K)) (xE6 (ev6 i) (1 : K))) :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) *
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) j (1 : Kˣ) ∈ R' := by
  have key := twE6wm_pair_identity (A := xE6 (ev6 i) 1) (B := xE6 (-ev6 i) (-1))
    (C := xE6 (ev6 j) 1) (D := xE6 (-ev6 j) (-1)) h1 h2 h3
  rw [twE6wm_weyl_eq i, twE6wm_weyl_eq j, ← key]
  exact R'.mul_mem (R'.mul_mem hAC hBD) hAC

private theorem twE6wm_W05 {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R') :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) (0 : Fin 6) (1 : Kˣ) *
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) (5 : Fin 6) (1 : Kˣ)
      ∈ R' := by
  have hAC : xE6 (ev6 0) (1 : K) * xE6 (ev6 5) (1 : K) ∈ R' := by
    have h := hR'.orbX (0, 5) (by decide) 1 (map_one η)
    rw [map_one σ] at h
    exact h
  have hBD : xE6 (-ev6 0) (-1 : K) * xE6 (-ev6 5) (-1 : K) ∈ R' := by
    have h := hR'.orbY (0, 5) (by decide) (-1) (by rw [map_neg, map_one])
    rw [map_neg, map_one] at h
    exact h
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := twE6wm_nonroot_05
  exact twE6wm_W_mul (i := 0) (j := 5) hAC hBD
    (twE6wm_commute 1 (-1) (twE6wm_isRoot_e 5) (isRoot_neg_single Tag.E6 0) a1 a2)
    (twE6wm_commute (-1) 1 (isRoot_neg_single Tag.E6 5) (twE6wm_isRoot_e 0) b1 b2)
    (twE6wm_commute 1 1 (twE6wm_isRoot_e 5) (twE6wm_isRoot_e 0) c1 c2)

private theorem twE6wm_W24 {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R') :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) (2 : Fin 6) (1 : Kˣ) *
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) (4 : Fin 6) (1 : Kˣ)
      ∈ R' := by
  have hAC : xE6 (ev6 2) (1 : K) * xE6 (ev6 4) (1 : K) ∈ R' := by
    have h := hR'.orbX (2, 4) (by decide) 1 (map_one η)
    rw [map_one σ] at h
    exact h
  have hBD : xE6 (-ev6 2) (-1 : K) * xE6 (-ev6 4) (-1 : K) ∈ R' := by
    have h := hR'.orbY (2, 4) (by decide) (-1) (by rw [map_neg, map_one])
    rw [map_neg, map_one] at h
    exact h
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := twE6wm_nonroot_24
  exact twE6wm_W_mul (i := 2) (j := 4) hAC hBD
    (twE6wm_commute 1 (-1) (twE6wm_isRoot_e 4) (isRoot_neg_single Tag.E6 2) a1 a2)
    (twE6wm_commute (-1) 1 (isRoot_neg_single Tag.E6 4) (twE6wm_isRoot_e 2) b1 b2)
    (twE6wm_commute 1 1 (twE6wm_isRoot_e 4) (twE6wm_isRoot_e 2) c1 c2)

private theorem twE6wm_mv_root (k : ℕ) {v : Fin Tag.E6.rank → ℤ} (hv : IsRoot Tag.E6 v) :
    IsRoot Tag.E6 (twE6wmMv k v) := by
  match k with
  | 0 => exact IsRoot.reflect (τ := Tag.E6) 1 hv
  | 1 => exact IsRoot.reflect (τ := Tag.E6) 3 hv
  | 2 => exact IsRoot.reflect (τ := Tag.E6) 0 (IsRoot.reflect (τ := Tag.E6) 5 hv)
  | 3 => exact IsRoot.reflect (τ := Tag.E6) 2 (IsRoot.reflect (τ := Tag.E6) 4 hv)
  | _ + 4 => exact hv

private theorem twE6wm_move_root {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    (k : ℕ) (v : Fin Tag.E6.rank → ℤ) : WeylMove R' v (twE6wmMv k v) := by
  match k with
  | 0 => exact twE6wm_single (twE6wm_weyl_mem hR' (i := 1) (by decide)) v
  | 1 => exact twE6wm_single (twE6wm_weyl_mem hR' (i := 3) (by decide)) v
  | 2 => exact twE6wm_pair (twE6wm_W05 hR') v
  | 3 => exact twE6wm_pair (twE6wm_W24 hR') v
  | _ + 4 => exact WeylMove.refl R' v

private theorem twE6wm_chain {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    (l : List ℕ) (v : Fin Tag.E6.rank → ℤ) (hv : IsRoot Tag.E6 v) :
    WeylMove R' v (twE6wmApply l v) := by
  induction l generalizing v with
  | nil => exact WeylMove.refl R' v
  | cons k l ih =>
    exact WeylMove.trans (twE6wm_move_root hR' k v) (ih (twE6wmMv k v) (twE6wm_mv_root k hv))
      (twE6wm_mv_root k hv)

private theorem twE6wm_fixed_aux {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R') :
    ∀ (n : ℕ) (g : Fin Tag.E6.rank → ℤ), (twE6wmHt g).natAbs = n → IsRoot Tag.E6 g →
      permLattice TwistTag.E6.perm g = g → WeylMove R' g (ev6 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hn hg hfix
    rcases twE6wm_check_fixed g (mem_rootFinset.2 hg) hfix with h | ⟨k, hfixk, hlt⟩
    · obtain ⟨b1, b2, b3⟩ := twE6wm_base_fixed
      rcases h with rfl | rfl | rfl | rfl
      · exact WeylMove.refl R' _
      · have h1 := twE6wm_chain hR' [0] (-ev6 1) (isRoot_neg_single Tag.E6 1)
        rw [b1] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [0, 1] (ev6 3) (twE6wm_isRoot_e 3)
        rw [b2] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [1, 0, 1] (-ev6 3) (isRoot_neg_single Tag.E6 3)
        rw [b3] at h1
        exact h1
    · have hv : IsRoot Tag.E6 (twE6wmMv k g) := twE6wm_mv_root k hg
      have hlt' : (twE6wmHt (twE6wmMv k g)).natAbs < n := by
        rw [← hn]
        exact hlt
      have ih' := ih (twE6wmHt (twE6wmMv k g)).natAbs hlt' (twE6wmMv k g) rfl hv hfixk
      exact WeylMove.trans (twE6wm_move_root hR' k g) ih' hv

private theorem twE6wm_fixed_to_e1 {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    (g : Fin Tag.E6.rank → ℤ) (hg : IsRoot Tag.E6 g)
    (hfix : permLattice TwistTag.E6.perm g = g) : WeylMove R' g (ev6 1) :=
  twE6wm_fixed_aux hR' _ g rfl hg hfix

theorem twE6_weylMove_fixed {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    {γ γ' : Fin Tag.E6.rank → ℤ} (hργ : permLattice TwistTag.E6.perm γ = γ)
    (hργ' : permLattice TwistTag.E6.perm γ' = γ') : WeylMove R' γ γ' := by
  intro hγ hγ'
  exact (WeylMove.trans (twE6wm_fixed_to_e1 hR' γ hγ hργ)
    (WeylMove.symm (twE6wm_fixed_to_e1 hR' γ' hγ' hργ')) (twE6wm_isRoot_e 1)) hγ hγ'

private theorem twE6wm_nonfixed_aux {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R') :
    ∀ (n : ℕ) (g : Fin Tag.E6.rank → ℤ), (twE6wmHt g).natAbs = n → IsRoot Tag.E6 g →
      ¬ permLattice TwistTag.E6.perm g = g → WeylMove R' g (ev6 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hn hg hfix
    rcases twE6wm_check_nonfixed g (mem_rootFinset.2 hg) hfix with h | ⟨k, hfixk, hlt⟩
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := twE6wm_base_nonfixed
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact WeylMove.refl R' _
      · have h1 := twE6wm_chain hR' [2] (-ev6 0) (isRoot_neg_single Tag.E6 0)
        rw [b1] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [2, 3] (ev6 2) (twE6wm_isRoot_e 2)
        rw [b2] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [2, 3, 2] (-ev6 2) (isRoot_neg_single Tag.E6 2)
        rw [b3] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [1, 3, 1, 2, 3] (ev6 4) (twE6wm_isRoot_e 4)
        rw [b4] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [1, 3, 1, 2, 3, 2] (-ev6 4) (isRoot_neg_single Tag.E6 4)
        rw [b5] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [3, 1, 2, 3, 1, 2, 3] (ev6 5) (twE6wm_isRoot_e 5)
        rw [b6] at h1
        exact h1
      · have h1 := twE6wm_chain hR' [2, 3, 1, 2, 3, 1, 2, 3] (-ev6 5) (isRoot_neg_single Tag.E6 5)
        rw [b7] at h1
        exact h1
    · have hv : IsRoot Tag.E6 (twE6wmMv k g) := twE6wm_mv_root k hg
      have hlt' : (twE6wmHt (twE6wmMv k g)).natAbs < n := by
        rw [← hn]
        exact hlt
      have ih' := ih (twE6wmHt (twE6wmMv k g)).natAbs hlt' (twE6wmMv k g) rfl hv hfixk
      exact WeylMove.trans (twE6wm_move_root hR' k g) ih' hv

private theorem twE6wm_nonfixed_to_e0 {R' : Subgroup ↥(adjointGroup Tag.E6 K)}
    (hR' : TwGens σ η R') (g : Fin Tag.E6.rank → ℤ) (hg : IsRoot Tag.E6 g)
    (hfix : ¬ permLattice TwistTag.E6.perm g = g) : WeylMove R' g (ev6 0) :=
  twE6wm_nonfixed_aux hR' _ g rfl hg hfix

theorem twE6_weylMove_nonfixed {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    {β β' : Fin Tag.E6.rank → ℤ} (hρβ : permLattice TwistTag.E6.perm β ≠ β)
    (hρβ' : permLattice TwistTag.E6.perm β' ≠ β') : WeylMove R' β β' := by
  intro hβ hβ'
  exact (WeylMove.trans (twE6wm_nonfixed_to_e0 hR' β hβ hρβ)
    (WeylMove.symm (twE6wm_nonfixed_to_e0 hR' β' hβ' hρβ')) (twE6wm_isRoot_e 0)) hβ hβ'

private theorem fourMonomial_core {V : Type*} [AddCommGroup V] [Module K V]
    (hex : ∃ u : K, η u = u ∧ σ u ≠ u)
    (W : Submodule K V) (w₀ w₁ w₂ w₃ : V)
    (h : ∀ u : K, η u = u → w₀ + u • w₁ + σ u • w₂ + (u * σ u) • w₃ ∈ W) :
    w₀ ∈ W ∧ w₁ ∈ W ∧ w₂ ∈ W ∧ w₃ ∈ W := by
  obtain ⟨u, hu, hσu⟩ := hex
  have hσ0 : σ 0 = 0 := map_zero σ
  have hσ1 : σ 1 = 1 := map_one σ
  have hu0 : u ≠ 0 := fun h0 => hσu (by rw [h0, hσ0])
  have hu1 : u ≠ 1 := fun h1 => hσu (by rw [h1, hσ1])
  have hσu0 : σ u ≠ 0 := fun h0 => hu0 (σ.injective (by rw [h0, hσ0]))
  have hA : u ≠ σ u := fun h' => hσu h'.symm
  have hA' : σ u ≠ u := hσu
  have hB : u * σ u ≠ u := by
    intro h'
    have h2 : σ u = 1 := mul_left_cancel₀ hu0 (h'.trans (mul_one u).symm)
    exact hu1 (σ.injective (h2.trans hσ1.symm))
  have hB' : u ≠ u * σ u := fun h' => hB h'.symm
  have hC : σ u ≠ u * σ u := by
    intro h'
    have h2 : σ u * u = σ u * 1 := by rw [mul_one, mul_comm, ← h']
    exact hu1 (mul_left_cancel₀ hσu0 h2)
  have hC' : u * σ u ≠ σ u := fun h' => hC h'.symm
  have hu' : u ∈ fixSubfield η := (mem_fixSubfield η).2 hu
  let x : ↥(fixSubfield η) := ⟨u, hu'⟩
  let ι : ↥(fixSubfield η) →* K := (fixSubfield η).subtype.toMonoidHom
  let s : ↥(fixSubfield η) →* K := (σ.toRingHom.comp (fixSubfield η).subtype).toMonoidHom
  let c : Fin 4 → (↥(fixSubfield η) →* K) := ![1, ι, s, ι * s]
  have hcy : ∀ (i : Fin 4) (y : ↥(fixSubfield η)),
      (c i) y = ![(1 : K), (y : K), σ (y : K), (y : K) * σ (y : K)] i := by
    intro i y
    fin_cases i <;> rfl
  have hc0 : ∀ i : Fin 4, (c i) 0 = ![(1 : K), 0, 0, 0] i := by
    intro i
    rw [hcy]
    fin_cases i <;> simp [hσ0]
  have hc : Function.Injective c := by
    intro i j hij
    have h0 : (c i) 0 = (c j) 0 := by rw [hij]
    have hx : (c i) x = (c j) x := by rw [hij]
    rw [hc0, hc0] at h0
    rw [hcy, hcy] at hx
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd h0 one_ne_zero
      | exact absurd h0 one_ne_zero.symm
      | exact absurd hx hA
      | exact absurd hx hA'
      | exact absurd hx hB
      | exact absurd hx hB'
      | exact absurd hx hC
      | exact absurd hx hC'
  have hli : LinearIndependent K (fun i : Fin 4 => (c i : ↥(fixSubfield η) → K)) :=
    (linearIndependent_monoidHom (↥(fixSubfield η)) K).comp c hc
  have hsepK : ∀ a₀ a₁ a₂ a₃ : K, (∀ y : K, η y = y → a₀ + y * a₁ + σ y * a₂ + (y * σ y) * a₃ = 0) →
      a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
    intro a₀ a₁ a₂ a₃ ha
    have hsum : ∑ i : Fin 4, (![a₀, a₁, a₂, a₃] : Fin 4 → K) i • (c i : ↥(fixSubfield η) → K) = 0 := by
      funext y
      have hy : η (y : K) = (y : K) := (mem_fixSubfield η).1 y.2
      have h1 := ha (y : K) hy
      simp [Finset.sum_apply, Fin.sum_univ_four, hcy]
      linear_combination h1
    have h := Fintype.linearIndependent_iff.1 hli _ hsum
    exact ⟨h 0, h 1, h 2, h 3⟩
  have hall : ∀ φ : Module.Dual K V, (∀ z ∈ W, φ z = 0) →
      φ w₀ = 0 ∧ φ w₁ = 0 ∧ φ w₂ = 0 ∧ φ w₃ = 0 := by
    intro φ hφ
    refine hsepK _ _ _ _ (fun y hy => ?_)
    have h1 := hφ _ (h y hy)
    simpa [map_add, map_smul, smul_eq_mul, mul_assoc] using h1
  have hmem : ∀ z : V, (∀ φ : Module.Dual K V, (∀ z' ∈ W, φ z' = 0) → φ z = 0) → z ∈ W := by
    intro z hz
    by_contra hnot
    obtain ⟨φ, hφz, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    apply hφz
    apply hz φ
    intro z' hz'
    have hmap : φ z' ∈ W.map φ := Submodule.mem_map_of_mem hz'
    rw [hφW, Submodule.mem_bot] at hmap
    exact hmap
  exact ⟨hmem w₀ (fun φ hφ => (hall φ hφ).1), hmem w₁ (fun φ hφ => (hall φ hφ).2.1),
    hmem w₂ (fun φ hφ => (hall φ hφ).2.2.1), hmem w₃ (fun φ hφ => (hall φ hφ).2.2.2)⟩

theorem fourMonomial_mem (hS : TwE6Setup K σ η p) {V : Type*} [AddCommGroup V] [Module K V]
    (W : Submodule K V) (w₀ w₁ w₂ w₃ : V)
    (h : ∀ u : K, η u = u → w₀ + u • w₁ + σ u • w₂ + (u * σ u) • w₃ ∈ W) :
    w₀ ∈ W ∧ w₁ ∈ W ∧ w₂ ∈ W ∧ w₃ ∈ W :=
  fourMonomial_core hS.exists_fixEta_not_fixSigma W w₀ w₁ w₂ w₃ h

private theorem alperinFactA :
    ∀ γ ∈ rootFinset Tag.E6, permLattice (τ := Tag.E6) TwistTag.E6.perm γ = γ →
      ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)),
        γ ≠ (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ∧ γ ≠ -(Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ∧
          γ ≠ (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ∧
          γ ≠ -(Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

private theorem alperinFactB :
    ∀ γ ∈ rootFinset Tag.E6, permLattice (τ := Tag.E6) TwistTag.E6.perm γ = γ →
      ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)),
        γ - (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ≠ (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ∧
          γ - (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ≠ (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

private theorem alperinFactC :
    ∀ γ ∈ rootFinset Tag.E6, permLattice (τ := Tag.E6) TwistTag.E6.perm γ = γ →
      ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)),
        (γ - (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset Tag.E6 →
          γ - (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ≠ (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ∧
          γ - (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ≠ -(Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ∧
          γ - (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) - (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ≠
            (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ)) := by
  decide +kernel

private theorem alperinFactD :
    ∀ γ ∈ rootFinset Tag.E6, permLattice (τ := Tag.E6) TwistTag.E6.perm γ = γ →
      ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)),
        (γ - (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6 →
          γ - (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) - (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ∉
            rootFinset Tag.E6) := by
  decide +kernel

private theorem alperinFactE :
    ∀ γ ∈ rootFinset Tag.E6, permLattice (τ := Tag.E6) TwistTag.E6.perm γ = γ →
      ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)),
        (γ + (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset Tag.E6 →
          γ + (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ≠ (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) ∧
          γ + (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ≠ -(Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ)) := by
  decide +kernel

private theorem alperinFactF :
    ∀ γ ∈ rootFinset Tag.E6, permLattice (τ := Tag.E6) TwistTag.E6.perm γ = γ →
      ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)),
        (γ + (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6 →
          γ + (Pi.single ij.1 1 : Fin Tag.E6.rank → ℤ) + (Pi.single ij.2 1 : Fin Tag.E6.rank → ℤ) ∉
            rootFinset Tag.E6) := by
  decide +kernel

private theorem alperinE6_string :
    ∀ i : Fin Tag.E6.rank, ∀ β ∈ rootFinset Tag.E6,
      β ≠ (Pi.single i 1 : Fin Tag.E6.rank → ℤ) → β ≠ -(Pi.single i 1 : Fin Tag.E6.rank → ℤ) →
        β + (Pi.single i 1 : Fin Tag.E6.rank → ℤ) + (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∉
            rootFinset Tag.E6 ∧
          (β + (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset Tag.E6 →
            β - (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6) := by
  decide +kernel

private theorem alperinEndHomXE6 (i : Fin Tag.E6.rank) (c : K) :
    endHom K (xE6 (Pi.single i 1) c) = xOp Tag.E6 K i c := by
  show endHom K (xPar (rootOperatorFamily Tag.E6) (Pi.single i 1) c) = _
  rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.E6).elt_simple]

private theorem alperinRootVec_zero {β : Fin Tag.E6.rank → ℤ} (hβ : ¬ IsRoot Tag.E6 β) :
    rootVec Tag.E6 K β = 0 := by
  simp [rootVec, hβ]

private theorem alperinXOp_rootVec_E6 (i : Fin Tag.E6.rank) (c : K) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (h1 : β ≠ Pi.single i 1) (h2 : β ≠ -Pi.single i 1) :
    xOp Tag.E6 K i c (rootVec Tag.E6 K β) =
      rootVec Tag.E6 K β + c • rootVec Tag.E6 K (β + Pi.single i 1) := by
  obtain ⟨hI, hII⟩ := alperinE6_string i β (mem_rootFinset.2 hβ) h1 h2
  obtain ⟨-, hchar⟩ := isRoot_add_smul_single_iff hβ i h1 h2
  have hI2 : ¬ IsRoot Tag.E6 (β + (2:ℤ) • Pi.single i 1) := by
    have e2 : β + (2:ℤ) • Pi.single i 1 = β + Pi.single i 1 + Pi.single i 1 := by abel
    rw [e2]
    exact fun h => hI (mem_rootFinset.2 h)
  have hsu : stringUp Tag.E6 i β ≤ 1 := by
    by_contra hlt
    apply hI2
    rw [hchar 2]
    exact ⟨by omega, by omega⟩
  have hP : IsRoot Tag.E6 (β + Pi.single i 1) ↔ 1 ≤ (stringUp Tag.E6 i β : ℤ) := by
    have h := hchar 1
    rw [show β + (1:ℤ) • Pi.single i 1 = β + Pi.single i 1 by abel] at h
    constructor
    · intro hp
      exact (h.1 hp).2
    · intro h1le
      exact h.2 ⟨by omega, h1le⟩
  have hsd : stringUp Tag.E6 i β = 1 → stringDown Tag.E6 i β = 0 := by
    intro hs
    have hp : IsRoot Tag.E6 (β + Pi.single i 1) := hP.2 (by omega)
    by_contra hne
    have hm : IsRoot Tag.E6 (β + (-1:ℤ) • Pi.single i 1) := by
      rw [hchar (-1)]
      exact ⟨by omega, by omega⟩
    have hm' : β - Pi.single i 1 ∈ rootFinset Tag.E6 := by
      rw [mem_rootFinset, show β - Pi.single i 1 = β + (-1:ℤ) • Pi.single i 1 by abel]
      exact hm
    exact hII (mem_rootFinset.2 hp) hm'
  rw [xOp_apply_rootVec_of_ne i c hβ h1 h2]
  rcases (show stringUp Tag.E6 i β = 0 ∨ stringUp Tag.E6 i β = 1 by omega) with hs | hs
  · have hn : ¬ IsRoot Tag.E6 (β + Pi.single i 1) := by
      intro hp
      have h1le := hP.1 hp
      omega
    rw [hs, zero_add, Finset.sum_range_one, alperinRootVec_zero (K := K) hn]
    simp
  · rw [hs, Finset.sum_range_succ, Finset.sum_range_one, hsd hs]
    simp

theorem twE6_orbit_col (σ : K ≃+* K) {i j : Fin 6}
    (hij : (i, j) ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6))) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hργ : permLattice TwistTag.E6.perm γ = γ) (u : K) :
    endHom K (xE6 (Pi.single i 1) u * xE6 (Pi.single j 1) (σ u)) (rootVec Tag.E6 K γ) =
      rootVec Tag.E6 K γ + u • rootVec Tag.E6 K (γ + (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) +
        σ u • rootVec Tag.E6 K (γ + (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) +
          (u * σ u) • rootVec Tag.E6 K (γ + (Pi.single i 1 : Fin Tag.E6.rank → ℤ) + (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := alperinFactA γ (mem_rootFinset.2 hγ) hργ (i, j) hij
  have hE := alperinFactE γ (mem_rootFinset.2 hγ) hργ (i, j) hij
  have hF := alperinFactF γ (mem_rootFinset.2 hγ) hργ (i, j) hij
  rw [map_mul, Module.End.mul_apply, alperinEndHomXE6 j (σ u), alperinEndHomXE6 i u,
    alperinXOp_rootVec_E6 j (σ u) hγ hA3 hA4, map_add, map_smul,
    alperinXOp_rootVec_E6 i u hγ hA1 hA2]
  by_cases hj : IsRoot Tag.E6 (γ + (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
  · obtain ⟨hE1, hE2⟩ := hE (mem_rootFinset.2 hj)
    rw [alperinXOp_rootVec_E6 i u hj hE1 hE2,
      add_right_comm γ (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (Pi.single i 1 : Fin Tag.E6.rank → ℤ)]
    module
  · have hk : ¬ IsRoot Tag.E6 (γ + (Pi.single i 1 : Fin Tag.E6.rank → ℤ) +
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
      intro h
      exact hF (fun h' => hj (mem_rootFinset.1 h')) (mem_rootFinset.2 h)
    rw [alperinRootVec_zero (K := K) hj, alperinRootVec_zero (K := K) hk, map_zero]
    simp

open _root_.Classical in
private theorem alperinCoordOr_of_isRoot {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (z : RootModule Tag.E6 K) : coordOr z γ = z (rootLabel hγ) := by
  unfold coordOr
  rw [dif_pos hγ]

open _root_.Classical in
private theorem alperinCoordOr_of_not {δ : Fin Tag.E6.rank → ℤ} (hδ : ¬ IsRoot Tag.E6 δ)
    (z : RootModule Tag.E6 K) : coordOr z δ = 0 := by
  unfold coordOr
  rw [dif_neg hδ]

private theorem alperinCoordOr_add (f g : RootModule Tag.E6 K) (δ : Fin Tag.E6.rank → ℤ) :
    coordOr (f + g) δ = coordOr f δ + coordOr g δ := by
  unfold coordOr
  split_ifs <;> simp

private theorem alperinCoordOr_zero (δ : Fin Tag.E6.rank → ℤ) :
    coordOr (0 : RootModule Tag.E6 K) δ = 0 := by
  unfold coordOr
  split_ifs <;> simp

private theorem alperinCoordOr_smul (a : K) (f : RootModule Tag.E6 K) (δ : Fin Tag.E6.rank → ℤ) :
    coordOr (a • f) δ = a * coordOr f δ := by
  unfold coordOr
  split_ifs <;> simp

open _root_.Classical in
private theorem alperinCoordOr_hVec (j : Fin Tag.E6.rank) (δ : Fin Tag.E6.rank → ℤ) :
    coordOr (CFSG.Blueprint.Chevalley.hVec Tag.E6 K j) δ = 0 := by
  have hv : (CFSG.Blueprint.Chevalley.hVec Tag.E6 K j : RootModule Tag.E6 K) =
      Finsupp.single (Sum.inl j) 1 := rfl
  rw [hv]
  unfold coordOr
  split_ifs <;> simp [Finsupp.single_apply, rootLabel]

open scoped _root_.Classical in
private theorem alperinCoordOr_rootVec (β δ : Fin Tag.E6.rank → ℤ) :
    coordOr (rootVec Tag.E6 K β) δ =
      @ite K (β = δ ∧ IsRoot Tag.E6 β) (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hβ : IsRoot Tag.E6 β
  · rw [CFSG.Blueprint.Chevalley.rootVec_eq_basisVec_of_isRoot (R := K) hβ]
    by_cases hδ : IsRoot Tag.E6 δ
    · rw [alperinCoordOr_of_isRoot hδ]
      simp [Finsupp.single_apply, rootLabel, hβ]
    · rw [alperinCoordOr_of_not hδ]
      have hne : β ≠ δ := fun h => hδ (h ▸ hβ)
      simp [hne]
  · rw [alperinRootVec_zero (K := K) hβ, alperinCoordOr_zero]
    simp [hβ]

open _root_.Classical in
private theorem alperinCoordOr_xOp (i : Fin Tag.E6.rank) (c : K) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (h1 : γ ≠ Pi.single i 1) (h2 : γ ≠ -Pi.single i 1)
    (h3 : γ - Pi.single i 1 ≠ Pi.single i 1) (z : RootModule Tag.E6 K) :
    coordOr (xOp Tag.E6 K i c z) γ = coordOr z γ + c * coordOr z (γ - Pi.single i 1) := by
  have h1' : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ≠ γ := fun h => h1 h.symm
  have h2' : -(Pi.single i 1 : Fin Tag.E6.rank → ℤ) ≠ γ := fun h => h2 h.symm
  have h3' : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ≠ γ - Pi.single i 1 := fun h => h3 h.symm
  have hne : -(Pi.single i 1 : Fin Tag.E6.rank → ℤ) ≠ γ - Pi.single i 1 :=
    fun h => hγ.ne_zero (sub_eq_neg_self.mp h.symm)
  induction z using Finsupp.induction_linear
  · simp [alperinCoordOr_zero]
  · next f g hf hg =>
      simp only [map_add, alperinCoordOr_add, hf, hg]
      ring
  · next ℓ a =>
      rw [← Finsupp.smul_single_one, map_smul]
      simp only [alperinCoordOr_smul]
      rcases ℓ with j | ⟨β, hβ⟩
      · have hv : (Finsupp.single (Sum.inl j) (1 : K) : RootModule Tag.E6 K) =
            CFSG.Blueprint.Chevalley.hVec Tag.E6 K j := rfl
        rw [hv, CFSG.Blueprint.Chevalley.xOp_apply_hVec]
        simp [alperinCoordOr_add, alperinCoordOr_smul, alperinCoordOr_hVec,
          alperinCoordOr_rootVec, h1']
      · have hv : (Finsupp.single (Sum.inr ⟨β, hβ⟩) (1 : K) : RootModule Tag.E6 K) =
            rootVec Tag.E6 K β :=
          (CFSG.Blueprint.Chevalley.rootVec_eq_basisVec_of_isRoot hβ).symm
        rw [hv]
        by_cases hi : β = Pi.single i 1
        · subst hi
          rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_single]
          simp [alperinCoordOr_add, alperinCoordOr_smul, alperinCoordOr_hVec,
            alperinCoordOr_rootVec, h1', h3']
        · by_cases hi' : β = -Pi.single i 1
          · subst hi'
            rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single]
            simp [alperinCoordOr_smul, alperinCoordOr_add, alperinCoordOr_hVec,
              alperinCoordOr_rootVec, h1', h2', hne]
          · rw [alperinXOp_rootVec_E6 i c hβ hi hi']
            have key : (β + Pi.single i 1 = γ ∧ IsRoot Tag.E6 (β + Pi.single i 1)) ↔
                (β = γ - Pi.single i 1 ∧ IsRoot Tag.E6 β) := by
              constructor
              · rintro ⟨h, -⟩
                exact ⟨eq_sub_of_add_eq h, hβ⟩
              · rintro ⟨h, -⟩
                have h' : β + Pi.single i 1 = γ := by rw [h, sub_add_cancel]
                exact ⟨h', by rw [h']; exact hγ⟩
            simp only [alperinCoordOr_add, alperinCoordOr_smul, alperinCoordOr_rootVec]
            by_cases hR : β = γ - Pi.single i 1 ∧ IsRoot Tag.E6 β
            · rw [if_pos hR, if_pos (key.mpr hR)]
              ring
            · rw [if_neg hR, if_neg (fun hq => hR (key.mp hq))]
              ring

theorem twE6_orbit_row (σ : K ≃+* K) {i j : Fin 6}
    (hij : (i, j) ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6))) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hργ : permLattice TwistTag.E6.perm γ = γ) (z : RootModule Tag.E6 K)
    (u : K) :
    (endHom K (xE6 (Pi.single i 1) u * xE6 (Pi.single j 1) (σ u)) z) (rootLabel hγ) =
      coordOr z γ + u * coordOr z (γ - (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) + σ u * coordOr z (γ - (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) +
        (u * σ u) * coordOr z (γ - (Pi.single i 1 : Fin Tag.E6.rank → ℤ) - (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := alperinFactA γ (mem_rootFinset.2 hγ) hργ (i, j) hij
  obtain ⟨hB1, hB2⟩ := alperinFactB γ (mem_rootFinset.2 hγ) hργ (i, j) hij
  have hC := alperinFactC γ (mem_rootFinset.2 hγ) hργ (i, j) hij
  have hD := alperinFactD γ (mem_rootFinset.2 hγ) hργ (i, j) hij
  rw [← alperinCoordOr_of_isRoot (K := K) hγ, map_mul, Module.End.mul_apply, alperinEndHomXE6 i u,
    alperinEndHomXE6 j (σ u), alperinCoordOr_xOp i u hγ hA1 hA2 hB1,
    alperinCoordOr_xOp j (σ u) hγ hA3 hA4 hB2]
  by_cases hδ : IsRoot Tag.E6 (γ - (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
  · obtain ⟨hC1, hC2, hC3⟩ := hC (mem_rootFinset.2 hδ)
    rw [alperinCoordOr_xOp j (σ u) hδ hC1 hC2 hC3 z]
    ring
  · have hD' : ¬ IsRoot Tag.E6
        (γ - (Pi.single i 1 : Fin Tag.E6.rank → ℤ) - (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
      fun h => hD (fun h' => hδ (mem_rootFinset.1 h')) (mem_rootFinset.2 h)
    simp only [alperinCoordOr_of_not (K := K) hδ, alperinCoordOr_of_not (K := K) hD']
    ring

theorem twE6_rootVec_mem_span (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    rootVec Tag.E6 K β ∈ Submodule.span K {x | ∃ r ∈ R', x = endHom K r (rootVec Tag.E6 K θ)} := by
  set S := Submodule.span K {x | ∃ r ∈ R', x = endHom K r (rootVec Tag.E6 K θ)} with hSdef
  have hRinv : ∀ r ∈ R', ∀ v ∈ S, endHom K r v ∈ S := by
    intro r hr v hv
    refine Submodule.span_induction (p := fun v _ => endHom K r v ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', R'.mul_mem hr hr', by rw [map_mul, Module.End.mul_apply]⟩
    · simp
    · intro x y _ _ hx hy
      simp only [map_add]
      exact S.add_mem hx hy
    · intro a x _ hx
      simp only [map_smul]
      exact S.smul_mem a hx
  have transfer : ∀ {γ δ : Fin Tag.E6.rank → ℤ}, WeylMove R' γ δ → IsRoot Tag.E6 γ →
      IsRoot Tag.E6 δ → rootVec Tag.E6 K γ ∈ S → rootVec Tag.E6 K δ ∈ S := by
    intro γ δ hw hγ hδ hγS
    obtain ⟨r, hr, ε, hε, hv, -⟩ := WeylMove.exists hw hγ hδ
    have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rcases hε with rfl | rfl <;> simp
    have e : rootVec Tag.E6 K δ = ((ε : ℤ) : K) • endHom K r (rootVec Tag.E6 K γ) := by
      rw [hv, smul_smul, hεε, one_smul]
    rw [e]
    exact S.smul_mem _ (hRinv r hr _ hγS)
  have hθS : rootVec Tag.E6 K θ ∈ S := Submodule.subset_span ⟨1, R'.one_mem, by simp⟩
  have hfix1 : ∀ γ, IsRoot Tag.E6 γ → permLattice TwistTag.E6.perm γ = γ →
      rootVec Tag.E6 K γ ∈ S :=
    fun γ hγ hfix =>
      transfer (twE6_weylMove_fixed hR' (isMaxHeightRoot_perm_fixed hθ) hfix) hθ.1 hγ hθS
  obtain ⟨γ₀, hγ₀def⟩ : ∃ γ₀ : Fin Tag.E6.rank → ℤ,
      γ₀ = (id ![0, 1, 1, 1, 1, 0] : Fin Tag.E6.rank → ℤ) := ⟨_, rfl⟩
  have hγ₀ : IsRoot Tag.E6 γ₀ := mem_rootFinset.1 (by rw [hγ₀def]; decide +kernel)
  have hγ₀fix : permLattice (τ := Tag.E6) TwistTag.E6.perm γ₀ = γ₀ := by
    rw [hγ₀def]; decide +kernel
  have hγ₀S : rootVec Tag.E6 K γ₀ ∈ S := hfix1 γ₀ hγ₀ hγ₀fix
  have hβ₁ : IsRoot Tag.E6 (γ₀ + (Pi.single (0 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) :=
    mem_rootFinset.1 (by rw [hγ₀def]; decide +kernel)
  have hβ₁nf : permLattice (τ := Tag.E6) TwistTag.E6.perm
      (γ₀ + (Pi.single (0 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) ≠
      γ₀ + (Pi.single (0 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) := by
    rw [hγ₀def]; decide +kernel
  have hW' : ∀ u : K, η u = u →
      rootVec Tag.E6 K γ₀ + u • rootVec Tag.E6 K (γ₀ + (Pi.single (0 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) +
        σ u • rootVec Tag.E6 K (γ₀ + (Pi.single (5 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) +
          (u * σ u) • rootVec Tag.E6 K (γ₀ + (Pi.single (0 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) +
            (Pi.single (5 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) ∈ S := by
    intro u hu
    have hm : endHom K (xE6 (Pi.single (0 : Fin 6) 1) u * xE6 (Pi.single (5 : Fin 6) 1) (σ u))
        (rootVec Tag.E6 K γ₀) ∈ S :=
      hRinv _ (hR'.orbX (0, 5) (by decide) u hu) _ hγ₀S
    rw [twE6_orbit_col (i := (0 : Fin 6)) (j := (5 : Fin 6)) σ (by decide) hγ₀ hγ₀fix u] at hm
    exact hm
  have hβ₁S : rootVec Tag.E6 K (γ₀ + (Pi.single (0 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) ∈ S :=
    (fourMonomial_mem hS S _ _ _ _ hW').2.1
  by_cases hfix : permLattice (τ := Tag.E6) TwistTag.E6.perm β = β
  · exact hfix1 β hβ hfix
  · exact transfer (twE6_weylMove_nonfixed hR' hβ₁nf hfix) hβ₁ hβ hβ₁S

private theorem twE6Root_endHom_xE6 (i : Fin Tag.E6.rank) (c : K) :
    endHom K (xE6 (Pi.single i 1) c) = xOp Tag.E6 K i c := by
  show endHom K (xPar (rootOperatorFamily Tag.E6) (Pi.single i 1) c) = _
  rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.E6).elt_simple]

private theorem twE6Root_xOp_fix {a : Fin Tag.E6.rank} {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (h1 : β ≠ Pi.single a 1) (h2 : β ≠ -Pi.single a 1)
    (hn : ¬ IsRoot Tag.E6 (β + Pi.single a 1)) (c : K) :
    xOp Tag.E6 K a c (rootVec Tag.E6 K β) = rootVec Tag.E6 K β := by
  have hs : CFSG.Blueprint.Chevalley.stringUp Tag.E6 a β = 0 := by
    have h := (CFSG.Blueprint.Chevalley.isRoot_add_smul_single_iff hβ a h1 h2).2 1
    simp only [one_smul] at h
    have hle : ¬ (1 : ℤ) ≤ (CFSG.Blueprint.Chevalley.stringUp Tag.E6 a β : ℤ) :=
      fun hh => hn (h.2 ⟨by omega, hh⟩)
    omega
  rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_of_ne a c hβ h1 h2, hs]
  simp

private theorem twE6Root_hVec_fix (a j : Fin Tag.E6.rank) (hc : Tag.E6.cartan j a = 0) (c : K) :
    xOp Tag.E6 K a c (hVec Tag.E6 K j) = hVec Tag.E6 K j := by
  rw [CFSG.Blueprint.Chevalley.xOp_apply_hVec, hc]
  simp

private theorem twE6Root_act_fixed (j : Fin Tag.E6.rank) :
    endHom K (xE6 (Pi.single j 1) 1) (rootVec Tag.E6 K (-Pi.single j 1)) =
      rootVec Tag.E6 K (-Pi.single j 1) + hVec Tag.E6 K j + rootVec Tag.E6 K (Pi.single j 1) := by
  rw [twE6Root_endHom_xE6, CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single]
  simp only [one_smul, one_pow]

private theorem twE6Root_act_inner (a b : Fin Tag.E6.rank) (d : K) (hd : d = 1)
    (n1 : (-Pi.single b 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single a 1)
    (n2 : (-Pi.single b 1 : Fin Tag.E6.rank → ℤ) ≠ -Pi.single a 1)
    (n3 : ¬ IsRoot Tag.E6 (-Pi.single b 1 + Pi.single a 1))
    (n4 : (Pi.single b 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single a 1)
    (n5 : (Pi.single b 1 : Fin Tag.E6.rank → ℤ) ≠ -Pi.single a 1)
    (n6 : ¬ IsRoot Tag.E6 (Pi.single b 1 + Pi.single a 1))
    (hc : Tag.E6.cartan b a = 0) :
    endHom K (xE6 (Pi.single a 1) 1 * xE6 (Pi.single b 1) d) (rootVec Tag.E6 K (-Pi.single b 1)) =
      rootVec Tag.E6 K (-Pi.single b 1) + hVec Tag.E6 K b + rootVec Tag.E6 K (Pi.single b 1) := by
  subst hd
  rw [map_mul, Module.End.mul_apply, twE6Root_endHom_xE6, twE6Root_endHom_xE6,
    CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single]
  simp only [one_smul, one_pow, map_add]
  rw [twE6Root_xOp_fix (isRoot_neg_single Tag.E6 b) n1 n2 n3 1, twE6Root_hVec_fix a b hc 1,
    twE6Root_xOp_fix (isRoot_single Tag.E6 b) n4 n5 n6 1]

private theorem twE6Root_act_outer (a b : Fin Tag.E6.rank) (d : K) (hd : d = 1)
    (n1 : (-Pi.single a 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single b 1)
    (n2 : (-Pi.single a 1 : Fin Tag.E6.rank → ℤ) ≠ -Pi.single b 1)
    (n3 : ¬ IsRoot Tag.E6 (-Pi.single a 1 + Pi.single b 1)) :
    endHom K (xE6 (Pi.single a 1) 1 * xE6 (Pi.single b 1) d) (rootVec Tag.E6 K (-Pi.single a 1)) =
      rootVec Tag.E6 K (-Pi.single a 1) + hVec Tag.E6 K a + rootVec Tag.E6 K (Pi.single a 1) := by
  subst hd
  rw [map_mul, Module.End.mul_apply, twE6Root_endHom_xE6, twE6Root_endHom_xE6,
    twE6Root_xOp_fix (isRoot_neg_single Tag.E6 a) n1 n2 n3 1,
    CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single]
  simp only [one_smul, one_pow]

private theorem twE6Root_hVec_of_act {W : Submodule K (RootModule Tag.E6 K)} {j : Fin Tag.E6.rank}
    (r : ↥(adjointGroup Tag.E6 K)) (hrW : ∀ v ∈ W, endHom K r v ∈ W)
    (hroots : ∀ β, IsRoot Tag.E6 β → rootVec Tag.E6 K β ∈ W)
    (hact : endHom K r (rootVec Tag.E6 K (-Pi.single j 1)) =
      rootVec Tag.E6 K (-Pi.single j 1) + hVec Tag.E6 K j + rootVec Tag.E6 K (Pi.single j 1)) :
    hVec Tag.E6 K j ∈ W := by
  have hneg : rootVec Tag.E6 K (-Pi.single j 1) ∈ W := hroots _ (isRoot_neg_single Tag.E6 j)
  have hpos : rootVec Tag.E6 K (Pi.single j 1) ∈ W := hroots _ (isRoot_single Tag.E6 j)
  have h1 : endHom K r (rootVec Tag.E6 K (-Pi.single j 1)) ∈ W := hrW _ hneg
  rw [hact] at h1
  have h2 := W.sub_mem (W.sub_mem h1 hneg) hpos
  have e : hVec Tag.E6 K j = rootVec Tag.E6 K (-Pi.single j 1) + hVec Tag.E6 K j +
      rootVec Tag.E6 K (Pi.single j 1) - rootVec Tag.E6 K (-Pi.single j 1) -
        rootVec Tag.E6 K (Pi.single j 1) := by abel
  rw [e]
  exact h2

theorem twE6_hVec_mem_span {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    (W : Submodule K (RootModule Tag.E6 K)) (hW : ∀ r ∈ R', ∀ v ∈ W, endHom K r v ∈ W)
    (hroots : ∀ β, IsRoot Tag.E6 β → rootVec Tag.E6 K β ∈ W) (j : Fin Tag.E6.rank) :
    hVec Tag.E6 K j ∈ W := by
  have hr0 : xE6 (Pi.single (0 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) 1 *
      xE6 (Pi.single (5 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) (σ 1) ∈ R' :=
    hR'.orbX (0, 5) (by decide) 1 (map_one η)
  have hr2 : xE6 (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) 1 *
      xE6 (Pi.single (4 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) (σ 1) ∈ R' :=
    hR'.orbX (2, 4) (by decide) 1 (map_one η)
  have hr1 : xE6 (Pi.single (1 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) 1 ∈ R' :=
    hR'.fixedX 1 (by decide) 1 (map_one σ) (map_one η)
  have hr3 : xE6 (Pi.single (3 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) 1 ∈ R' :=
    hR'.fixedX 3 (by decide) 1 (map_one σ) (map_one η)
  have h0 : hVec Tag.E6 K (0 : Fin 6) ∈ W :=
    twE6Root_hVec_of_act _ (fun v hv => hW _ hr0 v hv) hroots
      (twE6Root_act_outer (0 : Fin 6) (5 : Fin 6) (σ 1) (map_one σ)
        (by decide +kernel) (by decide +kernel)
        (by rw [← mem_rootFinset]; decide +kernel))
  have h1 : hVec Tag.E6 K (1 : Fin 6) ∈ W :=
    twE6Root_hVec_of_act _ (fun v hv => hW _ hr1 v hv) hroots (twE6Root_act_fixed (1 : Fin 6))
  have h2 : hVec Tag.E6 K (2 : Fin 6) ∈ W :=
    twE6Root_hVec_of_act _ (fun v hv => hW _ hr2 v hv) hroots
      (twE6Root_act_outer (2 : Fin 6) (4 : Fin 6) (σ 1) (map_one σ)
        (by decide +kernel) (by decide +kernel)
        (by rw [← mem_rootFinset]; decide +kernel))
  have h3 : hVec Tag.E6 K (3 : Fin 6) ∈ W :=
    twE6Root_hVec_of_act _ (fun v hv => hW _ hr3 v hv) hroots (twE6Root_act_fixed (3 : Fin 6))
  have h4 : hVec Tag.E6 K (4 : Fin 6) ∈ W :=
    twE6Root_hVec_of_act _ (fun v hv => hW _ hr2 v hv) hroots
      (twE6Root_act_inner (2 : Fin 6) (4 : Fin 6) (σ 1) (map_one σ)
        (by decide +kernel) (by decide +kernel)
        (by rw [← mem_rootFinset]; decide +kernel)
        (by decide +kernel) (by decide +kernel)
        (by rw [← mem_rootFinset]; decide +kernel)
        (by decide +kernel))
  have h5 : hVec Tag.E6 K (5 : Fin 6) ∈ W :=
    twE6Root_hVec_of_act _ (fun v hv => hW _ hr0 v hv) hroots
      (twE6Root_act_inner (0 : Fin 6) (5 : Fin 6) (σ 1) (map_one σ)
        (by decide +kernel) (by decide +kernel)
        (by rw [← mem_rootFinset]; decide +kernel)
        (by decide +kernel) (by decide +kernel)
        (by rw [← mem_rootFinset]; decide +kernel)
        (by decide +kernel))
  have key : ∀ k : Fin 6, hVec Tag.E6 K k ∈ W := by
    intro k
    fin_cases k
    exacts [h0, h1, h2, h3, h4, h5]
  exact key j

theorem twE6_span_orbit_eq_top (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R') :
    Submodule.span K {x | ∃ r ∈ R', x = endHom K r (rootVec Tag.E6 K θ)} = ⊤ := by
  classical
  set W := Submodule.span K {x | ∃ r ∈ R', x = endHom K r (rootVec Tag.E6 K θ)} with hW
  have hRinv : ∀ r ∈ R', ∀ v ∈ W, endHom K r v ∈ W := by
    intro r hr v hv
    refine Submodule.span_induction (p := fun v _ => endHom K r v ∈ W) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', R'.mul_mem hr hr', by rw [map_mul]; rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact W.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact W.smul_mem a hx
  have hroots : ∀ β, IsRoot Tag.E6 β → rootVec Tag.E6 K β ∈ W := fun β hβ =>
    twE6_rootVec_mem_span hS hθ hR' hβ
  rw [eq_top_iff, ← (Finsupp.basisSingleOne (R := K) (ι := Label Tag.E6)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  rw [Finsupp.coe_basisSingleOne]
  rcases b with i | ⟨β, hβ⟩
  · exact twE6_hVec_mem_span hR' W hRinv hroots i
  · have := hroots β hβ
    rwa [rootVec_of_isRoot' hβ] at this

private theorem twE6_coordOr_eq_of_isRoot (z : RootModule Tag.E6 K) {δ : Fin Tag.E6.rank → ℤ}
    (h : IsRoot Tag.E6 δ) : coordOr z δ = z (rootLabel h) := by
  unfold coordOr
  rw [dif_pos h]

theorem twE6_vanish_roots (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    (z : RootModule Tag.E6 K) (hz : z ∈ vanishSub R' (negLabel hθ.1)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : z (rootLabel hβ) = 0 := by
  have hZ : ∀ r ∈ R', ∀ w ∈ vanishSub R' (negLabel hθ.1),
      endHom K r w ∈ vanishSub R' (negLabel hθ.1) := by
    intro r hr w hw
    rw [mem_vanishSub] at hw ⊢
    intro r' hr'
    have h := hw (r' * r) (R'.mul_mem hr' hr)
    rwa [map_mul, Module.End.mul_apply] at h
  have hneg : ∀ w ∈ vanishSub R' (negLabel hθ.1), w (negLabel hθ.1) = 0 := by
    intro w hw
    have h := (mem_vanishSub.1 hw) 1 R'.one_mem
    rwa [map_one, Module.End.one_apply] at h
  have transfer : ∀ {b c : Fin Tag.E6.rank → ℤ} (hb : IsRoot Tag.E6 b) (hc : IsRoot Tag.E6 c),
      WeylMove R' b c → (∀ w ∈ vanishSub R' (negLabel hθ.1), w (rootLabel hc) = 0) →
      ∀ w ∈ vanishSub R' (negLabel hθ.1), w (rootLabel hb) = 0 := by
    intro b c hb hc hbc hcP w hw
    obtain ⟨r, hr, ε, hε, -, hεr⟩ := WeylMove.exists hbc hb hc
    have h1 := hcP (endHom K r w) (hZ r hr w hw)
    rw [hεr w] at h1
    rcases hε with rfl | rfl <;> simpa using h1
  have hθ' : IsRoot Tag.E6 (-θ) := isRoot_neg_iff.2 hθ.1
  have hρneg : permLattice TwistTag.E6.perm (-θ) = -θ := by
    have h := isMaxHeightRoot_perm_fixed hθ
    have hneg' : permLattice TwistTag.E6.perm (-θ) = -permLattice TwistTag.E6.perm θ := rfl
    rw [hneg', h]
    rfl
  have hfix : ∀ {b : Fin Tag.E6.rank → ℤ} (hb : IsRoot Tag.E6 b),
      permLattice TwistTag.E6.perm b = b → ∀ w ∈ vanishSub R' (negLabel hθ.1), w (rootLabel hb) = 0 :=
    fun hb hbf => transfer hb hθ' (twE6_weylMove_fixed hR' hbf hρneg) hneg
  obtain ⟨γ0, hγ0e⟩ : ∃ γ0 : Fin Tag.E6.rank → ℤ,
      γ0 = (Pi.single (1 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) + (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) +
        (Pi.single (3 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) + (Pi.single (4 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) :=
    ⟨_, rfl⟩
  have hγ0 : IsRoot Tag.E6 γ0 := by
    rw [hγ0e]; exact mem_rootFinset.1 (by decide +kernel)
  have hργ0 : permLattice (τ := Tag.E6) TwistTag.E6.perm γ0 = γ0 := by
    rw [hγ0e]; decide +kernel
  have hδ0 : IsRoot Tag.E6 (γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) := by
    rw [hγ0e]; exact mem_rootFinset.1 (by decide +kernel)
  have hδ0nf : permLattice (τ := Tag.E6) TwistTag.E6.perm (γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) ≠
      γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) := by
    rw [hγ0e]; decide +kernel
  have hγ0P : ∀ w ∈ vanishSub R' (negLabel hθ.1), w (rootLabel hγ0) = 0 := hfix hγ0 hργ0
  have hδ0P : ∀ w ∈ vanishSub R' (negLabel hθ.1), w (rootLabel hδ0) = 0 := by
    intro w hw
    have hc0 : coordOr w γ0 = 0 := by
      rw [twE6_coordOr_eq_of_isRoot w hγ0]
      exact hγ0P w hw
    have hij : ((2 : Fin 6), (4 : Fin 6)) ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)) := by
      decide
    have hkey : ∀ u : K, η u = u →
        u * coordOr w (γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) +
          σ u * coordOr w (γ0 - (Pi.single (4 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) +
          (u * σ u) * coordOr w (γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) -
            (Pi.single (4 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) = 0 := by
      intro u hu
      have hr : xE6 (Pi.single (2 : Fin 6) 1) u * xE6 (Pi.single (4 : Fin 6) 1) (σ u) ∈ R' :=
        hR'.orbX (2, 4) (by decide) u hu
      have h0 := hγ0P _ (hZ _ hr w hw)
      rw [twE6_orbit_row σ hij hγ0 hργ0 w u, hc0, zero_add] at h0
      exact h0
    have hmem := fourMonomial_mem hS (⊥ : Submodule K K) 0
      (coordOr w (γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)))
      (coordOr w (γ0 - (Pi.single (4 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)))
      (coordOr w (γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ) -
        (Pi.single (4 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)))
      (fun u hu => by simpa [smul_eq_mul] using hkey u hu)
    have hA : coordOr w (γ0 - (Pi.single (2 : Fin 6) 1 : Fin Tag.E6.rank → ℤ)) = 0 := by
      simpa using hmem.2.1
    rw [twE6_coordOr_eq_of_isRoot w hδ0] at hA
    exact hA
  by_cases hβf : permLattice TwistTag.E6.perm β = β
  · exact hfix hβ hβf z hz
  · exact transfer hβ hδ0 (twE6_weylMove_nonfixed hR' hβf hδ0nf) hδ0P z hz

private theorem twE6_rootless_bridge (i : Fin Tag.E6.rank) (c : K) :
    endHom K (xE6 (Pi.single i 1) c) = xOp Tag.E6 K i c := by
  show endHom K (xPar (rootOperatorFamily Tag.E6) (Pi.single i 1) c) = _
  rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.E6).elt_simple]

private theorem twE6_rootless_rootVec_apply {β γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) :
    rootVec Tag.E6 K β (rootLabel hγ) = if β = γ then 1 else 0 := by
  by_cases hβ : IsRoot Tag.E6 β
  · rw [rootVec_eq_basisVec_of_isRoot hβ, Finsupp.single_apply]
    by_cases h : β = γ
    · subst h
      simp [rootLabel]
    · have h' : ¬ ((Sum.inr ⟨β, hβ⟩ : Label Tag.E6) = rootLabel hγ) := fun e => h (by
        simp only [rootLabel, Sum.inr.injEq, Subtype.mk.injEq] at e
        exact e)
      rw [if_neg h', if_neg h]
  · have hne : β ≠ γ := fun e => hβ (by rw [e]; exact hγ)
    have hr : rootVec Tag.E6 K β = 0 := by
      rw [rootVec, dif_neg hβ]
    simp [hr, hne]

private theorem twE6_rootless_decomp (z : RootModule Tag.E6 K)
    (hz : ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0) :
    z = ∑ m, z (Sum.inl m) • hVec Tag.E6 K m := by
  ext l
  rcases l with m | ⟨β, hβ⟩
  · simp [hVec, Finsupp.single_apply]
  · have h : z (Sum.inr ⟨β, hβ⟩) = 0 := hz β hβ
    simp [hVec, Finsupp.single_apply, h]

private theorem twE6_rootless_xOp_hSum (i : Fin Tag.E6.rank) (c : K) (a : Fin Tag.E6.rank → K) :
    xOp Tag.E6 K i c (∑ m, a m • hVec Tag.E6 K m) =
      ∑ m, a m • hVec Tag.E6 K m +
        (c * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * a m) • rootVec Tag.E6 K (Pi.single i 1) := by
  rw [map_sum]
  simp only [map_smul, xOp_apply_hVec, smul_add, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

private theorem twE6_rootless_yOp_hSum (i : Fin Tag.E6.rank) (c : K) (a : Fin Tag.E6.rank → K) :
    yOp Tag.E6 K i c (∑ m, a m • hVec Tag.E6 K m) =
      ∑ m, a m • hVec Tag.E6 K m +
        (c * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * a m) • rootVec Tag.E6 K (-Pi.single i 1) := by
  rw [map_sum]
  simp only [map_smul, yOp_apply_hVec, smul_add, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

private theorem twE6_rootless_xOp_vec (z : RootModule Tag.E6 K)
    (hz : ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0) (i : Fin Tag.E6.rank) (c : K) :
    xOp Tag.E6 K i c z = z + (c * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) •
      rootVec Tag.E6 K (Pi.single i 1) := by
  have h : xOp Tag.E6 K i c (∑ m, z (Sum.inl m) • hVec Tag.E6 K m) =
      ∑ m, z (Sum.inl m) • hVec Tag.E6 K m +
        (c * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) •
          rootVec Tag.E6 K (Pi.single i 1) :=
    twE6_rootless_xOp_hSum i c (fun m => z (Sum.inl m))
  have hd : (∑ m, z (Sum.inl m) • hVec Tag.E6 K m) = z := (twE6_rootless_decomp z hz).symm
  rw [hd] at h
  exact h

private theorem twE6_rootless_yOp_vec (z : RootModule Tag.E6 K)
    (hz : ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0) (i : Fin Tag.E6.rank) (c : K) :
    yOp Tag.E6 K i c z = z + (c * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) •
      rootVec Tag.E6 K (-Pi.single i 1) := by
  have h : yOp Tag.E6 K i c (∑ m, z (Sum.inl m) • hVec Tag.E6 K m) =
      ∑ m, z (Sum.inl m) • hVec Tag.E6 K m +
        (c * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) •
          rootVec Tag.E6 K (-Pi.single i 1) :=
    twE6_rootless_yOp_hSum i c (fun m => z (Sum.inl m))
  have hd : (∑ m, z (Sum.inl m) • hVec Tag.E6 K m) = z := (twE6_rootless_decomp z hz).symm
  rw [hd] at h
  exact h

private theorem twE6_rootless_pair (Z : Submodule K (RootModule Tag.E6 K))
    (hroots : ∀ z ∈ Z, ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0)
    {z : RootModule Tag.E6 K} (hz : z ∈ Z) {i j : Fin Tag.E6.rank}
    (hw : xOp Tag.E6 K i 1 (xOp Tag.E6 K j 1 z) ∈ Z)
    (h1 : Pi.single j 1 ≠ (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
    (h2 : Pi.single j 1 ≠ -(Pi.single i 1 : Fin Tag.E6.rank → ℤ))
    (h3 : Pi.single j 1 + Pi.single i 1 ≠ (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
    (h4 : Pi.single j 1 + Pi.single i 1 ≠ (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :
    (∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) = 0 ∧
      (∑ m, ((Tag.E6.cartan m j).natAbs : K) * z (Sum.inl m)) = 0 := by
  have hrl : ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0 := hroots z hz
  have hxj := twE6_rootless_xOp_vec z hrl j 1
  have hxi := twE6_rootless_xOp_vec z hrl i 1
  have hvj : xOp Tag.E6 K i 1 (rootVec Tag.E6 K (Pi.single j 1)) =
      rootVec Tag.E6 K (Pi.single j 1) +
        (1 : K) • rootVec Tag.E6 K (Pi.single j 1 + Pi.single i 1) :=
    C2E6Std.xOp_rootVec_E6 i 1 (isRoot_single Tag.E6 j) h1 h2
  have hW : xOp Tag.E6 K i 1 (xOp Tag.E6 K j 1 z) - z =
      (∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) • rootVec Tag.E6 K (Pi.single i 1) +
        (∑ m, ((Tag.E6.cartan m j).natAbs : K) * z (Sum.inl m)) • rootVec Tag.E6 K (Pi.single j 1) +
        (∑ m, ((Tag.E6.cartan m j).natAbs : K) * z (Sum.inl m)) •
          rootVec Tag.E6 K (Pi.single j 1 + Pi.single i 1) := by
    rw [hxj, map_add, map_smul, hxi, hvj]
    simp only [one_mul, one_smul, smul_add]
    abel
  have hX : (∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) •
      rootVec Tag.E6 K (Pi.single i 1) +
      (∑ m, ((Tag.E6.cartan m j).natAbs : K) * z (Sum.inl m)) • rootVec Tag.E6 K (Pi.single j 1) +
      (∑ m, ((Tag.E6.cartan m j).natAbs : K) * z (Sum.inl m)) •
        rootVec Tag.E6 K (Pi.single j 1 + Pi.single i 1) ∈ Z := by
    rw [← hW]
    exact Z.sub_mem hw hz
  have e1 := hroots _ hX (Pi.single i 1) (isRoot_single Tag.E6 i)
  have e2 := hroots _ hX (Pi.single j 1) (isRoot_single Tag.E6 j)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    twE6_rootless_rootVec_apply (isRoot_single Tag.E6 i),
    twE6_rootless_rootVec_apply (isRoot_single Tag.E6 j),
    eq_self_iff_true, ↓reduceIte, h1, h1.symm, h3, h4, mul_one, mul_zero, add_zero,
    zero_add] at e1 e2
  exact ⟨e1, e2⟩

private theorem twE6_rootless_fixed (Z : Submodule K (RootModule Tag.E6 K))
    (hroots : ∀ z ∈ Z, ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0)
    {z : RootModule Tag.E6 K} (hz : z ∈ Z) {i : Fin Tag.E6.rank}
    (hw : xOp Tag.E6 K i 1 z ∈ Z) :
    (∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) = 0 := by
  have hrl : ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0 := hroots z hz
  have hxi := twE6_rootless_xOp_vec z hrl i 1
  have hX : (1 * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) •
      rootVec Tag.E6 K (Pi.single i 1) ∈ Z := by
    have hd : xOp Tag.E6 K i 1 z - z =
        (1 * ∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) •
          rootVec Tag.E6 K (Pi.single i 1) := by
      rw [hxi]
      abel
    rw [← hd]
    exact Z.sub_mem hw hz
  have e := hroots _ hX (Pi.single i 1) (isRoot_single Tag.E6 i)
  simp only [Finsupp.smul_apply, smul_eq_mul,
    twE6_rootless_rootVec_apply (isRoot_single Tag.E6 i),
    eq_self_iff_true, ↓reduceIte, mul_one, one_mul] at e
  exact e

theorem twE6_fixed_of_rootless {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R')
    (Z : Submodule K (RootModule Tag.E6 K)) (hstab : ∀ r ∈ R', ∀ z ∈ Z, endHom K r z ∈ Z)
    (hroots : ∀ z ∈ Z, ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0) :
    ∀ z ∈ Z, ∀ y : ↥(adjointGroup Tag.E6 K), endHom K y z = z := by
  intro z hz
  have hrl : ∀ β (hβ : IsRoot Tag.E6 β), z (rootLabel hβ) = 0 := hroots z hz
  have hfixed : ∀ i : Fin Tag.E6.rank, xE6 (Pi.single i 1) 1 ∈ R' →
      (∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) = 0 := by
    intro i hi
    apply twE6_rootless_fixed Z hroots hz
    have h := hstab _ hi z hz
    rwa [twE6_rootless_bridge] at h
  have hL1 := hfixed (1 : Fin 6) (hR'.fixedX 1 (by decide) 1 (map_one σ) (map_one η))
  have hL3 := hfixed (3 : Fin 6) (hR'.fixedX 3 (by decide) 1 (map_one σ) (map_one η))
  have e0 : endHom K (xE6 (Pi.single (0 : Fin 6) 1) 1) = xOp Tag.E6 K (0 : Fin 6) 1 :=
    twE6_rootless_bridge (0 : Fin 6) 1
  have e5 : endHom K (xE6 (Pi.single (5 : Fin 6) 1) 1) = xOp Tag.E6 K (5 : Fin 6) 1 :=
    twE6_rootless_bridge (5 : Fin 6) 1
  have e2 : endHom K (xE6 (Pi.single (2 : Fin 6) 1) 1) = xOp Tag.E6 K (2 : Fin 6) 1 :=
    twE6_rootless_bridge (2 : Fin 6) 1
  have e4 : endHom K (xE6 (Pi.single (4 : Fin 6) 1) 1) = xOp Tag.E6 K (4 : Fin 6) 1 :=
    twE6_rootless_bridge (4 : Fin 6) 1
  have hr05 : xE6 (Pi.single (0 : Fin 6) 1) 1 * xE6 (Pi.single (5 : Fin 6) 1) 1 ∈ R' := by
    have h := hR'.orbX (0, 5) (by decide) 1 (map_one η)
    rwa [map_one σ] at h
  have hw05 : xOp Tag.E6 K (0 : Fin 6) 1 (xOp Tag.E6 K (5 : Fin 6) 1 z) ∈ Z := by
    have h := hstab _ hr05 z hz
    rw [map_mul, e0, e5, Module.End.mul_apply] at h
    exact h
  have hpair05 :=
    twE6_rootless_pair Z hroots hz hw05 (by decide) (by decide) (by decide) (by decide)
  have hr24 : xE6 (Pi.single (2 : Fin 6) 1) 1 * xE6 (Pi.single (4 : Fin 6) 1) 1 ∈ R' := by
    have h := hR'.orbX (2, 4) (by decide) 1 (map_one η)
    rwa [map_one σ] at h
  have hw24 : xOp Tag.E6 K (2 : Fin 6) 1 (xOp Tag.E6 K (4 : Fin 6) 1 z) ∈ Z := by
    have h := hstab _ hr24 z hz
    rw [map_mul, e2, e4, Module.End.mul_apply] at h
    exact h
  have hpair24 :=
    twE6_rootless_pair Z hroots hz hw24 (by decide) (by decide) (by decide) (by decide)
  have hL : ∀ i : Fin 6, (∑ m, ((Tag.E6.cartan m i).natAbs : K) * z (Sum.inl m)) = 0 := by
    intro i
    fin_cases i
    · exact hpair05.1
    · exact hL1
    · exact hpair24.1
    · exact hL3
    · exact hpair24.2
    · exact hpair05.2
  have key : ∀ g ∈ Subgroup.closure {g : ModGL Tag.E6 K | ∃ (i : Fin Tag.E6.rank) (c : K),
      (g : Module.End K (RootModule Tag.E6 K)) = xOp Tag.E6 K i c ∨
        (g : Module.End K (RootModule Tag.E6 K)) = yOp Tag.E6 K i c},
      (g : Module.End K (RootModule Tag.E6 K)) z = z := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, c, h | h⟩ := hx
      · rw [h, twE6_rootless_xOp_vec z hrl i c, hL i, mul_zero, zero_smul, add_zero]
      · rw [h, twE6_rootless_yOp_vec z hrl i c, hL i, mul_zero, zero_smul, add_zero]
    | one => simp
    | mul x y hx hy ihx ihy => rw [Units.val_mul, Module.End.mul_apply, ihy, ihx]
    | inv x hx ih =>
      calc ((x⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) z
          = ((x⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
              (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) z) := by rw [ih]
        _ = ((x⁻¹ * x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) z := by
              rw [Units.val_mul, Module.End.mul_apply]
        _ = z := by simp
  intro y
  exact key (y : ModGL Tag.E6 K) y.2

theorem twE6_vanishSub_fixed (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) {R' : Subgroup ↥(adjointGroup Tag.E6 K)} (hR' : TwGens σ η R') :
    ∀ z ∈ vanishSub R' (negLabel hθ.1), ∀ y : ↥(adjointGroup Tag.E6 K), endHom K y z = z := by
  have hstab : ∀ r ∈ R', ∀ z ∈ vanishSub R' (negLabel hθ.1),
      endHom K r z ∈ vanishSub R' (negLabel hθ.1) := by
    intro r hr z hz
    rw [mem_vanishSub] at hz ⊢
    intro r' hr'
    have := hz (r' * r) (R'.mul_mem hr' hr)
    simpa [map_mul, Module.End.mul_apply] using this
  exact twE6_fixed_of_rootless hR' (vanishSub R' (negLabel hθ.1)) hstab
    (fun z hz β hβ => twE6_vanish_roots hS hθ hR' z hz hβ)

private theorem twE6_E3_pairing : ∀ γ ∈ rootFinset Tag.E6, ∃ i : Fin Tag.E6.rank,
    (∑ j, Tag.E6.cartan i j * γ j) = 1 ∨ (∑ j, Tag.E6.cartan i j * γ j) = -1 ∨
      (∑ j, Tag.E6.cartan i j * γ j) = 2 ∨ (∑ j, Tag.E6.cartan i j * γ j) = -2 := by
  decide +kernel

private theorem twE6_E3_exists_unit (hK : 4 ≤ Nat.card K) :
    ∃ u : K, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ -1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  by_contra h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro u _
    by_cases h0 : u = 0
    · simp [h0]
    by_cases h1 : u = 1
    · simp [h1]
    have h2 : u = -1 := by
      by_contra h2
      exact h ⟨u, h0, h1, h2⟩
    simp [h2]
  have hcard := Finset.card_le_card hsub
  have h3 : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
  omega

private theorem twE6_E3_fixed_zero (hK : 4 ≤ Nat.card K) {z : RootModule Tag.E6 K}
    (hz : ∀ y : ↥(adjointGroup Tag.E6 K), endHom K y z = z) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) : z (rootLabel hγ) = 0 := by
  obtain ⟨i, hi⟩ := twE6_E3_pairing γ (mem_rootFinset.2 hγ)
  obtain ⟨u, hu0, hu1, hu2⟩ := twE6_E3_exists_unit hK
  have hsq : u ^ 2 ≠ 1 := by
    intro h
    have h2 : u * u = 1 := by rw [← pow_two]; exact h
    rcases mul_self_eq_one_iff.1 h2 with h' | h'
    · exact hu1 h'
    · exact hu2 h'
  obtain ⟨t, ht⟩ : ∃ t : Kˣ, (t : K) = u := ⟨Units.mk0 u hu0, rfl⟩
  have hc : ∀ m : ℤ, (m = 1 ∨ m = -1 ∨ m = 2 ∨ m = -2) → ((t ^ m : Kˣ) : K) ≠ 1 := by
    intro m hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [zpow_one, ht]
      exact hu1
    · rw [zpow_neg_one, Units.val_inv_eq_inv_val, ht, ne_eq, inv_eq_one]
      exact hu1
    · rw [zpow_ofNat, Units.val_pow_eq_pow_val, ht]
      exact hsq
    · rw [zpow_neg, zpow_ofNat, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ht, ne_eq,
        inv_eq_one]
      exact hsq
  have hfix : endHom K (CFSG.LieType.Chevalley.torusElement Tag.E6 K i t) z (rootLabel hγ) =
      z (rootLabel hγ) := by
    rw [hz (CFSG.LieType.Chevalley.torusElement Tag.E6 K i t)]
  have e0 : endHom K (CFSG.LieType.Chevalley.torusElement Tag.E6 K i t) =
      (CFSG.Blueprint.Chevalley.torusElt Tag.E6 K i t : Module.End K (RootModule Tag.E6 K)) := rfl
  have hw : CFSG.LieType.Chevalley.labelWt Tag.E6 (rootLabel hγ) = γ := rfl
  rw [e0, CFSG.LieType.Chevalley.torusElt_apply, hw] at hfix
  have hfix' : (((t ^ (∑ j, Tag.E6.cartan i j * γ j) : Kˣ) : K) - 1) * z (rootLabel hγ) = 0 := by
    rw [sub_mul, one_mul, hfix, sub_self]
  rcases mul_eq_zero.1 hfix' with h | h
  · exact absurd (sub_eq_zero.1 h) (hc _ hi)
  · exact h

theorem eq_one_of_sub_mem_fixed (hK : 4 ≤ Nat.card K) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) (Z : Submodule K (RootModule Tag.E6 K))
    (hZ : ∀ z ∈ Z, ∀ y : ↥(adjointGroup Tag.E6 K), endHom K y z = z) (x : ↥(adjointGroup Tag.E6 K))
    (hx : ∀ v : RootModule Tag.E6 K, endHom K x v - v ∈ Z) : x = 1 := by
  classical
  let N : Subgroup ↥(adjointGroup Tag.E6 K) :=
    { carrier := {y | ∀ v : RootModule Tag.E6 K, endHom K y v - v ∈ Z}
      one_mem' := fun v => by simp
      mul_mem' := fun {y₁ y₂} h1 h2 v => by
        have e : endHom K (y₁ * y₂) v - v =
            endHom K y₁ (endHom K y₂ v - v) + (endHom K y₁ v - v) := by
          rw [map_mul, Module.End.mul_apply, map_sub]
          abel
        rw [e, hZ _ (h2 v) y₁]
        exact Z.add_mem (h2 v) (h1 v)
      inv_mem' := fun {y} h v => by
        have e : endHom K y⁻¹ v - v = -(endHom K y (endHom K y⁻¹ v) - endHom K y⁻¹ v) := by
          have : endHom K y (endHom K y⁻¹ v) = v := by
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
          rw [this]
          abel
        rw [e]
        exact Z.neg_mem (h _) }
  have hNn : N.Normal := ⟨fun y hy g v => by
    have e : endHom K (g * y * g⁻¹) v - v =
        endHom K g (endHom K y (endHom K g⁻¹ v) - endHom K g⁻¹ v) := by
      have : endHom K g (endHom K g⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, map_sub, this]
    rw [e, hZ _ (hy (endHom K g⁻¹ v)) g]
    exact hy _⟩
  haveI := isSimpleGroup_adjointGroup_of_type (K := K) (τ := Tag.E6) (Or.inl rfl)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · have hxN : x ∈ N := hx
    rw [h] at hxN
    exact Subgroup.mem_bot.1 hxN
  · exfalso
    have hmem : xPar (rootOperatorFamily Tag.E6) θ (1 : K) ∈ N := by
      rw [h]
      trivial
    have h1 := hmem (rootVec Tag.E6 K (-θ))
    have h2 := twE6_E3_fixed_zero hK (hZ _ h1) hθ.1
    apply xPar_apply_neg_root_coord hθ.1 (K := K)
    have hv : (rootVec Tag.E6 K (-θ)) (rootLabel hθ.1) = 0 := by
      rw [rootVec_of_isRoot' (isRoot_neg_iff.2 hθ.1)]
      have hne : (rootLabel hθ.1 : Label Tag.E6) ≠ negLabel hθ.1 := by
        intro hh
        have hh' : θ = -θ := by simpa using hh
        have := hθ.height_pos
        have h3' := congrArg height hh'
        simp only [height, Pi.neg_apply, Finset.sum_neg_distrib] at h3'
        simp only [height] at this
        omega
      simp [Finsupp.single_apply, hne]
    simpa [hv] using h2

theorem mem_twR_of_entries (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) (g : ↥(twistedE6RootGroup K σ))
    (hall : ∀ r ∈ twR σ η, ∀ r' ∈ twR σ η,
      entry (twIncl σ (r * g * r')) (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield η) :
    g ∈ twR σ η := by
  classical
  set Z := vanishSub (twRP σ η) (negLabel hθ.1) with hZ
  set gP : ↥(adjointGroup Tag.E6 K) := twIncl σ g with hgP
  set g₂ : ↥(adjointGroup Tag.E6 K) := entrywiseAdjointAut Tag.E6 η gP with hg₂
  have hRfix : ∀ r ∈ twR σ η, entrywiseAdjointAut Tag.E6 η (twIncl σ r) = twIncl σ r :=
    fun r hr => (mem_twR_iff σ η r).1 hr
  have hent : ∀ r ∈ twR σ η, ∀ r' ∈ twR σ η,
      entry (twIncl σ r * g₂ * twIncl σ r') (negLabel hθ.1) (rootLabel hθ.1) =
        entry (twIncl σ r * gP * twIncl σ r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r hr r' hr'
    have e : twIncl σ r * g₂ * twIncl σ r' =
        entrywiseAdjointAut Tag.E6 η (twIncl σ r * gP * twIncl σ r') := by
      rw [map_mul, map_mul, hRfix r hr, hRfix r' hr']
    rw [e, entry_entrywiseAdjointAut]
    have := hall r hr r' hr'
    rw [map_mul, map_mul] at this
    exact (mem_fixSubfield η).1 this
  have hDmem : ∀ r' ∈ twR σ η,
      (endHom K g₂ - endHom K gP) (endHom K (twIncl σ r') (rootVec Tag.E6 K θ)) ∈ Z := by
    intro r' hr'
    rw [hZ, mem_vanishSub]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hx
    have hv : rootVec Tag.E6 K θ = Finsupp.single (rootLabel hθ.1) 1 := rootVec_of_isRoot' hθ.1
    have h1 := hent r hr r' hr'
    unfold entry at h1
    rw [hv]
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, ← Module.End.mul_apply,
      ← map_mul] at h1 ⊢
    rw [sub_eq_zero]
    simpa [mul_assoc, Module.End.mul_apply] using h1
  have hspan := twE6_span_orbit_eq_top hS hθ (twR_gens hS)
  have hle : Submodule.span K {x | ∃ r ∈ twRP σ η, x = endHom K r (rootVec Tag.E6 K θ)} ≤
      Z.comap (endHom K g₂ - endHom K gP) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨r', hr', rfl⟩
    obtain ⟨r'', hr'', rfl⟩ := Subgroup.mem_map.1 hr'
    exact hDmem r'' hr''
  rw [hspan] at hle
  have hDV : ∀ v, (endHom K g₂ - endHom K gP) v ∈ Z := fun v => hle (Submodule.mem_top (x := v))
  have hx : ∀ v : RootModule Tag.E6 K, endHom K (g₂ * gP⁻¹) v - v ∈ Z := by
    intro v
    have h1 := hDV (endHom K gP⁻¹ v)
    have e1 : endHom K gP (endHom K gP⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, e1] at h1
    rw [map_mul, Module.End.mul_apply]
    exact h1
  have h1 := eq_one_of_sub_mem_fixed hS.four_le_card hθ Z
    (twE6_vanishSub_fixed hS hθ (twR_gens hS)) (g₂ * gP⁻¹) hx
  have h2 : g₂ = gP := mul_inv_eq_one.1 h1
  rw [mem_twR_iff]
  exact h2

theorem exists_bad_entry_twE6 (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) (g : ↥(twistedE6RootGroup K σ)) (hg : g ∉ twR σ η) :
    ∃ r ∈ twR σ η, ∃ r' ∈ twR σ η,
      entry (twIncl σ (r * g * r')) (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield η := by
  by_contra h
  push Not at h
  exact hg (mem_twR_of_entries hS hθ g h)

end Entry

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
