module

public import Certificates.Data.Kernel.Misc.OrbLab
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.KC.OrbLab

open CFSG.KC.Enum
open CFSG.KS (bAnd_iff allN_spec)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

variable {n k : ℕ} {f : ℕ → ℕ → ℕ} {G PS blk Hd PR GN DP : ℕ → ℕ} {nt : ℕ}

theorem olPt_spec {y : ℕ} (h : olPt n k f G PS blk Hd PR GN DP y = true) :
    PS y < n ∧ G (PS y) = y ∧ G y < n ∧ PS (G y) = y ∧
      (∀ j < k, f j y < n ∧ blk (PS (f j y)) = blk (PS y)) ∧
      (DP y = 0 → y = Hd (blk (PS y))) ∧
      (DP y ≠ 0 → PR y < n ∧ GN y < k ∧ DP y = DP (PR y) + 1 ∧ f (GN y) (PR y) = y) := by
  unfold olPt at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
  obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h6
  obtain ⟨h9, h10⟩ := (bAnd_iff _ _).1 h8
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h3, Nat.blt_eq.mp h5, Nat.eq_of_beq_eq_true h7,
    fun j hj => ?_, fun hd => ?_, fun hd => ?_⟩
  · have hj' := allN_spec h9 j hj
    rw [strictB_eq] at hj'
    obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 hj'
    exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a2⟩
  · have e : Nat.beq (DP y) (nat_lit 0) = true := by rw [hd]; rfl
    rw [e] at h10
    exact Nat.eq_of_beq_eq_true h10
  · have e : Nat.beq (DP y) (nat_lit 0) = false := by
      cases e' : Nat.beq (DP y) (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e') hd
    rw [e, strictB_eq] at h10
    obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 h10
    obtain ⟨b3, b4⟩ := (bAnd_iff _ _).1 b2
    obtain ⟨b5, b6⟩ := (bAnd_iff _ _).1 b4
    exact ⟨Nat.blt_eq.mp b1, Nat.blt_eq.mp b3, Nat.eq_of_beq_eq_true b5, Nat.eq_of_beq_eq_true b6⟩

theorem olOK_parts (h : olOK n k f G PS blk nt Hd PR GN DP = true) :
    (∀ y < n, olPt n k f G PS blk Hd PR GN DP y = true) ∧
      ∀ t < nt, Hd t < n ∧ blk (PS (Hd t)) = t := by
  unfold olOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨allN_spec h1, fun t ht => ?_⟩
  obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 (allN_spec h2 t ht)
  exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a2⟩

theorem ol_bij (h : olOK n k f G PS blk nt Hd PR GN DP = true) :
    ∀ y < n, PS y < n ∧ G (PS y) = y ∧ G y < n ∧ PS (G y) = y := fun y hy => by
  obtain ⟨a1, a2, a3, a4, -⟩ := olPt_spec ((olOK_parts h).1 y hy)
  exact ⟨a1, a2, a3, a4⟩

variable {H : Subgroup (Equiv.Perm (Fin n))} {g : ℕ → Equiv.Perm (Fin n)}

theorem lab_smul (hH : H = Subgroup.closure {h | ∃ j < k, g j = h})
    (hf : ∀ j < k, ∀ y : Fin n, f j y = g j y) (h : olOK n k f G PS blk nt Hd PR GN DP = true) :
    ∀ σ ∈ H, ∀ y : Fin n, blk (PS (σ y)) = blk (PS y) := by
  intro σ hσ
  rw [hH] at hσ
  induction hσ using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    intro y
    rw [← hf j hj y]
    exact ((olPt_spec ((olOK_parts h).1 y y.isLt)).2.2.2.2.1 j hj).2
  | one => exact fun y => rfl
  | mul a c _ _ ha hc => exact fun y => (ha (c y)).trans (hc y)
  | inv a _ ha =>
    intro y
    have e := ha (a⁻¹ y)
    rw [show a (a⁻¹ y) = y from Equiv.apply_symm_apply a y] at e
    exact e.symm

theorem mem_orbit_head (hH : H = Subgroup.closure {h | ∃ j < k, g j = h})
    (hf : ∀ j < k, ∀ y : Fin n, f j y = g j y) (h : olOK n k f G PS blk nt Hd PR GN DP = true) :
    ∀ y : Fin n, ∃ hy : Hd (blk (PS y)) < n, y ∈ MulAction.orbit H (⟨Hd (blk (PS y)), hy⟩ : Fin n) := by
  have key : ∀ d, ∀ y : Fin n, DP y = d →
      ∃ hy : Hd (blk (PS y)) < n, y ∈ MulAction.orbit H (⟨Hd (blk (PS y)), hy⟩ : Fin n) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hd
      obtain ⟨-, -, -, -, hcl, h0, hs⟩ := olPt_spec ((olOK_parts h).1 y y.isLt)
      by_cases hd0 : DP y = 0
      · have e := h0 hd0
        have hy : Hd (blk (PS y)) < n := e ▸ y.isLt
        refine ⟨hy, ?_⟩
        have ey : (⟨Hd (blk (PS y)), hy⟩ : Fin n) = y := Fin.ext e.symm
        rw [ey]
        exact MulAction.mem_orbit_self y
      · obtain ⟨hq, hgk, hdq, hfy⟩ := hs hd0
        obtain ⟨hy', ho⟩ := ih (DP (PR y)) (by omega) ⟨PR y, hq⟩ rfl
        have hlab : blk (PS (PR y)) = blk (PS y) := by
          have := (olPt_spec ((olOK_parts h).1 (PR y) hq)).2.2.2.2.1 (GN y) hgk
          rw [hfy] at this
          exact this.2.symm
        have hgm : g (GN y) ∈ H := by
          rw [hH]
          exact Subgroup.subset_closure ⟨GN y, hgk, rfl⟩
        have ey : y = (⟨g (GN y), hgm⟩ : H) • (⟨PR y, hq⟩ : Fin n) := by
          apply Fin.ext
          change (y : ℕ) = (g (GN y) ⟨PR y, hq⟩ : ℕ)
          rw [← hf (GN y) hgk ⟨PR y, hq⟩]
          exact hfy.symm
        have hy : Hd (blk (PS y)) < n := hlab ▸ hy'
        refine ⟨hy, ?_⟩
        have e2 : (⟨Hd (blk (PS y)), hy⟩ : Fin n) = ⟨Hd (blk (PS (PR y))), hy'⟩ :=
          Fin.ext (congrArg Hd hlab.symm)
        rw [e2]
        have ho2 := MulAction.mem_orbit_of_mem_orbit (⟨g (GN y), hgm⟩ : H) ho
        rw [← ey] at ho2
        exact ho2
  exact fun y => key _ y rfl

theorem mem_orbit_iff (hH : H = Subgroup.closure {h | ∃ j < k, g j = h})
    (hf : ∀ j < k, ∀ y : Fin n, f j y = g j y) (h : olOK n k f G PS blk nt Hd PR GN DP = true)
    {t : ℕ} (ht : t < nt) (hHd : Hd t < n) (y : Fin n) :
    blk (PS y) = t ↔ y ∈ MulAction.orbit H (⟨Hd t, hHd⟩ : Fin n) := by
  have hlt := ((olOK_parts h).2 t ht).2
  constructor
  · intro e
    obtain ⟨hy, ho⟩ := mem_orbit_head hH hf h y
    have e2 : (⟨Hd (blk (PS y)), hy⟩ : Fin n) = ⟨Hd t, hHd⟩ := Fin.ext (congrArg Hd e)
    rw [← e2]
    exact ho
  · rintro ⟨⟨σ, hσ⟩, rfl⟩
    have e := lab_smul hH hf h σ hσ ⟨Hd t, hHd⟩
    change blk (PS (σ ⟨Hd t, hHd⟩)) = t
    rw [e]
    exact hlt

end CFSG.KC.OrbLab

end
