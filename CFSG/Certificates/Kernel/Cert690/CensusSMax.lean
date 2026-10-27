module

public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.KC.C690S

theorem exists_rep_of_cover {G X : Type*} [Group G] [MulAction G X] {O F H' : Subgroup G}
    (hF : F ≤ H') (hH' : H' ≤ O) (b : X) (Y reps : Set X) (tp : X → G) (T : Set G)
    (hY : ∀ h ∈ O, h • b ∈ Y) (horb : ∀ q ∈ Y, ∃ p ∈ reps, ∃ f ∈ F, q = f • p)
    (htp : ∀ p ∈ reps, tp p ∈ O ∧ tp p • b = p)
    (hcov : ∀ y ∈ O, y • b = b → ∃ u ∈ T, ∃ c ∈ F, y = u * c)
    {h : G} (hh : h ∈ H') (hhF : h ∉ F) :
    ∃ p ∈ reps, ∃ u ∈ T, tp p * u ∈ H' ∧ tp p * u ∉ F := by
  obtain ⟨p, hp, f, hf, hq⟩ := horb _ (hY h (hH' hh))
  obtain ⟨htpO, htpb⟩ := htp p hp
  have hyO : (tp p)⁻¹ * f⁻¹ * h ∈ O :=
    O.mul_mem (O.mul_mem (O.inv_mem htpO) (O.inv_mem (hH' (hF hf)))) (hH' hh)
  have hyb : ((tp p)⁻¹ * f⁻¹ * h) • b = b := by
    rw [mul_smul, mul_smul, hq, inv_smul_smul, inv_smul_eq_iff]
    exact htpb.symm
  obtain ⟨u, hu, c, hc, hyuc⟩ := hcov _ hyO hyb
  have hr : tp p * u = f⁻¹ * h * c⁻¹ := by
    have e : f⁻¹ * h = tp p * ((tp p)⁻¹ * f⁻¹ * h) := by group
    rw [e, hyuc]
    group
  refine ⟨p, hp, u, hu, ?_, ?_⟩
  · rw [hr]
    exact H'.mul_mem (H'.mul_mem (H'.inv_mem (hF hf)) hh) (H'.inv_mem (hF hc))
  · intro hrF
    rw [hr] at hrF
    apply hhF
    have e : h = f * (f⁻¹ * h * c⁻¹) * c := by group
    rw [e]
    exact F.mul_mem (F.mul_mem hf hrF) hc

theorem maximality_by_index {G : Type*} [Group G] (H N : Subgroup G) (good : G → Prop)
    (F : ℕ → Subgroup G) (A : ℕ → Prop) (nF : ℕ)
    (hG1 : ∀ h ∈ H, good h) (hG2 : ∀ n ∈ N, ∀ x, good x → good (n⁻¹ * x * n))
    (hB : ∃ k < nF, A k ∧ ∃ n ∈ N, ∀ x ∈ F k, n * x * n⁻¹ ∈ H)
    (hK : ∀ k < nF, A k → ∀ H' : Subgroup G, F k ≤ H' → (∀ x ∈ H', good x) →
      (∃ h ∈ H', h ∉ F k) →
      ∃ k', k < k' ∧ k' < nF ∧ A k' ∧ ∃ n' ∈ N, ∀ x ∈ F k', n' * x * n'⁻¹ ∈ H') :
    ∃ k < nF, A k ∧ ∃ n ∈ N, ∀ x, x ∈ H ↔ n⁻¹ * x * n ∈ F k := by
  classical
  let P : ℕ → Prop := fun k => A k ∧ ∃ n ∈ N, ∀ x ∈ F k, n * x * n⁻¹ ∈ H
  let S : Finset ℕ := (Finset.range nF).filter P
  obtain ⟨k0, hk0, hP0⟩ := hB
  have hS : S.Nonempty := ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk0, hP0⟩⟩
  have hkS := S.max'_mem hS
  set k := S.max' hS
  obtain ⟨hklt, hAk, n, hn, hPn⟩ := (by simpa [S, P] using hkS :
    k < nF ∧ A k ∧ ∃ n ∈ N, ∀ x ∈ F k, n * x * n⁻¹ ∈ H)
  let H' : Subgroup G :=
    { carrier := {x | n * x * n⁻¹ ∈ H}
      mul_mem' := fun {a c} ha hc => by
        have e : n * (a * c) * n⁻¹ = (n * a * n⁻¹) * (n * c * n⁻¹) := by group
        change n * (a * c) * n⁻¹ ∈ H
        rw [e]
        exact H.mul_mem ha hc
      one_mem' := by
        change n * 1 * n⁻¹ ∈ H
        rw [mul_one, mul_inv_cancel]
        exact H.one_mem
      inv_mem' := fun {a} ha => by
        have e : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
        change n * a⁻¹ * n⁻¹ ∈ H
        rw [e]
        exact H.inv_mem ha }
  have memH' : ∀ x, x ∈ H' ↔ n * x * n⁻¹ ∈ H := fun x => Iff.rfl
  have hFH' : F k ≤ H' := fun x hx => (memH' x).mpr (hPn x hx)
  have hgood : ∀ x ∈ H', good x := by
    intro x hx
    have := hG2 n hn _ (hG1 _ ((memH' x).mp hx))
    simpa [mul_assoc] using this
  have hall : ∀ x ∈ H', x ∈ F k := by
    intro x hx
    by_contra hxF
    obtain ⟨k', hkk', hk'lt, hAk', n', hn', hF'⟩ := hK k hklt hAk H' hFH' hgood ⟨x, hx, hxF⟩
    have hP' : P k' := by
      refine ⟨hAk', n * n', N.mul_mem hn hn', fun y hy => ?_⟩
      have e : n * n' * y * (n * n')⁻¹ = n * (n' * y * n'⁻¹) * n⁻¹ := by group
      rw [e]
      exact (memH' _).mp (hF' y hy)
    have hle := S.le_max' k' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk'lt, hP'⟩)
    omega
  have e : ∀ x, n * (n⁻¹ * x * n) * n⁻¹ = x := fun x => by group
  refine ⟨k, hklt, hAk, n, hn, fun x => ⟨fun hx => hall _ ((memH' _).mpr ?_), fun hx => ?_⟩⟩
  · rw [e]
    exact hx
  · have := hPn _ hx
    rwa [e] at this

end CFSG.KC.C690S

end
