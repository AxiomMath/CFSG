module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvPre
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.HyperEichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

theorem commute_of_forall_apply_eq_orthJ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {W : Submodule K V} {a : V ≃ₗ[K] V}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hW : ∀ w ∈ W, a w = w) :
    ∀ x ∈ orthJ Q W, a * x = x * a := by
  have hle : orthJ Q W ≤ Subgroup.centralizer {a} := by
    rw [orthJ, Subgroup.closure_le]
    rintro _ ⟨u, hu, w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have := eichler_conj ha u w
    rw [hW u hu, hW w hw] at this
    calc a * eichler Q u w = a * eichler Q u w * a⁻¹ * a := by group
      _ = eichler Q u w * a := by rw [this]
  intro x hx
  have := Subgroup.mem_centralizer_iff.mp (hle hx) a rfl
  exact this

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

omit [Module.Finite (ZMod 2) V] in
theorem fixSub_anti {A A' : Subgroup (V ≃ₗ[ZMod 2] V)} (h : A ≤ A') : fixSub A' ≤ fixSub A :=
  fun _ hv g hg => hv g (h hg)

private theorem natCast_ne_zero_zmod_two' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ZMod 2) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm

theorem polarNondegOn_fixSub_zpowers (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hodd : Odd p)
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hap : a ^ p = 1) :
    PolarNondegOn Q (fixSub (Subgroup.zpowers a)) := by
  refine polarNondegOn_fixSub hQ ((Subgroup.zpowers_le).mpr ha) ?_
  refine odd_natCard_subgroup_of_pow_eq_one hodd fun h hh => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]

theorem elementaryGroup_le_iSup_orthJ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate)
    (hcO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ y ∈ elementaryGroup Q, g * y = y * g) → g = 1)
    (A : Subgroup (V ≃ₗ[ZMod 2] V)) (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1)
    (hcard : Nat.card A = p ^ 2) (P : HypPair Q) (hPe : ∀ h ∈ A, h P.e = P.e)
    (hPf : ∀ h ∈ A, h P.f = P.f) :
    elementaryGroup Q ≤ ⨆ (a : V ≃ₗ[ZMod 2] V) (_ : a ∈ A ∧ a ≠ 1 ∧
      4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers a))), orthJ Q (fixSub (Subgroup.zpowers a)) := by
  classical
  have hfinA : Finite A := by
    have := finite_linearEquiv (K := ZMod 2) (V := V)
    infer_instance
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpK := natCast_ne_zero_zmod_two' hp hp2
  have hgen := Coordinator.elementaryGroup_le_closure_hyperEichlerSet (Q := Q) hp hpK hQ hAO hcomm
    hexp P hPe hPf
  set S := Coordinator.hyperEichlerSet Q p A with hS
  have hAodd : Odd (Nat.card A) := by rw [hcard]; exact hodd.pow
  have hVDnd : PolarNondegOn Q (fixSub A) := polarNondegOn_fixSub hQ hAO hAodd
  have hVD0 : fixSub A ≠ ⊥ := by
    intro h
    have : P.e ∈ fixSub A := hPe
    rw [h] at this
    exact P.e_ne_zero (by simpa using this)
  have hWnd : ∀ a ∈ A, PolarNondegOn Q (fixSub (Subgroup.zpowers a)) := fun a ha =>
    polarNondegOn_fixSub_zpowers hQ hodd (hAO ha) (hexp a ha)
  have hVDle : ∀ a ∈ A, fixSub A ≤ fixSub (Subgroup.zpowers a) := fun a ha =>
    fixSub_anti ((Subgroup.zpowers_le).mpr ha)
  have hlow : ∀ a ∈ A, ¬ 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers a)) →
      fixSub (Subgroup.zpowers a) = fixSub A := by
    intro a ha h4
    by_contra hne
    exact h4 (four_le_finrank_of_lt hVDnd (hWnd a ha) hVD0
      (lt_of_le_of_ne (hVDle a ha) (Ne.symm hne)))
  have hgenmem : ∀ g ∈ S, ∃ a ∈ A, a ≠ 1 ∧ g ∈ orthJ Q (fixSub (Subgroup.zpowers a)) := by
    rintro g ⟨F, hFA, hF, u, w, hu, hw, rfl⟩
    have hp2' : p ≤ Nat.card F := by
      rw [hcard, pow_two] at hF
      exact Nat.le_of_mul_le_mul_left hF hp.pos
    have hFbot : F ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hp2'
      exact hp.one_lt.not_ge hp2'
    obtain ⟨f0, hf0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFbot
    refine ⟨(f0 : V ≃ₗ[ZMod 2] V), hFA f0.2, fun h => hf0 (Subtype.ext h), ?_⟩
    exact eichler_mem_orthJ (mem_fixSub_zpowers.mpr (hu f0 f0.2))
      (mem_fixSub_zpowers.mpr (hw f0 f0.2))
  have hne : ∃ a, a ∈ A ∧ a ≠ 1 ∧ 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers a)) := by
    by_contra hcon
    push Not at hcon
    have hJ : elementaryGroup Q ≤ orthJ Q (fixSub A) := by
      refine hgen.trans ?_
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨a, ha, ha1, hga⟩ := hgenmem g hg
      have := hlow a ha (by have := hcon a ha ha1; omega)
      rw [this] at hga
      exact hga
    have hA1 : ∀ a ∈ A, a = 1 := by
      intro a ha
      refine hcO a (hAO ha) fun y hy => ?_
      exact commute_of_forall_apply_eq_orthJ (hAO ha) (fun w (hw : w ∈ fixSub A) => hw a ha) y (hJ hy)
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hA1
    rw [this, Subgroup.card_bot] at hcard
    have := hp.one_lt
    nlinarith
  obtain ⟨a0, ha0A, ha01, ha04⟩ := hne
  refine hgen.trans ?_
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨a, ha, ha1, hga⟩ := hgenmem g hg
  by_cases h4 : 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers a))
  · exact (le_iSup₂ (f := fun (a : V ≃ₗ[ZMod 2] V) (_ : a ∈ A ∧ a ≠ 1 ∧
      4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers a))) => orthJ Q (fixSub (Subgroup.zpowers a)))
      a ⟨ha, ha1, h4⟩) hga
  · rw [hlow a ha h4] at hga
    have := orthJ_mono (Q := Q) (hVDle a0 ha0A)
    exact (le_iSup₂ (f := fun (a : V ≃ₗ[ZMod 2] V) (_ : a ∈ A ∧ a ≠ 1 ∧
      4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers a))) => orthJ Q (fixSub (Subgroup.zpowers a)))
      a0 ⟨ha0A, ha01, ha04⟩) (this hga)

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
