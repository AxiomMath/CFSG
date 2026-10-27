module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentAux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma fk3_coord_ab {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {γ : V ≃ₗ[ZMod 3] V} (hγ : IsSimilitude Q γ (-1))
    (hW : ∀ (i : Fin 2) (k : Fin 4), fr.b.repr (γ⁻¹ (fr.b (Sum.inl i))) (Sum.inr k) = 0)
    (m : Fin 2) : fr.b.repr (γ (fr.b (Sum.inr 0))) (Sum.inl m) = 0 := by
  have hy : fr.b.repr (γ⁻¹ (fr.b (Sum.inl m))) (Sum.inr 0) = 0 := hW m 0
  have hγγ : γ (γ⁻¹ (fr.b (Sum.inl m))) = fr.b (Sum.inl m) := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have h1 : QuadraticMap.polar Q (fr.b (Sum.inl m)) (γ (fr.b (Sum.inr 0))) = 0 := by
    rw [QuadraticMap.polar_comm]
    conv_lhs => rw [← hγγ]
    rw [ffOutFFE8Cent_polar_sim hγ, ffOutFFE8Cent_polar_basis fr (Sum.inr 0), hy]
    simp
  rw [ffOutFFE8Cent_polar_basis fr (Sum.inl m)] at h1
  have h2 : (2 : ZMod 3) * ffE8Norm ε (Sum.inl m) ≠ 0 := by
    fin_cases m <;> simp [ffE8Norm] <;> decide
  exact (mul_eq_zero.mp h1).resolve_left h2

theorem ffOutFFE8Cent_no_neg {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {γ : V ≃ₗ[ZMod 3] V} (hγ : IsSimilitude Q γ (-1))
    (hn : ∀ δ : V ≃ₗ[ZMod 3] V, (δ = γ ∨ δ = γ⁻¹) →
      ∀ e ∈ ffE8Group fr, ∃ e'' ∈ ffE8Group fr, ∃ s : ZMod 3, (s = 1 ∨ s = -1) ∧
        ∀ v, (e : V ≃ₗ[ZMod 3] V) (δ v) = s • δ ((e'' : V ≃ₗ[ZMod 3] V) v)) : False := by
  have hW2 := fun i k => ffOutFFE8Cent_inW fr (hn γ⁻¹ (Or.inr rfl)) i k
  have hab : ∀ m : Fin 2, fr.b.repr (γ (fr.b (Sum.inr 0))) (Sum.inl m) = 0 := by
    intro m
    refine fk3_coord_ab fr hγ (fun i k => ?_) m
    exact hW2 i k
  have hs : ∀ J : Finset (Fin 4), Even J.card → ∃ s : ZMod 3,
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) (γ (fr.b (Sum.inr 0))) =
        s • γ (fr.b (Sum.inr 0)) ∧
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) (γ (fr.b (Sum.inr 0))) =
        s • γ (fr.b (Sum.inr 0)) := by
    intro J hJ
    have he : fr.signChange (ffE8Hat J) ∈ ffE8Group fr :=
      (mem_ffE8Group_iff fr).mpr ⟨J, hJ, rfl⟩
    obtain ⟨e'', he'', s, -, hv⟩ := hn γ (Or.inl rfl) _ he
    rcases ffOutFFE8Cent_group_inr fr he'' 0 with h0 | h0
    · exact ⟨s, by rw [hv, h0], by rw [hv, h0]⟩
    · refine ⟨-s, ?_, ?_⟩ <;> rw [hv, h0, map_neg, smul_neg, neg_smul]
  obtain ⟨k, hk⟩ : ∃ k, fr.b.repr (γ (fr.b (Sum.inr 0))) (Sum.inr k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : γ (fr.b (Sum.inr 0)) = 0 := by
      apply fr.b.repr.injective
      ext i
      rcases i with m | k
      · simp [hab m]
      · simp [hcon k]
    exact fr.b.ne_zero (Sum.inr 0) (by simpa using h0)
  have hsupp : ∀ i, i ≠ Sum.inr k → fr.b.repr (γ (fr.b (Sum.inr 0))) i = 0 := fun i hi =>
    (ffOutFFE8Cent_supp fr hs hk hi).1
  have hQu := ffOutFFE8Cent_Q_single fr (γ (fr.b (Sum.inr 0))) (Sum.inr k) hsupp
  have hQ1 : Q (γ (fr.b (Sum.inr 0))) = -ε := by
    rw [hγ, fr.norm (Sum.inr 0)]
    simp [ffE8Norm]
  have hsq : fr.b.repr (γ (fr.b (Sum.inr 0))) (Sum.inr k) ^ 2 = 1 := by
    revert hk
    generalize fr.b.repr (γ (fr.b (Sum.inr 0))) (Sum.inr k) = x
    revert x
    decide
  rw [hQ1, hsq] at hQu
  simp only [ffE8Norm, Sum.elim_inr, mul_one] at hQu
  rcases hε with rfl | rfl <;> revert hQu <;> decide

theorem ffOutFFE8Cent_main (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q}
    (h : FFE8SData hQ Ē z ν) :
    ∀ x ∈ normalizer (Ē : Set (ProjSim Q)), SimInGStar x := by
  intro x hx
  obtain ⟨ε, hε, fr, hĒ, -⟩ := ffE8_frame_sim hQ hdim hsgn h
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  rcases ffOutFFE8Cent_mult γ with h1 | h1
  · exact ffOutFFE8Cent_simInGStar h1
  · exfalso
    refine ffOutFFE8Cent_no_neg hε fr h1 ?_
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact ffOutFFE8Cent_conj hĒ (δ := γ) hx
    · have hx' : (QuotientGroup.mk γ⁻¹ : ProjSim Q) ∈ normalizer (Ē : Set (ProjSim Q)) := by
        rw [QuotientGroup.mk_inv]
        exact Subgroup.inv_mem _ hx
      exact ffOutFFE8Cent_conj hĒ (δ := γ⁻¹) hx'

end CFSG.OddStandard.SmallF3.Omega
