module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
open scoped MatrixGroups

set_option linter.unusedSectionVars false

private theorem excRec_frame_dim {τ : Tag} {L : Type} [Field L] {ν r : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} {κ : ℤ}
    (hψ : IsSLFrame ψ σ) (hκ : κ ≠ 0) (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ)
    (h2 : 2 ≤ r) (hr : (frameRoots σ).ncard = r * (r + 1)) : ν = r + 1 := by
  classical
  have hcard : (frameRoots σ).ncard = ν * (ν - 1) := by
    have hinj : Set.InjOn (fun q : Fin ν × Fin ν => σ q.1 q.2) {q | q.1 ≠ q.2} := by
      rintro ⟨x, y⟩ hxy ⟨u, v⟩ huv h
      simp only [Set.mem_setOf_eq] at hxy huv
      obtain ⟨rfl, rfl⟩ := hψ.eq_of_eq hκ hnorm hxy huv h
      rfl
    have himg : frameRoots σ = (fun q : Fin ν × Fin ν => σ q.1 q.2) '' {q | q.1 ≠ q.2} := by
      ext t
      constructor
      · rintro ⟨x, y, hxy, rfl⟩
        exact ⟨(x, y), hxy, rfl⟩
      · rintro ⟨⟨x, y⟩, hxy, rfl⟩
        exact ⟨x, y, hxy, rfl⟩
    rw [himg, hinj.ncard_image]
    have hoff : ({q : Fin ν × Fin ν | q.1 ≠ q.2} : Set (Fin ν × Fin ν)) =
        ↑(Finset.univ.offDiag : Finset (Fin ν × Fin ν)) := by
      ext q
      simp [Finset.mem_offDiag]
    rw [hoff, Set.ncard_coe_finset, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
      Nat.mul_sub_left_distrib, mul_one]
  have h : ν * (ν - 1) = r * (r + 1) := hcard.symm.trans hr
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by
    rcases Nat.eq_zero_or_pos ν with h0 | h0
    · subst h0
      simp at h
      omega
    · omega⟩
  rw [Nat.add_sub_cancel] at h
  have hm : m = r := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
  omega

private theorem excRec_split_twistInner {τ : Tag} {L : Type} [Field L] {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {κ : ℤ} (hκ : κ ≠ 0) (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : Ψ = frameRoots σ)
    (φ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → φ (σ x y) = σ (π x) (π y)) : twistInner Ψ φ := by
  obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
  subst hΨ
  refine ⟨w, hw, ?_⟩
  rintro γ ⟨x, y, hxy, rfl⟩
  rw [hπ x y hxy, hwσ x y]

private theorem excRec_frame_cases {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ) (κ : ℤ),
      ν = compRank (componentRoots (rootCharHom a) i) + 1 ∧ 3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧
      (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ) ∧
      componentRoots (rootCharHom a) i = frameRoots σ ∧
      ((∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y →
          (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y)) ∨
        ∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y →
          (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x)) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
    g2LongA2Frame_proved S hp hpL hTp i hA.1 hA.2
  have hνr : ν = compRank (componentRoots (rootCharHom a) i) + 1 :=
    excRec_frame_dim hψ hκ hnorm hA.1 (by rw [← hΨ]; exact hA.2)
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have hm1 : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have hm2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, hm1, rfl⟩
    rw [hs, hΨ] at hm2
    exact hm2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact ⟨ν, ψ, σ, κ, hνr, hν, hψ, hκ, hnorm, hΨ, Or.inl ⟨π, hπ⟩⟩
  · exact ⟨ν, ψ, σ, κ, hνr, hν, hψ, hκ, hnorm, hΨ, Or.inr ⟨π, hπ⟩⟩

theorem excRec_typeA_suN {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ f, 1 ≤ f ∧ ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSU
        (compRank (componentRoots (rootCharHom a) i) + 1) (ringChar L) f := by
  classical
  obtain ⟨ν, ψ, σ, κ, hνr, hν, hψ, hκ, hnorm, hΨ, hcases⟩ :=
    excRec_frame_cases S hp hT hap ha1 i hA
  rcases hcases with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact absurd (excRec_split_twistInner hψ hκ hnorm hΨ
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) π hπ) hout
  · obtain ⟨f, hf1, hfeq, hmodel⟩ :=
      rationalComponent_unitaryFrame_model S hT i hν hψ hΨ π hπ hQS
    exact ⟨f, hf1, hfeq, by rw [← hνr]; exact hmodel⟩

private theorem excRec_unitary_not_twistInner {τ : Tag} {L : Type} [Field L] {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hν : 3 ≤ ν)
    (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : Ψ = frameRoots σ)
    (φ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → φ (σ x y) = σ (π y) (π x)) : ¬ twistInner Ψ φ := by
  subst hΨ
  rintro ⟨w, hw, hwφ⟩
  have key : ∀ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ frameRoots σ, s = rootReflection γ},
      ∃ θ : Equiv.Perm (Fin ν), ∀ c d, u • σ c d = σ (θ c) (θ d) := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨γ, ⟨x, y, hxy, rfl⟩, rfl⟩ := hs
      exact ⟨Equiv.swap x y, fun c d => hψ.rootReflection_smul hκ hnorm hxy c d⟩
    | one => exact ⟨1, fun c d => by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨θ₁, h₁⟩ := hu
      obtain ⟨θ₂, h₂⟩ := hv
      exact ⟨θ₁ * θ₂, fun c d =>
        (by rw [mul_smul, h₂, h₁] : (u * v) • σ c d = σ (θ₁ (θ₂ c)) (θ₁ (θ₂ d)))⟩
    | inv u _ hu =>
      obtain ⟨θ, h⟩ := hu
      refine ⟨θ.symm, fun c d => ?_⟩
      have h' := h (θ.symm c) (θ.symm d)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
      rw [← h', inv_smul_smul]
  obtain ⟨θ, hθ⟩ := key w hw
  have hrel : ∀ a b, a ≠ b → θ a = π b := by
    intro a b hab
    have h1 : σ (θ a) (θ b) = σ (π b) (π a) := by
      rw [← hθ, ← hwφ _ ⟨a, b, hab, rfl⟩, hπ a b hab]
    exact (hψ.eq_of_eq hκ hnorm (fun h => hab (θ.injective h))
      (fun h => hab (π.injective h).symm) h1).1
  have hab : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hac : (⟨0, by omega⟩ : Fin ν) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hbc : (⟨1, by omega⟩ : Fin ν) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  exact hbc (π.injective ((hrel _ _ hab).symm.trans (hrel _ _ hac)))

theorem excRec_typeA_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ f, 1 ≤ f ∧ ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL
        (compRank (componentRoots (rootCharHom a) i) + 1) (ringChar L) f := by
  classical
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · obtain ⟨f, hf1, hfeq, hmodel⟩ := rationalComponent_rankOne_model S hT i hr1
      (by rw [hA.2, hr1]) hQS
    exact ⟨f, hf1, hfeq, by rw [hr1]; exact hmodel⟩
  · obtain ⟨ν, ψ, σ, κ, hνr, hν, hψ, hκ, hnorm, hΨ, hcases⟩ :=
      excRec_frame_cases S hp hT hap ha1 i ⟨by omega, hA.2⟩
    rcases hcases with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · obtain ⟨f, hf1, hfeq, hmodel⟩ :=
        rationalComponent_splitFrame_model S hT i hν hψ hΨ π hπ
      exact ⟨f, hf1, hfeq, by rw [← hνr]; exact hmodel⟩
    · exact absurd hinner (excRec_unitary_not_twistInner hν hψ hκ hnorm hΨ
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) π hπ)

theorem excRec_lieModel_two {L : Type} [Field L] [CharP L 2] {G : Type} [Group G]
    {t : StatedLieTag} {n f : ℕ} (ht : t ∈ CFSG.Blueprint.classicalTags)
    (h : StatedClassicalModel G t n (ringChar L) f) : CFSG.Blueprint.LieModel G t n 2 f := by
  rw [ringChar.eq L 2] at h
  exact Or.inl ⟨ht, h⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
