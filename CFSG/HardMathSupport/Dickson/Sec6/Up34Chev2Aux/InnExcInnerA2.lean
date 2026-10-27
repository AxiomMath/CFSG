module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcA2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCong
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.PartOne.KE

namespace Up34Exc

section A2Lemmas

set_option linter.unusedSectionVars false

theorem exists_cube_root_unit {K : Type} [Field K] [Finite K] (h : Nat.card K = 4) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card Kˣ = 3 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h]
  have hnt : Nontrivial Kˣ := Fintype.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  refine ⟨ω, ?_, hω⟩
  rw [← hcard]
  exact pow_card_eq_one


theorem step_rootDiagUnit_of_mem_torus {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) :
    S.D.step (rootDiagUnit τ a) = rootDiagUnit τ a :=
  (mem_twistedTorusOf.1 hT).2

theorem rootDiagUnit_eq_or_inv_of_glue {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    {ω : Lˣ} {m : Fin τ.rank → ℤ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hglue : ∀ j, a j = ω ^ (ε * m j)) :
    rootDiagUnit τ a = rootDiagUnit τ (fun j => ω ^ m j) ∨
      rootDiagUnit τ a = (rootDiagUnit τ (fun j => ω ^ m j))⁻¹ := by
  rcases hε with rfl | rfl
  · left
    congr 1
    funext j
    rw [hglue j, one_mul]
  · right
    rw [rootDiagUnit_inv]
    congr 1
    funext j
    rw [hglue j, Pi.inv_apply, neg_one_mul, zpow_neg]

end A2Lemmas

section A2Central

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
  {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}

theorem inner_a2_central (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (D : InnerData S a i) (hRDg : RDGlue τ)
    (h6 : (componentRoots (rootCharHom a) i).ncard = 6)
    (hL34 : IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    ∃ w : ModGL τ L, w ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      (∀ g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, g * w = w * g) ∧
      w ^ 3 = 1 ∧ w ≠ 1 := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_rationalComponent S a i
  haveI : NeZero D.s := ⟨D.hs0.ne'⟩
  obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ := hRDg L a hap i h6
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply h1
    have : a = 1 := funext hcon
    rw [this, rootDiagUnit_one]
  obtain ⟨j0, hj0⟩ := ha1
  have hω3 : (a j0) ^ 3 = 1 := hap j0
  obtain ⟨ε, hε, hglue⟩ := hglueAll (a j0) hω3 hj0
  have hQmod := q_pow_mod_three_of_inner_a2 S hT i D.hinner hP hΨeq hω3 hj0 hε hglue ⟨j0, hj0⟩
  have hQ : S.D.q ^ D.s = Nat.card (fixSubfield D.σ) := by rw [D.hq, D.hKcard, ← pow_mul]
  rw [hQ] at hQmod
  have hm : 0 < D.e * D.s := Nat.mul_pos D.he D.hs0
  have hcases : Nat.card (fixSubfield D.σ) = 4 ∨ 16 ≤ Nat.card (fixSubfield D.σ) := by
    rw [D.hKcard] at hQmod ⊢
    generalize D.e * D.s = m at hm hQmod ⊢
    by_cases h4 : 4 ≤ m
    · right
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h4
    · left
      interval_cases m
      · norm_num at hQmod
      · norm_num
      · norm_num at hQmod
  rcases hcases with hQ4 | hQ16
  ·
    have hes : D.e * D.s = 2 := by
      have h4 : (2 : ℕ) ^ (D.e * D.s) = 2 ^ 2 := by rw [← D.hKcard, hQ4]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h4
    have hs2 : D.s ≤ 2 := by
      have : D.s ≤ D.e * D.s := Nat.le_mul_of_pos_left D.s D.he
      omega
    obtain ⟨ωK, hωK3, hωK1⟩ := exists_cube_root_unit hQ4
    set ι : fixSubfield D.σ →+* L := (fixSubfield D.σ).subtype with hι
    set ω : Lˣ := Units.map ι.toMonoidHom ωK with hω
    have hω3' : ω ^ 3 = 1 := by rw [hω, ← map_pow, hωK3, map_one]
    have hω1' : ω ≠ 1 := fun h => hωK1 (Units.map_injective (RingHom.injective ι) (by
      rw [map_one]; exact h))
    obtain ⟨ε', hε', hglue'⟩ := hglueAll ω hω3' hω1'
    set dω : ModGL τ L := rootDiagUnit τ (fun j => ω ^ a2Exp τ γ₁ γ₂ j) with hdω
    have hrel : rootDiagUnit τ a = dω ∨ rootDiagUnit τ a = dω⁻¹ :=
      rootDiagUnit_eq_or_inv_of_glue hε' hglue'
    have hz0C : z0 τ γ₁ γ₂ ωK ∈ componentRootSpan (fixSubfield D.σ) (rootCharHom a) i := by
      change z0 τ γ₁ γ₂ ωK ∈ rootSpan τ (fixSubfield D.σ) (componentRoots (rootCharHom a) i)
      refine z0_mem_rootSpan hP ?_ ?_ ?_ ?_ ωK <;> rw [hΨeq] <;> simp
    have hQ' : 4 ≤ 2 ^ (D.e * D.s) := by rw [hes]; norm_num
    obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) D.σ D.hσ hm hQ'
    have hperf := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield D.σ)
      (χ := rootCharHom a) ht i
    set c : ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) := ⟨_, hz0C⟩ with hc
    have hιc : baseChangeGL ι c.1 = dω := by
      change baseChangeGL ι (z0 τ γ₁ γ₂ ωK) = _
      rw [z0, baseChangeGL_rootDiagUnit, hdω]
      congr 1
      funext j
      rw [map_zpow]
    have hzd : Commute D.z (rootDiagUnit τ a) :=
      (rootDiagUnit_mul_comm_of_mem_Z a D.hzZ).symm
    have hzdω : Commute D.z dω := by
      rcases hrel with h | h
      · rw [← h]; exact hzd
      · rw [h] at hzd; exact Commute.inv_right_iff.1 hzd
    have hstep_a : S.D.step (rootDiagUnit τ a) = rootDiagUnit τ a :=
      step_rootDiagUnit_of_mem_torus S hT
    have hstep_ω : S.D.step dω = dω := by
      rcases hrel with h | h
      · rw [← h]; exact hstep_a
      · have e : dω = (rootDiagUnit τ a)⁻¹ := by rw [h, inv_inv]
        rw [e, map_inv, hstep_a]
    have hconj : D.z * dω * D.z⁻¹ = dω := by
      rw [hzdω.eq]; group
    have hpow : dω ^ D.s ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
      have h := pow_mem_rationalComponent_of_fixed S hT i (s := D.s) D.hs D.hmin D.σ D.z D.hnorm
        D.hz hperf c (by
          show S.D.step (D.z * baseChangeGL ι c.1 * D.z⁻¹) = D.z * baseChangeGL ι c.1 * D.z⁻¹
          rw [hιc, hconj]
          exact hstep_ω)
      have e : D.z * baseChangeGL (fixSubfield D.σ).subtype c.1 * D.z⁻¹ = dω := by
        rw [← hconj]
        exact congrArg (fun x => D.z * x * D.z⁻¹) hιc
      rw [e] at h
      exact h
    have hd3 : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
    refine ⟨rootDiagUnit τ a ^ D.s, ?_, ?_, ?_, ?_⟩
    · rcases hrel with h | h
      · rw [h]; exact hpow
      · rw [h, inv_pow]; exact inv_mem hpow
    · intro g hg
      have hgc := ((langSubnormal_of_mem_torus S hT i).1 hg).2
      have h := Subgroup.mem_centralizer_singleton_iff.1 hgc
      exact (Commute.pow_right (show Commute g (rootDiagUnit τ a) from h) D.s).eq
    · rw [← pow_mul, mul_comm, pow_mul, hd3, one_pow]
    · intro hw
      have hs12 : D.s = 1 ∨ D.s = 2 := by have := D.hs0; omega
      rcases hs12 with h | h
      · rw [h, pow_one] at hw
        exact h1 hw
      · rw [h] at hw
        apply h1
        calc rootDiagUnit τ a = rootDiagUnit τ a ^ 3 * (rootDiagUnit τ a ^ 2)⁻¹ := by group
          _ = 1 := by rw [hd3, hw]; simp
  · exfalso
    have hQ' : 4 ≤ 2 ^ (D.e * D.s) := by rw [← D.hKcard]; omega
    obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) D.σ D.hσ hm hQ'
    have hperf := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield D.σ)
      (χ := rootCharHom a) ht i
    obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
    have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
    have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
    have hN : (posRoots (componentRoots (rootCharHom a) i)).ncard = 3 := by omega
    have hbig' : 64 < Nat.card (fixSubfield D.σ) ^
        (posRoots (componentRoots (rootCharHom a) i)).ncard := by
      rw [hN]
      calc 64 < 16 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_left hQ16 3
    exact unipotent_not_isLThreeFour uniEmbed_holds (rootCharHom a) i (fixSubfield D.σ) g hg hgk
      hperf hL34 hbig'

end A2Central

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
