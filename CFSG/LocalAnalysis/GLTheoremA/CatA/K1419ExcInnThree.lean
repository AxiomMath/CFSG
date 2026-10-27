module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnArith
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInnerA2
public import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrder
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

section Three


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
  {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}

theorem l3u3_inn_a2_central (hF : L3U3Facts) (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1) (D : InnerData S a i)
    (hRDg : RDGlue τ) (h6 : (componentRoots (rootCharHom a) i).ncard = 6)
    (hL : L3U3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    ∃ w : ModGL τ L, w ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      (∀ g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, g * w = w * g) ∧
      w ^ 3 = 1 ∧ w ≠ 1 := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_rationalComponent S a i
  haveI : NeZero D.s := ⟨D.hs0.ne'⟩
  have hN := hF.order _ hL
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
  have hQ4 : 4 ≤ 2 ^ (D.e * D.s) := by
    by_contra hlt
    have h2 : ¬ 2 ≤ D.e * D.s := fun h2 => hlt (calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (D.e * D.s) := Nat.pow_le_pow_right (by norm_num) h2)
    have : D.e * D.s = 1 := by omega
    rw [D.hKcard, this] at hQmod
    norm_num at hQmod
  have h3K : 3 ∣ Nat.card (fixSubfield D.σ)ˣ := by
    rw [Nat.card_units]
    omega
  obtain ⟨ωK, hωKord⟩ := exists_prime_orderOf_dvd_card' 3 h3K
  have hωK3 : ωK ^ 3 = 1 := by
    rw [← hωKord]
    exact pow_orderOf_eq_one ωK
  have hωK1 : ωK ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωKord
    omega
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
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) D.σ D.hσ hm hQ4
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
  have h3s : ¬ 3 ∣ D.s := by
    obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
    have hcard := l3u3_inn_card_centerQuotient_mul hperf g hg hgk
    obtain ⟨d, cc, hd, hc0, hsym, hstep, hcardC⟩ :=
      CFSG.StandardType.SmallCompOrder.exists_card_componentRootSpan_counts
        (K := fixSubfield D.σ) (χ := rootCharHom a) i
    have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
    have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
    have hN3 : (posRoots (componentRoots (rootCharHom a) i)).ncard = 3 := by omega
    rw [hN3] at hcardC
    have hQeven : Even (Nat.card (fixSubfield D.σ)) :=
      D.hKcard ▸ Nat.even_pow.2 ⟨even_two, by omega⟩
    have hTodd : Odd (Nat.card (componentTorus (fixSubfield D.σ) (rootCharHom a) i)) := by
      rw [Nat.odd_iff]
      by_contra h2
      have h2' : 2 ∣ Nat.card (componentTorus (fixSubfield D.σ) (rootCharHom a) i) := by omega
      have h2'' := CFSG.StandardType.SmallCompOrder.prime_dvd_sub_one_of_dvd_card_componentTorus
        i Nat.prime_two h2'
      have := hQeven.two_dvd
      omega
    have hSodd : Odd (∑ k ∈ Finset.range (3 + 1), cc k * Nat.card (fixSubfield D.σ) ^ k) := by
      rw [Finset.sum_range_succ', hc0]
      have hev : Even (∑ k ∈ Finset.range 3,
          cc (k + 1) * Nat.card (fixSubfield D.σ) ^ (k + 1)) := by
        refine Finset.even_sum _ fun k _ => ?_
        exact (hQeven.pow_of_ne_zero (Nat.succ_ne_zero k)).mul_left _
      simpa using hev.add_one
    have hZdvd := CFSG.StandardType.SmallCompOrder.card_center_dvd_card_componentTorus
      (K := fixSubfield D.σ) (χ := rootCharHom a) i
    have key : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) *
          Nat.card (Subgroup.center ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i)) =
        Nat.card (componentTorus (fixSubfield D.σ) (rootCharHom a) i) * (2 ^ (D.e * D.s)) ^ 3 *
          ∑ k ∈ Finset.range (3 + 1), cc k * Nat.card (fixSubfield D.σ) ^ k := by
      rw [hcard, hcardC, D.hKcard]
    have := l3u3_inn_not_three_dvd_of_card_eq hN hTodd hSodd hZdvd key
    exact fun h3 => this (Dvd.dvd.mul_left h3 _)
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
    apply h3s
    have : orderOf (rootDiagUnit τ a) = 3 := orderOf_eq_prime hd3 h1
    exact this ▸ orderOf_dvd_of_pow_eq_one hw

end Three

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
