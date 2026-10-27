module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6ThreeLiftCent
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.FrameConj
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWPlane
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.Phi6ThreeArith
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.RootDiagPow
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6ThreeLift

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup TauCeti CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KEXC CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem exists_ne_one_map_eq_one_of_card_nine {L : Type} [Field L] {E : Type*} [Group E]
    (hE : Nat.card E = 9) (hE3 : ∀ x : E, x ^ 3 = 1) (φ : E →* Lˣ) :
    ∃ x : E, x ≠ 1 ∧ φ x = 1 := by
  by_contra h
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx1, hx⟩
  have hle : φ.range ≤ rootsOfUnity 3 L := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow, hE3, map_one]
  have h1 : Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h2 : Nat.card φ.range ≤ Nat.card (rootsOfUnity 3 L) := Subgroup.card_le_of_le hle
  have h3 := card_rootsOfUnity L 3
  omega


section Generic

variable {L : Type} [Field L] {G : Type} [Group G] {ι : G →* ModGL TwistTag.D4.tag L}
  {g0 : ModGL TwistTag.D4.tag L}

theorem orderOf_conj_apply (hι : Function.Injective ι) (z : G) :
    orderOf (g0⁻¹ * ι z * g0) = orderOf z := by
  have e1 : orderOf (g0⁻¹ * ι z * g0) = orderOf (ι z) := by
    have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective (ι z)
    simpa [MulAut.conj_apply] using this
  rw [e1, orderOf_injective ι hι z]

theorem exists_tupleHom_of_forall {E : Type*} [Group E] (ψ : E →* ModGL TwistTag.D4.tag L)
    (hψ : ∀ x, ∃ b, rootDiagUnit TwistTag.D4.tag b = ψ x) :
    ∃ β : E →* (Fin TwistTag.D4.tag.rank → Lˣ),
      ∀ x, rootDiagUnit TwistTag.D4.tag (β x) = ψ x := by
  have hinj : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := fun a b h =>
    CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.D4.tag) h
  let ψ' : E →* (rootDiagUnitHom TwistTag.D4.tag L).range :=
    ψ.codRestrict _ fun x => MonoidHom.mem_range.2 (hψ x)
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp ψ', fun x => ?_⟩
  have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply (ψ' x))
  rw [MonoidHom.ofInjective_apply] at h1
  exact h1

theorem exists_centralizer_le_of_frameTuples [IsAlgClosed L] (hι : Function.Injective ι)
    (hιC : ∀ g, ι g ∈ adjointGroup TwistTag.D4.tag L) (hg0 : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hL3 : ringChar L ≠ 3) {Fr : L →+* L} {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2)
    (hEtor : ∀ x ∈ E, ∃ b ∈ fixedCharTuples (d4T36M (-1)) Fr,
      rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * ι x * g0)
    {r' : ℕ} (hr' : r'.Prime) (hr'5 : 5 ≤ r') (hr'L : ringChar L ≠ r') {y : G} (hy1 : y ≠ 1)
    (hyr : y ^ r' = 1) {by' : Fin TwistTag.D4.tag.rank → Lˣ}
    (hbyF : by' ∈ fixedCharTuples (d4T36M (-1)) Fr)
    (hby : rootDiagUnit TwistTag.D4.tag by' = g0⁻¹ * ι y * g0) :
    ∃ x ∈ E, x ≠ 1 ∧
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  have : Fact r'.Prime := ⟨hr'⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 3) (x : G) x.2)
  have hE9 : Nat.card E = 9 := by rw [hEcard]; norm_num
  have hordy : orderOf (rootDiagUnit TwistTag.D4.tag by') = r' := by
    rw [hby, orderOf_conj_apply hι, orderOf_eq_prime hyr hy1]
  have hby1 : by' ≠ 1 := ne_one_of_orderOf_rootDiagUnit hr' hordy
  obtain ⟨β, hβ⟩ := exists_tupleHom_of_forall
    ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp E.subtype)) fun x => by
      obtain ⟨b, -, hb⟩ := hEtor x x.2
      exact ⟨b, by rw [hb]; simp⟩
  have hβx : ∀ x : E, rootDiagUnit TwistTag.D4.tag (β x) = g0⁻¹ * ι x * g0 := fun x => by
    rw [hβ]
    simp
  have hβF : ∀ x : E, β x ∈ fixedCharTuples (d4T36M (-1)) Fr := fun x => by
    obtain ⟨b, hbF, hb⟩ := hEtor x x.2
    have : b = β x := CFSG.LieType.Chevalley.rootDiagUnit_injective (hb.trans (hβx x).symm)
    exact this ▸ hbF
  have hβord : ∀ x : E, x ≠ 1 → orderOf (rootDiagUnit TwistTag.D4.tag (β x)) = 3 := fun x hx => by
    rw [hβx, orderOf_conj_apply hι]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 3) (x : G) x.2)
      fun h => hx (Subtype.ext h)
  rcases d4T36_rootCharKernel_cases (Or.inr rfl) hbyF hby1 with hker | ⟨i, hi⟩
  ·
    obtain ⟨x, hx1, -⟩ := exists_ne_one_map_eq_one_of_card_nine (L := L) hE9 hE3 1
    have hbp : rootDiagUnit Tag.D4 by' ^ r' = 1 := by
      have := pow_orderOf_eq_one (rootDiagUnit TwistTag.D4.tag by')
      rwa [hordy] at this
    exact ⟨x, x.2, fun h => hx1 (Subtype.ext h), centralizer_le_of_rootCharKernel_empty hι hιC hg0
      (hβx x) hby hker (Proving.stab_one_of_rootDiagUnit_pow hr' hr'5 hbp hker)⟩
  ·
    have hα : trialityU i ∈ rootCharKernel by' := by
      rw [hi]
      exact ⟨0, by norm_num, Or.inl (by rw [pow_zero, Matrix.one_mulVec])⟩
    obtain ⟨x, hx1, hxα⟩ := exists_ne_one_map_eq_one_of_card_nine (L := L) hE9 hE3
      ((MonoidHom.mk' (fun a => FourGroupChevalley.rootChar a (trialityU i))
        fun a b => CTTorus.rootChar_mul a b _).comp β)
    have hordx := hβord x hx1
    have hbx1 : β x ≠ 1 := ne_one_of_orderOf_rootDiagUnit Nat.prime_three hordx
    have hαx : trialityU i ∈ rootCharKernel (β x) := ⟨hα.1, hxα⟩
    have hix : rootCharKernel (β x) = trialitySigma i := by
      rcases d4T36_rootCharKernel_cases (Or.inr rfl) (hβF x) hbx1 with h | ⟨j, hj⟩
      · rw [h] at hαx
        exact absurd hαx (Set.notMem_empty _)
      · rcases eq_or_ne i j with rfl | hij
        · exact hj
        · exfalso
          rw [hi] at hα
          rw [hj] at hαx
          exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hij) hα hαx
    obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4,
        (fun α : Fin Tag.D4.rank → ℤ => v • α) '' d4A2Sigma = trialitySigma i := by
      obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
      obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
      exact ⟨w, by rw [d4A2Sigma_eq_trialityStdA2, ← hw]⟩
    exact ⟨x, x.2, fun h => hx1 (Subtype.ext h), centralizer_le_of_rootCharKernel_eq hι hιC hg0
      (hβx x) hby Nat.prime_three (by norm_num) hL3 hr' (by omega) hr'L hordx hordy
      (hix.trans hv.symm) (hi.trans hv.symm)⟩

end Generic


theorem phi6ThreeLift : Phi6ThreeLift := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ h3ℓ hd E hE hEcard hF
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨r', hr', hr'5, hr'ℓ, hr'd⟩ := Inner.exists_prime_ge_five_dvd_phi6 hℓ hℓ2 hf hd
  have : Fact r'.Prime := ⟨hr'⟩
  refine ⟨r', hr', hr'5, hr'ℓ, hr'd, ?_⟩
  obtain ⟨F, c₁, hc₁⟩ := hF
  obtain ⟨-, P, hPexp, hPcard, -, -⟩ :=
    Inner.exists_phi6_plane_with_involution hf K hK σ hσ hr' (by omega) hr'd
  have hPp : IsPGroup r' P := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hPexp g g.2)⟩
  obtain ⟨c₂, hc₂⟩ := Inner.exists_conj_into_frame_torus hf K hK σ hσ hr' (by omega) hr'd F P hPp
  have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard
  have hPea : CFSG.IsElementaryAbelian r' P := by
    refine { exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hPexp g g.2
  set c := c₁⁻¹ * c₂ with hc
  refine ⟨P.map (MulAut.conj c).toMonoidHom, CFSG.IsElementaryAbelian.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective,
      hPcard]
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hΩ : ringChar (AlgebraicClosure K) = ℓ := ringChar.eq _ ℓ
  have hι : Function.Injective
      ((triEmb K σ (AlgebraicClosure K)).comp (MulAut.conj c₁).toMonoidHom) :=
    triEmb_injective.comp (MulAut.conj c₁).injective
  have hT := twistedTorus_D4_eq_map_of_weylImage F.Fr F.hn F.w F.hnw (d4T36M (-1)) F.hw
  have htup : ∀ z, F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c₁ * z * c₁⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) →
      ∃ b ∈ fixedCharTuples (d4T36M (-1)) F.Fr, rootDiagUnit TwistTag.D4.tag b =
        F.g0⁻¹ * ((triEmb K σ (AlgebraicClosure K)).comp (MulAut.conj c₁).toMonoidHom) z *
          F.g0 := by
    intro z hz
    rw [hT] at hz
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.1 hz
    exact ⟨b, hb, hbz⟩
  rintro k ⟨y, hy, hy1, hky⟩
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
  have hconj : c₁ * ((MulAut.conj c).toMonoidHom y₀) * c₁⁻¹ = c₂ * y₀ * c₂⁻¹ := by
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨by', hbyF, hby⟩ := htup ((MulAut.conj c).toMonoidHom y₀) (by
    rw [hconj]
    exact hc₂ y₀ hy₀)
  have hyr : ((MulAut.conj c).toMonoidHom y₀) ^ r' = 1 := by
    rw [← map_pow, hPexp y₀ hy₀, map_one]
  obtain ⟨x, hxE, hx1, hle⟩ := exists_centralizer_le_of_frameTuples hι
    (fun g => triEmb_mem_adjointGroup _) F.hg0C (by rw [hΩ]; exact fun h => h3ℓ h.symm) hE hEcard
    (fun x hx => htup x (hc₁ x hx)) hr' hr'5 (by rw [hΩ]; exact fun h => hr'ℓ h.symm) hy1 hyr
    hbyF hby
  exact Subgroup.subset_closure ⟨x, hxE, hx1, Subgroup.mem_centralizer_singleton_iff.1
    (hle (Subgroup.mem_centralizer_singleton_iff.2 hky))⟩


theorem seitzExcAnisotropicForAt_trialityOdd_handback_of_coreW'
    (h : ∀ r, 5 ≤ r → Phi6CoreW r) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback_of_coreW_lift h phi6ThreeLift

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
