module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Toral
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralMain
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriAbs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res417Seven
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section Odd


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem card_le_three_of_normalizes (hσ3 : σ ^ 3 = 1) (h3 : ¬ 3 ∣ Nat.card Kˣ)
    {A R : Subgroup (ModGL TwistTag.D4.tag K)}
    (hAX : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hRX : R ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL TwistTag.D4.tag K)))
    {E : Subgroup (ModGL TwistTag.D4.tag K)} (hEA : E ≤ A) (hE3 : ∀ y ∈ E, y ^ 3 = 1) :
    Nat.card E ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3' : IsPGroup 3 E := fun y => ⟨1, by rw [pow_one]; exact Subtype.ext (hE3 y y.2)⟩
  obtain ⟨x₀, -, J, hJ, hEJ⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 (r := 2)
    (p := 3) (by norm_num) σ hσ3 (hEA.trans hAX) hE3' hRX hR2 hR (hEA.trans hAR)
  have h1 := card_le_three_of_le_graphFixedParabolicLevi σ hσ3 h3 hJ hEJ (by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE3 y hy, map_one])
  rwa [Subgroup.card_map_of_injective (MulAut.conj x₀).injective] at h1

theorem exists_conj_mem_range_of_normalizes (hσ3 : σ ^ 3 = 1) (h3 : ¬ 3 ∣ Nat.card Kˣ)
    {A R : Subgroup (ModGL TwistTag.D4.tag K)}
    (hAX : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hRX : R ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL TwistTag.D4.tag K)))
    {y : ModGL TwistTag.D4.tag K} (hyA : y ∈ A) (hy3 : y ^ 3 = 1) :
    ∃ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ∃ a : Fin TwistTag.D4.foldedTag.rank,
        g * y * g⁻¹ ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEA : Subgroup.zpowers y ≤ A := (Subgroup.zpowers_le).2 hyA
  have hE3 : ∀ z ∈ Subgroup.zpowers y, z ^ 3 = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast, hy3,
      _root_.one_zpow]
  have hE3' : IsPGroup 3 (Subgroup.zpowers y) :=
    fun z => ⟨1, by rw [pow_one]; exact Subtype.ext (hE3 z z.2)⟩
  obtain ⟨g, hg, J, hJ, hEJ⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 (r := 2)
    (p := 3) (by norm_num) σ hσ3 (hEA.trans hAX) hE3' hRX hR2 hR (hEA.trans hAR)
  obtain ⟨a, haJ⟩ := exists_subset_singleton_of_ne_univ hJ
  have hmem : g * y * g⁻¹ ∈ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a} :=
    graphFixedParabolicLevi_mono _ haJ
      (hEJ ⟨y, Subgroup.mem_zpowers y, by simp [MulAut.conj_apply]⟩)
  refine ⟨g, hg, a, mem_range_of_mem_graphFixedParabolicLevi σ h3 a hmem ?_⟩
  have h := map_pow (MulAut.conj g) y 3
  rw [hy3, map_one, MulAut.conj_apply] at h
  exact h.symm

end Odd

section Pair


variable {K : Type} [Field K] (σ : K →+* K)

theorem graphFixedRootPair_le_rootSpan_union (O : Set (Fin TwistTag.D4.tag.rank → ℤ)) :
    graphFixedRootPair TwistTag.D4 K σ O ≤ rootSpan TwistTag.D4.tag K (O ∪ -O) := by
  rw [CFSG.RankThree.PartOne.KE.rootSpan_union_eq]
  exact sup_le_sup inf_le_left inf_le_left

theorem range_orbitRankOneHom_eq_pair (a : Fin TwistTag.D4.foldedTag.rank) :
    (orbitRankOneHom TwistTag.D4 K σ a).range =
      graphFixedRootPair TwistTag.D4 K σ (fixedOrbitImage TwistTag.D4 1 a) := by
  have h : orbitConjRankOneHom TwistTag.D4 K σ 1 a = orbitRankOneHom TwistTag.D4 K σ a :=
    MonoidHom.ext fun g => by
      rw [orbitConjRankOneHom_apply, canonicalRep_one, one_mul, inv_one, mul_one]
  rw [← h]
  exact range_orbitConjRankOneHom (one_mem _) a

end Pair

section Check

theorem orth_check_outer : ∀ i ∈ TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank),
    ∀ γ ∈ TwistTag.D4.diagramOrbit (![1, 1, 2, 1] : Fin TwistTag.D4.tag.rank → ℤ),
      (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0 := by
  decide +kernel

theorem orth_check_middle : ∀ i ∈ TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank),
    ∀ γ ∈ TwistTag.D4.diagramOrbit (![1, 1, 1, 0] : Fin TwistTag.D4.tag.rank → ℤ),
      (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0 := by
  decide +kernel

end Check

section OrthHelpers

theorem orth_of_neg_right {β γ : Fin Tag.D4.rank → ℤ}
    (h : β ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ (-γ)) = 0) :
    β ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0 := by
  rw [Matrix.mulVec_neg, dotProduct_neg, neg_eq_zero] at h
  exact h

theorem orth_of_neg_left {β γ : Fin Tag.D4.rank → ℤ}
    (h : (-β) ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0) :
    β ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0 := by
  rw [neg_dotProduct, neg_eq_zero] at h
  exact h

end OrthHelpers

section PairMain


variable {K : Type} [Field K] (σ : K →+* K)

theorem exists_commuting_rank_one (a : Fin TwistTag.D4.foldedTag.rank) :
    ∃ (w : WeylGroup TwistTag.D4.tag) (b : Fin TwistTag.D4.foldedTag.rank),
      w ∈ relWeylTwist TwistTag.D4 ∧
      ∀ y ∈ (orbitRankOneHom TwistTag.D4 K σ a).range,
        ∀ z ∈ (orbitConjRankOneHom TwistTag.D4 K σ w b).range, y * z = z * y := by
  have key : ∃ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α ∧
      ∀ i ∈ TwistTag.D4.orbit a, ∀ γ ∈ TwistTag.D4.diagramOrbit α,
        (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0 := by
    rcases foldedD4_cases a with rfl | rfl
    · exact ⟨![1, 1, 2, 1], isRoot_iff_mem_artifactRoots.2 (by decide), orth_check_outer⟩
    · exact ⟨![1, 1, 1, 0], isRoot_iff_mem_artifactRoots.2 (by decide), orth_check_middle⟩
  obtain ⟨α, hα, horth⟩ := key
  obtain ⟨w, hw, b, hdiag, -, -⟩ := (diagram_root_orbit_reduction TwistTag.D4).1 α hα
  refine ⟨w, b, hw, fun y hy z hz => ?_⟩
  have hOset : fixedOrbitImage TwistTag.D4 w b =
      (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
    rw [hdiag, Finset.coe_image]
    rfl
  have hE : fixedOrbitImage TwistTag.D4 1 a =
      (fun i => (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) '' ↑(TwistTag.D4.orbit a) := by
    simp [fixedOrbitImage]
  rw [range_orbitRankOneHom_eq_pair] at hy
  rw [range_orbitConjRankOneHom hw b] at hz
  have hy' := graphFixedRootPair_le_rootSpan_union σ _ hy
  have hz' := graphFixedRootPair_le_rootSpan_union σ _ hz
  have hS₁ : ∀ r ∈ fixedOrbitImage TwistTag.D4 1 a ∪ -fixedOrbitImage TwistTag.D4 1 a,
      IsRoot TwistTag.D4.tag r := by
    rintro r (hr | hr)
    · exact isRoot_of_mem_fixedOrbitImage hr
    · have := IsRoot.neg (isRoot_of_mem_fixedOrbitImage (Set.mem_neg.1 hr))
      rwa [neg_neg] at this
  have hS₂ : ∀ r ∈ fixedOrbitImage TwistTag.D4 w b ∪ -fixedOrbitImage TwistTag.D4 w b,
      IsRoot TwistTag.D4.tag r := by
    rintro r (hr | hr)
    · exact isRoot_of_mem_fixedOrbitImage hr
    · have := IsRoot.neg (isRoot_of_mem_fixedOrbitImage (Set.mem_neg.1 hr))
      rwa [neg_neg] at this
  have horth' : ∀ β ∈ fixedOrbitImage TwistTag.D4 1 a ∪ -fixedOrbitImage TwistTag.D4 1 a,
      ∀ γ ∈ fixedOrbitImage TwistTag.D4 w b ∪ -fixedOrbitImage TwistTag.D4 w b,
        β ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0 := by
    have base : ∀ β ∈ fixedOrbitImage TwistTag.D4 1 a, ∀ γ ∈ fixedOrbitImage TwistTag.D4 w b,
        β ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ γ) = 0 := by
      intro β hβ γ hγ
      rw [hE] at hβ
      obtain ⟨i, hi, rfl⟩ := hβ
      rw [hOset] at hγ
      exact horth i hi γ hγ
    rintro β (hβ | hβ) γ (hγ | hγ)
    · exact base β hβ γ hγ
    · exact orth_of_neg_right (base β hβ (-γ) (Set.mem_neg.1 hγ))
    · exact orth_of_neg_left (base (-β) (Set.mem_neg.1 hβ) γ hγ)
    · exact orth_of_neg_left (orth_of_neg_right (base (-β) (Set.mem_neg.1 hβ) (-γ)
        (Set.mem_neg.1 hγ)))
  exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (L := K) (Or.inl rfl) hS₁ hS₂ horth'
    y hy' z hz'

end PairMain

section Big


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem three_dvd_card_SL2 {f c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ c) : 3 ∣ Nat.card (SL2 F) := by
  rw [← CFSG.Open.StatedAPI.card_statedSL 2 F, CFSG.Open.StatedAPI.card_statedSL_two F, hF]
  refine Dvd.dvd.mul_left ?_ _
  have h3m : ¬ 3 ∣ (2 ^ f) ^ c := fun h =>
    absurd (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h))
      (by decide)
  have hm : ((2 ^ f) ^ c) % 3 = 1 ∨ ((2 ^ f) ^ c) % 3 = 2 := by omega
  have hsq : (((2 ^ f) ^ c) ^ 2) % 3 = 1 := by
    rcases hm with h | h <;> simp [Nat.pow_mod, h]
  omega

theorem exists_big_exp_three_subgroup (hσ3 : σ ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {y : ModGL TwistTag.D4.tag K} (hyX : y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hy3 : orderOf y = 3) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {a : Fin TwistTag.D4.foldedTag.rank}
    (hya : g * y * g⁻¹ ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range) :
    ∃ E : Subgroup (ModGL TwistTag.D4.tag K), E ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      (∀ e ∈ E, e * y = y * e) ∧ (∀ e ∈ E, e ^ 3 = 1) ∧ 3 < Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, b, hw, hcomm⟩ := exists_commuting_rank_one (K := K) σ.toRingHom a
  set R' := orbitConjRankOneHom TwistTag.D4 K σ.toRingHom w b with hR'
  have hinj : Function.Injective R' :=
    orbitConjRankOneHom_injective (orbitRankOneHom_injective_D4 hσ3 b)
  have hFfin : Finite (orbitField TwistTag.D4 K σ.toRingHom b) := Subtype.finite
  have hFcard := card_orbitField_D4_orientation Nat.prime_two hf hK (r := 1) (Or.inl rfl)
    (σ := σ.toRingHom) (by simpa using hσ) b
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card'
    (G := SL2 (orbitField TwistTag.D4 K σ.toRingHom b)) 3 (three_dvd_card_SL2 hFcard)
  set z : ModGL TwistTag.D4.tag K := R' A with hz
  have hzo : orderOf z = 3 := by rw [hz, orderOf_injective R' hinj, hA]
  have hzX : z ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    orbitConjRankOneHom_mem_graphFixedRootGroup hw b A
  set y' : ModGL TwistTag.D4.tag K := g * y * g⁻¹ with hy'
  have hy'o : orderOf y' = 3 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    rw [hy3] at this
    simpa [MulAut.conj_apply] using this
  have hy'X : y' ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    mul_mem (mul_mem hg hyX) (inv_mem hg)
  have hzc : ∀ m ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range, m * z = z * m :=
    fun m hm => hcomm m hm z ⟨A, rfl⟩
  have hyz : y' * z = z * y' := hzc y' hya
  have hzn : z ∉ Subgroup.zpowers y' := by
    intro hzy
    have hzM : z ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range :=
      (Subgroup.zpowers_le.2 hya) hzy
    have hzC : z ∈ Subgroup.centralizer
        ((orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range : Set (ModGL TwistTag.D4.tag K)) :=
      Subgroup.mem_centralizer_iff.2 fun m hm => hzc m hm
    have h1 := eq_one_of_mem_range_of_mem_centralizer σ hσ3 a hzM hzC
    rw [h1, orderOf_one] at hzo
    omega
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set E' : Subgroup (ModGL TwistTag.D4.tag K) := Subgroup.zpowers y' ⊔ Subgroup.zpowers z with hE'
  have hyz' : Commute y' z := hyz
  have hcz : ∀ u ∈ Subgroup.zpowers y', ∀ v ∈ Subgroup.zpowers z, u * v = v * u := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hyz'.zpow_zpow i j).eq
  have hle : Subgroup.zpowers y' ≤
      Subgroup.centralizer (Subgroup.zpowers z : Set (ModGL TwistTag.D4.tag K)) :=
    fun u hu => Subgroup.mem_centralizer_iff.2 fun v hv => (hcz u hu v hv).symm
  have hmulset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y')
    (Subgroup.zpowers z) (hle.trans (Subgroup.centralizer_le_normalizer _))
  have hy'3 : y' ^ 3 = 1 := by rw [← hy'o]; exact pow_orderOf_eq_one y'
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hpow3 : ∀ {a : ModGL TwistTag.D4.tag K}, a ^ 3 = 1 → ∀ u ∈ Subgroup.zpowers a, u ^ 3 = 1 := by
    rintro a ha _ ⟨k, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast,
      ha, _root_.one_zpow]
  have hE'exp : ∀ e ∈ E', e ^ 3 = 1 := by
    intro e he
    have he' : e ∈ ((Subgroup.zpowers y' : Set (ModGL TwistTag.D4.tag K)) *
        (Subgroup.zpowers z : Set (ModGL TwistTag.D4.tag K))) := by
      rw [← hmulset]
      exact he
    obtain ⟨u, hu, v, hv, rfl⟩ := he'
    have hc : Commute u v := hcz u hu v hv
    rw [hc.mul_pow, hpow3 hy'3 u hu, hpow3 hz3 v hv, one_mul]
  have hE'X : E' ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    sup_le ((Subgroup.zpowers_le).2 hy'X) ((Subgroup.zpowers_le).2 hzX)
  have hE'y : ∀ e ∈ E', e * y' = y' * e := by
    have h1 : E' ≤ Subgroup.centralizer ({y'} : Set (ModGL TwistTag.D4.tag K)) := by
      refine sup_le ?_ ?_
      · refine (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
      · exact (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hyz'.eq.symm)
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 he)
  have hcard : 3 < Nat.card E' := by
    have hcardy : Nat.card (Subgroup.zpowers y') = 3 := by rw [Nat.card_zpowers, hy'o]
    by_contra hle3
    push Not at hle3
    have hleE : Subgroup.zpowers y' ≤ E' := le_sup_left
    have hge : Nat.card E' ≤ Nat.card (Subgroup.zpowers y') := by rw [hcardy]; exact hle3
    have heq := Subgroup.eq_of_le_of_card_ge hleE hge
    exact hzn (heq ▸ (le_sup_right : Subgroup.zpowers z ≤ E') (Subgroup.mem_zpowers z))
  refine ⟨E'.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    have := mul_mem (mul_mem (inv_mem hg) (hE'X he)) (inv_mem (inv_mem hg))
    simpa [MulAut.conj_apply] using this
  · rintro _ ⟨e, he, rfl⟩
    have h := hE'y e he
    have : g⁻¹ * e * g⁻¹⁻¹ * y = y * (g⁻¹ * e * g⁻¹⁻¹) := by
      have e1 : g * y * g⁻¹ = y' := rfl
      calc g⁻¹ * e * g⁻¹⁻¹ * y = g⁻¹ * (e * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * e) * g := by rw [e1, h]
        _ = y * (g⁻¹ * e * g⁻¹⁻¹) := by group
    simpa [MulAut.conj_apply] using this
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE'exp e he, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hcard

end Big

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem oddPCoreInClosure_triality_three_odd_aux {f : ℕ} (hf : 1 ≤ f) (hfodd : Odd f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (X : Subgroup (ModGL TwistTag.D4.tag K))
    (hXd : X = graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {x : ↥X} (hx : orderOf x = 3)
    (C : Subgroup ↥X) (hC : ∀ c : ↥X, c ∈ C ↔ c * x = x * c) :
    OddPCoreInClosure 3 ↥C := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite X := Subtype.finite
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have : Fintype K := Fintype.ofFinite K
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
      show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have h3 : ¬ 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    obtain ⟨k, rfl⟩ := hfodd
    have h2 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h8 : ((2 ^ (2 * k + 1)) ^ 3) % 3 = 2 := by
      rw [Nat.pow_mod, h2]
    omega
  haveI : Finite C := Subtype.finite
  intro N hN hle hcop
  by_contra hodd
  have hxC : x ∈ C := (hC x).2 rfl
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 C, (⟨x, hxC⟩ : C) ∈ (P : Subgroup C) := by
    have hpg : IsPGroup 3 (Subgroup.zpowers (⟨x, hxC⟩ : C)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
      exact hx
    obtain ⟨P, hP⟩ := hpg.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers _)⟩
  obtain ⟨R, hRne, hR2, hPR⟩ := exists_normalized_two_group Nat.prime_three C N hodd hcop P
  set φ : C →* ModGL TwistTag.D4.tag K := X.subtype.comp C.subtype with hφdef
  have hφ : Function.Injective φ :=
    (Subgroup.subtype_injective X).comp (Subgroup.subtype_injective C)
  set A : Subgroup (ModGL TwistTag.D4.tag K) := (P : Subgroup C).map φ with hA
  set R' : Subgroup (ModGL TwistTag.D4.tag K) := R.map X.subtype with hR'
  have hAX : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← hXd]
    rintro _ ⟨c, -, rfl⟩
    exact c.1.2
  have hRX : R' ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← hXd]
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have hR2' : IsPGroup 2 R' := hR2.map X.subtype
  have hR'ne : R' ≠ ⊥ := fun h0 =>
    hRne ((Subgroup.map_eq_bot_iff_of_injective R (Subgroup.subtype_injective X)).1 h0)
  have hAR : A ≤ Subgroup.normalizer (R' : Set (ModGL TwistTag.D4.tag K)) := by
    have : A = ((P : Subgroup C).map C.subtype).map X.subtype := by
      rw [hA, Subgroup.map_map]
    rw [this]
    exact (Subgroup.map_mono hPR).trans (Subgroup.le_normalizer_map X.subtype)
  have hxA : φ ⟨x, hxC⟩ ∈ A := ⟨_, hxP, rfl⟩
  have hyo : orderOf (φ ⟨x, hxC⟩) = 3 := by
    rw [orderOf_injective φ hφ, ← Subgroup.orderOf_coe]
    exact hx
  have hy3 : (φ ⟨x, hxC⟩) ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one _
  have hyX : φ ⟨x, hxC⟩ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← hXd]
    exact x.2
  obtain ⟨g, hg, a, hya⟩ := exists_conj_mem_range_of_normalizes σ hσ3 h3 hAX hRX hR2' hR'ne hAR
    hxA hy3
  obtain ⟨E, hEX, hEc, hE3, hEcard⟩ := exists_big_exp_three_subgroup σ hσ3 hf hK hσ
    (y := φ ⟨x, hxC⟩) hyX hyo hg hya
  have hEX' : E ≤ X := by rw [hXd]; exact hEX
  have hEφ : E ≤ φ.range := fun e he =>
    ⟨⟨⟨e, hEX' he⟩, (hC _).2 (Subtype.ext (hEc e he))⟩, rfl⟩
  exact false_of_sylow_subgroup Nat.prime_three P φ hφ E hEφ hE3 (m := 3)
    (fun E' hE'A hE'3 => card_le_three_of_normalizes σ hσ3 h3 hAX hRX hR2' hR'ne hAR hE'A hE'3)
    hEcard

theorem oddPCoreInClosure_triality_three_odd {f : ℕ} (hf : 1 ≤ f) (hfodd : Odd f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hx : orderOf x = 3) :
    OddPCoreInClosure 3
      ↥(Subgroup.centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :=
  oddPCoreInClosure_triality_three_odd_aux σ hf hfodd hK hσ _ rfl hx _ fun c =>
    Subgroup.mem_centralizer_singleton_iff

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
