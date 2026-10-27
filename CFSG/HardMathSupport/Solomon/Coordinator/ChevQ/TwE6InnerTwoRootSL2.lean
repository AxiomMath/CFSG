module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieConj
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieAux
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieSL2
public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootTransport
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieHeis

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

section Generic

private theorem mem_map_conj_iff_aux {Γ : Type*} [Group Γ] (H : Subgroup Γ) (g u : Γ) :
    u ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * u * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * u * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem map_conj_mul_aux {Γ : Type*} [Group Γ] (H : Subgroup Γ) (a b : Γ) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem exists_hyperplane_le_aux {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime)
    {D E : Subgroup Y} (h1 : D.relIndex E ≤ p) (hE : Nat.card E = p ^ 3) :
    ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p ∧ F ≤ D := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : D.relIndex E ∣ p ^ 3 := hE ▸ Subgroup.relIndex_dvd_card D E
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hi1 : i ≤ 1 := by
    by_contra h
    have h3 : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
    have h4 : p < p ^ 2 := by
      have := hp.two_le
      nlinarith
    omega
  interval_cases i
  · rw [pow_zero] at hi'
    obtain ⟨F, hFE, hF⟩ := CFSG.LieType.SeitzGeneration.exists_hyperplane_of_card hE
    exact ⟨F, hFE, hF, hFE.trans (Subgroup.relIndex_eq_one.1 hi')⟩
  · rw [pow_one] at hi'
    exact ⟨D ⊓ E, inf_le_right, by rw [Subgroup.inf_relIndex_right, hi'], inf_le_left⟩

end Generic

section RootSL2

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.SeitzGeneration.ExcWideThree


local notation "θ₀" => CFSG.LieType.Chevalley.e6HighestRoot

theorem exists_longRootPair_of_negDatum (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hvγ : v • permLattice TwistTag.E6.perm γ = -γ) :
    ∃ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm ∧
      ∀ u : twistedE6RootGroup K σ, u ∈ twE6LongRootSL2 X Xm ↔
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
          (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ}).map
            (MulAut.conj g0).toMonoidHom := by
  classical
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  haveI : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqf]
  have hFrc : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by rw [hFr, hqf]
  have hFrEq : iterateFrobenius (AlgebraicClosure K) (ringChar K) f = Fr :=
    RingHom.ext fun c => by rw [iterateFrobenius_def, hFrc]
  have hg0' : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) (ringChar K) f) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v := by
    rw [hFrEq]
    exact hg0
  obtain ⟨h, hhA, hhF, hconj⟩ :=
    exists_fixed_conj_rootSL2 (L := AlgebraicClosure K) (ringChar K) f hf1 hr hg0C hg0' hγ hvγ
  rw [hFrEq] at hhF
  obtain ⟨u₃, hu₃, t₃, ht₃, hdec⟩ := twE6_fixed_decomp hpr hf1 K hK' σ hσ' Fr hFrc hhA hhF
  have hSL2 : ∀ u : twistedE6RootGroup K σ,
      u ∈ twE6LongRootSL2 (TwE6LongRoot.stdX σ) (TwE6LongRoot.stdXm σ) ↔
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
          rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ₀, -θ₀} :=
    fun u => mem_twE6LongRootSL2_std_iff hpr hf1 hr K hK' σ hσ' u
  have hrootsθ : ∀ α ∈ ({θ₀, -θ₀} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    · exact isRoot_e6HighestRoot
    · exact IsRoot.neg isRoot_e6HighestRoot
  obtain ⟨U₃, hU₃⟩ : ∃ U₃ : twistedE6RootGroup K σ, U₃ = ⟨u₃, hu₃⟩ := ⟨_, rfl⟩
  have hU₃c : ((U₃ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = u₃ := by rw [hU₃]
  have hSeq : twE6LongRootSL2 ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)
      ((TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom) =
      (twE6LongRootSL2 (TwE6LongRoot.stdX σ) (TwE6LongRoot.stdXm σ)).map
        (MulAut.conj U₃).toMonoidHom :=
    TwE6LongRoot.twE6LongRootSL2_map (MulAut.conj U₃) _ _
  have hSbar : (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ₀, -θ₀}).map
      (MulAut.conj (baseChangeGL (algebraMap K (AlgebraicClosure K)) u₃)).toMonoidHom =
      (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ}).map
        (MulAut.conj g0).toMonoidHom := by
    rw [← hconj, hdec, map_conj_mul_aux,
      ExcWideThree.map_conj_eq_of_mem_normalizer
        (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hrootsθ ht₃)]
  refine ⟨(TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom,
    (TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom, ⟨U₃, rfl, rfl⟩, fun u => ?_⟩
  rw [hSeq, mem_map_conj_iff_aux, hSL2, ← hSbar, mem_map_conj_iff_aux]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hU₃c]

theorem exists_hyperplane_commute_of_rootSpan {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : CFSG.Open.IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) :
    ∃ F : Subgroup (twistedE6RootGroup K σ), F ≤ E₀ ∧ F.relIndex E₀ = 3 ∧
      ∀ f ∈ F, ∀ u : twistedE6RootGroup K σ,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
          (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ}).map
            (MulAut.conj g0).toMonoidHom →
        f * u = u * f := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  let δ : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL ι).comp (twistedE6RootGroup K σ).subtype)
  have hδ : ∀ x : twistedE6RootGroup K σ,
      δ x = g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * g0 := fun x => by
    simp [δ, MulAut.conj_apply]
  have hδT : ∀ x ∈ E₀, δ x ∈ torusGroup TwistTag.E6.tag L := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hT x hx)
    have hyx' : g0 * y * g0⁻¹ = baseChangeGL ι (x : ModGL TwistTag.E6.tag K) := by
      simpa [MulAut.conj_apply] using hyx
    have hxy : δ x = y := by
      rw [hδ, ← hyx']
      group
    rw [hxy]
    exact ((mem_twistedTorusOf).1 hy).1
  have hinj : Function.Injective (rootDiagUnitHom TwistTag.E6.tag L) :=
    fun _ _ h => CFSG.LieType.Chevalley.rootDiagUnit_injective h
  let e := MonoidHom.ofInjective hinj
  have hrange : ∀ x ∈ E₀, δ x ∈ (rootDiagUnitHom TwistTag.E6.tag L).range := by
    intro x hx
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hδT x hx)
    exact ⟨l, hl.symm⟩
  let δE : E₀ →* (rootDiagUnitHom TwistTag.E6.tag L).range :=
    (δ.comp E₀.subtype).codRestrict _ fun x => hrange x x.2
  have hrd : ∀ x : E₀, rootDiagUnit TwistTag.E6.tag (e.symm (δE x)) = δ x := by
    intro x
    have h1 := congrArg Subtype.val (e.apply_symm_apply (δE x))
    rw [MonoidHom.ofInjective_apply] at h1
    exact h1
  let χ : E₀ →* Lˣ :=
    { toFun := fun x => rootChar (e.symm (δE x)) γ
      map_one' := by simp [rootChar]
      map_mul' := fun x y => by
        simp only [map_mul, rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib] }
  have hχ : ∀ x : E₀, χ x = rootChar (e.symm (δE x)) γ := fun _ => rfl
  have hcomm : ∀ x : E₀, χ x = 1 → ∀ u : twistedE6RootGroup K σ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ}).map
          (MulAut.conj g0).toMonoidHom →
      (x : twistedE6RootGroup K σ) * u = u * (x : twistedE6RootGroup K σ) := by
    intro x hx u hu
    obtain ⟨a, ha⟩ : ∃ a, a = e.symm (δE x) := ⟨_, rfl⟩
    have hχa : rootChar a γ = 1 := by rw [ha, ← hχ, hx]
    have hχa' : rootChar a (-γ) = 1 := by
      have h0 := rootChar_sub a 0 γ
      rw [zero_sub, rootChar_zero, hχa] at h0
      simpa using h0
    obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.1 hu
    have hsc : rootDiagUnit TwistTag.E6.tag a * s = s * rootDiagUnit TwistTag.E6.tag a := by
      have hle := rootSpan_le_centralizer_rootDiagUnit (L := L) a
        (S := {γ, -γ}) (by
          intro α hα
          rcases hα with rfl | rfl
          · exact ⟨hγ, hχa⟩
          · exact ⟨IsRoot.neg hγ, hχa'⟩)
      exact (Subgroup.mem_centralizer_iff.1 (hle hs)) _ rfl
    have hx' : baseChangeGL ι ((x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ := by
      rw [ha, hrd x]
      change baseChangeGL ι ((x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        g0 * δ (x : twistedE6RootGroup K σ) * g0⁻¹
      rw [hδ]
      group
    have hu' : baseChangeGL ι (u : ModGL TwistTag.E6.tag K) = g0 * s * g0⁻¹ := by
      simpa [MulAut.conj_apply] using hsu.symm
    apply Subtype.ext
    apply baseChangeGL_injective ι
    simp only [Subgroup.coe_mul, map_mul]
    rw [hx', hu']
    calc g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ * (g0 * s * g0⁻¹)
        = g0 * (rootDiagUnit TwistTag.E6.tag a * s) * g0⁻¹ := by group
      _ = g0 * (s * rootDiagUnit TwistTag.E6.tag a) * g0⁻¹ := by rw [hsc]
      _ = g0 * s * g0⁻¹ * (g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹) := by group
  have hχ3 : ∀ x : E₀, χ x ^ 3 = 1 := by
    intro x
    rw [← map_pow]
    have h3 : x ^ 3 = 1 := Subtype.ext (by simpa using hE₀.2 _ x.2)
    rw [h3, map_one]
  have hrng : χ.range ≤ rootsOfUnity 3 L := by
    rintro _ ⟨x, rfl⟩
    exact (mem_rootsOfUnity 3 _).2 (hχ3 x)
  have hidx : χ.ker.index ≤ 3 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hrng).trans (card_rootsOfUnity (R := L) (k := 3))
  have hD : (χ.ker.map E₀.subtype).relIndex E₀ = χ.ker.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E₀.subtype_injective]
  obtain ⟨F, hFE, hFi, hFD⟩ :=
    exists_hyperplane_le_aux Nat.prime_three (hD ▸ hidx) hcard
  exact ⟨F, hFE, hFi, fun f hf u hu => by
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hFD hf)
    exact hcomm x hx u hu⟩

theorem mem_hyperClosure_of_rootSpan {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : CFSG.Open.IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    {u : twistedE6RootGroup K σ}
    (hu : baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
      (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ}).map
        (MulAut.conj g0).toMonoidHom) :
    u ∈ hyperClosure 3 ⊤ E₀ := by
  obtain ⟨F, hFE, hFi, hcomm⟩ := exists_hyperplane_commute_of_rootSpan hE₀ hcard hT hγ
  exact Subgroup.subset_closure ⟨Subgroup.mem_top _, F, hFE, hFi, fun f hf => hcomm f hf u hu⟩

theorem longRootSL2_le_hyperClosure {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : CFSG.Open.IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    {X Xm : Subgroup (twistedE6RootGroup K σ)}
    (hS : ∀ u : twistedE6RootGroup K σ, u ∈ twE6LongRootSL2 X Xm ↔
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ}).map
          (MulAut.conj g0).toMonoidHom) :
    twE6LongRootSL2 X Xm ≤ hyperClosure 3 ⊤ E₀ :=
  fun u hu => mem_hyperClosure_of_rootSpan hE₀ hcard hT hγ ((hS u).1 hu)

end RootSL2

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
