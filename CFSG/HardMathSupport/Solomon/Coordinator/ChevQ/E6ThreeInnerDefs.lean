module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoCalc

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.AGLEmbedding TauCeti

set_option linter.unusedSectionVars false

section Statements


@[expose] def E6InnerCubeGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ThreeScope LieTypeIndex.E6 K →
    ∀ E₀ : Subgroup (adjointGroup .E6 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → HyperGen 3 ⊤ E₀

@[expose] def E6InnerCubeGenAt (ε : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε → ThreeScope LieTypeIndex.E6 K →
    ∀ E₀ : Subgroup (adjointGroup .E6 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → HyperGen 3 ⊤ E₀

@[expose] def TwThreeScope (K : Type) [Field K] (σ : K ≃+* K) : Prop :=
  ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), Nat.card K = q.card ^ 2 ∧
    (∀ c, σ c = c ^ q.card) ∧ SeitzGoodIndex 3 (LieTypeIndex.twistedE6 q) ∧
    ¬ P1ThreeLieList 3 ⟨LieTypeIndex.twistedE6 q, hv⟩

@[expose] def TwE6InnerCubeGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), ¬ 3 ∣ Nat.card K → TwThreeScope K σ →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → HyperGen 3 ⊤ E₀

@[expose] def TwE6InnerCubeGenAt (ε : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = ε → TwThreeScope K σ →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → HyperGen 3 ⊤ E₀

end Statements

section Facts

theorem ringChar_eq_of_card_eq_pow {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) (h : Nat.card K = p ^ n) : ringChar K = p := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ p ^ n := by
    rw [← h, Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self _ m.ne_zero
  exact (Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow hdvd)

theorem ringChar_ne_three_of_not_dvd {K : Type} [Field K] [Finite K]
    (h : ¬ 3 ∣ Nat.card K) : ringChar K ≠ 3 := by
  classical
  intro h3
  have : Fintype K := Fintype.ofFinite K
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  apply h
  rw [Nat.card_eq_fintype_card, hn, h3]
  exact dvd_pow_self 3 n.ne_zero

theorem isTwoPow_of_card_eq' {q : PrimePower} {k : ℕ} (h : q.card = 2 ^ k) : IsTwoPow q k := by
  have h' : q.p ^ q.exponent = 2 ^ k := by rw [← PrimePower.card_def, h]
  have hp2 : q.p = 2 := by
    have hd : q.p ∣ 2 ^ k := h' ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hd)
  refine ⟨hp2, ?_⟩
  rw [hp2] at h'
  exact Nat.pow_right_injective le_rfl h'

theorem card_ne_four_of_seitzGoodIndex_E6 {q : PrimePower}
    (h : SeitzGoodIndex 3 (LieTypeIndex.E6 q)) : q.card ≠ 4 := by
  rcases h with h | h
  · intro hq
    refine h (Or.inr ⟨rfl, Or.inr (Or.inl ?_)⟩)
    show IsTwoPow q 1 ∨ IsTwoPow q 2 ∨ IsTwoPow q 3
    exact Or.inr (Or.inl (isTwoPow_of_card_eq' (by rw [hq]; norm_num)))
  · rcases h with h | h | h <;> simp [IsF4EightIndex, IsD4FourIndex, FourIndex] at h

theorem conj_injective_of_center_eq_bot' {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun φ : MulAut G => φ g) (MonoidHom.mem_ker.1 hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem hyperGen_top_of_seitzHyperGamma_conj {G : Type*} [Group G] {p : ℕ} {E₀ : Subgroup G}
    (h : seitzHyperGamma p (E₀.map (MulAut.conj : G →* MulAut G)) = ⊤) : HyperGen p ⊤ E₀ := by
  have hle : seitzHyperGamma p (E₀.map (MulAut.conj : G →* MulAut G)) ≤
      Subgroup.closure {k : G | k ∈ (⊤ : Subgroup G) ∧ ∃ F : Subgroup G, F ≤ E₀ ∧
        F.relIndex E₀ = p ∧ ∀ f ∈ F, f * k = k * f} := by
    refine iSup₂_le fun F' hF' k₀ hk₀ => ?_
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top _, E₀ ⊓ F'.comap MulAut.conj, inf_le_left, ?_, fun f hf => ?_⟩
    · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
      exact hF'.2
    · have h1 := hk₀ (MulAut.conj f) hf.2
      rw [MulAut.conj_apply] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
  intro k _
  exact hle (h ▸ Subgroup.mem_top k)

theorem normalizesRGroup_of_e6NormalizesR_conj
    {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.E6 K)}
    (h : E6NormalizesR K (E₀.map (MulAut.conj : adjointGroup Tag.E6 K →* MulAut _))) :
    NormalizesRGroup (ringChar K) E₀ := by
  obtain ⟨R, hR1, hRp, hR⟩ := h
  exact ⟨R, hR1, hRp, fun x hx => hR _ ⟨x, hx, rfl⟩⟩

end Facts

section Bridge


theorem seitzGoodInnerExcThreeE6_of_cubes (h : E6InnerCubeGen) : SeitzGoodInnerExcThreeE6 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist E₀ hE₀ hcard ⟨⟨q, hq⟩, hN, hgood, rfl⟩
  simp only at hq
  subst hq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hrc : ringChar K = q.p := ringChar.eq K q.p
  have hpq : (3 : ℕ) ≠ q.p := fun h3 => hpd (h3.trans (LieTypeIndex.characteristic_E6 q).symm)
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    rw [hKq, PrimePower.card_def] at h3
    exact hpq ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h3))
  refine SeitzExcOpenCubes.hyperGen_of_mulEquiv e ?_
  refine h K hK3 ⟨q, hv, hKq, hgood, hlist⟩ _
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hcard]) fun hN' => hN ?_
  have h1 := SeitzExcOpenRest2.normalizesRGroup_of_map_mulEquiv e hN'
  rw [hrc, ← LieTypeIndex.characteristic_E6 q] at h1
  exact h1

theorem seitzGoodInnerExcThreeTwE6_of_cubes (h : TwE6InnerCubeGen) :
    SeitzGoodInnerExcThreeTwE6 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist E₀ hE₀ hcard ⟨⟨q, hq⟩, hN, hgood, rfl⟩
  simp only at hq
  subst hq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hK' : Nat.card K = q.card ^ 2 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, PrimePower.card_def]
  have hrc : ringChar K = q.p := by
    refine ringChar_eq_of_card_eq_pow q.prime_p (n := q.exponent * 2) ?_ ?_
    · exact (Nat.mul_pos q.exponent_pos two_pos).ne'
    · rw [hK, ← pow_mul]
  have hpq : (3 : ℕ) ≠ q.p := fun h3 =>
    hpd (h3.trans (LieTypeIndex.characteristic_twistedE6 q).symm)
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    rw [hK, ← pow_mul] at h3
    exact hpq ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h3))
  refine SeitzExcOpenCubes.hyperGen_of_mulEquiv e ?_
  refine h K σ hK3 ⟨q, hv, hK', hσ', hgood, hlist⟩ _
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hcard]) fun hN' => hN ?_
  have h1 := SeitzExcOpenRest2.normalizesRGroup_of_map_mulEquiv e hN'
  rw [hrc, ← LieTypeIndex.characteristic_twistedE6 q] at h1
  exact h1

theorem e6InnerCubeGen_of_at (h1 : E6InnerCubeGenAt 1) (h2 : E6InnerCubeGenAt 2) :
    E6InnerCubeGen := by
  intro K _ _ hK3 hs E₀ hE₀ hc hN
  have hr : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
  rcases hr with hr | hr
  · exact h1 K hr hs E₀ hE₀ hc hN
  · exact h2 K hr hs E₀ hE₀ hc hN

theorem twE6InnerCubeGen_of_at (h1 : TwE6InnerCubeGenAt 1) (h2 : TwE6InnerCubeGenAt 2) :
    TwE6InnerCubeGen := by
  intro K _ _ σ hK3 hs E₀ hE₀ hc hN
  obtain ⟨q, hv, hKq, hσ, hg, hl⟩ := hs
  have hq3 : ¬ 3 ∣ q.card := fun h => hK3 (by rw [hKq]; exact dvd_pow h two_ne_zero)
  have hr : q.card % 3 = 1 ∨ q.card % 3 = 2 := by omega
  rcases hr with hr | hr
  · exact h1 K σ q.card hKq hσ hr ⟨q, hv, hKq, hσ, hg, hl⟩ E₀ hE₀ hc hN
  · exact h2 K σ q.card hKq hσ hr ⟨q, hv, hKq, hσ, hg, hl⟩ E₀ hE₀ hc hN

end Bridge

section One


@[expose] def E6InnerOneConjGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) → ¬ E6NormalizesR K E →
      seitzHyperGamma 3 E = ⊤

theorem e6InnerCubeGenAt_one_of_conjGen (h : E6InnerOneConjGen) : E6InnerCubeGenAt 1 := by
  intro K _ _ hK hs E₀ hE₀ hc hN
  obtain ⟨q, -, hKq, hgood, -⟩ := hs
  have hK4 : Nat.card K ≠ 4 := by
    rw [hKq]
    exact card_ne_four_of_seitzGoodIndex_E6 hgood
  have hK3 : ringChar K ≠ 3 := ringChar_ne_three_of_not_dvd (by omega)
  have hinj := conj_injective_of_center_eq_bot' (G := adjointGroup Tag.E6 K)
    center_adjointGroup_eq_bot
  refine hyperGen_top_of_seitzHyperGamma_conj
    (h K hK3 (by omega) hK4 _ (hE₀.map _) ?_ ?_ ?_)
  · rw [Subgroup.card_map_of_injective hinj, hc]
  · rintro _ ⟨x, -, rfl⟩
    exact CFSG.Fischer.mem_innerAut.2 ⟨x, rfl⟩
  · exact fun hR => hN (normalizesRGroup_of_e6NormalizesR_conj hR)

end One

section OnePieces


@[expose] def FixesForm (v : WeylGroup Tag.E6) (l : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ β : Fin Tag.E6.rank → ℤ, ∑ i, l i * (v • β) i = ∑ i, l i * β i

@[expose] def E6InnerSylowMono : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ e6Inndiag K → IsPGroup 3 E →
      ∃ φ ∈ e6Inndiag K, ∀ X ∈ E.map (MulAut.congr φ).toMonoidHom, ∃ v, BmMono X v

@[expose] def E6InnerSylowMonoLine : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 →
    ∀ ω : Kˣ, ω ^ 3 = 1 → ω ≠ 1 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ e6Inndiag K → IsPGroup 3 E →
      (∀ X ∈ E, Commute X (MulAut.conj (e6LineElt ω))) →
      ∃ φ ∈ e6Inndiag K, Commute φ (MulAut.conj (e6LineElt ω)) ∧
        ∀ X ∈ E.map (MulAut.congr φ).toMonoidHom, ∃ v, BmMono X v

@[expose] def E6MonoFixNormalizes : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (E : Subgroup (MulAut (adjointGroup Tag.E6 K)))
    (l : Fin Tag.E6.rank → ℤ), l ≠ 0 → (∀ X ∈ E, ∃ v, BmMono X v ∧ FixesForm v l) →
      E6NormalizesR K E

@[expose] def E6WeylEllipticOfNoFixed : Prop :=
  ∀ Ω : Subgroup (WeylGroup Tag.E6), (∀ w ∈ Ω, w ^ 3 = 1) → (∀ w ∈ Ω, ∀ u ∈ Ω, w * u = u * w) →
    (∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ∃ w ∈ Ω, ¬ FixesForm w l) →
    ∃ w ∈ Ω, ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ¬ FixesForm w l

@[expose] def E6MonoEllipticFix24 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 →
    ∀ s : adjointGroup Tag.E6 K, s ^ 3 = 1 → ∀ v : WeylGroup Tag.E6, BmMono (MulAut.conj s) v →
      (∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ¬ FixesForm v l) →
      Module.finrank K (LinearMap.ker
        (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24

@[expose] def E6InnerAll24Plane : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) → ¬ E6NormalizesR K E →
      ∃ P ≤ E, Nat.card P = 3 ^ 2 ∧ ∀ s : adjointGroup Tag.E6 K, MulAut.conj s ∈ P → s ≠ 1 →
        Module.finrank K (LinearMap.ker
          (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24

end OnePieces

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
