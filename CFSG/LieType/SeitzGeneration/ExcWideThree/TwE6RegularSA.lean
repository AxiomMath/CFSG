module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularSAData
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularInnerLine
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLongRoot
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularNoR

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg

section Pure

theorem triPairing_smul_add_smul {τ : Tag} (c₁ c₂ : ZMod 3) (b₁ b₂ : Fin τ.rank → ZMod 3)
    (v : Fin τ.rank → ℤ) :
    triPairing (c₁ • b₁ + c₂ • b₂) v = c₁ * triPairing b₁ v + c₂ * triPairing b₂ v := by
  simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem pow_mul_pow_ne_one {G : Type*} [Group G] {x₁ x₂ : G} (hx₁ : x₁ ^ 3 = 1) (hx₁1 : x₁ ≠ 1)
    (hx₂ : x₂ ^ 3 = 1) (hx₂n : x₂ ∉ Subgroup.zpowers x₁) {m₁ m₂ : ℕ} (h₁ : m₁ < 3) (h₂ : m₂ < 3)
    (hm : ¬ (m₁ = 0 ∧ m₂ = 0)) : x₁ ^ m₁ * x₂ ^ m₂ ≠ 1 := by
  intro h
  have hz1 : ∀ n : ℕ, x₁ ^ n ∈ Subgroup.zpowers x₁ := fun n => by
    rw [← zpow_natCast]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x₁) _
  interval_cases m₁ <;> interval_cases m₂
  · exact hm ⟨rfl, rfl⟩
  ·
    apply hx₂n
    have : x₂ = 1 := by simpa using h
    rw [this]
    exact Subgroup.one_mem _
  · apply hx₂n
    have h3 : x₂ ^ 2 = 1 := by simpa using h
    have : x₂ = 1 := by
      calc x₂ = x₂ ^ 3 * (x₂ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx₂, h3]; simp
    rw [this]
    exact Subgroup.one_mem _
  · apply hx₁1
    simpa using h
  · apply hx₂n
    have : x₂ = (x₁ ^ 1)⁻¹ := by
      have := eq_inv_of_mul_eq_one_right h
      simpa using this
    rw [this]
    exact Subgroup.inv_mem _ (hz1 1)
  · apply hx₂n
    have h2 : x₂ ^ 2 = (x₁ ^ 1)⁻¹ := eq_inv_of_mul_eq_one_right h
    have : x₂ = (x₂ ^ 2) ^ 2 := by
      calc x₂ = x₂ ^ 3 * x₂ := by rw [hx₂, one_mul]
        _ = (x₂ ^ 2) ^ 2 := by group
    rw [this, h2]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (hz1 1)) 2
  · apply hx₁1
    have h3 : x₁ ^ 2 = 1 := by simpa using h
    calc x₁ = x₁ ^ 3 * (x₁ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx₁, h3]; simp
  · apply hx₂n
    have : x₂ = (x₁ ^ 2)⁻¹ := by
      have := eq_inv_of_mul_eq_one_right h
      simpa using this
    rw [this]
    exact Subgroup.inv_mem _ (hz1 2)
  · apply hx₂n
    have h2 : x₂ ^ 2 = (x₁ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
    have : x₂ = (x₂ ^ 2) ^ 2 := by
      calc x₂ = x₂ ^ 3 * x₂ := by rw [hx₂, one_mul]
        _ = (x₂ ^ 2) ^ 2 := by group
    rw [this, h2]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (hz1 2)) 2

end Pure

section SA


@[expose] def TwE6LiftBridge : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 →
    ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K), (∀ c, Fr c = c ^ q) →
    ∀ (v w' : WeylGroup TwistTag.E6.tag),
      (∀ y, w' • y = -permLattice TwistTag.E6.perm (v⁻¹ • y)) →
    ∀ (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      ∀ (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ), (∀ i, a i ^ 3 = 1) →
        ∏ i, a i ^ e6DiagCoeff i = 1 → w' ∈ rootCharStabilizer a →
        rootChar a (e6Shift w') = 1 →
        ∀ y : ModGL TwistTag.E6.tag K,
          baseChangeGL (algebraMap K (AlgebraicClosure K)) y =
            g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ → y ∈ twistedE6RootGroup K σ

@[expose] def TwE6InnerLineLie : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
    ∀ D : TwLangData K σ q (twPlanePre K σ E),
    ∀ e ∈ E, e ≠ 1 →
    ∀ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      (∃ g : ↥(twistedE6InndiagGL K σ), twistedE6InndiagConj K σ g = e ∧
        rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K))
            (D.c * (g : ModGL TwistTag.E6.tag K) * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0) →
    ∀ β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β₁ → IsRoot TwistTag.E6.tag β₂ →
      IsRoot TwistTag.E6.tag (β₁ + β₂) → rootChar a β₁ = 1 → rootChar a β₂ = 1 →
      D.v • permLattice TwistTag.E6.perm β₁ = -β₁ → D.v • permLattice TwistTag.E6.perm β₂ = -β₂ →
      ∃ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm ∧
        (∀ ε ∈ E, (twE6LongRootSL2 X Xm).map ε.toMonoidHom = twE6LongRootSL2 X Xm) ∧
        (∀ u ∈ twE6LongRootSL2 X Xm, e u = u) ∧
        ∃ R : Subgroup (twistedE6RootGroup K σ), R ≤ twE6LongRootRadical X ∧
          (∀ u ∈ R, e u = u) ∧ ¬ R ≤ X

theorem twE6InnerLineLongRoot_of_lie
    (hB : TwE6LiftBridge) (hL : TwE6InnerLineLie) : TwE6InnerLineLongRoot := by
  intro K _ _ σ q hK3 hσ hK E hE hEab hcard hnin D hreg
  classical
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have h3 : 3 ∣ q + 1 := three_dvd_of_not_le_innerAut K σ q hσ hK E hE hnin
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  haveI : Fact (ringChar K).Prime := ⟨hpr⟩
  obtain ⟨ω, hω⟩ := exists_primCubeRoot K hK3
  have hω' : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.coe_units_iff.1 hω
  have hω3 : ω ^ 3 = 1 := hω'.pow_eq_one
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqf]
  have hexp : ∀ x ∈ twPlanePre K σ E, x ^ 3 = 1 := fun x hx =>
    pow_three_eq_one_of_mem_twPlanePre (ringChar K) f hpr hf1 K hK' σ hσ' E hx
  have hAcard : Nat.card (twPlanePre K σ E) = 3 ^ 2 := by
    rw [card_twPlanePre (ringChar K) f hpr hf1 K hK' σ hσ' E hE]
    exact hcard
  obtain ⟨x₁, hx₁A, hx₁1⟩ : ∃ x ∈ twPlanePre K σ E, x ≠ 1 := by
    have hne : twPlanePre K σ E ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hAcard]
      norm_num
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x₂, hx₂A, hx₂n⟩ := exists_mem_not_mem_zpowers (twPlanePre K σ E) hAcard hx₁A
    (hexp x₁ hx₁A) hx₁1
  have hx₂1 : x₂ ≠ 1 := fun h => hx₂n (h ▸ Subgroup.one_mem _)
  have hgen : Subgroup.closure ({x₁, x₂} : Set (ModGL TwistTag.E6.tag K)) = twPlanePre K σ E :=
    closure_pair_eq_of_not_mem (twPlanePre K σ E) hAcard hx₁A hx₂A (hexp x₁ hx₁A) hx₁1 hx₂n
  obtain ⟨a₁, ha₁, k₁, hk₁⟩ := diag_exponent_gen D.g0 D.c _ (twistedTorus_le _ _) D.hc ω hω hx₁A
    (hexp x₁ hx₁A)
  obtain ⟨a₂, ha₂, k₂, hk₂⟩ := diag_exponent_gen D.g0 D.c _ (twistedTorus_le _ _) D.hc ω hω hx₂A
    (hexp x₂ hx₂A)
  have hcube : ∀ {k : Fin Tag.E6.rank → ℕ} {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ},
      (∀ i, a i = ω ^ k i) → ∀ i, a i ^ 3 = 1 := fun {k a} hk i => by
    rw [hk i, ← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hinner₁ : (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k₁ i : ℤ) := by
    by_contra hout
    obtain ⟨α, hα, hkill⟩ := outer_kills_gen hexp hAcard D.g0 D.c _ (twistedTorus_le _ _) D.hc ω hω
      hx₁A hx₁1 a₁ ha₁ k₁ hk₁ hout
    exact hreg ⟨α, hα, hkill⟩
  have hinner₂ : (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k₂ i : ℤ) := by
    by_contra hout
    obtain ⟨α, hα, hkill⟩ := outer_kills_gen hexp hAcard D.g0 D.c _ (twistedTorus_le _ _) D.hc ω hω
      hx₂A hx₂1 a₂ ha₂ k₂ hk₂ hout
    exact hreg ⟨α, hα, hkill⟩
  have hprod₁ : ∏ i, a₁ i ^ e6DiagCoeff i = 1 := rootChar_eq_one_of_dvd hω3 hk₁ hinner₁
  have hprod₂ : ∏ i, a₂ i ^ e6DiagCoeff i = 1 := rootChar_eq_one_of_dvd hω3 hk₂ hinner₂
  obtain ⟨w', hw'⟩ : ∃ w' : WeylGroup TwistTag.E6.tag,
      ∀ y, w' • y = -permLattice TwistTag.E6.perm (D.v⁻¹ • y) :=
    ⟨CFSG.RankThree.Chevalley.e6HRReflProd * D.v⁻¹, fun y => by
      rw [mul_smul, CFSG.RankThree.Chevalley.e6HRReflProd_smul]⟩
  have hstab₁ : w' ∈ rootCharStabilizer a₁ :=
    D.mem_rootCharStabilizer h3 hx₁A ha₁ (hcube hk₁) hw'
  have hstab₂ : w' ∈ rootCharStabilizer a₂ :=
    D.mem_rootCharStabilizer h3 hx₂A ha₂ (hcube hk₂) hw'
  set b₁ : Fin Tag.E6.rank → ZMod 3 := fun i => ((k₁ i : ℕ) : ZMod 3) with hb₁
  set b₂ : Fin Tag.E6.rank → ZMod 3 := fun i => ((k₂ i : ℕ) : ZMod 3) with hb₂
  have hstab : ∀ {k : Fin Tag.E6.rank → ℕ} {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ},
      (∀ i, a i = ω ^ k i) → ∀ w ∈ rootCharStabilizer a,
        w ∈ charStabilizer (triChar (fun i => ((k i : ℕ) : ZMod 3))) := by
    intro k a hk w hw v
    have h1 : rootChar a (w • v - v) = 1 := by
      rw [rootChar_sub, hw v, mul_inv_cancel]
    have h2 := (twE6_rootChar_eq_one_iff_triPairing hω' hk (w • v - v)).1 h1
    rw [triChar_apply, triChar_apply]
    congr 1
    have h3 : triPairing (fun i => ((k i : ℕ) : ZMod 3)) (w • v) =
        triPairing (fun i => ((k i : ℕ) : ZMod 3)) (w • v - v) +
          triPairing (fun i => ((k i : ℕ) : ZMod 3)) v := by
      rw [← triPairing_add, sub_add_cancel]
    rw [h3, h2, zero_add]
  have hwb₁ : w' ∈ charStabilizer (triChar b₁) := hstab hk₁ w' hstab₁
  have hwb₂ : w' ∈ charStabilizer (triChar b₂) := hstab hk₂ w' hstab₂
  have hregpair : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      rootChar a₁ α ≠ 1 ∨ rootChar a₂ α ≠ 1 := by
    intro α hα
    by_contra hcon
    push Not at hcon
    exact hreg ⟨α, hα, D.kills_of_generators hgen ha₁ ha₂ hcon.1 hcon.2⟩
  have hreg' : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ (triPairing b₁ α = 0 ∧ triPairing b₂ α = 0) := by
    rintro α hα ⟨h1, h2⟩
    rcases hregpair α hα with h | h
    · exact h ((twE6_rootChar_eq_one_iff_triPairing hω' hk₁ α).2 h1)
    · exact h ((twE6_rootChar_eq_one_iff_triPairing hω' hk₂ α).2 h2)
  have hcN : D.c ∈ Subgroup.normalizer
      (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL_le_normalizer K σ D.hcI
  have hbridge : ∀ (x : ModGL TwistTag.E6.tag K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (k : Fin Tag.E6.rank → ℕ), x ∈ twPlanePre K σ E →
      rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) *
          D.g0 → (∀ i, a i = ω ^ k i) → (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k i : ℤ) →
      triPairing (fun i => ((k i : ℕ) : ZMod 3)) (e6Shift w') = 0 → x ∈ twistedE6RootGroup K σ := by
    intro x a k hx ha hk hdiv hs
    have hmem := hB K σ q hK3 hσ hK h3 D.Fr D.hFr D.v w' hw' D.g0 D.hg0C D.hg0 a (hcube hk)
      (rootChar_eq_one_of_dvd hω3 hk hdiv) (D.mem_rootCharStabilizer h3 hx ha (hcube hk) hw')
      ((twE6_rootChar_eq_one_iff_triPairing hω' hk (e6Shift w')).2 hs)
      (D.c * x * D.c⁻¹) (by rw [ha]; group)
    exact (Subgroup.mem_normalizer_iff.1 hcN x).2 hmem
  have hshift : triPairing b₁ (e6Shift w') ≠ 0 ∨ triPairing b₂ (e6Shift w') ≠ 0 := by
    by_contra hs0
    push Not at hs0
    have hx₁C : x₁ ∈ twistedE6RootGroup K σ := hbridge x₁ a₁ k₁ hx₁A ha₁ hk₁ hinner₁ hs0.1
    have hx₂C : x₂ ∈ twistedE6RootGroup K σ := hbridge x₂ a₂ k₂ hx₂A ha₂ hk₂ hinner₂ hs0.2
    have hAC : twPlanePre K σ E ≤ twistedE6RootGroup K σ := by
      rw [← hgen]
      refine (Subgroup.closure_le _).2 ?_
      rintro z (rfl | rfl)
      · exact hx₁C
      · exact hx₂C
    apply hnin
    intro ε hε
    have hεr : ε ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj]
      exact hE hε
    obtain ⟨g, rfl⟩ := hεr
    have hgA : (g : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
      (mem_twPlanePre_iff K σ E _).2 ⟨g, rfl, hε⟩
    have hgC := hAC hgA
    refine ⟨⟨(g : ModGL TwistTag.E6.tag K), hgC⟩, ?_⟩
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply]
    simp [MulAut.conj_apply]
  set c₁ : ZMod 3 := triPairing b₂ (e6Shift w') with hc₁
  set c₂ : ZMod 3 := -triPairing b₁ (e6Shift w') with hc₂
  have hc : c₁ ≠ 0 ∨ c₂ ≠ 0 := by
    rcases hshift with h | h
    · right
      simpa [hc₂] using h
    · left
      exact h
  have hk0 : triPairing (c₁ • b₁ + c₂ • b₂) (e6Shift w') = 0 := by
    rw [triPairing_smul_add_smul, hc₁, hc₂]
    ring
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hβ₁₂, hkβ₁, hkβ₂, hfix₁, hfix₂⟩ :=
    e6RegularInnerLine_holds b₁ b₂ hreg' w' hwb₁ hwb₂ hshift c₁ c₂ hc hk0
  set m₁ : ℕ := c₁.val with hm₁
  set m₂ : ℕ := c₂.val with hm₂
  have hm₁3 : m₁ < 3 := ZMod.val_lt c₁
  have hm₂3 : m₂ < 3 := ZMod.val_lt c₂
  have hmne : ¬ (m₁ = 0 ∧ m₂ = 0) := by
    rintro ⟨h1, h2⟩
    rcases hc with hc | hc
    · exact hc ((ZMod.val_eq_zero c₁).1 h1)
    · exact hc ((ZMod.val_eq_zero c₂).1 h2)
  have hz : x₁ ^ m₁ * x₂ ^ m₂ ∈ twPlanePre K σ E :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hx₁A _) (Subgroup.pow_mem _ hx₂A _)
  obtain ⟨g, hgz, hgE⟩ := (mem_twPlanePre_iff K σ E _).1 hz
  have he1 : twistedE6InndiagConj K σ g ≠ 1 := by
    intro h
    have hg1 : g = 1 := twistedE6InndiagConj_injective hpr hf1 hK' σ hσ' (h.trans (map_one _).symm)
    have hz1 : x₁ ^ m₁ * x₂ ^ m₂ = 1 := by
      rw [← hgz, hg1]
      rfl
    exact pow_mul_pow_ne_one (hexp x₁ hx₁A) hx₁1 (hexp x₂ hx₂A) hx₂n hm₁3 hm₂3 hmne hz1
  obtain ⟨az, haz⟩ : ∃ az : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, az = a₁ ^ m₁ * a₂ ^ m₂ :=
    ⟨_, rfl⟩
  have hdiagz : rootDiagUnit Tag.E6 az = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * (g : ModGL TwistTag.E6.tag K) * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 := by
    rw [haz]
    exact rootDiagUnit_pow_mul_eq D.g0 D.c x₁ x₂ (g : ModGL TwistTag.E6.tag K) a₁ a₂ ha₁ ha₂ m₁ m₂ hgz.symm
  have hakz : ∀ i, az i = ω ^ (m₁ * k₁ i + m₂ * k₂ i) := fun i => by
    rw [haz, Pi.mul_apply, Pi.pow_apply, Pi.pow_apply, hk₁ i, hk₂ i, ← pow_mul, ← pow_mul, ← pow_add,
      mul_comm (k₁ i), mul_comm (k₂ i)]
  have hkvec : (fun i => (((m₁ * k₁ i + m₂ * k₂ i : ℕ)) : ZMod 3)) = c₁ • b₁ + c₂ • b₂ := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb₁, hb₂, Nat.cast_add, Nat.cast_mul,
      hm₁, hm₂, ZMod.natCast_zmod_val]
  have hrc : ∀ β, triPairing (c₁ • b₁ + c₂ • b₂) β = 0 → rootChar az β = 1 :=
    fun β hβ => (twE6_rootChar_eq_one_iff_triPairing hω' hakz β).2 (by rw [hkvec]; exact hβ)
  obtain ⟨X, Xm, hpair, hinv, hfix, R, hRQ, hRfix, hRX⟩ := hL K σ q hK3 hσ hK E hE D
    (twistedE6InndiagConj K σ g) hgE he1 az ⟨g, rfl, hdiagz⟩ β₁ β₂ hβ₁ hβ₂ hβ₁₂
    (hrc β₁ hkβ₁) (hrc β₂ hkβ₂) (smul_perm_eq_neg_of_fixed hw' hfix₁)
    (smul_perm_eq_neg_of_fixed hw' hfix₂)
  exact ⟨X, Xm, hpair, hinv, twistedE6InndiagConj K σ g, hgE, he1, hfix, R, hRQ, hRfix, hRX⟩

end SA

end CFSG.LieType.SeitzGeneration.ExcWideThree
