module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Uniqueness.Section15HeringDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Extend


section Formulas

variable {F : Type} [Field F]

theorem coe_conjNormal (c : adjointGroup Tag.D4 F) (b : Fin Tag.D4.rank → Fˣ) (σ : F ≃+* F)
    (w : adjointGroup Tag.D4 F) :
    ((MulAut.conj c * exactNormalAut Tag.D4 F b σ 0) w : ModGL Tag.D4 F) =
      ((c : ModGL Tag.D4 F) * rootDiagUnit Tag.D4 b) *
        Units.map (entrywiseHom σ.toRingHom) (w : ModGL Tag.D4 F) *
          ((c : ModGL Tag.D4 F) * rootDiagUnit Tag.D4 b)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_exactNormalAut, exactQ_zero]
  group

theorem coe_graphNormal (g : adjointGroup Tag.D4 F) (a : Fin Tag.D4.rank → Fˣ) (σ : F ≃+* F)
    (w : adjointGroup Tag.D4 F) :
    ((MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F 1)) w : ModGL Tag.D4 F) =
      ((g : ModGL Tag.D4 F) * rootDiagUnit Tag.D4 a * d4P F) *
        Units.map (entrywiseHom σ.toRingHom) (w : ModGL Tag.D4 F) *
          ((g : ModGL Tag.D4 F) * rootDiagUnit Tag.D4 a * d4P F)⁻¹ := by
  have hP : Units.map (entrywiseHom (τ := Tag.D4) σ.toRingHom) (d4P F) = d4P F :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) σ.toRingHom
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, pow_one]
  simp only [map_mul, map_inv, hP]
  group

end Formulas

section Lift

variable {ℓ : ℕ} [Fact ℓ.Prime] {K K₃ : Type} [Field K] [Finite K] [CharP K ℓ] [Field K₃]
  [Finite K₃] [Algebra K K₃]

theorem exists_ringEquiv_lift (σ' : K ≃+* K) :
    ∃ σt : K₃ ≃+* K₃, (∀ c : K, σt (algebraMap K K₃ c) = algebraMap K K₃ (σ' c)) ∧
      ∃ k : ℕ, ∀ y : K₃, σt y = y ^ (ℓ ^ k) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  have hK : Nat.card K = ℓ ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨fr, hfr, -, hgen, -, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ n.pos hK
  have hmem : σ' ∈ Subgroup.zpowers fr := by rw [hgen]; exact Subgroup.mem_top σ'
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hmem)
  have hσ : ∀ c, σ' c = c ^ (ℓ ^ k) := fun c => by
    rw [← hk]
    exact ringAut_pow_apply_of_frobenius hfr k c
  have : CharP K₃ ℓ := charP_of_injective_algebraMap (algebraMap K K₃).injective ℓ
  have hinj : Function.Injective (iterateFrobenius K₃ ℓ k) := (iterateFrobenius K₃ ℓ k).injective
  refine ⟨RingEquiv.ofBijective (iterateFrobenius K₃ ℓ k)
    ⟨hinj, Finite.surjective_of_injective hinj⟩, fun c => ?_, k, fun y => ?_⟩
  · change iterateFrobenius K₃ ℓ k (algebraMap K K₃ c) = algebraMap K K₃ (σ' c)
    rw [iterateFrobenius_def, hσ, map_pow]
  · exact iterateFrobenius_def ℓ k y

end Lift

theorem exists_pow_coprime_three {Γ : Type*} [Group Γ] [Finite Γ] (Z : Γ) (n : ℕ)
    (hn : Nat.Coprime 3 n) (hnZ : n ∣ orderOf Z) :
    ∃ m : ℕ, m ≡ 1 [MOD n] ∧ Nat.Coprime 3 (orderOf (Z ^ m)) := by
  classical
  have hN : orderOf Z ≠ 0 := (orderOf_pos Z).ne'
  obtain ⟨a, N', hN3, hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN 3 (by norm_num)
  have hco : Nat.Coprime (3 ^ a) N' :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
  obtain ⟨m, hm0, hm1⟩ := Nat.chineseRemainder hco 0 1
  have hnN' : n ∣ N' := by
    have : n ∣ 3 ^ a * N' := hN' ▸ hnZ
    exact (Nat.Coprime.pow_right a hn.symm).dvd_of_dvd_mul_left this
  refine ⟨m, hm1.of_dvd hnN', ?_⟩
  have h3a : 3 ^ a ∣ m := (Nat.modEq_zero_iff_dvd).1 hm0
  have hpow : (Z ^ m) ^ N' = 1 := by
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hN']
    obtain ⟨t, ht⟩ := h3a
    exact ⟨t, by rw [ht]; ring⟩
  have hdvd : orderOf (Z ^ m) ∣ N' := orderOf_dvd_of_pow_eq_one hpow
  exact Nat.Coprime.coprime_dvd_right hdvd
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)

section Star

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_one_of_card_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card_sub_one_eq_one c hc
    rw [← Nat.card_eq_fintype_card, hK] at h
    simpa using h

theorem units_map_entrywiseHom_one_D4 (w : ModGL Tag.D4 K) :
    Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) w = w := by
  have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
  rw [e1]
  exact Units.ext (entrywise_id (R := K) _)

theorem d4P_inv_conj_mem {F : Type} [Field F] {m : ModGL Tag.D4 F} (hm : m ∈ adjointGroup Tag.D4 F) :
    (d4P F)⁻¹ * m * d4P F ∈ adjointGroup Tag.D4 F := by
  have h : ((d4Graph F 2 ⟨m, hm⟩ : adjointGroup Tag.D4 F) : ModGL Tag.D4 F) ∈
      adjointGroup Tag.D4 F := (d4Graph F 2 ⟨m, hm⟩).2
  rw [coe_d4Graph] at h
  have hP3 : d4P F ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 F
  have hP2 : d4P F ^ 2 = (d4P F)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hP3)
  rw [hP2, inv_inv] at h
  exact h

theorem star_commute (g c : adjointGroup Tag.D4 K) (a b : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hcomm : (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) *
        (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) =
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) *
        (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0))
    (X Y : ModGL Tag.D4 K)
    (hX : X = (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K)
    (hY : Y = (c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) (v : adjointGroup Tag.D4 K) :
    ((X * Y)⁻¹ * (Y * Units.map (entrywiseHom σ.toRingHom) X)) * (v : ModGL Tag.D4 K) =
      (v : ModGL Tag.D4 K) * ((X * Y)⁻¹ * (Y * Units.map (entrywiseHom σ.toRingHom) X)) := by
  classical
  obtain ⟨u, rfl⟩ : ∃ u, entrywiseAdjointAut Tag.D4 σ u = v :=
    ⟨(entrywiseAdjointAut Tag.D4 σ)⁻¹ v, by simp⟩
  have h : (((MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) *
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1))) u : ModGL Tag.D4 K) =
      (((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) *
      (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0)) u : ModGL Tag.D4 K) :=
    congrArg (fun φ : MulAut (adjointGroup Tag.D4 K) =>
      ((φ u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) hcomm
  have hl : (((MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) *
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1))) u : ModGL Tag.D4 K) =
      Y * Units.map (entrywiseHom σ.toRingHom) (X * (u : ModGL Tag.D4 K) * X⁻¹) * Y⁻¹ := by
    have := graphType_coe_normalForm (K := K) g a 1 u
    rw [pow_one] at this
    rw [MulAut.mul_apply, coe_conjNormal, ← hY, this, ← hX]
  have hr : (((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) *
      (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0)) u : ModGL Tag.D4 K) =
      X * (Y * Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) * Y⁻¹) * X⁻¹ := by
    have := graphType_coe_normalForm (K := K) g a 1
      ((MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) u)
    rw [pow_one] at this
    rw [MulAut.mul_apply, this, coe_conjNormal, ← hX, ← hY]
  rw [hl, hr] at h
  simp only [map_mul, map_inv] at h
  have hc : (X * Y) * Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) * (X * Y)⁻¹ =
      (Y * Units.map (entrywiseHom σ.toRingHom) X) *
        Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) *
          (Y * Units.map (entrywiseHom σ.toRingHom) X)⁻¹ := by
    calc (X * Y) * Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) * (X * Y)⁻¹
        = X * (Y * Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) * Y⁻¹) * X⁻¹ := by
          group
      _ = Y * (Units.map (entrywiseHom σ.toRingHom) X *
            Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) *
              (Units.map (entrywiseHom σ.toRingHom) X)⁻¹) * Y⁻¹ := h.symm
      _ = _ := by group
  have := graphType_commute_of_conj_eq (X * Y) (Y * Units.map (entrywiseHom σ.toRingHom) X)
    (Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K)) hc
  rw [coe_entrywiseAdjointAut]
  exact this

theorem star_identity (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K)
    (g c : adjointGroup Tag.D4 K) (a b : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hcomm : (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) *
        (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) =
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) *
        (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0)) :
    ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) *
        Units.map (entrywiseHom σ.toRingHom)
          ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) *
        ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) := by
  classical
  obtain ⟨Y, hY⟩ : ∃ Y : ModGL Tag.D4 K, Y = (c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b :=
    ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ModGL Tag.D4 K,
      X = (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K := ⟨_, rfl⟩
  have hkey := star_commute g c a b σ hcomm X Y hX hY
  rw [← hY, ← hX]
  suffices hR : (X * Y)⁻¹ * (Y * Units.map (entrywiseHom σ.toRingHom) X) = 1 from
    (inv_mul_eq_one.1 hR).symm
  rcases hK with h2 | h4
  ·
    have ha : a = 1 := funext fun i => Units.ext (by
      rcases eq_zero_or_one_of_card_two h2 (a i : K) with h | h
      · exact absurd h (a i).ne_zero
      · simpa using h)
    have hb : b = 1 := funext fun i => Units.ext (by
      rcases eq_zero_or_one_of_card_two h2 (b i : K) with h | h
      · exact absurd h (b i).ne_zero
      · simpa using h)
    have hσ : σ = 1 := RingEquiv.ext fun x => by
      rcases eq_zero_or_one_of_card_two h2 x with h | h <;> simp [h]
    subst ha hb hσ
    rw [rootDiagUnit_one, mul_one] at hX hY
    have hmem : (X * Y)⁻¹ * (Y * Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) X) ∈
        adjointGroup Tag.D4 K := by
      rw [units_map_entrywiseHom_one_D4]
      have e : (X * Y)⁻¹ * (Y * X) =
          (c : ModGL Tag.D4 K)⁻¹ * ((d4P K)⁻¹ * ((g : ModGL Tag.D4 K)⁻¹ * c * g) * d4P K) := by
        rw [hX, hY]
        group
      rw [e]
      exact mul_mem (inv_mem c.2) (d4P_inv_conj_mem (mul_mem (mul_mem (inv_mem g.2) c.2) g.2))
    obtain ⟨r, hr⟩ : ∃ r : adjointGroup Tag.D4 K, (r : ModGL Tag.D4 K) =
        (X * Y)⁻¹ * (Y * Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) X) :=
      ⟨⟨_, hmem⟩, rfl⟩
    have hcen : r ∈ Subgroup.center (adjointGroup Tag.D4 K) := by
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hr]
      exact (hkey v).symm
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcen
    rw [← hr, hcen]
    rfl
  ·
    obtain ⟨L, hLf, hLa, ι, -⟩ : ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L),
        True := ⟨AlgebraicClosure K, inferInstance, inferInstance, algebraMap K _, trivial⟩
    have hfaith := Chevalley_large_finite_root_centralizer_faithfulness_of_four_le Tag.D4 K h4 L ι
    have hdiag : ∀ a' : Fin Tag.D4.rank → Kˣ,
        baseChangeGL ι (rootDiagUnit Tag.D4 a') ∈ adjointGroup Tag.D4 L := fun a' => by
      rw [baseChangeGL_rootDiagUnit]
      exact (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
    have hgm : ∀ g' : adjointGroup Tag.D4 K,
        baseChangeGL ι (g' : ModGL Tag.D4 K) ∈ adjointGroup Tag.D4 L := fun g' =>
      CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g'.2
    have hSg : baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) (g : ModGL Tag.D4 K)) ∈
        adjointGroup Tag.D4 L := by
      have := hgm (entrywiseAdjointAut Tag.D4 σ g)
      rwa [coe_entrywiseAdjointAut] at this
    have hSd : baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.D4 a)) ∈
        adjointGroup Tag.D4 L := by
      rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_rootDiagUnit]
      exact hdiag _
    have hSP : Units.map (entrywiseHom (τ := Tag.D4) σ.toRingHom) (d4P K) = d4P K :=
      units_map_entrywiseHom_diagramMap (t := TwistTag.D4) σ.toRingHom
    have e : baseChangeGL ι ((X * Y)⁻¹ * (Y * Units.map (entrywiseHom σ.toRingHom) X)) =
        (baseChangeGL ι (rootDiagUnit Tag.D4 b))⁻¹ * (baseChangeGL ι (c : ModGL Tag.D4 K))⁻¹ *
          ((d4P L)⁻¹ * ((baseChangeGL ι (rootDiagUnit Tag.D4 a))⁻¹ *
            (baseChangeGL ι (g : ModGL Tag.D4 K))⁻¹ * baseChangeGL ι (c : ModGL Tag.D4 K) *
              baseChangeGL ι (rootDiagUnit Tag.D4 b) *
              baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) (g : ModGL Tag.D4 K)) *
              baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.D4 a))) *
            d4P L) := by
      rw [hX, hY]
      simp only [map_mul, map_inv, hSP, graphType_baseChangeGL_d4P]
      group
    have hmemR : baseChangeGL ι ((X * Y)⁻¹ * (Y * Units.map (entrywiseHom σ.toRingHom) X)) ∈
        adjointGroup Tag.D4 L := by
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hdiag b)) (inv_mem (hgm c)))
        (d4P_inv_conj_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem (hdiag a))
          (inv_mem (hgm g))) (hgm c)) (hdiag b)) hSg) hSd))
    have hR1 : baseChangeGL ι ((X * Y)⁻¹ * (Y * Units.map (entrywiseHom σ.toRingHom) X)) = 1 := by
      refine hfaith.2.2.1 _ hmemR fun h hh => ?_
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hh
      rw [← map_mul, ← map_mul]
      exact congrArg _ (hkey ⟨v, hv⟩)
    exact hfaith.1 (hR1.trans (map_one _).symm)

end Star

end Extend

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
