module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4DescentInner
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassA
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityGe5Aux
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.ExtendProps
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.NormalForm
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Faithful

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

theorem ringEquiv_eq_one_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (σ : K ≃+* K) : σ = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = p := by rw [← Nat.card_eq_fintype_card, hK]
  let e := ZMod.ringEquivOfPrime K hp hK'
  have h : σ.toRingHom.comp e.toRingHom = e.toRingHom := RingHom.ext_zmod _ _
  refine RingEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := e.surjective x
  have := congrArg (fun r : ZMod p →+* K => r y) h
  simpa using this

set_option linter.unusedSectionVars false

section Sigma


theorem graphFixedInclusion_injective' (K : Type) [Field K] (σ : K ≃+* K) :
    Function.Injective (graphFixedInclusion K σ) := by
  intro y₁ y₂ h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact h'

theorem d4_sigma_eq_one {K : Type} [Field K] [Finite K] [CharP K 3]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (α : MulAut (adjointGroup Tag.D4 K))
    (hαdef : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1))
    (hα3 : α ^ 3 = 1)
    (c : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (Ξ : MulAut (adjointGroup Tag.D4 K)) (hΞdef : Ξ = MulAut.conj c * exactNormalAut Tag.D4 K b σ 0)
    (hcop : Nat.Coprime 3 (orderOf Ξ)) (hcomm : Ξ * α = α * Ξ)
    (hfix : ∀ x ∈ fixSubgroup α, Ξ x = x) : σ = 1 := by
  classical
  by_contra hσ1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, hf, hKf⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 3 ^ f := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hKcard : 4 ≤ Nat.card K := by
    by_contra hlt
    push Not at hlt
    have h3 : Nat.card K = 3 := by
      have : 3 ≤ 3 ^ f := Nat.le_self_pow (by omega) 3
      omega
    exact hσ1 (ringEquiv_eq_one_of_card_prime Nat.prime_three h3 σ)
  have hstar : ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) *
        Units.map (entrywiseHom σ.toRingHom)
          ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) *
        ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) := by
    refine star_identity (Or.inr hKcard) g c a b σ ?_
    rw [← hΞdef, ← hαdef]
    exact hcomm
  obtain ⟨K₃, hF₃, hFin₃, hAlg, Fr, hK₃, hFr, ψ, φ, hψβ, hφ3, hφo, hFrψ, -, hfix2, hx4fix,
    hx4range⟩ := dual_data_one (ℓ := 3) hf K hKf α hα3 g a hαdef
  have hchar : CharP K₃ 3 :=
    charP_of_injective_algebraMap (algebraMap K K₃).injective 3
  obtain ⟨σt, hσt, k, hσtk⟩ := exists_ringEquiv_lift (ℓ := 3) (K₃ := K₃) σ
  generalize algebraMap K K₃ = ι at hσt hψβ hfix2
  have hFrι : ∀ x : K, Fr (ι x) = ι x := fun x => by
    rw [hFr, ← map_pow]
    congr 1
    have : Fintype K := Fintype.ofFinite K
    rw [← hKf, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hFrσt : ∀ y, Fr (σt y) = σt (Fr y) := fun y => by
    rw [hFr (σt y), hσtk y, hσtk (Fr y), hFr y, ← pow_mul, ← pow_mul, mul_comm]
  have hFr3 : ∀ c, Fr (Fr (Fr c)) = c := fun c => by
    have : Fintype K₃ := Fintype.ofFinite K₃
    rw [hFr, hFr, hFr, ← pow_mul, ← pow_mul,
      show 3 ^ f * (3 ^ f * 3 ^ f) = (3 ^ f) ^ 3 by ring,
      ← hK₃, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨Ξt₀, hΞt₀⟩ : ∃ Ξt₀ : MulAut (adjointGroup Tag.D4 K₃),
      Ξt₀ = MulAut.conj (baseChangeAdj ι c) *
        exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0 := ⟨_, rfl⟩
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : MulAut (adjointGroup Tag.D4 K₃), β₀ = MulAut.conj (baseChangeAdj ι g) *
      (exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (a i)) Fr 0 *
        d4Graph K₃ 1) := ⟨_, rfl⟩
  have hN1 : Ξt₀ * β₀ = β₀ * Ξt₀ := by
    rw [hΞt₀, hβ₀]
    exact ext_commute_graph ι c g a b σ σt Fr hσt hFrι hFrσt hstar
  have hN2 : Ξt₀ * entrywiseAdjointAut Tag.D4 Fr = entrywiseAdjointAut Tag.D4 Fr * Ξt₀ := by
    rw [hΞt₀]
    exact ext_commute_entrywise ι c b σt Fr hFrι hFrσt
  have hE1 : ∀ u, Ξt₀ (baseChangeAdj ι u) = baseChangeAdj ι (Ξ u) := fun u => by
    rw [hΞt₀, hΞdef]
    exact ext_apply_baseChange ι c b σ σt hσt u
  have hinjA : Function.Injective (baseChangeAdj ι) := fun u u' h =>
    Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))
  have hEn : ∀ (n : ℕ) (u : adjointGroup Tag.D4 K),
      (Ξt₀ ^ n) (baseChangeAdj ι u) = baseChangeAdj ι ((Ξ ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih, hE1]
  have hdvd : orderOf Ξ ∣ orderOf Ξt₀ := by
    refine orderOf_dvd_of_pow_eq_one (MulEquiv.ext fun u => hinjA ?_)
    rw [← hEn, pow_orderOf_eq_one]
    try rfl
  obtain ⟨m, hm1, hm3⟩ := exists_pow_coprime_three Ξt₀ (orderOf Ξ) hcop hdvd
  obtain ⟨Ξt, hΞt⟩ : ∃ Ξt : MulAut (adjointGroup Tag.D4 K₃), Ξt = Ξt₀ ^ m := ⟨_, rfl⟩
  have hΞt3 : Nat.Coprime 3 (orderOf Ξt) := hΞt ▸ hm3
  have hΞm : Ξ ^ m = Ξ := by
    have h : Ξ ^ m = Ξ ^ 1 := (pow_eq_pow_iff_modEq).2 hm1
    rw [h, pow_one]
  have hΞt1 : ∀ u, Ξt (baseChangeAdj ι u) = baseChangeAdj ι (Ξ u) := fun u => by
    rw [hΞt, hEn, hΞm]
  have hNβ : Ξt * β₀ = β₀ * Ξt := by
    rw [hΞt]
    exact Commute.pow_left (show Commute Ξt₀ β₀ from hN1) m
  have hNT : Ξt * entrywiseAdjointAut Tag.D4 Fr = entrywiseAdjointAut Tag.D4 Fr * Ξt := by
    rw [hΞt]
    exact Commute.pow_left (show Commute Ξt₀ (entrywiseAdjointAut Tag.D4 Fr) from hN2) m
  have hθ3 : Nat.Coprime 3 (orderOf (ψ * Ξt * ψ⁻¹)) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ?_) hΞt3
    rw [conj_pow, pow_orderOf_eq_one]
    group
  obtain ⟨x, hx⟩ : ∃ x : MulAut (adjointGroup Tag.D4 K₃),
      x = twistedEntrywiseAut TwistTag.D4 1 Fr := ⟨_, rfl⟩
  have hψβx : ψ * β₀ * ψ⁻¹ = x := by
    rw [hβ₀, hx]
    exact hψβ
  have hθx : (ψ * Ξt * ψ⁻¹) * x = x * (ψ * Ξt * ψ⁻¹) := by
    rw [← hψβx]
    calc ψ * Ξt * ψ⁻¹ * (ψ * β₀ * ψ⁻¹) = ψ * (Ξt * β₀) * ψ⁻¹ := by group
      _ = ψ * (β₀ * Ξt) * ψ⁻¹ := by rw [hNβ]
      _ = ψ * β₀ * ψ⁻¹ * (ψ * Ξt * ψ⁻¹) := by group
  have hθΘ : (ψ * Ξt * ψ⁻¹) * (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹) =
      (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹) * (ψ * Ξt * ψ⁻¹) :=
    calc ψ * Ξt * ψ⁻¹ * (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹)
        = ψ * (Ξt * entrywiseAdjointAut Tag.D4 Fr) * ψ⁻¹ := by group
      _ = ψ * (entrywiseAdjointAut Tag.D4 Fr * Ξt) * ψ⁻¹ := by rw [hNT]
      _ = ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹ * (ψ * Ξt * ψ⁻¹) := by group
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :=
    finite_graphFixedRootGroup_D4 Fr
  have hφdata : OuterCentData 3 φ :=
    outerCentData_three_of_classes hf hK₃ Fr hFr
      (outerCentData_three_classA hf hK₃ Fr hFr) φ hφ3 hφo
  have hL27 : ¬ (3 = 3 ∧ IsLTwoTwentySeven (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) := by
    rintro ⟨-, hL⟩
    exact (chevSimple_graphFixedRootGroup_cubic Nat.prime_three (by norm_num) hf K₃ hK₃ Fr
      (r := 1) (Or.inl rfl) (fun c => by rw [hFr c, pow_one])).2.2 rfl hL
  have hθinner : ψ * Ξt * ψ⁻¹ ∈ innerAut (adjointGroup Tag.D4 K₃) := by
    refine descent_inner x
      (graphFixedInclusion K₃ Fr) (graphFixedInclusion_injective' K₃ Fr)
      (fun y => by rw [hx]; exact hx4fix y)
      (fun w hw => by rw [hx] at hw; exact hx4range w hw)
      φ (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹) (fun y => (hFrψ y).symm)
      (fun ζ hζ3 hζφ hζfix => hφdata.cent hL27 ζ hζ3 hζφ (fun t ht => hζfix t ht))
      (center_graphFixedRootGroup_eq_bot Fr.surjective)
      (by rw [hx]; exact faithfulAt_x4_one Fr hFr3) (ψ * Ξt * ψ⁻¹) hθ3 hθx hθΘ ?_
    intro y hy
    obtain ⟨u, hu⟩ := hfix2 y hy
    have hu' : Ξ u.1 = u.1 := hfix u.1 u.2
    have h1 : (ψ * Ξt * ψ⁻¹) (ψ (baseChangeAdj ι u.1)) = ψ (baseChangeAdj ι u.1) := by
      change ψ (Ξt (ψ⁻¹ (ψ (baseChangeAdj ι u.1)))) = _
      rw [MulAut.inv_apply_self, hΞt1, hu']
    exact (congrArg (ψ * Ξt * ψ⁻¹) hu).trans (h1.trans hu.symm)
  have hΞtinner : Ξt ∈ innerAut (adjointGroup Tag.D4 K₃) := by
    obtain ⟨y', hy'⟩ := hθinner
    refine ⟨ψ⁻¹ y', ?_⟩
    have h := descent_mulAut_mul_conj ψ⁻¹ y'
    calc MulAut.conj (ψ⁻¹ y') = MulAut.conj (ψ⁻¹ y') * ψ⁻¹ * ψ := by group
      _ = ψ⁻¹ * MulAut.conj y' * ψ := by rw [← h]
      _ = Ξt := by rw [hy']; group
  obtain ⟨z, hz⟩ := hΞtinner
  have hfp1 : fieldPart Ξt = 1 := by rw [← hz]; exact fieldPart_conj z
  have hfpt₀ : fieldPart Ξt₀ = σt := by
    rw [hΞt₀, map_mul, fieldPart_conj, one_mul]
    have := fieldPart_normalForm (K := K₃) (fun i => Units.map ι.toMonoidHom (b i)) σt 0
    rwa [d4Graph_zero, mul_one] at this
  have hfpΞ : fieldPart Ξ = σ := by
    rw [hΞdef, map_mul, fieldPart_conj, one_mul]
    have := fieldPart_normalForm (K := K) b σ 0
    rwa [d4Graph_zero, mul_one] at this
  have hσtm : σt ^ m = 1 := by
    rw [← hfpt₀, ← map_pow, ← hΞt]
    exact hfp1
  have hσm : σ ^ m = 1 := by
    refine RingEquiv.ext fun u => ?_
    have hpow : ∀ n : ℕ, ∀ u : K, (σt ^ n) (ι u) = ι ((σ ^ n) u) := by
      intro n
      induction n with
      | zero => intro u; simp
      | succ n ih =>
        intro u
        rw [pow_succ', pow_succ', RingAut.mul_apply, RingAut.mul_apply, ih, hσt]
    have h := hpow m u
    rw [hσtm] at h
    exact ι.injective (by simpa using h.symm)
  apply hσ1
  calc σ = fieldPart (Ξ ^ m) := by rw [hΞm, hfpΞ]
    _ = σ ^ m := by rw [map_pow, hfpΞ]
    _ = 1 := hσm

end Sigma

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
