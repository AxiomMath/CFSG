module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjLift
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

set_option linter.unusedSectionVars false

section Arith

theorem e6Conj_pow_eq_self_of_pow_three {M : Type*} [Monoid M] {v : M} (hv : v ^ 3 = 1) {q : ℕ}
    (hq : 3 ∣ q - 1) (hq1 : 1 ≤ q) : v ^ q = v := by
  obtain ⟨m, hm⟩ := hq
  have : q = 3 * m + 1 := by omega
  rw [this, pow_succ, pow_mul, hv, one_pow, one_mul]

theorem three_dvd_natCard_sub_one {K : Type} [Field K] [Finite K] {ω : Kˣ} (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) : 3 ∣ Nat.card K - 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime h3 h1
  have h := orderOf_dvd_natCard ω
  rwa [hord, Nat.card_units] at h

theorem e6RootParams_kacCoweight {k : Type} [Field k] (ω : kˣ) :
    e6RootParams (fun l => ω ^ e6KacCoweight l) = e6LineChar ω :=
  cartanChar_e6KacCoweight ω

end Arith

section Cocycle


variable {K : Type} [Field K] [Finite K]

theorem lang_cocycle_mem_toralRootGroup_threeA2 {p e : ℕ} [Fact p.Prime] [CharP K p]
    [CharP (AlgebraicClosure K) p] (hp3 : p ≠ 3) (hK : Nat.card K = p ^ e)
    {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {s : ModGL Tag.E6 K}
    (hs : s ∈ adjointGroup Tag.E6 K) {y : ModGL Tag.E6 (AlgebraicClosure K)}
    (hy : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hsy : baseChangeGL (algebraMap K (AlgebraicClosure K)) s =
      y * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (rootDiagUnit Tag.E6 (e6LineChar ω)) * y⁻¹) :
    y⁻¹ * entrywiseFrobGL Tag.E6 (AlgebraicClosure K) p e y ∈
      toralRootGroup Tag.E6 (AlgebraicClosure K) (fun i =>
        Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (e6LineChar ω i)) := by
  have h3q : 3 ∣ p ^ e - 1 := hK ▸ three_dvd_natCard_sub_one hω3 hω1
  have hq1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨Ey, hEy⟩ := exists_finset_descent hy
  obtain ⟨K₃, hK₃, hEK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K) Ey
  have : Finite K₃ := hK₃
  have : CharP K₃ p := Subfield.charP K₃ p
  obtain ⟨y₃, hy₃C, hy₃⟩ := hEy K₃ hEK₃
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K →+* K₃,
      K₃.subtype.comp ι₃ = algebraMap K (AlgebraicClosure K) :=
    ⟨(algebraMap K (AlgebraicClosure K)).codRestrict K₃ fun c => hιK₃ ⟨c, rfl⟩,
      RingHom.ext fun _ => rfl⟩
  obtain ⟨Fr₃, hFr₃def⟩ : ∃ Fr₃ : K₃ →+* K₃, Fr₃ = iterateFrobenius K₃ p e := ⟨_, rfl⟩
  have hFr₃ : ∀ c, Fr₃ c = c ^ (p ^ e) := fun c => by
    rw [hFr₃def, iterateFrobenius_def]
  have hFrι : Fr₃.comp ι₃ = ι₃ := by
    have : Fintype K := Fintype.ofFinite K
    ext c
    rw [RingHom.comp_apply, hFr₃, ← map_pow]
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hK] at h
    rw [h]
  have hFrL : K₃.subtype.comp Fr₃ = (iterateFrobenius (AlgebraicClosure K) p e).comp
      K₃.subtype := by
    ext c
    simp only [RingHom.comp_apply, Subfield.coe_subtype, hFr₃, iterateFrobenius_def]
    push_cast
    rfl
  have hbcinj : Function.Injective (baseChangeGL (τ := Tag.E6) K₃.subtype) :=
    baseChangeGL_injective K₃.subtype
  have hbcι : ∀ g : ModGL Tag.E6 K, baseChangeGL K₃.subtype (baseChangeGL ι₃ g) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) g := fun g => by
    rw [baseChangeGL_baseChangeGL, hιι]
  obtain ⟨d₃, hd₃⟩ : ∃ d, d = baseChangeGL ι₃ (rootDiagUnit Tag.E6 (e6LineChar ω)) :=
    ⟨_, rfl⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s', s' = baseChangeGL ι₃ s := ⟨_, rfl⟩
  have hs₃y : s₃ = y₃ * d₃ * y₃⁻¹ := by
    apply hbcinj
    rw [map_mul, map_mul, map_inv, hy₃, hd₃, hs₃, hbcι, hbcι]
    exact hsy
  have hF₃bc : ∀ g : ModGL Tag.E6 K₃, Units.map (entrywiseHom Fr₃) g = baseChangeGL Fr₃ g :=
    fun g => units_map_entrywiseHom_eq_baseChangeGL Fr₃ g
  obtain ⟨c₃, hc₃⟩ : ∃ c, c = y₃⁻¹ * Units.map (entrywiseHom Fr₃) y₃ := ⟨_, rfl⟩
  have hc₃L : baseChangeGL K₃.subtype c₃ =
      y⁻¹ * entrywiseFrobGL Tag.E6 (AlgebraicClosure K) p e y := by
    rw [hc₃, map_mul, map_inv, hy₃]
    congr 1
    rw [← hy₃]
    exact (units_map_entrywiseHom_baseChangeGL K₃.subtype
      (iterateFrobenius (AlgebraicClosure K) p e) Fr₃ hFrL.symm y₃).symm
  have hF₃d : Units.map (entrywiseHom Fr₃) d₃ = d₃ := by
    rw [hF₃bc, hd₃, baseChangeGL_baseChangeGL, hFrι]
  have hF₃s : Units.map (entrywiseHom Fr₃) s₃ = s₃ := by
    rw [hF₃bc, hs₃, baseChangeGL_baseChangeGL, hFrι]
  have hF₃y₃ : Units.map (entrywiseHom Fr₃) y₃ ∈ adjointGroup Tag.E6 K₃ := by
    rw [hF₃bc]
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup Fr₃ hy₃C
  obtain ⟨a₃, ha₃⟩ : ∃ a : Fin Tag.E6.rank → K₃ˣ,
      a = fun i => Units.map ι₃.toMonoidHom (e6LineChar ω i) := ⟨_, rfl⟩
  have hd₃a : d₃ = rootDiagUnit Tag.E6 a₃ := by
    rw [hd₃, baseChangeGL_rootDiagUnit, ha₃]
  have hc₃d : c₃ * d₃ = d₃ * c₃ := by
    have h1 : Units.map (entrywiseHom Fr₃) y₃ * d₃ * (Units.map (entrywiseHom Fr₃) y₃)⁻¹ =
        y₃ * d₃ * y₃⁻¹ := by
      rw [← hs₃y, ← hF₃s, hs₃y, map_mul, map_mul, map_inv, hF₃d]
    have h2 : c₃ * d₃ * c₃⁻¹ = d₃ := by
      calc c₃ * d₃ * c₃⁻¹ = y₃⁻¹ * (Units.map (entrywiseHom Fr₃) y₃ * d₃ *
            (Units.map (entrywiseHom Fr₃) y₃)⁻¹) * y₃ := by rw [hc₃]; group
        _ = y₃⁻¹ * (y₃ * d₃ * y₃⁻¹) * y₃ := by rw [h1]
        _ = d₃ := by group
    rw [← mul_inv_eq_iff_eq_mul.1 h2]
  have hc₃C : c₃ ∈ toralCentralizer Tag.E6 K₃ a₃ := by
    refine mem_toralCentralizer.2 ⟨by rw [hc₃]; exact mul_mem (inv_mem hy₃C) hF₃y₃, ?_⟩
    rw [← hd₃a]
    calc d₃ * c₃ * d₃⁻¹ = c₃ * d₃ * d₃⁻¹ := by rw [hc₃d]
      _ = c₃ := by group
  obtain ⟨u₀₃, hu₀₃⟩ : ∃ u : Fin Tag.E6.rank → K₃ˣ,
      u = fun l => Units.map ι₃.toMonoidHom (ω ^ e6KacCoweight l) := ⟨_, rfl⟩
  have hu₀₃a : e6RootParams u₀₃ = a₃ := by
    rw [hu₀₃, e6RootParams_map, e6RootParams_kacCoweight, ha₃]
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid K₃ u₀₃ := ⟨_, rfl⟩
  obtain ⟨π₃, hπ₃⟩ : ∃ π : e6Data_valid.minGroup K₃ →* ModGL Tag.E6 K₃,
      π = (adjointGroup Tag.E6 K₃).subtype.comp (e6Isogeny K₃) := ⟨_, rfl⟩
  have hπ₃a : ∀ g, π₃ g = ((e6Isogeny K₃ g : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) :=
    fun g => by rw [hπ₃]; rfl
  have hπT : π₃ T = d₃ := by
    rw [hπ₃a, hT, hd₃a, ← hu₀₃a]
    exact e6Isogeny_minTorus u₀₃
  obtain ⟨yl, hyl⟩ := e6Isogeny_surjective K₃ ⟨y₃, hy₃C⟩
  have hπy : π₃ yl = y₃ := by
    rw [hπ₃a, hyl]
  obtain ⟨sl, hsl⟩ := e6Isogeny_surjective K ⟨s, hs⟩
  obtain ⟨sl₃, hsl₃⟩ : ∃ g, g = minBC e6Data_valid ι₃ sl := ⟨_, rfl⟩
  have hπs : π₃ sl₃ = s₃ := by
    rw [hπ₃a, hsl₃, e6Isogeny_minBC, hsl, hs₃]
  obtain ⟨z₀, hz₀⟩ : ∃ z, z = (yl * T * yl⁻¹)⁻¹ * sl₃ := ⟨_, rfl⟩
  have hz₀c : z₀ ∈ Subgroup.center (e6Data_valid.minGroup K₃) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [← hπ₃a, hz₀, map_mul, map_inv, map_mul, map_mul, map_inv, hπy, hπT, hπs, hs₃y]
    group
  have hsT : sl₃ = yl * T * yl⁻¹ * z₀ := by
    rw [hz₀]
    group
  obtain ⟨Fl, hFl⟩ : ∃ F : e6Data_valid.minGroup K₃ →* e6Data_valid.minGroup K₃,
      F = minBC e6Data_valid Fr₃ := ⟨_, rfl⟩
  have hFls : Fl sl₃ = sl₃ := by
    rw [hFl, hsl₃, minBC_minBC_E6, hFrι]
  have hFlT : Fl T = T := by
    rw [hFl, hT, minBC_minTorus_E6]
    congr 1
    funext l
    rw [hu₀₃]
    apply Units.ext
    change Fr₃ (ι₃ (((ω ^ e6KacCoweight l : Kˣ)) : K)) = ι₃ (((ω ^ e6KacCoweight l : Kˣ)) : K)
    exact RingHom.congr_fun hFrι _
  have hFlz : Fl z₀ = z₀ := by
    obtain ⟨v, hv, hv3⟩ := exists_minTorus_of_mem_center_E6 hz₀c
    rw [hv, hFl, minBC_minTorus_E6]
    congr 1
    funext l
    apply Units.ext
    change Fr₃ ((v l : K₃ˣ) : K₃) = ((v l : K₃ˣ) : K₃)
    rw [hFr₃]
    have h := congrArg Units.val (hv3 l)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact e6Conj_pow_eq_self_of_pow_three h h3q hq1
  have hπFy : π₃ (Fl yl) = Units.map (entrywiseHom Fr₃) y₃ := by
    rw [hπ₃a, hFl, e6Isogeny_minBC, hF₃bc, hyl]
  have hcomm := conj_comm_of_frobenius Fl hsT hFls hFlT hFlz
  have hπc : π₃ (yl⁻¹ * Fl yl) = c₃ := by
    rw [map_mul, map_inv, hπy, hπFy, hc₃]
  have hcl : ((e6Isogeny K₃ (yl⁻¹ * Fl yl) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = c₃ := by
    rw [← hπ₃a, hπc]
  have hcomm' : (yl⁻¹ * Fl yl) * minTorus e6Data_valid K₃ u₀₃ =
      minTorus e6Data_valid K₃ u₀₃ * (yl⁻¹ * Fl yl) := by
    rw [← hT]
    exact hcomm
  have ha₃3 : ∀ i, e6RootParams u₀₃ i ^ 3 = 1 := fun i => by
    rw [hu₀₃a, ha₃, ← map_pow, e6LineChar_pow_three hω3, map_one]
  have hc₃M : c₃ ∈ toralRootGroup Tag.E6 K₃ a₃ := by
    rw [← hu₀₃a]
    exact mem_toralRootGroup_of_commute_lift_char hp3 u₀₃ ha₃3
      (by rw [hu₀₃a]; exact hc₃C) hcl hcomm'
  have hM := baseChangeGL_mem_toralRootGroup K₃.subtype hc₃M
  rw [hc₃L] at hM
  convert hM using 2
  funext i
  rw [ha₃]
  apply Units.ext
  change (algebraMap K (AlgebraicClosure K)) ((e6LineChar ω i : Kˣ) : K) =
    K₃.subtype (ι₃ ((e6LineChar ω i : Kˣ) : K))
  rw [← RingHom.comp_apply, hιι]

end Cocycle

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
