module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2ConjLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjLift
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.Steinberg

theorem e6LineChar_map {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (v : kˣ) :
    (fun i => Units.map ψ.toMonoidHom (e6LineChar v i)) =
      e6LineChar (Units.map ψ.toMonoidHom v) := by
  funext i
  by_cases hi : i = e6KacNode
  · subst hi
    rw [e6LineChar_kacNode, e6LineChar_kacNode]
  · rw [e6LineChar_of_ne _ hi, e6LineChar_of_ne _ hi, map_one]

section Cocycle


theorem tw_cocycle_mem_toralRootGroup_fin {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] (hp3 : p ≠ 3) (θ : k →+* k) (q : ℕ) (hθ : ∀ c, θ c = c ^ q) (hq : q % 3 = 2)
    {g0 : ModGL Tag.E6 k} (hg0 : g0 ∈ adjointGroup Tag.E6 k)
    (hF : twistHom TwistTag.E6 k θ g0 = g0 * canonicalRep (coxeterSystem Tag.E6) k e6W0Four)
    (u : Fin Tag.E6.rank → kˣ) (hu3 : ∀ l, u l ^ 3 = 1) (ha3 : ∀ j, e6RootParams u j ^ 3 = 1)
    {x : e6Data_valid.minGroup k} (hx : TwistedE6.sigma k θ x = x)
    {y : ModGL Tag.E6 k} (hy : y ∈ adjointGroup Tag.E6 k)
    (hxy : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      g0 * (y * rootDiagUnit Tag.E6 (e6RootParams u) * y⁻¹) * g0⁻¹) :
    y⁻¹ * twE6F0 k θ y ∈ toralRootGroup Tag.E6 k (e6RootParams u) := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : e6Data_valid.minGroup k →* ModGL Tag.E6 k,
      π = (adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k) := ⟨_, rfl⟩
  have hπa : ∀ g, π g = ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) := fun g => by
    rw [hπ]
    rfl
  set N := twE6NSc k with hN
  have hNπ : π N = canonicalRep (coxeterSystem Tag.E6) k e6W0Four := by
    rw [hπa]
    exact e6Isogeny_twE6NSc_eq
  obtain ⟨g1, hg1⟩ := e6Isogeny_surjective k ⟨g0, hg0⟩
  have hg1π : π g1 = g0 := by rw [hπa, hg1]
  set Fb := TwistedE6.sigma k θ with hFb
  have hFg1 : π (Fb g1) = twistHom TwistTag.E6 k θ g0 := by
    rw [hπa, hFb, e6Isogeny_sigma θ g1]
    show twistHom TwistTag.E6 k θ ((e6Isogeny k g1 : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
    rw [← hπa, hg1π]
  set ζ0 := (g1 * N)⁻¹ * Fb g1 with hζ0
  have hζ0c : ζ0 ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [← hπa, hζ0, map_mul, map_inv, map_mul, hg1π, hNπ, hFg1, hF, inv_mul_cancel]
  have hF1 : Fb g1 = g1 * N * ζ0 := by rw [hζ0]; group
  have hc0 := Subgroup.mem_center_iff.1 hζ0c
  set sh := g1⁻¹ * x * g1 with hsh
  have hFsh : twistSc θ sh = sh := by
    change N * Fb sh * N⁻¹ = sh
    have hNz : N * ζ0 * N⁻¹ = ζ0 := by rw [hc0 N, mul_inv_cancel_right]
    have hzs : ζ0⁻¹ * sh * ζ0 = sh := by rw [mul_assoc, hc0 sh, inv_mul_cancel_left]
    rw [hsh, map_mul, map_mul, map_inv, hx, hF1]
    calc N * ((g1 * N * ζ0)⁻¹ * x * (g1 * N * ζ0)) * N⁻¹
        = (N * ζ0 * N⁻¹)⁻¹ * (g1⁻¹ * x * g1) * (N * ζ0 * N⁻¹) := by group
      _ = g1⁻¹ * x * g1 := by rw [hNz, ← hsh, hzs]
  have hshπ : π sh = y * rootDiagUnit Tag.E6 (e6RootParams u) * y⁻¹ := by
    rw [hsh, map_mul, map_mul, map_inv, hg1π, hπa x, hxy]
    group
  set T := minTorus e6Data_valid k u with hT
  have hTπ : π T = rootDiagUnit Tag.E6 (e6RootParams u) := by
    rw [hπa, hT]
    exact e6Isogeny_minTorus u
  have hFT : twistSc θ T = T := twistSc_minTorus_of_pow_three_q θ q hθ hq u hu3
  obtain ⟨yl, hyl⟩ := e6Isogeny_surjective k ⟨y, hy⟩
  have hylπ : π yl = y := by rw [hπa, hyl]
  set z0 := (yl * T * yl⁻¹)⁻¹ * sh with hz0
  have hz0c : z0 ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [← hπa, hz0, map_mul, map_inv, map_mul, map_mul, map_inv, hylπ, hTπ, hshπ, inv_mul_cancel]
  have hsT : sh = yl * T * yl⁻¹ * z0 := by rw [hz0]; group
  have hFz0 : twistSc θ z0 = z0 := twistSc_center θ q hθ hq hz0c
  have hcomm := conj_comm_of_frobenius (twistSc θ) hsT hFsh hFT hFz0
  have hπc : π (yl⁻¹ * twistSc θ yl) = y⁻¹ * twE6F0 k θ y := by
    rw [map_mul, map_inv, hylπ, hπa (twistSc θ yl), e6Isogeny_twistSc_eq, ← hπa, hylπ]
  have hcC : y⁻¹ * twE6F0 k θ y ∈ toralCentralizer Tag.E6 k (e6RootParams u) := by
    refine mem_toralCentralizer.2 ⟨?_, ?_⟩
    · rw [← hπc, hπa]
      exact (e6Isogeny k _).2
    · have h1 : π (yl⁻¹ * twistSc θ yl) * π T = π T * π (yl⁻¹ * twistSc θ yl) := by
        rw [← map_mul, ← map_mul, hcomm]
      rw [hπc, hTπ] at h1
      rw [← h1, mul_inv_cancel_right]
  exact mem_toralRootGroup_of_commute_lift_char hp3 u ha3 hcC (by rw [← hπa]; exact hπc) hcomm

theorem tw_cocycle_mem_toralRootGroup_threeA2 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6W0Four)
    {ω : Kˣ} (hω3 : ω ^ 3 = 1) {z : ModGL Tag.E6 K} (hz : z ∈ twistedE6RootGroup K σ)
    {y : ModGL Tag.E6 (AlgebraicClosure K)} (hy : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hzy : baseChangeGL (algebraMap K (AlgebraicClosure K)) z =
      g0 * (y * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (rootDiagUnit Tag.E6 (e6LineChar ω)) * y⁻¹) * g0⁻¹) :
    y⁻¹ * twE6F0 (AlgebraicClosure K) Fr y ∈ toralRootGroup Tag.E6 (AlgebraicClosure K)
      (fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (e6LineChar ω i)) := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hKp : CharP K p :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP L p := charP_of_injective_algebraMap ι.injective p
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (show f ≠ 0 by omega))
    omega
  obtain ⟨Eg, hEg⟩ := exists_finset_descent hg0C
  obtain ⟨Ey, hEy⟩ := exists_finset_descent hy
  obtain ⟨K₃, hK₃, hSK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K) (Eg ∪ Ey)
  haveI : Finite K₃ := hK₃
  have hgK : (Eg : Set L) ⊆ K₃ := fun x hx =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_left _ hx))
  have hyK : (Ey : Set L) ⊆ K₃ := fun x hx =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_right _ hx))
  have hιK : ∀ x : K, ι x ∈ K₃ := fun x => hιK₃ ⟨x, rfl⟩
  obtain ⟨g3, hg3C, hg3⟩ := hEg K₃ hgK
  obtain ⟨y3, hy3C, hy3⟩ := hEy K₃ hyK
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K →+* K₃, K₃.subtype.comp ι₃ = ι :=
    ⟨ι.codRestrict K₃ hιK, RingHom.ext fun x => rfl⟩
  haveI : CharP K₃ p := Subfield.charP K₃ p
  obtain ⟨φ, hφdef⟩ : ∃ φ : K₃ →+* K₃, φ = iterateFrobenius K₃ p f := ⟨_, rfl⟩
  have hφq : ∀ c : K₃, φ c = c ^ (p ^ f) := fun c => by
    rw [hφdef, iterateFrobenius_def]
  have hφL : K₃.subtype.comp φ = Fr.comp K₃.subtype := by
    ext c
    simp only [RingHom.comp_apply, Subfield.coe_subtype, hφq, hFr, map_pow]
  have hφι : φ.comp ι₃ = ι₃.comp σ.toRingHom := by
    ext c
    simp only [RingHom.comp_apply, hφq, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ,
      map_pow]
  have hbcinj : Function.Injective (baseChangeGL (τ := Tag.E6) K₃.subtype) :=
    baseChangeGL_injective K₃.subtype
  have hbcι : ∀ x : ModGL Tag.E6 K, baseChangeGL K₃.subtype (baseChangeGL ι₃ x) =
      baseChangeGL ι x := fun x => by
    rw [baseChangeGL_baseChangeGL, hιι]
  have hF₃ : twistHom TwistTag.E6 K₃ φ g3 =
      g3 * canonicalRep (coxeterSystem Tag.E6) K₃ e6W0Four := by
    apply hbcinj
    have h1 := twistHom_baseChangeGL (t := TwistTag.E6) K₃.subtype (σk := φ) (σ := Fr) hφL g3
    have e1 : baseChangeGL K₃.subtype (twistHom TwistTag.E6 K₃ φ g3) =
        twistHom TwistTag.E6 L Fr g0 :=
      h1.symm.trans (congrArg (twistHom TwistTag.E6 L Fr) hg3)
    have e2 : baseChangeGL K₃.subtype (g3 * canonicalRep (coxeterSystem Tag.E6) K₃ e6W0Four) =
        g0 * canonicalRep (coxeterSystem Tag.E6) L e6W0Four := by
      rw [map_mul, baseChangeGL_canonicalRep, hg3]
    exact e1.trans (hF.trans e2.symm)
  set ω₃ : K₃ˣ := Units.map ι₃.toMonoidHom ω with hω₃
  set u₃ : Fin Tag.E6.rank → K₃ˣ := fun l => ω₃ ^ e6KacCoweight l with hu₃
  have hu₃a : e6RootParams u₃ = e6LineChar ω₃ := cartanChar_e6KacCoweight ω₃
  have hω₃3 : ω₃ ^ 3 = 1 := by rw [hω₃, ← map_pow, hω3, map_one]
  have hu₃3 : ∀ l, u₃ l ^ 3 = 1 := fun l => by
    rw [hu₃, ← pow_mul, mul_comm, pow_mul, hω₃3, one_pow]
  have ha₃3 : ∀ j, e6RootParams u₃ j ^ 3 = 1 := fun j => by
    rw [hu₃a]
    exact e6LineChar_pow_three hω₃3 j
  have htup : (fun i => Units.map K₃.subtype.toMonoidHom (e6RootParams u₃ i)) =
      fun i => Units.map ι.toMonoidHom (e6LineChar ω i) := by
    rw [hu₃a, hω₃, ← e6LineChar_map]
    funext i
    apply Units.ext
    change K₃.subtype (ι₃ _) = ι _
    rw [← RingHom.comp_apply, hιι]
  obtain ⟨s, hsσ, hsπ⟩ := tw_exists_sigma_fixed_lift hp hf hK σ hσ hz
  set x := minBC e6Data_valid ι₃ s with hxdef
  have hxF : TwistedE6.sigma K₃ φ x = x := by
    rw [hxdef, twl_sigma_minBC ι₃ σ.toRingHom φ hφι, hsσ]
  have hxπ : ((e6Isogeny K₃ x : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      baseChangeGL ι₃ z := by
    rw [hxdef, e6Isogeny_minBC, hsπ]
  have hd : baseChangeGL K₃.subtype (rootDiagUnit Tag.E6 (e6RootParams u₃)) =
      baseChangeGL ι (rootDiagUnit Tag.E6 (e6LineChar ω)) := by
    rw [baseChangeGL_rootDiagUnit, baseChangeGL_rootDiagUnit, htup]
  have hπ : ((e6Isogeny K₃ x : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      g3 * (y3 * rootDiagUnit Tag.E6 (e6RootParams u₃) * y3⁻¹) * g3⁻¹ := by
    apply hbcinj
    rw [hxπ, hbcι, hzy, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hg3, hy3, hd]
  have hc3 := tw_cocycle_mem_toralRootGroup_fin hp3 φ (p ^ f) hφq hq hg3C hF₃ u₃ hu₃3 ha₃3 hxF
    hy3C hπ
  have hM := baseChangeGL_mem_toralRootGroup K₃.subtype hc3
  have hbcF : baseChangeGL K₃.subtype (y3⁻¹ * twE6F0 K₃ φ y3) = y⁻¹ * twE6F0 L Fr y := by
    rw [map_mul, map_inv, hy3, baseChangeGL_twE6F0 K₃.subtype hφL, hy3]
  rw [hbcF, htup] at hM
  exact hM

end Cocycle

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
