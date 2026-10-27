module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Steinberg.Minuscule.MinData (toWeight reflectWeight)

set_option linter.unusedSectionVars false

section Class


@[expose] def twPhi {k : Type} [Field k] (Fr : k →+* k) (ω : List (Fin Tag.E6.rank))
    (u : Fin Tag.E6.rank → kˣ) : Fin Tag.E6.rank → kˣ :=
  ω.foldr e6StarS (fun l => Units.map Fr.toMonoidHom (u (e6RhoFour l)))

theorem twPhi_map {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (Fr : k →+* k)
    (Fr' : k' →+* k') (h : ψ.comp Fr = Fr'.comp ψ) (ω : List (Fin Tag.E6.rank))
    (u : Fin Tag.E6.rank → kˣ) :
    twPhi Fr' ω (fun l => Units.map ψ.toMonoidHom (u l)) =
      fun l => Units.map ψ.toMonoidHom (twPhi Fr ω u l) := by
  have e : (fun l => Units.map Fr'.toMonoidHom (Units.map ψ.toMonoidHom (u (e6RhoFour l)))) =
      fun l => Units.map ψ.toMonoidHom (Units.map Fr.toMonoidHom (u (e6RhoFour l))) := by
    funext l
    apply Units.ext
    exact (RingHom.congr_fun h ((u (e6RhoFour l) : kˣ) : k)).symm
  unfold twPhi
  rw [e, twl_foldr_e6StarS_map]

theorem e6RootParams_mul' {K : Type} [Field K] (u v : Fin Tag.E6.rank → Kˣ) :
    e6RootParams (u * v) = e6RootParams u * e6RootParams v := by
  funext j
  simp only [e6RootParams, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem twPhi_lang {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (ω : List (Fin Tag.E6.rank)) (z : Fin Tag.E6.rank → Lˣ) :
    ∃ u : Fin Tag.E6.rank → Lˣ, twPhi Fr ω u = u * z := by
  classical
  set ν : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
    fun l => ω.foldl (fun ν j => reflectWeight j ν) (Pi.single l 1) with hν
  have hfold : ∀ (a : Fin Tag.E6.rank → Lˣ) (l : Fin Tag.E6.rank),
      ω.foldr e6StarS a l = ∏ j, a j ^ ν l j := fun a l => by
    have h1 : e6WtEval (ω.foldr e6StarS a) (Pi.single l 1) = ω.foldr e6StarS a l := by
      simp [e6WtEval, Pi.single_apply]
    rw [← h1, e6WtEval_foldr]
    rfl
  have hPhi : ∀ (a : Fin Tag.E6.rank → Lˣ) (l : Fin Tag.E6.rank),
      twPhi Fr ω a l = ∏ j, a j ^ ((q : ℤ) * ν l (e6RhoFour j)) := fun a l => by
    unfold twPhi
    rw [hfold]
    have e : ∀ j, (Units.map Fr.toMonoidHom (a (e6RhoFour j))) ^ ν l j =
        (fun j' => a j' ^ ((q : ℤ) * ν l (e6RhoFour j'))) (e6RhoFour j) := fun j => by
      have h : Units.map Fr.toMonoidHom (a (e6RhoFour j)) = a (e6RhoFour j) ^ q :=
        Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
      simp only [e6RhoFour_apply_apply]
      rw [h, ← zpow_natCast, ← zpow_mul]
    rw [Finset.prod_congr rfl fun j _ => e j]
    exact Equiv.prod_comp e6RhoFour (fun j' => a j' ^ ((q : ℤ) * ν l (e6RhoFour j')))
  set N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
    Matrix.of fun l j => (Pi.single l 1 : Fin Tag.E6.rank → ℤ) j -
      (q : ℤ) * ν l (e6RhoFour j) with hN
  have hNdet : N.det ≠ 0 := by
    refine det_ne_zero_of_mapMatrix_eq_one hq ?_
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hN, Matrix.of_apply, map_sub, map_mul,
      map_natCast, ZMod.natCast_self, zero_mul, sub_zero, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  obtain ⟨a, ha⟩ := exists_rootChar_rows_eq (τ := Tag.E6) (L := L) hNdet (fun l => (z l)⁻¹)
  refine ⟨a, funext fun l => ?_⟩
  have h1 := ha l
  have hsingle : ∏ j, a j ^ (Pi.single l 1 : Fin Tag.E6.rank → ℤ) j = a l := by
    rw [Finset.prod_eq_single l (fun j _ hj => by simp [Pi.single_apply, hj])
      (fun h => absurd (Finset.mem_univ l) h)]
    simp
  have h2 : FourGroupChevalley.rootChar a (N l) = a l / twPhi Fr ω a l := by
    simp only [FourGroupChevalley.rootChar, hN, Matrix.of_apply, zpow_sub, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib]
    rw [hPhi, hsingle, div_eq_mul_inv]
  rw [h2, div_eq_iff_eq_mul] at h1
  rw [Pi.mul_apply, h1, mul_comm ((z l)⁻¹) (twPhi Fr ω a l), mul_assoc, inv_mul_cancel, mul_one]

theorem exists_finite_subfield_frob {p f : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (S : Finset (AlgebraicClosure K)) :
    ∃ (K₃ : Subfield (AlgebraicClosure K)) (_ : Finite K₃) (ι₃ : K →+* K₃) (φ : K₃ →+* K₃),
      (S : Set (AlgebraicClosure K)) ⊆ K₃ ∧
      K₃.subtype.comp ι₃ = algebraMap K (AlgebraicClosure K) ∧
      (∀ c : K₃, φ c = c ^ (p ^ f)) ∧ K₃.subtype.comp φ = Fr.comp K₃.subtype ∧
      φ.comp ι₃ = ι₃.comp σ.toRingHom := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hKp : CharP K p :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨K₃, hK₃, hSK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K) S
  haveI : Finite K₃ := hK₃
  have hιK : ∀ x : K, algebraMap K (AlgebraicClosure K) x ∈ K₃ := fun x => hιK₃ ⟨x, rfl⟩
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K →+* K₃,
      K₃.subtype.comp ι₃ = algebraMap K (AlgebraicClosure K) :=
    ⟨(algebraMap K (AlgebraicClosure K)).codRestrict K₃ hιK, RingHom.ext fun x => rfl⟩
  haveI : CharP K₃ p := Subfield.charP K₃ p
  obtain ⟨φ, hφdef⟩ : ∃ φ : K₃ →+* K₃, φ = iterateFrobenius K₃ p f := ⟨_, rfl⟩
  have hφq : ∀ c : K₃, φ c = c ^ (p ^ f) := fun c => by
    rw [hφdef, iterateFrobenius_def]
  refine ⟨K₃, hK₃, ι₃, φ, hSK₃, hιι, hφq, ?_, ?_⟩
  · ext c
    simp only [RingHom.comp_apply, Subfield.coe_subtype, hφq, hFr, map_pow]
  · ext c
    simp only [RingHom.comp_apply, hφq, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ,
      map_pow]

theorem tw_torus_conj_fixed {p f : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    {ω : List (Fin Tag.E6.rank)} (hω : (coxeterSystem Tag.E6).IsReduced ω)
    (u z : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) (hΦ : twPhi Fr ω u = u * z)
    (hz : e6RootParams z = 1) :
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr (rootDiagUnit Tag.E6 (e6RootParams u)) =
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
          ((coxeterSystem Tag.E6).wordProd ω))⁻¹ * rootDiagUnit Tag.E6 (e6RootParams u) *
        canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
          ((coxeterSystem Tag.E6).wordProd ω) := by
  classical
  set L := AlgebraicClosure K with hL
  obtain ⟨K₃, hK₃, ι₃, φ, hSK₃, hιι, hφq, hφL, hφι⟩ := exists_finite_subfield_frob hp hK σ hσ Fr hFr
    (Finset.univ.image fun l => ((u l : Lˣ) : L))
  haveI : Finite K₃ := hK₃
  have huK : ∀ l, ((u l : Lˣ) : L) ∈ K₃ := fun l =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_image.2 ⟨l, Finset.mem_univ l, rfl⟩))
  obtain ⟨u₃, hu₃⟩ : ∃ u₃ : Fin Tag.E6.rank → K₃ˣ,
      ∀ l, Units.map K₃.subtype.toMonoidHom (u₃ l) = u l :=
    ⟨fun l => Units.mk0 ⟨((u l : Lˣ) : L), huK l⟩
      fun h0 => (u l).ne_zero (congrArg Subtype.val h0), fun l => Units.ext rfl⟩
  have hu₃' : (fun l => Units.map K₃.subtype.toMonoidHom (u₃ l)) = u := funext hu₃
  set z₃ : Fin Tag.E6.rank → K₃ˣ := fun l => (u₃ l)⁻¹ * twPhi φ ω u₃ l with hz₃
  have hΦ₃ : twPhi φ ω u₃ = u₃ * z₃ := by
    funext l
    simp [hz₃]
  have hzz₃ : (fun l => Units.map K₃.subtype.toMonoidHom (z₃ l)) = z := by
    have h1 := twPhi_map K₃.subtype φ Fr hφL ω u₃
    rw [hu₃'] at h1
    funext l
    have h3 : twPhi Fr ω u l = Units.map K₃.subtype.toMonoidHom (twPhi φ ω u₃ l) := congrFun h1 l
    have h2 : twPhi Fr ω u l = u l * z l := by rw [hΦ]; rfl
    have h4 : Units.map K₃.subtype.toMonoidHom (twPhi φ ω u₃ l) = u l * z l := h3.symm.trans h2
    simp only [hz₃, map_mul, map_inv, hu₃]
    rw [h4]
    group
  have hz₃1 : e6RootParams z₃ = 1 := by
    have h1 : (fun j => Units.map K₃.subtype.toMonoidHom (e6RootParams z₃ j)) = e6RootParams z := by
      rw [← e6RootParams_map', hzz₃]
    rw [hz] at h1
    funext j
    exact units_map_subtype_injective K₃ (by
      have := congrFun h1 j
      simpa using this)
  set N₃ := canonicalRep (coxeterSystem Tag.E6) K₃ ((coxeterSystem Tag.E6).wordProd ω) with hN₃
  set t₃ := rootDiagUnit Tag.E6 (e6RootParams u₃) with ht₃
  have hT : ((e6Isogeny K₃ (minTorus e6Data_valid K₃ u₃) : adjointGroup Tag.E6 K₃) :
      ModGL Tag.E6 K₃) = t₃ := e6Isogeny_minTorus u₃
  have hσT : ((e6Isogeny K₃ (TwistedE6.sigma K₃ φ (minTorus e6Data_valid K₃ u₃)) :
      adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = twistHom TwistTag.E6 K₃ φ t₃ := by
    rw [e6Isogeny_sigma φ]
    show twistHom TwistTag.E6 K₃ φ
      ((e6Isogeny K₃ (minTorus e6Data_valid K₃ u₃) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = _
    rw [hT]
  have hn : ((e6Isogeny K₃ (e6NWord K₃ ω) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = N₃ :=
    e6Isogeny_nWord_eq_canonicalRep hω
  have hconj : e6NWord K₃ ω * TwistedE6.sigma K₃ φ (minTorus e6Data_valid K₃ u₃) *
      (e6NWord K₃ ω)⁻¹ = minTorus e6Data_valid K₃ (twPhi φ ω u₃) := by
    rw [twl_sigma_minTorus, nWord_conj_minTorus]
    rfl
  set Ft : ModGL Tag.E6 K₃ := ((e6Isogeny K₃ (TwistedE6.sigma K₃ φ (minTorus e6Data_valid K₃ u₃)) :
      adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) with hFt
  have hFt' : Ft = N₃⁻¹ * t₃ * N₃ := by
    have h1 := congrArg (fun g : e6Data_valid.minGroup K₃ =>
      ((e6Isogeny K₃ g : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃)) hconj
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hn, e6Isogeny_minTorus, hΦ₃, e6RootParams_mul', hz₃1, mul_one] at h1
    calc Ft = N₃⁻¹ * (N₃ * Ft * N₃⁻¹) * N₃ := by group
      _ = N₃⁻¹ * t₃ * N₃ := by rw [h1]
  have hid₃ : twistHom TwistTag.E6 K₃ φ t₃ = N₃⁻¹ * t₃ * N₃ := hσT.symm.trans hFt'
  have e2 : baseChangeGL K₃.subtype t₃ = rootDiagUnit Tag.E6 (e6RootParams u) := by
    rw [ht₃, baseChangeGL_rootDiagUnit]
    have hd : (fun i => Units.map K₃.subtype.toMonoidHom (e6RootParams u₃ i)) =
        e6RootParams u := by
      rw [← e6RootParams_map', hu₃']
    rw [hd]
  have e3 := twistHom_baseChangeGL (t := TwistTag.E6) K₃.subtype (σk := φ) (σ := Fr)
    (by rw [hφL]) t₃
  have e1 := congrArg (baseChangeGL (τ := Tag.E6) K₃.subtype) hid₃
  have e4 : baseChangeGL K₃.subtype (N₃⁻¹ * t₃ * N₃) =
      (canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω))⁻¹ *
        rootDiagUnit Tag.E6 (e6RootParams u) *
          canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω) := by
    rw [map_mul, map_mul, map_inv, hN₃, baseChangeGL_canonicalRep, e2]
  exact (congrArg (twistHom TwistTag.E6 L Fr) e2.symm).trans (e3.trans (e1.trans e4))

theorem exists_primCubeRoot_of_charP {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} [Fact p.Prime]
    [CharP L p] (hp3 : p ≠ 3) : ∃ ζ : Lˣ, IsPrimitiveRoot (ζ : L) 3 := by
  have hne3 : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have : p ∣ 3 := (CharP.cast_eq_zero_iff L p 3).1 h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 this)
  haveI : NeZero ((3 : ℕ) : L) := ⟨hne3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hζu : IsUnit ζ := hζ.isUnit (by norm_num)
  exact ⟨hζu.unit, by rw [IsUnit.unit_spec]; exact hζ⟩

@[expose] def e6CenterExp : Fin Tag.E6.rank → ℤ := ![1, 0, 2, 0, 1, 2]

theorem e6CenterExp_cartan : ∀ j : Fin Tag.E6.rank,
    (3 : ℤ) ∣ ∑ l, Tag.E6.cartan l j * e6CenterExp l := by
  decide +kernel

theorem e6RootParams_center {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    e6RootParams (fun l => ζ ^ e6CenterExp l) = 1 := by
  funext j
  simp only [e6RootParams, Pi.one_apply]
  rw [show (∏ l, (ζ ^ e6CenterExp l) ^ Tag.E6.cartan l j) =
      ζ ^ (∑ l, Tag.E6.cartan l j * e6CenterExp l) by
    rw [← liftProd_zpow_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← zpow_mul, mul_comm]]
  exact (zpow_eq_zpow_of_dvd hζ (a := ∑ l, Tag.E6.cartan l j * e6CenterExp l) (b := 0)
    (by simpa using e6CenterExp_cartan j)).trans (zpow_zero ζ)

theorem tw_exists_class_element {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (g0 : ModGL Tag.E6 (AlgebraicClosure K)) (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    {ω : List (Fin Tag.E6.rank)} (hω : (coxeterSystem Tag.E6).IsReduced ω)
    (hF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        ((coxeterSystem Tag.E6).wordProd ω)) :
    ∃ t ∈ torusGroup Tag.E6 (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr t =
        (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
            ((coxeterSystem Tag.E6).wordProd ω))⁻¹ * t *
          canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
            ((coxeterSystem Tag.E6).wordProd ω) ∧
      g0 * t * g0⁻¹ ∉ (twistedE6RootGroup K σ).map
        (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hKp : CharP K p :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨ζ, hζ⟩ := exists_primCubeRoot_of_charP (L := AlgebraicClosure K) hp3
  have hζ3 : ζ ^ 3 = 1 := Units.ext (by simpa using hζ.pow_eq_one)
  obtain ⟨u, hu⟩ := twPhi_lang (L := AlgebraicClosure K) hq2 hFr ω (fun l => ζ ^ e6CenterExp l)
  refine ⟨rootDiagUnit Tag.E6 (e6RootParams u), rootDiagUnit_mem_torusGroup _,
    tw_torus_conj_fixed hp hK σ hσ Fr hFr hω u _ hu (e6RootParams_center hζ3), ?_⟩
  intro hmem
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hmem
  have key := tw_class_trivial_of_mem hp hf hK σ hσ hq Fr hFr g0 hg0C hω hF u hy hyeq
  have h1 : u * (fun l => ζ ^ e6CenterExp l) = u := by
    rw [← hu]
    exact key
  have h2 : (fun l => ζ ^ e6CenterExp l) = 1 := mul_left_cancel (h1.trans (mul_one u).symm)
  have h3 : ζ ^ e6CenterExp 0 = 1 := congrFun h2 0
  have h4 : ζ = 1 := by simpa [e6CenterExp] using h3
  exact hζ.ne_one (by norm_num) (by rw [h4]; simp)

end Class

end CFSG.LieType.SeitzGeneration.ExcHighThree
