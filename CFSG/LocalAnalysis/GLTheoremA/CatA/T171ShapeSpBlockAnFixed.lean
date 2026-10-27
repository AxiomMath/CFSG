module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockComm
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneFixed
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269SBlk
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpAsmAnalysis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem indAut_mem_inner_of_inducesInnerMod {G : Type} [Group G] {p : ℕ} {L : Subgroup G}
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (hin : InducesInnerMod p L a) :
    CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L a ha ∈ inner (PSimple p L) := by
  have ha' : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ ha
  have hinv : (⟨a⁻¹, ha'⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨a, ha⟩)⁻¹ := rfl
  have hbar : barAut p L ⟨a⁻¹, ha'⟩ ∈ inner (PQuot p L) := by
    rw [hinv, map_inv]
    exact Subgroup.inv_mem _ ((inducesInnerMod_iff_barAut_mem_inner ha).1 hin)
  obtain ⟨k, hk⟩ := hbar
  refine ⟨QuotientGroup.mk' (Subgroup.center (PQuot p L)) k, ?_⟩
  show MulAut.conj (QuotientGroup.mk' (Subgroup.center (PQuot p L)) k) =
    CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L a ha
  unfold CFSG.LocalAnalysis.GLTheoremA.MI.indAut
  show MulAut.conj (QuotientGroup.mk' (Subgroup.center (PQuot p L)) k) =
    chevAut p L ⟨a⁻¹, ha'⟩
  rw [chevAut, MonoidHom.comp_apply, ← hk]
  exact (centerQuotient_conj k).symm

noncomputable def fixedRestrict {m : ℕ} {K : Type} [Field K] {x y : StatedSp m K}
    (h : Commute y x) :
    primaryComponent (spEnd x) (X - 1) ≃ₗ[K] primaryComponent (spEnd x) (X - 1) where
  toFun v := ⟨spEnd y (v : Fin m ⊕ Fin m → K),
    spEnd_mapsTo_primaryComponent h (X - 1) v.2⟩
  invFun v := ⟨spEnd y⁻¹ (v : Fin m ⊕ Fin m → K),
    spEnd_mapsTo_primaryComponent (Commute.inv_left h) (X - 1) v.2⟩
  left_inv v := by
    apply Subtype.ext
    show spEnd y⁻¹ (spEnd y (v : Fin m ⊕ Fin m → K)) = (v : Fin m ⊕ Fin m → K)
    rw [← Module.End.mul_apply, ← CFSG.RankThree.PartOne.KCSpFull.spEnd_mul, inv_mul_cancel,
      CFSG.RankThree.PartOne.KCSpFull.spEnd_one]
    rfl
  right_inv v := by
    apply Subtype.ext
    show spEnd y (spEnd y⁻¹ (v : Fin m ⊕ Fin m → K)) = (v : Fin m ⊕ Fin m → K)
    rw [← Module.End.mul_apply, ← CFSG.RankThree.PartOne.KCSpFull.spEnd_mul, mul_inv_cancel,
      CFSG.RankThree.PartOne.KCSpFull.spEnd_one]
    rfl
  map_add' u v := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
  map_smul' c v := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]

theorem fixedRestrict_mem_sesq {m : ℕ} {K : Type} [Field K] {x y : StatedSp m K}
    (h : Commute y x) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv (fixedRestrict h) ∈
      sesqUnitaryGroup ((spForm m K).restrict (primaryComponent (spEnd x) (X - 1))) := by
  intro u v
  exact mem_sesqUnitaryGroup.mp (spLin_mem y) _ _

theorem fixedRestrict_pow_apply {m : ℕ} {K : Type} [Field K] {x y : StatedSp m K}
    (h : Commute y x) (k : ℕ) (v : primaryComponent (spEnd x) (X - 1)) :
    (((fixedRestrict h) ^ k) v : Fin m ⊕ Fin m → K) = spEnd (y ^ k) v := by
  induction k generalizing v with
  | zero =>
    rw [pow_zero y, CFSG.RankThree.PartOne.KCSpFull.spEnd_one]
    rfl
  | succ k ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih (fixedRestrict h v), pow_succ,
      CFSG.RankThree.PartOne.KCSpFull.spEnd_mul, Module.End.mul_apply]
    rfl

theorem ofLinearEquiv_pow {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (k : ℕ) :
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e) ^ k =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (e ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Units.ext rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]

theorem spSupported_X_sub_one_eq_bot {m : ℕ} {K : Type} [Field K] {x : StatedSp m K}
    (hsq : Squarefree (minpoly K (spEnd x))) (hd : spFixedDim x = 0) :
    spSupported x ({X - 1} : Set K[X]) = ⊥ := by
  have hV : primaryComponent (spEnd x) (X - 1) = ⊥ := Submodule.finrank_eq_zero.mp hd
  have hmem : (X - 1 : K[X]) ∉ primaryFactors (spEnd x) := fun h =>
    primaryComponent_ne_bot hsq h hV
  rw [eq_bot_iff]
  intro g hg
  have hfix : ∀ k ∈ primaryFactors (spEnd x), ∀ v ∈ primaryComponent (spEnd x) k,
      spEnd g v = v := by
    intro k hk v hv
    exact (mem_spSupported.mp hg).2 k hk (by rintro rfl; exact hmem hk) v hv
  have h1 : spEnd g = 1 :=
    ext_primaryComponent hsq (fun k hk v hv => by simpa using hfix k hk v hv)
  have h2 : spEnd g = spEnd (1 : StatedSp m K) := by
    rw [h1]
    exact (CFSG.RankThree.PartOne.KCSpFull.spEnd_one).symm
  exact Subgroup.mem_bot.mpr (spEnd_injective h2)

theorem spFixedFactor_commutator_eq_self {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : StatedSp m K} (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hblocks : SpPrimaryBlocks 2 n p x (proj m K x))
    (hd0 : spFixedDim x ≠ 0) (hd2 : spFixedDim x ≠ 2)
    (h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2)) :
    ⁅spSupported x ({X - 1} : Set K[X]), spSupported x ({X - 1} : Set K[X])⁆ =
      spSupported x ({X - 1} : Set K[X]) := by
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      have h2c := Finite.one_lt_card (α := K)
      omega
    · exact h0
  have hlist : SpFixedListed x := by
    obtain ⟨s, hs, -⟩ := hblocks.rank
    refine ⟨?_, ?_⟩
    · rw [show spFixedDim x = 2 * s from hs]
      have hspos : 0 < 2 * s := by
        have h := Nat.pos_of_ne_zero hd0
        rwa [show spFixedDim x = 2 * s from hs] at h
      omega
    · rintro ⟨h2, -⟩
      exact hd2 h2
  have hq := spFixedFactor_isQuasisimple (ℓ := 2) (f := n) hK Nat.prime_two hn1 hblocks hlist h42
  have hperf : commutator ↥(spSupported x ({X - 1} : Set K[X])) = ⊤ := hq.1.commutator_eq_top
  rw [← Subgroup.map_subtype_commutator (spSupported x ({X - 1} : Set K[X])), hperf,
    Subgroup.map_top, Subgroup.range_subtype]

theorem spFixedFactor_mem_commutator_of_four_two {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : StatedSp m K} (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hblocks : SpPrimaryBlocks 2 n p x (proj m K x))
    (hd4 : spFixedDim x = 4) (hK2 : Nat.card K = 2)
    {u : StatedSp m K} (hu : u ∈ spSupported x ({X - 1} : Set K[X])) (hup : u ^ p = 1) :
    u ∈ ⁅spSupported x ({X - 1} : Set K[X]), spSupported x ({X - 1} : Set K[X])⁆ := by
  obtain ⟨-, hodd⟩ := spFixed_four_two hK2 hblocks hd4
  exact hodd hp hp2 u hu hup

theorem spFixedFactor_commutator_commutative_of_two_two {m n p : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : StatedSp m K} (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hblocks : SpPrimaryBlocks 2 n p x (proj m K x))
    (hd2 : spFixedDim x = 2) (hK2 : Nat.card K = 2) :
    IsMulCommutative ↥⁅spSupported x ({X - 1} : Set K[X]),
      spSupported x ({X - 1} : Set K[X])⁆ := by
  classical
  have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) :=
    X_sub_one_mem_primaryFactors x (by omega)
  obtain ⟨φ, -⟩ := hblocks.fixedFactor hmem
  have hB : ((spForm m K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin m ⊕ Fin m → K)
  obtain ⟨s', hs', ⟨e⟩⟩ :=
    exists_mulEquiv_sesqUnitaryGroup_statedSp hB hblocks.fixed_nondegenerate
  have hs1 : s' = 1 := by
    have : Module.finrank K (primaryComponent (spEnd x) (X - 1)) = 2 := hd2
    omega
  subst hs1
  set F := spSupported x ({X - 1} : Set K[X]) with hF
  have hsolvSp : Group.IsSolvable (StatedSp 1 K) :=
    CFSG.AGLEmbedding.LeviBlock.spFlag_isSolvable_Sp (K := K) (m := 1) (Or.inr ⟨rfl, hK2⟩)
  have hsolvF : Group.IsSolvable ↥F :=
    Group.isSolvable_of_isSolvable_injective (f := (φ.trans e).toMonoidHom)
      (φ.trans e).injective
  have hcard : Nat.card ↥F = 6 := by
    have h := card_spFixedFactor_of_dim_two hblocks hd2
    have hF' : F = spFixedFactor x := rfl
    rw [hF', h, hK2]
    norm_num
  have hnotperf : ¬ Group.IsPerfect ↥F := by
    intro hperf
    haveI : Nontrivial ↥F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
    haveI := hperf
    exact Group.IsPerfect.not_isSolvable _ hsolvF
  have hDne : ⁅F, F⁆ ≠ F := by
    intro hEq
    apply hnotperf
    rw [Group.isPerfect_def]
    refine Subgroup.map_injective F.subtype_injective ?_
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_subtype_commutator F, hEq]
  have hlt : ⁅F, F⁆ < F := lt_of_le_of_ne (Subgroup.commutator_le_self F) hDne
  have hcardD : Nat.card ↥⁅F, F⁆ < 6 := by
    have hle' : Nat.card ↥⁅F, F⁆ ≤ Nat.card ↥F := Subgroup.card_le_of_le hlt.le
    have hne' : Nat.card ↥⁅F, F⁆ ≠ Nat.card ↥F := by
      intro hc
      exact hDne (Subgroup.eq_of_le_of_card_ge hlt.le (le_of_eq hc.symm))
    have h1 : Nat.card ↥⁅F, F⁆ < Nat.card ↥F := lt_of_le_of_ne hle' hne'
    rwa [hcard] at h1
  have hdvd : Nat.card ↥⁅F, F⁆ ∣ 6 := by
    have h1 : Nat.card ↥((⁅F, F⁆).subgroupOf F) ∣ Nat.card ↥F :=
      Subgroup.card_subgroup_dvd_card ((⁅F, F⁆).subgroupOf F)
    have h2 : Nat.card ↥((⁅F, F⁆).subgroupOf F) = Nat.card ↥⁅F, F⁆ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self F)).toEquiv
    rwa [h2, hcard] at h1
  have hle : Nat.card ↥⁅F, F⁆ ≤ 3 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k
        · omega
        · omega
      · exact h
    have hmono : Nat.card ↥⁅F, F⁆ * 2 ≤ Nat.card ↥⁅F, F⁆ * k :=
      Nat.mul_le_mul_left _ hk2
    omega
  have hpos : 0 < Nat.card ↥⁅F, F⁆ := Nat.card_pos
  rcases (by omega : Nat.card ↥⁅F, F⁆ = 1 ∨ Nat.card ↥⁅F, F⁆ = 2 ∨
      Nat.card ↥⁅F, F⁆ = 3) with h1 | h1 | h1
  · haveI : Subsingleton ↥⁅F, F⁆ :=
      (Finite.card_le_one_iff_subsingleton (α := ↥⁅F, F⁆)).mp (by omega)
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · haveI : Fact (Nat.card ↥⁅F, F⁆).Prime := ⟨h1 ▸ Nat.prime_two⟩
    exact (isCyclic_of_prime_card (α := ↥⁅F, F⁆) rfl).isMulCommutative
  · haveI : Fact (Nat.card ↥⁅F, F⁆).Prime := ⟨h1 ▸ Nat.prime_three⟩
    exact (isCyclic_of_prime_card (α := ↥⁅F, F⁆) rfl).isMulCommutative

theorem exists_fixed_lift {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : StatedSp m K} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hblocks : SpPrimaryBlocks 2 n p x (proj m K x)) :
    ∃ u ∈ spSupported x ({X - 1} : Set K[X]), u ^ p = 1 ∧
      ∀ g ∈ spSupported x ({X - 1} : Set K[X]), u⁻¹ * g * u = y⁻¹ * g * y := by
  classical
  have hcomm : Commute y x := hxy.symm
  have hyC : y ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
  have hyinvC : y⁻¹ ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)) := Subgroup.inv_mem _ hyC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      have h2c := Finite.one_lt_card (α := K)
      omega
    · exact h0
  haveI hchar : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp |>.1 h0).symm
  by_cases hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)
  ·
    set V1 := primaryComponent (spEnd x) (X - 1) with hV1
    obtain ⟨φ, hφ⟩ := hblocks.fixedFactor hmem
    set y1 : LinearMap.GeneralLinearGroup K V1 :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv (fixedRestrict hcomm) with hy1def
    have hy1 : y1 ∈ sesqUnitaryGroup ((spForm m K).restrict V1) :=
      fixedRestrict_mem_sesq hcomm
    set u : StatedSp m K :=
      ((φ.symm ⟨y1, hy1⟩ : ↥(spSupported x ({X - 1} : Set K[X])))).1 with hudef
    have huF : u ∈ spSupported x ({X - 1} : Set K[X]) :=
      ((φ.symm ⟨y1, hy1⟩ : ↥(spSupported x ({X - 1} : Set K[X])))).2
    have hφu : φ ⟨u, huF⟩ = ⟨y1, hy1⟩ := φ.apply_symm_apply ⟨y1, hy1⟩
    have hy1p_lin : (fixedRestrict hcomm) ^ p = 1 := by
      ext v
      rw [fixedRestrict_pow_apply hcomm p v, hy,
        CFSG.RankThree.PartOne.KCSpFull.spEnd_one]
      rfl
    have hy1p : y1 ^ p = 1 := by
      rw [hy1def, ofLinearEquiv_pow, hy1p_lin]
      exact Units.ext rfl
    have hup : u ^ p = 1 := by
      have hsub : (⟨u, huF⟩ : ↥(spSupported x ({X - 1} : Set K[X]))) ^ p = 1 := by
        apply φ.injective
        rw [map_pow, map_one, hφu]
        exact Subtype.ext hy1p
      exact congrArg Subtype.val hsub
    refine ⟨u, huF, hup, ?_⟩
    intro g hg
    have hgyF : y⁻¹ * g * y ∈ spSupported x ({X - 1} : Set K[X]) := by
      have h := spFixedFactor_normalized x y⁻¹ hyinvC g hg
      simpa only [spFixedFactor, inv_inv] using h
    have hgC : Commute g x := by
      have h := spFixedFactor_le_centralizer x hg
      exact Subgroup.mem_centralizer_singleton_iff.mp h
    have huV : ∀ w : Fin m ⊕ Fin m → K, w ∈ V1 → spEnd u w = spEnd y w := by
      intro w hw
      have h1 := hφ ⟨u, huF⟩ ⟨w, hw⟩
      have h2 : (((y1 : LinearMap.GeneralLinearGroup K V1) : Module.End K V1)
          ⟨w, hw⟩ : Fin m ⊕ Fin m → K) = spEnd y w := by
        rw [hy1def]
        rfl
      calc spEnd u w
          = (((φ ⟨u, huF⟩ : LinearMap.GeneralLinearGroup K V1) : Module.End K V1)
              ⟨w, hw⟩ : Fin m ⊕ Fin m → K) := h1.symm
        _ = (((y1 : LinearMap.GeneralLinearGroup K V1) : Module.End K V1)
              ⟨w, hw⟩ : Fin m ⊕ Fin m → K) := by rw [hφu]
        _ = spEnd y w := h2
    have huinvV : ∀ w : Fin m ⊕ Fin m → K, w ∈ V1 → spEnd u⁻¹ w = spEnd y⁻¹ w := by
      intro w hw
      let y1inv : LinearMap.GeneralLinearGroup K V1 := y1⁻¹
      have hy1inv : y1inv =
          LinearMap.GeneralLinearGroup.ofLinearEquiv ((fixedRestrict hcomm)⁻¹) := by
        dsimp only [y1inv]
        rw [hy1def]
        rfl
      have h1 := hφ (⟨u, huF⟩⁻¹) ⟨w, hw⟩
      have h2 : ((y1inv : Module.End K V1) ⟨w, hw⟩ : Fin m ⊕ Fin m → K) = spEnd y⁻¹ w := by
        rw [hy1inv]
        rfl
      calc spEnd u⁻¹ w
          = (((φ (⟨u, huF⟩⁻¹) : LinearMap.GeneralLinearGroup K V1) : Module.End K V1)
              ⟨w, hw⟩ : Fin m ⊕ Fin m → K) := h1.symm
        _ = ((y1inv : Module.End K V1) ⟨w, hw⟩ : Fin m ⊕ Fin m → K) := by
            rw [show (⟨u, huF⟩⁻¹ : ↥(spSupported x ({X - 1} : Set K[X]))) = (⟨u, huF⟩)⁻¹ from rfl,
              map_inv, hφu]
            rfl
        _ = spEnd y⁻¹ w := h2
    let ginv : ↥(spSupported x ({X - 1} : Set K[X])) :=
      ⟨u⁻¹ * g * u, (spSupported x ({X - 1} : Set K[X])).mul_mem
        ((spSupported x ({X - 1} : Set K[X])).mul_mem
          ((spSupported x ({X - 1} : Set K[X])).inv_mem huF) hg) huF⟩
    let gy : ↥(spSupported x ({X - 1} : Set K[X])) := ⟨y⁻¹ * g * y, hgyF⟩
    have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hx).squarefree
    have hconjEnd : spEnd (u⁻¹ * g * u) = spEnd (y⁻¹ * g * y) := by
      apply ext_primaryComponent hsq
      intro k hk w hw
      by_cases hk1 : k = X - 1
      · subst k
        rw [CFSG.RankThree.PartOne.KCSpFull.spEnd_mul,
          CFSG.RankThree.PartOne.KCSpFull.spEnd_mul,
          CFSG.RankThree.PartOne.KCSpFull.spEnd_mul,
          CFSG.RankThree.PartOne.KCSpFull.spEnd_mul,
          Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
          huV w hw]
        exact huinvV _ (spEnd_mapsTo_primaryComponent hgC (X - 1)
          (spEnd_mapsTo_primaryComponent hcomm (X - 1) hw))
      · have h1 : spEnd (ginv : StatedSp m K) w = w :=
          (mem_spSupported.mp ginv.2).2 k hk (by simpa using hk1) w hw
        have h2 : spEnd (gy : StatedSp m K) w = w :=
          (mem_spSupported.mp gy.2).2 k hk (by simpa using hk1) w hw
        simpa [ginv, gy] using h1.trans h2.symm
    exact spEnd_injective hconjEnd
  ·
    have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hx).squarefree
    have hF : spSupported x ({X - 1} : Set K[X]) = ⊥ := by
      have hzero : spFixedDim x = 0 := by
        by_contra h0
        exact hmem (X_sub_one_mem_primaryFactors x (by omega))
      exact spSupported_X_sub_one_eq_bot hsq hzero
    refine ⟨1, ?_, one_pow p, ?_⟩
    · rw [hF]
      exact Subgroup.mem_bot.mpr rfl
    · intro g hg
      have hg1 : g = 1 := by
        rw [hF] at hg
        exact Subgroup.mem_bot.mp hg
      rw [hg1]
      group

theorem spFixedFactor_oddOrder_mem_commutator_or_commutative {m n p : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) {x : StatedSp m K} (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hblocks : SpPrimaryBlocks 2 n p x (proj m K x))
    {u : StatedSp m K} (hu : u ∈ spSupported x ({X - 1} : Set K[X])) (hup : u ^ p = 1) :
    u ∈ ⁅spSupported x ({X - 1} : Set K[X]), spSupported x ({X - 1} : Set K[X])⁆ ∨
      IsMulCommutative ↥⁅spSupported x ({X - 1} : Set K[X]),
        spSupported x ({X - 1} : Set K[X])⁆ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      have h2c := Finite.one_lt_card (α := K)
      omega
    · exact h0
  haveI hchar : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp |>.1 h0).symm
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hx).squarefree
  by_cases hd0 : spFixedDim x = 0
  · left
    have hF : spSupported x ({X - 1} : Set K[X]) = ⊥ := spSupported_X_sub_one_eq_bot hsq hd0
    have hu1 : u = 1 := by
      rw [hF] at hu
      exact Subgroup.mem_bot.mp hu
    rw [hu1]
    exact Subgroup.one_mem _
  by_cases hd2 : spFixedDim x = 2
  · by_cases hK2 : Nat.card K = 2
    · right
      exact spFixedFactor_commutator_commutative_of_two_two hK hm hp hp2 hx hx1 hblocks hd2 hK2
    · left
      have hlist : SpFixedListed x := by
        refine ⟨by omega, ?_⟩
        intro hc
        rcases hc with ⟨-, hq⟩
        rcases hq with h2 | h3
        · exact hK2 h2
        · haveI : CharP K 2 := hchar
          letI : Fintype K := Fintype.ofFinite K
          obtain ⟨m, -, hm⟩ := FiniteField.card K 2
          have hm' : Nat.card K = 2 ^ (m : ℕ) := by
            rw [Nat.card_eq_fintype_card, hm]
          rw [h3] at hm'
          have hm0 : (m : ℕ) ≠ 0 := m.pos.ne'
          have h2dvd : 2 ∣ 2 ^ (m : ℕ) := dvd_pow_self 2 hm0
          rw [← hm'] at h2dvd
          norm_num at h2dvd
      have h42' : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2) := fun h => by omega
      have hq := spFixedFactor_isQuasisimple (ℓ := 2) (f := n) hK Nat.prime_two hn1 hblocks
        hlist h42'
      change u ∈ ⁅spFixedFactor x, spFixedFactor x⁆
      rw [← Subgroup.map_subtype_commutator (spFixedFactor x),
        hq.1.commutator_eq_top, Subgroup.map_top, Subgroup.range_subtype]
      exact hu
  · by_cases h42 : spFixedDim x = 4 ∧ Nat.card K = 2
    · left
      exact spFixedFactor_mem_commutator_of_four_two hK hm hp hp2 hx hx1 hblocks h42.1 h42.2 hu hup
    · left
      rw [spFixedFactor_commutator_eq_self hK hm hp hp2 hx hx1 hblocks hd0 hd2 h42]
      exact hu

theorem inducesInnerMod_fixed {m p : ℕ} {K : Type} [Field K]
    {x y : StatedSp m K} {J : Subgroup (StatedProj (StatedSp m K))}
    (hJeq : J = (⁅spSupported x ({X - 1} : Set K[X]),
      spSupported x ({X - 1} : Set K[X])⁆).map (proj m K))
    {u : StatedSp m K}
    (huD : u ∈ ⁅spSupported x ({X - 1} : Set K[X]),
      spSupported x ({X - 1} : Set K[X])⁆)
    (hconj : ∀ g ∈ spSupported x ({X - 1} : Set K[X]), u⁻¹ * g * u = y⁻¹ * g * y) :
    InducesInnerMod p J (proj m K y) := by
  refine ⟨proj m K u, ?_, ?_⟩
  · rw [hJeq]
    exact Subgroup.mem_map_of_mem _ huD
  · intro z hz
    rw [hJeq] at hz
    obtain ⟨g, hgD, hgz⟩ := Subgroup.mem_map.mp hz
    have hgF : g ∈ spSupported x ({X - 1} : Set K[X]) :=
      Subgroup.commutator_le_self _ hgD
    have h1 : (proj m K u)⁻¹ * z * (proj m K u) =
        (proj m K y)⁻¹ * z * (proj m K y) := by
      rw [← hgz]
      calc (proj m K u)⁻¹ * proj m K g * proj m K u
          = proj m K (u⁻¹ * g * u) := by rw [map_mul, map_mul, map_inv]
        _ = proj m K (y⁻¹ * g * y) := by rw [hconj g hgF]
        _ = (proj m K y)⁻¹ * proj m K g * proj m K y := by rw [map_mul, map_mul, map_inv]
    rw [h1, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem spFixedBlockAnalysis_holds :
    ∀ {m n p : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 2 ^ n → 2 ≤ m →
      p.Prime → p ≠ 2 →
      ∀ (x y : StatedSp m K), x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ≠ 1 →
      ∀ J : Subgroup (StatedProj (StatedSp m K)),
        J = (⁅spSupported x ({X - 1} : Set K[X]), spSupported x ({X - 1} : Set K[X])⁆).map
          (proj m K) →
        (hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))) →
        MI.indAut p J (proj m K y) hN ∈
            CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) := by
  intro m n p K _ _ hK hm hp hp2 x y hxp hyp hxy hx1 J hJeq hN
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      have h2c := Finite.one_lt_card (α := K)
      omega
    · exact h0
  haveI hchar : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp |>.1 h0).symm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero m := ⟨by omega⟩
  have hm1 : 1 ≤ m := by omega
  have ha1 : proj m K x ≠ 1 := fun h1 =>
    hx1 ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := m) (K := K)).1 (by rw [h1, map_one]))
  have ha : orderOf (proj m K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) ha1
  have hxp' : orderOf x = p := orderOf_eq_prime hxp hx1
  have hblocks : SpPrimaryBlocks 2 n p x (proj m K x) :=
    (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := n) (p := p) (r := m)
      (K := K) Nat.prime_two hn1 hK hp hp2 hp2 hm1 (proj m K x) ha).2 x rfl hxp'
  by_cases hpJ : p ∣ Nat.card J
  · obtain ⟨u, huF, hup, hconj⟩ := exists_fixed_lift hK hm hp hp2 hxp hyp hxy hx1 hblocks
    rcases spFixedFactor_oddOrder_mem_commutator_or_commutative hK hm hp hp2 hxp hx1 hblocks
      huF hup with huD | hcomm
    · exact indAut_mem_inner_of_inducesInnerMod hN (inducesInnerMod_fixed hJeq huD hconj)
    ·
      haveI hcommD : IsMulCommutative ↥⁅spSupported x ({X - 1} : Set K[X]),
          spSupported x ({X - 1} : Set K[X])⁆ := hcomm
      haveI hproj : Function.Injective (proj m K) :=
        CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154s_proj_injective (K := K) (r := m) (by
          have := CharP.cast_eq_zero K 2
          simpa using this)
      have e : ↥⁅spSupported x ({X - 1} : Set K[X]),
          spSupported x ({X - 1} : Set K[X])⁆ ≃* ↥J :=
        (Subgroup.equivMapOfInjective _ (proj m K) hproj).trans
          (MulEquiv.subgroupCongr hJeq.symm)
      haveI hcommJ : IsMulCommutative ↥J := ⟨⟨fun a b => by
        obtain ⟨a', rfl⟩ := e.surjective a
        obtain ⟨b', rfl⟩ := e.surjective b
        rw [← map_mul, ← map_mul, (isMulCommutative_iff.mp hcomm) a' b']⟩⟩
      haveI hcommQ : IsMulCommutative (PQuot p J) := ⟨⟨fun a b => by
        refine Quotient.inductionOn a fun a' => Quotient.inductionOn b fun b' => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          (isMulCommutative_iff.mp hcommJ) a' b']⟩⟩
      have hcenter : Subgroup.center (PQuot p J) = ⊤ := Subgroup.center_eq_top
      haveI : Subsingleton (PSimple p J) := by
        have h : PSimple p J = (PQuot p J ⧸ (⊤ : Subgroup (PQuot p J))) := by
          unfold PSimple
          rw [hcenter]
        exact h ▸ QuotientGroup.subsingleton_quotient_top
      exact mem_inner_of_subsingleton _
  · haveI := subsingleton_pSimple_of_not_dvd hp hpJ
    exact mem_inner_of_subsingleton _

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
