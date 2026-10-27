module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Tools
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL blockSL_injective)
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_mul blockMat_one det_blockMat
  blockIdx)
open Matrix
open scoped MatrixGroups

theorem exists_surjective_of_cover {U S Y : Type} [Group U] [Group S] [Group Y] [Finite U]
    [Finite Y] {β : U →* S} (hβ : Function.Surjective β)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* U), Function.Surjective π →
      π.ker ≤ center E → IsPGroup 2 π.ker → ∃ σ : U →* E, ∀ x, π (σ x) = x)
    (hq : IsQuasisimple Y) (hZ2 : IsPGroup 2 (center Y)) (e : Y ⧸ center Y ≃* S) :
    ∃ α : U →* Y, Function.Surjective α ∧ β.ker.map α = center Y ∧ α.ker ≤ β.ker := by
  have : Group.IsPerfect Y := hq.1
  set η : Y →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ hηs
    (hηker ▸ le_rfl) (hηker ▸ hZ2)
  refine ⟨α, hαs, hker.symm.trans hηker, fun A hA => ?_⟩
  rw [MonoidHom.mem_ker] at hA ⊢
  rw [← hα, hA, map_one]

namespace SL

variable {K : Type} [Field K]

variable (K) in
@[expose] def negBlockK (n j k : ℕ) : Matrix (Fin n) (Fin n) K :=
  blockMat n j (-1 : Matrix (Fin k) (Fin k) K)

theorem negBlockK_eq_diagonal (n j k : ℕ) :
    negBlockK K n j k = Matrix.diagonal (fun a : Fin n =>
      if j ≤ a.val ∧ a.val < j + k then (-1 : K) else 1) := by
  ext a b
  rw [negBlockK, blockMat_apply, Matrix.diagonal_apply]
  by_cases hb : (j ≤ a.val ∧ a.val < j + k) ∧ (j ≤ b.val ∧ b.val < j + k)
  · rw [dite_eq_left hb]
    by_cases hab : a = b
    · subst hab
      simp [hb.1]
    · have : (⟨a.val - j, by omega⟩ : Fin k) ≠ ⟨b.val - j, by omega⟩ := by
        intro h
        apply hab
        apply Fin.ext
        have := congrArg Fin.val h
        simp only at this
        omega
      simp [hab, this]
  · rw [dite_eq_right hb]
    by_cases hab : a = b
    · subst hab
      have : ¬ (j ≤ a.val ∧ a.val < j + k) := fun h => hb ⟨h, h⟩
      simp [this]
    · simp [hab]

theorem blockSL_mem_longRootGroupK {n j k : ℕ} (hj : j + k ≤ n) (A : SL(k, K)) :
    blockSL K n k j hj A ∈ longRootGroup (negBlockK K n j k) := by
  have hA : (-1 : Matrix (Fin k) (Fin k) K) * (A : Matrix (Fin k) (Fin k) K) =
      (A : Matrix (Fin k) (Fin k) K) * (-1) := by simp
  refine ⟨?_, ?_⟩
  · rw [coe_blockSL, negBlockK, ← blockMat_mul hj, ← blockMat_mul hj, hA]
  · rw [coe_blockSL, negBlockK, Matrix.mul_add, Matrix.mul_one, ← blockMat_mul hj]
    have : ((A : Matrix (Fin k) (Fin k) K) * (-1)) = -(A : Matrix (Fin k) (Fin k) K) := by simp
    rw [this]
    unfold blockMat
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul]
    abel

theorem exists_blockSL_of_mem_longRootGroupK (h2 : (2 : K) ≠ 0) {n j k : ℕ} (hj : j + k ≤ n)
    {x : SL(n, K)} (hx : x ∈ longRootGroup (negBlockK K n j k)) :
    ∃ A : SL(k, K), blockSL K n k j hj A = x := by
  obtain ⟨h1, h3⟩ := hx
  rw [negBlockK_eq_diagonal] at h1 h3
  set X : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hX
  set d : Fin n → K := fun a => if j ≤ a.val ∧ a.val < j + k then (-1 : K) else 1 with hd
  have e1 : ∀ a b, X a b * d b = d a * X a b := fun a b => by
    have := congr_fun (congr_fun h1 a) b
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have h3' : X * Matrix.diagonal (fun a => 1 + d a) = Matrix.diagonal (fun a => 1 + d a) := by
    have : (1 : Matrix (Fin n) (Fin n) K) + Matrix.diagonal d =
        Matrix.diagonal (fun a => 1 + d a) := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_add]
    rwa [this] at h3
  have e3 : ∀ a b, X a b * (1 + d b) = if a = b then 1 + d a else 0 := fun a b => by
    have := congr_fun (congr_fun h3' a) b
    simpa [Matrix.mul_diagonal, Matrix.diagonal_apply] using this
  let A : Matrix (Fin k) (Fin k) K := Matrix.of fun p q => X (blockIdx j hj p) (blockIdx j hj q)
  have hXA : X = blockMat n j A := by
    ext a b
    rw [blockMat_apply]
    by_cases hab : (j ≤ a.val ∧ a.val < j + k) ∧ (j ≤ b.val ∧ b.val < j + k)
    · rw [dite_eq_left hab]
      have ha : blockIdx j hj (⟨a.val - j, by omega⟩ : Fin k) = a :=
        Fin.ext (by simp only [blockIdx]; omega)
      have hb : blockIdx j hj (⟨b.val - j, by omega⟩ : Fin k) = b :=
        Fin.ext (by simp only [blockIdx]; omega)
      simp only [A, Matrix.of_apply, ha, hb]
    · rw [dite_eq_right hab]
      by_cases hb : j ≤ b.val ∧ b.val < j + k
      · have ha : ¬ (j ≤ a.val ∧ a.val < j + k) := fun h => hab ⟨h, hb⟩
        have hne : a ≠ b := fun h => ha (h ▸ hb)
        have := e1 a b
        simp only [hd, ite_eq_left hb, ite_eq_right ha] at this
        rw [Matrix.one_apply_ne hne]
        have h' : (2 : K) * X a b = 0 := by linear_combination -this
        exact (mul_eq_zero.mp h').resolve_left h2
      · have := e3 a b
        by_cases hab' : a = b
        · subst hab'
          rw [Matrix.one_apply_eq]
          simp only [hd, ite_eq_right hb, ite_true] at this
          have h' : (2 : K) * (X a a - 1) = 0 := by linear_combination this
          have := (mul_eq_zero.mp h').resolve_left h2
          linear_combination this
        · rw [Matrix.one_apply_ne hab']
          simp only [hd, ite_eq_right hb, hab', ite_false] at this
          have h' : (2 : K) * X a b = 0 := by linear_combination this
          exact (mul_eq_zero.mp h').resolve_left h2
  have hdet : A.det = 1 := by
    rw [← det_blockMat hj A, ← hXA]
    exact x.2
  exact ⟨⟨A, hdet⟩, Subtype.ext hXA.symm⟩

theorem range_blockSL_eq_longRootGroupK (h2 : (2 : K) ≠ 0) {n j k : ℕ} (hj : j + k ≤ n) :
    (blockSL K n k j hj).range = longRootGroup (negBlockK K n j k) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact blockSL_mem_longRootGroupK hj A
  · intro hx
    obtain ⟨A, hA⟩ := exists_blockSL_of_mem_longRootGroupK h2 hj hx
    exact ⟨A, hA⟩

theorem negBlockK_two_eq_neg (n : ℕ) (hn : 2 ≤ n) :
    negBlockK K n 2 (n - 2) = -negBlock K n 0 := by
  rw [negBlockK_eq_diagonal, negBlock_eq_diagonal, Matrix.diagonal_neg]
  congr 1
  funext a
  have := a.isLt
  by_cases ha : a.val < 2
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]

variable [Finite K]

theorem isTwoQuasisimple_of_isQuasisimple {J : Type*} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h2 : 2 ∣ Nat.card J) : IsTwoQuasisimple J := by
  have hO : pPrimeCore 2 J ≠ ⊤ := by
    intro h
    have hc := pPrimeCore_coprime_card (p := 2) (G := J)
    rw [h, card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 hc
  refine ⟨hq.1, ?_⟩
  set g := QuotientGroup.mk' (pPrimeCore 2 J)
  have hrange : g.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq g with h | h
  · exfalso
    apply hO
    rw [eq_top_iff]
    intro y _
    have hy : g y ∈ g.range := ⟨y, rfl⟩
    rw [h, mem_bot] at hy
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
  · exact LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv) h

theorem card_center_sl {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (center (SpecialLinearGroup (Fin n) K)) = Nat.gcd n (Nat.card K - 1) := by
  have := Fintype.ofFinite K
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, by omega⟩ : Fin n)).toEquiv,
    Fintype.card_fin, LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd,
    Nat.card_eq_fintype_card]

theorem concl_sl {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn4 : 4 ≤ n) (hn2 : Even n)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {a : SpecialLinearGroup (Fin n) K}
    (ha : a ∈ center (SpecialLinearGroup (Fin n) K)) (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    Concl p f (SpecialLinearGroup (Fin n) K) a := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h => by rw [h, pow_zero] at h5; omega
  have hn : 2 ≤ n := by omega
  have hqU : IsQuasisimple (SpecialLinearGroup (Fin n) K) :=
    RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hn (by omega)
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ha
  have hr2 : r * r = 1 := by
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0,
      by omega⟩ ⟨0, by omega⟩) ha2
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, ← hr] at h1
    simpa [Matrix.scalar_apply] using h1
  have hr1 : r ≠ 1 := fun h =>
    ha1 (Subtype.ext (by rw [← hr, h, map_one, Matrix.SpecialLinearGroup.coe_one]))
  have hrm : r = -1 := (mul_self_eq_one_iff.mp hr2).resolve_left hr1
  have ham : (a : Matrix (Fin n) (Fin n) K) = -1 := by rw [← hr, hrm, map_neg, map_one]
  set u := rootInv K hn with hu
  have hcl := isClassicalSL2_rootSL2 h2 hn
  have huZ : u ∉ center (SpecialLinearGroup (Fin n) K) := by
    intro h
    obtain ⟨s, -, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have hum : (u : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) s := hs.symm
    rw [hu, coe_rootInv, negBlock_eq_diagonal] at hum
    have e0 := congrFun (congrFun hum ⟨0, by omega⟩) ⟨0, by omega⟩
    have e2 := congrFun (congrFun hum ⟨2, by omega⟩) ⟨2, by omega⟩
    simp only [Matrix.diagonal_apply_eq, Matrix.scalar_apply] at e0 e2
    rw [ite_eq_left (by simp)] at e0
    rw [ite_eq_right (by simp)] at e2
    exact h2 (by linear_combination e2 - e0)
  obtain ⟨eL⟩ := hcl.nonempty_mulEquiv
  have hsL : IsSLTwoOver (p ^ f) (rootSL2 K hn) := by
    have := Fintype.ofFinite K
    exact ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hK], ⟨eL⟩⟩
  obtain ⟨hqL, hOL⟩ := isQuasisimple_of_isSLTwoOver hp hp2 h5 hsL
  have hj : 2 + (n - 2) ≤ n := by omega
  set J₂ := (blockSL K n (n - 2) 2 hj).range with hJ₂
  have hJ₂' : J₂ = longRootGroup (-negBlock K n 0) := by
    rw [hJ₂, range_blockSL_eq_longRootGroupK h2 hj, negBlockK_two_eq_neg n hn]
  let eJ : SpecialLinearGroup (Fin (n - 2)) K ≃* J₂ := MonoidHom.ofInjective (blockSL_injective hj)
  have hqJ : IsQuasisimple J₂ := LocalCores.isQuasisimple_of_mulEquiv eJ
    (RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (by omega) (by omega))
  have hcomm : ∀ {c : SpecialLinearGroup (Fin n) K}, c ∈ centralizer {u} →
      (c : Matrix (Fin n) (Fin n) K) * -negBlock K n 0 = -negBlock K n 0 * c := by
    intro c hc
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      (mem_centralizer_singleton_iff.mp hc)
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu, coe_rootInv] at h1
    rw [Matrix.mul_neg, Matrix.neg_mul, h1]
  have hJle : J₂ ≤ centralizer {u} := by
    intro x hx
    rw [hJ₂'] at hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h1 := hx.1
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu, coe_rootInv]
    exact h1
  have hJn : (J₂.subgroupOf (centralizer {u})).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJle]
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    rw [hJ₂']
    constructor
    · exact fun hx => conj_mem_longRootGroup_of_commute (hcomm hc) hx
    · intro hx
      have := conj_mem_longRootGroup_of_commute (hcomm (inv_mem hc)) hx
      rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  have hneg : (-1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K).det = 1 := by
    rw [det_neg, det_one, mul_one, Fintype.card_fin]
    exact (Even.neg_one_pow (by obtain ⟨m, hm⟩ := hn2; exact ⟨m - 1, by omega⟩))
  have hau : a * u = blockSL K n (n - 2) 2 hj (⟨-1, hneg⟩ : SL(n - 2, K)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ham, hu, coe_rootInv]
    change -1 * negBlock K n 0 = negBlockK K n 2 (n - 2)
    rw [negBlockK_two_eq_neg n hn, neg_one_mul]
  have hauJ : a * u ∈ J₂ := by
    rw [hau, hJ₂]
    exact ⟨_, rfl⟩
  have hau2 : orderOf (a * u) = 2 := by
    have hcomm' : a * u = u * a := (mem_center_iff.mp ha u).symm
    have huu : u * u = 1 := by rw [← sq, ← hcl.orderOf_eq_two, pow_orderOf_eq_one]
    refine orderOf_eq_prime ?_ fun h => huZ ?_
    · rw [sq]
      calc a * u * (a * u) = a * (u * a) * u := by group
        _ = a * (a * u) * u := by rw [← hcomm']
        _ = a * a * (u * u) := by group
        _ = 1 := by rw [ha2, huu, one_mul]
    · have : u = a⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact inv_mem ha
  have h2J : 2 ∣ Nat.card J₂ := by
    have h1 := orderOf_dvd_natCard (⟨a * u, hauJ⟩ : J₂)
    rwa [Subgroup.orderOf_mk, hau2] at h1
  have hlie : Blueprint.LieModel (↥J₂ ⧸ Open.fusionZStar ↥J₂) .PSL (n - 2) p f := by
    have hZJ : (center (SpecialLinearGroup (Fin (n - 2)) K)).map eJ.toMonoidHom =
        Open.fusionZStar ↥J₂ := by
      rw [fusionZStar_eq_center_of_isQuasisimple hqJ h2J]
      exact Subgroup.map_center_eq eJ
    refine Or.inl ⟨by decide, ⟨hp, hf, by omega, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨(QuotientGroup.congr _ _ eJ hZJ).symm.trans
        (projectiveSpecialLinearGroupEquivStatedProj (n - 2) K)⟩⟩
    all_goals
      intro h
      simp only [Prod.mk.injEq] at h
      omega
  refine ⟨u, hcl.orderOf_eq_two, not_mem_fusionZStar hqU (orderOf_eq_prime (by rw [sq, ha2]) ha1)
    huZ, rootSL2 K hn, J₂,
    isTwoComponentIn_of_normal hcl.le_centralizer
      ((isLongRootSL2_standard hn).normal_subgroupOf_centralizer h2) hqL hOL,
    ⟨hJle, Subgroup.Normal.isSubnormal hJn, isTwoQuasisimple_of_isQuasisimple hqJ h2J⟩,
    fun h => ?_, hcl.mem, isSLTwoOver_quot hp hp2 h5 hsL, ⟨.PSL, n - 2, hlie⟩, .inr hauJ⟩
  have huJ : u ∈ J₂ := h ▸ hcl.mem
  obtain ⟨A, hA⟩ := huJ
  have h1 := congrFun (congrFun (congrArg (fun g : SpecialLinearGroup (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K)) hA) ⟨0, by omega⟩) ⟨0, by omega⟩
  simp only [coe_blockSL, hu, coe_rootInv, negBlock_eq_diagonal, Matrix.diagonal_apply_eq] at h1
  rw [blockMat_apply, dite_eq_right (by simp), ite_eq_left (by simp), Matrix.one_apply_eq] at h1
  exact h2 (by linear_combination h1)

end SL

theorem rowSL : RowSL := by
  intro Y _ _ hq hZ p hp hp2 τ n f ⟨hτ, hn2⟩ hlie h5 hpsl hc t ht htZ
  subst hτ
  have hn2' : n ≠ 2 := fun h => hpsl (h ▸ hlie)
  have hlie' := hlie
  rcases hlie' with ⟨-, ⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hn4 : 4 ≤ n := by
    obtain ⟨k, hk⟩ := hn2
    omega
  have hcZ := hc (n / 2) f (by omega) (by omega)
    (.inl (by rw [Nat.two_mul_div_two_of_even hn2]; exact hlie))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := Fintype.ofFinite K
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  have hsplit0 : ∀ (E : Type) [Group E] (π : E →* SpecialLinearGroup (Fin (m + 1)) K),
      Function.Surjective π → π.ker ≤ center E →
        ∃ σ : SpecialLinearGroup (Fin (m + 1)) K →* E, ∀ g, π (σ g) = g :=
    fun E _ π hπ hcen => LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
      (by omega) h5K hπ hcen
  let e' : Y ⧸ center Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj (m + 1) K).symm
  obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover
    (β := QuotientGroup.mk' (center (SpecialLinearGroup (Fin (m + 1)) K)))
    (QuotientGroup.mk'_surjective _) (fun E _ _ π hπ hcen _ => hsplit0 E π hπ hcen) hq hZ e'
  rw [QuotientGroup.ker_mk'] at hαZ hαk
  have hg0 : Nat.gcd (m + 1) (Nat.card K - 1) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
  have hZY : Nat.card (center Y) = ordProj[2] (Nat.gcd (m + 1) (Nat.card K - 1)) := by
    rw [hcZ, Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e').toEquiv]
    obtain ⟨-, ⟨eM⟩⟩ := LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_split
      (k := K) (m := m) (by omega) hsplit0
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      ← Nat.card_eq_fintype_card]
  have hψmem : ∀ x : center (SpecialLinearGroup (Fin (m + 1)) K),
      (α.comp (center (SpecialLinearGroup (Fin (m + 1)) K)).subtype) x ∈ center Y := fun x =>
    hαZ ▸ mem_map_of_mem α x.2
  let ψ := (α.comp (center (SpecialLinearGroup (Fin (m + 1)) K)).subtype).codRestrict (center Y)
    hψmem
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hαZ] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hψk : Nat.card ψ.ker = Nat.card α.ker := by
    have hmap : ψ.ker.map (center (SpecialLinearGroup (Fin (m + 1)) K)).subtype = α.ker := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact congrArg Subtype.val hy
      · intro hx
        exact ⟨⟨x, hαk hx⟩, Subtype.ext hx, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective (center _).subtype_injective]
  have hmul := Subgroup.card_ker_mul_card_of_surjective hψs
  rw [hψk, hZY, SL.card_center_sl (by omega)] at hmul
  have hk : ¬ 2 ∣ Nat.card α.ker := by
    have h1 : Nat.card α.ker = ordCompl[2] (Nat.gcd (m + 1) (Nat.card K - 1)) :=
      Nat.eq_of_mul_eq_mul_right (Nat.ordProj_pos _ 2) (by
        rw [hmul, mul_comm]
        exact (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm)
    rw [h1]
    exact Nat.not_dvd_ordCompl Nat.prime_two hg0
  obtain ⟨a, ha2, hat⟩ := Frame.exists_involution_lift α hk ht (MonoidHom.mem_range.mpr (hαs t))
  have haZ : a ∈ center (SpecialLinearGroup (Fin (m + 1)) K) := by
    have htU : t ∈ (center (SpecialLinearGroup (Fin (m + 1)) K)).map α := hαZ ▸ htZ
    obtain ⟨c, hc, hct⟩ := htU
    have h1 : a⁻¹ * c ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hat, hct, inv_mul_cancel]
    have : a = c * (a⁻¹ * c)⁻¹ := by group
    rw [this]
    exact mul_mem hc (inv_mem (hαk h1))
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; exact absurd ha2 (by norm_num)
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  rw [← hat]
  exact Concl.map (φ := α) hαs hk (SL.concl_sl hp hp2 hn4 hn2 hK h5 haZ ha1 haa)

end CFSG.ComponentClassification.HarrisLit.T1.P54
