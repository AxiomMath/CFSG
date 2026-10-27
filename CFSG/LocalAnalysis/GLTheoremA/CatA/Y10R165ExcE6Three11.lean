module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three16
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine3

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective
  adjEmb_mem adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff
  twistedTorusOf mem_twistedTorusOf twistedFixedPoints mem_twistedFixedPoints subtorusSigma)
open CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit
  rootSpan_torusRootKernel_le_centralizer rootChar_neg')
open CFSG.HardMathSupport.Lang.TwE6Step3
open CFSG.RankThree.Lattice (e6T3W IsSeparated commute_of_isSeparated)
open scoped Matrix MatrixGroups Pointwise



structure E6ThreeConclData (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂)
    (xt zt : ↥(e6Data_valid.minGroup F)) : Type where
  hxt1 : xt ≠ 1
  hztxt : zt ∉ Subgroup.zpowers xt
  hJx : centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ≤
    Subgroup.centralizer ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F))
  hJn : ((centralizerLayerPullback D₂.ψ (D₁.KL.P 0)).subgroupOf
    (Subgroup.centralizer ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F)))).Normal
  Ql : Subgroup (adjointGroup Tag.E6 F)
  hQlJ : Ql ≤ centralizerLayerPullback D₂.ψ (D₁.KL.P 0)
  hQlz : Ql ≤ Subgroup.centralizer ({e6Isogeny F zt} : Set (adjointGroup Tag.E6 F))
  hQln : (Ql.subgroupOf (centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊓
    Subgroup.centralizer ({e6Isogeny F zt} : Set (adjointGroup Tag.E6 F)))).Normal
  hQlq : CFSG.Open.IsQuasisimple ↥Ql
  hpQl : p ∣ Nat.card Ql
  hJ₁x : centralizerLayerPullback D₂.ψ (D₁.KL.P 1) ≤
    Subgroup.centralizer ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F))
  hJ₁perf : ⁅centralizerLayerPullback D₂.ψ (D₁.KL.P 1),
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1)⁆ =
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1)
  s₀ : adjointGroup Tag.E6 F
  hs₀J₁ : s₀ ∈ centralizerLayerPullback D₂.ψ (D₁.KL.P 1)
  hsq₀ : orderOf s₀ = q
  hsZ : (⟨s₀, hs₀J₁⟩ : ↥(centralizerLayerPullback D₂.ψ (D₁.KL.P 1))) ∉
    Subgroup.center ↥(centralizerLayerPullback D₂.ψ (D₁.KL.P 1))
  h2ker : ¬ 2 ∣ Nat.card (e6Isogeny F).ker

theorem e6Three_concl_data (F : Type) [Field F] [Finite F] [CharP F 2]
    [Finite ↥(e6Data_valid.minGroup F)]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂)
    {xt zt : ↥(e6Data_valid.minGroup F)} (hxtÃ : xt ∈ Ã) (hztÃ : zt ∈ Ã)
    (hxtπ : e6Isogeny F xt = D₁.x) (hztπ : e6Isogeny F zt = D₁.z) :
    Nonempty (E6ThreeConclData F n p q Ã D₁ D₂ D₃ xt zt) := by
  obtain ⟨Q, hQdef, hQel, hker, g0, c,
    _, hAT, _, _, _, x_L,
    _, x, hxQ, hxLx, hxne, _,
    _, _, _, S₁, _, KL,
    _, _, _, _, _, _,
    _, _, z_L, hzA, hzLx, hS₁z,
    z, hzQ, hzLz⟩ := D₁
  obtain ⟨ψ, _, hψ, hP0, hJleC, hJn, hJq, hpJ, hJ₁leC, hJ₁q, _, _, hcommJ⟩ := D₂
  obtain ⟨_, s, hsZ, hsq, _⟩ := D₃
  dsimp only [] at hψ hP0 hJleC hJn hJq hpJ hJ₁leC hJ₁q hcommJ hxtπ hztπ
  let s₀ : adjointGroup Tag.E6 F := (s : adjointGroup Tag.E6 F)
  have hs₀J₁ : s₀ ∈ centralizerLayerPullback ψ (KL.P 1) := s.2
  have hsq₀ : orderOf s₀ = q := by
    dsimp only [s₀]
    rw [Subgroup.orderOf_coe]
    exact hsq
  have hJ₁perf : ⁅centralizerLayerPullback ψ (KL.P 1),
      centralizerLayerPullback ψ (KL.P 1)⁆ =
      centralizerLayerPullback ψ (KL.P 1) :=
    (Subgroup.isPerfect_iff (H := centralizerLayerPullback ψ (KL.P 1))).mp
      (Group.IsPerfect.mk hJ₁q.1)
  have h2ker : ¬ 2 ∣ Nat.card (e6Isogeny F).ker := by
    rw [hker, (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F).1]
    intro h
    have h2 : 2 ∣ 3 := h.trans (Nat.gcd_dvd_left 3 (Nat.card F - 1))
    omega
  have hxt1 : xt ≠ 1 := fun h => hxne (by rw [← hxtπ, h, map_one])
  have hztxt : zt ∉ Subgroup.zpowers xt := by
    intro hz
    apply hzLx
    have hz' : z ∈ Subgroup.zpowers x := by
      have := Subgroup.mem_map_of_mem (e6Isogeny F) hz
      rwa [MonoidHom.map_zpowers, hxtπ, hztπ] at this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hcalc : z_L = x_L ^ k := by
      calc z_L = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * z * c⁻¹) * g0 := hzLz
        _ = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * x ^ k * c⁻¹) * g0 := by rw [← hk]
        _ = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) ((c * x * c⁻¹) ^ k) * g0 := by
              have hconjpow : c * x ^ k * c⁻¹ = (c * x * c⁻¹) ^ k := by
                rw [show c * x ^ k * c⁻¹ = (MulAut.conj c) (x ^ k) by rfl, map_zpow]
                rfl
              rw [hconjpow]
        _ = (g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * x * c⁻¹) * g0) ^ k := by
              have hmap := map_zpow (MulAut.conj g0⁻¹)
                (adjEmb Tag.E6 F (AlgebraicClosure F) (c * x * c⁻¹)) k
              simpa [MulAut.conj_apply] using hmap
        _ = x_L ^ k := by rw [← hxLx]
    exact hcalc.symm
  have hJx : centralizerLayerPullback ψ (KL.P 0) ≤ Subgroup.centralizer
      ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F)) := by
    rw [hxtπ]; exact hJleC
  have hJn' : ((centralizerLayerPullback ψ (KL.P 0)).subgroupOf (Subgroup.centralizer
      ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F)))).Normal := by
    rw [hxtπ]; exact hJn
  have hJ₁x : centralizerLayerPullback ψ (KL.P 1) ≤ Subgroup.centralizer
      ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F)) := by
    rw [hxtπ]; exact hJ₁leC
  have hzJ : centralizerLayerPullback ψ (KL.P 0) ≤ Subgroup.centralizer
      ({z} : Set (adjointGroup Tag.E6 F)) := by
    have hzLT : z_L ∈ twistedTorus (phi3N (AlgebraicClosure F))
        (iterateFrobenius (AlgebraicClosure F) 2 n) := hAT hzA
    have hrootz : rootSpan Tag.E6 (AlgebraicClosure F) S₁ ≤
        Subgroup.centralizer ({z_L} : Set (ModGL Tag.E6 (AlgebraicClosure F))) :=
      (CFSG.LieType.Chevalley.rootSpan_mono hS₁z).trans
        (rootSpan_torusRootKernel_le_centralizer (mem_twistedTorus.1 hzLT).1)
    have hP0z : KL.P 0 ≤ Subgroup.centralizer
        ({z_L} : Set (ModGL Tag.E6 (AlgebraicClosure F))) := by
      rw [hP0]; exact inf_le_left.trans hrootz
    intro y hy
    have hyC : y ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)) := hJleC hy
    have hpsiy : ψ ⟨y, hyC⟩ ∈ KL.P 0 := by
      rw [centralizerLayerPullback] at hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      exact (show w = ⟨y, hyC⟩ from Subtype.ext hwy) ▸ (Subgroup.mem_comap.mp hw)
    have hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hQel.comm hzQ hxQ)
    have hcommψ : Commute (ψ ⟨y, hyC⟩) z_L :=
      Subgroup.mem_centralizer_singleton_iff.1 (hP0z hpsiy)
    have hpsiz : ψ ⟨z, hzC⟩ = z_L := (hψ ⟨z, hzC⟩).trans hzLz.symm
    have hcommψ' : Commute (ψ ⟨y, hyC⟩) (ψ ⟨z, hzC⟩) := by rwa [hpsiz]
    have hyz : Commute y z := commute_of_psi_commute (F := F) (x := x) (c := c) (g0 := g0)
      (ψ := ψ) hψ hcommψ'
    exact Subgroup.mem_centralizer_singleton_iff.mpr hyz.eq
  obtain ⟨Ql, hQlJ, hQlz, hQln, hQlq, hpQl⟩ := exists_layer_of_centralizing
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hJq) hpJ hzJ
  have hQlz' : Ql ≤ Subgroup.centralizer
      ({e6Isogeny F zt} : Set (adjointGroup Tag.E6 F)) := by rwa [hztπ]
  have hQln' : (Ql.subgroupOf (centralizerLayerPullback ψ (KL.P 0) ⊓ Subgroup.centralizer
      ({e6Isogeny F zt} : Set (adjointGroup Tag.E6 F)))).Normal := by rwa [hztπ]
  refine ⟨⟨hxt1, hztxt, hJx, hJn', Ql, hQlJ, hQlz', hQln', ?_, hpQl, hJ₁x, hJ₁perf,
    s₀, hs₀J₁, hsq₀, hsZ, h2ker⟩⟩
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hQlq

section Model


structure E6ThreeCoprimeTorusData (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂) : Type where
  Fq : Subgroup (adjointGroup Tag.E6 F)
  hFqle : Fq ≤ centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
      Subgroup.zpowers (D₃.s : adjointGroup Tag.E6 F)
  hFqel : IsElemAbelian q Fq
  hFqcard : Nat.card Fq = q ^ 3
  hFqpR : 3 ≤ CFSG.Open.pRank q Fq
  hFqC : Fq ≤ Subgroup.centralizer ({D₁.x} : Set (adjointGroup Tag.E6 F))
  hFqN : Fq ≤ Subgroup.normalizer
      (centralizerLayerPullback D₂.ψ (D₁.KL.P 0) : Set (adjointGroup Tag.E6 F))
  hFqV : Fq ≤ centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1)
  xt : ↥(e6Data_valid.minGroup F)
  hxtÃ : xt ∈ Ã
  hxtπ : e6Isogeny F xt = D₁.x
  zt : ↥(e6Data_valid.minGroup F)
  hztÃ : zt ∈ Ã
  hztπ : e6Isogeny F zt = D₁.z
  hVperf : ⁅centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1),
      centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1)⁆ =
      centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1)
  hVx' : centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1) ≤
      Subgroup.centralizer ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F))

structure E6ThreeCoprimeLiftData (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (xt : ↥(e6Data_valid.minGroup F)) (Fq : Subgroup (adjointGroup Tag.E6 F)) : Type where
  W : Subgroup ↥(e6Data_valid.minGroup F)
  hWperf : ⁅W, W⁆ = W
  hWC : W ≤ Subgroup.centralizer ({xt} : Set ↥(e6Data_valid.minGroup F))
  hWmap : W.map (e6Isogeny F) = centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
      centralizerLayerPullback D₂.ψ (D₁.KL.P 1)
  hPmap : (Fq.comap (e6Isogeny F) ⊓ W).map (e6Isogeny F) = Fq

structure E6ThreeCoprimeRankData (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (xt : ↥(e6Data_valid.minGroup F)) (Fq : Subgroup (adjointGroup Tag.E6 F)) : Type where
  R : Subgroup ↥(e6Data_valid.minGroup F)
  hRel : IsElemAbelian q R
  hRmap : R.map (e6Isogeny F) = Fq
  hRC : R ≤ Subgroup.centralizer ({xt} : Set ↥(e6Data_valid.minGroup F))
  hRcard3 : Nat.card R = q ^ 3
  hRpR : 3 ≤ CFSG.Open.pRank q R
  hRker : R ⊓ (e6Isogeny F).ker = ⊥

def e6Three_coprime_torus (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hq : q.Prime)
    (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂) :
    E6ThreeCoprimeTorusData F n p q Ã D₁ D₂ D₃ := by
  refine Classical.choice ?_
  obtain ⟨Q, hQdef, _, _, _, _,
    _, _, _, _, _, _,
    _, x, hxQ, _, _, _,
    _, _, _, _, _, KL,
    _, _, _, _, _, _,
    _, _, _, _, _, _,
    z, hzQ, _⟩ := D₁
  obtain ⟨ψ, _, _, _, hJleC, _, hJq, _, hJ₁leC, hJ₁q, eJ, _, hcommJ⟩ := D₂
  obtain ⟨hqdiv', s, _, hsq, hinf_center⟩ := D₃
  let s₀ : adjointGroup Tag.E6 F := (s : adjointGroup Tag.E6 F)
  have hs₀J₁ : s₀ ∈ centralizerLayerPullback ψ (KL.P 1) := s.2
  have hsq₀ : orderOf s₀ = q := by
    dsimp only [s₀]
    rw [Subgroup.orderOf_coe]
    exact hsq
  rw [hQdef] at hxQ hzQ
  have hdisj : centralizerLayerPullback ψ (KL.P 0) ⊓ Subgroup.zpowers s₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyJ, hys⟩ := Subgroup.mem_inf.mp hy
    have hyJ₁ : y ∈ centralizerLayerPullback ψ (KL.P 1) :=
      Subgroup.zpowers_le.mpr hs₀J₁ hys
    have hycent : (⟨y, hyJ₁⟩ : ↥(centralizerLayerPullback ψ (KL.P 1))) ∈
        Subgroup.center ↥(centralizerLayerPullback ψ (KL.P 1)) := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h := hcommJ y hyJ (b : adjointGroup Tag.E6 F) b.2
      exact Subtype.ext (by simpa using h.eq.symm)
    have hys' : (⟨y, hyJ₁⟩ : ↥(centralizerLayerPullback ψ (KL.P 1))) ∈ Subgroup.zpowers s := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hys
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
    have hbot : (⟨y, hyJ₁⟩ : ↥(centralizerLayerPullback ψ (KL.P 1))) ∈
        Subgroup.zpowers s ⊓ Subgroup.center ↥(centralizerLayerPullback ψ (KL.P 1)) :=
      ⟨hys', hycent⟩
    rw [hinf_center] at hbot
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hbot)
  have hcommzs : ∀ a ∈ centralizerLayerPullback ψ (KL.P 0), ∀ b ∈ Subgroup.zpowers s₀,
      a * b = b * a := by
    intro a ha b hb
    exact (hcommJ a ha b (Subgroup.zpowers_le.mpr hs₀J₁ hb)).eq
  obtain ⟨Fq, hFqle, hFqel, hFqcard, hFqpR⟩ :=
    exists_rank_three_qTorus (G := adjointGroup Tag.E6 F) (K := F)
      (J₀ := centralizerLayerPullback ψ (KL.P 0)) (J₁ := Subgroup.zpowers s₀) eJ hq hqdiv' hcommzs
      hdisj (Subgroup.mem_zpowers s₀) hsq₀
  have hFqC : Fq ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)) := by
    refine hFqle.trans (sup_le ?_ ?_)
    · exact hJleC
    · exact Subgroup.zpowers_le.mpr (hJ₁leC hs₀J₁)
  have hFqN : Fq ≤ Subgroup.normalizer
      (centralizerLayerPullback ψ (KL.P 0) : Set (adjointGroup Tag.E6 F)) := by
    refine hFqle.trans (sup_le ?_ ?_)
    · exact Subgroup.le_normalizer
    · refine (Subgroup.zpowers_le.mpr ?_).trans
        (Subgroup.centralizer_le_normalizer
          (centralizerLayerPullback ψ (KL.P 0) : Set (adjointGroup Tag.E6 F)))
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcommJ y hy s₀ hs₀J₁).eq)
  have hJperf : ⁅centralizerLayerPullback ψ (KL.P 0), centralizerLayerPullback ψ (KL.P 0)⁆ =
      centralizerLayerPullback ψ (KL.P 0) :=
    (Subgroup.isPerfect_iff (H := centralizerLayerPullback ψ (KL.P 0))).mp
      (Group.IsPerfect.mk hJq.1)
  have hJ₁perf : ⁅centralizerLayerPullback ψ (KL.P 1), centralizerLayerPullback ψ (KL.P 1)⁆ =
      centralizerLayerPullback ψ (KL.P 1) :=
    (Subgroup.isPerfect_iff (H := centralizerLayerPullback ψ (KL.P 1))).mp
      (Group.IsPerfect.mk hJ₁q.1)
  have hVperf : ⁅centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1),
      centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1)⁆ =
      centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1) := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    refine sup_le ?_ ?_
    · have h := Subgroup.commutator_mono
        (le_sup_left : centralizerLayerPullback ψ (KL.P 0) ≤
          centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1))
        (le_sup_left : centralizerLayerPullback ψ (KL.P 0) ≤
          centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1))
      rwa [hJperf] at h
    · have h := Subgroup.commutator_mono
        (le_sup_right : centralizerLayerPullback ψ (KL.P 1) ≤
          centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1))
        (le_sup_right : centralizerLayerPullback ψ (KL.P 1) ≤
          centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1))
      rwa [hJ₁perf] at h
  have hFqV : Fq ≤ centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1) :=
    hFqle.trans (sup_le_sup le_rfl (Subgroup.zpowers_le.mpr hs₀J₁))
  have hVx : centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1) ≤
      Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)) :=
    sup_le hJleC hJ₁leC
  obtain ⟨xt, hxtÃ, hxtπ⟩ := Subgroup.mem_map.mp hxQ
  obtain ⟨zt, hztÃ, hztπ⟩ := Subgroup.mem_map.mp hzQ
  have hVx' : centralizerLayerPullback ψ (KL.P 0) ⊔ centralizerLayerPullback ψ (KL.P 1) ≤
      Subgroup.centralizer ({e6Isogeny F xt} : Set (adjointGroup Tag.E6 F)) := by
    rw [hxtπ]; exact hVx
  exact ⟨
    { Fq := Fq, hFqle := hFqle, hFqel := hFqel, hFqcard := hFqcard, hFqpR := hFqpR,
      hFqC := hFqC, hFqN := hFqN, hFqV := hFqV, xt := xt, hxtÃ := hxtÃ, hxtπ := hxtπ,
      zt := zt, hztÃ := hztÃ, hztπ := hztπ, hVperf := hVperf, hVx' := hVx' }⟩

def e6Three_coprime_lift (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂)
    (T : E6ThreeCoprimeTorusData F n p q Ã D₁ D₂ D₃) :
    E6ThreeCoprimeLiftData F n p q Ã D₁ D₂ T.xt T.Fq := by
  refine Classical.choice ?_
  obtain ⟨Fq, _, _, _, _, _, _, hFqV, xt, _, _, _, _, _, hVperf, hVx'⟩ := T
  have hker : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) := D₁.hker
  obtain ⟨W, hWperf, hWC, hWmap⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_perfect_lift_centralizer
      (π := e6Isogeny F) (t := xt) (e6Isogeny_surjective F) (le_of_eq hker) hVperf hVx'
  have hPmap : (Fq.comap (e6Isogeny F) ⊓ W).map (e6Isogeny F) = Fq := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_comap.mp hy.1
    · intro f hf
      have hfV : f ∈ centralizerLayerPullback D₂.ψ (D₁.KL.P 0) ⊔
          centralizerLayerPullback D₂.ψ (D₁.KL.P 1) := hFqV hf
      rw [← hWmap] at hfV
      obtain ⟨w, hwW, hwf⟩ := Subgroup.mem_map.mp hfV
      exact ⟨w, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_comap.mpr (hwf ▸ hf), hwW⟩, hwf⟩
  exact ⟨{ W := W, hWperf := hWperf, hWC := hWC, hWmap := hWmap, hPmap := hPmap }⟩

def e6Three_coprime_rank (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (e6Isogeny F).ker)
    (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂)
    (T : E6ThreeCoprimeTorusData F n p q Ã D₁ D₂ D₃)
    (L : E6ThreeCoprimeLiftData F n p q Ã D₁ D₂ T.xt T.Fq) :
    E6ThreeCoprimeRankData F n p q Ã T.xt T.Fq := by
  refine Classical.choice ?_
  let Fq := T.Fq
  let hFqel := T.hFqel
  let hFqcard := T.hFqcard
  let xt := T.xt
  let W := L.W
  let hWC := L.hWC
  let hPmap := L.hPmap
  obtain ⟨R, hRP, hRel, hRmap, hRcard⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_elemAbelian_lift
      (p := q) hq hqZ hPmap hFqel
  have hRC : R ≤ Subgroup.centralizer ({xt} : Set ↥(e6Data_valid.minGroup F)) :=
    hRP.trans (inf_le_right.trans hWC)
  have hRcard3 : Nat.card R = q ^ 3 := by rw [hRcard, hFqcard]
  have hRpR : 3 ≤ CFSG.Open.pRank q R :=
    CFSG.SectionRank.le_pRank hq.one_lt le_rfl hRel (by rw [hRcard3])
  have hRker : R ⊓ (e6Isogeny F).ker = ⊥ := by
    have hrange : Nat.card ↥((e6Isogeny F).comp R.subtype).range = Nat.card ↥R := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hRmap, hRcard]
    have hmul := Subgroup.card_ker_mul_card_range ((e6Isogeny F).comp R.subtype)
    rw [hrange] at hmul
    have hker1 : Nat.card ↥((e6Isogeny F).comp R.subtype).ker = 1 := by
      have hmul' : Nat.card ↥((e6Isogeny F).comp R.subtype).ker * Nat.card ↥R =
          1 * Nat.card ↥R := by rw [hmul, one_mul]
      exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) hmul'
    have hkerbot : ((e6Isogeny F).comp R.subtype).ker = ⊥ := Subgroup.card_eq_one.mp hker1
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyR, hyker⟩ := Subgroup.mem_inf.mp hy
    have hy' : (⟨y, hyR⟩ : ↥R) ∈ ((e6Isogeny F).comp R.subtype).ker := by
      rw [MonoidHom.mem_ker]; simpa using hyker
    have hy1 : (⟨y, hyR⟩ : ↥R) = 1 := Subgroup.mem_bot.mp (hkerbot ▸ hy')
    exact Subtype.ext_iff.mp hy1
  exact ⟨
    { R := R, hRel := hRel, hRmap := hRmap, hRC := hRC, hRcard3 := hRcard3,
      hRpR := hRpR, hRker := hRker }⟩

theorem e6Three_coprime_concl (F : Type) [Field F] [Finite F] [CharP F 2]
    [Finite ↥(e6Data_valid.minGroup F)]
    (n p q : ℕ) (hp : p.Prime)
    (Ã : Subgroup ↥(e6Data_valid.minGroup F)) (hAe : IsElemAbelian p Ã)
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂)
    (T : E6ThreeCoprimeTorusData F n p q Ã D₁ D₂ D₃)
    (Rd : E6ThreeCoprimeRankData F n p q Ã T.xt T.Fq) :
    Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
      (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  obtain ⟨hxt1, hztxt, hJx, hJn', Ql, hQlJ, hQlz', hQln', hQlq, hpQl,
    hJ₁x, hJ₁perf, s₀, hs₀J₁, hsq₀, hsZ, h2ker⟩ :=
    Classical.choice (e6Three_concl_data F n p q Ã D₁ D₂ D₃ T.hxtÃ T.hztÃ T.hxtπ T.hztπ)
  obtain ⟨R, hRel, hRmap, hRC, _, hRpR, hRker⟩ := Rd
  have hFliftnorm : R.map (e6Isogeny F) ≤ Subgroup.normalizer
      (centralizerLayerPullback D₂.ψ (D₁.KL.P 0) : Set (adjointGroup Tag.E6 F)) := by
    rw [hRmap]; exact T.hFqN
  have hconcl : Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã (e6Isogeny F).ker :=
    concl165Avoid_of_central_lift hp (e6Isogeny F) (e6Isogeny_surjective F) (le_of_eq D₁.hker)
      hAe T.hxtÃ T.hztÃ hxt1 hztxt hJx hJn' D₂.hJq D₂.hpJ hQlJ hQlz' hQln' hQlq hpQl
      hRel hRC hFliftnorm hRpR hRker
  rw [D₁.hker] at hconcl
  exact hconcl

theorem e6Model165At_three_of_coprime (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 3)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (hqZ : ¬ q ∣ Nat.card (e6Isogeny F).ker) :
    letI : Finite ↥(e6Data_valid.minGroup F) :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
    ∀ Ã : Subgroup ↥(e6Data_valid.minGroup F), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(e6Data_valid.minGroup F)),
        orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤ CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã →
      Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
        (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  letI : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  intro Ã hAe _hASC hmax hA3
  classical
  let D₁ := e6Three_frame_data F n p q hcard hn hp hp2 hrk hq Ã hAe hmax hA3
  let D₂ := e6Three_layer_data F n p q hcard hp hp2 hrk Ã D₁
  let D₃ := e6Three_centre_data F n p q hcard hn hq hqdiv Ã D₁ D₂
  let T := e6Three_coprime_torus F n p q hq Ã D₁ D₂ D₃
  let L := e6Three_coprime_lift F n p q Ã D₁ D₂ D₃ T
  let Rd := e6Three_coprime_rank F n p q hq hqZ Ã D₁ D₂ D₃ T L
  exact e6Three_coprime_concl F n p q hp Ã hAe D₁ D₂ D₃ T Rd

end Model

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
