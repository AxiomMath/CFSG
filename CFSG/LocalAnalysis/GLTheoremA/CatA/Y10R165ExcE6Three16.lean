module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165LayerPullback
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin2
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6ThreeDvd

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


@[expose] def centralizerLayerPullback {K M : Type*} [Group K] [Group M] {C : Subgroup K}
    (ψ : ↥C →* M) (P : Subgroup M) : Subgroup K :=
  (P.comap ψ).map C.subtype

theorem centralizerLayerPullback_data {K M : Type*} [Group K] [Group M] {C : Subgroup K}
    {ψ : ↥C →* M} (hψ : Function.Injective ψ) {P : Subgroup M} (hP : P ≤ ψ.range)
    (hPq : CFSG.Open.IsQuasisimple ↥P)
    (hnorm : ∀ d : ↥C, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P) :
    centralizerLayerPullback ψ P ≤ C ∧
      Subgroup.Normal ((centralizerLayerPullback ψ P).subgroupOf C) ∧
      CFSG.Open.IsQuasisimple ↥(centralizerLayerPullback ψ P) ∧
      Nat.card ↥(centralizerLayerPullback ψ P) = Nat.card ↥P := by
  obtain ⟨h1, h2, h3, h4⟩ := quasisimple_normal_map_comap_of_layer ψ hψ hP hPq hnorm
  exact ⟨h1, h2, h3, h4⟩

structure E6ThreeFrameData (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F)) : Type where
  Q : Subgroup (adjointGroup Tag.E6 F)
  hQdef : Q = Ã.map (e6Isogeny F)
  hQel : IsElemAbelian p Q
  hker : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F)
  g0 : ModGL Tag.E6 (AlgebraicClosure F)
  c : adjointGroup Tag.E6 F
  A : Subgroup (ModGL Tag.E6 (AlgebraicClosure F))
  hAT : A ≤ twistedTorus (phi3N (AlgebraicClosure F))
      (iterateFrobenius (AlgebraicClosure F) 2 n)
  hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure F)
  hg0 : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)) g0 =
      g0 * phi3N (AlgebraicClosure F)
  hperf : ∀ P : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)),
      Finite P → P ≤ adjointGroup Tag.E6 (AlgebraicClosure F) →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)) x = x) →
      ⁅P, P⁆ = P → P ≤ (adjEmb Tag.E6 F (AlgebraicClosure F)).range
  x_L : ModGL Tag.E6 (AlgebraicClosure F)
  hxLT : x_L ∈ twistedTorus (phi3N (AlgebraicClosure F))
      (iterateFrobenius (AlgebraicClosure F) 2 n)
  x : adjointGroup Tag.E6 F
  hxQ : x ∈ Q
  hxLx : x_L = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * x * c⁻¹) * g0
  hxne : x ≠ 1
  hxord : orderOf x = p
  hf : 1 ≤ n
  hFr : ∀ c : AlgebraicClosure F,
      iterateFrobenius (AlgebraicClosure F) 2 n c = c ^ (2 ^ n)
  w : WeylGroup Tag.E6
  S₁ : Set (Fin Tag.E6.rank → ℤ)
  S₂ : Set (Fin Tag.E6.rank → ℤ)
  KL : KernelLayer (phi3N (AlgebraicClosure F))
      (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)))
      (torusRootKernel x_L) F (Fin 2)
  hw₁ : (w • ·) '' S₁ = parabolicRoots Tag.E6 support13
  hw₂ : (w • ·) '' S₂ = parabolicRoots Tag.E6 support56
  hS₁r : ∀ α ∈ S₁, IsRoot Tag.E6 α
  hvS₁ : ∀ α ∈ S₁, e6T3W • α ∈ S₁
  hS₂r : ∀ α ∈ S₂, IsRoot Tag.E6 α
  hvS₂ : ∀ α ∈ S₂, e6T3W • α ∈ S₂
  hKL : KL.P = ![rootSpan Tag.E6 (AlgebraicClosure F) S₁ ⊓
      twistedFixedPoints (phi3N (AlgebraicClosure F))
        (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n))),
      rootSpan Tag.E6 (AlgebraicClosure F) S₂ ⊓
      twistedFixedPoints (phi3N (AlgebraicClosure F))
        (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)))]
  hdvdP : ∀ i, p ∣ Nat.card ↥(KL.P i)
  z_L : ModGL Tag.E6 (AlgebraicClosure F)
  hzA : z_L ∈ A
  hzLx : z_L ∉ Subgroup.zpowers x_L
  hS₁z : S₁ ⊆ torusRootKernel z_L
  z : adjointGroup Tag.E6 F
  hzQ : z ∈ Q
  hzLz : z_L = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * z * c⁻¹) * g0

structure E6ThreeLayerData (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã) : Type where
  ψ : ↥(Subgroup.centralizer ({D₁.x} : Set (adjointGroup Tag.E6 F))) →*
      ModGL Tag.E6 (AlgebraicClosure F)
  hψinj : Function.Injective ψ
  hψ : ∀ y, ψ y = D₁.g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F)
      (D₁.c * (y : Subgroup.centralizer ({D₁.x} : Set (adjointGroup Tag.E6 F))) *
        D₁.c⁻¹) * D₁.g0
  hP0 : D₁.KL.P 0 = rootSpan Tag.E6 (AlgebraicClosure F) D₁.S₁ ⊓
      twistedFixedPoints (phi3N (AlgebraicClosure F))
        (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)))
  hJleC : centralizerLayerPullback ψ (D₁.KL.P 0) ≤
      Subgroup.centralizer ({D₁.x} : Set (adjointGroup Tag.E6 F))
  hJn : Subgroup.Normal ((centralizerLayerPullback ψ (D₁.KL.P 0)).subgroupOf
      (Subgroup.centralizer ({D₁.x} : Set (adjointGroup Tag.E6 F))))
  hJq : CFSG.Open.IsQuasisimple ↥(centralizerLayerPullback ψ (D₁.KL.P 0))
  hpJ : p ∣ Nat.card (centralizerLayerPullback ψ (D₁.KL.P 0))
  hJ₁leC : centralizerLayerPullback ψ (D₁.KL.P 1) ≤
      Subgroup.centralizer ({D₁.x} : Set (adjointGroup Tag.E6 F))
  hJ₁q : CFSG.Open.IsQuasisimple ↥(centralizerLayerPullback ψ (D₁.KL.P 1))
  eJ : ↥(centralizerLayerPullback ψ (D₁.KL.P 0)) ≃* SL(3, F)
  eJ₁ : ↥(centralizerLayerPullback ψ (D₁.KL.P 1)) ≃* SL(3, F)
  hcommJ : ∀ a ∈ centralizerLayerPullback ψ (D₁.KL.P 0),
      ∀ b ∈ centralizerLayerPullback ψ (D₁.KL.P 1), Commute a b

structure E6ThreeCentreData (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã) (D₂ : E6ThreeLayerData F n p q Ã D₁) : Type where
  hqdiv' : q ∣ Nat.card F - 1
  s : ↥(centralizerLayerPullback D₂.ψ (D₁.KL.P 1))
  hsZ : s ∉ Subgroup.center ↥(centralizerLayerPullback D₂.ψ (D₁.KL.P 1))
  hsq : orderOf s = q
  hinf_center : Subgroup.zpowers s ⊓
      Subgroup.center ↥(centralizerLayerPullback D₂.ψ (D₁.KL.P 1)) = ⊥

def e6Three_frame_data (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 3) (hq : q.Prime)
    (Ã : Subgroup ↥(e6Data_valid.minGroup F)) (hAe : IsElemAbelian p Ã)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤
      CFSG.Open.pRank p Ã)
    (hA3 : 3 ≤ CFSG.Open.pRank p Ã) :
    E6ThreeFrameData F n p q Ã := by
  refine Classical.choice ?_
  letI : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hp5 : 5 < p := by have := seven_le_of_card hcard hp hp2 hrk; omega
  have hpq : p ∣ Nat.card F ^ 2 + Nat.card F + 1 := three_dvd_card_sq_add hcard hp hp2 hrk
  have hker : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)
  set Q : Subgroup (adjointGroup Tag.E6 F) := Ã.map (e6Isogeny F) with hQdef
  have hQel : IsElemAbelian p Q := CFSG.SectionRank.isElemAbelian_map hAe (e6Isogeny F)
  obtain ⟨g0, c, A, hAeq, hAT, hAel, hAcardA, hg0C, hg0, hperf⟩ :=
    exists_frame_image hcard hn hp hp2 hrk hAe hmax
  obtain ⟨x_L, hxLA, hxL1, hxker⟩ := exists_A2A2_point hcard hn hp hp2 hrk hAel hAcardA hAT
  have hxA : x_L ∈ A := hxLA
  have hxLT : x_L ∈ twistedTorus (phi3N (AlgebraicClosure F))
      (iterateFrobenius (AlgebraicClosure F) 2 n) := hAT hxLA
  rw [hAeq, mem_frameImage] at hxLA
  obtain ⟨x, hxQ, hxLx⟩ := hxLA
  have hxne : x ≠ 1 := by
    intro h1
    apply hxL1
    rw [hxLx, h1]
    simp
  have hxord : orderOf x = p := orderOf_eq_prime (hQel.2 x hxQ) hxne
  have hf : 1 ≤ n := by omega
  have hFr : ∀ c : AlgebraicClosure F,
      iterateFrobenius (AlgebraicClosure F) 2 n c = c ^ (2 ^ n) :=
    fun c => iterateFrobenius_def 2 n c
  have hFrK : ∀ c : AlgebraicClosure F,
      iterateFrobenius (AlgebraicClosure F) 2 n c = c ^ Nat.card F := by
    intro c; rw [hFr, hcard]
  obtain ⟨w, S₁, S₂, KL, _, hw₁, hw₂, hS₁r, hvS₁, hS₂r, hvS₂, hKL, hdvdP⟩ :=
    CFSG.RankThree.PartOne.KE6.NonsplitLayers.phi3_A2A2_kernelLayer_dvd_P
      (K := F) (Ω := AlgebraicClosure F) hf hcard hFr hxLT hxker hpq
  have hS₁neg : ∀ α ∈ S₁, -α ∈ S₁ :=
    neg_stable_of_image_parabolicRoots (L := AlgebraicClosure F) hw₁
  have hS₁card : S₁.ncard = 6 :=
    ncard_of_image_parabolicRoots (L := AlgebraicClosure F) hw₁
  set β : Fin Tag.E6.rank → ℤ := Pi.single (e6Index 0) 1 with hβdef
  have hβP : β ∈ parabolicRoots Tag.E6 support13 :=
    single_mem_parabolicRoots ((mem_support13 (e6Index 0)).2 (Or.inl rfl))
  have hmemα : w • (w⁻¹ • β) ∈ (w • ·) '' S₁ := by
    rw [hw₁]; simpa using hβP
  obtain ⟨α, hα, hwα⟩ := hmemα
  have hαeq : α = w⁻¹ • β := by
    have h := congrArg (fun z => w⁻¹ • z) hwα
    simpa using h
  rw [hαeq] at hα
  obtain ⟨z_L, hzLA, hzLx, hS₁z⟩ :=
    exists_second_point_of_stable (Ω := AlgebraicClosure F) hp5 hFrK hAel hAcardA hAT
      hxA hxL1 hS₁r hS₁neg hvS₁ hS₁card hα
  have hzA : z_L ∈ A := hzLA
  rw [hAeq, mem_frameImage] at hzLA
  obtain ⟨z, hzQ, hzLz⟩ := hzLA
  exact ⟨
    { Q := Q, hQdef := hQdef, hQel := hQel, hker := hker, g0 := g0, c := c, A := A,
      hAT := hAT, hg0C := hg0C, hg0 := hg0, hperf := hperf, x_L := x_L,
      hxLT := hxLT, x := x, hxQ := hxQ, hxLx := hxLx, hxne := hxne, hxord := hxord,
      hf := hf, hFr := hFr, w := w, S₁ := S₁, S₂ := S₂, KL := KL, hw₁ := hw₁,
      hw₂ := hw₂, hS₁r := hS₁r, hvS₁ := hvS₁, hS₂r := hS₂r, hvS₂ := hvS₂,
      hKL := hKL, hdvdP := hdvdP, z_L := z_L, hzA := hzA, hzLx := hzLx,
      hS₁z := hS₁z, z := z, hzQ := hzQ, hzLz := hzLz }⟩

def e6Three_layer_data (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hcard : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 3)
    (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D : E6ThreeFrameData F n p q Ã) :
    E6ThreeLayerData F n p q Ã D := by
  refine Classical.choice ?_
  obtain ⟨_, _, _, _, g0, c, _, _, hg0C, hg0, hperf, x_L, hxLT, x, _, hxLx,
    _, hxord, hf, hFr, w, S₁, S₂, KL, hw₁, hw₂, hS₁r, hvS₁, hS₂r, hvS₂, hKL,
    hdvdP, _, _, _, _, _, _, _⟩ := D
  classical
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hp5 : 5 < p := by have := seven_le_of_card hcard hp hp2 hrk; omega
  have hpq : p ∣ Nat.card F ^ 2 + Nat.card F + 1 := three_dvd_card_sq_add hcard hp hp2 hrk
  have hpqi : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + (Nat.card F : ℤ) + 1 :=
    three_dvd_card_sq_add_int hcard hp hp2 hrk
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hPψ⟩ :=
    exists_psi_of_kernelLayer (F := F) hcard hp hp5 hpqi hg0C hg0 hperf hxLx hxLT hxord KL
  have hnorm0 : ∀ d : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F))),
      ∀ u ∈ KL.P 0, ψ d * u * (ψ d)⁻¹ ∈ KL.P 0 :=
    fun d u hu => KL.norm 0 (ψ d) (hψHQ d) (hψR d) u hu
  have hnorm1 : ∀ d : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F))),
      ∀ u ∈ KL.P 1, ψ d * u * (ψ d)⁻¹ ∈ KL.P 1 :=
    fun d u hu => KL.norm 1 (ψ d) (hψHQ d) (hψR d) u hu
  have hJdata := centralizerLayerPullback_data
    (C := Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)))
    (ψ := ψ) hψinj (hPψ 0) (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (KL.quasi 0)) hnorm0
  obtain ⟨hJleC, hJn, hJq, hJcard⟩ := hJdata
  have hJ₁data := centralizerLayerPullback_data
    (C := Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)))
    (ψ := ψ) hψinj (hPψ 1) (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (KL.quasi 1)) hnorm1
  obtain ⟨hJ₁leC, hJ₁n, hJ₁q, hJ₁card⟩ := hJ₁data
  have hpJ : p ∣ Nat.card (centralizerLayerPullback ψ (KL.P 0)) := by
    rw [hJcard]; exact hdvdP 0
  have hpJ₁ : p ∣ Nat.card (centralizerLayerPullback ψ (KL.P 1)) := by
    rw [hJ₁card]; exact hdvdP 1
  set Nw : ModGL Tag.E6 (AlgebraicClosure F) := canonicalRep (coxeterSystem Tag.E6)
    (AlgebraicClosure F) w with hNw
  have hQ₁ : (rootSpan Tag.E6 (AlgebraicClosure F) S₁).map
      (MulAut.conj Nw).toMonoidHom = subsystemGroup Tag.E6 (AlgebraicClosure F) support13 := by
    rw [(canonical_weyl_root_transport Tag.E6 (AlgebraicClosure F)).1 w S₁ hS₁r, hw₁,
      subsystemGroup_eq_rootSpan]
  have hQ₂ : (rootSpan Tag.E6 (AlgebraicClosure F) S₂).map
      (MulAut.conj Nw).toMonoidHom = subsystemGroup Tag.E6 (AlgebraicClosure F) support56 := by
    rw [(canonical_weyl_root_transport Tag.E6 (AlgebraicClosure F)).1 w S₂ hS₂r, hw₂,
      subsystemGroup_eq_rootSpan]
  have hsep : IsSeparated support13 support56 := by
    intro a ha b hb
    have ha' : a = e6Index 0 ∨ a = e6Index 2 := (mem_support13 a).1 ha
    have hb' : b = e6Index 4 ∨ b = e6Index 5 := (mem_support56 b).1 hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> decide
  have hcommP : ∀ a ∈ KL.P 0, ∀ b ∈ KL.P 1, Commute a b := by
    intro a ha b hb
    have haP : a ∈ rootSpan Tag.E6 (AlgebraicClosure F) S₁ := by
      have h := ha; rw [hKL] at h; simpa using h |>.1
    have hbP : b ∈ rootSpan Tag.E6 (AlgebraicClosure F) S₂ := by
      have h := hb; rw [hKL] at h; simpa using h |>.1
    have haN : Nw * a * Nw⁻¹ ∈ subsystemGroup Tag.E6 (AlgebraicClosure F) support13 := by
      rw [← hQ₁]; exact Subgroup.mem_map_of_mem _ haP
    have hbN : Nw * b * Nw⁻¹ ∈ subsystemGroup Tag.E6 (AlgebraicClosure F) support56 := by
      rw [← hQ₂]; exact Subgroup.mem_map_of_mem _ hbP
    have hc := commute_of_isSeparated hsep haN hbN
    have h' : a * b = b * a := by
      have h := congrArg (fun z => Nw⁻¹ * z * Nw) hc.eq
      simpa [mul_assoc] using h
    exact h'
  have hcommJ : ∀ a ∈ centralizerLayerPullback ψ (KL.P 0),
      ∀ b ∈ centralizerLayerPullback ψ (KL.P 1), Commute a b :=
    map_comap_commute hψinj (fun a ha b hb => (hcommP a ha b hb).eq)
  have hP0 : KL.P 0 = rootSpan Tag.E6 (AlgebraicClosure F) S₁ ⊓
      twistedFixedPoints (phi3N (AlgebraicClosure F))
        (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n))) := by
    have := congrFun hKL 0; simpa using this
  have hP1 : KL.P 1 = rootSpan Tag.E6 (AlgebraicClosure F) S₂ ⊓
      twistedFixedPoints (phi3N (AlgebraicClosure F))
        (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n))) := by
    have := congrFun hKL 1; simpa using this
  obtain ⟨eP0, eP1, -, -⟩ := phi3_A2A2_layer_equivs (Ω := AlgebraicClosure F)
    (Fr := iterateFrobenius (AlgebraicClosure F) 2 n) hf hcard hFr hS₁r hvS₁ hw₁ hS₂r hvS₂ hw₂ hpq
  have hJequiv : Nonempty (↥(centralizerLayerPullback ψ (KL.P 0)) ≃* SL(3, F)) :=
    ⟨(comapMapMulEquiv hψinj (hPψ 0)).trans
      ((MulEquiv.subgroupCongr hP0).trans (Classical.choice eP0))⟩
  have hJ₁equiv : Nonempty (↥(centralizerLayerPullback ψ (KL.P 1)) ≃* SL(3, F)) :=
    ⟨(comapMapMulEquiv hψinj (hPψ 1)).trans
      ((MulEquiv.subgroupCongr hP1).trans (Classical.choice eP1))⟩
  obtain ⟨eJ⟩ := hJequiv
  obtain ⟨eJ₁⟩ := hJ₁equiv
  exact ⟨
    { ψ := ψ, hψinj := hψinj, hψ := hψ, hP0 := hP0, hJleC := hJleC, hJn := hJn,
      hJq := hJq, hpJ := hpJ, hJ₁leC := hJ₁leC, hJ₁q := hJ₁q, eJ := eJ, eJ₁ := eJ₁,
      hcommJ := hcommJ }⟩

def e6Three_centre_data (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hq : q.Prime) (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (Ã : Subgroup ↥(e6Data_valid.minGroup F))
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁) :
    E6ThreeCentreData F n p q Ã D₁ D₂ := by
  refine Classical.choice ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, KL, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := D₁
  obtain ⟨ψ, _, _, _, _, _, _, _, _, _, _, eJ₁, _⟩ := D₂
  have hqdiv' : q ∣ Nat.card F - 1 := by
    rcases hqdiv with h | ⟨hn1, -⟩
    · rwa [hcard]
    · omega
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨T, hTle, hTel, hTcard⟩ :=
    exists_elemAbelian_le_of_mulEquiv
      (e := eJ₁.trans (Subgroup.topEquiv (G := SL(3, F))).symm)
      (T := LinEngine.diagSLSub (F := F) 2 q) le_top
      (LinEngine.isElemAbelian_diagSLSub (F := F))
      (LinEngine.card_diagSLSub (F := F) hqdiv')
  let eZ : ↥(Subgroup.center ↥(centralizerLayerPullback ψ (KL.P 1))) ≃
      ↥(Subgroup.center (SL(3, F))) :=
    Equiv.subtypeEquiv eJ₁.toEquiv (fun y => by
      exact ⟨fun hy => MulEquivClass.apply_mem_center eJ₁ hy,
        fun hy => by
          rw [Subgroup.mem_center_iff] at hy ⊢
          intro g
          have h := hy (eJ₁ g)
          exact eJ₁.injective (by simpa using h)⟩)
  have hdvdZ : Nat.card (Subgroup.center ↥(centralizerLayerPullback ψ (KL.P 1))) ∣
      Nat.gcd 3 (Nat.card F - 1) := by
    rw [Nat.card_congr eZ]
    exact CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3) (by norm_num) F
  have hZ : Nat.card (Subgroup.center ↥(centralizerLayerPullback ψ (KL.P 1))) ∣ 3 :=
    hdvdZ.trans (Nat.gcd_dvd_left 3 _)
  obtain ⟨s, hsJ, hsq₀, hsZ⟩ := exists_noncentral_of_elemAbelian
    (J := centralizerLayerPullback ψ (KL.P 1))
    (T := T) hTle hq hTel hTcard hZ
  let s' : ↥(centralizerLayerPullback ψ (KL.P 1)) := ⟨s, hsJ⟩
  have hsq : orderOf s' = q := by
    rw [← Subgroup.orderOf_coe]
    exact hsq₀
  have hinf_center :
      Subgroup.zpowers s' ⊓ Subgroup.center ↥(centralizerLayerPullback ψ (KL.P 1)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hys, hyz⟩ := Subgroup.mem_inf.mp hy
    by_contra hy1
    have hdvd : orderOf y ∣ q := by
      rw [← hsq]; exact orderOf_dvd_of_mem_zpowers hys
    have hyq : orderOf y = q := by
      rcases (Nat.dvd_prime hq).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1
      · exact h
    have hsy : Subgroup.zpowers s' = Subgroup.zpowers y := by
      have hle : Subgroup.zpowers y ≤ Subgroup.zpowers s' := Subgroup.zpowers_le.mpr hys
      have hcard : Nat.card ↥(Subgroup.zpowers s') ≤ Nat.card ↥(Subgroup.zpowers y) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hsq, hyq]
      exact (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers y)
        (K := Subgroup.zpowers s') hle hcard).symm
    have hs_y : s' ∈ Subgroup.zpowers y := by
      rw [← hsy]; exact Subgroup.mem_zpowers s'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hs_y
    refine hsZ (by
      change s' ∈ Subgroup.center ↥(centralizerLayerPullback ψ (KL.P 1))
      rw [← hm]
      exact Subgroup.zpow_mem _ hyz m)
  exact ⟨
    { hqdiv' := hqdiv', s := s', hsZ := hsZ, hsq := hsq, hinf_center := hinf_center }⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
