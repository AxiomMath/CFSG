module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnCoord
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnStab
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnTorus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpTwist
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Twist
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KGD.D4Frame
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Lang

open scoped CFSG.ConvolutionPoints

open CFSG.ClassicalInvolution.ModelFacts.Levi in
theorem ap_lang_M {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) {L : Type} [Field L] [CharP L p]
    [IsAlgClosed L] {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2) :
    ∃ m ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2,
      u = m⁻¹ * (trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) m *
        (trialityOpposition L)⁻¹) := by
  classical
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  set z : ModGL TwistTag.D4.tag L := trialityOpposition L with hz
  set a : Fin TwistTag.D4.tag.rank → Lˣ := ![A, A, 1, A] with ha
  set M : Subgroup (ModGL TwistTag.D4.tag L) :=
    torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2 with hM
  have hkerχ : kernelRoots (rootCharHom a) = d4LongA2 := by
    ext α
    exact d4Minus_rootCharKernel hA3 hA1 α
  have hconn : IsConnectedAlgebraicSubgroup L
      (M.map (modGLPoint TwistTag.D4.tag L).toMonoidHom) := by
    have h :=
      CFSG.ClassicalInvolution.ModelFacts.Levi.isConnectedAlgebraicSubgroup_torus_sup_rootSpan
        (k := L) (rootCharHom a)
    rwa [hkerχ] at h
  obtain ⟨hsm, -, -⟩ := hconn.smooth
  have key : ∀ g, frobTwistGL TwistTag.D4.tag L p f (z * diagramMap TwistTag.D4 L) g =
      z * twistHom TwistTag.D4 L Fr g * z⁻¹ := by
    intro g
    rw [frobTwistGL_apply]
    change (z * diagramMap TwistTag.D4 L) * entrywiseFrobGL TwistTag.D4.tag L p f g *
      (z * diagramMap TwistTag.D4 L)⁻¹ = z * (diagramMap TwistTag.D4 L *
        entrywiseFrobGL TwistTag.D4.tag L p f g * (diagramMap TwistTag.D4 L)⁻¹) * z⁻¹
    group
  have hMS : ∀ g ∈ M, frobTwistGL TwistTag.D4.tag L p f (z * diagramMap TwistTag.D4 L) g ∈ M := by
    intro g hg
    rw [key]
    have hle : M ≤ M.comap ((MulAut.conj z).toMonoidHom.comp (twistHom TwistTag.D4 L Fr)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · change z * twistHom TwistTag.D4 L Fr x * z⁻¹ ∈ M
        rw [trialityOpposition_twistHom_torus Fr hx]
        exact Subgroup.mem_sup_left (inv_mem (twistHom_mem_torusGroup_d4 Fr hx))
      · change z * twistHom TwistTag.D4 L Fr x * z⁻¹ ∈ M
        exact Subgroup.mem_sup_right (mp_conj_z0_rootSpan (twistHom_mem_rootSpan_d4LongA2 f hx))
    exact hle hg
  obtain ⟨m, hm, h⟩ := exists_eq_inv_mul_frobTwistGL p hf (z * diagramMap TwistTag.D4 L) hconn hsm
    hMS hu
  exact ⟨m, hm, by rw [h, key]⟩

end Lang

theorem ap_fuse {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) {L : Type} [Field L] [CharP L p]
    [IsAlgClosed L] {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    {g₀ c X₁ X₂ : ModGL TwistTag.D4.tag L} (hg₀ : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hFg₀ : twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L)
    (hcG : c ∈ adjointGroup TwistTag.D4.tag L)
    (hX₁ : X₁ = g₀ * rootDiagUnit TwistTag.D4.tag
      (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) * g₀⁻¹)
    (hFX₁ : twistHom TwistTag.D4 L (iterateFrobenius L p f) X₁ = X₁)
    (hFX₂ : twistHom TwistTag.D4 L (iterateFrobenius L p f) X₂ = X₂)
    (hc : c * X₁ * c⁻¹ = X₂) :
    ∃ c' ∈ adjointGroup TwistTag.D4.tag L,
      twistHom TwistTag.D4 L (iterateFrobenius L p f) c' = c' ∧ c' * X₁ * c'⁻¹ = X₂ := by
  classical
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  set F := twistHom TwistTag.D4 L Fr with hFdef
  set z : ModGL TwistTag.D4.tag L := trialityOpposition L with hz
  set a : Fin TwistTag.D4.tag.rank → Lˣ := ![A, A, 1, A] with ha
  set d : ModGL TwistTag.D4.tag L := rootDiagUnit TwistTag.D4.tag a with hd
  set M : Subgroup (ModGL TwistTag.D4.tag L) :=
    torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2 with hM
  have hker : ∀ α, α ∈ rootCharKernel a ↔ α ∈ d4LongA2 := d4Minus_rootCharKernel hA3 hA1
  set u : ModGL TwistTag.D4.tag L := g₀⁻¹ * (c⁻¹ * F c) * g₀ with hu
  have hFc : F c * X₁ * (F c)⁻¹ = X₂ := by
    have h := congrArg F hc
    rwa [map_mul, map_mul, map_inv, hFX₁, hFX₂] at h
  have hd' : d = g₀⁻¹ * X₁ * g₀ := by
    rw [hX₁]
    group
  have hucomm : u * d = d * u := by
    have h1 : (c⁻¹ * F c) * X₁ = X₁ * (c⁻¹ * F c) := by
      calc (c⁻¹ * F c) * X₁ = c⁻¹ * (F c * X₁ * (F c)⁻¹) * F c := by group
        _ = c⁻¹ * (c * X₁ * c⁻¹) * F c := by rw [hFc, hc]
        _ = X₁ * (c⁻¹ * F c) := by group
    calc u * d = g₀⁻¹ * ((c⁻¹ * F c) * X₁) * g₀ := by rw [hu, hd']; group
      _ = g₀⁻¹ * (X₁ * (c⁻¹ * F c)) * g₀ := by rw [h1]
      _ = d * u := by rw [hu, hd']; group
  have huG : u ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem (inv_mem hg₀) (mul_mem (inv_mem hcG)
      (twistHom_mem_adjointGroup TwistTag.D4 L Fr hcG))) hg₀
  have hS : ∀ α ∈ d4LongA2, IsRoot TwistTag.D4.tag α := fun _ h => d4LongA2_isRoot h
  have hcen := mem_torus_mul_rootSpan_of_commute_of_stab (d4_stab_three_A2 hA3 hA1) hS
    (fun α hα => d4LongA2_neg_mem hα) (fun α hα => (hker α).1 hα) huG hucomm
  have huM : u ∈ M := by
    obtain ⟨h, hh, r, hr, hhr⟩ := Set.mem_mul.1 hcen
    rw [← hhr]
    exact Subgroup.mul_mem_sup hh hr
  obtain ⟨m, hmM, hum⟩ := ap_lang_M hf hA3 hA1 huM
  have hMcent : ∀ x ∈ M, x * d = d * x := by
    have hle : M ≤ Subgroup.centralizer ({d} : Set (ModGL TwistTag.D4.tag L)) := by
      refine sup_le (fun x hx => ?_) (rootSpan_le_centralizer a (fun α hα => (hker α).2 hα))
      exact Subgroup.mem_centralizer_singleton_iff.2
        (torusGroup_comm hx (rootDiagUnit_mem_torusGroup a))
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hMG : M ≤ adjointGroup TwistTag.D4.tag L :=
    sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L d4LongA2)
  have hmG := hMG hmM
  have hmd := hMcent m hmM
  refine ⟨c * g₀ * m⁻¹ * g₀⁻¹, mul_mem (mul_mem (mul_mem hcG hg₀) (inv_mem hmG)) (inv_mem hg₀),
    ?_, ?_⟩
  ·
    have hFcu : F c = c * g₀ * u * g₀⁻¹ := by
      rw [hu]
      group
    have e1 : F (c * g₀ * m⁻¹ * g₀⁻¹) = F c * (g₀ * z) * (F m)⁻¹ * (g₀ * z)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hFg₀]
    have hum' : u = m⁻¹ * (z * F m * z⁻¹) := hum
    have e2 : u * (z * F m * z⁻¹)⁻¹ = m⁻¹ := by
      rw [hum']
      group
    calc F (c * g₀ * m⁻¹ * g₀⁻¹) = F c * (g₀ * z) * (F m)⁻¹ * (g₀ * z)⁻¹ := e1
      _ = c * g₀ * (u * (z * F m * z⁻¹)⁻¹) * g₀⁻¹ := by rw [hFcu]; group
      _ = c * g₀ * m⁻¹ * g₀⁻¹ := by rw [e2]
  ·
    have hmd' : m⁻¹ * d * m = d := by
      calc m⁻¹ * d * m = m⁻¹ * (d * m) := by group
        _ = m⁻¹ * (m * d) := by rw [← hmd]
        _ = d := by group
    calc c * g₀ * m⁻¹ * g₀⁻¹ * X₁ * (c * g₀ * m⁻¹ * g₀⁻¹)⁻¹
        = c * g₀ * (m⁻¹ * (g₀⁻¹ * X₁ * g₀) * m) * g₀⁻¹ * c⁻¹ := by group
      _ = c * g₀ * (m⁻¹ * d * m) * g₀⁻¹ * c⁻¹ := by rw [hd']
      _ = c * (g₀ * d * g₀⁻¹) * c⁻¹ := by rw [hmd']; group
      _ = X₂ := by rw [← hc, hX₁]

theorem ap_fuse_Y {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hFg₀ : twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L)
    {x x' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : triEmb K σ L x = g₀ * rootDiagUnit TwistTag.D4.tag
      (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) * g₀⁻¹)
    {c : ModGL TwistTag.D4.tag L} (hcG : c ∈ adjointGroup TwistTag.D4.tag L)
    (hc : c * triEmb K σ L x * c⁻¹ = triEmb K σ L x') :
    ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, y * x * y⁻¹ = x' := by
  classical
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  obtain ⟨c', hc'G, hFc', hc'⟩ := ap_fuse hf hA3 hA1 hg₀ hFg₀ hcG hx
    (triEmb_fixed Fr hcomm x) (triEmb_fixed Fr hcomm x') hc
  have hrange : c' ∈ (triEmb K σ L).range := by
    rw [triEmb_range hp hf hK hσ Fr hFr]
    exact Subgroup.mem_inf.2 ⟨hc'G, hFc'⟩
  obtain ⟨y, hy⟩ := hrange
  refine ⟨y, triEmb_injective (K := K) (σ := σ) (L := L) ?_⟩
  rw [map_mul, map_mul, map_inv, hy]
  exact hc'

end CFSG.GH74.GLS.Stage2.Bender.Thm1
