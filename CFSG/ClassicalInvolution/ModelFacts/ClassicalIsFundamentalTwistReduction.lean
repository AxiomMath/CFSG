module

public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3952
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups

open scoped CFSG.ConvolutionPoints

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem isFiniteToralTwistReduction_of_reps_exact (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {D : ModGL τ k}
    (hD : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (ρ : Equiv.Perm (Fin τ.rank))
    (hFd : ∀ b : Fin τ.rank → kˣ, (∀ i, b i = 1 ∨ b i = -1) →
      frobTwistGL τ k p e D (rootDiagUnit τ b) = rootDiagUnit τ fun i => b (ρ.symm i))
    (reps : List (SignRep τ))
    (hfix : ∀ r ∈ reps, permChar ρ (signMaskChar τ r.mask) = signMaskChar τ r.mask)
    (hrep : ∀ χ, permChar ρ χ ∈ charOrbit χ →
      ∃ r ∈ reps, χ ∈ charOrbit (signMaskChar τ r.mask))
    (hΩ : ∀ r ∈ reps, (kernelPosStabilizer (signMaskChar τ r.mask) : Set (WeylGroup τ)) =
      {w | ∃ l ∈ r.omegaWords, ToralSign.wordElt τ l = w})
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    {x : ModGL τ k} (hx : x ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ reps, ∃ l ∈ r.omegaWords,
      ToralSign.wordElt τ l ∈ kernelPosStabilizer (signMaskChar τ r.mask) ∧
      Finite (fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
        (frobTwistGL τ k p e (wordWeylMatrix τ k l * D))) ∧
      ∃ g₁ ∈ adjointGroup τ k,
        g₁ * x * g₁⁻¹ = rootDiagUnit τ (signCharTuple (k := k) (signMaskChar τ r.mask)) ∧
        g₁ * (frobTwistGL τ k p e D g₁)⁻¹ = wordWeylMatrix τ k l ∧
        ∀ ℓ : ℕ, ℓ.Prime → ∀ L : Subgroup (ModGL τ k),
          (L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
              fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
                Subgroup.centralizer {x} ∧
            CFSG.IsPComponent ℓ (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
              (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k)
                (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}))) →
          (L.map (MulAut.conj g₁).toMonoidHom ≤ fixedPointsIn
              (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
              (frobTwistGL τ k p e (wordWeylMatrix τ k l * D)) ∧
            CFSG.IsPComponent ℓ ((L.map (MulAut.conj g₁).toMonoidHom).subgroupOf
              (fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k
                (kernelRoots (signMaskChar τ r.mask)))
                (frobTwistGL τ k p e (wordWeylMatrix τ k l * D))))) := by
  classical
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set F := frobTwistGL τ k p e D with hF
  set R := fixedPointsIn (adjointGroup τ k) F with hR
  have hFG : ∀ g ∈ adjointGroup τ k, F g ∈ adjointGroup τ k := fun g hg =>
    conj_mem_adjointGroup_of_map_eq hD _ (entrywiseFrobGL_mem p e hg)
  obtain ⟨hxG, hxF⟩ := mem_fixedPointsIn.1 hx
  obtain ⟨g, hg, r, hr, hgx, hFt⟩ :=
    exists_conj_eq_rootDiagUnit_of_reps hp ρ F hFG hFd reps hfix hrep hxG hxF hx2
  set χ := signMaskChar τ r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk χ
  have hFgx : F g * x * (F g)⁻¹ = rootDiagUnit τ a := by
    rw [← hFt, ← hgx, map_mul, map_mul, map_inv, hxF]
  have hcZ : g * (F g)⁻¹ ∈ toralCentralizer τ k a := by
    refine mem_toralCentralizer.2 ⟨mul_mem hg (inv_mem (hFG g hg)), ?_⟩
    calc rootDiagUnit τ a * (g * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ =
        (g * x * g⁻¹) * (g * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ := by rw [hgx]
      _ = g * (F g)⁻¹ * (F g * x * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
      _ = g * (F g)⁻¹ := by rw [hFgx]; group
  obtain ⟨-, -, ⟨hMZ, hMn, -, -, eW, heW⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component τ k hk a ha
  obtain ⟨q, hq⟩ := eW.surjective (QuotientGroup.mk ⟨_, hcZ⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hwχ : w ∈ charStabilizer χ := (mem_rootCharStabilizer_signCharTuple hk χ).1 hw
  obtain ⟨u, hu, hωΩ⟩ := exists_mul_mem_kernelPosStabilizer hwχ
  set ω := w * u with hω_def
  have huW : u ∈ kernelReflectionGroup a := by
    rw [kernelReflectionGroup_signCharTuple hk]
    exact hu
  have hωa : ω ∈ rootCharStabilizer a :=
    (mem_rootCharStabilizer_signCharTuple hk χ).2 (kernelPosStabilizer_le hωΩ)
  have hmk : (QuotientGroup.mk ⟨w, hw⟩ : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) =
        QuotientGroup.mk ⟨ω, hωa⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change w⁻¹ * (w * u) ∈ kernelReflectionGroup a
    rw [inv_mul_cancel_left]
    exact huW
  rw [hmk, heW, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  change (canonicalRep (coxeterSystem τ) k ω)⁻¹ * (g * (F g)⁻¹) ∈ toralRootGroup τ k a at hq
  obtain ⟨l, hl, hlω⟩ : ∃ l ∈ r.omegaWords, ToralSign.wordElt τ l = ω := by
    have h1 : ω ∈ (kernelPosStabilizer χ : Set (WeylGroup τ)) := hωΩ
    rw [hΩ r hr] at h1
    exact h1
  set N := wordWeylMatrix τ k l with hN_def
  set n := canonicalRep (coxeterSystem τ) k ω with hn_def
  have hh₀ : N * n⁻¹ ∈ torusGroup τ k := by
    refine mem_torusGroup_of_mapsRootLines_one (mul_mem (wordWeylMatrix_mem_monomialSubgroup l)
      (inv_mem (canonicalRep_mem_monomialSubgroup k ω))) ?_
    have h := (mapsRootLines_wordWeylMatrix (k := k) l).mul
      (mapsRootLines_canonicalRep (R := k) ω).inv
    rwa [hlω, mul_inv_cancel] at h
  have hnZ : n ∈ toralCentralizer τ k a := canonicalRep_mem_toralCentralizer hωa
  have hNZ : N ∈ toralCentralizer τ k a := by
    have h := mul_mem (torusGroup_le_toralCentralizer a hh₀) hnZ
    rwa [inv_mul_cancel_right] at h
  have hcv : ∃ m ∈ toralRootGroup τ k a, g * (F g)⁻¹ = m * N := by
    refine ⟨(N * n⁻¹)⁻¹ * (N * (n⁻¹ * (g * (F g)⁻¹)) * N⁻¹), mul_mem
      (inv_mem (le_sup_left (a := torusGroup τ k) hh₀))
      ((Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hNZ) _).1 hq), ?_⟩
    group
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have := commutator_subgroupOf_normal R
  have := isSolvable_quotient_commutator_subgroupOf R
  obtain ⟨z, hzM, hzcoc, -, hQfin, -, -, hcomp⟩ :=
    rational_centralizer_cocycle_reduction_of_map_conj p hp he hD hRfin hRsub ha hg hgx hFt hNZ hcv
  have hSeq : (MulAut.conj N).toMonoidHom.comp F = frobTwistGL τ k p e (N * D) := by
    refine MonoidHom.ext fun y => ?_
    simp only [hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev]
    group
  rw [hSeq, toralRootGroup, hker] at hQfin hcomp
  have hzG : z ∈ adjointGroup τ k := (mem_toralCentralizer.1 (hMZ hzM)).1
  have hzd : z * rootDiagUnit τ a * z⁻¹ = rootDiagUnit τ a := by
    have h1 := (mem_toralCentralizer.1 (hMZ hzM)).2
    calc z * rootDiagUnit τ a * z⁻¹ = (rootDiagUnit τ a * z * (rootDiagUnit τ a)⁻¹) *
          rootDiagUnit τ a * z⁻¹ := by rw [h1]
      _ = rootDiagUnit τ a := by group
  refine ⟨r, hr, l, hl, by rw [hlω]; exact hωΩ, hQfin, z * g, mul_mem hzG hg, ?_, hzcoc,
    fun ℓ hℓ L hL => ((hcomp ℓ hℓ).1 L).1 hL⟩
  calc z * g * x * (z * g)⁻¹ = z * (g * x * g⁻¹) * z⁻¹ := by group
    _ = rootDiagUnit τ a := by rw [hgx, hzd]

end CFSG.ClassicalInvolution.ModelFacts
