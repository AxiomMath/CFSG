module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Comp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CoreRows

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.ClassicalInvolution.ModelFacts
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.Burgoyne.E2 CFSG.ComponentClassification.Burgoyne.E2.TwE7
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups


theorem outerCoreAt_twisted_three {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p] {g : adjointGroup .E7 K} {a : Fin Tag.E7.rank → Kˣ}
    {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps) (h3 : r.mask = 3) {g₁ : ModGL .E7 L}
    (hg₁G : g₁ ∈ adjointGroup .E7 L)
    (hconj : g₁ * liftElt (algebraMap K L) (g : ModGL .E7 K) a * g₁⁻¹ =
      rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)))
    (hcoc : g₁ * (frobTwistGL .E7 L p f 1 g₁)⁻¹ = wordWeylMatrix .E7 L e7Word2_1) :
    OuterCoreAt (MulAut.conj g * rootDiagAut .E7 K a) := by
  classical
  have hp : p.Prime := Fact.out
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hinj, -, -, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L
    (algebraMap K L)
  set R := fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1) with hR
  set Ψ : adjointGroup .E7 K →* ModGL .E7 L := (MulAut.conj g₁).toMonoidHom.comp (embE7 L)
    with hΨ
  have hΨinj : Function.Injective Ψ :=
    (MulAut.conj g₁).injective.comp (hinj.comp Subtype.val_injective)
  have hΨc : ∀ c, g₁⁻¹ * Ψ c * g₁ = embE7 L c := fun c => by
    change g₁⁻¹ * (g₁ * embE7 L c * g₁⁻¹) * g₁ = _
    group
  have hH := map_adjointGroup_eq_commutator L hp2 hK
  have hRR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hιH : ∀ c, embE7 L c ∈ ⁅R, R⁆ := fun c => by
    rw [← hH]
    exact Subgroup.mem_map_of_mem _ c.2
  have hΨG : ∀ c, Ψ c ∈ adjointGroup .E7 L := fun c =>
    mul_mem (mul_mem hg₁G (mem_fixedPointsIn.1 (hRR (hιH c))).1) (inv_mem hg₁G)
  have hmemΨ : ∀ w, g₁⁻¹ * w * g₁ ∈ ⁅R, R⁆ → w ∈ Ψ.range := by
    intro w hw
    rw [← hH] at hw
    obtain ⟨c, hc, hcw⟩ := hw
    refine ⟨⟨c, hc⟩, ?_⟩
    change g₁ * baseChangeGL (algebraMap K L) c * g₁⁻¹ = w
    rw [hcw]
    group
  obtain ⟨D, -, u, -, hDe, hDχ, hDθ, hsub, hqs, hu, hCY, hYC⟩ := exists_twisted_layer hp2 hf hk
    hr (e7Word2_1_mem_omegaWords hr (Or.inr h3)) e7Word2_1_ne_nil hg₁G hconj hcoc
  have hχ3 : D.χ = signMaskChar .E7 3 := by rw [hDχ, h3]
  set C' := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC'
  set N := (twCent p L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a)).map
    (MulAut.conj g₁).toMonoidHom with hN
  have hYΨ : N ≤ Ψ.range := by
    rintro _ ⟨y, hy, rfl⟩
    refine hmemΨ _ ?_
    change g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ ∈ _
    rw [show g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ = y by group]
    exact (Subgroup.mem_inf.1 hy).1
  have hC'Ψ : C' ≤ Ψ.range := hCY.trans hYΨ
  have hMG : torusGroup .E7 L ⊔ rootSpan .E7 L (kernelRoots (signMaskChar .E7 r.mask)) ≤
      adjointGroup .E7 L := sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _)
  have huG : u ∈ adjointGroup .E7 L := hMG hu
  have hmap : (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)).map Ψ = N := by
    rw [hN, hΨ, ← Subgroup.map_map, map_fixedSubgroup_eq_twCent L hp2 hK g a]
  have hC'n : (C'.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCY]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e := hYC y hy
    constructor
    · intro hh
      rw [← e]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← e] at hh
      obtain ⟨h', hh', he⟩ := hh
      have he' : y * h' * y⁻¹ = y * h * y⁻¹ := he
      rwa [← mul_left_cancel (mul_right_cancel he')]
  have hC'q : GorensteinWalter.IsQuasisimple C' :=
    HarrisLit.L33.SR.E1.gw_isQuasisimple_of_mulEquiv
      (D.orbitGroup.equivMapOfInjective _ (MulAut.conj u).injective)
      (HarrisLit.L33.SR.E1.gw_isQuasisimple_of_isQuasisimple hqs)
  obtain ⟨hX, -⟩ := HarrisLit.L33.SR.E1.isComponentOf_oddFixed_of_map
    (MulAut.conj g * rootDiagAut .E7 K a) Ψ hΨinj hmap hCY hC'n.isSubnormal hC'q
  have hdiag : ∀ x : adjointGroup .E7 K, (∀ y ∈ C'.comap Ψ, x * y * x⁻¹ = y) →
      ∃ b : Fin (Tag.rank .E7) → Lˣ, u⁻¹ * Ψ x * u = rootDiagUnit .E7 b := by
    intro x hx
    have hcC : ∀ w ∈ D.orbitGroup, (u⁻¹ * Ψ x * u) * w = w * (u⁻¹ * Ψ x * u) := by
      intro w hw
      obtain ⟨q, hq⟩ := hC'Ψ ⟨w, hw, rfl⟩
      have hqX : q ∈ C'.comap Ψ := by
        change Ψ q ∈ C'
        rw [hq]
        exact ⟨w, hw, rfl⟩
      have h := congrArg Ψ (hx q hqX)
      rw [map_mul, map_mul, map_inv, hq] at h
      change Ψ x * (u * w * u⁻¹) * (Ψ x)⁻¹ = u * w * u⁻¹ at h
      calc u⁻¹ * Ψ x * u * w = u⁻¹ * (Ψ x * (u * w * u⁻¹) * (Ψ x)⁻¹) * Ψ x * u := by group
        _ = u⁻¹ * (u * w * u⁻¹) * Ψ x * u := by rw [h]
        _ = w * (u⁻¹ * Ψ x * u) := by group
    obtain ⟨b, hb, -, -⟩ := eq_of_commute_orbitGroup_three D (TwE7.three_le_q D) hχ3 hDθ
      (mul_mem (mul_mem (inv_mem huG) (hΨG x)) huG) hcC
    exact ⟨b, hb⟩
  refine outerCoreAt_of_component (center_adjointGroup_eq_bot_field .E7 K) hX ?_ ?_
  ·
    intro β hβ _ hfix
    refine mem_inner_of_odd_fix_orbitGroup (u := u) (g₁ := g₁) hK D hDe hDθ
      (four_mem_simpleRootsJ D (Or.inr rfl) hχ3) (fun w hw => ?_) hβ fun t ⟨w, hw, ht⟩ =>
        hfix t ?_
    · obtain ⟨c, hc⟩ := hC'Ψ ⟨w, hw, rfl⟩
      refine ⟨(c : ModGL .E7 K), c.2, ?_⟩
      change embE7 L c = _
      rw [← hΨc, hc]
      rfl
    · change g₁ * baseChangeGL (algebraMap K L) (t : ModGL .E7 K) * g₁⁻¹ ∈ C'
      rw [ht, show g₁ * (g₁⁻¹ * (u * w * u⁻¹) * g₁) * g₁⁻¹ = u * w * u⁻¹ by group]
      exact ⟨w, hw, rfl⟩
  ·
    intro c c' _ _ _ _ hcX hc'X
    obtain ⟨b, hb⟩ := hdiag c hcX
    obtain ⟨b', hb'⟩ := hdiag c' hc'X
    have hbb : rootDiagUnit .E7 b * rootDiagUnit .E7 b' =
        rootDiagUnit .E7 b' * rootDiagUnit .E7 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    apply hΨinj
    rw [map_mul, map_mul]
    calc Ψ c * Ψ c' = u * ((u⁻¹ * Ψ c * u) * (u⁻¹ * Ψ c' * u)) * u⁻¹ := by group
      _ = u * ((u⁻¹ * Ψ c' * u) * (u⁻¹ * Ψ c * u)) * u⁻¹ := by rw [hb, hb', hbb]
      _ = Ψ c' * Ψ c := by group

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7
