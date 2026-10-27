module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Beta
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CoreRows
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Transfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaExc

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

theorem eq_one_of_pow_three_eq_one {L : Type} [Field L] [CharP L 3] {x : Lˣ} (hx : x ^ 3 = 1) :
    x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : ((x : L) - 1) ^ 3 = 0 := by
    rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, sub_self]
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h))

end CFSG.ComponentClassification.Burgoyne.E2

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.ClassicalInvolution.ModelFacts
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups


theorem eq_one_of_pow_three_twisted_three {f : ℕ} [Fact (Nat.Prime 3)] {K : Type} [Field K]
    [Finite K] [CharP K 3] (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 3] {g : adjointGroup .E7 K}
    {a : Fin Tag.E7.rank → Kˣ}
    {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps) (h3 : r.mask = 3) {g₁ : ModGL .E7 L}
    (hg₁G : g₁ ∈ adjointGroup .E7 L)
    (hconj : g₁ * liftElt (algebraMap K L) (g : ModGL .E7 K) a * g₁⁻¹ =
      rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)))
    (hcoc : g₁ * (frobTwistGL .E7 L 3 f 1 g₁)⁻¹ = wordWeylMatrix .E7 L e7Word2_1)
    {B : Subgroup (MulAut (adjointGroup .E7 K))}
    (hB : (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤ B)
    {y : MulAut (adjointGroup .E7 K)}
    (hy : y ∈ oddCoreIn B (MulAut.conj g * rootDiagAut .E7 K a)) (hy3 : y ^ 3 = 1) : y = 1 := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hk := isAlgebraic_zmod_of_isAlgClosure 3 K L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (Nat.odd_iff.2 rfl).pow
  obtain ⟨hinj, -, -, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L
    (algebraMap K L)
  set R := fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L 3 f 1) with hR
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
  have hYΨ : (twCent 3 L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a)).map
      (MulAut.conj g₁).toMonoidHom ≤ Ψ.range := by
    rintro _ ⟨y, hy, rfl⟩
    refine hmemΨ _ ?_
    change g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ ∈ _
    rw [show g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ = y by group]
    exact (Subgroup.mem_inf.1 hy).1
  have hC'Ψ := hCY.trans hYΨ
  have htw : ∀ c, (MulAut.conj g * rootDiagAut .E7 K a) c = c ↔
      Ψ c ∈ (twCent 3 L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a)).map
        (MulAut.conj g₁).toMonoidHom := by
    intro c
    have h := map_fixedSubgroup_eq_twCent L hp2 hK g a
    constructor
    · intro hc
      refine ⟨embE7 L c, ?_, rfl⟩
      rw [← h]
      exact ⟨c, hc, rfl⟩
    · rintro ⟨y, hy, hyc⟩
      rw [← h] at hy
      obtain ⟨c', hc', rfl⟩ := hy
      have : c' = c := hΨinj hyc
      rw [← this]
      exact hc'
  have hMG : torusGroup .E7 L ⊔ rootSpan .E7 L (kernelRoots (signMaskChar .E7 r.mask)) ≤
      adjointGroup .E7 L := sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _)
  have huG : u ∈ adjointGroup .E7 L := hMG hu
  set C' := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC'
  have hZ : center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot_field .E7 K
  have hqC' : IsQuasisimple C' := LocalCores.isQuasisimple_of_mulEquiv
    (D.orbitGroup.equivMapOfInjective _ (MulAut.conj u).injective) hqs
  let eQ : C'.comap Ψ ≃* C' := ((C'.comap Ψ).equivMapOfInjective Ψ hΨinj).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hC'Ψ))
  have hC'norm : ∀ c, (MulAut.conj g * rootDiagAut .E7 K a) c = c →
      ∀ w ∈ C', Ψ c * w * (Ψ c)⁻¹ ∈ C' := by
    intro c hc w hw
    have h := Subgroup.mem_map_of_mem (MulAut.conj (Ψ c)).toMonoidHom hw
    rw [hYC (Ψ c) ((htw c).1 hc)] at h
    exact h
  have hQα : C'.comap Ψ ≤ fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a) :=
    fun c hc => (htw c).2 (hCY hc)
  have hQN : fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a) ≤
      normalizer ((C'.comap Ψ : Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) := by
    intro c hc
    have hc' : (MulAut.conj g * rootDiagAut .E7 K a) c = c := hc
    rw [mem_normalizer_iff]
    intro q
    exact (conj_mem_comap_iff (hC'norm c hc') (hC'norm c⁻¹ (by rw [map_inv, hc'])) q).symm
  have hfixy : ∀ x ∈ C'.comap Ψ, y x = x := fun x hx =>
    fix_of_mem_oddCoreIn hZ hB (LocalCores.isQuasisimple_of_mulEquiv eQ.symm hqC') hQα hQN hy hx
  obtain ⟨c, rfl⟩ := mem_inner_of_odd_fix_orbitGroup (u := u) (g₁ := g₁) hK D hDe hDθ
    (four_mem_simpleRootsJ D (Or.inr rfl) hχ3) (fun w hw => by
      obtain ⟨c, hc⟩ := hC'Ψ ⟨w, hw, rfl⟩
      refine ⟨(c : ModGL .E7 K), c.2, ?_⟩
      change embE7 L c = _
      rw [← hΨc, hc]
      rfl) (odd_orderOf_of_mem_oddCoreIn hy) fun t ⟨w, hw, ht⟩ => hfixy t (by
      change g₁ * baseChangeGL (algebraMap K L) (t : ModGL .E7 K) * g₁⁻¹ ∈ C'
      rw [ht, show g₁ * (g₁⁻¹ * (u * w * u⁻¹) * g₁) * g₁⁻¹ = u * w * u⁻¹ by group]
      exact ⟨w, hw, rfl⟩)
  have hcQ : ∀ q ∈ C'.comap Ψ, c * q = q * c := fun q hq => by
    have h := hfixy q hq
    rw [MulAut.conj_apply] at h
    calc c * q = c * q * c⁻¹ * c := by group
      _ = q * c := by rw [h]
  have hcC : ∀ w ∈ D.orbitGroup, (u⁻¹ * Ψ c * u) * w = w * (u⁻¹ * Ψ c * u) := by
    intro w hw
    obtain ⟨q, hq⟩ := hC'Ψ ⟨w, hw, rfl⟩
    have hq' : Ψ q ∈ C' := by
      rw [hq]
      exact ⟨w, hw, rfl⟩
    have h := congrArg Ψ (hcQ q hq')
    rw [map_mul, map_mul, hq] at h
    change Ψ c * (u * w * u⁻¹) = (u * w * u⁻¹) * Ψ c at h
    calc u⁻¹ * Ψ c * u * w = u⁻¹ * (Ψ c * (u * w * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * w * u⁻¹) * Ψ c) * u := by rw [h]
      _ = w * (u⁻¹ * Ψ c * u) := by group
  obtain ⟨b, hb, hb2, hb01⟩ := eq_of_commute_orbitGroup_three D (three_le_q D) hχ3 hDθ
    (mul_mem (mul_mem (inv_mem huG) (hΨG c)) huG) hcC
  have hu3 : u ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (kernelRoots (signMaskChar .E7 3)) := by
    rw [← h3]
    exact hu
  have hbu := rootDiagUnit_commute_levi_three hb2 hb01 hu3
  have hΨb : Ψ c = rootDiagUnit .E7 b := by
    calc Ψ c = u * (u⁻¹ * Ψ c * u) * u⁻¹ := by group
      _ = u * rootDiagUnit .E7 b * u⁻¹ := by rw [← hb]
      _ = rootDiagUnit .E7 b := by rw [← hbu]; group
  have hc3 : c ^ 3 = 1 := conj_injective hZ (by rw [map_pow, hy3, map_one])
  have hb3 : b ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := .E7)
    rw [← rootDiagUnit_pow, ← hΨb, ← map_pow, hc3, map_one, rootDiagUnit_one]
  have hb1 : b = 1 := by
    funext i
    exact eq_one_of_pow_three_eq_one (by rw [← Pi.pow_apply, hb3, Pi.one_apply])
  have hc1 : c = 1 := hΨinj (by rw [hΨb, hb1, rootDiagUnit_one, map_one])
  rw [hc1, map_one]

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
