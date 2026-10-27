module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Frame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Transfer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CoreRows

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.ClassicalInvolution.ModelFacts
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups


theorem burgTorusFor_twisted_three {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    [CharP K p] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p] {g : adjointGroup .E7 K}
    {a : Fin Tag.E7.rank → Kˣ} (hα : orderOf (MulAut.conj g * rootDiagAut .E7 K a) = 2)
    (hxR : liftElt (algebraMap K L) (g : ModGL .E7 K) a ∈
      fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1))
    {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps) (h3 : r.mask = 3) {g₁ : ModGL .E7 L}
    (hg₁G : g₁ ∈ adjointGroup .E7 L)
    (hconj : g₁ * liftElt (algebraMap K L) (g : ModGL .E7 K) a * g₁⁻¹ =
      rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)))
    (hcoc : g₁ * (frobTwistGL .E7 L p f 1 g₁)⁻¹ = wordWeylMatrix .E7 L e7Word2_1) :
    BurgTorusFor (MulAut.conj g * rootDiagAut .E7 K a) := by
  classical
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hp : p.Prime := Fact.out
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L p]; exact hp2
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
  have hιR : ∀ c, g₁⁻¹ * Ψ c * g₁ ∈ R := fun c => by rw [hΨc]; exact hRR (hιH c)
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
  have hYΨ : (twCent p L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a)).map
      (MulAut.conj g₁).toMonoidHom ≤ Ψ.range := by
    rintro _ ⟨y, hy, rfl⟩
    refine hmemΨ _ ?_
    change g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ ∈ _
    rw [show g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ = y by group]
    exact (Subgroup.mem_inf.1 hy).1
  have hC'Ψ := hCY.trans hYΨ
  have htw : ∀ c, (MulAut.conj g * rootDiagAut .E7 K a) c = c ↔
      Ψ c ∈ (twCent p L f (liftElt (algebraMap K L) (g : ModGL .E7 K) a)).map
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
  obtain ⟨S', e, he1, hS'H, hS'c, hS'd, hS'χ⟩ :=
    exists_twisted_sl2_frame (K := K) hp2 hK (by omega) hg₁G hcoc
  have hS'Ψ : S' ≤ Ψ.range := fun w hw => hmemΨ w (hS'H w hw)
  have hqK : IsQuasisimple (SL(2, K)) := by
    have : Fintype K := Fintype.ofFinite K
    have h4 : ∃ s : Finset K, s.card = 4 := by
      have h : 4 ≤ (Finset.univ : Finset K).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        omega
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h
      exact ⟨t, ht⟩
    exact RankThree.Classical.isQuasisimple_SL2 h4
  have hxd : g₁⁻¹ * rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) * g₁ ∈
      R := by
    rw [← hconj, show g₁⁻¹ * (g₁ * liftElt (algebraMap K L) (g : ModGL .E7 K) a * g₁⁻¹) * g₁ =
      liftElt (algebraMap K L) (g : ModGL .E7 K) a by group]
    exact hxR
  have hMG : torusGroup .E7 L ⊔ rootSpan .E7 L (kernelRoots (signMaskChar .E7 r.mask)) ≤
      adjointGroup .E7 L := sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _)
  have huG : u ∈ adjointGroup .E7 L := hMG hu
  refine burgTorusFor_of_frame (center_adjointGroup_eq_bot_field .E7 K) hα hΨinj hC'Ψ hS'Ψ
    (LocalCores.isQuasisimple_of_mulEquiv (D.orbitGroup.equivMapOfInjective _
      (MulAut.conj u).injective) hqs) hK2 hqK e (fun c hc => (htw c).2 (hCY hc)) ?_ ?_
    (x' := rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask))) ?_
    (hS'd _ hxd) ?_ ?_ ?_
  ·
    intro c hc w hw
    have h := Subgroup.mem_map_of_mem (MulAut.conj (Ψ c)).toMonoidHom hw
    rw [hYC (Ψ c) ((htw c).1 hc)] at h
    exact h
  ·
    intro c hc
    exact hS'c (Ψ c) (hΨG c) (hιR c) (by rw [← he1]; exact hc)
  ·
    intro s
    rw [← hconj]
    have h := liftElt_conj (algebraMap K L) g a s
    change g₁ * baseChangeGL (algebraMap K L) (((MulAut.conj g * rootDiagAut .E7 K a) s :
      adjointGroup .E7 K) : ModGL .E7 K) * g₁⁻¹ = _ * (g₁ * baseChangeGL (algebraMap K L)
        (s : ModGL .E7 K) * g₁⁻¹) * _
    rw [← h]
    group
  ·
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have h := hS'χ _ fun w hw => by
      calc rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) * w =
          rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) * w *
            (rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)))⁻¹ *
              rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) := by group
        _ = w * rootDiagUnit .E7 (signCharTuple (k := L) (signMaskChar .E7 r.mask)) := by
          rw [hcon w hw]
    rw [h3, rootChar_three_e7Beta0] at h
    have h' := congrArg (fun z : Lˣ => (z : L)) h
    simp only [Units.val_neg, Units.val_one] at h'
    exact Ring.neg_one_ne_one_of_char_ne_two hL2 h'
  ·
    intro β hβ hfix
    refine mem_inner_of_odd_fix_orbitGroup (u := u) (g₁ := g₁) hK D hDe hDθ
      (four_mem_simpleRootsJ D (Or.inr rfl) hχ3) (fun w hw => ?_) hβ fun t ⟨w, hw, ht⟩ => hfix t ?_
    · obtain ⟨c, hc⟩ := hC'Ψ ⟨w, hw, rfl⟩
      refine ⟨(c : ModGL .E7 K), c.2, ?_⟩
      change embE7 L c = _
      rw [← hΨc, hc]
      rfl
    · change g₁ * baseChangeGL (algebraMap K L) (t : ModGL .E7 K) * g₁⁻¹ ∈ _
      rw [ht, show g₁ * (g₁⁻¹ * (u * w * u⁻¹) * g₁) * g₁⁻¹ = u * w * u⁻¹ by group]
      exact ⟨w, hw, rfl⟩
  ·
    intro c hc hcQ
    have hcC : ∀ w ∈ D.orbitGroup, (u⁻¹ * Ψ c * u) * w = w * (u⁻¹ * Ψ c * u) := by
      intro w hw
      obtain ⟨q, hq⟩ := hC'Ψ ⟨w, hw, rfl⟩
      have hq' : Ψ q ∈ D.orbitGroup.map (MulAut.conj u).toMonoidHom := by
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
    have hbR : g₁⁻¹ * rootDiagUnit .E7 b * g₁ ∈ R := by rw [← hΨb]; exact hιR c
    refine ⟨fun w hw => by rw [hΨb]; exact hS'd b hbR w hw, fun hcS => ?_⟩
    have h1 := hS'χ b fun w hw => by rw [← hΨb]; exact hcS w hw
    rw [rootChar_e7Beta0 hb2] at h1
    have h0 : b (e7Node 0) = 1 := by rwa [h1, mul_one] at hb01
    have hb1 : b = 1 := by
      funext i
      obtain ⟨j, rfl⟩ : ∃ j : Fin 7, e7Node j = i := ⟨i, rfl⟩
      rcases (show j.val = 0 ∨ j.val = 1 ∨ 2 ≤ j.val by omega) with h | h | h
      · rw [show j = 0 from Fin.ext h]
        exact h0
      · rw [show j = 1 from Fin.ext h]
        exact h1
      · exact hb2 j h
    apply hΨinj
    rw [hΨb, hb1, rootDiagUnit_one, map_one]

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
