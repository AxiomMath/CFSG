module

public import CFSG.FeitThompson.Representations.WeightedEqualityBlocksAttainNormBound
public import CFSG.FeitThompson.Representations.DegreeZeroBridgeJoinsCoherentFamilies
public import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence
public import CFSG.FeitThompson.Representations.CentralLayerCoherenceExtension
public import CFSG.FeitThompson.Representations.WeightedExtensionFailureEqualityDegreeBound
public import CFSG.FeitThompson.Representations.FreeCentralSectionJointCoherence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace WeightedPivotJoining

open CoherentAntirealBlock PositiveWeightedBlockSaturation

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

theorem tau_eq_sum_zsmul (hc : IsSubcoherent S tau R) {ι : Type*} [Fintype ι]
    {d : ι → L → ℂ} {c : ι → ℤ} (hd : ∀ i, d i ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    {g : L → ℂ} (hsum : g = ∑ i, (c i : ℂ) • d i) :
    tau g = ∑ i, (c i : ℂ) • tau (d i) := by
  classical
  set D : ι → intSpanZeroAtOne (S : Set (L → ℂ)) := fun i => ⟨d i, hd i⟩ with hD
  have hcoe : ((∑ i, c i • D i : intSpanZeroAtOne (S : Set (L → ℂ))) : L → ℂ) = g := by
    rw [hsum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, hD, Int.cast_smul_eq_zsmul]
  have hgmem : g ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := by
    rw [← hcoe]; exact (∑ i, c i • D i).2
  have h1 : tau g = hc.tauHom ⟨g, hgmem⟩ := (hc.tauHom_apply ⟨g, hgmem⟩).symm
  rw [h1, show (⟨g, hgmem⟩ : intSpanZeroAtOne (S : Set (L → ℂ))) = ∑ i, c i • D i from
    Subtype.ext hcoe.symm, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hc.tauHom_apply, ← Int.cast_smul_eq_zsmul ℂ (c i)]

theorem exists_isCoherentWith_of_set_eq {U V : Set (L → ℂ)} (hUV : U = V)
    {τU : charSpanZero U →+ virtualChars G} {τV : charSpanZero V →+ virtualChars G}
    {νU : Submodule.span ℤ U →+ virtualChars G} (hν : IsCoherentWith U τU νU)
    (hco : ∀ (f : charSpanZero U) (g : charSpanZero V), (f : L → ℂ) = (g : L → ℂ) →
      (τU f : G → ℂ) = (τV g : G → ℂ)) :
    ∃ νV : Submodule.span ℤ V →+ virtualChars G, IsCoherentWith V τV νV ∧
      ∀ (f : Submodule.span ℤ U) (g : Submodule.span ℤ V), (f : L → ℂ) = (g : L → ℂ) →
        (νU f : G → ℂ) = (νV g : G → ℂ) := by
  subst hUV
  exact ⟨νU, WeightedMinDegreeRigidity.isCoherentWith_congr_baseline
    (fun f => hco f f rfl) hν, fun f g hfg => by rw [show f = g from Subtype.ext hfg]⟩

variable {X Y : Finset (L → ℂ)}
  {τY : charSpanZero (Y : Set (L → ℂ)) →+ virtualChars G}
  {νY : Submodule.span ℤ (Y : Set (L → ℂ)) →+ virtualChars G}
  {e : ℕ} {η : L → ℂ} {a : (L → ℂ) → ℤ} {V : (L → ℂ) → G → ℂ}

theorem exists_isCoherentWith_of_bridges (hc : IsSubcoherent S tau R)
    (hXS : X ⊆ S) (hYS : Y ⊆ S) (hXY : Disjoint X Y)
    (hYIrr : ∀ ψ ∈ Y, ψ ∈ Irr L)
    (hνY : IsCoherentWith (Y : Set (L → ℂ)) τY νY)
    (hη : η ∈ Y) (hYdeg : ∀ ψ ∈ Y, ψ 1 = (e : ℂ))
    (hdeg : ∀ χ ∈ X, χ 1 = (a χ : ℂ) * (e : ℂ))
    (hVmem : ∀ χ ∈ X, V χ ∈ Submodule.span ℤ (Irr G))
    (hVbridge : ∀ χ ∈ X, tau (χ - (a χ : ℂ) • η)
      = V χ - (a χ : ℂ) • (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ))
    (hVorth : ∀ χ ∈ X, cfInner (V χ) (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) = 0) :
    ∃ νX : Submodule.span ℤ (X : Set (L → ℂ)) →+ virtualChars G,
      IsCoherentWith (X : Set (L → ℂ)) (WeightedFeitExtension.subTauHom hc
        (Finset.coe_subset.2 hXS)) νX ∧
      ∀ χ ∈ X, ∀ w : Submodule.span ℤ (X : Set (L → ℂ)), (w : L → ℂ) = χ →
        ((νX w : virtualChars G) : G → ℂ) = V χ := by
  classical
  set hv := (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) with hhv
  have hηS : η ∈ S := hYS hη
  have hηdeg : η 1 = (e : ℂ) := hYdeg η hη
  have hηη : cfInner η η = 1 := cfInner_self_of_mem_Irr (hYIrr η hη)
  have hvv : cfInner hv hv = 1 := by rw [hhv, hνY.inner_eq]; exact hηη
  have hene : (e : ℂ) ≠ 0 := by
    rw [← hηdeg]; exact apply_one_ne_zero_of_mem_Irr (hYIrr η hη)
  set u : ((X : Set (L → ℂ)) : Type _) → L → ℂ := fun i => (i : L → ℂ) with hu
  set g : ((X : Set (L → ℂ)) : Type _) → ℂ := fun i => cfInner (u i) (u i) with hg
  have hXcoe : ∀ i : ((X : Set (L → ℂ)) : Type _), u i ∈ X := fun i => Finset.mem_coe.1 i.2
  have hudeg : ∀ i, u i 1 = (a (u i) : ℂ) * (e : ℂ) := fun i => hdeg _ (hXcoe i)
  have hgramu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0 := by
    intro i j
    by_cases hij : i = j
    · rw [if_pos hij, hij]
    · rw [if_neg hij]
      exact cfInner_eq_zero_of_ne hc (hXS (hXcoe i)) (hXS (hXcoe j))
        fun hcc => hij (Subtype.ext hcc)
  have hgne : ∀ i, g i ≠ 0 := fun i hgi =>
    hc.ne_zero _ (hXS (hXcoe i)) (cfInner_self_eq_zero.1 hgi)
  set v : ((X : Set (L → ℂ)) : Type _) → G → ℂ := fun i => V (u i) with hvdef
  have hvmem : ∀ i, v i ∈ Submodule.span ℤ (Irr G) := fun i => hVmem _ (hXcoe i)
  have hmemsub : ∀ i, u i - (a (u i) : ℂ) • η ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := fun i =>
    sub_smul_mem_intSpanZeroAtOne (hXS (hXcoe i)) hηS hηdeg (hudeg i)
  have hXYne : ∀ i, (u i) ≠ η := fun i hcc =>
    (Finset.disjoint_left.1 hXY (hXcoe i)) (by rw [show u i = η from hcc]; exact hη)
  have hcross : ∀ i, cfInner (u i) η = 0 := fun i =>
    cfInner_eq_zero_of_ne hc (hXS (hXcoe i)) hηS (hXYne i)
  have hcross' : ∀ i, cfInner η (u i) = 0 := fun i => by
    rw [← conj_cfInner, hcross i, map_zero]
  have hvorth : ∀ i, cfInner (v i) hv = 0 := fun i => hVorth _ (hXcoe i)
  have hvorth' : ∀ i, cfInner hv (v i) = 0 := fun i => by
    rw [← conj_cfInner, hvorth i, map_zero]
  have hbr : ∀ i, tau (u i - (a (u i) : ℂ) • η) = v i - (a (u i) : ℂ) • hv := fun i =>
    hVbridge _ (hXcoe i)
  have hgramv : ∀ i j, cfInner (v i) (v j) = if i = j then g i else 0 := by
    intro i j
    have key := cfInner_tau_tau hc (hmemsub i) (hmemsub j)
    rw [hbr i, hbr j,
      cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
      cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, hvorth i, hvorth' j, hvv,
      cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
      cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, hcross i, hcross' j, hηη] at key
    simp only [map_intCast] at key
    rw [show cfInner (v i) (v j) = cfInner (u i) (u j) from by linear_combination key]
    exact hgramu i j
  set τX := virtToSpanIrr.comp
    (WeightedFeitExtension.subTauHom hc (Finset.coe_subset.2 hXS)) with hτX
  have hτXcoe : ∀ w : charSpanZero (X : Set (L → ℂ)), ((τX w : Submodule.span ℤ (Irr G)) : G → ℂ)
      = tau (w : L → ℂ) := fun w => by
    rw [hτX, coe_virtToSpanIrr_comp, WeightedFeitExtension.subTauHom_apply]
  have hτ : ∀ w : charSpanZero (X : Set (L → ℂ)), ∀ c : ((X : Set (L → ℂ)) : Type _) → ℤ,
      ((w : L → ℂ)) = ∑ i, (c i : ℂ) • u i →
      (((τX w : Submodule.span ℤ (Irr G)) : G → ℂ)) = ∑ i, (c i : ℂ) • v i := by
    intro w c hwc
    have hzero : ∑ i, (c i : ℂ) * (a (u i) : ℂ) = 0 := by
      have h1 : (w : L → ℂ) 1 = 0 := charSpanZero_apply_one w
      rw [hwc] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : ∑ i, (c i : ℂ) * ((a (u i) : ℂ) * (e : ℂ)) = 0 := by
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => by rw [hudeg i]
      rw [show ∑ i, (c i : ℂ) * ((a (u i) : ℂ) * (e : ℂ))
          = (∑ i, (c i : ℂ) * (a (u i) : ℂ)) * (e : ℂ) from by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring] at h2
      exact (mul_eq_zero.1 h2).resolve_right hene
    have hwsum : (w : L → ℂ) = ∑ i, (c i : ℂ) • (u i - (a (u i) : ℂ) • η) := by
      rw [hwc, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        smul_sub (c i : ℂ) (u i) ((a (u i) : ℂ) • η), Finset.sum_sub_distrib]
      rw [show ∑ i, (c i : ℂ) • ((a (u i) : ℂ) • η)
          = (∑ i, (c i : ℂ) * (a (u i) : ℂ)) • η from by
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul], hzero, zero_smul, sub_zero]
    rw [hτXcoe, tau_eq_sum_zsmul hc hmemsub hwsum]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [hbr i, smul_sub, smul_smul], Finset.sum_sub_distrib]
    rw [show ∑ i, ((c i : ℂ) * (a (u i) : ℂ)) • hv = (∑ i, (c i : ℂ) * (a (u i) : ℂ)) • hv from
      (Finset.sum_smul ..).symm, hzero, zero_smul, sub_zero]
  obtain ⟨νX, hνXcoh, hνXval⟩ := exists_isCoherentWith_of_gram_eq (L := L) (G := G)
    (u := u) (S := (X : Set (L → ℂ))) Subtype.range_coe.symm hgramu hgne hvmem hgramv hτ
  refine ⟨νX, WeightedMinDegreeRigidity.isCoherentWith_congr_baseline (fun w => ?_) hνXcoh,
    fun χ hχ w hw => ?_⟩
  · rw [AddMonoidHom.comp_apply, coe_spanIrrToVirtualChars, hτXcoe,
      WeightedFeitExtension.subTauHom_apply]
  · exact hνXval ⟨χ, Finset.mem_coe.2 hχ⟩ w hw

theorem isCoherent_union_of_bridges (hc : IsSubcoherent S tau R)
    (hXS : X ⊆ S) (hYS : Y ⊆ S) (hXY : Disjoint X Y)
    {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ X) (hYne : Y.Nonempty)
    (hXstar : ∀ ψ ∈ X, star ψ ∈ X) (hYstar : ∀ ψ ∈ Y, star ψ ∈ Y)
    (hYIrr : ∀ ψ ∈ Y, ψ ∈ Irr L)
    (hνY : IsCoherentWith (Y : Set (L → ℂ)) τY νY)
    (hτY : ∀ f : charSpanZero (Y : Set (L → ℂ)), (τY f : G → ℂ) = tau (f : L → ℂ))
    (hη : η ∈ Y) (hYdeg : ∀ ψ ∈ Y, ψ 1 = (e : ℂ))
    (hdeg : ∀ χ ∈ X, χ 1 = (a χ : ℂ) * (e : ℂ))
    (hVmem : ∀ χ ∈ X, V χ ∈ Submodule.span ℤ (Irr G))
    (hVbridge : ∀ χ ∈ X, tau (χ - (a χ : ℂ) • η)
      = V χ - (a χ : ℂ) • (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ))
    (hVorth : ∀ χ ∈ X, cfInner (V χ) (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) = 0)
    {τU : charSpanZero ((X : Set (L → ℂ)) ∪ (Y : Set (L → ℂ))) →+ virtualChars G}
    (hτU : ∀ f : charSpanZero ((X : Set (L → ℂ)) ∪ (Y : Set (L → ℂ))),
      (τU f : G → ℂ) = tau (f : L → ℂ)) :
    IsCoherent ((X : Set (L → ℂ)) ∪ (Y : Set (L → ℂ))) τU := by
  classical
  obtain ⟨νX, hνX, hνXval⟩ := exists_isCoherentWith_of_bridges hc hXS hYS hXY hYIrr hνY hη
    hYdeg hdeg hVmem hVbridge hVorth
  have hUS : (X ∪ Y : Finset (L → ℂ)) ⊆ S := Finset.union_subset hXS hYS
  set τ₀ := WeightedFeitExtension.subTauHom hc (Finset.coe_subset.2 hUS) with hτ₀def
  set φ : Submodule.span ℤ (Y : Set (L → ℂ)) :=
    a χ₀ • (⟨η, mem_span_of_mem hη⟩ : Submodule.span ℤ (Y : Set (L → ℂ))) with hφ
  have hφcoe : (φ : L → ℂ) = (a χ₀ : ℂ) • η := by
    rw [hφ, SetLike.val_smul, Int.cast_smul_eq_zsmul]
  have hφ1 : χ₀ 1 = (φ : L → ℂ) 1 := by
    rw [hφcoe, Pi.smul_apply, smul_eq_mul, hYdeg η hη, hdeg χ₀ hχ₀]
  have hνYφ : (νY φ : G → ℂ) = (a χ₀ : ℂ) • (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) := by
    rw [hφ, map_zsmul, SetLike.val_smul, Int.cast_smul_eq_zsmul]
  have hbridge : tau (χ₀ - (φ : L → ℂ))
      = (νX ⟨χ₀, mem_span_of_mem hχ₀⟩ : G → ℂ) - (νY φ : G → ℂ) := by
    rw [hφcoe, hνYφ, hVbridge χ₀ hχ₀, hνXval χ₀ hχ₀ _ rfl]
  have hjoin := CoherentJoin.isCoherentWith_joinHom hc hXS hXstar ⟨χ₀, hχ₀⟩ hνX
    (fun f => WeightedFeitExtension.subTauHom_apply hc _ f) hYS hYstar hYne hνY hτY hXY
    (τU := τ₀) (fun f => WeightedFeitExtension.subTauHom_apply hc _ f) hχ₀ φ hφ1 hbridge
  exact FreeCentralSectionJointCoherence.isCoherent_of_eq_of_coe_eq (tau := tau)
    (Finset.coe_union X Y) (fun f => WeightedFeitExtension.subTauHom_apply hc _ f) hτU
    hjoin.isCoherent

theorem cfInner_tau_sub_smul_pivot (hc : IsSubcoherent S tau R)
    {X Y : Set (L → ℂ)} (hXfin : X.Finite) (hYfin : Y.Finite)
    (hXS : X ⊆ (S : Set (L → ℂ))) (hYS : Y ⊆ (S : Set (L → ℂ))) (hXY : Disjoint X Y)
    (hXstar : ∀ ψ ∈ X, star ψ ∈ X) (hYstar : ∀ ψ ∈ Y, star ψ ∈ Y) (hYIrr : Y ⊆ Irr L)
    {τY : charSpanZero Y →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνY : IsCoherentWith Y τY νY)
    (hτY : ∀ f : charSpanZero Y, (τY f : G → ℂ) = tau (f : L → ℂ))
    (hη : η ∈ Y) (hYdeg : ∀ ψ ∈ Y, ψ 1 = (e : ℂ))
    {ι : Type*} [Fintype ι] {χ : ι → L → ℂ} {b : ι → ℤ}
    (hχX : ∀ i, χ i ∈ X) (hdeg : ∀ i, χ i 1 = (b i : ℂ) * (e : ℂ)) (hbpos : ∀ i, 1 ≤ b i)
    {w : L → ℂ} {r : ℤ} (hwdef : w = ∑ i, (b i : ℂ) • χ i) (hrdef : r = ∑ i, b i ^ 2)
    (hweq : cfInner (tau (w - (r : ℂ) • η))
      (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ) = -(r : ℂ))
    (i : ι) :
    ∃ Vi ∈ Submodule.span ℤ (Irr G), tau (χ i - (b i : ℂ) • η)
        = Vi - (b i : ℂ) • (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ) ∧
      cfInner Vi (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ) = 0 := by
  classical
  obtain ⟨Xf, hXc⟩ : ∃ Xf : Finset (L → ℂ), (Xf : Set (L → ℂ)) = X :=
    ⟨hXfin.toFinset, hXfin.coe_toFinset⟩
  obtain ⟨Yf, hYc⟩ : ∃ Yf : Finset (L → ℂ), (Yf : Set (L → ℂ)) = Y :=
    ⟨hYfin.toFinset, hYfin.coe_toFinset⟩
  subst hXc hYc
  obtain ⟨E, hER, -, hEsum, hEorth⟩ := exists_subset_card_eq_and_tau_eq hc
    (Finset.coe_subset.1 hXS) (Finset.coe_subset.1 hYS) (Finset.disjoint_coe.1 hXY)
    (fun ψ hψ => hXstar ψ (Finset.mem_coe.2 hψ)) (fun ψ hψ => hYstar ψ (Finset.mem_coe.2 hψ))
    hνY hτY (fun ψ hψ => hYIrr (Finset.mem_coe.2 hψ)) (Finset.mem_coe.1 hη)
    (fun ψ hψ => hYdeg ψ (Finset.mem_coe.2 hψ)) hχX hdeg hbpos hwdef hrdef hweq i
  refine ⟨∑ v ∈ E, v, ?_, hEsum, isOrthogonal_iff.1 (hEorth η (Finset.mem_coe.1 hη))⟩
  refine Submodule.sum_mem _ fun v hv => ?_
  exact mem_span_Irr_of_mem_virtualCharSpan
    (hc.R_subset _ (Finset.coe_subset.1 hXS (hχX i)) v (hER hv))

theorem isCoherent_union_of_bridges' (hc : IsSubcoherent S tau R)
    {X Y : Set (L → ℂ)} (hXfin : X.Finite) (hYfin : Y.Finite)
    (hXS : X ⊆ (S : Set (L → ℂ))) (hYS : Y ⊆ (S : Set (L → ℂ))) (hXY : Disjoint X Y)
    {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ X) (hYne : Y.Nonempty)
    (hXstar : ∀ ψ ∈ X, star ψ ∈ X) (hYstar : ∀ ψ ∈ Y, star ψ ∈ Y) (hYIrr : Y ⊆ Irr L)
    {τY : charSpanZero Y →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνY : IsCoherentWith Y τY νY)
    (hτY : ∀ f : charSpanZero Y, (τY f : G → ℂ) = tau (f : L → ℂ))
    (hη : η ∈ Y) (hYdeg : ∀ ψ ∈ Y, ψ 1 = (e : ℂ))
    (hdeg : ∀ χ ∈ X, χ 1 = (a χ : ℂ) * (e : ℂ))
    (hVmem : ∀ χ ∈ X, V χ ∈ Submodule.span ℤ (Irr G))
    (hVbridge : ∀ χ ∈ X, tau (χ - (a χ : ℂ) • η)
      = V χ - (a χ : ℂ) • (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ))
    (hVorth : ∀ χ ∈ X, cfInner (V χ) (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ) = 0)
    {τU : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτU : ∀ f : charSpanZero (X ∪ Y), (τU f : G → ℂ) = tau (f : L → ℂ)) :
    IsCoherent (X ∪ Y) τU := by
  classical
  obtain ⟨Xf, hXc⟩ : ∃ Xf : Finset (L → ℂ), (Xf : Set (L → ℂ)) = X :=
    ⟨hXfin.toFinset, hXfin.coe_toFinset⟩
  obtain ⟨Yf, hYc⟩ : ∃ Yf : Finset (L → ℂ), (Yf : Set (L → ℂ)) = Y :=
    ⟨hYfin.toFinset, hYfin.coe_toFinset⟩
  subst hXc hYc
  exact isCoherent_union_of_bridges hc (Finset.coe_subset.1 hXS) (Finset.coe_subset.1 hYS)
    (Finset.disjoint_coe.1 hXY) (Finset.mem_coe.1 hχ₀) (Finset.coe_nonempty.1 hYne)
    hXstar hYstar hYIrr hνY hτY (Finset.mem_coe.1 hη) hYdeg hdeg hVmem hVbridge hVorth hτU

theorem isCoherent_union_of_exists_bridge (hc : IsSubcoherent S tau R)
    {X Y : Set (L → ℂ)} (hXfin : X.Finite) (hYfin : Y.Finite)
    (hXS : X ⊆ (S : Set (L → ℂ))) (hYS : Y ⊆ (S : Set (L → ℂ))) (hXY : Disjoint X Y)
    {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ X) (hYne : Y.Nonempty)
    (hXstar : ∀ ψ ∈ X, star ψ ∈ X) (hYstar : ∀ ψ ∈ Y, star ψ ∈ Y) (hYIrr : Y ⊆ Irr L)
    {τY : charSpanZero Y →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνY : IsCoherentWith Y τY νY)
    (hτY : ∀ f : charSpanZero Y, (τY f : G → ℂ) = tau (f : L → ℂ))
    (hη : η ∈ Y) (hYdeg : ∀ ψ ∈ Y, ψ 1 = (e : ℂ))
    {b : (L → ℂ) → ℤ} (hdeg : ∀ χ ∈ X, χ 1 = (b χ : ℂ) * (e : ℂ))
    (hVex : ∀ χ ∈ X, ∃ Vχ ∈ Submodule.span ℤ (Irr G), tau (χ - (b χ : ℂ) • η)
        = Vχ - (b χ : ℂ) • (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ) ∧
      cfInner Vχ (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ) = 0)
    {τU : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτU : ∀ f : charSpanZero (X ∪ Y), (τU f : G → ℂ) = tau (f : L → ℂ)) :
    IsCoherent (X ∪ Y) τU := by
  classical
  choose! W hWmem hWbridge hWorth using hVex
  exact isCoherent_union_of_bridges' hc hXfin hYfin hXS hYS hXY hχ₀ hYne hXstar hYstar hYIrr
    hνY hτY hη hYdeg hdeg hWmem hWbridge hWorth hτU

end WeightedPivotJoining

end CFSG.FeitThompson
