module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerComp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc (catEquiv_adjointGroup_of_card
  not_isD2SeitzException_of_chevalleyExc isChevalleyExcIndex_E6)

section Assembly

set_option linter.unusedSectionVars false


theorem toralCentralizer_le_seitzHyperGamma_inner (hLayer : E6ThreeLayerGen)
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK : 3 ∣ Nat.card K - 1) (hK4 : Nat.card K ≠ 4) {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEi : E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K))
    (hER : ¬ E6NormalizesR K E) (hh : MulAut.conj (e6LineElt ω) ∈ E) :
    toralCentralizer .E6 K (e6LineChar ω) ≤
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := by
  have hComp := e6ThreeCompGenInner_holds
  have hED : E ≤ e6Inndiag K := hEi.trans (innerAut_le_e6Inndiag K)
  have hU : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := by
    rw [rootSpan_iUnion_e6LineRoots]
    have hf : ∀ i, e6LineFactor K i ≤
        (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := fun i x hx =>
      ⟨⟨x, rootSpan_le_adjointGroup K _ hx⟩,
        hLayer K hK3 hK hK4 ω h3 h1 E hE hEc hED hh i (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    exact sup_le (sup_le (hf 0) (hf 1)) (hf 2)
  have hT : torusGroup .E6 K ≤ (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype :=
    (torusGroup_le_seitzHyperGamma_sup hK h3 h1 hE hEc hED hh).trans (sup_le le_rfl hU)
  have hM : toralRootGroup .E6 K (e6LineChar ω) ≤
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := by
    show torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω)) ≤ _
    rw [e6Line_kernel h3 h1]
    exact sup_le hT hU
  have hn : canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype :=
    sup_le le_rfl hM (hComp K hK3 hK hK4 ω h3 h1 E hE hEc hEi hER hh)
  rw [e6Line_centralizer h3 h1]
  exact sup_le hM ((Subgroup.zpowers_le).2 hn)

theorem e6InnerOneConjGen_of_core (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hS3 : E6ThreeA2ConjStmt) (hLayer : E6ThreeLayerGen)
    (hPlane : E6InnerAll24Plane) : E6InnerOneConjGen := by
  intro K _ _ hK3 hK hK4 E hE hEc hEi hER
  classical
  obtain ⟨ω, h3, h1⟩ := e6Line_exists_cube_root_unit hK
  obtain ⟨P, hPE, hPc, hP24⟩ := hPlane K hK3 hK hK4 E hE hEc hEi hER
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  let q : TauCeti.PrimePower := ⟨ringChar K, n, hℓ, n.pos⟩
  have hqK : Nat.card K = q.card := by
    rw [Nat.card_eq_fintype_card, hn, TauCeti.PrimePower.card_def]
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := TauCeti.LieTypeIndex.valid_E6 q
  obtain ⟨e⟩ := catEquiv_adjointGroup_of_card CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    K hqK
  have hgen := planeGen_of_kfact hS Nat.prime_three (by norm_num) ⟨_, hv⟩ e.symm
    (by
      show 3 ≠ (TauCeti.LieTypeIndex.E6 q).characteristic
      rw [TauCeti.LieTypeIndex.characteristic_E6]
      exact fun h => hK3 h.symm)
    (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E6 q)) (hE.mono hPE) hPc
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro s ⟨f, hfP, hf1, hfs⟩
  have hfE : f ∈ E := hPE hfP
  obtain ⟨v, rfl⟩ := CFSG.Fischer.mem_innerAut.1 (hEi hfE)
  have hv1 : v ≠ 1 := fun h => hf1 (by rw [h, map_one])
  have hv3 : v ^ 3 = 1 := by
    have hc : v ^ 3 ∈ Subgroup.center (adjointGroup Tag.E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) => φ x)
        (show MulAut.conj (v ^ 3) = 1 by rw [map_pow]; exact hE.2 _ hfE)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    rw [center_adjointGroup_eq_bot] at hc
    exact Subgroup.mem_bot.1 hc
  have hdim := hP24 v hfP hv1
  obtain ⟨g, hgC, hg⟩ := hS3 K ω h3 h1 (v : ModGL .E6 K) v.2
    (by have := congrArg Subtype.val hv3; simpa using this) hdim
  obtain ⟨g', hg'⟩ : ∃ g' : adjointGroup Tag.E6 K, (g' : ModGL .E6 K) = g := ⟨⟨g, hgC⟩, rfl⟩
  have hgv : g' * v * g'⁻¹ = e6LineElt ω := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg', coe_e6LineElt]
    exact hg
  obtain ⟨c, hc⟩ : ∃ c : MulAut (adjointGroup Tag.E6 K), c = MulAut.conj g' := ⟨_, rfl⟩
  have hcI : c ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
    rw [hc]
    exact ⟨g', rfl⟩
  have hE'a : IsElemAbelian 3 (E.map (MulAut.congr c).toMonoidHom) := hE.map _
  have hE'c : Nat.card (E.map (MulAut.congr c).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr c).injective, hEc]
  have hE'i : E.map (MulAut.congr c).toMonoidHom ≤
      CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
    rintro _ ⟨ε, hε, rfl⟩
    rw [congr_toMonoidHom_apply]
    exact mul_mem (mul_mem hcI (hEi hε)) (inv_mem hcI)
  have hE'R : ¬ E6NormalizesR K (E.map (MulAut.congr c).toMonoidHom) :=
    fun h => hER (e6NormalizesR_of_map_congr c h)
  have hh : MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr c).toMonoidHom := by
    refine ⟨MulAut.conj v, hfE, ?_⟩
    rw [congr_toMonoidHom_apply, hc, ← hgv, map_mul, map_mul, map_inv]
  have hC := toralCentralizer_le_seitzHyperGamma_inner hLayer hK3 hK hK4 h3 h1 hE'a hE'c
    hE'i hE'R hh
  have hcs : ((c s : adjointGroup Tag.E6 K) : ModGL .E6 K) ∈
      toralCentralizer .E6 K (e6LineChar ω) := by
    refine mem_toralCentralizer.2 ⟨(c s).2, ?_⟩
    have hvs : v * s * v⁻¹ = s := by simpa only [MulAut.conj_apply] using hfs
    have key : e6LineElt ω * c s * (e6LineElt ω)⁻¹ = c s := by
      rw [← hgv, hc, MulAut.conj_apply]
      calc g' * v * g'⁻¹ * (g' * s * g'⁻¹) * (g' * v * g'⁻¹)⁻¹ = g' * (v * s * v⁻¹) * g'⁻¹ := by
            group
        _ = g' * s * g'⁻¹ := by rw [hvs]
    have := congrArg Subtype.val key
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_e6LineElt] using this
  obtain ⟨y, hy, hyc⟩ := hC hcs
  have hyc' : y = c s := Subtype.ext hyc
  rw [hyc'] at hy
  exact mem_seitzHyperGamma_of_congr hy

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
