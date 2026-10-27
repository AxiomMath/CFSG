module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCoreDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneUntw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc (catEquiv_adjointGroup_of_card
  not_isD2SeitzException_of_chevalleyExc isChevalleyExcIndex_E6)

section Transport

variable {X : Type*} [Group X]

theorem seitzHyperGamma_congr_le_map {p : ℕ} (c : MulAut X) (E : Subgroup (MulAut X)) :
    seitzHyperGamma p (E.map (MulAut.congr c).toMonoidHom) ≤
      (seitzHyperGamma p E).map c.toMonoidHom := by
  have hinj : Function.Injective (MulAut.congr c).toMonoidHom := (MulAut.congr c).injective
  refine iSup₂_le fun F' hF' => ?_
  obtain ⟨hF'E, hF'p⟩ := hF'
  set F := F'.comap (MulAut.congr c).toMonoidHom with hF
  have hFE : F ≤ E := by
    intro a ha
    obtain ⟨a', ha', hfa⟩ := hF'E ha
    rw [← hinj hfa]
    exact ha'
  have hmap : F.map (MulAut.congr c).toMonoidHom = F' := by
    rw [hF, Subgroup.map_comap_eq, inf_of_le_right (hF'E.trans (Subgroup.map_le_range _ E))]
  have hFp : F.relIndex E = p := by
    rw [← Subgroup.relIndex_map_map_of_injective F E hinj, hmap]
    exact hF'p
  intro y hy
  refine ⟨c⁻¹ y, ?_, by simp⟩
  refine (le_iSup₂_of_le F ⟨hFE, hFp⟩ le_rfl : fixedPoints F ≤ seitzHyperGamma p E) ?_
  rw [mem_fixedPoints]
  intro a ha
  have h1 := (mem_fixedPoints.1 hy) ((MulAut.congr c).toMonoidHom a)
    (hmap ▸ Subgroup.mem_map_of_mem _ ha)
  have h2 : c (a (c⁻¹ y)) = y := by simpa [MulAut.congr_apply] using h1
  have h3 := congrArg (c⁻¹ : MulAut X) h2
  rwa [MulAut.inv_apply_self] at h3

theorem mem_seitzHyperGamma_of_congr {p : ℕ} {c : MulAut X} {E : Subgroup (MulAut X)} {y : X}
    (hy : c y ∈ seitzHyperGamma p (E.map (MulAut.congr c).toMonoidHom)) :
    y ∈ seitzHyperGamma p E := by
  obtain ⟨z, hz, hzy⟩ := seitzHyperGamma_congr_le_map c E hy
  have hzy' : z = y := c.injective (by simpa using hzy)
  rwa [← hzy']

theorem congr_toMonoidHom_apply (c ε : MulAut X) :
    (MulAut.congr c).toMonoidHom ε = c * ε * c⁻¹ :=
  MulEquiv.ext fun _ => rfl

end Transport

theorem e6InnerAll24_map_conj
    {K : Type} [Field K] (g : adjointGroup Tag.E6 K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (h : E6InnerAll24 K E) :
    E6InnerAll24 K (E.map (MulAut.congr (MulAut.conj g)).toMonoidHom) := by
  rintro s ⟨ε, hε, hεs⟩ hs1
  rw [congr_toMonoidHom_apply] at hεs
  have hε' : ε = MulAut.conj (g⁻¹ * s * g) := by
    rw [map_mul, map_mul, map_inv, ← hεs]
    group
  have h1 : g⁻¹ * s * g ≠ 1 := by
    intro h1
    apply hs1
    calc s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have h24 := h (g⁻¹ * s * g) (hε' ▸ hε) h1
  have hs' : (g : ModGL .E6 K) * ((g⁻¹ * s * g : adjointGroup Tag.E6 K) : ModGL .E6 K) *
      (g : ModGL .E6 K)⁻¹ = s := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have key := finrank_ker_conj_sub_one (g : ModGL .E6 K)
    ((g⁻¹ * s * g : adjointGroup Tag.E6 K) : ModGL .E6 K)
  rw [hs'] at key
  exact key.trans h24

theorem e6NormalizesR_of_map_congr
    {K : Type} [Field K] [Finite K] (c : MulAut (adjointGroup Tag.E6 K))
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (h : E6NormalizesR K (E.map (MulAut.congr c).toMonoidHom)) : E6NormalizesR K E := by
  obtain ⟨R, hR1, hRp, hRE⟩ := h
  refine ⟨R.map c⁻¹.toMonoidHom, ?_, hRp.map _, fun ε hε => ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective R (MulEquiv.injective _)]
    exact hR1
  · have h1 := hRE _ (Subgroup.mem_map_of_mem (MulAut.congr c).toMonoidHom hε)
    calc (R.map c⁻¹.toMonoidHom).map ε.toMonoidHom
        = (R.map ((MulAut.congr c).toMonoidHom ε).toMonoidHom).map c⁻¹.toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map]
          congr 1
          ext x
          simp [MulAut.congr_apply]
      _ = R.map c⁻¹.toMonoidHom := by rw [h1]

section Assembly

set_option linter.unusedSectionVars false


theorem toralCentralizer_le_seitzHyperGamma (hLayer : E6ThreeLayerGen) (hTorus : E6ThreeTorusGen)
    (hComp : E6ThreeCompGen) {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK : 3 ∣ Nat.card K - 1) (hK4 : Nat.card K ≠ 4) {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hED : E ≤ e6Inndiag K)
    (hEi : ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) (hER : ¬ E6NormalizesR K E)
    (hA : E6InnerAll24 K E) (hh : MulAut.conj (e6LineElt ω) ∈ E) :
    toralCentralizer .E6 K (e6LineChar ω) ≤
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := by
  have hU : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := by
    rw [rootSpan_iUnion_e6LineRoots]
    have hf : ∀ i, e6LineFactor K i ≤
        (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := fun i x hx =>
      ⟨⟨x, rootSpan_le_adjointGroup K _ hx⟩,
        hLayer K hK3 hK hK4 ω h3 h1 E hE hEc hED hh i (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    exact sup_le (sup_le (hf 0) (hf 1)) (hf 2)
  have hT : torusGroup .E6 K ≤ (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype :=
    (hTorus K hK3 hK hK4 ω h3 h1 E hE hEc hED hEi hER hh).trans (sup_le le_rfl hU)
  have hM : toralRootGroup .E6 K (e6LineChar ω) ≤
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype := by
    show torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω)) ≤ _
    rw [e6Line_kernel h3 h1]
    exact sup_le hT hU
  have hn : canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype :=
    sup_le le_rfl hM (hComp K hK3 hK hK4 ω h3 h1 E hE hEc hED hEi hER hA hh)
  rw [e6Line_centralizer h3 h1]
  exact sup_le hM ((Subgroup.zpowers_le).2 hn)

theorem e6DiagNonParCubes_of_core (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hS3 : E6ThreeA2ConjStmt) (hLayer : E6ThreeLayerGen) (hTorus : E6ThreeTorusGen)
    (hComp : E6ThreeCompGen) (hNotAll24 : E6ThreeNotAll24Gen) :
    E6ThreeDefs.E6DiagNonParCubes := by
  intro K _ _ hK3 hK hK4 E hE hEc hED hEi hER
  classical
  by_cases hA : E6InnerAll24 K E
  swap
  · exact hNotAll24 K hK3 hK hK4 E hE hEc hED hEi hER hA
  obtain ⟨ω, h3, h1⟩ := e6Line_exists_cube_root_unit hK
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  let q : TauCeti.PrimePower := ⟨ringChar K, n, hℓ, n.pos⟩
  have hqK : Nat.card K = q.card := by
    rw [Nat.card_eq_fintype_card, hn, TauCeti.PrimePower.card_def]
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := TauCeti.LieTypeIndex.valid_E6 q
  obtain ⟨e⟩ := catEquiv_adjointGroup_of_card CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    K hqK
  have hPc : Nat.card ↥(E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) = 3 ^ 2 :=
    card_inf_innerAut_of_le_e6Inndiag K hEc hED hEi
  have hgen := planeGen_of_kfact hS Nat.prime_three (by norm_num) ⟨_, hv⟩ e.symm
    (by
      show 3 ≠ (TauCeti.LieTypeIndex.E6 q).characteristic
      rw [TauCeti.LieTypeIndex.characteristic_E6]
      exact fun h => hK3 h.symm)
    (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E6 q))
    (hE.mono (inf_le_left : E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) ≤ E)) hPc
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro s ⟨f, hfP, hf1, hfs⟩
  obtain ⟨hfE, hfI⟩ := Subgroup.mem_inf.1 hfP
  obtain ⟨v, rfl⟩ := CFSG.Fischer.mem_innerAut.1 hfI
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
  have hdim := hA v hfE hv1
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
  have hE'D : E.map (MulAut.congr c).toMonoidHom ≤ e6Inndiag K := by
    rintro _ ⟨ε, hε, rfl⟩
    have hcD := innerAut_le_e6Inndiag K hcI
    rw [congr_toMonoidHom_apply]
    exact mul_mem (mul_mem hcD (hED hε)) (inv_mem hcD)
  have hE'i : ¬ E.map (MulAut.congr c).toMonoidHom ≤
      CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
    intro h
    apply hEi
    intro ε hε
    have h1 := h ⟨ε, hε, rfl⟩
    rw [congr_toMonoidHom_apply] at h1
    have he : ε = c⁻¹ * (c * ε * c⁻¹) * c := by group
    rw [he]
    exact mul_mem (mul_mem (inv_mem hcI) h1) hcI
  have hE'R : ¬ E6NormalizesR K (E.map (MulAut.congr c).toMonoidHom) :=
    fun h => hER (e6NormalizesR_of_map_congr c h)
  have hE'A : E6InnerAll24 K (E.map (MulAut.congr c).toMonoidHom) := by
    rw [hc]
    exact e6InnerAll24_map_conj g' hA
  have hh : MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr c).toMonoidHom := by
    refine ⟨MulAut.conj v, hfE, ?_⟩
    rw [congr_toMonoidHom_apply, hc, ← hgv, map_mul, map_mul, map_inv]
  have hC := toralCentralizer_le_seitzHyperGamma hLayer hTorus hComp hK3 hK hK4 h3 h1 hE'a hE'c
    hE'D hE'i hE'R hE'A hh
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

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
