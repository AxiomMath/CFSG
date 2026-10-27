module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnCard
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2ConjStmt
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
  (not_isD2SeitzException_of_chevalleyExc isChevalleyExcIndex_twistedE6)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (catEquiv_twistedE6_of_field)

section Transport


theorem twE6FixDim_conj (K : Type) [Field K] (σ : K ≃+* K) (g u : twistedE6RootGroup K σ) :
    twE6FixDim K σ (g * u * g⁻¹) = twE6FixDim K σ u :=
  finrank_ker_conj_sub_one (g : ModGL TwistTag.E6.tag K) (u : ModGL TwistTag.E6.tag K)

theorem twE6InnerAll24_map_conj {K : Type} [Field K] {σ : K ≃+* K} (g : twistedE6RootGroup K σ)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (h : TwE6InnerAll24 K σ E) :
    TwE6InnerAll24 K σ (E.map (MulAut.congr (MulAut.conj g)).toMonoidHom) := by
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
  have h25 := twE6FixDim_conj K σ g (g⁻¹ * s * g)
  rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h25
  rw [h25]
  exact h24

theorem twE6NormalizesR_of_map_congr {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (c : MulAut (twistedE6RootGroup K σ)) {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (h : TwE6NormalizesR K σ (E.map (MulAut.congr c).toMonoidHom)) : TwE6NormalizesR K σ E := by
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

end Transport

section Assembly

set_option linter.unusedSectionVars false


theorem twE6DiagNonParCubes_of_core (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hS1 : TwE6ThreeA2LineStmt) (hS3 : TwE6ThreeA2ConjStmt) (hLayer : TwE6ThreeLayerGen)
    (hTorus : TwE6ThreeTorusGen) (hComp : TwE6ThreeCompGen) (hNot : TwE6NotAll24Gen) :
    E6ThreeDefs.TwE6DiagNonParCubes := by
  intro K _ _ σ q hK3 hσ hKq h3 hq2 E hE hEc hED hEi hER
  classical
  by_cases hall : TwE6InnerAll24 K σ E
  swap
  · exact hNot K σ q hK3 hσ hKq h3 hq2 E hE hEc hED hEi hER hall
  obtain ⟨h₀, L, T, n, hline⟩ := hS1 K σ q hK3 hσ hKq h3 hq2
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq (by omega)
  let qp : TauCeti.PrimePower := ⟨ringChar K, f, hp, by omega⟩
  have hqp : qp.card = q := by
    rw [TauCeti.PrimePower.card_def]
    exact hqf.symm
  have hv : (TauCeti.LieTypeIndex.twistedE6 qp).Valid := TauCeti.LieTypeIndex.valid_twistedE6 qp
  obtain ⟨e⟩ := catEquiv_twistedE6_of_field qp hv K (hqp ▸ hKq) σ (hqp ▸ hσ)
  have hPc : Nat.card ↥(E ⊓ twistedE6Inn K σ) = 3 ^ 2 := card_inf_twistedE6Inn hKq σ hσ hEc hED hEi
  have hgen := planeGen_of_kfact hS Nat.prime_three (by norm_num) ⟨_, hv⟩ e.symm
    (by
      show 3 ≠ (TauCeti.LieTypeIndex.twistedE6 qp).characteristic
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact fun h => hK3 h.symm)
    (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 qp))
    (hE.mono (inf_le_left : E ⊓ twistedE6Inn K σ ≤ E)) hPc
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro s ⟨φ, hφP, hφ1, hφs⟩
  obtain ⟨hφE, hφI⟩ := Subgroup.mem_inf.1 hφP
  obtain ⟨v, rfl⟩ := hφI
  have hv1 : v ≠ 1 := fun h => hφ1 (by rw [h, map_one])
  have hv3 : v ^ 3 = 1 := by
    have hc : v ^ 3 ∈ Subgroup.center (twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) => φ x)
        (show MulAut.conj (v ^ 3) = 1 by rw [map_pow]; exact hE.2 _ hφE)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    rw [exceptional_fixed_center_trivial TwistTag.E6 K σ] at hc
    exact Subgroup.mem_bot.1 hc
  obtain ⟨g, hgC, hg⟩ := hS3 K σ q hK3 hσ hKq h3 hq2 (v : ModGL TwistTag.E6.tag K) v.2
    h₀ hline.h₀_mem (by have := congrArg Subtype.val hv3; simpa using this) hline.h₀_pow
    (hall v hφE hv1) hline.finrank_fixed
  obtain ⟨g', hg'⟩ : ∃ g' : twistedE6RootGroup K σ, (g' : ModGL TwistTag.E6.tag K) = g :=
    ⟨⟨g, hgC⟩, rfl⟩
  have hgv : g' * v * g'⁻¹ = ⟨h₀, hline.h₀_mem⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg']
    exact hg
  obtain ⟨c, hc⟩ : ∃ c : MulAut (twistedE6RootGroup K σ), c = MulAut.conj g' := ⟨_, rfl⟩
  have hcI : c ∈ twistedE6Inn K σ := by
    rw [hc]
    exact ⟨g', rfl⟩
  have hE'a : IsElemAbelian 3 (E.map (MulAut.congr c).toMonoidHom) := hE.map _
  have hE'c : Nat.card (E.map (MulAut.congr c).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr c).injective, hEc]
  have hE'D : E.map (MulAut.congr c).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rintro _ ⟨ε, hε, rfl⟩
    have hcD : c ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := Subgroup.mem_sup_left hcI
    rw [congr_toMonoidHom_apply]
    exact mul_mem (mul_mem hcD (hED hε)) (inv_mem hcD)
  have hE'i : ¬ E.map (MulAut.congr c).toMonoidHom ≤ twistedE6Inn K σ := by
    intro h
    apply hEi
    intro ε hε
    have h1 := h ⟨ε, hε, rfl⟩
    rw [congr_toMonoidHom_apply] at h1
    have he : ε = c⁻¹ * (c * ε * c⁻¹) * c := by group
    rw [he]
    exact mul_mem (mul_mem (inv_mem hcI) h1) hcI
  have hE'R : ¬ TwE6NormalizesR K σ (E.map (MulAut.congr c).toMonoidHom) :=
    fun h => hER (twE6NormalizesR_of_map_congr c h)
  have hall' : TwE6InnerAll24 K σ (E.map (MulAut.congr c).toMonoidHom) := by
    rw [hc]
    exact twE6InnerAll24_map_conj g' hall
  have hh : ∃ s₀ : twistedE6RootGroup K σ, (s₀ : ModGL TwistTag.E6.tag K) = h₀ ∧
      MulAut.conj s₀ ∈ E.map (MulAut.congr c).toMonoidHom := by
    refine ⟨⟨h₀, hline.h₀_mem⟩, rfl, MulAut.conj v, hφE, ?_⟩
    rw [congr_toMonoidHom_apply, hc, ← hgv, map_mul, map_mul, map_inv]
  have hLay := hLayer K σ q hK3 hσ hKq h3 hq2 h₀ L T n hline _ hE'a hE'c hE'D hE'i hE'R hall' hh
  have hTor := hTorus K σ q hK3 hσ hKq h3 hq2 h₀ L T n hline _ hE'a hE'c hE'D hE'i hE'R hall' hh
  have hCmp := hComp K σ q hK3 hσ hKq h3 hq2 h₀ L T n hline _ hE'a hE'c hE'D hE'i hE'R hall' hh
  have hU : ⨆ i, L i ≤ (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
      (twistedE6RootGroup K σ).subtype := iSup_le hLay
  have hTU : T ⊔ ⨆ i, L i ≤ (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
      (twistedE6RootGroup K σ).subtype := sup_le (hTor.trans (sup_le le_rfl hU)) hU
  have hn : n ∈ (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
      (twistedE6RootGroup K σ).subtype := (sup_le le_rfl hTU) hCmp
  have hCent : twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} ≤
      (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
        (twistedE6RootGroup K σ).subtype := by
    rw [hline.centralizer_eq]
    exact sup_le hTU ((Subgroup.zpowers_le).2 hn)
  have hcomm : (⟨h₀, hline.h₀_mem⟩ : twistedE6RootGroup K σ) * c s =
      c s * ⟨h₀, hline.h₀_mem⟩ := by
    have hvs : v * s = s * v := by
      have h := hφs
      simp only [MulAut.conj_apply] at h
      exact mul_inv_eq_iff_eq_mul.1 h
    rw [← hgv, hc, MulAut.conj_apply]
    calc g' * v * g'⁻¹ * (g' * s * g'⁻¹) = g' * (v * s) * g'⁻¹ := by group
      _ = g' * (s * v) * g'⁻¹ := by rw [hvs]
      _ = g' * s * g'⁻¹ * (g' * v * g'⁻¹) := by group
  have hcs : ((c s : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈
      twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} := by
    refine Subgroup.mem_inf.2 ⟨(c s).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    have := congrArg Subtype.val hcomm
    simpa only [Subgroup.coe_mul] using this
  obtain ⟨y, hy, hyc⟩ := hCent hcs
  have hyc' : y = c s := Subtype.ext hyc
  rw [hyc'] at hy
  exact mem_seitzHyperGamma_of_congr hy

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
