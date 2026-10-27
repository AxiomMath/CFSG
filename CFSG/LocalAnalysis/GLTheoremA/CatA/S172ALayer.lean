module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AResid

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut)

open CFSG.LocalAnalysis.GLTheoremA.S172 (Cfg172) in
open CFSG.LocalAnalysis.GLTheoremA.S10 (cs) in
theorem s172ALayer_of_bridge
    (hb : CFSG.LocalAnalysis.GLTheoremA.CatDistinct.OrderBridge) :
    S172ALayer := by
  classical
  intro n hn hn7 Ω _ _ S B D K x hcfg hS hK D₁ K₁ hstd₁ hK₁
  obtain ⟨r, hr⟩ := hn
  have hr3 : 3 ≤ r := by omega
  obtain ⟨L⟩ := exists_lsetup hr hr3 hcfg hS
  have hnr : (n - 1) / 2 = r := by omega
  have hn2 : n - 2 = 2 * r - 1 := by omega
  have hn3 : (n - 3) / 2 = r - 1 := by omega
  rw [hnr] at hK
  rw [hn2] at hK₁
  rw [hn3]
  obtain ⟨d, hdE, hd1, hd3, hD, hdcase⟩ := classify_gen L hcfg.std
  obtain ⟨d₁, hd₁E, hd₁1, hd₁3, hD₁, hd₁case⟩ := classify_gen L hstd₁
  rw [hn2] at hdcase hd₁case
  have hdfull : Module.finrank (ZMod 2) (GL.fixSp d) = 1 := by
    rcases hdcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact (not_both_types hb hr3 hK h).elim
    · exact h
  have hd₁one : Module.finrank (ZMod 2) (GL.comSp d₁) = 2 := by
    rcases hd₁case with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact (not_both_types hb hr3 h hK₁).elim
  obtain ⟨hDB, -, -, -, -, -, -⟩ := hcfg.std
  obtain ⟨hD₁B, -, -, -, -, -, -⟩ := hstd₁
  have hEel := isElemAbelian_range L.φ L.hBel
  have hcomm : d * d₁ = d₁ * d :=
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨d, hdE⟩ ⟨d₁, hd₁E⟩)
  have hdC : d ∈ Subgroup.centralizer ({d₁} : Set (VecAut n)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have hc₁ := GL.isCompl_fixSp_comSp hd₁3
  have hcentD := inf_cs_eq_map L.Θ L.φ hDB L.hΘ L.hΘS L.hconj hdE hD
  have hcentD₁ := inf_cs_eq_map L.Θ L.φ hD₁B L.hΘ L.hΘS L.hconj hd₁E hD₁
  have hH : S ⊓ cs (D ⊔ D₁) = (Subgroup.centralizer ({d₁} : Set (VecAut n)) ⊓
      Subgroup.centralizer ({d} : Set (VecAut n))).map L.Θ := by
    show S ⊓ Subgroup.centralizer ((D ⊔ D₁ : Subgroup Ω) : Set Ω) = _
    rw [centralizer_sup, inf_inf_distrib_left, hcentD, hcentD₁,
      ← Subgroup.map_inf_eq _ _ _ L.hΘ, inf_comm]
  have hle : GL.fixSp d ≤ GL.fixSp d₁ := by
    intro u hu
    have hg : d₁ * d = d * d₁ := hcomm.symm
    exact GL.mem_fixSp.2 (GL.fix_of_finrank_one hdfull (fun u hu => GL.cent_fix hg hu) u hu)
  set dW : ↥(GL.fixSp d₁) ≃ₗ[ZMod 2] ↥(GL.fixSp d₁) := GL.resFix d₁ ⟨d, hdC⟩ with hdW
  have h3W : dW ^ 3 = 1 := by
    have h : (⟨d, hdC⟩ : Subgroup.centralizer ({d₁} : Set (VecAut n))) ^ 3 = 1 := Subtype.ext hd3
    calc dW ^ 3 = GL.resFix d₁ ((⟨d, hdC⟩ : Subgroup.centralizer ({d₁} : Set (VecAut n))) ^ 3) :=
          (map_pow _ _ _).symm
      _ = 1 := by rw [h, map_one]
  have hfixW : Module.finrank (ZMod 2) (GL.fixSp dW) = 1 := by
    have hsub : GL.fixSp dW = Submodule.comap (GL.fixSp d₁).subtype (GL.fixSp d) := by
      ext w
      rw [GL.mem_fixSp, Submodule.mem_comap, GL.mem_fixSp]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [hsub, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)]
    exact hdfull
  have hV : Module.finrank (ZMod 2) (Fin n → ZMod 2) = 2 * r + 1 := by
    rw [Module.finrank_fin_fun, hr]
  have hsum₁ := GL.finrank_fixSp hd₁3
  have hsumW := GL.finrank_fixSp h3W
  have hmW : Module.finrank (ZMod 2) (GL.comSp dW) = 2 * (r - 1) := by omega
  obtain ⟨F, hFle, hFn, hFc, hFq, hF3, ⟨eQ⟩⟩ := GL.fullLayer h3W hfixW hmW (by omega : 2 ≤ r - 1)
  obtain ⟨hle', hnorm', hcomm'⟩ := GL.ext_layer hd₁3 hd₁one hdC F hFle hFn hFc
  have hNq' : CFSG.Open.IsQuasisimple ↥(F.map (GL.glueHom hc₁)) :=
    isQuasisimple_map_inj _ (GL.glueHom_injective hc₁) hFq
  have hNq : CFSG.Open.IsQuasisimple ↥((F.map (GL.glueHom hc₁)).map L.Θ) :=
    isQuasisimple_map_inj _ L.hΘ hNq'
  have hlay := layer_eq_of_normal_quasisimple (Subgroup.map_mono hle')
    (normal_map_subgroupOf L.Θ hle' hnorm') hNq (by
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono hcomm')
  have hΞ : Function.Injective (L.Θ.comp (GL.glueHom hc₁)) :=
    L.hΘ.comp (GL.glueHom_injective hc₁)
  have hfin : catalogIs (PSimple 3 ((F.map (GL.glueHom hc₁)).map L.Θ)) (isLnA (r - 1) 4) := by
    rw [Subgroup.map_map]
    exact catalogIs_pSimple_map _ hΞ hFq hF3 (by omega) eQ
  exact catalogIs_pSimple_congr (hlay.2.symm.trans (congrArg GLALayer hH).symm) hfin

section Holds


theorem s172ALayer_holds : S172ALayer :=
  s172ALayer_of_bridge CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremA.S172A

end
