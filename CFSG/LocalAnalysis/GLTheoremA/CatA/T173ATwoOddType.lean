module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem six_dvd_card_GL (m : ℕ) (h3 : 3 ≤ m) : 6 ∣ Nat.card (GL (Fin m) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have h6 : 6 ∣ 2 ^ (k + 3) - 2 ^ (k + 1) := by
    refine ⟨2 ^ k, ?_⟩
    have : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  exact h6.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨k + 1, by omega⟩ : Fin (k + 3))))

private theorem three_dvd_card_linearEquiv (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (h3 : 3 ≤ Module.finrank (ZMod 2) W) :
    3 ∣ Nat.card (W ≃ₗ[ZMod 2] W) := by
  classical
  let b := Module.finBasis (ZMod 2) W
  let e : GL (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  rw [← Nat.card_congr e.toEquiv]
  exact (by norm_num : 3 ∣ 6).trans (six_dvd_card_GL (Module.finrank (ZMod 2) W) h3)

theorem lin_two_catalog_top (hV : 5 ≤ Module.finrank (ZMod 2) V) :
    catalogIs (PSimple 3 (⊤ : Subgroup (V ≃ₗ[ZMod 2] V)))
      (isLnA (Module.finrank (ZMod 2) V) 2) := by
  have h3 : 3 ≤ Module.finrank (ZMod 2) V := by omega
  let eLin : V ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
    LinearEquiv.ofFinrankEq V (Fin (Module.finrank (ZMod 2) V) → ZMod 2) (by
      rw [Module.finrank_fin_fun])
  let E : ↥(⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) ≃* VecAut (Module.finrank (ZMod 2) V) :=
    (Subgroup.topEquiv (G := V ≃ₗ[ZMod 2] V)).trans (S172A.GL.conjEquiv eLin)
  haveI : IsSimpleGroup (VecAut (Module.finrank (ZMod 2) V)) :=
    (S172A.GL.vecAut_simple_nonab h3).1
  haveI : IsSimpleGroup (V ≃ₗ[ZMod 2] V) := (S172A.GL.conjEquiv eLin).isSimpleGroup
  haveI : IsSimpleGroup ↥(⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) :=
    (Subgroup.topEquiv (G := V ≃ₗ[ZMod 2] V)).isSimpleGroup
  have hnab : ∃ a b : ↥(⊤ : Subgroup (V ≃ₗ[ZMod 2] V)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (S172A.GL.vecAut_simple_nonab h3).2
    exact ⟨E.symm a, E.symm b, fun h => hab (by simpa using congrArg E h)⟩
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) :=
    S172A.GL.isQuasisimple_of_simple_nonab hnab
  have hZ : Subgroup.center ↥(⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) = ⊥ :=
    S172A.GL.center_eq_bot_of_simple_nonab hnab
  have hcard : 3 ∣ Nat.card ↥(⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) := by
    rw [Nat.card_congr (Subgroup.topEquiv (G := V ≃ₗ[ZMod 2] V)).toEquiv]
    exact three_dvd_card_linearEquiv V h3
  obtain ⟨eP⟩ := S172A.pSimple_equiv hq hZ hcard
  exact S172A.catalogIs_isLnA_of_vecAut hV (eP.trans E)

theorem lin_two_oddFull_layerType (hV : 7 ≤ Module.finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg3 : g ^ 3 = 1) (hfix : Module.finrank (ZMod 2) (fixSp g) = 1) :
    catalogIs (PSimple 3 (stdLayer g)) (isLnA ((Module.finrank (ZMod 2) V - 1) / 2) 4) := by
  obtain ⟨m, hm⟩ := S172A.GL.even_finrank_comSp hg3
  have hm' : Module.finrank (ZMod 2) (comSp g) = 2 * m := by omega
  have hsum := S172A.GL.finrank_fixSp hg3
  have hm2 : 2 ≤ m := by omega
  have hVeq : Module.finrank (ZMod 2) V = 2 * m + 1 := by omega
  have hmeq : (Module.finrank (ZMod 2) V - 1) / 2 = m := by
    rw [hVeq]
    omega
  rw [hmeq]
  obtain ⟨F, hFC, hFn, hFcomm, hFq, hF3, ⟨eQ⟩⟩ :=
    S172A.GL.fullLayer hg3 hfix hm' hm2
  obtain ⟨-, hLayer⟩ := S172A.layer_eq_of_normal_quasisimple hFC hFn hFq hFcomm
  obtain ⟨eP⟩ := S172A.pSimple_equiv_centerQuot hFq hF3
  have hstd : stdLayer g = F := by
    unfold stdLayer
    exact hLayer
  rw [hstd]
  exact S172A.catalogIs_isLnA_four_of_three_le (m := m) (by omega : 3 ≤ m)
    (eP.symm.trans eQ)

theorem lin_two_oddBlock_type (hV : 6 ≤ Module.finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg3 : g ^ 3 = 1) (hfix : Module.finrank (ZMod 2) (fixSp g) = 1) :
    catalogIs (PSimple 3 (linTwoOddBlock g)) (isLnA (Module.finrank (ZMod 2) V - 1) 2) := by
  let hc : IsCompl (comSp g) (fixSp g) := (S172A.GL.isCompl_fixSp_comSp hg3).symm
  have hK : linTwoOddBlock g = (S172A.GL.glueHom hc).range := lin_two_oddBlock_eq_range hg3
  rw [hK]
  let φ : ((comSp g) ≃ₗ[ZMod 2] (comSp g)) →* (V ≃ₗ[ZMod 2] V) := S172A.GL.glueHom hc
  have hφ : Function.Injective φ := S172A.GL.glueHom_injective hc
  let eK : ((comSp g) ≃ₗ[ZMod 2] (comSp g)) ≃* ↥(φ.range) := MonoidHom.ofInjective hφ
  have hdimU : Module.finrank (ZMod 2) (comSp g) = Module.finrank (ZMod 2) V - 1 := by
    have hsum := S172A.GL.finrank_fixSp hg3
    omega
  have hdimU3 : 3 ≤ Module.finrank (ZMod 2) (comSp g) := by omega
  let eU : (comSp g) ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) (comSp g)) → ZMod 2) :=
    LinearEquiv.ofFinrankEq (comSp g)
      (Fin (Module.finrank (ZMod 2) (comSp g)) → ZMod 2) (by rw [Module.finrank_fin_fun])
  haveI : IsSimpleGroup (VecAut (Module.finrank (ZMod 2) (comSp g))) :=
    (S172A.GL.vecAut_simple_nonab hdimU3).1
  haveI : IsSimpleGroup ((comSp g) ≃ₗ[ZMod 2] (comSp g)) :=
    (S172A.GL.conjEquiv eU).isSimpleGroup
  haveI : IsSimpleGroup ↥(φ.range) := eK.symm.isSimpleGroup
  have hnabU : ∃ a b : (comSp g) ≃ₗ[ZMod 2] (comSp g), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (S172A.GL.vecAut_simple_nonab hdimU3).2
    exact ⟨(S172A.GL.conjEquiv eU).symm a, (S172A.GL.conjEquiv eU).symm b,
      fun h => hab (by simpa using congrArg (S172A.GL.conjEquiv eU) h)⟩
  have hnabK : ∃ a b : ↥(φ.range), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabU
    exact ⟨eK a, eK b, fun h => hab (by simpa using congrArg eK.symm h)⟩
  have hqK : CFSG.Open.IsQuasisimple ↥(φ.range) :=
    S172A.GL.isQuasisimple_of_simple_nonab hnabK
  have hZK : Subgroup.center ↥(φ.range) = ⊥ :=
    S172A.GL.center_eq_bot_of_simple_nonab hnabK
  have hcardK : 3 ∣ Nat.card ↥(φ.range) := by
    rw [← Nat.card_congr eK.toEquiv]
    exact three_dvd_card_linearEquiv (comSp g) hdimU3
  obtain ⟨eP⟩ := S172A.pSimple_equiv hqK hZK hcardK
  have eAll : PSimple 3 φ.range ≃* VecAut (Module.finrank (ZMod 2) V - 1) := by
    rw [← hdimU]
    exact eP.trans (eK.symm.trans (S172A.GL.conjEquiv eU))
  exact S172A.catalogIs_isLnA_of_vecAut (by omega : 5 ≤ Module.finrank (ZMod 2) V - 1) eAll

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
