module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HNCheck
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.NoIrrEngines
public import CFSG.Sporadic.HNSchreier.Seeds
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.GH74.Generic.GKFCover
public import Certificates.Certificate2081
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2107
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate3166
public import Certificates.Certificate9114
public import Certificates.Certificate9208
public import Certificates.Certificate14985
public import Certificates.Certificate16041
public import Certificates.Certificate24321
public import Certificates.Certificate26963
public import Certificates.Certificate129008
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.Recognition.HNMultiplier
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import Certificates.Certificate1016Base
public import Certificates.Certificate8171
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint CFSG.Sporadic.F5 CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier
  CFSG.Sporadic.HNSchreier.Native CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem hnMat_list_prod (l : List (J CFSG.Sporadic.HN.Native.hnData)) :
    mat CFSG.Sporadic.HN.Native.hnData l.prod =
      (l.map (mat CFSG.Sporadic.HN.Native.hnData)).prod := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    rfl

noncomputable def hnSlpJ (prog : List (List ℕ)) : Array (J CFSG.Sporadic.HN.Native.hnData) :=
  prog.foldl (fun R w => R.push (w.map fun l => R.getD (l - 1) 1).prod)
    #[a CFSG.Sporadic.HN.Native.hnData, b CFSG.Sporadic.HN.Native.hnData]

def HnCorr (R : Array (Array (Array ℕ))) (RJ : Array (J CFSG.Sporadic.HN.Native.hnData)) :
    Prop :=
  R.size = RJ.size ∧
    ∀ k, toMat 5 133 (R.getD k (idM 133)) = mat CFSG.Sporadic.HN.Native.hnData (RJ.getD k 1)

theorem toMat_wordM_of_corr {R : Array (Array (Array ℕ))}
    {RJ : Array (J CFSG.Sporadic.HN.Native.hnData)} (h : HnCorr R RJ) (w : List ℕ) :
    toMat 5 133 (wordM (fun l => R.getD (l - 1) (idM 133)) w) =
      mat CFSG.Sporadic.HN.Native.hnData (w.map fun l => RJ.getD (l - 1) 1).prod := by
  rw [toMat_wordM, hnMat_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun l _ => h.2 (l - 1))

theorem hnCorr_push {R : Array (Array (Array ℕ))} {RJ : Array (J CFSG.Sporadic.HN.Native.hnData)}
    (h : HnCorr R RJ) (w : List ℕ) :
    HnCorr (R.push (wordM (fun l => R.getD (l - 1) (idM 133)) w))
      (RJ.push (w.map fun l => RJ.getD (l - 1) 1).prod) := by
  have hw := toMat_wordM_of_corr h w
  obtain ⟨hsz, h⟩ := h
  refine ⟨by simp [hsz], fun k => ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push,
    Array.getElem?_push, hsz]
  split_ifs
  · exact hw
  · rw [← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?]
    exact h k

theorem hnCorr_foldl (prog : List (List ℕ)) :
    ∀ (R : Array (Array (Array ℕ))) (RJ : Array (J CFSG.Sporadic.HN.Native.hnData)), HnCorr R RJ →
      HnCorr (prog.foldl (fun R w => R.push (wordM (fun l => R.getD (l - 1) (idM 133)) w)) R)
        (prog.foldl (fun R w => R.push (w.map fun l => R.getD (l - 1) 1).prod) RJ) := by
  induction prog with
  | nil => exact fun _ _ h => h
  | cons w prog ih => exact fun R RJ h => ih _ _ (hnCorr_push h w)

theorem hnCorr_init :
    HnCorr #[rowsA, rowsB]
      #[a CFSG.Sporadic.HN.Native.hnData, b CFSG.Sporadic.HN.Native.hnData] := by
  refine ⟨rfl, fun k => ?_⟩
  rcases k with _ | _ | k
  · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_zero,
      Option.getD_some]
    rw [mat_a' (det_ne_zero_of_pow_eq_one' (by norm_num) Certificates.certificate3166.1)]
    exact toMat_rowsA (CFSG.Sporadic.HN.Native.hnData ())
  · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some]
    rw [mat_b' (det_ne_zero_of_pow_eq_one' (by norm_num) Certificates.certificate3166.2.1)]
    exact toMat_rowsB (CFSG.Sporadic.HN.Native.hnData ())
  · simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_succ,
      List.getElem?_nil, Option.getD_none]
    rw [toMat_idM]
    rfl

theorem hnSlp_corr (prog : List (List ℕ)) :
    HnCorr (hnSlpM prog) (hnSlpJ prog) :=
  hnCorr_foldl prog _ _ hnCorr_init

@[irreducible] noncomputable def hnReg (l : ℕ) : J CFSG.Sporadic.HN.Native.hnData :=
  (hnSlpJ hnHeisProg).getD (l - 1) 1

theorem hnRelOK_spec {u v : List ℕ}
    (h : hnRelOK (hnSlpM hnHeisProg) u v = true) : (u.map hnReg).prod = (v.map hnReg).prod := by
  apply mat_injective
  have hu := toMat_wordM_of_corr (hnSlp_corr hnHeisProg) u
  have hv := toMat_wordM_of_corr (hnSlp_corr hnHeisProg) v
  unfold hnReg
  rw [← hu, ← hv]
  exact toMat_eq_of_beq h

theorem hnReg_ne_one_of_notIdM {l : ℕ}
    (h : notIdM 133 ((hnSlpM hnHeisProg).getD (l - 1) (idM 133)) = true) : hnReg l ≠ 1 := by
  intro h1
  apply toMat_ne_one_of_notIdM h
  rw [(hnSlp_corr hnHeisProg).2 (l - 1)]
  have : (hnSlpJ hnHeisProg).getD (l - 1) 1 = 1 := by
    unfold hnReg at h1
    exact h1
  rw [this]
  rfl

private theorem pow_five_of_word {G : Type*} [Monoid G] {g : G}
    (h : g * (g * (g * (g * g))) = 1) :
    g ^ 5 = 1 := by
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

private theorem heisCfg_five_two {G : Type*} [Group G] {x₁ x₂ y₁ y₂ z : G}
    (hx₁ : x₁ ^ 5 = 1) (hx₂ : x₂ ^ 5 = 1) (hz : z ^ 5 = 1)
    (hzx₁ : x₁ * z = z * x₁) (hzx₂ : x₂ * z = z * x₂) (hzy₁ : y₁ * z = z * y₁)
    (hzy₂ : y₂ * z = z * y₂) (hyx₁ : x₁ * y₁ = y₁ * (x₁ * z)) (hyx₂ : x₂ * y₂ = y₂ * (x₂ * z))
    (hxx : x₁ * x₂ = x₂ * x₁) (hyy : y₁ * y₂ = y₂ * y₁) (hxy₁ : x₁ * y₂ = y₂ * x₁)
    (hxy₂ : x₂ * y₁ = y₁ * x₂) (hz1 : z ≠ 1) :
    HeisCfg 5 2 ![x₁, x₂] ![y₁, y₂] z where
  xp := Fin.forall_fin_two.2 ⟨hx₁, hx₂⟩
  zp := hz
  zx := Fin.forall_fin_two.2 ⟨hzx₁, hzx₂⟩
  zy := Fin.forall_fin_two.2 ⟨hzy₁, hzy₂⟩
  yx := by
    have key : ∀ x y : G, x * y = y * (x * z) → y⁻¹ * x * y = x * z := fun x y h => by
      rw [mul_assoc, h]
      group
    exact Fin.forall_fin_two.2 ⟨key _ _ hyx₁, key _ _ hyx₂⟩
  xx := Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨rfl, hxx⟩, Fin.forall_fin_two.2 ⟨hxx.symm, rfl⟩⟩
  yy := Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => hyy⟩,
    Fin.forall_fin_two.2 ⟨fun _ => hyy.symm, fun h => absurd rfl h⟩⟩
  xy := Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => hxy₁⟩,
    Fin.forall_fin_two.2 ⟨fun _ => hxy₂, fun h => absurd rfl h⟩⟩
  z1 := hz1

theorem hn_heisCfgJ :
    HeisCfg 5 2 ![hnReg hnHeisX1, hnReg hnHeisX2] ![hnReg hnHeisY1, hnReg hnHeisY2]
        (hnReg hnHeisZ) ∧ ∀ i, ![hnReg hnHeisY1, hnReg hnHeisY2] i ^ 5 = 1 := by
  have h := Certificates.certificate129008
  unfold hnHeisCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, hz⟩ := h
  replace h1 := hnRelOK_spec h1
  replace h2 := hnRelOK_spec h2
  replace h3 := hnRelOK_spec h3
  replace h4 := hnRelOK_spec h4
  replace h5 := hnRelOK_spec h5
  replace h6 := hnRelOK_spec h6
  replace h7 := hnRelOK_spec h7
  replace h8 := hnRelOK_spec h8
  replace h9 := hnRelOK_spec h9
  replace h10 := hnRelOK_spec h10
  replace h11 := hnRelOK_spec h11
  replace h12 := hnRelOK_spec h12
  replace h13 := hnRelOK_spec h13
  replace h14 := hnRelOK_spec h14
  replace h15 := hnRelOK_spec h15
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1 h2 h3 h4
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h5 h6 h7 h8
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h9 h10 h11
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h12 h13 h14
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h15
  exact ⟨heisCfg_five_two (pow_five_of_word h1) (pow_five_of_word h2) (pow_five_of_word h5) h6 h7
    h8 h9 h10 h11 h12 h13 h14 h15 (hnReg_ne_one_of_notIdM hz),
    Fin.forall_fin_two.2 ⟨pow_five_of_word h3, pow_five_of_word h4⟩⟩

theorem hn_heisCfg :
    HeisCfg 5 2 (fun i => CFSG.Sporadic.Bridge.HN.nativeEquiv.symm
          (![hnReg hnHeisX1, hnReg hnHeisX2] i))
        (fun i => CFSG.Sporadic.Bridge.HN.nativeEquiv.symm (![hnReg hnHeisY1, hnReg hnHeisY2] i))
        (CFSG.Sporadic.Bridge.HN.nativeEquiv.symm (hnReg hnHeisZ)) ∧
      ∀ i, CFSG.Sporadic.Bridge.HN.nativeEquiv.symm (![hnReg hnHeisY1, hnReg hnHeisY2] i) ^ 5 =
        1 := by
  obtain ⟨h, hy⟩ := hn_heisCfgJ
  set e := CFSG.Sporadic.Bridge.HN.nativeEquiv with he
  refine ⟨?_, fun i => e.injective (by
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]; exact hy i)⟩
  exact
    { xp := fun i => e.injective (by
        rw [map_pow, MulEquiv.apply_symm_apply, map_one]; exact h.xp i)
      zp := e.injective (by rw [map_pow, MulEquiv.apply_symm_apply, map_one]; exact h.zp)
      zx := fun i => e.injective (by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h.zx i)
      zy := fun i => e.injective (by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h.zy i)
      yx := fun i => e.injective (by
        rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h.yx i)
      xx := fun i j => e.injective (by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h.xx i j)
      yy := fun i j hij => e.injective (by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h.yy i j hij)
      xy := fun i j hij => e.injective (by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h.xy i j hij)
      z1 := fun h1 => h.z1 (by rw [← e.apply_symm_apply (hnReg hnHeisZ), h1, map_one]) }

theorem hn_index_inner :
    (inner NativeSporadic.HN).index = 2 :=
  ctuc_hn_full_automorphism_group.2.2.2.2.2.2.2.2.2.2.2.1

noncomputable def hnCarrierEquiv : NativeSporadic.HN ≃* NativeSporadic.Carrier .HN :=
  MulEquiv.refl _

theorem hn_center
    (L : Type) [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (he : Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.HN)) :
    Nat.card (Subgroup.center L) = 1 := by
  obtain ⟨e⟩ := he
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans hnCarrierEquiv)
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (NativeSporadic.Carrier .HN)) =
      1 := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_HN
  rw [hM] at h
  exact Nat.dvd_one.1 h

private theorem orderOf_two_zmod_five_hn : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem noIrrFFOffender_HN_native :
    NoIrrFFOffender NativeSporadic.HN := by
  obtain ⟨h, hy⟩ := hn_heisCfg
  refine noIrrFFOffender_of_heisCfg (k := 2) (c := 1) (by norm_num)
    (fun B _ _ => card_le_two_mul_inf_inner_of_index hn_index_inner B)
    (fun L _ _ hq he _ => ?_) h hy ?_
  · rw [hn_center L hq he]
    norm_num
  · rw [CFSG.Sporadic.HN.card_HN, orderOf_two_zmod_five_hn]
    norm_num

theorem noIrrFFOffender_HN :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .HN).Group :=
  noIrrFFOffender_transfer noIrrFFOffender_HN_native
    CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_HN :
    GF2NoFFSporadicFor .HN :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_HN

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
