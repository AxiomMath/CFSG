module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderContra
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSp4Std
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderTransport
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2OffInner
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Out
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoA2Inner

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoA2PerMaxData
public import CFSG.ClassicalGroups.Symplectic.ComponentCoverGriessB2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepOffenderJ
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem le_sup_centralizer_of_bestOffender_sp4 (hM1 : K54NatQuotSp4) (hP : K54PerfStabSp4)
    {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ) {L : Subgroup G}
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* StatedSp 2 F) {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hbest : IsBestOffenderOn ρ A ⊤) : A ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
  classical
  by_contra hnot
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  obtain ⟨N, hrange, hIcomm, hAI⟩ := hM1 G V ρ hfaith L F n hn hF ⟨e⟩ A hAN hbest hnot
  have hinj : Function.Injective (antiSp F).subtype := Subtype.val_injective
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hrange' : N.Mat.range = (antiSp F).subtype.range :=
    hrange.trans (Subgroup.range_subtype _).symm
  have hperf : PerfStab N.Mat := PerfStab.of_range_eq N.mat_inj hinj hrange' (hP F hF4)
  have hS : NatSchur N.Mat := NatSchur.of_range_eq hrange' natSchur_antiSp
  have hO : NatOut N.Mat := NatOut.of_range_eq hrange' natOut_antiSp
  have hcen : Subgroup.center ↥L = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by norm_num)] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  have hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 := by
    intro z hz hc
    have hzc : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hc k k.2)
    rw [hcen, Subgroup.mem_bot] at hzc
    have h1 : z = 1 := congrArg Subtype.val hzc
    rw [h1, one_pow]
  have hB2 : ∀ b ∈ A, b * b = 1 := fun b hb =>
    hfaith (by
      rw [map_one]
      exact LinearMap.ext fun v => (hbest.1 b hb b hb).2 v Submodule.mem_top)
  have hrel := relIndex_innerPart_le_two_sp4 L A hn hF e hAN hB2
  have hall := NatQuot.forall_conjAgree_of_bestOffender hfaith hn hF (by norm_num : 2 ≤ 4)
    (by norm_num : 4 ≤ 6) N hperf hS hO hZ hIcomm hbest hAN hAI hrel
  exact hnot (le_sup_centralizer_of_forall_conjAgree hall)

theorem k54InnerAt_of_B2 {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hM1 : K54NatQuotSp4) (hP : K54PerfStabSp4) (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf Ls ⊤)
    (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower) (hd : d.1 = .B 2 Q)
    (hQ : Q.p = 2)
    (hLd : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    K54InnerAt T Ls := by
  classical
  intro A hA
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  let : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  obtain ⟨eL⟩ := hLd
  rcases d with ⟨d, hv⟩
  have hd' : d = TauCeti.LieTypeIndex.B 2 Q := hd
  subst hd'
  have hf : 2 ≤ Q.exponent := two_le_exponent_of_valid_B2 hQ hv
  obtain ⟨e⟩ := CFSG.ClassicalGroups.Symplectic.exists_mulEquiv_statedSp_of_component_B2 hL.2.2
    hf hQ rfl eL
  exact le_sup_centralizer_of_bestOffender_sp4 hM1 hP (gnRep hV) (gnRep_injective hV) hf
    (GaloisField.card 2 Q.exponent (by omega)) e (map_mk_le_normalizer_component hX hV hL hA)
    (isBestOffenderOn_gnImg hX hV hA)

theorem gnImg_thompsonJ_le_sup_centralizer_of_B2 {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hM1 : K54NatQuotSp4) (hP : K54PerfStabSp4) (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf Ls ⊤)
    (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower) (hd : d.1 = .B 2 Q)
    (hQ : Q.p = 2)
    (hLd : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    gnImg T (thompsonJ T) ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
  gnImg_thompsonJ_le_sup_centralizer_of_K54InnerAt (k54InnerAt_of_B2 hM1 hP hX hL d Q hd hQ hLd)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
