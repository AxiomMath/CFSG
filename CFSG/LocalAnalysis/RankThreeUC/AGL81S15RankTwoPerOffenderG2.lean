module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderContra
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderTransport
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderG2Std
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderG2Perf
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderG2Out
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderG2M1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoA2Inner

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoA2PerMaxData
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepOffenderJ

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.Ch11.SecB.K5

theorem le_sup_centralizer_of_bestOffender_g2
    {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ) {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥L) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* ↥(cayleyGroup F)) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hbest : IsBestOffenderOn ρ A ⊤) :
    A ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
  classical
  by_contra hnot
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  obtain ⟨N, hrange, hIcomm, hAI⟩ := exists_natQuot_g2 ρ hfaith hq hn hF e hAN hbest hnot
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hperf : PerfStab N.Mat :=
    PerfStab.of_range_eq N.mat_inj g2Six_injective hrange (g2_perfStab hF4)
  have hS : NatSchur N.Mat := NatSchur.of_range_eq hrange natSchur_g2Six
  have hO : NatOut N.Mat := NatOut.of_range_eq hrange (natOut_g2Six hn hF)
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hcen : Subgroup.center ↥L = ⊥ :=
    g2_center_eq_bot hn hFc
      (e.trans (MulEquiv.subgroupCongr CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup.symm))
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
  have hrel := relIndex_innerPart_le_two_g2 L A hn hF e hAN hB2
  have hall := NatQuot.forall_conjAgree_of_bestOffender hfaith hn hF (by norm_num : 2 ≤ 6)
    (by norm_num : 6 ≤ 6) N hperf hS hO hZ hIcomm hbest hAN hAI hrel
  exact hnot (le_sup_centralizer_of_forall_conjAgree hall)

theorem k54InnerAt_of_G2
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf Ls ⊤) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥Ls ≃* ↥(cayleyGroup F)) :
    K54InnerAt T Ls := by
  classical
  intro A hA
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  let : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  exact le_sup_centralizer_of_bestOffender_g2 (gnRep hV) (gnRep_injective hV) hL.2.2 hn hF e
    (map_mk_le_normalizer_component hX hV hL hA) (isBestOffenderOn_gnImg hX hV hA)

theorem gnImg_thompsonJ_le_sup_centralizer_of_G2
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf Ls ⊤) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥Ls ≃* ↥(cayleyGroup F)) :
    gnImg T (thompsonJ T) ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
  gnImg_thompsonJ_le_sup_centralizer_of_K54InnerAt (k54InnerAt_of_G2 hX hL hn hF e)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
