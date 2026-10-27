module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepOffenderJ
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSL3Nat
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSL3Std
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderIndex
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderTransport
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderContra
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderSplit
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoA2Inner
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Matrix
open scoped MatrixGroups

theorem le_sup_centralizer_of_bestOffender_sl3 {G : Type} [Group G] [Finite G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hfaith : Function.Injective ρ) {L : Subgroup G} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(3, F)) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hbest : IsBestOffenderOn ρ A ⊤) :
    A ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
  classical
  by_contra hnot
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  obtain ⟨N, hNr, hIcomm, hAI⟩ := exists_natQuot_sl3 ρ hfaith hn hF e hAN hbest hnot
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hS : NatSchur N.Mat := NatSchur.of_range_eq hNr natSchur_sl3
  have hO : NatOut N.Mat := NatOut.of_range_eq hNr natOut_sl3
  have hP : PerfStab N.Mat := PerfStab.of_range_eq N.mat_inj
    (fun g g' h => (Matrix.SpecialLinearGroup.toGL_inj g g').mp h) hNr (sl3_perfStab h4)
  have hZ' : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 := center_pow_three e
  have hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2)
    simpa using congrArg Subtype.val (hZ' _ hmem)
  have hfaith' : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := fun a _ h =>
    hfaith (by rw [map_one]; exact LinearMap.ext h)
  obtain ⟨hA2, -⟩ := (isBestOffender_iff_on ρ A hfaith').mpr hbest
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) a ha
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA2.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hrel := NatQuot.relIndex_innerPart_le_two (by norm_num) N hS hO hIcomm hAsq hAc hAN hAI
  have hall := NatQuot.forall_conjAgree_of_bestOffender hfaith hn hF (by norm_num) (by norm_num) N
    hP hS hO hZ hIcomm hbest hAN hAI hrel
  exact hnot (le_sup_centralizer_of_forall_conjAgree hall)

section AGL

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem k54InnerAt_of_A2 (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf Ls ⊤) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : ↥Ls ≃* SL(3, F)) : K54InnerAt T Ls := by
  intro A hA
  classical
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hinj : Function.Injective (gnRep hV) := gnRep_injective hV
  have hfaith' : ∀ a ∈ A.map (QuotientGroup.mk' (gnC T)), (∀ v, gnRep hV a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hbest : IsBestOffenderOn (gnRep hV) (A.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on _ _ hfaith').mp
      ⟨isElementaryAbelian_map_mk hA, isBestOffender_gnRep hV hX hA⟩
  exact le_sup_centralizer_of_bestOffender_sl3 (gnRep hV) hinj hn hF e
    (map_mk_le_normalizer_component hX hV hL hA) hbest

theorem gnImg_thompsonJ_le_sup_centralizer_of_A2 (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf Ls ⊤) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥Ls ≃* SL(3, F)) :
    gnImg T (thompsonJ T) ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
  gnImg_thompsonJ_le_sup_centralizer_of_K54InnerAt (k54InnerAt_of_A2 hX hL hn hF e)

end AGL

end CFSG.LocalAnalysis.RankThreeUC.S15
