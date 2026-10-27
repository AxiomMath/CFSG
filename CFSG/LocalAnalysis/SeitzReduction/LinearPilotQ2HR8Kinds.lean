module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2BLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitSmall
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftDecomp
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift centralizerPerfectCore OddSchurTrivial)
open Matrix (SpecialLinearGroup)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_surjective_neighbourCore_of_perfectCore_eq {X : Subgroup G}
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hcore : perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G)))) = Kc) (hB : HasBLift Kc) :
    ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
      q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
      ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
        oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
          ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ := by
  obtain ⟨q, hqs, hqc, hqapp⟩ := exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  refine ⟨q, hqs, hqc, ?_, hqapp⟩
  have hle : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  set φ : centralizerPerfectCore X →* centralizer (X : Set G) := Subgroup.inclusion hle with hφ
  have hφinj : Function.Injective φ := Subgroup.inclusion_injective hle
  have hmap : q.ker.map φ ≤ oddCore (centralizer (X : Set G)) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (q y : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) = 1 := by
      rw [MonoidHom.mem_ker.1 hy]
      rfl
    rw [hqapp] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hcard : Nat.card q.ker = Nat.card (q.ker.map φ) :=
    (Subgroup.card_map_of_injective hφinj).symm
  have hOodd : Odd (Nat.card (oddCore (centralizer (X : Set G)))) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  rw [hcard]
  exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hmap)

theorem exists_surjective_specialLinear_of_lieModel_four
    {P : Type} [Group P] [Finite P]
    [Group.IsPerfect P] {Kc : Type} [Group Kc] {m : ℕ} (hm : 3 ≤ m)
    (hmodel : LieModel Kc .PSL m 2 2) {q : P →* Kc} (hq : Function.Surjective q)
    (hqc : q.ker ≤ center P) (hqo : Odd (Nat.card q.ker)) :
    Nat.card q.ker ∣ Nat.gcd m 3 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
        ∃ ψ : Kc ≃* Matrix.ProjectiveSpecialLinearGroup (Fin m) F,
          ∃ α : SpecialLinearGroup (Fin m) F →* P, Function.Surjective α ∧
            α.ker ≤ center (SpecialLinearGroup (Fin m) F) ∧
            ∀ s, ψ (q (α s)) = (s : Matrix.ProjectiveSpecialLinearGroup (Fin m) F) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨F, _, _, hF, ⟨ψ₀⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  set ψ : Kc ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (k + 1)) F :=
    ψ₀.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL (k + 1) F).symm with hψ
  set η : P →* Matrix.ProjectiveSpecialLinearGroup (Fin (k + 1)) F := ψ.toMonoidHom.comp q
    with hη
  have hηs : Function.Surjective η := ψ.surjective.comp hq
  have hker : η.ker = q.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hηc : η.ker ≤ center P := hker ▸ hqc
  have hηo : Odd (Nat.card η.ker) := hker ▸ hqo
  obtain ⟨α, hα, hαs, -⟩ := SeitzQ2.exists_surjective_of_psl hηs hηc hηo
  have hdvd := SeitzQ2.card_ker_dvd_psl hηs hηc hηo
  rw [hker, hF4] at hdvd
  refine ⟨hdvd, F, inferInstance, inferInstance, inferInstance, hF4, ψ, α, hαs, ?_, fun s => hα s⟩
  intro s hs
  have h1 := hα s
  rw [MonoidHom.mem_ker.1 hs, map_one] at h1
  exact (QuotientGroup.eq_one_iff s).1 h1.symm

end Generic

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbourCore_field_linear_two
    (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL (n - 2) 2 2) :
    perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) =
        Kc ∧ HasBLift Kc ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        Nat.card q.ker ∣ Nat.gcd (n - 2) 3 ∧
        (∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) =
            QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
              ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩) ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
          ∃ ψ : Kc ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n - 2)) F,
            ∃ α : SpecialLinearGroup (Fin (n - 2)) F →* centralizerPerfectCore X,
              Function.Surjective α ∧ α.ker ≤ center (SpecialLinearGroup (Fin (n - 2)) F) ∧
              ∀ s, ψ (q (α s)) = (s : Matrix.ProjectiveSpecialLinearGroup (Fin (n - 2)) F) := by
  obtain ⟨-, -, -, -, hcomp, hsyl, -, -⟩ :=
    neighbour_hyps_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX htX hDe
  obtain ⟨_, -, -, hB3⟩ := hasBLift_neighbour_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX hDe
  set s := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ with hsdef
  have hs : orderOf s = 2 := orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hsD : s ∈ centralizer (((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) : Set _) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hcomp.1 hd)
  have hsC : s ∉ centralizer (Kc : Set _) := by
    intro h
    apply hτ
    have h1 : (⟨s, hsN⟩ : normalizer (Kc : Set _)) ∈ Kc.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact h
    exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
  obtain ⟨F', _, _, -, ⟨ψ'⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have hOut := isSolvable_outer_of_mulEquiv (by omega : 3 ≤ n - 2) ψ'
  have hcore := perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKc hDK hs hsD hsN hsC hsyl hOut
  have hB : HasBLift Kc := (hB3 Kc hKc hsN hsC).1
  obtain ⟨q, hqs, hqc, hqo, hqapp⟩ := exists_surjective_neighbourCore_of_perfectCore_eq hcore hB
  have : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (CFSG.Quasithin.perfectCore_perfect _)
  obtain ⟨hdvd, F, hF1, hF2, hF3, hF4, ψ, α, hαs, hαc, hα⟩ :=
    exists_surjective_specialLinear_of_lieModel_four (by omega) hmodel hqs hqc hqo
  exact ⟨hcore, hB, q, hqs, hqc, hqo, hdvd, hqapp, F, hF1, hF2, hF3, hF4, ψ, α, hαs, hαc, hα⟩

theorem nonempty_map_oddCore_mulEquiv_specialLinear_two {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    center (SpecialLinearGroup (Fin (n - 2)) K) = ⊥ ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ ∧
      Nonempty (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) ≃*
          SpecialLinearGroup (Fin (n - 2)) K) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  obtain ⟨-, -, -, -, -, hDC, hDq', ⟨φ⟩, -, -⟩ :=
    neighbour_data_torusQ1 e hn hab htC hX₀ hX₀c hX hDe
  have hDX : D ≤ centralizer (X : Set G) := hDC.trans inf_le_left
  have hSL : center (SpecialLinearGroup (Fin (n - 2)) K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).2 (eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz)
  have hZD : center D = ⊥ := F4Pilot.center_eq_bot_congr φ.symm hSL
  let eDD : D.subgroupOf (centralizer (X : Set G)) ≃* D := subgroupOfEquivOfLe hDX
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf (centralizer (X : Set G))) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv eDD.symm hDq'
  have hD'Z : center (D.subgroupOf (centralizer (X : Set G))) = ⊥ :=
    F4Pilot.center_eq_bot_congr eDD.symm hZD
  let eDb := F4Pilot.mapMkEquivOfInfEqBot (oddCore (centralizer (X : Set G)))
    (D.subgroupOf (centralizer (X : Set G))) (F4Pilot.inf_oddCore_eq_bot hD'q hD'Z)
  exact ⟨hSL, F4Pilot.center_eq_bot_congr eDb hD'Z, ⟨eDb.symm.trans (eDD.trans φ)⟩⟩

theorem neighbourCore_swap_linear_two
    (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hiso : Nonempty (Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    HasBLift Kc ∧ HasBLift (Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk'
        (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) ∧
      (oddCoreLift Kc).map (MulAut.conj (⟨t, htX⟩ : centralizer (X : Set G))).toMonoidHom ≤
        centralizer (oddCoreLift Kc : Set (centralizer (X : Set G))) ∧
      oddCoreLift Kc ⊓
          (oddCoreLift Kc).map (MulAut.conj (⟨t, htX⟩ : centralizer (X : Set G))).toMonoidHom =
        ⊥ ∧
      oddCoreLift Kc ⊔
          (oddCoreLift Kc).map (MulAut.conj (⟨t, htX⟩ : centralizer (X : Set G))).toMonoidHom =
        perfectCore (⊤ : Subgroup (centralizer (X : Set G))) ∧
      oddCoreLift Kc ⊓ oddCore (centralizer (X : Set G)) = ⊥ ∧
      (oddCoreLift Kc).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = Kc ∧
      Nonempty (oddCoreLift Kc ≃* Kc) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  obtain ⟨-, -, -, -, hlayer, -, -, -, -, -⟩ :=
    neighbour_data_torusQ1 e hn hab htC hX₀ hX₀c hX hDe
  obtain ⟨-, -, hDq, -, hcomp, hsyl, -, -⟩ :=
    neighbour_hyps_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX htX hDe
  obtain ⟨_, hXodd, -, -⟩ := hasBLift_neighbour_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX hDe
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hKp : ⁅Kc, Kc⁆ = Kc := isPerfect_iff.mp hKc.1.1
  obtain ⟨hBsup, hBK⟩ :=
    hasBLift_sup_conj_of_forall_odd_mem htC ht hLt htX hlayer hDq hXodd hKp hcomm
  obtain ⟨hSL, -, ⟨eD⟩⟩ :=
    nonempty_map_oddCore_mulEquiv_specialLinear_two hK e hn htC hab hX₀ hX₀c hX hDe
  obtain ⟨ψ⟩ := hiso
  set eK : Kc ≃* SpecialLinearGroup (Fin (n - 2)) K := ψ.trans eD with heK
  let eP : SpecialLinearGroup (Fin (n - 2)) K ≃* LinearFlag.projectiveSL (n - 2) K :=
    ((QuotientGroup.quotientMulEquivOfEq hSL).trans QuotientGroup.quotientBot).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n - 2) K)
  have hOut : Group.IsSolvable (Outer Kc) :=
    isSolvable_outer_of_mulEquiv (by omega : 3 ≤ n - 2) (eK.trans eP)
  have hSchur : OddSchurTrivial Kc :=
    (SeitzQ2.oddSchurTrivial_specialLinearGroup (n - 3) K).of_mulEquiv
      ((reindexSpecialLinear (finCongr (show n - 3 + 1 = n - 2 by omega))).trans eK.symm)
  have htt : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← ht, pow_orderOf_eq_one]; rfl)
  have hsD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) : Set _) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hcomp.1 hd)
  have hdata : F4Pilot.SwapComponentData
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) Kc
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
    ⟨by rw [← map_mul, htt, map_one], hKc, hne, hcomm, hDKK, hsD, hsyl⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    UnitaryPilot.swapLift_decomposition_of_hasBLift hdata hOut hBK hBsup
  set π := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) with hπ
  have : Group.IsPerfect (oddCoreLift Kc) := isPerfect_iff.mpr h4
  have hmem : ∀ x : oddCoreLift Kc, π x ∈ Kc := fun x => h5.le (mem_map_of_mem π x.2)
  set η : oddCoreLift Kc →* Kc := (π.comp (oddCoreLift Kc).subtype).codRestrict Kc hmem with hη
  have hηs : Function.Surjective η := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hx, rfl⟩ := h5.ge hk
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : oddCoreLift Kc, x ∈ η.ker → (x : centralizer (X : Set G)) ∈
      oddCore (centralizer (X : Set G)) := by
    intro x hx
    have h1 : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hηc : η.ker ≤ center (oddCoreLift Kc) := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.1 (hBK y.2) _ (hker x hx)).symm
  have hηo : Odd (Nat.card η.ker) := by
    have hcard : Nat.card η.ker = Nat.card (η.ker.map (oddCoreLift Kc).subtype) :=
      (Subgroup.card_map_of_injective (oddCoreLift Kc).subtype_injective).symm
    have hle : η.ker.map (oddCoreLift Kc).subtype ≤ oddCore (centralizer (X : Set G)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker x hx
    rw [hcard]
    exact Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_le hle)
  have hηi : Function.Injective η :=
    hSchur (oddCoreLift Kc) inferInstance η hηs hηc hηo
  have hO : oddCoreLift Kc ⊓ oddCore (centralizer (X : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxO⟩
    have h1 : η ⟨x, hx⟩ = 1 := by
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff x).2 hxO
    have h2 : (⟨x, hx⟩ : oddCoreLift Kc) = 1 := hηi (by rw [h1, map_one])
    exact (mem_bot).2 (congrArg Subtype.val h2)
  refine ⟨hBK, hBsup, h1, ?_, h3, hO, h5, ⟨MulEquiv.ofBijective η ⟨hηi, hηs⟩⟩⟩
  rw [eq_bot_iff, ← hO]
  exact le_inf inf_le_left h2

end Seitz

end CFSG.SeitzReduction.LinearPilot
