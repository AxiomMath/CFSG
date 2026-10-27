module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Rows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamSwap
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial oddCoreLift)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_swapDecomposition_nsTorusSp {m : ℕ} (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (h : NsKindSp e t k .swap) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (modelToG e (nsTorusSp K k)) ∧
      centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓ centralizer ({t} : Set G) =
        modelToG e (complSp K k) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set X : Subgroup G := modelToG e (nsTorusSp K k) with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := modelToG e (complSp K k) with hDdef
  obtain ⟨htX, Kb, hKb, hDK, hcase⟩ := h
  have hswap : Kb.map (MulAut.conj (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩)).toMonoidHom ≠ Kb ∧
      ⁅Kb, Kb.map (MulAut.conj (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      Nonempty (Kb ⧸ center Kb ≃*
        ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) : Subgroup (H ⧸ oddCore H))) := by
    rcases hcase with ⟨hκ, -⟩ | ⟨-, h⟩
    · exact absurd rfl hκ
    · exact h
  obtain ⟨hne, hcomm, ⟨eK⟩⟩ := hswap
  have ht't' : (⟨t, htX⟩ : H) * ⟨t, htX⟩ = 1 := Subtype.ext htt
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nsTorusSp_of_seitzSetting hset hK hm e htC ht k
    (X := X) rfl htX (D := D) rfl
  obtain ⟨-, -, -, -, -, -, hDXt, hDq, ⟨ψD⟩, hDZ, -⟩ :=
    neighbour_data_nsTorusSp hK hm e k htC (X := X) rfl (D := D) rfl
  have hDH : D ≤ H := hDXt.trans inf_le_left
  have hDt : D ≤ centralizer ({t} : Set G) := hDXt.trans inf_le_right
  have hτD : QuotientGroup.mk' (oddCore H) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :
        Subgroup (H ⧸ oddCore H)) : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : F4Pilot.SwapComponentData (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩) Kb
      ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) :=
    ⟨by rw [← map_mul, ht't', map_one], hKb, hne, hcomm, hDK, hτD, hsyl⟩
  have hO := F4Pilot.oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  obtain ⟨-, hC, -⟩ := bLift_neighbour_nsTorusSp_of_seitzSetting hset hK hm e htC ht k
    (X := X) rfl htX (D := D) rfl
  have hZ : center Kb = ⊥ := hdata.center_eq_bot hO
  let eKD : Kb ≃* (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eK
  let eD' : StatedSp m K ≃* D.subgroupOf H := ψD.symm.trans (subgroupOfEquivOfLe hDH).symm
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv (subgroupOfEquivOfLe hDH).symm hDq
  have hD'Z : center (D.subgroupOf H) = ⊥ :=
    F4Pilot.center_eq_bot_congr (subgroupOfEquivOfLe hDH).symm hDZ
  let eDb : D.subgroupOf H ≃* (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :=
    F4Pilot.mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H)
      (F4Pilot.inf_oddCore_eq_bot hD'q hD'Z)
  let eKC : Kb ≃* StatedSp m K := eKD.trans (eDb.symm.trans eD'.symm)
  have hOut : Group.IsSolvable (Outer Kb) := by
    have : Group.IsSolvable (Outer (StatedSp m K)) := isSolvable_outer_statedSp (by omega)
    exact solvable_of_equiv eKC.symm
  have hSchur : OddSchurTrivial Kb := (F4Pilot.oddSchurTrivial_statedSp m K).of_mulEquiv eKC.symm
  obtain ⟨hcH, hdH, hsH, -, -, hcardH⟩ :=
    F4Pilot.swapLift_decomposition ht't' hC hdata hOut hSchur
  have hKct : ((oddCoreLift Kb).map H.subtype).map (MulAut.conj t).toMonoidHom =
      ((oddCoreLift Kb).map (MulAut.conj (⟨t, htX⟩ : H)).toMonoidHom).map H.subtype :=
    (map_subtype_map_conj_eq (oddCoreLift Kb) ⟨t, htX⟩).symm
  have hc1 : ((oddCoreLift Kb).map H.subtype).map (MulAut.conj t).toMonoidHom ≤
      centralizer (((oddCoreLift Kb).map H.subtype : Subgroup G) : Set G) := by
    rw [hKct]
    exact map_le_centralizer_map_of_le H.subtype hcH
  have hd1 : (oddCoreLift Kb).map H.subtype ⊓
      ((oddCoreLift Kb).map H.subtype).map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hKct, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hdH, Subgroup.map_bot]
  have he1 : (oddCoreLift Kb).map H.subtype ⊔
      ((oddCoreLift Kb).map H.subtype).map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore X := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  refine ⟨(oddCoreLift Kb).map H.subtype, hc1, hd1, he1, ?_⟩
  have hDperf : ⁅D, D⁆ = D := by
    have : Group.IsPerfect D := ⟨hDq.1⟩
    exact isPerfect_iff.mp this
  have hDE : D ≤ centralizerPerfectCore X := CFSG.Quasithin.le_perfectCore_of_perfect hDH hDperf
  have hrange := F4Pilot.range_swapDiagHom hc1 htt hd1
  rw [he1] at hrange
  have hinj := F4Pilot.swapDiagHom_injective hc1 hd1
  have hcard : Nat.card (centralizerPerfectCore X ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      Nat.card D := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      card_map_of_injective H.subtype_injective, hcardH,
      Nat.card_congr ((eKD.trans eDb.symm).trans (subgroupOfEquivOfLe hDH)).toEquiv]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm

theorem exists_swapParam_nsTorusSp {m : ℕ} (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) (h : NsKindSp e t k .swap) :
    ∃ P : SwapParam t (modelToG e (complSp K k)), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨Kc, hc, hd, hE, hfix⟩ := exists_swapDecomposition_nsTorusSp hset hK hm e htC ht k h
  exact E8Pilot.exists_swapParam_of_decomposition htt hc hd hE hfix

end CFSG.SeitzReduction.SymplecticPilot
