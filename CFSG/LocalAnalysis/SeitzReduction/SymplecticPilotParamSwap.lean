module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapNormalize

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial swapDiagHom oddCoreLift)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section Generic

variable {G : Type*} [Group G] {t : G}

theorem map_subtype_map_conj_eq {H : Subgroup G} (A : Subgroup H) (h : H) :
    (A.map (MulAut.conj h).toMonoidHom).map H.subtype =
      (A.map H.subtype).map (MulAut.conj (h : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_le_centralizer_map_of_le {A B : Type*} [Group A] [Group B] (φ : A →* B)
    {Y D : Subgroup A} (h : Y ≤ centralizer (D : Set A)) :
    Y.map φ ≤ centralizer ((D.map φ : Subgroup B) : Set B) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (h hy) d hd]

theorem exists_swapParam_of_decomposition {D : Type*} [Group D] (htt : t * t = 1)
    {Kc E : Subgroup G} (hcomm : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G))
    (hdisj : Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥)
    (hE : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = E) (ε : D →* G) (hε : Function.Injective ε)
    (hfix : E ⊓ centralizer ({t} : Set G) = ε.range) :
    ∃ Ψ : D × D →* G, Function.Injective Ψ ∧ Ψ.range = E ∧ (∀ x, Ψ (x, x) = ε x) ∧
      ∀ x y, t * Ψ (x, y) * t⁻¹ = Ψ (y, x) := by
  have hδrange : (swapDiagHom hcomm).range = ε.range := by
    rw [F4Pilot.range_swapDiagHom hcomm htt hdisj, hE, hfix]
  have hδinj := F4Pilot.swapDiagHom_injective hcomm hdisj
  obtain ⟨lam, hlam⟩ : ∃ lam : D ≃* Kc, ∀ x, swapDiagHom hcomm (lam x) = ε x := by
    refine ⟨(MonoidHom.ofInjective hε).trans ((MulEquiv.subgroupCongr hδrange.symm).trans
      (MonoidHom.ofInjective hδinj).symm), fun x => ?_⟩
    have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hδinj).apply_symm_apply
      ((MulEquiv.subgroupCongr hδrange.symm) (MonoidHom.ofInjective hε x)))
    rw [MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply] at h1
    exact h1
  have hc : ∀ x y : D, Commute ((Kc.subtype.comp lam.toMonoidHom) x)
      (((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)) y) := fun x y =>
    F4Pilot.commute_of_map_conj_le_centralizer hcomm _ (lam x).2 _ ⟨_, (lam y).2, rfl⟩
  set Φ₀ := (Kc.subtype.comp lam.toMonoidHom).noncommCoprod
    ((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)) hc with hΦ₀
  have hΦ₀apply : ∀ x y, Φ₀ (x, y) = (lam x : G) * (t * (lam y : G) * t⁻¹) := fun x y => rfl
  have hrange1 : (Kc.subtype.comp lam.toMonoidHom).range = Kc := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 lam.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have hrange2 : ((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)).range =
      Kc.map (MulAut.conj t).toMonoidHom := by
    rw [MonoidHom.range_comp, hrange1]
  have hinj : Function.Injective Φ₀ := by
    rw [hΦ₀, MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.val_injective.comp lam.injective,
      (MulAut.conj t).injective.comp (Subtype.val_injective.comp lam.injective), ?_⟩
    rw [hrange1, hrange2]
    exact disjoint_iff.2 hdisj
  have hrange : Φ₀.range = E := by
    rw [hΦ₀, MonoidHom.noncommCoprod_range, hrange1, hrange2, hE]
  refine ⟨Φ₀, hinj, hrange, fun x => ?_, fun x y => ?_⟩
  · rw [hΦ₀apply, ← hlam, F4Pilot.swapDiagHom_apply]
  · rw [hΦ₀apply, hΦ₀apply]
    have hcy : (lam y : G) * (t * (lam x : G) * t⁻¹) = t * (lam x : G) * t⁻¹ * (lam y : G) :=
      F4Pilot.commute_of_map_conj_le_centralizer hcomm _ (lam y).2 _ ⟨_, (lam x).2, rfl⟩
    calc t * ((lam x : G) * (t * (lam y : G) * t⁻¹)) * t⁻¹ =
        (t * (lam x : G) * t⁻¹) * ((t * t) * (lam y : G) * (t * t)⁻¹) := by group
      _ = (lam y : G) * (t * (lam x : G) * t⁻¹) := by rw [htt, hcy]; group

end Generic

section RootTorus


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_swapDecomposition_rootTorusSp {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (h : RootKindSp e t f k .swap) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e k ∧
      neighbourCore e k ⊓ centralizer ({t} : Set G) = modelToG e (complSp K k) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set X : Subgroup G := modelToG e (rootTorusSp K k) with hXdef
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
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_rootTorusSp_of_seitzSetting hset hKc hq hm e htC ht k
    (X := X) rfl htX (D := D) rfl
  obtain ⟨-, -, -, -, -, -, hDXt, hDq, ⟨ψD⟩, hDZ, -⟩ :=
    neighbour_data_rootTorusSp hq hm e k htC (X := X) rfl (D := D) rfl
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
  obtain ⟨-, hC, -⟩ := bLift_neighbour_rootTorusSp_of_seitzSetting hset hKc hq hm e htC ht k
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
    have : Group.IsSolvable (Outer (StatedSp m K)) := isSolvable_outer_statedSp hm
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
      ((oddCoreLift Kb).map H.subtype).map (MulAut.conj t).toMonoidHom = neighbourCore e k := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  refine ⟨(oddCoreLift Kb).map H.subtype, hc1, hd1, he1, ?_⟩
  have hDE : D ≤ neighbourCore e k := modelToG_complSp_le_neighbourCore e hq (by omega) k
  have hrange := F4Pilot.range_swapDiagHom hc1 htt hd1
  rw [he1] at hrange
  have hinj := F4Pilot.swapDiagHom_injective hc1 hd1
  have hcard : Nat.card (neighbourCore e k ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      Nat.card D := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      card_map_of_injective H.subtype_injective, hcardH,
      Nat.card_congr ((eKD.trans eDb.symm).trans (subgroupOfEquivOfLe hDH)).toEquiv]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm

theorem nonempty_swapNeighbourParam_of_rootKindSp {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (h : RootKindSp e t f k .swap) : Nonempty (SwapNeighbourParam e t k) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨Kc, hc, hd, hE, hfix⟩ := exists_swapDecomposition_rootTorusSp hset hKc hf hm e htC ht k h
  let ε : spBlock K ({k}ᶜ : Finset (Fin (m + 1))) →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp (spBlock K ({k}ᶜ : Finset (Fin (m + 1)))).subtype)
  have hε : Function.Injective ε :=
    L.subtype_injective.comp (e.symm.injective.comp Subtype.val_injective)
  have hεrange : ε.range = modelToG e (complSp K k) := by
    rw [← spBlock_compl_singleton, MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
    rfl
  obtain ⟨Ψ, hinj, hrange, hdiag, hswap⟩ :=
    exists_swapParam_of_decomposition htt hc hd hE ε hε (hfix.trans hεrange.symm)
  refine ⟨SwapNeighbourParam.ofNormalized Ψ hrange ?_ hdiag hswap⟩
  rw [(MonoidHom.ker_eq_bot_iff Ψ).2 hinj]
  exact bot_le

end RootTorus

end CFSG.SeitzReduction.SymplecticPilot
