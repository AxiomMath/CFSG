module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFourParam
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift oddCoreLift SwapComponentData)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

theorem proj_torusDiagSL_mem_centralizer_levTorus {n : ℕ} {K : Type*} [Field K] (a : Fin n)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    LinearFlag.proj n K (torusDiagSL c) ∈
      centralizer (levTorus (K := K) a : Set (LinearFlag.projectiveSL n K)) := by
  refine mem_centralizer_iff.2 fun x hx => ?_
  obtain ⟨κ, rfl⟩ := hx
  rw [MonoidHom.comp_apply, levTorusHom_eq_torusDiagSL, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul]
  exact congrArg (fun z => LinearFlag.proj n K (torusDiagSL z)) (mul_comm _ _)

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_swapNeighbourParam_levTorus_of_swapRow_of_split (hset : SeitzSetting G L)
    {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (a : Fin 4)
    (hsplit : OddCentralSplit (blockSpecialLinear (K := K) (({a} : Finset (Fin 4))ᶜ)))
    (hrow : NeighbourSwapRow e t (.levi a)) :
    Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) a))
      (({a} : Finset (Fin 4))ᶜ)) := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  show Nonempty (SwapNeighbourParam e t (modelToG e ((Neighbour.levi a : Neighbour 4).torus K))
    (Neighbour.levi a : Neighbour 4).index)
  obtain ⟨htX, Kc, hKc', hDKK, hne, hcomm, hZK, ⟨eKD⟩⟩ := hrow
  set X := modelToG e ((Neighbour.levi a : Neighbour 4).torus K) with hXdef
  set H := centralizer (X : Set G) with hHdef
  set N : Finset (Fin 4) := (Neighbour.levi a : Neighbour 4).index with hNdef
  set D := modelToG e (blockSL (K := K) N) with hDdef
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set τ := π t' with hτ
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hN3 : 3 ≤ N.card := by
    rw [hNdef, Neighbour.index_levi, Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  have hN4 : N.card < 4 := by
    rw [hNdef, Neighbour.index_levi, Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
    omega
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_levTorus_of_seitzSetting (X := X) (D := D) hset
    hKc e htC ht a rfl htX rfl
  obtain ⟨c₀, hc₀⟩ := exists_pow_four_ne_one hq
  obtain ⟨-, -, -, -, -, hDC, -, -, -, -⟩ :=
    neighbour_data_levTorus (X := X) (D := D) e le_rfl a ⟨c₀, hc₀⟩ htC rfl rfl
  have hDH : D ≤ H := hDC.trans inf_le_left
  have hDt : D ≤ centralizer ({t} : Set G) := hDC.trans inf_le_right
  have hτD : τ ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData τ Kc Db :=
    ⟨by rw [hτ, ← map_mul, ht't', map_one], hKc', hne, hcomm, hDKK, hτD, hsyl⟩
  have hDbne : Db ≠ ⊥ := CFSG.SeitzReduction.ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨-, -, hBl⟩ := bLift_neighbour_levTorus_of_seitzSetting (X := X) (D := D) hset hKc e htC
    ht a rfl htX rfl
  have hKp : ⁅Kc, Kc⁆ = Kc := Subgroup.isPerfect_iff.mp hKc'.1.1
  have hKτp : ⁅Kc.map (MulAut.conj τ).toMonoidHom, Kc.map (MulAut.conj τ).toMonoidHom⁆ =
      Kc.map (MulAut.conj τ).toMonoidHom := by
    rw [← map_commutator, hKp]
  have hτ2 : τ ^ 2 = 1 := by
    rw [sq]
    exact hdata.mul_self
  have hBsup : HasBLift (Kc ⊔ Kc.map (MulAut.conj τ).toMonoidHom) :=
    hBl _ (F4Pilot.commutator_sup_eq_sup_of_perfect hKp hKτp) (mem_normalizer_sup_map_conj hτ2 Kc)
      (F4Pilot.sup_conj_le_commutator_zpowers hKp hcomm)
  have hBK : HasBLift Kc := F4Pilot.HasBLift.mono le_sup_left hBsup
  have hZDb : center Db = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw' : eKD.symm w ∈ center Kc := by
      rw [mem_center_iff] at hw ⊢
      intro z
      apply eKD.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hw]
    rw [hZK, mem_bot] at hw'
    rw [mem_bot, ← eKD.apply_symm_apply w, hw', map_one]
  have hcardN : Fintype.card ((Neighbour.levi a : Neighbour 4).index) = 3 := by
    rw [Fintype.card_coe, Neighbour.index_levi, Finset.card_compl, Fintype.card_fin,
      Finset.card_singleton]
  obtain ⟨ε, hεinj, hεrange, -⟩ := exists_projectiveSL_embedding e (.levi a)
    (Fintype.equivFinOfCardEq hcardN) le_rfl hDbne hZDb le_rfl
  have hεsurj : Function.Surjective ε := by
    intro w
    have hw : w ∈ ε.range := by
      rw [hεrange]
      exact mem_subgroupOf.2 w.2
    exact hw
  have hOut : Group.IsSolvable (Outer Kc) :=
    isSolvable_outer_of_mulEquiv le_rfl
      (eKD.trans (MulEquiv.ofBijective ε ⟨hεinj, hεsurj⟩).symm)
  obtain ⟨hcH, hdH, hsH, -, -⟩ :=
    UnitaryPilot.swapLift_decomposition_of_hasBLift hdata hOut hBK hBsup
  have hodd : Odd (Nat.card (oddCoreLift Kc ⊓ (oddCoreLift Kc).map (MulAut.conj t').toMonoidHom :
      Subgroup H)) :=
    (CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := H)).of_dvd_nat
      (Subgroup.card_dvd_of_le hdH)
  have hSperf : Group.IsPerfect (blockSpecialLinear (K := K) N) :=
    Subgroup.isPerfect_iff.2 (commutator_blockSpecialLinear_eq_of_three_le hN3)
  let ιG : blockSpecialLinear (K := K) N →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj 4 K).comp
      (blockSpecialLinear (K := K) N).subtype))
  have hιD : ∀ x : blockSpecialLinear (K := K) N, ιG x ∈ D := fun x =>
    symm_mem_modelToG e (proj_mem_blockSL x.2)
  let ι : blockSpecialLinear (K := K) N →* H := ιG.codRestrict H fun x => hDH (hιD x)
  have hιinj : ∀ x, ι x = 1 → x = 1 := by
    intro x hx
    have h0 : ((ι x : H) : G) = 1 := congrArg Subtype.val hx
    have h1 : e.symm (LinearFlag.proj 4 K x) = 1 := Subtype.ext h0
    have h2 : LinearFlag.proj 4 K x = 1 := by
      rw [← map_one e.symm] at h1
      exact e.symm.injective h1
    exact Subtype.ext (eq_one_of_mem_blockSpecialLinear_of_proj_eq_one hN4 x.2 h2)
  have hPmap : (perfectCore (⊤ : Subgroup H)).map H.subtype = centralizerPerfectCore X := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hDE : D ≤ centralizerPerfectCore X :=
    modelToG_blockSL_index_le_neighbourCore e (.levi a) (commutator_blockSL_eq_of_three_le hN3)
  have hιK : ∀ x, ι x ∈ oddCoreLift Kc ⊔ (oddCoreLift Kc).map (MulAut.conj t').toMonoidHom := by
    intro x
    rw [hsH]
    have h1 : (ι x : G) ∈ (perfectCore (⊤ : Subgroup H)).map H.subtype := hPmap ▸ hDE (hιD x)
    obtain ⟨w, hw, hwx⟩ := h1
    rwa [show w = ι x from Subtype.ext hwx] at hw
  have hιt : ∀ x, t' * ι x * t'⁻¹ = ι x := fun x => Subtype.ext (by
    change t * ιG x * t⁻¹ = ιG x
    rw [← mem_centralizer_iff.1 htC (ιG x) (e.symm _).2, mul_inv_cancel_right])
  have hιrange : ι.range = D.subgroupOf H := by
    ext ⟨w, hw⟩
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨x, hx⟩
      rw [← congrArg Subtype.val hx]
      exact hιD x
    · intro hwD
      obtain ⟨z, hz, rfl⟩ := (mem_modelToG e).1 hwD
      obtain ⟨A, hA, rfl⟩ := mem_blockSL.1 hz
      exact ⟨⟨A, hA⟩, Subtype.ext rfl⟩
  have hsplit' : OddCentralSplit (blockSpecialLinear (K := K) N) := hsplit
  obtain ⟨φ, hφK, hφ⟩ := UnitaryPilot.exists_swapLift hcH ht't' hsplit' hodd ι hιK hιt
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply hιinj
    rw [← hφ x, hx, mul_one, mul_inv_cancel, mul_one]
  have hφrange : φ.range = oddCoreLift Kc :=
    UnitaryPilot.range_eq_oddCoreLift_of_swapLift hdata hBK (Nat.card_congr eKD.toEquiv) hφK hφ
      (by rw [hιrange])
  refine ⟨{ Ψ := H.subtype.comp (UnitaryPilot.swapParamHom hcH hφK)
            range_eq := ?_
            ker_le := ?_
            diag := fun x => congrArg Subtype.val (hφ x)
            N2 := ?_
            swap := fun x y =>
              congrArg Subtype.val (UnitaryPilot.conj_swapParamHom hcH hφK ht't' x y) }⟩
  · rw [MonoidHom.range_comp, UnitaryPilot.range_swapParamHom, hφrange, hsH, hPmap]
  · intro x hx
    exact UnitaryPilot.ker_swapParamHom_le_center hcH hφK ht't' hφinj (Subtype.ext hx)
  ·
    intro c x y
    have hgX : ((e.symm (LinearFlag.proj 4 K (torusDiagSL c)) : L) : G) ∈ H :=
      modelToG_le_centralizer e (le_refl (centralizer (levTorus (K := K) a :
        Set (LinearFlag.projectiveSL 4 K))))
        (symm_mem_modelToG e (proj_torusDiagSL_mem_centralizer_levTorus a c))
    set g' : H := ⟨_, hgX⟩ with hg'def
    have hg't : g' * t' = t' * g' := Subtype.ext (mem_centralizer_iff.1 htC _ (e.symm _).2)
    have hr : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units]
      exact odd_natCard_sub_one
    have hgr : g' ^ Nat.card Kˣ = 1 := Subtype.ext (by
      change ((e.symm (LinearFlag.proj 4 K (torusDiagSL c)) : L) : G) ^ Nat.card Kˣ = 1
      rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, ← map_pow,
        pow_card_units_eq_one_blockTorusParam c, map_one, map_one, map_one,
        OneMemClass.coe_one])
    obtain ⟨σs, hσs⟩ := hdata.exists_sign
    have hσ1 : σs (π g') = 1 := UnitaryPilot.eq_one_of_pow_eq_one_of_odd hr
      (by rw [← map_pow, ← map_pow, hgr, map_one, map_one])
    have hg'N : g' ∈ normalizer (oddCoreLift Kc : Set H) :=
      F4Pilot.mem_normalizer_oddCoreLift Kc (hσs _ hσ1)
    have hα : ∀ z, ι ((conjDiag (RingHom.id K) N c).toMonoidHom z) = g' * ι z * g'⁻¹ := fun z =>
      Subtype.ext (by
        change ((e.symm (LinearFlag.proj 4 K ((conjDiag (RingHom.id K) N c z :
          blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin 4) K)) : L) : G) = _
        rw [coe_conjDiag_id_apply, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
        rfl)
    have hφα := UnitaryPilot.swapLift_comp_eq_conj hcH hφK hφ hg'N hg't
      (conjDiag (RingHom.id K) N c).toMonoidHom hα
    have e1 : g'⁻¹ * t' * g' = t' := by
      rw [mul_assoc, ← hg't, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : g'⁻¹ * t'⁻¹ = t'⁻¹ * g'⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hg't]
    have key : UnitaryPilot.swapParamHom hcH hφK
        (conjDiag (RingHom.id K) N c x, conjDiag (RingHom.id K) N c y) =
          g' * UnitaryPilot.swapParamHom hcH hφK (x, y) * g'⁻¹ := by
      rw [UnitaryPilot.swapParamHom_apply, UnitaryPilot.swapParamHom_apply]
      change φ ((conjDiag (RingHom.id K) N c).toMonoidHom x) *
        (t' * φ ((conjDiag (RingHom.id K) N c).toMonoidHom y) * t'⁻¹) = _
      rw [hφα, hφα]
      calc g' * φ x * g'⁻¹ * (t' * (g' * φ y * g'⁻¹) * t'⁻¹)
          = g' * φ x * (g'⁻¹ * t' * g') * φ y * (g'⁻¹ * t'⁻¹) := by group
        _ = g' * φ x * t' * φ y * (t'⁻¹ * g'⁻¹) := by rw [e1, e2]
        _ = g' * (φ x * (t' * φ y * t'⁻¹)) * g'⁻¹ := by group
    exact congrArg Subtype.val key

theorem nonempty_swapNeighbourParam_levTorus_of_swapRow
    (hset : SeitzSetting G L)
    {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (a : Fin 4) (hrow : NeighbourSwapRow e t (.levi a)) :
    Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) a))
      (({a} : Finset (Fin 4))ᶜ)) := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hNne : (({a} : Finset (Fin 4))ᶜ).Nonempty := Finset.card_pos.1 (by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
    omega)
  exact nonempty_swapNeighbourParam_levTorus_of_swapRow_of_split hset hKc hf e htC ht a
    (oddCentralSplit_blockSpecialLinear hNne) hrow

end Swap

end CFSG.SeitzReduction.LinearPilot
