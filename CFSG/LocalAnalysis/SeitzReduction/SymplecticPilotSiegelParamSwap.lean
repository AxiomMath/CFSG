module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamField
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift oddCoreLift SwapComponentData)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit modelToG symm_mem_modelToG)

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

omit [Finite G] in
theorem symm_diagSp_mem_centralizer_siegelTorus (e : L ≃* StatedSp n K) (c : Fin n → Kˣ) :
    ((e.symm (diagSp K n c) : L) : G) ∈ centralizer (modelToG e (siegelTorus K n) : Set G) :=
  LinearPilot.map_symm_le_centralizer_map_symm e
    (A := siegelTorus K n) (B := diagTorusSp K ⊤)
    (by
      rintro _ ⟨c', -, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      change diagSp K n (fun _ => s) * diagSp K n c' = diagSp K n c' * diagSp K n (fun _ => s)
      rw [← map_mul, ← map_mul, mul_comm])
    (symm_mem_modelToG e ⟨c, mem_top c, rfl⟩)

theorem exists_siegelSwapParam_aux (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hsplit : OddCentralSplit (siegelLevi K n)) {X D : Subgroup G}
    (hX : X = modelToG e (siegelTorus K n)) (hD : D = modelToG e (siegelLevi K n))
    (htX : t ∈ centralizer (X : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc' : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hZK : center Kc = ⊥)
    (eKD : Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :
    ∃ Ψ : siegelLevi K n × siegelLevi K n →* G, Ψ.range = centralizerPerfectCore X ∧
      Ψ.ker ≤ center (siegelLevi K n × siegelLevi K n) ∧
      (∀ x : siegelLevi K n, Ψ (x, x) = ((e.symm x : L) : G)) ∧
      (∀ (s : Fin n → Kˣ) (x : siegelLevi K n × siegelLevi K n),
        Ψ (conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi s x.1,
          conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi s x.2) =
          ((e.symm (diagSp K n s) : L) : G) * Ψ x * ((e.symm (diagSp K n s) : L) : G)⁻¹) ∧
      (∀ x y : siegelLevi K n, t * Ψ (x, y) * t⁻¹ = Ψ (y, x)) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  subst hX hD
  set π := QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))) with hπ
  set Db := ((modelToG e (siegelLevi K n)).subgroupOf
    (centralizer (modelToG e (siegelTorus K n) : Set G))).map π with hDbdef
  set t' : centralizer (modelToG e (siegelTorus K n) : Set G) := ⟨t, htX⟩ with ht'def
  set τ := π t' with hτ
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht't' : t' * t' = 1 := Subtype.ext htt
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_siegelTorus_of_seitzSetting
    (X := modelToG e (siegelTorus K n)) (D := modelToG e (siegelLevi K n))
    hset hKc hq hn e htC ht rfl htX rfl
  obtain ⟨-, -, -, -, hDC, -, -, -, -⟩ := neighbour_data_siegelTorus hq hn e htC rfl rfl
  have hDH : modelToG e (siegelLevi K n) ≤ centralizer (modelToG e (siegelTorus K n) : Set G) :=
    hDC.trans inf_le_left
  have hDt : modelToG e (siegelLevi K n) ≤ centralizer ({t} : Set G) := hDC.trans inf_le_right
  have hτD : τ ∈ centralizer (Db : Set _) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData τ Kc Db :=
    ⟨by rw [hτ, ← map_mul, ht't', map_one], hKc', hne, hcomm, hDKK, hτD, hsyl⟩
  have hDbne : Db ≠ ⊥ := CFSG.SeitzReduction.ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨-, -, hBl⟩ := bLift_neighbour_siegelTorus_of_seitzSetting
    (X := modelToG e (siegelTorus K n)) (D := modelToG e (siegelLevi K n)) hset hKc
    hq hn e htC ht rfl htX rfl
  have hKp : ⁅Kc, Kc⁆ = Kc := Subgroup.isPerfect_iff.mp hKc'.1.1
  have hKτp : ⁅Kc.map (MulAut.conj τ).toMonoidHom, Kc.map (MulAut.conj τ).toMonoidHom⁆ =
      Kc.map (MulAut.conj τ).toMonoidHom := by
    rw [← map_commutator, hKp]
  have hτ2 : τ ^ 2 = 1 := by
    rw [sq]
    exact hdata.mul_self
  have hBsup : HasBLift (Kc ⊔ Kc.map (MulAut.conj τ).toMonoidHom) :=
    hBl _ (F4Pilot.commutator_sup_eq_sup_of_perfect hKp hKτp)
      (LinearPilot.mem_normalizer_sup_map_conj hτ2 Kc)
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
  have hrangeB : (siegelBarHom e).range = Db := by
    rw [range_siegelBarHom]
  obtain ⟨ε, hεinj, hεrange, -⟩ := exists_projectiveSL_embedding_of_hom (Kc := Db) hn
    (siegelBarHom e) (by rw [hrangeB]; exact hDbne) (by rw [hrangeB]; exact hZDb)
    hrangeB.le
  have hεsurj : Function.Surjective ε := by
    intro w
    have hw : w ∈ ε.range := by
      rw [hεrange, hrangeB]
      exact mem_subgroupOf.2 w.2
    exact hw
  have hOut : Group.IsSolvable (Outer Kc) :=
    LinearPilot.isSolvable_outer_of_mulEquiv hn
      (eKD.trans (MulEquiv.ofBijective ε ⟨hεinj, hεsurj⟩).symm)
  obtain ⟨hcH, hdH, hsH, -, -⟩ :=
    UnitaryPilot.swapLift_decomposition_of_hasBLift hdata hOut hBK hBsup
  have hodd : Odd (Nat.card (oddCoreLift Kc ⊓ (oddCoreLift Kc).map (MulAut.conj t').toMonoidHom :
      Subgroup (centralizer (modelToG e (siegelTorus K n) : Set G)))) :=
    (CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (G := centralizer (modelToG e (siegelTorus K n) : Set G))).of_dvd_nat
        (Subgroup.card_dvd_of_le hdH)
  have hSperf : Group.IsPerfect (siegelLevi K n) :=
    Subgroup.isPerfect_iff.2 (Subgroup.isPerfect_iff.1 (isQuasisimple_siegelLevi hq (by omega)).1)
  let ιG : siegelLevi K n →* G := L.subtype.comp (e.symm.toMonoidHom.comp (siegelLevi K n).subtype)
  have hιD : ∀ x : siegelLevi K n, ιG x ∈ modelToG e (siegelLevi K n) := fun x =>
    symm_mem_modelToG e x.2
  let ι : siegelLevi K n →* centralizer (modelToG e (siegelTorus K n) : Set G) :=
    ιG.codRestrict _ fun x => hDH (hιD x)
  have hιinj : ∀ x, ι x = 1 → x = 1 := by
    intro x hx
    have h0 : ((ι x : centralizer (modelToG e (siegelTorus K n) : Set G)) : G) = 1 :=
      congrArg Subtype.val hx
    have h1 : e.symm (x : StatedSp n K) = 1 := Subtype.ext h0
    have h2 : (x : StatedSp n K) = 1 := by
      rw [← map_one e.symm] at h1
      exact e.symm.injective h1
    exact Subtype.ext h2
  have hPmap : (perfectCore (⊤ : Subgroup (centralizer (modelToG e (siegelTorus K n) : Set G)))).map
      (centralizer (modelToG e (siegelTorus K n) : Set G)).subtype =
        centralizerPerfectCore (modelToG e (siegelTorus K n)) := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hDE : modelToG e (siegelLevi K n) ≤
      centralizerPerfectCore (modelToG e (siegelTorus K n)) :=
    modelToG_siegelLevi_le_siegelCore e hq (by omega)
  have hιK : ∀ x, ι x ∈ oddCoreLift Kc ⊔ (oddCoreLift Kc).map (MulAut.conj t').toMonoidHom := by
    intro x
    rw [hsH]
    have h1 : (ι x : G) ∈
        (perfectCore (⊤ : Subgroup (centralizer (modelToG e (siegelTorus K n) : Set G)))).map
        (centralizer (modelToG e (siegelTorus K n) : Set G)).subtype := hPmap ▸ hDE (hιD x)
    obtain ⟨w, hw, hwx⟩ := h1
    rwa [show w = ι x from Subtype.ext hwx] at hw
  have hιt : ∀ x, t' * ι x * t'⁻¹ = ι x := fun x => Subtype.ext (by
    change t * ιG x * t⁻¹ = ιG x
    rw [← mem_centralizer_iff.1 htC (ιG x) (e.symm _).2, mul_inv_cancel_right])
  have hιrange : ι.range = (modelToG e (siegelLevi K n)).subgroupOf
      (centralizer (modelToG e (siegelTorus K n) : Set G)) := by
    ext ⟨w, hw⟩
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨x, hx⟩
      rw [← congrArg Subtype.val hx]
      exact hιD x
    · intro hwD
      obtain ⟨z, hz, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hwD
      exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩
  obtain ⟨φ, hφK, hφ⟩ := UnitaryPilot.exists_swapLift hcH ht't' hsplit hodd ι hιK hιt
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply hιinj
    rw [← hφ x, hx, mul_one, mul_inv_cancel, mul_one]
  have hφrange : φ.range = oddCoreLift Kc :=
    UnitaryPilot.range_eq_oddCoreLift_of_swapLift hdata hBK (Nat.card_congr eKD.toEquiv) hφK hφ
      (by rw [hιrange])
  refine ⟨(centralizer (modelToG e (siegelTorus K n) : Set G)).subtype.comp
    (UnitaryPilot.swapParamHom hcH hφK), ?_, ?_,
    fun x => congrArg Subtype.val (hφ x), ?_,
    fun x y => congrArg Subtype.val (UnitaryPilot.conj_swapParamHom hcH hφK ht't' x y)⟩
  · rw [MonoidHom.range_comp, UnitaryPilot.range_swapParamHom, hφrange, hsH, hPmap]
  · intro x hx
    exact UnitaryPilot.ker_swapParamHom_le_center hcH hφK ht't' hφinj (Subtype.ext hx)
  ·
    intro c x
    have hgX : ((e.symm (diagSp K n c) : L) : G) ∈
        centralizer (modelToG e (siegelTorus K n) : Set G) :=
      symm_diagSp_mem_centralizer_siegelTorus e c
    let g' : centralizer (modelToG e (siegelTorus K n) : Set G) := ⟨_, hgX⟩
    have hg't : g' * t' = t' * g' := Subtype.ext (mem_centralizer_iff.1 htC _ (e.symm _).2)
    have hr : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units]
      exact LinearPilot.odd_natCard_sub_one
    have hgr : g' ^ Nat.card Kˣ = 1 := Subtype.ext (by
      change ((e.symm (diagSp K n c) : L) : G) ^ Nat.card Kˣ = 1
      have hc : c ^ Nat.card Kˣ = 1 := funext fun i => pow_card_eq_one'
      rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, hc, map_one, map_one, OneMemClass.coe_one])
    obtain ⟨σs, hσs⟩ := hdata.exists_sign
    have hσ1 : σs (π g') = 1 := UnitaryPilot.eq_one_of_pow_eq_one_of_odd hr
      (by rw [← map_pow, ← map_pow, hgr, map_one, map_one])
    have hg'N : g' ∈
        normalizer (oddCoreLift Kc : Set (centralizer (modelToG e (siegelTorus K n) : Set G))) :=
      F4Pilot.mem_normalizer_oddCoreLift Kc (hσs _ hσ1)
    have hα : ∀ z,
        ι ((conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi c).toMonoidHom z) =
          g' * ι z * g'⁻¹ := fun z => Subtype.ext (by
      change ((e.symm ((conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi c z :
        siegelLevi K n) : StatedSp n K) : L) : G) = _
      rw [coe_conjDiagSub_apply, liftParam_id, map_mul, map_mul, map_inv]
      rfl)
    have hφα := UnitaryPilot.swapLift_comp_eq_conj hcH hφK hφ hg'N hg't
      (conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi c).toMonoidHom hα
    have e1 : g'⁻¹ * t' * g' = t' := by
      rw [mul_assoc, ← hg't, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : g'⁻¹ * t'⁻¹ = t'⁻¹ * g'⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hg't]
    have key : UnitaryPilot.swapParamHom hcH hφK
        (conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi c x.1,
          conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi c x.2) =
          g' * UnitaryPilot.swapParamHom hcH hφK x * g'⁻¹ := by
      rw [UnitaryPilot.swapParamHom_apply, UnitaryPilot.swapParamHom_apply]
      change φ ((conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi c).toMonoidHom x.1) *
        (t' * φ ((conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi c).toMonoidHom
          x.2) * t'⁻¹) = _
      rw [hφα, hφα]
      calc g' * φ x.1 * g'⁻¹ * (t' * (g' * φ x.2 * g'⁻¹) * t'⁻¹)
          = g' * φ x.1 * (g'⁻¹ * t' * g') * φ x.2 * (g'⁻¹ * t'⁻¹) := by group
        _ = g' * φ x.1 * t' * φ x.2 * (t'⁻¹ * g'⁻¹) := by rw [e1, e2]
        _ = g' * (φ x.1 * (t' * φ x.2 * t'⁻¹)) * g'⁻¹ := by group
    exact congrArg Subtype.val key

theorem nonempty_siegelSwapParam_of_swapRow_of_split (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hsplit : OddCentralSplit (siegelLevi K n)) (hrow : SiegelSwapRow e t) :
    Nonempty (SiegelSwapParam e t) := by
  obtain ⟨htX, Kc, hKc', hDKK, hne, hcomm, hZK, ⟨eKD⟩⟩ := hrow
  obtain ⟨Ψ, hrange, hker, hdiag, hN2, hswap⟩ := exists_siegelSwapParam_aux hset hKc hf hn e htC
    ht hsplit rfl rfl htX hKc' hDKK hne hcomm hZK eKD
  exact ⟨⟨Ψ, hrange, hker, hdiag, hN2, hswap⟩⟩

theorem siegel_normal_or_fieldParam_or_swapParam (hcat : LinearPilot.SLmCatalogueClausesAt n)
    (hdet : LinearPilot.SLmEvenTypeDetAt n) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hsplit : OddCentralSplit (siegelLevi K n)) {F : Type} [Field F] [Finite F] (ι : K →+* F)
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    (t ∈ centralizer (modelToG e (siegelTorus K n) : Set G) ∧
        (((modelToG e (siegelLevi K n)).subgroupOf
          (centralizer (modelToG e (siegelTorus K n) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (siegelTorus K n) : Set G))))).Normal) ∨
      Nonempty (SiegelFieldParam e t ι σ) ∨ Nonempty (SiegelSwapParam e t) := by
  rcases siegel_normal_or_fieldParam_or_swap hcat hdet hset hKc hf hn e htC ht ι hσ1 hσσ hfix with
    h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (nonempty_siegelSwapParam_of_swapRow_of_split hset hKc hf hn e htC ht
      hsplit h))

end Swap

end CFSG.SeitzReduction.SymplecticPilot
