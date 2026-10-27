module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotMainInputs
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift oddCoreLift SwapComponentData)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

section Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem proj_torusDiagSL_mem_centralizer_rootTorus {a b : Fin n} (hab : a ≠ b)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    LinearFlag.proj n K (torusDiagSL c) ∈
      centralizer (rootTorus (K := K) hab : Set (LinearFlag.projectiveSL n K)) := by
  refine mem_centralizer_iff.2 fun x hx => ?_
  obtain ⟨κ, rfl⟩ := hx
  change LinearFlag.proj n K (torusDiagSL (rootTorusHom hab κ)) * LinearFlag.proj n K
      (torusDiagSL c) = LinearFlag.proj n K (torusDiagSL c) *
        LinearFlag.proj n K (torusDiagSL (rootTorusHom hab κ))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm (rootTorusHom hab κ) c]

theorem pow_card_units_eq_one_blockTorusParam [Finite K]
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) : c ^ Nat.card Kˣ = 1 := by
  apply Subtype.ext
  funext i
  change (c.1 i) ^ Nat.card Kˣ = 1
  exact pow_card_eq_one'

theorem eq_one_of_mem_blockSpecialLinear_of_proj_eq_one {N : Finset (Fin n)} (hN : N.card < n)
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ blockSpecialLinear N)
    (h : LinearFlag.proj n K x = 1) : x = 1 := by
  rw [← range_blockEmbed] at hx
  obtain ⟨A, rfl⟩ := hx
  have hA : A = 1 := proj_comp_blockEmbed_injective hN (by
    rw [MonoidHom.comp_apply, h, map_one])
  rw [hA, map_one]

theorem coe_conjDiag_id_apply (N : Finset (Fin n))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (x : blockSpecialLinear (K := K) N) :
    ((conjDiag (RingHom.id K) N c x : blockSpecialLinear (K := K) N) :
      SpecialLinearGroup (Fin n) K) = torusDiagSL c * x * (torusDiagSL c)⁻¹ := by
  have h : Matrix.SpecialLinearGroup.map (RingHom.id K) (torusDiagSL c) = torusDiagSL c := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  rw [coe_conjDiag_apply, h]

end Matrix

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_swapNeighbourParam_rootTorus_of_swapRow_of_split (hset : SeitzSetting G L)
    {n f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) {g y : G}
    (hyD : y ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))) (hy : orderOf y = 2)
    (hg : g⁻¹ * t * g = t * y)
    (hyP : ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ P ≤ L ∧ y ∈ P ∧ P ≤ centralizer ({y} : Set G))
    (hsplit : OddCentralSplit (blockSpecialLinear (K := K) (({a, b} : Finset (Fin n))ᶜ)))
    (hrow : RootTorusSwapRow e t hab) :
    Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
      (({a, b} : Finset (Fin n))ᶜ)) := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  obtain ⟨htX, Kc, hKc', hDKK, hne, hcomm, hZK, ⟨eKD⟩⟩ := hrow
  set X := modelToG e (rootTorus (K := K) hab) with hXdef
  set H := centralizer (X : Set G) with hHdef
  set N : Finset (Fin n) := ({a, b} : Finset (Fin n))ᶜ with hNdef
  set D := modelToG e (blockSL (K := K) N) with hDdef
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set τ := π t' with hτ
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hcard : N.card = n - 2 := by
    rw [hNdef, Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  have hN3 : 3 ≤ N.card := by omega
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_rootTorus_of_seitzSetting (X := X) (D := D) hset
    hKc hf e hn htC ht hab rfl htX rfl
  obtain ⟨-, -, -, -, -, -, hDC, -, -, -, -⟩ :=
    neighbour_data_rootTorus (X := X) (D := D) e hn hq hab htC rfl rfl
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
  have hDbp : ⁅Db, Db⁆ = Db := Subgroup.isPerfect_iff.1 (⟨hcomp.2.2.1⟩ : Group.IsPerfect _)
  have hττ : (Kc.map (MulAut.conj τ).toMonoidHom).map (MulAut.conj τ).toMonoidHom = Kc := by
    rw [F4Pilot.map_conj_map_conj_eq_map_conj_mul, hdata.mul_self, map_one]
    ext x
    simp
  have h1 : ⁅Kc, Db⁆ ≠ ⊥ := fun hb => hDbne
    (UnitaryPilot.eq_bot_of_le_sup_of_commutator_eq_bot hDKK hDbp hb
      (UnitaryPilot.commutator_map_conj_eq_bot_of_mem_centralizer hτD hb))
  have h2 : ⁅Kc.map (MulAut.conj τ).toMonoidHom, Db⁆ ≠ ⊥ := fun hb => hDbne
    (UnitaryPilot.eq_bot_of_le_sup_of_commutator_eq_bot hDKK hDbp
      (hττ ▸ UnitaryPilot.commutator_map_conj_eq_bot_of_mem_centralizer hτD hb) hb)
  obtain ⟨-, -, hBl⟩ := bLift_rootTorus_of_fused_of_seitzSetting (X := X) (D := D) hset hKc hq e
    hn htC ht hab rfl rfl hyD hy hg hyP
  obtain ⟨hBK, hBsup⟩ := hBl Kc (Kc.map (MulAut.conj τ).toMonoidHom) hKc'
    (F4Pilot.isComponent_map_conj hKc' τ) h1 h2
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
  have hcardN : Fintype.card ((Neighbour.root a b hab).index) = n - 2 := by
    rw [Fintype.card_coe, Neighbour.index_root, Finset.card_compl, Fintype.card_fin,
      Finset.card_pair hab]
  obtain ⟨ε, hεinj, hεrange, -⟩ := exists_projectiveSL_embedding e (.root a b hab)
    (Fintype.equivFinOfCardEq hcardN) (by omega) hDbne hZDb le_rfl
  have hεsurj : Function.Surjective ε := by
    intro w
    have hw : w ∈ ε.range := by
      rw [hεrange]
      exact mem_subgroupOf.2 w.2
    exact hw
  have hOut : Group.IsSolvable (Outer Kc) :=
    isSolvable_outer_of_mulEquiv (by omega)
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
    L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj n K).comp
      (blockSpecialLinear (K := K) N).subtype))
  have hιD : ∀ x : blockSpecialLinear (K := K) N, ιG x ∈ D := fun x =>
    symm_mem_modelToG e (proj_mem_blockSL x.2)
  let ι : blockSpecialLinear (K := K) N →* H := ιG.codRestrict H fun x => hDH (hιD x)
  have hιinj : ∀ x, ι x = 1 → x = 1 := by
    intro x hx
    have h0 : ((ι x : H) : G) = 1 := congrArg Subtype.val hx
    have h1 : e.symm (LinearFlag.proj n K x) = 1 := Subtype.ext h0
    have h2 : LinearFlag.proj n K x = 1 := by
      rw [← map_one e.symm] at h1
      exact e.symm.injective h1
    exact Subtype.ext (eq_one_of_mem_blockSpecialLinear_of_proj_eq_one (by omega) x.2 h2)
  have hPmap : (perfectCore (⊤ : Subgroup H)).map H.subtype = centralizerPerfectCore X := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hDE : D ≤ centralizerPerfectCore X :=
    modelToG_blockSL_index_le_neighbourCore e (.root a b hab)
      (commutator_blockSL_eq_of_three_le hN3)
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
  obtain ⟨φ, hφK, hφ⟩ := UnitaryPilot.exists_swapLift hcH ht't' hsplit hodd ι hιK hιt
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
    have hgX : ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈ H :=
      modelToG_le_centralizer e (le_refl (centralizer (rootTorus (K := K) hab :
        Set (LinearFlag.projectiveSL n K))))
        (symm_mem_modelToG e (proj_torusDiagSL_mem_centralizer_rootTorus hab c))
    set g' : H := ⟨_, hgX⟩ with hg'def
    have hg't : g' * t' = t' * g' := Subtype.ext (mem_centralizer_iff.1 htC _ (e.symm _).2)
    have hr : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units]
      exact odd_natCard_sub_one
    have hgr : g' ^ Nat.card Kˣ = 1 := Subtype.ext (by
      change ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ^ Nat.card Kˣ = 1
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
        change ((e.symm (LinearFlag.proj n K ((conjDiag (RingHom.id K) N c z :
          blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K)) : L) : G) = _
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

theorem nonempty_swapNeighbourParam_rootTorus_of_swapRow
    (hset : SeitzSetting G L)
    {n f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    {a b : Fin n} (hab : a ≠ b) (hrow : RootTorusSwapRow e t hab) :
    Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
      (({a, b} : Finset (Fin n))ᶜ)) := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  obtain ⟨g, y, hy1, hyD, hg⟩ := exists_conj_eq_mul_mem_blockSL_compl_pair e
    (le_centralizer_of_mem_centralizer htC) (by omega) hab hR5
  have hyG : (y : G) ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ)) :=
    (mem_modelToG e).2 ⟨e y, hyD, by simp⟩
  have hy2 : orderOf (y : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e y]
    exact hy1.orderOf_eq_two one_ne_zero
  have hNne : (({a, b} : Finset (Fin n))ᶜ).Nonempty := Finset.card_pos.1 (by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
    omega)
  exact nonempty_swapNeighbourParam_rootTorus_of_swapRow_of_split hset hKc hf e hn htC ht hab hyG
    hy2 hg (exists_perfect_le_centralizer_of_isInvolutionClass_one e (by omega) (Or.inl hn) hy1)
    (oddCentralSplit_blockSpecialLinear hNne) hrow

end Swap

theorem linearSwapLiftInput_holds :
    LinearSwapLiftInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hR5 a b hab hrow
  exact nonempty_swapNeighbourParam_rootTorus_of_swapRow hset hKc hf e hn
    (mem_centralizer_of_inf_eq_zpowers hKt) ht hR5 hab hrow

end CFSG.SeitzReduction.LinearPilot
