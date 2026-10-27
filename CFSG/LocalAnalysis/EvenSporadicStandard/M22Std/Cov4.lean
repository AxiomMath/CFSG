module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverMain
public import Certificates.Certificate24820

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.M22Cover CFSG.QuasithinUnique.Ch1.TitsCover
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA)

theorem exists_valuation {E : Type*} [Group E] (d : CovData) (hd : covCheck d = true)
    (X : CentralExt E (Equiv.Perm (Fin 22))) (xt : Fin 3 → E)
    (hxt : ∀ i, X.φ (xt i) = d.x i) (hlift : ∀ bl ∈ d.blocks, ∃ gt : E, X.φ gt = bl.g) :
    ∃ c : ℕ → ZMod 2, (∀ f ∈ forms0 d, evalForm d.M c f = 0) ∧
      ∀ e < 3 * d.nV, c e = cE d.tab xt e := by
  classical
  simp only [covCheck, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hgood, hblk⟩, hvalid⟩, -⟩ := hd
  obtain ⟨hT, hx⟩ := goodCheck_sound hgood
  have hblk' : ∀ bl ∈ d.blocks, blkCheck d d.elaTab bl = true := List.all_eq_true.1 hblk
  have hvalid' : ∀ eq ∈ d.eqns, eq.valid d = true := List.all_eq_true.1 hvalid
  have hmem : ∀ b < d.blocks.length, d.blocks[b]! ∈ d.blocks := fun b hb => by
    rw [getElem!_pos d.blocks b hb]
    exact List.getElem_mem hb
  have hex : ∀ b : ℕ, ∃ (gt : E) (γ : ℕ → ZMod 2), b < d.blocks.length →
      ∀ j < (d.blocks[b]!).va.length,
        gt * sig d.tab xt ((d.blocks[b]!).va[j]!) * gt⁻¹ =
          sig d.tab xt ((d.blocks[b]!).vb[j]!) * X.toZ (γ j) := by
    intro b
    by_cases hb : b < d.blocks.length
    · obtain ⟨gt, hgt⟩ := hlift _ (hmem b hb)
      obtain ⟨-, -, hrel⟩ := blkCheck_sound hx (hblk' _ (hmem b hb))
      obtain ⟨γ, hγ⟩ := exists_gamma X xt hxt hgt (fun j => (d.blocks[b]!).va[j]!)
        (fun j => (d.blocks[b]!).vb[j]!) (d.blocks[b]!).va.length fun j hj => (hrel j hj).2.2
      exact ⟨gt, γ, fun _ => hγ⟩
    · exact ⟨1, 0, fun h => absurd h hb⟩
  choose gt γs hγ using hex
  have hlen : ∀ b < d.blocks.length, (d.blocks[b]!).va.length ≤ 32 := fun b hb =>
    (blkCheck_sound hx (hblk' _ (hmem b hb))).2.1
  let d' : CovData := { d with free := [] }
  refine ⟨valOf d xt γs, fun f hf => ?_, fun e he => valOf_edge d xt γs he⟩
  obtain ⟨eq, heq, rfl⟩ := List.mem_map.1 hf
  have hv : eq.valid d = true := hvalid' eq (by
    rw [eqns_eq_eqns0_append]
    exact List.mem_append_left _ heq)
  have hnf : ∀ e, eq ≠ Eqn.free e := by
    intro e h
    subst h
    simp [eqns0] at heq
  have hv' : eq.valid d' = true := by
    cases eq with
    | free e => exact absurd rfl (hnf e)
    | tree v i => exact hv
    | trans w v₀ v₁ => exact hv
    | fus b ρ => exact hv
  exact eqn_sound d' X xt hT hxt hγ hlen (fun e he => by simp [d'] at he) eq hv'

theorem walk_sum_eq {E : Type*} [Group E] (d : CovData) (hd : covCheck d = true)
    (X : CentralExt E (Equiv.Perm (Fin 22))) (xt : Fin 3 → E)
    (hxt : ∀ i, X.φ (xt i) = d.x i) (hlift : ∀ bl ∈ d.blocks, ∃ gt : E, X.φ gt = bl.g)
    {W : List Letter} {e : ℕ} (he : e < 3 * d.nV)
    (hred : reduceF (gePivots (d.M + 5) d.M (forms0 d)) (d.M + 5)
      (formOf (d.tab.walkEdges 0 W) ^^^ 2 ^ e) = 0) :
    ((d.tab.walkEdges 0 W).map (cE d.tab xt)).sum = cE d.tab xt e := by
  obtain ⟨c, hform, hc⟩ := exists_valuation d hd X xt hxt hlift
  have hT := covCheck_good hd
  have hW := hT.walkEdges_lt hT.zero_lt W
  have h := reduceF_sound (gePivots_sound (d.M + 5) hform) (d.M + 5)
    (formOf (d.tab.walkEdges 0 W) ^^^ 2 ^ e)
  have hM : 3 * d.nV ≤ d.M := by unfold CovData.M; omega
  have hnV : d.tab.nV = d.nV := rfl
  have hsum : ((d.tab.walkEdges 0 W).map c).sum = ((d.tab.walkEdges 0 W).map (cE d.tab xt)).sum :=
    congrArg List.sum (List.map_congr_left fun e' he' => hc e' (by have := hW e' he'; omega))
  rw [hred, evalForm_zero, evalForm_xor,
    evalForm_formOf _ _ (fun e' he' => by have := hW e' he'; omega),
    evalForm_unit _ (by omega : e < d.M), hsum, hc e he] at h
  have h2 := h.symm
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h2
  exact h2

theorem walk_sum_eq_zero {E : Type*} [Group E] (d : CovData) (hd : covCheck d = true)
    (X : CentralExt E (Equiv.Perm (Fin 22))) (xt : Fin 3 → E)
    (hxt : ∀ i, X.φ (xt i) = d.x i) (hlift : ∀ bl ∈ d.blocks, ∃ gt : E, X.φ gt = bl.g)
    {W : List Letter}
    (hred : reduceF (gePivots (d.M + 5) d.M (forms0 d)) (d.M + 5)
      (formOf (d.tab.walkEdges 0 W)) = 0) :
    ((d.tab.walkEdges 0 W).map (cE d.tab xt)).sum = 0 := by
  obtain ⟨c, hform, hc⟩ := exists_valuation d hd X xt hxt hlift
  have hT := covCheck_good hd
  have hW := hT.walkEdges_lt hT.zero_lt W
  have h := reduceF_sound (gePivots_sound (d.M + 5) hform) (d.M + 5)
    (formOf (d.tab.walkEdges 0 W))
  have hM : 3 * d.nV ≤ d.M := by unfold CovData.M; omega
  have hnV : d.tab.nV = d.nV := rfl
  have hsum : ((d.tab.walkEdges 0 W).map c).sum = ((d.tab.walkEdges 0 W).map (cE d.tab xt)).sum :=
    congrArg List.sum (List.map_congr_left fun e' he' => hc e' (by have := hW e' he'; omega))
  rw [hred, evalForm_zero, evalForm_formOf _ _ (fun e' he' => by have := hW e' he'; omega),
    hsum] at h
  exact h.symm

namespace IsM22Cover

variable {L : Type} [Group L] {t : L}

@[expose] def permHom (e : L ⧸ center L ≃* Carrier .M22) : L →* Equiv.Perm (Fin 22) :=
  toPerm.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))

theorem permHom_apply (e : L ⧸ center L ≃* Carrier .M22) (x : L) :
    permHom e x = toPerm (e (x : L ⧸ center L)) := rfl

theorem mk_t (h : IsM22Cover L t) : ((t : L) : L ⧸ center L) = 1 :=
  (QuotientGroup.eq_one_iff t).2 (h.center_eq ▸ mem_zpowers t)

@[expose] def centralExt (h : IsM22Cover L t) (e : L ⧸ center L ≃* Carrier .M22) :
    CentralExt L (Equiv.Perm (Fin 22)) where
  φ := permHom e
  ζ := t
  φ_ζ := by
    rw [permHom_apply, h.mk_t, map_one, map_one]
  ne_one := h.t_ne_one
  sq := h.mul_self_t
  central := h.t_central
  ker := fun x hx => by
    rw [permHom_apply] at hx
    have h1 : e (x : L ⧸ center L) = 1 := toPerm_injective (hx.trans (map_one toPerm).symm)
    exact h.eq_one_or_eq_t_of_mk_eq_one (by simpa using h1)

theorem centralExt_range (h : IsM22Cover L t) (e : L ⧸ center L ≃* Carrier .M22) :
    ∀ y ∈ NativeSporadic.M22, ∃ x : L, (h.centralExt e).φ x = y := by
  intro y hy
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm (mkM22 y hy))
  refine ⟨q, ?_⟩
  show permHom e q = y
  rw [permHom_apply, hq, MulEquiv.apply_symm_apply, toPerm_mkM22]

theorem centralExt_mem (h : IsM22Cover L t) (e : L ⧸ center L ≃* Carrier .M22) :
    ∀ x : L, (h.centralExt e).φ x ∈ NativeSporadic.M22 := fun x =>
  (show NativeSporadic.M22 from e (x : L ⧸ center L)).2

theorem cE_free_eq_one [Finite L]
    [Group.IsPerfect L] (h : IsM22Cover L t) (e : L ⧸ center L ≃* Carrier .M22)
    (xt : Fin 3 → L) (hxt : ∀ i, (h.centralExt e).φ (xt i) = covData.x i) :
    cE covData.tab xt 189 = 1 := by
  by_contra hne1
  have h0 : cE covData.tab xt 189 = 0 := by
    rcases zmod_two_cases (cE covData.tab xt 189) with h' | h'
    · exact h'
    · exact absurd h' hne1
  exact false_of_double_cover (h.centralExt e) (h.centralExt_range e) (centralExt_mem h e) xt hxt
    (fun e' he' => by
      rw [covData_free] at he'
      have : e' = 189 := by simpa using he'
      rw [this]
      exact h0)

theorem sig_sq_rel
    [Finite L] [Group.IsPerfect L] (h : IsM22Cover L t)
    (e : L ⧸ center L ≃* Carrier .M22) (xt : Fin 3 → L)
    (hxt : ∀ i, (h.centralExt e).φ (xt i) = covData.x i) :
    sig covData.tab xt 79 * sig covData.tab xt 79 =
      sig covData.tab xt 7 * sig covData.tab xt 7 * t := by
  let X := h.centralExt e
  have hrange := h.centralExt_range e
  have hT := covCheck_good covCheck_covData
  have hlift : ∀ bl ∈ covData.blocks, ∃ gt : L, X.φ gt = bl.g := fun bl _ =>
    hrange _ bl.g_mem
  have hck := Certificates.certificate24820
  simp only [sqCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨⟨hclosed, hred⟩, -⟩, -⟩, -⟩ := hck
  have h189 : 189 < 3 * covData.nV := by rw [covData_nV]; norm_num
  have hsum := walk_sum_eq covData covCheck_covData X xt hxt hlift h189 hred
  have hc1 := h.cE_free_eq_one e xt hxt
  have hpsi := closed_walk X xt hT hxt hT.zero_lt hclosed
  rw [hsum, hc1] at hpsi
  have h1 : psi xt (sqWalk covData 79 7) = sig covData.tab xt 79 * sig covData.tab xt 79 *
      (sig covData.tab xt 7)⁻¹ * (sig covData.tab xt 7)⁻¹ := by
    simp only [sqWalk, psi_append, psi_posW, psi_invW]
    rfl
  have hpsi' : sig covData.tab xt 79 * sig covData.tab xt 79 * (sig covData.tab xt 7)⁻¹ *
      (sig covData.tab xt 7)⁻¹ = t := by
    rw [← h1, hpsi]
    exact X.toZ_one
  calc sig covData.tab xt 79 * sig covData.tab xt 79
      = (sig covData.tab xt 79 * sig covData.tab xt 79 * (sig covData.tab xt 7)⁻¹ *
        (sig covData.tab xt 7)⁻¹) * (sig covData.tab xt 7 * sig covData.tab xt 7) := by group
    _ = t * (sig covData.tab xt 7 * sig covData.tab xt 7) := by rw [hpsi']
    _ = sig covData.tab xt 7 * sig covData.tab xt 7 * t := h.t_central _

theorem orderOf_sig_sq
    [Finite L] (h : IsM22Cover L t)
    (e : L ⧸ center L ≃* Carrier .M22) (xt : Fin 3 → L)
    (hxt : ∀ i, (h.centralExt e).φ (xt i) = covData.x i) :
    orderOf ((sig covData.tab xt 79 * sig covData.tab xt 79 : L) : L ⧸ center L) = 2 := by
  have hck := Certificates.certificate24820
  simp only [sqCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨-, hv1⟩, hinv⟩, hne⟩ := hck
  have hel := covData.rep_el (fun i => covData.xa_rep i) hv1
  have hz := rep_compA hel hel
  have hsq : (covData.tab.el covData.x 79 * covData.tab.el covData.x 79) *
      (covData.tab.el covData.x 79 * covData.tab.el covData.x 79) = 1 :=
    eq_of_eqA (rep_compA hz hz) rep_idA hinv
  have hne' : covData.tab.el covData.x 79 * covData.tab.el covData.x 79 ≠ 1 := fun h' => by
    have h2 := (eqA_iff hz rep_idA).2 h'
    rw [h2] at hne
    exact absurd hne (by decide)
  have hord : orderOf (covData.tab.el covData.x 79 * covData.tab.el covData.x 79) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hsq) hne'
  have hinj : Function.Injective (toPerm.comp e.toMonoidHom) :=
    toPerm_injective.comp e.injective
  rw [← orderOf_injective _ hinj, ← hord]
  congr 1
  show permHom e _ = _
  rw [map_mul, show permHom e (sig covData.tab xt 79) = covData.tab.el covData.x 79 from
    phi_sig (h.centralExt e) xt hxt covData.tab 79]

theorem exists_sq_pair
    [Finite L] [Group.IsPerfect L] (h : IsM22Cover L t) :
    ∃ w₁ w₂ : L, orderOf ((w₁ * w₁ : L) : L ⧸ center L) = 2 ∧ w₁ * w₁ = w₂ * w₂ * t := by
  obtain ⟨e⟩ := h.quotient
  have hrange := h.centralExt_range e
  have hxmem : ∀ i, covData.x i ∈ NativeSporadic.M22 := fun i => wordP_mem _
  choose xt hxt using fun i : Fin 3 => hrange (covData.x i) (hxmem i)
  exact ⟨sig covData.tab xt 79, sig covData.tab xt 7, h.orderOf_sig_sq e xt hxt,
    h.sig_sq_rel e xt hxt⟩

theorem exists_sq_of_lift
    [Finite L] [Group.IsPerfect L] (h : IsM22Cover L t) :
    ∀ u : L, orderOf (u : L ⧸ center L) = 2 → ∃ w : L, w * w = u := by
  obtain ⟨w₁, w₂, hord, hrel⟩ := h.exists_sq_pair
  intro u hu
  obtain ⟨cb, hc⟩ := h.involution_conj hord hu
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  have hyc : (u : L ⧸ center L) = ((c * (w₁ * w₁) * c⁻¹ : L) : L ⧸ center L) := by
    rw [hc]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rcases h.eq_or_eq_mul_t_of_mk_eq hyc with h1 | h1
  · exact ⟨c * w₁ * c⁻¹, by rw [h1]; group⟩
  · refine ⟨c * w₂ * c⁻¹, ?_⟩
    have h2 : c * w₂ * c⁻¹ * (c * w₂ * c⁻¹) = c * (w₂ * w₂) * c⁻¹ := by group
    have h3 : w₂ * w₂ = w₁ * w₁ * t := by
      rw [hrel, mul_assoc, h.mul_self_t, mul_one]
    rw [h1, h2, h3]
    calc c * (w₁ * w₁ * t) * c⁻¹ = c * (w₁ * w₁) * (t * c⁻¹) := by simp only [mul_assoc]
      _ = c * (w₁ * w₁) * (c⁻¹ * t) := by rw [h.t_central c⁻¹]
      _ = c * (w₁ * w₁) * c⁻¹ * t := by simp only [mul_assoc]

end IsM22Cover

end CFSG.EvenSporadicStandard.M22Std
