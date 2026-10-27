module

public import CFSG.CGT.Foote82.T66.BranchBBasic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPerm
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.Coordinator

namespace BranchB

section ConjPerm

variable {Y : Type} [Group Y] (E : Subgroup Y) [E.Normal] {N : ℕ} (hN : 7 ≤ N)
  (e : ↥E ≃* alternatingGroup (Fin N))

noncomputable def conjPerm : Y →* Equiv.Perm (Fin N) :=
  (CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv hN e).toMonoidHom.comp
    (MulAut.conjNormal (H := E))

theorem conjPerm_coe (x : ↥E) :
    conjPerm E hN e (x : Y) = ((e x : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) := by
  show CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv hN e (MulAut.conjNormal (x : Y)) = _
  rw [MulAut.conjNormal_val, CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv_conj,
    CFSG.GH74.GLS.IVK.Proofs2.psiAlt_apply]

theorem commute_of_conjPerm_eq_one {y : Y} (hy : conjPerm E hN e y = 1) (x : ↥E) :
    y * (x : Y) * y⁻¹ = x := by
  have hc : MulAut.conjNormal (H := E) y = 1 :=
    (CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv hN e).map_eq_one_iff.1 hy
  have h1 := congrArg (fun f : MulAut ↥E => ((f x : ↥E) : Y)) hc
  simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using h1

end ConjPerm

theorem isComponentOf_of_le {Γ : Type*} [Group Γ] {A K H : Subgroup Γ}
    (hc : IsComponentOf A K) (hAH : A ≤ H) (hHK : H ≤ K) : IsComponentOf A H := by
  refine ⟨hAH, ?_, hc.2.2⟩
  have := hc.2.1.inf H
  rwa [inf_eq_left.2 hAH, inf_eq_right.2 hHK] at this

theorem isComponentOf_subgroupOf {Γ : Type*} [Group Γ] {A K H : Subgroup Γ}
    (hc : IsComponentOf A K) (hKH : K ≤ H) :
    IsComponentOf (A.subgroupOf H) (K.subgroupOf H) :=
  ⟨Subgroup.comap_mono hc.1, hc.2.1.comap H.subtype,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hc.1.trans hKH)) hc.2.2⟩

theorem isComponentOf_map {Γ Δ : Type*} [Group Γ] [Group Δ] {A K : Subgroup Γ}
    (hc : IsComponentOf A K) (f : Γ →* Δ) (hf : Function.Injective f) :
    IsComponentOf (A.map f) (K.map f) :=
  ⟨Subgroup.map_mono hc.1, hc.2.1.map f,
    CFSG.Open.IsQuasisimple.of_mulEquiv (A.equivMapOfInjective f hf).symm hc.2.2⟩

theorem two_le_pRank {Γ : Type*} [Group Γ] [Finite Γ] {E H : Subgroup Γ} (hEH : E ≤ H)
    (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) : 2 ≤ CFSG.Open.pRank 2 H := by
  refine le_csSup ⟨Nat.card Γ, ?_⟩ ⟨E, hEH, hE, by rw [hE4]; norm_num⟩
  rintro k ⟨F, -, -, hF⟩
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ = Nat.card F := hF.symm
    _ ≤ Nat.card Γ := Subgroup.card_le_card_group F

theorem fixed_zpowers_iff {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    (∀ r ∈ Subgroup.zpowers σ, r i = i) ↔ σ i = i := by
  constructor
  · intro hi
    exact hi σ (Subgroup.mem_zpowers σ)
  · intro hi r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hi k

theorem altOn_eq_altFixingMoved {N : ℕ} (π : Equiv.Perm (Fin N)) :
    altOn {i | π i = i} = CFSG.OddStandard.AltStdSec.SwapPartner.altFixingMoved π := by
  ext g
  rw [CFSG.OddStandard.AltStdSec.SwapPartner.mem_altFixingMoved, altOn, Subgroup.mem_inf,
    mem_fixingSubgroup_iff]
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Equiv.Perm.smul_def]

theorem two_mul_card_altOn {N : ℕ} (π : Equiv.Perm (Fin N))
    (h2 : 2 ≤ Fintype.card {i : Fin N // π i = i}) :
    2 * Nat.card (altOn {i | π i = i}) = (Fintype.card {i : Fin N // π i = i}).factorial := by
  rw [altOn_eq_altFixingMoved]
  exact CFSG.OddStandard.AltStdSec.SwapPartner.two_mul_card_altFixingMoved h2

theorem card_fix_add_card_support {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Fintype.card {i : Fin N // π i = i} + π.support.card = N := by
  rw [Fintype.card_subtype]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun i => π i = i)
  rw [Finset.card_univ, Fintype.card_fin] at this
  convert this using 2
  rfl

theorem conj_swap {N : ℕ} (π : Equiv.Perm (Fin N)) (a b : Fin N) :
    π * Equiv.swap a b * π⁻¹ = Equiv.swap (π a) (π b) := by
  refine Equiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := π.surjective x
  show π (Equiv.swap a b (π.symm (π y))) = Equiv.swap (π a) (π b) (π y)
  rw [Equiv.symm_apply_apply]
  exact (π.injective.swap_apply a b y).symm

theorem exists_four_group {N : ℕ} {A : Finset (Fin N)} (hA : A.card = 4) :
    ∃ E : Subgroup (Equiv.Perm (Fin N)), Nat.card E = 4 ∧ E ≤ alternatingGroup (Fin N) ∧
      (∀ e ∈ E, ∀ i ∉ A, e i = i) ∧ (∀ e ∈ E, e * e = 1) ∧
      (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) := by
  classical
  haveI hK := alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  let ι : Fin 4 ↪ Fin N := (A.orderEmbOfFin hA).toEmbedding
  have hι : Set.range ι = ↑A := Finset.range_orderEmbOfFin A hA
  let f : alternatingGroup (Fin 4) →* Equiv.Perm (Fin N) :=
    (Equiv.Perm.viaEmbeddingHom ι).comp (alternatingGroup (Fin 4)).subtype
  have hf : Function.Injective f :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp Subtype.val_injective
  refine ⟨(alternatingGroup.kleinFour (Fin 4)).map f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf]
    exact hK.card_four
  · rintro _ ⟨k, -, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    show Equiv.Perm.sign (Equiv.Perm.viaEmbedding (k : Equiv.Perm (Fin 4)) ι) = 1
    unfold Equiv.Perm.viaEmbedding
    rw [Equiv.Perm.sign_extendDomain]
    exact k.2
  · rintro _ ⟨k, -, rfl⟩ i hi
    refine Equiv.Perm.viaEmbedding_apply_of_notMem _ ι i ?_
    rw [hι]
    exact hi
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul f]
    have h1 : (⟨k, hk⟩ : alternatingGroup.kleinFour (Fin 4)) * ⟨k, hk⟩ = 1 :=
      IsKleinFour.mul_self _
    have h2 : k * k = 1 := congrArg Subtype.val h1
    rw [h2, map_one]
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    rw [← map_mul f, ← map_mul f]
    congr 1
    have := (IsKleinFour.isMulCommutative (G := alternatingGroup.kleinFour (Fin 4))).is_comm.comm
      ⟨k, hk⟩ ⟨k', hk'⟩
    exact congrArg Subtype.val this

theorem map_conj_alternatingGroup {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (alternatingGroup (Fin N)).map (MulAut.conj π).toMonoidHom = alternatingGroup (Fin N) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact (alternatingGroup.normal (α := Fin N)).conj_mem g hg π
  · intro g hg
    refine ⟨π⁻¹ * g * π, ?_, ?_⟩
    · have := (alternatingGroup.normal (α := Fin N)).conj_mem g hg π⁻¹
      rwa [inv_inv] at this
    · simp [MulAut.conj_apply, mul_assoc]

theorem eq_top_of_alternatingGroup_le {N : ℕ} {K : Subgroup (Equiv.Perm (Fin N))}
    (hK : alternatingGroup (Fin N) ≤ K) {t : Equiv.Perm (Fin N)} (ht : t ∈ K)
    (hts : Equiv.Perm.sign t = -1) : K = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
  · exact hK (Equiv.Perm.mem_alternatingGroup.2 hg)
  · have h1 : g * t ∈ K := hK (Equiv.Perm.mem_alternatingGroup.2 (by
      rw [map_mul, hg, hts]
      decide))
    have := K.mul_mem h1 (K.inv_mem ht)
    rwa [mul_inv_cancel_right] at this

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Hyp

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} (h : Hyp G L z v)

noncomputable def chi {N : ℕ} (hN : 7 ≤ N)
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N)) :
    ↥(bbH₁ G L z v) →* Equiv.Perm (Fin N) :=
  haveI := Lemma63.instNormalLayer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range
  (conjPerm (CFSG.layer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) hN
    (((CFSG.layer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range).equivMapOfInjective
      (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range.subtype
      (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range.subtype_injective).trans φA)).comp
    (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).rangeRestrict

include h

theorem chi_of_mem {N : ℕ} (hN : 7 ≤ N)
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N))
    {a : ↥(bbH₁ G L z v)} (ha : (a : GLV V) ∈ bbL₀ G L v) :
    h.chi hN φA a = ((φA ⟨_, h.map_mem_layerIn ha⟩ : alternatingGroup (Fin N)) :
      Equiv.Perm (Fin N)) := by
  obtain ⟨x, hx, hxa⟩ := h.map_mem_layerIn ha
  have hxa' : x = (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).rangeRestrict a := Subtype.ext hxa
  haveI := Lemma63.instNormalLayer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range
  have e1 : h.chi hN φA a = conjPerm _ hN
      (((CFSG.layer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range).equivMapOfInjective
        (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range.subtype
        (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range.subtype_injective).trans φA)
      ((⟨x, hx⟩ : ↥(CFSG.layer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range)) :
        ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) := by
    subst hxa'
    rfl
  have e2 : ((CFSG.layer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range).equivMapOfInjective
      (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range.subtype
      (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range.subtype_injective) ⟨x, hx⟩ =
      ⟨_, h.map_mem_layerIn ha⟩ := Subtype.ext hxa
  rw [e1, conjPerm_coe, MulEquiv.trans_apply, e2]

theorem chi_injective {N : ℕ} (hN : 7 ≤ N)
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N)) :
    Function.Injective (h.chi hN φA) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  haveI := Lemma63.instNormalLayer ↥(sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range
  have hcomm : ∀ a ∈ bbL₀ G L v, (g : GLV V) * a = a * g := by
    intro a ha
    have haH : a ∈ bbH₁ G L z v := h.L₀_le_H₁ ha
    obtain ⟨x, hx, hxa⟩ := h.map_mem_layerIn (a := ⟨a, haH⟩) ha
    have h1 := commute_of_conjPerm_eq_one _ hN _ hg ⟨x, hx⟩
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_rangeRestrict] at h2
    have hxa' : (x : GLV (Sect (bbW₀ G L v) (bbW₁ G L v))) =
        sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ ⟨a, haH⟩ := hxa
    rw [hxa'] at h2
    have h3 : sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ (g * ⟨a, haH⟩ * g⁻¹) =
        sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ ⟨a, haH⟩ := by
      rw [map_mul (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) (g * ⟨a, haH⟩) g⁻¹,
        map_mul (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) g ⟨a, haH⟩,
        map_inv (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) g]
      exact h2
    have h4 := h.injective h3
    have h5 : g * ⟨a, haH⟩ = ⟨a, haH⟩ * g := by
      calc g * ⟨a, haH⟩ = g * ⟨a, haH⟩ * g⁻¹ * g := by rw [inv_mul_cancel_right]
        _ = ⟨a, haH⟩ * g := by rw [h4]
    exact congrArg Subtype.val h5
  have hgL₀ := h.mem_L₀_of_commute g.2 hcomm
  rw [h.chi_of_mem hN φA hgL₀] at hg
  have h6 : φA ⟨_, h.map_mem_layerIn hgL₀⟩ = 1 := Subtype.ext hg
  have h7 := congrArg Subtype.val (φA.map_eq_one_iff.1 h6)
  exact h.injective (h7.trans (map_one (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)).symm)

theorem chi_map_L₀ {N : ℕ} (hN : 7 ≤ N)
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N)) :
    ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map (h.chi hN φA) =
      alternatingGroup (Fin N) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    rw [h.chi_of_mem hN φA ha]
    exact (φA _).2
  · intro σ hσ
    obtain ⟨w, hw⟩ := φA.surjective ⟨σ, hσ⟩
    have hw' : (w : GLV (Sect (bbW₀ G L v) (bbW₁ G L v))) ∈
        ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) := by
      rw [← h.layerIn_range]
      exact w.2
    obtain ⟨a, ha, haw⟩ := hw'
    refine ⟨a, ha, ?_⟩
    rw [h.chi_of_mem hN φA ha]
    have : (⟨_, h.map_mem_layerIn ha⟩ :
        ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range)) = w := Subtype.ext haw
    rw [this, hw]

abbrev HeartEquiv {N : ℕ}
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N))
    (ψW : Sect (bbW₀ G L v) (bbW₁ G L v) ≃+ altHeart N) : Prop :=
  ∀ (e : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range))
    (y : Sect (bbW₀ G L v) (bbW₁ G L v)) (x : evenWeight N), ψW y = (x : altHeart N) →
      ψW ((e : GLV (Sect (bbW₀ G L v) (bbW₁ G L v))) y) =
        (evenWeightPerm (φA e : Equiv.Perm (Fin N)) x : altHeart N)

theorem equiv_of_mem {N : ℕ} (hN : 7 ≤ N)
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N))
    (ψW : Sect (bbW₀ G L v) (bbW₁ G L v) ≃+ altHeart N) (hψW : h.HeartEquiv φA ψW)
    {a : ↥(bbH₁ G L z v)} (ha : (a : GLV V) ∈ bbL₀ G L v)
    (y : Sect (bbW₀ G L v) (bbW₁ G L v)) :
    ψW (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ a y) = altAct (h.chi hN φA a) (ψW y) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (ψW y)
  rw [h.chi_of_mem hN φA ha, ← hx, altAct_mk]
  exact hψW ⟨_, h.map_mem_layerIn ha⟩ y x hx.symm

theorem equiv_z {N : ℕ} (hN : 7 ≤ N)
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N))
    (ψW : Sect (bbW₀ G L v) (bbW₁ G L v) ≃+ altHeart N) (hψW : h.HeartEquiv φA ψW)
    (y : Sect (bbW₀ G L v) (bbW₁ G L v)) :
    ψW (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ ⟨z, h.z_mem_H₁⟩ y) =
      altAct (h.chi hN φA ⟨z, h.z_mem_H₁⟩) (ψW y) := by
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ↥(bbH₁ G L z v), z₁ = ⟨z, h.z_mem_H₁⟩ := ⟨_, rfl⟩
  rw [← hz₁]
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin N), σ = h.chi hN φA z₁ := ⟨_, rfl⟩
  rw [← hσ]
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(bbH₁ G L z v) →* GLV (Sect (bbW₀ G L v) (bbW₁ G L v)),
      φ = sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ := ⟨_, rfl⟩
  rw [← hφ]
  let c : altHeart N →+ altHeart N := (altAct σ⁻¹).comp (ψW.toAddMonoidHom.comp
    (((φ z₁ : GLV (Sect (bbW₀ G L v) (bbW₁ G L v))) :
      Sect (bbW₀ G L v) (bbW₁ G L v) →ₗ[ZMod 2] Sect (bbW₀ G L v) (bbW₁ G L v)).toAddMonoidHom.comp
      ψW.symm.toAddMonoidHom))
  have hcx : ∀ x, c x = altAct σ⁻¹ (ψW (φ z₁ (ψW.symm x))) := fun _ => rfl
  have hL₀eq : ∀ (a : ↥(bbH₁ G L z v)), (a : GLV V) ∈ bbL₀ G L v →
      ∀ y, ψW (φ a y) = altAct (h.chi hN φA a) (ψW y) := fun a ha y => by
    rw [hφ]
    exact h.equiv_of_mem hN φA ψW hψW ha y
  have hcomm : ∀ τ ∈ alternatingGroup (Fin N), ∀ x, c (altAct τ x) = altAct τ (c x) := by
    intro τ hτ x
    rw [← h.chi_map_L₀ hN φA] at hτ
    obtain ⟨a, ha, rfl⟩ := hτ
    have ha' : ((z₁ * a * z₁⁻¹ : ↥(bbH₁ G L z v)) : GLV V) ∈ bbL₀ G L v :=
      h.conj_mem_L₀ z₁.2 ha
    have e1 : altAct (h.chi hN φA a) x = ψW (φ a (ψW.symm x)) := by
      rw [hL₀eq a ha, AddEquiv.apply_symm_apply]
    have e2 : φ z₁ (φ a (ψW.symm x)) = φ (z₁ * a * z₁⁻¹) (φ z₁ (ψW.symm x)) := by
      have k1 : φ (z₁ * a) = φ (z₁ * a * z₁⁻¹) * φ z₁ := by
        rw [← map_mul φ (z₁ * a * z₁⁻¹) z₁, inv_mul_cancel_right]
      have k2 : φ (z₁ * a) = φ z₁ * φ a := map_mul φ z₁ a
      exact congrArg (fun f : GLV (Sect (bbW₀ G L v) (bbW₁ G L v)) => f (ψW.symm x))
        (k2.symm.trans k1)
    have e3 : h.chi hN φA (z₁ * a * z₁⁻¹) = σ * h.chi hN φA a * σ⁻¹ := by
      rw [map_mul (h.chi hN φA) (z₁ * a) z₁⁻¹, map_mul (h.chi hN φA) z₁ a,
        map_inv (h.chi hN φA) z₁, ← hσ]
    rw [hcx, hcx, e1, AddEquiv.symm_apply_apply, e2, hL₀eq _ ha', e3, ← altAct_mul,
      ← altAct_mul]
    congr 1
    group
  have hc1 : c = AddMonoidHom.id (altHeart N) := by
    rcases altHeart_endo_eq_zero_or_id (by omega) c hcomm with h0 | h0
    · exfalso
      have hab : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      have hca : (⟨2, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
      have hcb : (⟨2, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      apply mk_pairEW_ne_zero hab hca hcb
      have hp := congrArg (fun f : altHeart N →+ altHeart N =>
        f (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pairEW
          (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ : altHeart N)) h0
      simp only [hcx, AddMonoidHom.zero_apply] at hp
      have hp' := congrArg (altAct σ) hp
      rw [altAct_apply_inv, map_zero, AddEquiv.map_eq_zero_iff] at hp'
      have hp'' := congrArg (fun w => (φ z₁)⁻¹ w) hp'
      simp only [map_zero] at hp''
      rw [show (φ z₁)⁻¹ (φ z₁ (ψW.symm _)) = ψW.symm _ from (φ z₁).symm_apply_apply _,
        AddEquiv.map_eq_zero_iff] at hp''
      exact hp''
    · exact h0
  have := congrArg (fun f : altHeart N →+ altHeart N => f (ψW y)) hc1
  simp only [hcx, AddEquiv.symm_apply_apply, AddMonoidHom.id_apply] at this
  rw [← this, altAct_apply_inv]

theorem chi_equivariant {N : ℕ} (hN : 7 ≤ N)
    (φA : ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) ≃* alternatingGroup (Fin N))
    (ψW : Sect (bbW₀ G L v) (bbW₁ G L v) ≃+ altHeart N) (hψW : h.HeartEquiv φA ψW)
    (g : ↥(bbH₁ G L z v)) (y : Sect (bbW₀ G L v) (bbW₁ G L v)) :
    ψW (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ g y) = altAct (h.chi hN φA g) (ψW y) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(bbH₁ G L z v) →* GLV (Sect (bbW₀ G L v) (bbW₁ G L v)),
      φ = sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥(bbH₁ G L z v) →* Equiv.Perm (Fin N), χ = h.chi hN φA := ⟨_, rfl⟩
  rw [← hφ, ← hχ]
  let S : Subgroup ↥(bbH₁ G L z v) :=
    { carrier := {g | ∀ y, ψW (φ g y) = altAct (χ g) (ψW y)}
      mul_mem' := fun {a b} ha hb y => by
        show ψW (φ (a * b) y) = altAct (χ (a * b)) (ψW y)
        rw [map_mul φ a b, map_mul χ a b, altAct_mul, ← hb y, ← ha (φ b y)]
        rfl
      one_mem' := fun y => by
        show ψW (φ 1 y) = altAct (χ 1) (ψW y)
        rw [map_one φ, map_one χ, altAct_one]
        rfl
      inv_mem' := fun {a} ha y => by
        show ψW (φ a⁻¹ y) = altAct (χ a⁻¹) (ψW y)
        have := ha (φ a⁻¹ y)
        rw [show φ a (φ a⁻¹ y) = y by rw [map_inv φ a]; exact (φ a).apply_symm_apply y] at this
        rw [map_inv χ a, this, altAct_inv_apply] }
  obtain ⟨K, hO⟩ := h.orbitData
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hO.sup_eq]
    refine sup_le (fun a ha y => ?_) ?_
    · rw [hφ, hχ]
      exact h.equiv_of_mem hN φA ψW hψW ha y
    · intro r hr
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show (r : GLV V) ∈ Subgroup.zpowers z from hr)
      have hrk : r = (⟨z, h.z_mem_H₁⟩ : ↥(bbH₁ G L z v)) ^ k :=
        Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [hrk]
      refine zpow_mem (fun y => ?_) k
      rw [hφ, hχ]
      exact h.equiv_z hN φA ψW hψW y
  have hg : g ∈ S := by
    rw [hS]
    exact Subgroup.mem_top g
  exact hg y

theorem map_L_eq_altOn {N : ℕ} (f : ↥(bbH₁ G L z v) →* Equiv.Perm (Fin N))
    (hf : Function.Injective f)
    (hA : ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map f = alternatingGroup (Fin N)) :
    5 ≤ Nat.card {i : Fin N // f ⟨z, h.z_mem_H₁⟩ i = i} ∧
      (L.subgroupOf (bbH₁ G L z v)).map f = altOn {i | f ⟨z, h.z_mem_H₁⟩ i = i} := by
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ↥(bbH₁ G L z v), z₁ = ⟨z, h.z_mem_H₁⟩ := ⟨_, rfl⟩
  rw [← hz₁]
  have hzz : z₁ * z₁ = 1 := Subtype.ext (by rw [hz₁]; exact h.zz)
  have hσσ : f z₁ * f z₁ = 1 := by rw [← map_mul f z₁ z₁, hzz, map_one f]
  have hR : IsPGroup 2 (Subgroup.zpowers (f z₁)) := fun r =>
    ⟨1, Subtype.ext (by
      rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
      exact mul_self_of_mem_zpowers hσσ r.2)⟩
  have hc₀ : IsComponentOf L
      (bbH₁ G L z v ⊓ Subgroup.centralizer (Subgroup.zpowers z : Set (GLV V))) :=
    isComponentOf_of_le h.setup6₀.component
      (le_inf h.L_le_H₁ (h.setup6₀.component.1.trans inf_le_right))
      (inf_le_inf_right _ h.H₁_le_H₀)
  have hc₁ := isComponentOf_map (isComponentOf_subgroupOf hc₀ inf_le_left) f hf
  have hX : ((bbH₁ G L z v ⊓ Subgroup.centralizer (Subgroup.zpowers z : Set (GLV V))).subgroupOf
      (bbH₁ G L z v)).map f =
      f.range ⊓ Subgroup.centralizer (Subgroup.zpowers (f z₁) : Set (Equiv.Perm (Fin N))) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
      have hgz : z₁ ^ k * g = g * z₁ ^ k := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow, hz₁]
        exact Subgroup.mem_centralizer_iff.1 hg.2 _ (Subgroup.zpow_mem_zpowers z k)
      rw [← map_zpow f z₁ k, ← map_mul f, ← map_mul f, hgz]
    · rintro _ ⟨⟨g, rfl⟩, hc⟩
      refine ⟨g, ⟨g.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
      have h1 : f z₁ * f g = f g * f z₁ :=
        Subgroup.mem_centralizer_iff.1 hc _ (Subgroup.mem_zpowers _)
      rw [← map_mul f, ← map_mul f] at h1
      have h2 : z * (g : GLV V) = g * z := by
        have := congrArg Subtype.val (hf h1)
        rwa [Subgroup.coe_mul, Subgroup.coe_mul, hz₁] at this
      exact (Commute.zpow_left h2 k).eq
  rw [hX] at hc₁
  have hX₁ : alternatingGroup (Fin N) ⊓ Subgroup.centralizer
      (Subgroup.zpowers (f z₁) : Set (Equiv.Perm (Fin N))) ≤
      f.range ⊓ Subgroup.centralizer (Subgroup.zpowers (f z₁) : Set (Equiv.Perm (Fin N))) :=
    inf_le_inf_right _ (hA ▸ Subgroup.map_le_range f _)
  obtain ⟨h5, hK⟩ := eq_altOn_of_isComponentOf hR hX₁ inf_le_right hc₁
  have hset : {i | ∀ r ∈ Subgroup.zpowers (f z₁), r i = i} = {i | f z₁ i = i} :=
    Set.ext fun i => fixed_zpowers_iff (f z₁) i
  rw [hset] at hK
  refine ⟨?_, hK⟩
  have hcard : Nat.card {i : Fin N // ∀ r ∈ Subgroup.zpowers (f z₁), r i = i} =
      Nat.card {i : Fin N // f z₁ i = i} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun i => fixed_zpowers_iff (f z₁) i)
  rwa [hcard] at h5

theorem card_fix_eq {N n : ℕ} (hn : 6 ≤ n) (f : ↥(bbH₁ G L z v) →* Equiv.Perm (Fin N))
    (hf : Function.Injective f)
    (hA : ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map f = alternatingGroup (Fin N))
    (eL : ↥((L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) ≃*
      alternatingGroup (Fin n)) :
    Fintype.card {i : Fin N // f ⟨z, h.z_mem_H₁⟩ i = i} = n := by
  obtain ⟨h5, hK⟩ := h.map_L_eq_altOn f hf hA
  have c1 : Nat.card ↥((L.subgroupOf (bbH₁ G L z v)).map
      (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) = Nat.card ↥(L.subgroupOf (bbH₁ G L z v)) :=
    Subgroup.card_map_of_injective h.injective
  have c2 : Nat.card ↥((L.subgroupOf (bbH₁ G L z v)).map f) =
      Nat.card ↥(L.subgroupOf (bbH₁ G L z v)) := Subgroup.card_map_of_injective hf
  rw [hK] at c2
  have c3 : Nat.card (alternatingGroup (Fin n)) = Nat.card ↥((L.subgroupOf (bbH₁ G L z v)).map
      (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) := (Nat.card_congr eL.toEquiv).symm
  have h5' : 2 ≤ Fintype.card {i : Fin N // f ⟨z, h.z_mem_H₁⟩ i = i} := by
    rw [← Nat.card_eq_fintype_card]
    omega
  have c4 := two_mul_card_altOn (f ⟨z, h.z_mem_H₁⟩) h5'
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have c5 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hfact : (Fintype.card {i : Fin N // f ⟨z, h.z_mem_H₁⟩ i = i}).factorial = n.factorial := by
    rw [← c4, ← c5, c3, c1, c2]
  exact (Nat.factorial_inj (by omega)).1 hfact

theorem k_eq_one {n k : ℕ} (hn : 6 ≤ n) (hk : 1 ≤ k)
    (eL : Nonempty (↥((L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) ≃*
      alternatingGroup (Fin n)))
    (hheart : IsAltHeartFor (layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range)
      (n + 2 * k)) : k = 1 := by
  obtain ⟨eL⟩ := eL
  obtain ⟨φA, -, -⟩ := hheart
  have hN : 7 ≤ n + 2 * k := by omega
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥(bbH₁ G L z v) →* Equiv.Perm (Fin (n + 2 * k)),
      χ = h.chi hN φA := ⟨_, rfl⟩
  have hinj : Function.Injective χ := hχ ▸ h.chi_injective hN φA
  have hA : ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map χ = alternatingGroup (Fin (n + 2 * k)) :=
    hχ ▸ h.chi_map_L₀ hN φA
  have hcard := h.card_fix_eq hn χ hinj hA eL
  obtain ⟨-, hK⟩ := h.map_L_eq_altOn χ hinj hA
  have hsupp := card_fix_add_card_support (χ ⟨z, h.z_mem_H₁⟩)
  rw [hcard] at hsupp
  by_contra hk1
  obtain ⟨A, hAs, hA4⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (χ ⟨z, h.z_mem_H₁⟩).support.card by omega)
  obtain ⟨E, hE4, hEA, hEfix, hEsq, hEcomm⟩ := exists_four_group hA4
  have hEL : ∀ e ∈ E, ∀ l ∈ L.subgroupOf (bbH₁ G L z v), e * χ l = χ l * e := by
    intro e he l hl
    have hl' : χ l ∈ altOn {i | χ ⟨z, h.z_mem_H₁⟩ i = i} := hK ▸ ⟨l, hl, rfl⟩
    refine (Equiv.Perm.Disjoint.commute fun i => ?_).eq
    by_cases hi : i ∈ A
    · right
      have hmov : χ ⟨z, h.z_mem_H₁⟩ i ≠ i := Equiv.Perm.mem_support.1 (hAs hi)
      exact (mem_fixingSubgroup_iff _).1 hl'.2 i hmov
    · left
      exact hEfix e he i hi
  let E₁ : Subgroup ↥(bbH₁ G L z v) := E.comap χ
  let E₂ : Subgroup (GLV V) := E₁.map (bbH₁ G L z v).subtype
  have hErange : E ≤ χ.range := hEA.trans (hA ▸ Subgroup.map_le_range χ _)
  have hE₂4 : Nat.card E₂ = 4 := by
    rw [Subgroup.card_map_of_injective (bbH₁ G L z v).subtype_injective, ← hE4,
      ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hErange]
  have hE₂le : E₂ ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨h.H₁_le_G g.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hlH : l ∈ bbH₁ G L z v := h.L_le_H₁ hl
    have h1 := hEL (χ g) hg ⟨l, hlH⟩ hl
    rw [← map_mul χ, ← map_mul χ] at h1
    exact (congrArg Subtype.val (hinj h1)).symm
  have hE₂ab : IsElemAbelian 2 E₂ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨g, hg, rfl⟩⟩ := a
      obtain ⟨_, ⟨g', hg', rfl⟩⟩ := b
      have h1 := hEcomm (χ g) hg (χ g') hg'
      rw [← map_mul χ, ← map_mul χ] at h1
      have h2 : (g : GLV V) * g' = g' * g := congrArg Subtype.val (hinj h1)
      exact Subtype.ext h2
    · rintro _ ⟨g, hg, rfl⟩
      have h1 := hEsq (χ g) hg
      rw [← map_mul χ, ← map_one χ] at h1
      rw [sq]
      exact congrArg Subtype.val (hinj h1)
  have h2 := two_le_pRank hE₂le hE₂ab hE₂4
  rw [h.rank] at h2
  omega

theorem caseIData {n : ℕ} (hn : 6 ≤ n)
    (eL : Nonempty (↥((L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) ≃*
      alternatingGroup (Fin n)))
    (hheart : IsAltHeartFor (layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) (n + 2)) :
    ∃ ψ : ↥(bbH₁ G L z v) ≃* Equiv.Perm (Fin (n + 2)), CaseIData G L z v (bbH₁ G L z v) n ψ := by
  obtain ⟨eL⟩ := eL
  obtain ⟨φA, ψW, hψW⟩ := hheart
  have hN : 7 ≤ n + 2 := by omega
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(bbH₁ G L z v) →* GLV (Sect (bbW₀ G L v) (bbW₁ G L v)),
      φ = sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥(bbH₁ G L z v) →* Equiv.Perm (Fin (n + 2)),
      χ = h.chi hN φA := ⟨_, rfl⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ↥(bbH₁ G L z v), z₁ = ⟨z, h.z_mem_H₁⟩ := ⟨_, rfl⟩
  have hinj : Function.Injective χ := hχ ▸ h.chi_injective hN φA
  have hA : ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map χ = alternatingGroup (Fin (n + 2)) :=
    hχ ▸ h.chi_map_L₀ hN φA
  have hequiv : ∀ g y, ψW (φ g y) = altAct (χ g) (ψW y) := fun g y => by
    rw [hφ, hχ]
    exact h.chi_equivariant hN φA ψW hψW g y
  have hcard := h.card_fix_eq hn χ hinj hA eL
  have hsupp := card_fix_add_card_support (χ ⟨z, h.z_mem_H₁⟩)
  rw [hcard] at hsupp
  obtain ⟨a, b, hab, hσ⟩ := Equiv.Perm.card_support_eq_two.1 (show
    (χ ⟨z, h.z_mem_H₁⟩).support.card = 2 by omega)
  have hb' : Equiv.swap 0 a b ≠ 0 := by
    intro hb0
    apply hab
    have := (Equiv.swap 0 a).injective (hb0.trans (Equiv.swap_apply_right 0 a).symm)
    exact this.symm
  let π : Equiv.Perm (Fin (n + 2)) := Equiv.swap 1 (Equiv.swap 0 a b) * Equiv.swap 0 a
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp [Fin.ext_iff]
  have hπa : π a = 0 := by
    show Equiv.swap 1 (Equiv.swap 0 a b) (Equiv.swap 0 a a) = 0
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne h01 hb'.symm]
  have hπb : π b = 1 := by
    show Equiv.swap 1 (Equiv.swap 0 a b) (Equiv.swap 0 a b) = 1
    rw [Equiv.swap_apply_right]
  let ψ₀ : ↥(bbH₁ G L z v) →* Equiv.Perm (Fin (n + 2)) := (MulAut.conj π).toMonoidHom.comp χ
  have hψ₀ : ∀ g, ψ₀ g = π * χ g * π⁻¹ := fun g => rfl
  have hψ₀z : ψ₀ z₁ = Equiv.swap 0 1 := by
    rw [hψ₀, hz₁, hσ, conj_swap, hπa, hπb]
  have hψ₀inj : Function.Injective ψ₀ := (MulAut.conj π).injective.comp hinj
  have hψ₀A : ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map ψ₀ =
      alternatingGroup (Fin (n + 2)) := by
    rw [← Subgroup.map_map, hA, map_conj_alternatingGroup]
  have hψ₀surj : Function.Surjective ψ₀ := by
    rw [← MonoidHom.range_eq_top]
    refine eq_top_of_alternatingGroup_le (hψ₀A ▸ Subgroup.map_le_range ψ₀ _)
      ⟨z₁, hψ₀z⟩ ?_
    rw [Equiv.Perm.sign_swap h01]
  let ψ : ↥(bbH₁ G L z v) ≃* Equiv.Perm (Fin (n + 2)) :=
    MulEquiv.ofBijective ψ₀ ⟨hψ₀inj, hψ₀surj⟩
  have hψψ₀ : ψ.toMonoidHom = ψ₀ := MonoidHom.ext fun _ => rfl
  refine ⟨ψ, ?_⟩
  have hset : {i : Fin (n + 2) | ψ₀ ⟨z, h.z_mem_H₁⟩ i = i} = {i | i ≠ 0 ∧ i ≠ 1} := by
    rw [← hz₁, hψ₀z]
    ext i
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hi
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · rw [h0, Equiv.swap_apply_left] at hi
        exact h01 hi.symm
      · rw [h1, Equiv.swap_apply_right] at hi
        exact h01 hi
    · rintro ⟨h0, h1⟩
      exact Equiv.swap_apply_of_ne_of_ne h0 h1
  have hq : CFSG.Open.IsQuasisimple ↥(bbL₀ G L v) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (((Subgroup.subgroupOfEquivOfLe h.L₀_le_H₁).symm.trans
        (((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).equivMapOfInjective χ hinj)).trans
        (MulEquiv.subgroupCongr hA))
      (CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup (by omega))
  refine
    { le := h.H₁_le_H₀
      six_le := hn
      z_mem := h.z_mem_H₁
      ψ_z := by
        show ψ₀ ⟨z, h.z_mem_H₁⟩ = _
        rw [← hz₁, hψ₀z]
      L_le := h.L_le_H₁
      ψ_L := by
        rw [hψψ₀, (h.map_L_eq_altOn ψ₀ hψ₀inj hψ₀A).2, hset]
      ψ_H := by
        rw [hψψ₀, ← hψ₀A, Subgroup.comap_map_eq_self_of_injective hψ₀inj,
          Subgroup.map_subgroupOf_eq_of_le h.L₀_le_H₁]
      component := ⟨h.L₀_le_H₀, h.isSubnormal_L₀, hq⟩
      heart := ?_ }
  let mk : ↥(bbW₁ G L v) →+ Sect (bbW₀ G L v) (bbW₁ G L v) :=
    ((bbW₀ G L v).comap (bbW₁ G L v).subtype).mkQ.toAddMonoidHom
  let β : ↥(bbW₁ G L v) →+ altHeart (n + 2) := ((altAct π).comp ψW.toAddMonoidHom).comp mk
  have hβ : ∀ w, β w = altAct π (ψW (Submodule.Quotient.mk w)) := fun _ => rfl
  refine ⟨β, fun x => ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (ψW.symm (altAct π⁻¹ x))
    refine ⟨w, ?_⟩
    rw [hβ, hw, AddEquiv.apply_symm_apply, altAct_apply_inv]
  · ext w
    rw [AddMonoidHom.mem_ker, hβ, Submodule.mem_toAddSubgroup, Submodule.mem_comap]
    constructor
    · intro h0
      have h1 := congrArg (altAct π⁻¹) h0
      rw [altAct_inv_apply, map_zero, AddEquiv.map_eq_zero_iff,
        Submodule.Quotient.mk_eq_zero] at h1
      exact h1.1
    · intro h0
      have h1 : (Submodule.Quotient.mk w : Sect (bbW₀ G L v) (bbW₁ G L v)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 ⟨h0, w.2⟩
      rw [h1, map_zero, map_zero]
  · intro g w w' hww' x hx
    have hmk : (Submodule.Quotient.mk w' : Sect (bbW₀ G L v) (bbW₁ G L v)) =
        φ g (Submodule.Quotient.mk w) := by
      rw [hφ, sectHom_mk]
      congr 1
      exact Subtype.ext hww'
    rw [hβ, hmk, hequiv, ← altAct_mk, ← hx, hβ]
    show altAct π (altAct (χ g) (ψW _)) = altAct (π * χ g * π⁻¹) (altAct π (ψW _))
    rw [← altAct_mul, ← altAct_mul]
    congr 1
    group

end Hyp

end BranchB

end CFSG.CGT.Foote82
