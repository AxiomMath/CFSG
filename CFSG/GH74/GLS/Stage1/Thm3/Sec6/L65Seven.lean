module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65AbsHyp

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
open scoped commutatorElement

section Transfer

variable {F C : Type*} [Group F] [Group C]

theorem isComponent_map_of_injective_of_normal (φ : F →* C) (hφ : Function.Injective φ)
    (hn : φ.range.Normal) {B : Subgroup F} (hB : CFSG.IsComponent B) :
    CFSG.IsComponent (B.map φ) := by
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv (B.equivMapOfInjective φ hφ) hB.1, ?_⟩
  have h1 : (B.map φ.rangeRestrict).IsSubnormal := hB.2.map φ.rangeRestrict_surjective
  have h2 := Subgroup.IsSubnormal.trans' h1 hn.isSubnormal
  rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2

theorem isComponent_comap_of_injective (φ : F →* C) (hφ : Function.Injective φ)
    {B : Subgroup C} (hle : B ≤ φ.range) (hB : CFSG.IsComponent B) :
    CFSG.IsComponent (B.comap φ) := by
  refine ⟨?_, hB.2.comap φ⟩
  exact LocalCores.isQuasisimple_of_mulEquiv
    (((B.comap φ).equivMapOfInjective φ hφ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hle))).symm hB.1

end Transfer

section CentralizerNormalizes

variable {X : Type} [Group X] [Finite X]

theorem centralizer_le_normalizer_of_unique_component {s : X} {L A : Subgroup X}
    (hL : CFSG.IsComponent L) (hAL : A ≤ L) (hAs : A ≤ centralizer ({s} : Set X))
    (hAc : CFSG.IsComponent (A.subgroupOf (centralizer ({s} : Set X))))
    (huniq : ∀ B : Subgroup X, B ≤ centralizer ({s} : Set X) →
      CFSG.IsComponent (B.subgroupOf (centralizer ({s} : Set X))) → B = A) :
    centralizer ({s} : Set X) ≤ normalizer (L : Set X) := by
  intro c hc
  set C := centralizer ({s} : Set X) with hCdef
  have hAq : CFSG.IsQuasisimple ↥A :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAs) hAc.1
  have hAperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp hAq.1
  have hAbot : A ≠ ⊥ := by
    intro h
    have : Nontrivial ↥A := LocalCores.isQuasisimple_nontrivial hAq
    exact (Subgroup.nontrivial_iff_ne_bot A).mp this h
  let c' : ↥C := ⟨c, hc⟩
  have hB := LocalCores.isComponent_map_mulEquiv (MulAut.conj c') hAc
  have hBle : A.map (MulAut.conj c).toMonoidHom ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    exact C.mul_mem (C.mul_mem hc (hAs ha)) (C.inv_mem hc)
  have hBeq : (A.subgroupOf C).map (MulAut.conj c').toMonoidHom =
      (A.map (MulAut.conj c).toMonoidHom).subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
    · rintro ⟨a, ha, hax⟩
      exact ⟨⟨a, hAs ha⟩, ha, Subtype.ext hax⟩
  have hBA : A.map (MulAut.conj c).toMonoidHom = A := huniq _ hBle (hBeq ▸ hB)
  have hL' := LocalCores.isComponent_map_mulEquiv (MulAut.conj c) hL
  have hAL' : A ≤ L.map (MulAut.conj c).toMonoidHom := by
    calc A = A.map (MulAut.conj c).toMonoidHom := hBA.symm
      _ ≤ _ := Subgroup.map_mono hAL
  rcases LocalCores.distinct_components_commute hL hL' with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
  · exfalso
    have h1 : ⁅A, A⁆ ≤ ⁅L, L.map (MulAut.conj c).toMonoidHom⁆ := Subgroup.commutator_mono hAL hAL'
    rw [h] at h1
    exact hAbot (by rw [← hAperf]; exact le_bot_iff.mp h1)

end CentralizerNormalizes

section FixedComponent

variable {X : Type} [Group X]

@[expose] def embCL (L C : Subgroup X) : ↥(C.subgroupOf L) →* ↥C where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem embCL_injective (L C : Subgroup X) : Function.Injective (embCL L C) := by
  intro x y h
  have h' : x.1.1 = y.1.1 := congrArg (fun z : ↥C => (z : X)) h
  exact Subtype.ext (Subtype.ext h')

theorem embCL_range_normal {L C : Subgroup X} (hCL : C ≤ normalizer (L : Set X)) :
    (embCL L C).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  have hgx : (g : X) * x.1.1 * (g : X)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hCL g.2) _).mp x.1.2
  refine ⟨⟨⟨(g : X) * x.1.1 * (g : X)⁻¹, hgx⟩, ?_⟩, rfl⟩
  exact C.mul_mem (C.mul_mem g.2 x.2) (C.inv_mem g.2)

theorem isComponent_subgroupOf_fixed {L C A : Subgroup X} (hAL : A ≤ L)
    (hAc : CFSG.IsComponent (A.subgroupOf C)) :
    CFSG.IsComponent ((A.subgroupOf L).subgroupOf (C.subgroupOf L)) := by
  have h : (A.subgroupOf L).subgroupOf (C.subgroupOf L) = (A.subgroupOf C).comap (embCL L C) :=
    rfl
  rw [h]
  refine isComponent_comap_of_injective _ (embCL_injective L C) ?_ hAc
  intro x hx
  exact ⟨⟨⟨x.1, hAL hx⟩, x.2⟩, rfl⟩

theorem eq_of_isComponent_subgroupOf_fixed {L C A : Subgroup X}
    (hCL : C ≤ normalizer (L : Set X))
    (huniq : ∀ B : Subgroup X, B ≤ C → CFSG.IsComponent (B.subgroupOf C) → B = A)
    (B' : Subgroup ↥L) (hB' : B' ≤ C.subgroupOf L)
    (hc : CFSG.IsComponent (B'.subgroupOf (C.subgroupOf L))) : B' = A.subgroupOf L := by
  have h1 := isComponent_map_of_injective_of_normal (embCL L C) (embCL_injective L C)
    (embCL_range_normal hCL) hc
  have hle : B'.map L.subtype ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB' hx
  have heq : (B'.subgroupOf (C.subgroupOf L)).map (embCL L C) =
      (B'.map L.subtype).subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
    · rintro ⟨l, hl, hlx⟩
      have hlx' : (l : X) = (x : X) := hlx
      refine ⟨⟨l, by rw [Subgroup.mem_subgroupOf, hlx']; exact x.2⟩, hl, ?_⟩
      exact Subtype.ext hlx'
  have hBA : B'.map L.subtype = A := huniq _ hle (heq ▸ h1)
  calc B' = (B'.map L.subtype).comap L.subtype :=
        (Subgroup.comap_map_eq_self_of_injective L.subtype_injective B').symm
    _ = A.comap L.subtype := by rw [hBA]
    _ = A.subgroupOf L := rfl

end FixedComponent

section CenterTransport

variable {A B : Type*} [Group A] [Group B]

theorem natCard_center_eq_of_mulEquiv (e : A ≃* B) : Nat.card (center A) = Nat.card (center B) := by
  rw [← Subgroup.map_center_eq e]
  exact (Subgroup.card_map_of_injective e.injective).symm

theorem nonempty_centerQuot_equiv_of_mulEquiv {S : Type*} [Group S] (e : A ≃* B)
    (h : Nonempty (B ⧸ center B ≃* S)) : Nonempty (A ⧸ center A ≃* S) :=
  h.elim fun f => ⟨(QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)).trans f⟩

end CenterTransport

section Hypothesis

variable {X : Type} [Group X] [Finite X]

theorem ivk714Hyp_centralizer {s : X} {L A : Subgroup X}
    (hL : CFSG.IsQuasisimple ↥L) (hsL : s ∈ normalizer (L : Set X))
    (hCL : centralizer ({s} : Set X) ≤ normalizer (L : Set X))
    (hAL : A ≤ L) (hAs : A ≤ centralizer ({s} : Set X))
    (hA7 : Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 7)))
    (hZodd : Odd (Nat.card (center ↥A)))
    (hAc : CFSG.IsComponent (A.subgroupOf (centralizer ({s} : Set X))))
    (huniq : ∀ B : Subgroup X, B ≤ centralizer ({s} : Set X) →
      CFSG.IsComponent (B.subgroupOf (centralizer ({s} : Set X))) → B = A) :
    Ivk714Hyp (↥L ⧸ center ↥L) (centerQuotAut (L.normalizerMonoidHom ⟨s, hsL⟩)) := by
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨s, hsL⟩ with hα
  have hF : fixedSubgroup ↥L α = (centralizer ({s} : Set X)).subgroupOf L := by
    ext x
    show α x = x ↔ (x : X) ∈ centralizer ({s} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    show s * (x : X) * s⁻¹ = (x : X) ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hA7' : Nonempty
      (↥(A.subgroupOf L) ⧸ center ↥(A.subgroupOf L) ≃* alternatingGroup (Fin 7)) :=
    nonempty_centerQuot_equiv_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAL) hA7
  have hZodd' : Odd (Nat.card (center ↥(A.subgroupOf L))) := by
    rw [natCard_center_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAL)]
    exact hZodd
  refine ivk714Hyp_of_unique_component hL α (A.subgroupOf L) ?_ hA7' hZodd' ?_ ?_
  · rw [hF]
    intro x hx
    exact hAs hx
  · rw [hF]
    exact isComponent_subgroupOf_fixed hAL hAc
  · rw [hF]
    intro B' hB' hc
    exact eq_of_isComponent_subgroupOf_fixed hCL huniq B' hB' hc

end Hypothesis

section Counting

@[expose] noncomputable def centerQuotAutHom (L : Type) [Group L] :
    MulAut L →* MulAut (L ⧸ center L) where
  toFun := centerQuotAut
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [centerQuotAut_apply_mk]
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [centerQuotAut_apply_mk]

variable {X : Type} [Group X]

theorem kz_le_range {s : X} {L : Subgroup X} (hsL : s ∈ normalizer (L : Set X)) :
    kz (↥L ⧸ center ↥L) (centerQuotAut (L.normalizerMonoidHom ⟨s, hsL⟩)) ≤
      ((centerQuotAutHom ↥L).comp L.normalizerMonoidHom).range := by
  refine sup_le ?_ ?_
  · rintro _ ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨x, Subgroup.le_normalizer x.2⟩, ?_⟩
    ext y
    induction y using QuotientGroup.induction_on with
    | H y =>
      show centerQuotAut (L.normalizerMonoidHom ⟨x, _⟩) (QuotientGroup.mk y) = _
      rw [centerQuotAut_apply_mk]
      rfl
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨s, hsL⟩, rfl⟩

variable [Finite X]

theorem centerQuotAut_eq_one_of_h714 (h714 : IVK_7_14_g4) {s w : X}
    (hs : s * s = 1) (hw : w ∈ center X) (hw2 : orderOf w = 2) (h8 : ¬ 2 ^ 8 ∣ Nat.card X)
    {L : Subgroup X} (hLq : CFSG.IsQuasisimple ↥L) (hsL : s ∈ normalizer (L : Set X))
    (hGH : GHList (↥L ⧸ center ↥L))
    (hHyp : Ivk714Hyp (↥L ⧸ center ↥L) (centerQuotAut (L.normalizerMonoidHom ⟨s, hsL⟩))) :
    centerQuotAut (L.normalizerMonoidHom ⟨s, hsL⟩) = 1 := by
  by_contra hne
  set Φ : ↥(normalizer (L : Set X)) →* MulAut (↥L ⧸ center ↥L) :=
    (centerQuotAutHom ↥L).comp L.normalizerMonoidHom with hΦ
  set ζ := centerQuotAut (L.normalizerMonoidHom ⟨s, hsL⟩) with hζ
  have hζΦ : ζ = Φ ⟨s, hsL⟩ := rfl
  have hζ2 : ζ ^ 2 = 1 := by
    have h1 : (⟨s, hsL⟩ : ↥(normalizer (L : Set X))) ^ 2 = 1 :=
      Subtype.ext (by simpa [pow_two] using hs)
    rw [hζΦ, ← map_pow, h1, map_one]
  have hord : orderOf ζ = 2 := orderOf_eq_prime hζ2 hne
  have h2 : 2 ^ 7 ∣ Nat.card ↥(kz (↥L ⧸ center ↥L) ζ) :=
    (h714 (↥L ⧸ center ↥L) hLq.2.1 hGH ζ hord hHyp).2
  have hdvdrange : 2 ^ 7 ∣ Nat.card Φ.range :=
    h2.trans (Subgroup.card_dvd_of_le (kz_le_range hsL))
  have hwN : w ∈ normalizer (L : Set X) := Subgroup.center_le_normalizer _ hw
  have hw'ker : (⟨w, hwN⟩ : ↥(normalizer (L : Set X))) ∈ Φ.ker := by
    have h1 : (⟨w, hwN⟩ : ↥(normalizer (L : Set X))) ∈ (L.normalizerMonoidHom).ker := by
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      exact Subgroup.center_le_centralizer _ hw
    rw [MonoidHom.mem_ker] at h1 ⊢
    simp [hΦ, h1]
  have hdvdker : 2 ∣ Nat.card Φ.ker := by
    have := orderOf_dvd_natCard (⟨⟨w, hwN⟩, hw'ker⟩ : ↥Φ.ker)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hw2] at this
  have hcard := Subgroup.card_ker_mul_card_range Φ
  have hN : 2 ^ 8 ∣ Nat.card ↥(normalizer (L : Set X)) := by
    rw [← hcard]
    have e : (2 : ℕ) ^ 8 = 2 * 2 ^ 7 := by norm_num
    rw [e]
    exact Nat.mul_dvd_mul hdvdker hdvdrange
  exact h8 (hN.trans (Subgroup.card_subgroup_dvd_card _))

end Counting

section Perfect

theorem fixed_of_centerQuotAut_eq_one {L : Type} [Group L] (hL : Group.IsPerfect L)
    (α : MulAut L) (h : centerQuotAut α = 1) (l : L) : α l = l := by
  have hfix : ∀ x : L, (α x)⁻¹ * x ∈ center L := by
    intro x
    have h1 := congrArg (fun φ : MulAut (L ⧸ center L) => φ (QuotientGroup.mk x)) h
    simp only [centerQuotAut_apply_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.mp h1
  have hcomm : ⁅(⊤ : Subgroup L), ⊤⁆ ≤ fixedSubgroup L α := by
    rw [Subgroup.commutator_le]
    rintro x - y -
    have key : ⁅α x * ((α x)⁻¹ * x), α y * ((α y)⁻¹ * y)⁆ = ⁅α x, α y⁆ := by
      rw [AbsHyp.commutatorElement_mul_central_left (hfix x),
        AbsHyp.commutatorElement_mul_central_right (hfix y)]
    have e1 : α x * ((α x)⁻¹ * x) = x := by group
    have e2 : α y * ((α y)⁻¹ * y) = y := by group
    rw [e1, e2] at key
    show α ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement, key]
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = (⊤ : Subgroup L) := by
    rw [Group.isPerfect_def, _root_.commutator_def] at hL
    exact hL
  rw [htop] at hcomm
  exact hcomm (Subgroup.mem_top l : l ∈ (⊤ : Subgroup L))

end Perfect

theorem lemma_seven (h714 : IVK_7_14_g4) {X : Type} [Group X] [Finite X] {s w : X}
    (hs : s * s = 1) (hw : w ∈ center X) (hw2 : orderOf w = 2) (h8 : ¬ 2 ^ 8 ∣ Nat.card X)
    {L : Subgroup X} (hL : CFSG.IsComponent L) (hsL : s ∈ normalizer (L : Set X))
    (hGH : GHList (↥L ⧸ center ↥L)) {A : Subgroup X} (hAL : A ≤ L)
    (hAs : A ≤ centralizer ({s} : Set X))
    (hA7 : Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 7)))
    (hZodd : Odd (Nat.card (center ↥A)))
    (hAc : CFSG.IsComponent (A.subgroupOf (centralizer ({s} : Set X))))
    (huniq : ∀ B : Subgroup X, B ≤ centralizer ({s} : Set X) →
      CFSG.IsComponent (B.subgroupOf (centralizer ({s} : Set X))) → B = A) :
    ∀ l ∈ L, s * l = l * s := by
  intro l hl
  have hCL : centralizer ({s} : Set X) ≤ normalizer (L : Set X) :=
    centralizer_le_normalizer_of_unique_component hL hAL hAs hAc huniq
  have hHyp := ivk714Hyp_centralizer hL.1 hsL hCL hAL hAs hA7 hZodd hAc huniq
  have h1 := centerQuotAut_eq_one_of_h714 h714 hs hw hw2 h8 hL.1 hsL hGH hHyp
  have h2 := fixed_of_centerQuotAut_eq_one hL.1.1 _ h1 ⟨l, hl⟩
  have h3 : s * l * s⁻¹ = l := congrArg Subtype.val h2
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
