module

public import CFSG.GH74.GLS.NT44.RigidPairNormalization
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
import CFSG.GH74.Generic.BProg.B1.Lift0
import CFSG.GH74.GLS.NT44.ActualCover
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedLift

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.PerfectAutomorphisms

section Fixed

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem rac_normalizerMonoidHom_sq {I : Subgroup G} {v : G} (hv2 : v ^ 2 = 1)
    (hvI : v ∈ Subgroup.normalizer (I : Set G)) :
    (I.normalizerMonoidHom ⟨v, hvI⟩) ^ 2 = 1 := by
  have hv : (⟨v, hvI⟩ : Subgroup.normalizer (I : Set G)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hv2
  calc (I.normalizerMonoidHom ⟨v, hvI⟩) ^ 2
      = I.normalizerMonoidHom ((⟨v, hvI⟩ : Subgroup.normalizer (I : Set G)) ^ 2) :=
        (map_pow _ _ 2).symm
    _ = 1 := by rw [hv, map_one]

theorem range_inclusion_inf_centralizer_eq_fixSubgroup {I : Subgroup G} {v : G} (hv2 : v ^ 2 = 1)
    (hvI : v ∈ Subgroup.normalizer (I : Set G)) :
    ((QuotientGroup.mk' (pPrimeCore 2 ↥I)).comp
        (Subgroup.inclusion (inf_le_left :
          I ⊓ Subgroup.centralizer ({v} : Set G) ≤ I))).range =
      fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥I)
        (I.normalizerMonoidHom ⟨v, hvI⟩)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : MulAut ↥I := I.normalizerMonoidHom ⟨v, hvI⟩
  let N : Subgroup ↥I := pPrimeCore 2 ↥I
  let C : Subgroup G := I ⊓ Subgroup.centralizer ({v} : Set G)
  have hC : C ≤ I := inf_le_left
  change ((QuotientGroup.mk' N).comp (Subgroup.inclusion hC)).range =
    fixSubgroup (MulAut.mapQuotient N σ)
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    rw [mem_fixSubgroup]
    change (MulAut.mapQuotient N σ) (QuotientGroup.mk (Subgroup.inclusion hC y)) =
      QuotientGroup.mk (Subgroup.inclusion hC y)
    rw [MulAut.mapQuotient_mk]
    congr 1
    apply Subtype.ext
    rw [show ((σ (Subgroup.inclusion hC y)) : G) = v * (y : G) * v⁻¹ from
      Subgroup.normalizerMonoidHom_apply_apply_coe I ⟨v, hvI⟩ _]
    change v * (y : G) * v⁻¹ = (y : G)
    have hy : (y : G) * v = v * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp y.2.2
    rw [← hy]
    group
  · intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [mem_fixSubgroup] at hq
    change (MulAut.mapQuotient N σ) (QuotientGroup.mk k) = QuotientGroup.mk k at hq
    rw [MulAut.mapQuotient_mk] at hq
    have hx : σ k * k⁻¹ ∈ N := by
      simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hq
    have hNinv : ∀ n ∈ N, σ n ∈ N := by
      intro n hn
      have hmap : Subgroup.map σ.toMonoidHom N = N :=
        (Subgroup.characteristic_iff_map_eq.mp
          (CFSG.pPrimeCore_characteristic (p := 2) (G := ↥I))) σ
      rw [← hmap]
      exact Subgroup.mem_map_of_mem σ.toMonoidHom hn
    have hNodd : ¬ 2 ∣ Nat.card ↥N :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (by simpa [N] using
          (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥I)))
    obtain ⟨y, hyN, hyfix⟩ :=
      CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_lift
        σ (rac_normalizerMonoidHom_sq hv2 hvI) N inferInstance hNinv hNodd k hx
    have hycent : (y : G) ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe I ⟨v, hvI⟩ y
      rw [show σ y = y from hyfix] at hcoe
      have hcomm : v * (y : G) = (y : G) * v := by
        calc v * (y : G) = (v * (y : G) * v⁻¹) * v := by group
          _ = (y : G) * v := by conv_rhs => rw [hcoe]
      exact hcomm.symm
    refine ⟨⟨(y : G), y.2, hycent⟩, ?_⟩
    change ((QuotientGroup.mk' N) (Subgroup.inclusion hC
      ⟨(y : G), y.2, hycent⟩)) = QuotientGroup.mk k
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    change y * k⁻¹ ∈ N
    exact hyN

theorem not_two_dvd_card_ker_inclusion_inf_centralizer {I : Subgroup G} {v : G} :
    ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 ↥I)).comp
        (Subgroup.inclusion (inf_le_left :
          I ⊓ Subgroup.centralizer ({v} : Set G) ≤ I))).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.GH74.Generic.BProg.B1.not_two_dvd_card_ker_comp_mk _
    (Subgroup.inclusion_injective _) _
    (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card)

omit [Finite G] in
theorem isSubnormal_inf_centralizer_of_isPCompIn {x v : G} {I : Subgroup G}
    (hI : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) I) :
    ((I ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf
      (Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({v} : Set G))).IsSubnormal := by
  have h := (CFSG.GH74.Generic.BProg.B1.isSubnormal_of_isPCompIn hI).comap
    (Subgroup.inclusion (inf_le_left :
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G) ≤
        Subgroup.centralizer ({x} : Set G)))
  rwa [show Subgroup.comap
      (Subgroup.inclusion (inf_le_left :
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G) ≤
          Subgroup.centralizer ({x} : Set G)))
      (I.subgroupOf (Subgroup.centralizer ({x} : Set G))) =
      (I ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({v} : Set G)) from by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf]
      exact ⟨by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using hy, y.2.2⟩
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using hy.1] at h

private theorem rac_glaPLayer_fixSubgroup_eq_bot {x v : G} {I : Subgroup G}
    (hv2 : v ^ 2 = 1) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hI : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) I)
    (h99 : ∀ M : Subgroup G, ¬ IsPCompIn 2
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) M) :
    CFSG.Open.GLAPLayer 2 (fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥I)
      (I.normalizerMonoidHom ⟨v, hvI⟩))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨Lb, hLb⟩ : ∃ Lb, CFSG.Open.GLAPComponent 2 (fixSubgroup (MulAut.mapQuotient
      (pPrimeCore 2 ↥I) (I.normalizerMonoidHom ⟨v, hvI⟩))) Lb := by
    by_contra h
    push Not at h
    exact hne (by rw [CFSG.Open.GLAPLayer, sSup_eq_bot]; exact fun J hJ => (h J hJ).elim)
  have hLb' := (i183_glaPComponent_iff_isPComponent Nat.prime_two).1 hLb
  have hJb : IsPCompIn 2 ((QuotientGroup.mk' (pPrimeCore 2 ↥I)).comp
      (Subgroup.inclusion (inf_le_left :
        I ⊓ Subgroup.centralizer ({v} : Set G) ≤ I))).range Lb := by
    rw [range_inclusion_inf_centralizer_eq_fixSubgroup hv2 hvI]
    exact hLb'
  obtain ⟨hY, -⟩ := CFSG.GH74.Generic.BProg.B1.exists_isPCompIn_lift_of_odd_ker _
    not_two_dvd_card_ker_inclusion_inf_centralizer hJb
  exact h99 _ (CFSG.GH74.Generic.BProg.B1.isPCompIn_of_isSubnormal 2
    (inf_le_inf_right _ hI.1) (isSubnormal_inf_centralizer_of_isPCompIn hI) hY)

omit [Finite G] in
theorem mapQuotient_normalizerMonoidHom_eq_one_iff {I : Subgroup G} {t : G}
    (htI : t ∈ Subgroup.normalizer (I : Set G)) :
    MulAut.mapQuotient (pPrimeCore 2 ↥I) (I.normalizerMonoidHom ⟨t, htI⟩) = 1 ↔
      t ∈ centralizerSection I (pPrimeCoreOf 2 I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : MulAut ↥I := I.normalizerMonoidHom ⟨t, htI⟩
  let N : Subgroup ↥I := pPrimeCore 2 ↥I
  have hcoe : ∀ k : ↥I, ((k * (σ k)⁻¹ : ↥I) : G) = (k : G) * t * (k : G)⁻¹ * t⁻¹ := by
    intro k
    have hσ : ((σ k : ↥I) : G) = t * k * t⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe I ⟨t, htI⟩ _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ]
    group
  have hstep : ∀ k : ↥I, (QuotientGroup.mk (σ k) : ↥I ⧸ N) = QuotientGroup.mk k ↔
      (k : G) * t * (k : G)⁻¹ * t⁻¹ ∈ pPrimeCoreOf 2 I := by
    intro k
    have hN : (σ k)⁻¹ * k ∈ N ↔ k * (σ k)⁻¹ ∈ N := by
      constructor
      · intro h
        convert (inferInstance : N.Normal).conj_mem _ h k using 1
        group
      · intro h
        convert (inferInstance : N.Normal).conj_mem _ h k⁻¹ using 1
        group
    rw [QuotientGroup.eq, hN, pPrimeCoreOf, ← hcoe]
    constructor
    · intro h
      exact Subgroup.mem_map_of_mem I.subtype h
    · rintro ⟨n, hn, hn'⟩
      have hnk : n = k * (σ k)⁻¹ := Subtype.ext hn'
      rw [← hnk]
      exact hn
  constructor
  · intro h1
    refine ⟨htI, CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf htI, fun k hk => ?_⟩
    rw [commutatorElement_def]
    refine (hstep ⟨k, hk⟩).1 ?_
    have h := congrArg (fun f : MulAut (↥I ⧸ N) => f (QuotientGroup.mk (⟨k, hk⟩ : ↥I))) h1
    rw [MulAut.mapQuotient_mk, MulAut.one_apply] at h
    exact h
  · rintro ⟨-, -, hc⟩
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.mapQuotient_mk, MulAut.one_apply]
      have hk := hc k k.2
      rw [commutatorElement_def] at hk
      exact (hstep k).2 hk

omit [Finite G] in
private theorem rac_mem_cxK_of_mapQuotient_eq_one {x v : G} {I : Subgroup G}
    (hvx : v * x = x * v) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (h1 : MulAut.mapQuotient (pPrimeCore 2 ↥I) (I.normalizerMonoidHom ⟨v, hvI⟩) = 1) :
    v ∈ CxK x I :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr hvx,
    (mapQuotient_normalizerMonoidHom_eq_one_iff hvI).mp h1⟩

omit [Finite G] in
theorem mem_cxK_self_of_isPCompIn {v : G} {L : Subgroup G}
    (hL : IsPCompIn 2 (Subgroup.centralizer ({v} : Set G)) L) : v ∈ CxK v L := by
  have hLC : L ≤ Subgroup.centralizer ({v} : Set G) := hL.1
  have hcomm : ∀ l : G, l ∈ L → l * v = v * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
  have hvL : v ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun l hl => hcomm l hl)
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hvL,
    CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf hvL, ?_⟩
  intro k hk
  rw [commutatorElement_def, show k * v * k⁻¹ * v⁻¹ = 1 from by rw [hcomm k hk]; group]
  exact Subgroup.one_mem _

omit [Finite G] in
private theorem rac_mapQuotient_ne_one {x v : G} {I L : Subgroup G} (hvx : v * x = x * v)
    (hv2 : orderOf v = 2) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hL : IsPCompIn 2 (Subgroup.centralizer ({v} : Set G)) L)
    (hodd : Odd (Nat.card ↥(CxK x I ⊓ CxK v L))) :
    MulAut.mapQuotient (pPrimeCore 2 ↥I) (I.normalizerMonoidHom ⟨v, hvI⟩) ≠ 1 := by
  intro h1
  have hmem : v ∈ CxK x I ⊓ CxK v L :=
    ⟨rac_mem_cxK_of_mapQuotient_eq_one hvx hvI h1, mem_cxK_self_of_isPCompIn hL⟩
  have hdvd : orderOf v ∣ Nat.card ↥(CxK x I ⊓ CxK v L) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  rw [hv2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end Fixed

section Classes

theorem congr_centerQuotientHom_comp_apply {K H : Type} [Group K] [Group H]
    (b : (K ⧸ Subgroup.center K) ≃* H) (α : MulAut K) (k : K) :
    (b.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) (α k) =
      MulAut.congr b (centerQuotientHom K α)
        ((b.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) k) := by
  change b ((QuotientGroup.mk' (Subgroup.center K)) (α k)) =
    MulAut.congr b (centerQuotientHom K α)
      (b ((QuotientGroup.mk' (Subgroup.center K)) k))
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  exact (congrArg b (onCenterQuotient_apply_mk α k)).symm

private theorem rac_glaPLayer_fixSubgroup_congr_eq_bot {K H : Type} [Group K] [Group H]
    [Finite K] [Finite H] (b : (K ⧸ Subgroup.center K) ≃* H) (α : MulAut K)
    (hα : CFSG.Open.GLAPLayer 2 (fixSubgroup α) = ⊥) :
    CFSG.Open.GLAPLayer 2 (fixSubgroup (MulAut.congr b (centerQuotientHom K α))) = ⊥ := by
  have hker : (b.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker ≤
      Subgroup.center K := by
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hk
    have h1 : (QuotientGroup.mk' (Subgroup.center K)) k = 1 := b.injective (by simpa using hk)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h := map_glaPLayer_fixSubgroup_eq
    (b.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) hker α
    (MulAut.congr b (centerQuotientHom K α)) (congr_centerQuotientHom_comp_apply b α)
    (b.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))) Nat.prime_two
  rw [← h, hα, Subgroup.map_bot]

private theorem rac_glaPLayer_fixSubgroup_ne_bot_of_isConj {H : Type} [Group H] [Finite H]
    {β δ : MulAut H} (h : IsConj β δ) (hδ : CFSG.Open.GLAPLayer 2 (fixSubgroup δ) ≠ ⊥) :
    CFSG.Open.GLAPLayer 2 (fixSubgroup β) ≠ ⊥ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hker : c.toMonoidHom.ker ≤ Subgroup.center H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : x = 1 := c.injective (by simpa using hx)
    rw [hx1]
    exact Subgroup.one_mem _
  have hαβ : ∀ k : H, c.toMonoidHom (β k) = δ (c.toMonoidHom k) := by
    intro k
    have h := congrArg (fun f : MulAut H => f (c k)) hc
    simpa [MulAut.mul_apply] using h
  intro hβ
  have h := map_glaPLayer_fixSubgroup_eq c.toMonoidHom hker β δ hαβ
    (MulEquiv.surjective c) Nat.prime_two
  rw [hβ, Subgroup.map_bot] at h
  exact hδ h.symm

private theorem rac_glaPLayer_fixSubgroup_conjAutS_ne_bot
    {r : R}
    (hsimple : IsSimpleGroup ↥(Subgroup.centralizer ({(r : Equiv.Perm (Fin 42))} :
      Set (Equiv.Perm (Fin 42))) ⊓ S))
    (hnonab : ∃ a b : ↥(Subgroup.centralizer ({(r : Equiv.Perm (Fin 42))} :
      Set (Equiv.Perm (Fin 42))) ⊓ S), a * b ≠ b * a)
    (heven : 2 ∣ Nat.card ↥(Subgroup.centralizer ({(r : Equiv.Perm (Fin 42))} :
      Set (Equiv.Perm (Fin 42))) ⊓ S)) :
    CFSG.Open.GLAPLayer 2 (fixSubgroup (conjAutS r)) ≠ ⊥ := by
  set C : Subgroup (Equiv.Perm (Fin 42)) :=
    Subgroup.centralizer ({(r : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ S with hC
  set A : Subgroup ↥S := fixSubgroup (conjAutS r) with hA
  have hmem : ∀ t : ↥S, t ∈ A ↔ (t : Equiv.Perm (Fin 42)) ∈ C := by
    intro t
    rw [hA, mem_fixSubgroup, hC]
    constructor
    · intro ht
      have h := congrArg (fun u : ↥S => (u : Equiv.Perm (Fin 42))) ht
      rw [conjAutS_apply] at h
      have h' : (r : Equiv.Perm (Fin 42)) * (t : Equiv.Perm (Fin 42)) =
          (t : Equiv.Perm (Fin 42)) * (r : Equiv.Perm (Fin 42)) := by
        calc (r : Equiv.Perm (Fin 42)) * (t : Equiv.Perm (Fin 42))
            = ((r : Equiv.Perm (Fin 42)) * (t : Equiv.Perm (Fin 42)) *
                (r : Equiv.Perm (Fin 42))⁻¹) * (r : Equiv.Perm (Fin 42)) := by group
          _ = (t : Equiv.Perm (Fin 42)) * (r : Equiv.Perm (Fin 42)) := by rw [h]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr h'.symm, t.2⟩
    · rintro ⟨hc, -⟩
      apply Subtype.ext
      rw [conjAutS_apply]
      have hc' : (t : Equiv.Perm (Fin 42)) * (r : Equiv.Perm (Fin 42)) =
          (r : Equiv.Perm (Fin 42)) * (t : Equiv.Perm (Fin 42)) :=
        Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [← hc']
      group
  have hmap : A.map S.subtype = C := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (hmem t).mp ht
    · intro hx
      exact ⟨⟨x, hx.2⟩, (hmem ⟨x, hx.2⟩).mpr hx, rfl⟩
  let e : ↥A ≃* ↥C :=
    (Subgroup.equivMapOfInjective A S.subtype S.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hCsimple : IsSimpleGroup ↥C := hsimple
  have hAsimple : IsSimpleGroup ↥A := MulEquiv.isSimpleGroup e
  have hncA : ∃ a b : ↥A, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have h2A : 2 ∣ Nat.card ↥A := by
    rw [Nat.card_congr e.toEquiv]
    exact heven
  have hnormal : (A.subgroupOf A).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hAle : A ≤ CFSG.Open.GLAPLayer 2 A :=
    le_glaPLayer_of_normal_simple (p := 2) (Y := A) (A := A) Nat.prime_two le_rfl hnormal hncA h2A
  have hAne : A ≠ ⊥ := by
    intro hAb
    have h1 : Nat.card ↥A = 1 := by rw [hAb, Subgroup.card_bot]
    rw [h1] at h2A
    obtain ⟨k, hk⟩ := h2A
    omega
  intro hbot
  rw [hbot] at hAle
  exact hAne (le_bot_iff.mp hAle)

private theorem rac_isConj_of_sq_eq_one {β : MulAut S}
    (h2 : β ^ 2 = 1) (h1 : β ≠ 1) :
    IsConj β (conjAutS r₁R) ∨ IsConj β (conjAutS r₂R) ∨ IsConj β (conjAutS r₃R) ∨
      IsConj β (conjAutS r₄R) := by
  obtain ⟨ρ, rfl⟩ := conjAutS_surjective β
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' : orderOf (conjAutS ρ) = 2 := orderOf_eq_prime h2 h1
  have hρ : orderOf ρ = 2 := by
    rw [← orderOf_injective conjAutS conjAutS_injective ρ]
    exact h2'
  rcases (orderOf_eq_two_iff ρ).mp hρ with h | h | h | h
  · exact Or.inl (MonoidHom.map_isConj conjAutS h)
  · exact Or.inr (Or.inl (MonoidHom.map_isConj conjAutS h))
  · exact Or.inr (Or.inr (Or.inl (MonoidHom.map_isConj conjAutS h)))
  · exact Or.inr (Or.inr (Or.inr (MonoidHom.map_isConj conjAutS h)))

private theorem rac_mem_range_conj_of_isConj_r₁
    {β : MulAut S} (h : IsConj β (conjAutS r₁R)) :
    β ∈ (MulAut.conj : S →* MulAut S).range := by
  have hr₁ : conjAutS r₁R = MulAut.conj (⟨r₁, r₁_mem_S⟩ : S) := by
    ext s
    rfl
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [hr₁] at hc
  refine MonoidHom.mem_range.mpr ⟨c.symm (⟨r₁, r₁_mem_S⟩ : S), ?_⟩
  ext y
  rw [MulAut.conj_apply]
  have h1 : c (β y) = (⟨r₁, r₁_mem_S⟩ : S) * c y * (⟨r₁, r₁_mem_S⟩ : S)⁻¹ := by
    have h2 := congrArg (fun f : MulAut S => f (c y)) hc
    simpa [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.symm_apply_apply] using h2
  have h3 : β y = c.symm ((⟨r₁, r₁_mem_S⟩ : S) * c y * (⟨r₁, r₁_mem_S⟩ : S)⁻¹) := by
    rw [← h1]
    exact (MulEquiv.symm_apply_apply c (β y)).symm
  rw [h3]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]

private theorem rac_mem_range_conj_of_congr_centerQuotientHom {K H : Type} [Group K]
    [Group H] [Group.IsPerfect K] (b : (K ⧸ Subgroup.center K) ≃* H) {α : MulAut K}
    (h : MulAut.congr b (centerQuotientHom K α) ∈ (MulAut.conj : H →* MulAut H).range) :
    α ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp h
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.WeakClosure81.isInner_of_onCenterQuotient_inner α
    ⟨b.symm s, fun y => by
      have hy := congrArg (fun φ : MulAut H => b.symm (φ (b y))) hs
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.conj_apply, map_mul, map_inv] at hy
      exact hy.symm⟩
  exact ⟨g, MulEquiv.ext fun y => (hg y).symm⟩

theorem nonempty_centerQuotient_equiv_of_mem_rigidSet
    {G : Type} [Group G] [Finite G] {fullQ : Type}
    [Group fullQ] (hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (h16 : Nat.card (Subgroup.center fullQ) = 16) {x : G} {I : Subgroup G}
    (hI : I ∈ RigidSet fullQ x) :
    Nonempty ((kBar I ⧸ Subgroup.center (kBar I)) ≃* S) := by
  obtain ⟨eI⟩ := hI.2
  have hfin : Finite fullQ := Finite.of_equiv (kBar I) eI.toEquiv
  have hq : CFSG.IsQuasisimple fullQ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eI
      (TwoThin.isQuasisimple_hat (P92.rig_pcomp hI))
  obtain ⟨b₀, -⟩ := @actualCoverOfL34 fullQ _ hfin hq hL34 h16
  exact ⟨(QuotientGroup.congr (Subgroup.center (kBar I)) (Subgroup.center fullQ) eI
    (Subgroup.map_center_eq eI)).trans b₀⟩

end Classes

theorem glaPLayer_fixSubgroup_eq_bot_of_rigid_actor_of_one_lt_card :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (_hr : 1 < Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)),
  ∃ (hnorm : ∀ (I : Subgroup G),
      I ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x →
        v ∈ Subgroup.normalizer (I : Set G)),
    ∀ (I : Subgroup G)
      (hI : I ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x),
      let alpha : MulAut (CFSG.GH74.GLS.kBar I) :=
        MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥I)
          (I.normalizerMonoidHom ⟨v, hnorm I hI⟩)
      CFSG.Open.GLAPLayer 2
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup alpha) = ⊥ := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax hr
  classical
  obtain ⟨hNx, -⟩ := normalizes_rigid_families_of_rigid_actor hnonab hKproper hL34 h16 hx2
    hv2 hxv hvx hJ hvN hvact hxP hmax
  have h99 := no_isPCompIn_common_centralizer_of_rigid_actor_of_one_lt_card hnonab
    hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax hr
  have hv2' : v ^ 2 = 1 := by
    rw [← hv2]
    exact pow_orderOf_eq_one v
  exact ⟨hNx, fun I hI =>
    rac_glaPLayer_fixSubgroup_eq_bot hv2' (hNx I hI) (P92.rig_pcomp hI) h99⟩

theorem inner_or_projective_unitary_of_rigid_actor_of_one_lt_card :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (_hr : 1 < Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)),
  ∃ (hnorm : ∀ (I : Subgroup G),
      I ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x →
        v ∈ Subgroup.normalizer (I : Set G)),
    ∀ (I : Subgroup G)
      (hI : I ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x),
      let alpha : MulAut (CFSG.GH74.GLS.kBar I) :=
        MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥I)
          (I.normalizerMonoidHom ⟨v, hnorm I hI⟩)
      ∃ b :
          (CFSG.GH74.GLS.kBar I ⧸
            Subgroup.center (CFSG.GH74.GLS.kBar I)) ≃*
              CFSG.ComponentClassification.PSL3Four.S,
        let beta : MulAut CFSG.ComponentClassification.PSL3Four.S :=
          MulAut.congr b
            (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
              (CFSG.GH74.GLS.kBar I) alpha)
        alpha ≠ 1 ∧
          ¬ IsConj beta
            (CFSG.ComponentClassification.PSL3Four.conjAutS
              CFSG.ComponentClassification.PSL3Four.r₂R) ∧
          ¬ IsConj beta
            (CFSG.ComponentClassification.PSL3Four.conjAutS
              CFSG.ComponentClassification.PSL3Four.r₃R) ∧
          (alpha ∈
              (MulAut.conj : CFSG.GH74.GLS.kBar I →*
                MulAut (CFSG.GH74.GLS.kBar I)).range ∨
            IsConj beta
              (CFSG.ComponentClassification.PSL3Four.conjAutS
                CFSG.ComponentClassification.PSL3Four.r₄R)) := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax hr
  classical
  obtain ⟨hnorm, hfix⟩ := glaPLayer_fixSubgroup_eq_bot_of_rigid_actor_of_one_lt_card hnonab
    hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax hr
  refine ⟨hnorm, fun I hI => ?_⟩
  have hv2' : v ^ 2 = 1 := by
    rw [← hv2]
    exact pow_orderOf_eq_one v
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  have hLv : J.map (MulAut.conj g).toMonoidHom ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj hJ g
    rw [hg] at h
    exact h
  have hodd := odd_card_cxK_inf_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax I hI _ hLv
  have hα1 := rac_mapQuotient_ne_one hvx hv2 (hnorm I hI) (P92.rig_pcomp hLv) hodd
  obtain ⟨b⟩ := nonempty_centerQuotient_equiv_of_mem_rigidSet hL34 h16 hI
  have hperf : Group.IsPerfect (kBar I) := (TwoThin.isQuasisimple_hat (P92.rig_pcomp hI)).1
  refine ⟨b, ?_⟩
  intro beta
  have hfixβ : CFSG.Open.GLAPLayer 2 (fixSubgroup beta) = ⊥ :=
    rac_glaPLayer_fixSubgroup_congr_eq_bot b _ (hfix I hI)
  have hβ2 : beta ^ 2 = 1 := by
    have hα2 : (MulAut.mapQuotient (pPrimeCore 2 ↥I)
        (I.normalizerMonoidHom ⟨v, hnorm I hI⟩)) ^ 2 = 1 := by
      rw [← map_pow, rac_normalizerMonoidHom_sq hv2' (hnorm I hI), map_one]
    change (MulAut.congr b (centerQuotientHom (CFSG.GH74.GLS.kBar I)
      (MulAut.mapQuotient (pPrimeCore 2 ↥I)
        (I.normalizerMonoidHom ⟨v, hnorm I hI⟩)))) ^ 2 = 1
    rw [← map_pow, ← map_pow, hα2, map_one, map_one]
  have hβ1 : beta ≠ 1 := by
    intro hb1
    have : Group.IsPerfect (CFSG.GH74.GLS.kBar I) := hperf
    refine hα1 ?_
    refine centerQuotientHom_injective (CFSG.GH74.GLS.kBar I) ?_
    rw [map_one]
    refine (MulAut.congr b).injective ?_
    rw [map_one]
    exact hb1
  have h2 : ¬ IsConj beta (conjAutS r₂R) := fun h =>
    rac_glaPLayer_fixSubgroup_ne_bot_of_isConj h
      (rac_glaPLayer_fixSubgroup_conjAutS_ne_bot isSimpleGroup_C₂ exists_mul_ne_C₂
        (show 2 ∣ Nat.card C₂ by rw [card_C₂]; norm_num)) hfixβ
  have h3 : ¬ IsConj beta (conjAutS r₃R) := fun h =>
    rac_glaPLayer_fixSubgroup_ne_bot_of_isConj h
      (rac_glaPLayer_fixSubgroup_conjAutS_ne_bot isSimpleGroup_C₃ exists_mul_ne_C₃
        (show 2 ∣ Nat.card C₃ by rw [card_C₃]; norm_num)) hfixβ
  refine ⟨hα1, h2, h3, ?_⟩
  rcases rac_isConj_of_sq_eq_one hβ2 hβ1 with h | h | h | h
  · exact Or.inl (rac_mem_range_conj_of_congr_centerQuotientHom b
      (rac_mem_range_conj_of_isConj_r₁ h))
  · exact absurd h h2
  · exact absurd h h3
  · exact Or.inr h

end CFSG.GH74.GLS.NT44

end
