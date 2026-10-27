module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.I171
open CFSG.ComponentClassification.OuterAutomorphisms (centerQuotient_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom
  centerQuotientHom_injective hom_eq_id_of_central_displacement)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {L J E : Subgroup G} {d b : G}

private theorem open_isQuasisimple' {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem barX_ne_bot_of_glaPComponent' {X J : Subgroup G}
    (hJ : GLAPComponent p X J) :
    (J.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ≠ ⊥ := by
  intro hbot
  have h3 := hJ.2.2.1
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

private theorem prime_dvd_card_of_glaPComponent' {X J : Subgroup G} (hp : p.Prime)
    (hJ : GLAPComponent p X J) : p ∣ Nat.card ↥J := by
  by_contra hnd
  have hcop : Nat.Coprime p (Nat.card ↥J) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have htop : GLAPPrimeCore p ↥J = ⊤ := by
    have : (⊤ : Subgroup ↥J) ≤ GLAPPrimeCore p ↥J :=
      le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    exact top_le_iff.1 this
  have hJO : J ≤ GLAPPrimeCoreOf p X := by
    intro j hj
    refine CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p
      hJ.2.1 ?_
    exact (chev_mem_glaPPrimeCoreOf_iff hj).2 (htop ▸ Subgroup.mem_top _)
  apply barX_ne_bot_of_glaPComponent' hJ
  rw [eq_bot_iff]
  rintro _ ⟨⟨j, hjX⟩, hj, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (chev_mem_glaPPrimeCoreOf_iff hjX).1 (hJO (Subgroup.mem_subgroupOf.1 hj))

private theorem centralizes_of_centMod_of_isQuasisimple' {K : Subgroup G} {g : G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hne : GLAPPrimeCore p ↥K ≠ ⊤)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hc : CentMod p K g) :
    g ∈ Subgroup.centralizer (K : Set G) := by
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOZ : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hne
  let σ : ↥K →* ↥K := (Subgroup.normalizerMonoidHom (H := K)) ⟨g, hg⟩
  have hσ : ∀ x : ↥K, ((σ x : ↥K) : G) = g * (x : G) * g⁻¹ := fun x =>
    chev_coe_normalizerMonoidHom ⟨g, hg⟩ x
  have hdisp : ∀ x : ↥K, x⁻¹ * σ x ∈ Subgroup.center ↥K := by
    intro x
    have hmemG : ⁅((x : ↥K) : G)⁻¹, g⁆ ∈ GLAPPrimeCoreOf p K :=
      hc.2 (Subgroup.commutator_mem_commutator (K.inv_mem x.2) (Subgroup.mem_zpowers g))
    have hmemK : ⁅((x : ↥K) : G)⁻¹, g⁆ ∈ K :=
      (Subgroup.map_subtype_le (GLAPPrimeCore p ↥K)) hmemG
    have hcore : (⟨⁅((x : ↥K) : G)⁻¹, g⁆, hmemK⟩ : ↥K) ∈ GLAPPrimeCore p ↥K :=
      (chev_mem_glaPPrimeCoreOf_iff hmemK).1 hmemG
    have hval : ((x⁻¹ * σ x : ↥K) : G) = ⁅((x : ↥K) : G)⁻¹, g⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
      group
    rw [show x⁻¹ * σ x = ⟨⁅((x : ↥K) : G)⁻¹, g⁆, hmemK⟩ from Subtype.ext hval]
    exact hOZ hcore
  have hid := hom_eq_id_of_central_displacement σ hdisp
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hfix : σ ⟨x, hx⟩ = ⟨x, hx⟩ := congrArg (fun φ : ↥K →* ↥K => φ ⟨x, hx⟩) hid
  have hval : g * x * g⁻¹ = x := by
    have := congrArg Subtype.val hfix
    simpa only [hσ, MonoidHom.id_apply] using this
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

private theorem chevAut_inv_apply_mk {K : Subgroup G} {b : G}
    (hbK' : b⁻¹ ∈ Subgroup.normalizer (K : Set G)) {q q' : PQuot p K}
    (h : indRel p K b q q') :
    chevAut p K ⟨b⁻¹, hbK'⟩ (QuotientGroup.mk q) = QuotientGroup.mk q' := by
  obtain ⟨l, l', rfl, rfl, hll⟩ := h
  change chevAut p K ⟨b⁻¹, hbK'⟩ (chevQuotHom p K l) = chevQuotHom p K l'
  rw [chevAut_chevQuotHom]
  congr 1
  apply Subtype.ext
  rw [chev_coe_normalizerMonoidHom, hll]
  group

private theorem fixSubgroup_conj_eq_centralizer {S : Type} [Group S] (x : S) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set S) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc g * x = (x * g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

private theorem map_centralizer_singleton {A B : Type} [Group A] [Group B] (f : A ≃* B) (t : A) :
    (Subgroup.centralizer ({t} : Set A)).map f.toMonoidHom =
      Subgroup.centralizer ({f t} : Set B) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨f.symm y, ?_, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

private theorem conj_inv_apply {S : Type} [Group S] (y z : S) :
    (MulAut.conj y)⁻¹ z = y⁻¹ * z * y := by
  rw [show (MulAut.conj y)⁻¹ = MulAut.conj y⁻¹ from
    (map_inv (MulAut.conj : S →* MulAut S) y).symm]
  rw [MulAut.conj_apply, inv_inv]

private theorem map_centralizer_conj {S : Type} [Group S] (c t : S) (hct : c * t = t * c) :
    (Subgroup.centralizer ({t} : Set S)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({t} : Set S) := by
  rw [map_centralizer_singleton (MulAut.conj c) t]
  have h : (MulAut.conj c) t = t := by
    rw [MulAut.conj_apply, hct]
    group
  rw [h]

private theorem map_conj_eq_self_of_mem_normalizer {S : Type} [Group S] {K : Subgroup S} {c : S}
    (hc : c ∈ Subgroup.normalizer (K : Set S)) :
    K.map (MulAut.conj c).toMonoidHom = K := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hc x).1 hx
  · intro x hx
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hc) x).1 hx
    · show c * (c⁻¹ * x * c) * c⁻¹ = x
      group

private theorem exists_conj_chevAut {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hin : InducesInnerMod p K g) :
    ∃ y : PSimple p K, MulAut.conj y = chevAut p K ⟨g, hg⟩ := by
  obtain ⟨k, hk⟩ := (inducesInnerMod_iff_barAut_mem_inner hg).1 hin
  refine ⟨QuotientGroup.mk' (Subgroup.center (PQuot p K)) k, ?_⟩
  rw [← centerQuotient_conj k]
  show centerQuotientHom (PQuot p K) (MulAut.conj k) =
    centerQuotientHom (PQuot p K) (barAut p K ⟨g, hg⟩)
  exact congrArg (centerQuotientHom (PQuot p K)) hk

private theorem exists_xy_chevAut (hS : Shape15Cfg p L J E d) (hbE : b ∈ E)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hOut : OutHalf) (hshape : ¬ I171LieShapeAt p L) (hinb : InducesInnerMod p L b) :
    ∃ x y : PSimple p L,
      x ≠ 1 ∧ x ^ p = 1 ∧ y ^ p = 1 ∧ Commute x y ∧
      MulAut.conj x = chevAut p L ⟨d, hdN⟩ ∧
      MulAut.conj y = chevAut p L ⟨b, hbN⟩ ∧
      GLAPComponent p (Subgroup.centralizer ({x} : Set (PSimple p L))) (chevTransfer p L J) := by
  have hind : InducesInnerMod p L d :=
    (hOut G p L J E d d hS hS.d_mem).resolve_right hshape
  obtain ⟨x, hx⟩ := exists_conj_chevAut hdN hind
  obtain ⟨y, hy⟩ := exists_conj_chevAut hbN hinb
  haveI : Group.IsPerfect ↥L := hS.qs.1
  haveI hperf : Group.IsPerfect (PQuot p L) :=
    Group.IsPerfect.ofSurjective (f := pQuotHom p L) (pQuotHom_surjective p L)
  have hcen : Subgroup.center (PSimple p L) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (G := PQuot p L)
  have hpJ : p ∣ Nat.card ↥J :=
    prime_dvd_card_of_glaPComponent' hS.prime hS.pcomp
  have hJL : J ≤ L := hS.pcomp.1.trans inf_le_left
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJL)
  have hne : GLAPPrimeCore p ↥L ≠ ⊤ := by
    intro htop
    have hc := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥L
    rw [htop, Subgroup.card_top] at hc
    exact hS.prime.ne_one (Nat.eq_one_of_dvd_coprimes hc (dvd_refl p) hpL)
  have hx1 : x ≠ 1 := by
    intro hx0
    have hchev1 : chevAut p L ⟨d, hdN⟩ = 1 := by rw [← hx, hx0, map_one]
    have hbar1 : barAut p L ⟨d, hdN⟩ = 1 := by
      apply centerQuotientHom_injective (PQuot p L)
      show centerQuotientHom (PQuot p L) (barAut p L ⟨d, hdN⟩) = centerQuotientHom (PQuot p L) 1
      rw [map_one]
      exact hchev1
    have hc : CentMod p L d := (chev_barAut_eq_one_iff_centMod hdN).1 hbar1
    have hcL : d ∈ Subgroup.centralizer (L : Set G) :=
      centralizes_of_centMod_of_isQuasisimple' (open_isQuasisimple' hS.qs) hne hdN hc
    have hmem : d ∈ E ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hcL⟩
    rw [hS.faithful] at hmem
    exact hS.d_ne (Subgroup.mem_bot.1 hmem)
  have hxp : x ^ p = 1 := by
    apply mulAutConj_injective_of_center_eq_bot hcen
    rw [map_pow, hx, chevAut_pow_eq_one p L hdN (hS.elem.2 d hS.d_mem), map_one]
  have hyp : y ^ p = 1 := by
    apply mulAutConj_injective_of_center_eq_bot hcen
    rw [map_pow, hy, chevAut_pow_eq_one p L hbN (hS.elem.2 b hbE), map_one]
  have hcomm : Commute x y := by
    show x * y = y * x
    apply mulAutConj_injective_of_center_eq_bot hcen
    rw [map_mul, map_mul, hx, hy, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hbE hS.d_mem).symm
  have hfixx : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (chevAut p L ⟨d, hdN⟩) =
      Subgroup.centralizer ({x} : Set (PSimple p L)) := by
    rw [← hx]
    exact fixSubgroup_conj_eq_centralizer x
  have hJ'comp : GLAPComponent p (Subgroup.centralizer ({x} : Set (PSimple p L)))
      (chevTransfer p L J) := by
    have h := glaPComponent_chevTransfer hS.prime hdN
      (isPGroup_zpowers_of_pow_eq_one (hS.elem.2 d hS.d_mem)) hS.pcomp
    rwa [hfixx] at h
  exact ⟨x, y, hx1, hxp, hyp, hcomm, hx, hy, hJ'comp⟩

private theorem chevTransfer_map_conj {K J : Subgroup G} {c : G}
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hJK : J ≤ K) {y : PSimple p K}
    (hy : MulAut.conj y = chevAut p K ⟨c, hcK⟩) :
    chevTransfer p K (J.map (MulAut.conj c).toMonoidHom) =
      (chevTransfer p K J).map (MulAut.conj y).toMonoidHom := by
  have hsub : (J.map (MulAut.conj c).toMonoidHom).subgroupOf K =
      (J.subgroupOf K).map (K.normalizerMonoidHom ⟨c, hcK⟩) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨j, hj, hjx⟩
      refine ⟨⟨(j : G), hJK hj⟩, Subgroup.mem_subgroupOf.2 hj, ?_⟩
      apply Subtype.ext
      change c * j * c⁻¹ = (x : G)
      change (MulAut.conj c) j = (x : G) at hjx
      rwa [MulAut.conj_apply] at hjx
    · rintro ⟨z, hz, hzx⟩
      refine ⟨(z : G), Subgroup.mem_subgroupOf.1 hz, ?_⟩
      change (MulAut.conj c) (z : G) = (x : G)
      rw [MulAut.conj_apply]
      exact congrArg Subtype.val hzx
  calc chevTransfer p K (J.map (MulAut.conj c).toMonoidHom)
      = ((J.map (MulAut.conj c).toMonoidHom).subgroupOf K).map (chevQuotHom p K) := rfl
    _ = ((J.subgroupOf K).map (K.normalizerMonoidHom ⟨c, hcK⟩)).map (chevQuotHom p K) := by
          rw [hsub]
    _ = (J.subgroupOf K).map ((chevQuotHom p K).comp (K.normalizerMonoidHom ⟨c, hcK⟩)) := by
          rw [Subgroup.map_map]
    _ = (J.subgroupOf K).map ((MulAut.conj y).toMonoidHom.comp (chevQuotHom p K)) := by
          congr 1
          ext z
          change chevQuotHom p K (K.normalizerMonoidHom ⟨c, hcK⟩ z) =
            (MulAut.conj y) (chevQuotHom p K z)
          rw [← chevAut_chevQuotHom, ← hy]
    _ = ((J.subgroupOf K).map (chevQuotHom p K)).map (MulAut.conj y).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = (chevTransfer p K J).map (MulAut.conj y).toMonoidHom := rfl

private theorem mem_normalizer_of_modelNorm (hS : Shape15Cfg p L J E d) (hbE : b ∈ E)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    {y : PSimple p L} (hy : MulAut.conj y = chevAut p L ⟨b, hbN⟩)
    (hyN : y ∈ Subgroup.normalizer (chevTransfer p L J : Set (PSimple p L))) :
    b ∈ Subgroup.normalizer (J : Set G) := by
  have hJL : J ≤ L := hS.pcomp.1.trans inf_le_left
  have hbd : b * d = d * b :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hbE hS.d_mem
  have hXmap : (L ⊓ Subgroup.centralizer ({d} : Set G)).map (MulAut.conj b).toMonoidHom =
      L ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj b).injective,
      map_conj_eq_self_of_mem_normalizer hbN, map_centralizer_conj b d hbd]
  have hJ''comp : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G))
      (J.map (MulAut.conj b).toMonoidHom) := by
    have h := glaPComponent_map_mulEquiv hS.prime (MulAut.conj b) hS.pcomp
    rwa [hXmap] at h
  have htrans : chevTransfer p L (J.map (MulAut.conj b).toMonoidHom) =
      chevTransfer p L J := by
    rw [chevTransfer_map_conj hbN hJL hy]
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).1 hyN
  have hJeq : J = J.map (MulAut.conj b).toMonoidHom :=
    eq_of_chevTransfer_eq hS.prime hdN
      (isPGroup_zpowers_of_pow_eq_one (hS.elem.2 d hS.d_mem)) hS.pcomp hJ''comp
      (by rw [htrans])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : b * x * b⁻¹ ∈ J.map (MulAut.conj b).toMonoidHom :=
      Subgroup.mem_map.2 ⟨x, hx, by change b * x * b⁻¹ = b * x * b⁻¹; rfl⟩
    rwa [← hJeq] at hmem
  · intro hx
    have hmem : b * x * b⁻¹ ∈ J.map (MulAut.conj b).toMonoidHom := by
      rw [← hJeq]
      exact hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hmem
    have hzx' : b * z * b⁻¹ = b * x * b⁻¹ := by
      change (MulAut.conj b) z = b * x * b⁻¹ at hzx
      rwa [MulAut.conj_apply] at hzx
    have hzx'' : z = x := by
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = b⁻¹ * (b * x * b⁻¹) * b := by rw [hzx']
        _ = x := by group
    rwa [hzx''] at hz

private theorem injective_pSimpleMapOfSurjective {A B : Type} [Group A] [Finite A]
    [Group B] [Finite B] (hp : p.Prime) (g : A →* B) (hg : Function.Surjective g)
    (hA : CFSG.Open.IsQuasisimple (A ⧸ GLAPPrimeCore p A))
    (hB : CFSG.Open.IsQuasisimple (B ⧸ GLAPPrimeCore p B)) :
    Function.Injective (pSimpleMapOfSurjective hp g hg) := by
  haveI : IsSimpleGroup ((A ⧸ GLAPPrimeCore p A) ⧸ Subgroup.center (A ⧸ GLAPPrimeCore p A)) :=
    hA.2
  haveI : IsSimpleGroup ((B ⧸ GLAPPrimeCore p B) ⧸ Subgroup.center (B ⧸ GLAPPrimeCore p B)) :=
    hB.2
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pSimpleMapOfSurjective hp g hg).ker with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne
      ((B ⧸ GLAPPrimeCore p B) ⧸ Subgroup.center (B ⧸ GLAPPrimeCore p B))
    obtain ⟨a', rfl⟩ := pSimpleMapOfSurjective_surjective hp g hg a
    obtain ⟨b', rfl⟩ := pSimpleMapOfSurjective_surjective hp g hg b
    apply hab
    have h1 : pSimpleMapOfSurjective hp g hg a' = 1 := by
      rw [← MonoidHom.mem_ker, h]; trivial
    have h2 : pSimpleMapOfSurjective hp g hg b' = 1 := by
      rw [← MonoidHom.mem_ker, h]; trivial
    rw [h1, h2]

private theorem exists_equiv_chevTransfer (hS : Shape15Cfg p L J E d) (hbE : b ∈ E)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hbJ : b ∈ Subgroup.normalizer (J : Set G)) {x y : PSimple p L}
    (hy : MulAut.conj y = chevAut p L ⟨b, hbN⟩)
    (hJ'comp : GLAPComponent p (Subgroup.centralizer ({x} : Set (PSimple p L)))
      (chevTransfer p L J))
    (hyN : y ∈ Subgroup.normalizer (chevTransfer p L J : Set (PSimple p L))) :
    ∃ e : PSimple p J ≃* PSimple p (chevTransfer p L J),
      ∀ s s' : PSimple p J, indRelS p J b s s' →
        indRelS p (chevTransfer p L J) y (e s) (e s') := by
  have hJL : J ≤ L := hS.pcomp.1.trans inf_le_left
  have hbN' : b⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hbN
  have hbJ' : b⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hbJ
  have hyN' : y⁻¹ ∈ Subgroup.normalizer (chevTransfer p L J : Set (PSimple p L)) :=
    Subgroup.inv_mem _ hyN
  let f : ↥J →* ↥(chevTransfer p L J) :=
    { toFun := fun j => ⟨chevQuotHom p L (Subgroup.inclusion hJL j),
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 j.2)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨u, hu, hus⟩ := Subgroup.mem_map.1 hs
    refine ⟨⟨(u : G), Subgroup.mem_subgroupOf.1 hu⟩, ?_⟩
    apply Subtype.ext
    show chevQuotHom p L (Subgroup.inclusion hJL _) = s
    rw [show Subgroup.inclusion hJL (⟨(u : G), Subgroup.mem_subgroupOf.1 hu⟩ : ↥J) = u from
      Subtype.ext rfl]
    exact hus
  have hinj : Function.Injective (pSimpleMapOfSurjective hS.prime f hf) :=
    injective_pSimpleMapOfSurjective hS.prime f hf
      (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp)
      (isQuasisimple_pQuot_of_glaPComponent hS.prime hJ'comp)
  let e : PSimple p J ≃* PSimple p (chevTransfer p L J) :=
    MulEquiv.ofBijective (pSimpleMapOfSurjective hS.prime f hf)
      ⟨hinj, pSimpleMapOfSurjective_surjective hS.prime f hf⟩
  have he : ∀ j : ↥J, e (chevQuotHom p J j) =
      chevQuotHom p (chevTransfer p L J) (f j) := by
    intro j
    show pSimpleMapOfSurjective hS.prime f hf (chevQuotHom p J j) =
      chevQuotHom p (chevTransfer p L J) (f j)
    rfl
  refine ⟨e, ?_⟩
  intro s s' hs
  obtain ⟨q, q', hrel, hq, hq'⟩ := hs
  subst hq; subst hq'
  obtain ⟨j, hj⟩ := chevQuotHom_surjective p J (QuotientGroup.mk q)
  have hbjJ : b⁻¹ * (j : G) * b ∈ J := by
    simpa using (Subgroup.mem_normalizer_iff.1 hbJ' (j : G)).1 j.2
  set jb : ↥J := ⟨b⁻¹ * (j : G) * b, hbjJ⟩ with hjb
  have hq'_eq : (QuotientGroup.mk q' : PSimple p J) = chevQuotHom p J jb := by
    have h1 : chevAut p J ⟨b⁻¹, hbJ'⟩ (QuotientGroup.mk q) = QuotientGroup.mk q' :=
      chevAut_inv_apply_mk hbJ' hrel
    rw [← hj] at h1
    rw [← h1]
    rw [chevAut_chevQuotHom]
    congr 1
    apply Subtype.ext
    rw [chev_coe_normalizerMonoidHom, hjb]
    group
  have hconj : (f jb : PSimple p L) = y⁻¹ * (f j : PSimple p L) * y := by
    show chevQuotHom p L (Subgroup.inclusion hJL jb) =
      y⁻¹ * chevQuotHom p L (Subgroup.inclusion hJL j) * y
    have h1 : Subgroup.inclusion hJL jb =
        L.normalizerMonoidHom ⟨b⁻¹, hbN'⟩ (Subgroup.inclusion hJL j) := by
      apply Subtype.ext
      rw [chev_coe_normalizerMonoidHom, inv_inv]
      rfl
    rw [h1, ← chevAut_chevQuotHom]
    have h2 : chevAut p L ⟨b⁻¹, hbN'⟩ = (MulAut.conj y)⁻¹ := by
      rw [show (⟨b⁻¹, hbN'⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨b, hbN⟩)⁻¹ from rfl,
        map_inv, hy]
    rw [h2, conj_inv_apply]
  refine ⟨pQuotHom p (chevTransfer p L J) (f j),
    pQuotHom p (chevTransfer p L J) (f jb), ?_, ?_, ?_⟩
  · refine ⟨f j, f jb, rfl, rfl, ?_⟩
    exact hconj
  · rw [← hj, he j]
    rfl
  · rw [hq'_eq, he jb]
    rfl

end Helpers

theorem redSimple_holds : RedSimple := by
  intro hMT F hOut hSM
  intro G _ _ p L J E d b hS hbE hcat hshape hinb
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hS.normalizes hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hS.normalizes hbE
  obtain ⟨x, y, hx1, hxp, hyp, hcomm, hx, hy, hJ'comp⟩ :=
    exists_xy_chevAut hS hbE hdN hbN hOut hshape hinb
  have hmodel : ShapeModelAt (PSimple p L) p :=
    hSM (PSimple p L) p hS.prime hS.odd hcat hshape
  obtain ⟨hyN, hinnJ'⟩ := hmodel x y hx1 hxp hyp hcomm _ hJ'comp
  have hbJ : b ∈ Subgroup.normalizer (J : Set G) :=
    mem_normalizer_of_modelNorm hS hbE hdN hbN hy hyN
  have hperf : commutator (PQuot p J) = ⊤ :=
    (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp).1
  obtain ⟨e, he⟩ := exists_equiv_chevTransfer hS hbE hdN hbN hbJ hy hJ'comp hyN
  exact ⟨hbJ, hMT G (PSimple p L) p J (chevTransfer p L J) b y e hperf hbJ he hinnJ'⟩

theorem redSimpleNorm_holds : RedSimpleNorm := by
  intro F hOut hSNM
  intro G _ _ p L J E d b hS hbE hcat hshape hinb
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hS.normalizes hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hS.normalizes hbE
  obtain ⟨x, y, hx1, hxp, hyp, hcomm, -, hy, hJ'comp⟩ :=
    exists_xy_chevAut hS hbE hdN hbN hOut hshape hinb
  have hmodel : ShapeModelNormAt (PSimple p L) p :=
    hSNM (PSimple p L) p hS.prime hS.odd hcat hshape
  have hyN : y ∈ Subgroup.normalizer (chevTransfer p L J : Set (PSimple p L)) :=
    hmodel x y hx1 hxp hyp hcomm _ hJ'comp
  exact mem_normalizer_of_modelNorm hS hbE hdN hbN hy hyN

end CFSG.LocalAnalysis.GLTheoremA.F151

end
