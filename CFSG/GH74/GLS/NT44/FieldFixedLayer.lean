module

public import CFSG.GH74.GLS.NT44.RigidActorClasses
import CFSG.GH74.GLS.NT44.RigidSingleton
import CFSG.GH74.GLS.NT44.RigidPump
import CFSG.GH74.GLS.NT44.RigidPumpExistence
import CFSG.GH74.GLS.NT44.RigidCenterCommutators
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourOuterTwoSubgroup
import CFSG.GH74.Generic.BProg.B1.Lift0
import CFSG.GroupTheory.PCore.QuasisimpleNormalCore
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedLift

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm4
open CFSG.HardMathSupport.Solomon.Coordinator

section Core

theorem pPrimeCore_eq_bot_of_map_isSimpleGroup {K Q : Type*} [Group K] [Group Q] [Finite K]
    (π : K →* Q) (hker : IsPGroup 2 π.ker) {H : Subgroup K}
    (hsimple : IsSimpleGroup ↥(H.map π)) (h2 : 2 ∣ Nat.card ↥(H.map π)) :
    pPrimeCore 2 ↥H = ⊥ := by
  classical
  let f : ↥H →* ↥(H.map π) :=
    (π.comp H.subtype).codRestrict (H.map π) fun h => Subgroup.mem_map_of_mem π h.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨h, hh, rfl⟩ := hq
    exact ⟨⟨h, hh⟩, rfl⟩
  have hsimpleQ : IsSimpleGroup (↥H ⧸ f.ker) :=
    @MulEquiv.isSimpleGroup (↥H ⧸ f.ker) _ ↥(H.map π) _ hsimple
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hdvd : 2 ∣ Nat.card (↥H ⧸ f.ker) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    exact h2
  have hkerf : IsPGroup 2 ↥(f.ker) := by
    have hcom : f.ker = π.ker.comap H.subtype := by
      ext x
      simp only [f, MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.codRestrict_apply,
        MonoidHom.comp_apply]
      constructor
      · intro hx
        exact Subtype.ext_iff.1 hx
      · intro hx
        exact Subtype.ext hx
    rw [hcom]
    exact hker.comap_of_injective H.subtype H.subtype_injective
  have hcore : pPrimeCore 2 ↥(f.ker) = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hkerf
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(f.ker))) :=
      @pPrimeCore_coprime_card 2 ↥(f.ker) _ _ (Fact.mk Nat.prime_two)
    have hdvd' : Nat.card (pPrimeCore 2 ↥(f.ker)) ∣ 2 ^ n := by
      rw [← hn]
      simpa using Subgroup.card_dvd_of_le (H := pPrimeCore 2 ↥(f.ker)) (K := ⊤) le_top
    exact (hcop.symm.pow_right n).eq_one_of_dvd hdvd'
  exact pPrimeCore_eq_bot_of_normal_quotient_simple Nat.prime_two (N := f.ker) hcore
    hsimpleQ hdvd

end Core

section Layer

variable {G : Type} [Group G] [Finite G]

theorem exists_isPCompIn_inf_centralizer_of_glaPComponent {x v : G} {I : Subgroup G}
    (hv2 : v ^ 2 = 1) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hI : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) I) {Ab : Subgroup (kBar I)}
    (hAb : CFSG.Open.GLAPComponent 2 (fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥I)
      (I.normalizerMonoidHom ⟨v, hvI⟩))) Ab) :
    ∃ Λ : Subgroup G,
      IsPCompIn 2 (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) Λ ∧
        Λ ≤ I ∧ (Λ.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 2 ↥I)) = Ab := by
  classical
  have hAb' := (i183_glaPComponent_iff_isPComponent Nat.prime_two).1 hAb
  let C : Subgroup G := I ⊓ Subgroup.centralizer ({v} : Set G)
  let φ : ↥C →* kBar I :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥I)).comp
      (Subgroup.inclusion (inf_le_left : I ⊓ Subgroup.centralizer ({v} : Set G) ≤ I))
  have hφrange : φ.range = fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥I)
      (I.normalizerMonoidHom ⟨v, hvI⟩)) :=
    range_inclusion_inf_centralizer_eq_fixSubgroup hv2 hvI
  have hJb : IsPCompIn 2 φ.range Ab := by
    rw [hφrange]
    exact hAb'
  have hkerφ : ¬ 2 ∣ Nat.card φ.ker := by
    simpa [φ] using not_two_dvd_card_ker_inclusion_inf_centralizer (I := I) (v := v)
  obtain ⟨hY, hYmap⟩ :=
    CFSG.GH74.Generic.BProg.B1.exists_isPCompIn_lift_of_odd_ker φ hkerφ hJb
  let Λ : Subgroup G := oPrimeResidualOf 2 ((Ab.comap φ).map C.subtype)
  have hΛC : Λ ≤ C := hY.1
  have hsub : (Λ.subgroupOf C).map (Subgroup.inclusion (inf_le_left : C ≤ I)) =
      Λ.subgroupOf I := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rw [← hwz, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact Subgroup.mem_subgroupOf.1 hw
    · intro hz
      refine ⟨⟨z.1, hΛC (Subgroup.mem_subgroupOf.1 hz)⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hz)
      · exact Subtype.ext rfl
  have hmap : (Λ.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 2 ↥I)) = Ab := by
    rw [← hsub, Subgroup.map_map]
    exact hYmap
  exact ⟨Λ, CFSG.GH74.Generic.BProg.B1.isPCompIn_of_isSubnormal 2
    (inf_le_inf_right _ hI.1) (isSubnormal_inf_centralizer_of_isPCompIn hI) hY,
    hΛC.trans inf_le_left, hmap⟩

theorem mapQuotient_eq_self_of_mem_glaPLayer {fullQ : Type} [Group fullQ] {x v y : G}
    {J : Subgroup G} (hx2 : orderOf x = 2) (hv2 : v ^ 2 = 1)
    (hxv : x ∈ Subgroup.centralizer ({v} : Set G))
    (hJ : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) J)
    (hvJ : v ∈ Subgroup.normalizer (J : Set G)) (hyJ : y ∈ Subgroup.normalizer (J : Set G))
    (hyv : y ∈ Subgroup.centralizer ({v} : Set G)) (hyZ : y ∈ zStar (Kz fullQ v))
    (hO : pPrimeCore 2 ↥(fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨v, hvJ⟩))) = ⊥) :
    ∀ k ∈ CFSG.Open.GLAPLayer 2 (fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨v, hvJ⟩))),
      MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨y, hyJ⟩) k = k := by
  classical
  set α : MulAut (kBar J) :=
    MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvJ⟩)
  set β : MulAut (kBar J) :=
    MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨y, hyJ⟩)
  have hO' : pPrimeCore 2 ↥(fixSubgroup α) = ⊥ := hO
  have hle : CFSG.Open.GLAPLayer 2 (fixSubgroup α) ≤ fixSubgroup β := by
    rw [CFSG.Open.GLAPLayer]
    refine sSup_le ?_
    intro Ab hAb
    obtain ⟨Λ, hΛcomp, hΛJ, hΛmap⟩ :=
      exists_isPCompIn_inf_centralizer_of_glaPComponent hv2 hvJ hJ hAb
    intro k hk
    rw [mem_fixSubgroup]
    rw [← hΛmap] at hk
    obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.1 hk
    rw [← hlk]
    change MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨y, hyJ⟩)
      ((QuotientGroup.mk' (pPrimeCore 2 ↥J)) l) = (QuotientGroup.mk' (pPrimeCore 2 ↥J)) l
    rw [QuotientGroup.mk'_apply, MulAut.mapQuotient_mk, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv]
    have hlΛ : (l : G) ∈ Λ := Subgroup.mem_subgroupOf.1 hl
    have hlp : (l : G) ∈ pLayerOf 2 (Subgroup.centralizer ({v} : Set G)) :=
      CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf hx2 hxv hΛcomp hlΛ
    have hcommCore : (l : G) * y * (l : G)⁻¹ * y⁻¹ ∈
        pPrimeCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
      simpa [commutatorElement_def] using commutator_mem_of_mem_zStar_kz hyZ (l : G) hlp
    have hlJ : (l : G) ∈ J := hΛJ hlΛ
    have hlV : (l : G) ∈ Subgroup.centralizer ({v} : Set G) := (hΛcomp.1 hlΛ).2
    have hcommJ : (l : G) * y * (l : G)⁻¹ * y⁻¹ ∈ J := by
      have hy : y * (l : G)⁻¹ * y⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hyJ (l : G)⁻¹).mp (J.inv_mem hlJ)
      simpa only [mul_assoc] using J.mul_mem hlJ hy
    have hcommV : (l : G) * y * (l : G)⁻¹ * y⁻¹ ∈
        Subgroup.centralizer ({v} : Set G) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hl' : Commute (l : G) v := Subgroup.mem_centralizer_singleton_iff.mp hlV
      have hy' : Commute y v := Subgroup.mem_centralizer_singleton_iff.mp hyv
      simpa only [mul_assoc] using
        (((hl'.mul_left hy').mul_left hl'.inv_left).mul_left hy'.inv_left).eq
    let C : Subgroup G := J ⊓ Subgroup.centralizer ({v} : Set G)
    have hcommC : (l : G) * y * (l : G)⁻¹ * y⁻¹ ∈ C := ⟨hcommJ, hcommV⟩
    let φ : ↥C →* kBar J :=
      (QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp
        (Subgroup.inclusion (inf_le_left : J ⊓ Subgroup.centralizer ({v} : Set G) ≤ J))
    have hφrange : φ.range = fixSubgroup α :=
      range_inclusion_inf_centralizer_eq_fixSubgroup hv2 hvJ
    let M : Subgroup G := pPrimeCoreOf 2 (Subgroup.centralizer ({v} : Set G)) ⊓ C
    have hMnorm : (M.subgroupOf C).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      change (g : G) * (n : G) * (g : G)⁻¹ ∈ M
      refine ⟨?_, ?_⟩
      · exact TwoThin.pPrimeCoreOf_normalized (Subgroup.centralizer ({v} : Set G)) g.2.2 hn.1
      · refine ⟨?_, ?_⟩
        · exact J.mul_mem (J.mul_mem g.2.1 hn.2.1) (J.inv_mem g.2.1)
        · change (g : G) * (n : G) * (g : G)⁻¹ ∈ Subgroup.centralizer ({v} : Set G)
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          have hgc : Commute (g : G) v := Subgroup.mem_centralizer_singleton_iff.mp g.2.2
          have hnc : Commute (n : G) v := Subgroup.mem_centralizer_singleton_iff.mp hn.2.2
          simpa only [mul_assoc] using ((hgc.mul_left hnc).mul_left hgc.inv_left).eq
    let ψ : ↥C →* ↥(fixSubgroup α) :=
      φ.codRestrict (fixSubgroup α) fun x => by
        rw [← hφrange]
        exact ⟨x, rfl⟩
    have hψ_surj : Function.Surjective ψ := by
      rintro ⟨q, hq⟩
      have hq' : q ∈ φ.range := by rw [hφrange]; exact hq
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 hq'
      exact ⟨w, Subtype.ext (by simpa [ψ] using hw)⟩
    have himg_normal : ((M.subgroupOf C).map ψ).Normal := hMnorm.map ψ hψ_surj
    have hMcard : Nat.Coprime 2 (Nat.card (M.subgroupOf C)) := by
      have hodd : Odd (Nat.card (pPrimeCoreOf 2 (Subgroup.centralizer ({v} : Set G)))) :=
        TwoThin.card_pPrimeCoreOf_odd _
      have hcop : Nat.Coprime 2 (Nat.card M) :=
        (Nat.coprime_two_left.mpr hodd).coprime_dvd_right
          (Subgroup.card_dvd_of_le
            (inf_le_left : M ≤ pPrimeCoreOf 2 (Subgroup.centralizer ({v} : Set G))))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ≤ C)).toEquiv]
      exact hcop
    have himg_coprime : Nat.Coprime 2 (Nat.card ((M.subgroupOf C).map ψ)) :=
      hMcard.coprime_dvd_right (Subgroup.card_map_dvd (H := M.subgroupOf C) (f := ψ))
    have himg_le : (M.subgroupOf C).map ψ ≤ pPrimeCore 2 ↥(fixSubgroup α) :=
      le_sSup ⟨himg_normal, himg_coprime⟩
    have hpsi_one : ψ ⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩ = 1 := by
      have hxM : (⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩ : ↥C) ∈ M.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hcommCore, hcommC⟩
      have hmem := himg_le (Subgroup.mem_map_of_mem ψ hxM)
      rw [hO'] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hφ_one : φ ⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩ = 1 := by
      have h1 : ((ψ ⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩ : ↥(fixSubgroup α)) : kBar J) = 1 := by
        rw [hpsi_one]
        rfl
      simpa [ψ] using h1
    have hmemJ : (Subgroup.inclusion (inf_le_left : C ≤ J) ⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩) ∈
        pPrimeCore 2 ↥J :=
      (QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥J)
        (Subgroup.inclusion (inf_le_left : C ≤ J) ⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩)).1
        (by simpa [φ] using hφ_one)
    have hinvJ : (Subgroup.inclusion (inf_le_left : C ≤ J) ⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩)⁻¹ ∈
        pPrimeCore 2 ↥J :=
      (pPrimeCore 2 ↥J).inv_mem hmemJ
    have hinv_eq :
        (Subgroup.inclusion (inf_le_left : C ≤ J) ⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hcommC⟩)⁻¹ =
          J.normalizerMonoidHom ⟨y, hyJ⟩ l * l⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inclusion]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      group
    rw [← hinv_eq]
    exact hinvJ
  intro k hk
  exact hle hk

end Layer

theorem false_of_not_inner_of_four_le_card
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    {L : Subgroup G} (hL : L ∈ RigidSet fullQ v) {V : Subgroup G}
    (hVx : V ≤ Subgroup.centralizer ({x} : Set G))
    (hVZ : V ≤ zStar L)
    (hV2 : IsPGroup 2 V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV4 : 4 ≤ Nat.card V)
    (hVinn : ∀ a ∈ V, ∀ haJ : a ∈ Subgroup.normalizer (J : Set G),
      MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨a, haJ⟩) ∈
        (MulAut.conj : kBar J →* MulAut (kBar J)).range → a = 1) :
    False := by
  classical
  have hsub : ∀ s : G, orderOf s = 2 → (RigidSet fullQ s).Subsingleton :=
    rigidSet_subsingleton_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact
      hxP hmax
  have hsub_x : (RigidSet fullQ x).Subsingleton := hsub x hx2
  have hsub_v : (RigidSet fullQ v).Subsingleton := hsub v hv2
  have hKz_x : Kz fullQ x = J := kz_eq_of_rigidSet_subsingleton (Q := fullQ) hsub_x hJ
  have hKz_v : Kz fullQ v = L := kz_eq_of_rigidSet_subsingleton (Q := fullQ) hsub_v hL
  have hVnJ : V ≤ Subgroup.normalizer (J : Set G) :=
    hVx.trans (centralizer_le_normalizer_of_rigidSet_subsingleton (Q := fullQ) hsub_x hJ)
  have hperf : Group.IsPerfect (kBar J) := (TwoThin.isQuasisimple_hat (hJ.1.1.2.2)).1
  have hcenter_card : Nat.card ↥(Subgroup.center (kBar J)) = 16 := by
    obtain ⟨e⟩ := hJ.2
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans h16
  let π : kBar J →* kBar J ⧸ Subgroup.center (kBar J) :=
    QuotientGroup.mk' (Subgroup.center (kBar J))
  let cq : MulAut (kBar J) →* MulAut (kBar J ⧸ Subgroup.center (kBar J)) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (kBar J)
  let ψ : ↥V →* MulAut (kBar J ⧸ Subgroup.center (kBar J)) :=
    cq.comp ((MulAut.mapQuotient (pPrimeCore 2 ↥J)).comp
      (J.normalizerMonoidHom.comp (Subgroup.inclusion hVnJ)))
  have hψ_apply : ∀ u : ↥V, ψ u = cq (MulAut.mapQuotient (pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩)) := fun _ => rfl
  have hψ_ker : ∀ u : ↥V, ψ u = 1 → u = 1 := by
    intro u hu
    have hα : MulAut.mapQuotient (pPrimeCore 2 ↥J)
        (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩) = 1 := by
      have hq : cq (MulAut.mapQuotient (pPrimeCore 2 ↥J)
          (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩)) = cq 1 := by
        rw [map_one]
        exact (hψ_apply u).symm.trans hu
      have : Group.IsPerfect (kBar J) := hperf
      exact (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
        (kBar J)) hq
    have hαr : MulAut.mapQuotient (pPrimeCore 2 ↥J)
        (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩) ∈
        (MulAut.conj : kBar J →* MulAut (kBar J)).range := by
      rw [hα]
      exact MonoidHom.mem_range.mpr ⟨1, map_one MulAut.conj⟩
    apply Subtype.ext
    exact hVinn u.1 u.2 (hVnJ u.2) hαr
  have hψ_inj : Function.Injective ψ := by
    intro u w huw
    have h1 : ψ (u * w⁻¹) = 1 := by rw [map_mul, map_inv, huw, mul_inv_cancel]
    have h2 : u * w⁻¹ = 1 := hψ_ker (u * w⁻¹) h1
    calc u = u * w⁻¹ * w := by group
      _ = 1 * w := by rw [h2]
      _ = w := by group
  have hA2 : IsPGroup 2 ψ.range := by
    rintro ⟨g, hg⟩
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨n, hn⟩ := hV2 u
    refine ⟨n, Subtype.ext ?_⟩
    show (ψ u) ^ 2 ^ n = 1
    rw [← map_pow, hn, map_one]
  have hAcard : Nat.card ↥ψ.range = Nat.card ↥V :=
    (Nat.card_congr (MonoidHom.ofInjective hψ_inj).toEquiv).symm
  have h4' : 4 ≤ Nat.card ↥ψ.range := by rw [hAcard]; exact hV4
  have hinn : ∀ a ∈ ψ.range, a ∈ (MulAut.conj :
      (kBar J ⧸ Subgroup.center (kBar J)) →*
        MulAut (kBar J ⧸ Subgroup.center (kBar J))).range → a = 1 := by
    intro a ha hinner
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp ha
    have hαr : MulAut.mapQuotient (pPrimeCore 2 ↥J)
        (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩) ∈
        (MulAut.conj : kBar J →* MulAut (kBar J)).range := by
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hinner
      have h1 : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient
          (MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩)) =
          MulAut.conj q := (hψ_apply u).symm.trans hq.symm
      have : Group.IsPerfect (kBar J) := hperf
      obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.WeakClosure81.isInner_of_onCenterQuotient_inner
        (MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩))
        ⟨q, fun x => by rw [h1, MulAut.conj_apply]⟩
      exact MonoidHom.mem_range.mpr ⟨g, MulEquiv.ext fun x => (hg x).symm⟩
    have hu1 : u = 1 := by
      apply Subtype.ext
      exact hVinn u.1 u.2 (hVnJ u.2) hαr
    rw [hu1, map_one]
  have hY : CFSG.Blueprint.LieModel (kBar J ⧸ Subgroup.center (kBar J)) .PSL 3 2 2 := by
    obtain ⟨e⟩ := hJ.2
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center (kBar J)) (Subgroup.center fullQ) e
        (Subgroup.map_center_eq e)).symm hL34
  obtain ⟨b, hbA, hb1, hb2, hbsimple, hbnonab, hbcard, hbfix⟩ :=
    CFSG.ComponentClassification.PSL3Four.exists_field_mem_of_four_le_card hY hA2 hinn h4'
  obtain ⟨v₀, hv₀val⟩ := MonoidHom.mem_range.mp hbA
  let αv : MulAut (kBar J) := MulAut.mapQuotient (pPrimeCore 2 ↥J)
    (J.normalizerMonoidHom ⟨v₀.1, hVnJ v₀.2⟩)
  have hβ : cq αv = b := (hψ_apply v₀).symm.trans hv₀val
  have hv₀_sq : v₀.1 ^ 2 = 1 := by
    have h : ψ (v₀ ^ 2) = 1 := by rw [map_pow, hv₀val, pow_two, hb2]
    have h2 : v₀ ^ 2 = 1 := hψ_inj (by rw [h, map_one])
    simpa using congrArg (fun z : ↥V => z.1) h2
  have hv₀_ne : v₀.1 ≠ 1 := by
    intro h1
    have h2 : v₀ = 1 := Subtype.ext h1
    rw [h2, map_one] at hv₀val
    exact hb1 hv₀val.symm
  have hv₀2 : orderOf v₀.1 = 2 := by
    have hdvd : orderOf v₀.1 ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hv₀_sq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv₀_ne
    · exact h
  have hfixb : CFSG.Open.GLAPLayer 2 (fixSubgroup b) = fixSubgroup b := by
    apply le_antisymm
    · rw [CFSG.Open.GLAPLayer]
      exact sSup_le fun M hM => hM.1
    · have : IsSimpleGroup ↥(fixSubgroup b) := hbsimple
      refine le_glaPLayer_of_normal_simple Nat.prime_two (Y := fixSubgroup b) le_rfl ?_ hbnonab ?_
      · have htop : (fixSubgroup b).subgroupOf (fixSubgroup b) = ⊤ := by
          ext x; simp
        rw [htop]; infer_instance
      · rw [hbcard]; norm_num
  have hαβ : ∀ k : kBar J, π (αv k) = cq αv (π k) := by
    intro k
    exact (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk αv k).symm
  have hker : π.ker ≤ Subgroup.center (kBar J) := le_of_eq (QuotientGroup.ker_mk' _)
  have hmapGL : (CFSG.Open.GLAPLayer 2 (fixSubgroup αv)).map π = fixSubgroup b := by
    have h := map_glaPLayer_fixSubgroup_eq π hker αv (cq αv) hαβ
      (QuotientGroup.mk'_surjective (Subgroup.center (kBar J))) Nat.prime_two
    rw [h, hβ, hfixb]
  have hHmap : (fixSubgroup αv).map π = fixSubgroup b := by
    apply le_antisymm
    · calc (fixSubgroup αv).map π ≤ fixSubgroup (cq αv) :=
            map_fixSubgroup_le π hker αv (cq αv) hαβ
        _ = fixSubgroup b := by rw [hβ]
    · calc fixSubgroup b = (CFSG.Open.GLAPLayer 2 (fixSubgroup αv)).map π := hmapGL.symm
        _ ≤ (fixSubgroup αv).map π := Subgroup.map_mono (by
            rw [CFSG.Open.GLAPLayer]
            exact sSup_le fun M hM => hM.1)
  have hker2 : IsPGroup 2 π.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (Subgroup.center (kBar J))).ker
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 4) (by rw [hcenter_card]; norm_num)
  have hO : pPrimeCore 2 ↥(fixSubgroup αv) = ⊥ :=
    pPrimeCore_eq_bot_of_map_isSimpleGroup π hker2 (by rw [hHmap]; exact hbsimple)
      (by rw [hHmap, hbcard]; norm_num)
  have hv₀Z : v₀.1 ∈ zStar (Kz fullQ v) := by
    rw [hKz_v]
    exact hVZ v₀.2
  obtain ⟨Jf, hJf⟩ := exists_pump_family_of_mem_zStar_kz (fullQ := fullQ) hnonab hv₀2 hv₀Z
  have hlt : PumpUpLT 2 v L v₀.1 (Jf L) := hJf L hL
  have hyZ : ∀ u : ↥V, u.1 ∈ zStar (Kz fullQ v₀.1) := by
    intro u
    have hpow : ∃ n : ℕ, u.1 ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hV2 u
      exact ⟨n, by simpa using congrArg (fun z : ↥V => z.1) hn⟩
    have hcent : u.1 ∈ Subgroup.centralizer ({v₀.1} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hVc u.1 u.2 v₀.1 v₀.2)
    exact mem_zStar_kz_of_pumpUpLT (fullQ := fullQ) (x := v) (t := v₀.1) (y := u.1)
      (K := L) (K' := Jf L) hL hlt (hVZ u.2) hpow hcent
  have hxv' : x ∈ Subgroup.centralizer ({v₀.1} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hVx v₀.2)).symm
  have htriv : ∀ u : ↥V, ∀ k ∈ CFSG.Open.GLAPLayer 2 (fixSubgroup αv),
      MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩) k = k := by
    intro u k hk
    exact mapQuotient_eq_self_of_mem_glaPLayer (fullQ := fullQ) hx2 hv₀_sq hxv'
      (hJ.1.1.2.2) (hVnJ v₀.2) (hVnJ u.2)
      (Subgroup.mem_centralizer_singleton_iff.mpr (hVc u.1 u.2 v₀.1 v₀.2)) (hyZ u) hO k hk
  have hfixpt : ∀ u : ↥V, ∀ c : kBar J ⧸ Subgroup.center (kBar J),
      b c = c → ψ u c = c := by
    intro u c hc
    have hc' : c ∈ (CFSG.Open.GLAPLayer 2 (fixSubgroup αv)).map π := by
      rw [hmapGL]
      exact mem_fixSubgroup.mpr hc
    obtain ⟨k, hk, hkc⟩ := hc'
    have hαu : MulAut.mapQuotient (pPrimeCore 2 ↥J)
        (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩) k = k := htriv u k hk
    calc ψ u c = ψ u (π k) := by rw [hkc]
      _ = cq (MulAut.mapQuotient (pPrimeCore 2 ↥J)
            (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩)) (π k) := by rw [hψ_apply u]
      _ = π (MulAut.mapQuotient (pPrimeCore 2 ↥J)
            (J.normalizerMonoidHom ⟨u.1, hVnJ u.2⟩) k) :=
            CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ k
      _ = π k := by rw [hαu]
      _ = c := hkc
  have hb2' : b ^ 2 = 1 := by rw [pow_two]; exact hb2
  have hborder : orderOf b = 2 := by
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hAle : ψ.range ≤ Subgroup.zpowers b := by
    intro c hc
    have hfixc : ∀ y : kBar J ⧸ Subgroup.center (kBar J), b y = y → c y = y := by
      intro y hy
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hc
      exact hfixpt u y hy
    rcases hbfix c hc hfixc with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers b
  have hle2 : Nat.card ↥ψ.range ≤ 2 := by
    have h1 : Nat.card ↥ψ.range ≤ Nat.card ↥(Subgroup.zpowers b) := Subgroup.card_le_of_le hAle
    have h2 : Nat.card ↥(Subgroup.zpowers b) = 2 := by rw [Nat.card_zpowers, hborder]
    rwa [h2] at h1
  omega


end CFSG.GH74.GLS.NT44

end
