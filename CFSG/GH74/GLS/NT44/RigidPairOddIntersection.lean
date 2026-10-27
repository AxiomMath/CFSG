module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GH74.Generic.BProg.B3.S3T3E8B
import CFSG.GH74.GLS.NT44.RigidCentralInvolution
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
import CFSG.GH74.GLS.NT44.RigidCenterInclusion
import CFSG.GH74.GLS.NT44.RigidPump
import CFSG.GH74.GLS.Bg.Iii2.L41Comp
import CFSG.GH74.GLS.C3.Layer1.Th2P72cR16
import CFSG.GH74.GLS.Bg.Pu5.L295ADiag
import CFSG.GH74.GLS.NT44.RigidPumpExistence
import CFSG.GH74.GLS.NT44.RigidCoverage
import CFSG.GH74.GLS.NT44.RigidCenterSylow
import CFSG.GH74.GLS.NT44.RigidPairSections
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.GLS.TwoThin.Rank

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
open CFSG.GH74.Generic.BProg.B3 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem oddInter_original_intersection_involution [Finite G] {x v : G} {I L : Subgroup G}
    (heven : Even (Nat.card ↥(CxK x I ⊓ CxK v L))) :
    ∃ u : G, orderOf u = 2 ∧ u ∈ centralizer ({x} : Set G) ∧
      u ∈ centralizerSection I (pPrimeCoreOf 2 I) ∧
      u ∈ centralizer ({v} : Set G) ∧
      u ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CxK x I ⊓ CxK v L)) 2 heven.two_dvd
  exact ⟨u, (Subgroup.orderOf_coe u).trans hu, u.2.1.1, u.2.1.2, u.2.2.1, u.2.2.2⟩

private theorem oddInter_immediate_x_section {fullQ : Type} [Group fullQ] {x v u : G}
    {L : Subgroup G} (hL : L ∈ RigidSet fullQ v)
    (huL : u ∈ centralizerSection L (pPrimeCoreOf 2 L))
    (hdep : u = x ∨ u = x * v) :
    x ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  rcases hdep with rfl | rfl
  · exact huL
  have hvL : v ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun l hl => (mem_centralizer_singleton_iff.mp (hL.1.1.2.2.1 hl)).symm)
      (Subgroup.map_subtype_le _)
  have hvv : v * v = 1 := by simpa only [hL.1.1.1, pow_two] using pow_orderOf_eq_one v
  simpa only [mul_assoc, hvv, mul_one] using
    (centralizerSection L (pPrimeCoreOf 2 L)).mul_mem huL hvL

private theorem oddInter_rank_at_original_u [Finite G] {fullQ : Type} [Group fullQ] {x v u : G}
    {J L : Subgroup G} (hJ : J ∈ RigidSet fullQ x) (hL : L ∈ RigidSet fullQ v)
    (hvx : v * x = x * v)
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hu2 : orderOf u = 2) (hux : u * x = x * u) (huv : u * v = v * u)
    (hneX : u ≠ x) (hneXV : u ≠ x * v) :
    3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
  have hx2 : orderOf x = 2 := hJ.1.1.1
  have hv2 : orderOf v = 2 := hL.1.1.1
  have hxx : x * x = 1 := by simpa only [hx2, pow_two] using pow_orderOf_eq_one x
  have hvv : v * v = 1 := by simpa only [hv2, pow_two] using pow_orderOf_eq_one v
  have huu : u * u = 1 := by simpa only [hu2, pow_two] using pow_orderOf_eq_one u
  have hx1 : x ≠ 1 := by intro h; simp [h] at hx2
  have hu1 : u ≠ 1 := by intro h; simp [h] at hu2
  have hxJ : x ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun j hj => (mem_centralizer_singleton_iff.mp (hJ.1.1.2.2.1 hj)).symm)
      (Subgroup.map_subtype_le _)
  have hvE : v ∉ zpowers x := fun h => hvact (zpowers_le.mpr hxJ h)
  by_cases huvEq : u = v
  · subst u
    simpa [oBound] using hL.1.1.2.1
  have hc : ∀ a ∈ zpowers x, a * v = v * a := fun a ha =>
    mem_centralizer_singleton_iff.mp
      ((zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hvx.symm)) ha)
  have huE : u ∉ zpowers x ⊔ zpowers v := by
    intro h
    obtain ⟨a, ha, hua⟩ := S3Sec29H.mem_sup_zpowers hvv hc h
    rcases P92.mem_zpowers_involution hxx ha with rfl | rfl
    · rcases hua with h | h
      · exact hu1 h
      · exact huvEq (by simpa using h)
    · exact hua.elim hneX hneXV
  obtain ⟨hE, hcard⟩ := S3T3.e8_of_triple hxx hx1 hvv huu hvx.symm hux.symm huv.symm hvE huE
  let E : Subgroup G := zpowers x ⊔ zpowers v ⊔ zpowers u
  let _ : IsElementaryAbelian 2 E := hE
  have hEC : E ≤ centralizer ({u} : Set G) :=
    sup_le (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hux.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr huv.symm)))
      (zpowers_le.mpr (by simp [mem_centralizer_singleton_iff]))
  have hr : pRank 2 E = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa [E] using hcard)
  rw [← hr]
  exact C3.Layer1.Back.pRank_mono' hEC

private theorem oddInter_sylow_contains_original_triple [Finite G] {x v u : G}
    (hx : x * x = 1) (hv : v * v = 1) (hu : u * u = 1)
    (hxv : x * v = v * x) (hxu : x * u = u * x) (hvu : v * u = u * v) :
    ∃ S : Subgroup G, IsSylowOf 2 S (centralizer ({x} : Set G)) ∧
      x ∈ S ∧ v ∈ S ∧ u ∈ S := by
  let E : Subgroup G := zpowers x ⊔ zpowers v ⊔ zpowers u
  have hEu : zpowers x ⊔ zpowers v ≤ centralizer ({u} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxu))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hvu))
  have hEV : zpowers x ≤ centralizer ({v} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxv)
  let _ : IsElementaryAbelian 2 E :=
    S3Sec29H.isElementaryAbelian_sup_zpowers
      (S3Sec29H.isElementaryAbelian_sup_zpowers (S3Sec29H.isElementaryAbelian_zpowers hx)
        hv (fun a ha => mem_centralizer_singleton_iff.mp (hEV ha)))
      hu (fun a ha => mem_centralizer_singleton_iff.mp (hEu ha))
  have hEC : E ≤ centralizer ({x} : Set G) :=
    sup_le (sup_le (zpowers_le.mpr (by simp [mem_centralizer_singleton_iff]))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxv.symm)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxu.symm))
  obtain ⟨S, hS, hES⟩ := P92.exists_sylow_ge (IsElementaryAbelian.isPGroup 2 E) hEC
  exact ⟨S, hS, hES (mem_sup_left (mem_sup_left (mem_zpowers x))),
    hES (mem_sup_left (mem_sup_right (mem_zpowers v))), hES (mem_sup_right (mem_zpowers u))⟩

private theorem oddInter_original_W [Finite G] {fullQ : Type} [Group fullQ] {x : G} {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer ({x} : Set G))) (hxS : x ∈ S)
    (hxP : x ∈ Kz fullQ x) :
    IsSylowOf 2 (S ⊓ zStar (Kz fullQ x)) (zStar (Kz fullQ x)) ∧
      x ∈ S ⊓ zStar (Kz fullQ x) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC := kz_le_centralizer (Q := fullQ) (z := x)
  refine ⟨hS.inf_of_le_normalizer (inf_le_left.trans hPC) ?_, hxS, ?_⟩
  · intro c hc
    exact Alt51.mem_normalizer_zStar (centralizer_le_normalizer_kz hc)
  · exact Alt51.z_mem_zStar hPC hxP

private theorem oddInter_individual_sylow_and_even [Finite G] {fullQ : Type} [Group fullQ] {x : G}
    {S I : Subgroup G} (hI : I ∈ RigidSet fullQ x)
    (hS : IsSylowOf 2 S (centralizer ({x} : Set G)))
    (h16 : Nat.card (center fullQ) = 16) :
    IsSylowOf 2 (S ⊓ zStar I) (zStar I) ∧ Even (Nat.card ↥(S ⊓ zStar I)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSI := P92.sylow_inf hI hS
  have hSZ : IsSylowOf 2 (S ⊓ zStar I) (zStar I) := by
    have h := hSI.inf_of_le_normalizer (show zStar I ≤ I from inf_le_left)
      (fun i hi => Alt51.mem_normalizer_zStar (Subgroup.le_normalizer hi))
    simpa only [inf_assoc, inf_eq_right.mpr (show zStar I ≤ I from inf_le_left)] using h
  obtain ⟨b, hb, hb2⟩ := exists_involution_inf_zStar_of_mem_rigidSet hI hS h16
  refine ⟨hSZ, even_iff_two_dvd.mpr ?_⟩
  have hd := orderOf_dvd_natCard (⟨b, hb⟩ : ↥(S ⊓ zStar I))
  simpa only [Subgroup.orderOf_mk, hb2] using hd

open CFSG.GH74.GLS.Stage1.Thm2.Recip

private theorem oddInter_even_zStar {fullQ : Type} [Group fullQ] {s : G} {B : Subgroup G}
    (hB : IsRigidOfType fullQ s B) (h16 : Nat.card (center fullQ) = 16) :
    Even (Nat.card (zStar B)) := by
  let f : zStar B →* center (Hat B) :=
    ((hatMk B).comp (inclusion (show zStar B ≤ B from inf_le_left))).codRestrict _
      (fun b => (Alt51.mem_zStar_iff_hat_mem_center (K := B) ⟨b, b.2.1⟩).mp b.2)
  have hsur : Function.Surjective f := by
    intro c
    obtain ⟨b, hb⟩ := hatMk_surjective B c.val
    have hbc : (b : G) ∈ zStar B :=
      (Alt51.mem_zStar_iff_hat_mem_center b).mpr (hb ▸ c.2)
    refine ⟨⟨b, hbc⟩, ?_⟩
    apply Subtype.ext
    exact hb
  have hc : Nat.card (center (Hat B)) = 16 := by
    obtain ⟨e⟩ := hB.2
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans h16
  have hd := Subgroup.card_dvd_of_surjective hsur
  rw [hc] at hd
  exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 16).trans hd)

private theorem oddInter_fixed_in_intrinsic_center [Finite G] {fullQ : Type} [Group fullQ] {t s : G}
    {B : Subgroup G} (hB : IsRigidOfType fullQ t B)
    (h16 : Nat.card (center fullQ) = 16) (hs : orderOf s = 2)
    (hsSec : s ∈ centralizerSection B (pPrimeCoreOf 2 B)) :
    ∃ w : G, w ∈ zStar B ∧ orderOf w = 2 ∧ w ∈ centralizer ({s} : Set G) := by
  exact CFSG.ComponentClassification.SubgroupFixedInvolution.involution_normalizing
    (zStar B) (oddInter_even_zStar hB h16) s hs (Alt51.mem_normalizer_zStar hsSec.1)

open CFSG.GH74.GLS.Stage1.Thm3.Sec4

private theorem oddInter_actual_orbit_fixed_a [Finite G] {fullQ : Type} [Group fullQ] {x v u : G}
    {I S : Subgroup G} (hI : I ∈ RigidSet fullQ x)
    (hS : IsSylowOf 2 S (centralizer ({x} : Set G)))
    (h16 : Nat.card (center fullQ) = 16) (hv2 : orderOf v = 2) (hu2 : orderOf u = 2)
    (hvS : v ∈ S) (huS : u ∈ S) (hvu : v * u = u * v)
    (huI : u ∈ centralizerSection I (pPrimeCoreOf 2 I))
    (hRu : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G))) :
    ∃ a : G, orderOf a = 2 ∧ a ∈ S ⊓ zStar (Kz fullQ x) ∧
      a ∈ centralizer ({v} : Set G) ∧ a ∈ centralizer ({u} : Set G) ∧
      a ∈ zStar (Kz fullQ u) := by
  let B : Subgroup G := S ⊓ zStar I
  let B0 : Subgroup G := B ⊔ cmap v B
  have hIv : cmap v I ∈ RigidSet fullQ x := by
    have h := isRigidOfType_conj hI v
    have hvx := mem_centralizer_singleton_iff.mp (hS.le hvS)
    have he : v * x * v⁻¹ = x := by rw [hvx]; group
    rwa [he] at h
  have hbu : B ≤ centralizer ({u} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (Bg.Pu5.comm_of_mem_cSec hS.isPGroup hb.1 huS hb.2.1 huI)
  have hvu' : v * u * v⁻¹ = u := by rw [hvu]; group
  have huIv : u ∈ centralizerSection (cmap v I) (pPrimeCoreOf 2 (cmap v I)) := by
    have h := Bg.Pu5.conj_mem_cSec_cmap huI v
    rwa [hvu'] at h
  have hBS : cmap v B ≤ S := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp (Subgroup.le_normalizer hvS) b).mp hb.1
  have hBZ : cmap v B ≤ zStar (cmap v I) := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb.2.1, rfl⟩, Bg.Pu5.conj_mem_cSec_cmap hb.2.2 v⟩
  have hbvu : cmap v B ≤ centralizer ({u} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (Bg.Pu5.comm_of_mem_cSec hS.isPGroup (hBS hb) huS (hBZ hb).1 huIv)
  have hB0u : B0 ≤ centralizer ({u} : Set G) := sup_le hbu hbvu
  have hB0W : B0 ≤ S ⊓ zStar (Kz fullQ x) := by
    apply sup_le
    · exact fun _ hb => ⟨hb.1, zStar_le_zStar_kz_of_mem_rigidSet hI hb.2⟩
    · exact fun _ hb => ⟨hBS hb, zStar_le_zStar_kz_of_mem_rigidSet hIv (hBZ hb)⟩
  have hvBB : cmap v (cmap v B) = B := by
    have h := cmap_inv_cancel v B
    rwa [inv_eq_self_of_orderOf_eq_two hv2] at h
  have hvB0 : v ∈ normalizer (B0 : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (B ⊔ cmap v B).map (MulAut.conj v).toMonoidHom = B ⊔ cmap v B
    rw [Subgroup.map_sup]
    change cmap v B ⊔ cmap v (cmap v B) = B ⊔ cmap v B
    rw [hvBB, sup_comm]
  have hB0even : Even (Nat.card B0) := by
    have hB := (oddInter_individual_sylow_and_even hI hS h16).2
    exact even_iff_two_dvd.mpr
      (hB.two_dvd.trans (Subgroup.card_dvd_of_le (show B ≤ B0 from le_sup_left)))
  obtain ⟨a, ha, ha2, hav⟩ :=
    ComponentClassification.SubgroupFixedInvolution.involution_normalizing B0 hB0even v hv2 hvB0
  have hpow : ∀ b ∈ S, ∃ n : ℕ, b ^ (2 ^ n) = 1 := by
    intro b hb
    obtain ⟨n, hn⟩ := hS.isPGroup.exists_pow_pow_eq_one (⟨b, hb⟩ : S)
    exact ⟨n, congrArg Subtype.val hn⟩
  obtain ⟨M, hM⟩ := TwoThin.exists_pumpup_of_involution hI.1.1.1 hu2 hI.1.1.2.2
    (hS.le huS) huI hI.1.1 hRu
  obtain ⟨Mv, hMv⟩ := TwoThin.exists_pumpup_of_involution hIv.1.1.1 hu2 hIv.1.1.2.2
    (hS.le huS) huIv hIv.1.1 hRu
  have hB0Zu : B0 ≤ zStar (Kz fullQ u) := by
    apply sup_le
    · intro b hb
      exact mem_zStar_kz_of_pumpUpLT hI hM hb.2 (hpow b hb.1) (hbu hb)
    · intro b hb
      exact mem_zStar_kz_of_pumpUpLT hIv hMv (hBZ hb) (hpow b (hBS hb)) (hbvu hb)
  exact ⟨a, ha2, hB0W ha, hav, hB0u ha, hB0Zu ha⟩

open CFSG.GH74.GLS.TwoThin
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
open CFSG.GH74.GLS.Bg.Iii2.L41 CFSG.LocalAnalysis.ComponentInitial

private theorem oddInter_normalizes_from_fixed_image [Finite G] {t r : G} {X D : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) (hD : IsPCompIn 2 X D)
    (hrX : r ∈ X)
    (hcen : ∀ w ∈ bar t D, sbar r (hXt hrX) * w * (sbar r (hXt hrX))⁻¹ = w) :
    r ∈ normalizer (D : Set G) := by
  have hXeq : cmap r X = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hrX)
  have hDc : IsPCompIn 2 X (cmap r D) := by
    have h := isPCompIn_cmap hD r
    rwa [hXeq] at h
  have hbar : bar t (cmap r D) = bar t D := by
    rw [CFSG.GH74.GLS.Bg.Iii2.L41.bar_cmap (hXt hrX)]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      change sbar r (hXt hrX) * u * (sbar r (hXt hrX))⁻¹ ∈ bar t D
      rw [hcen u hu]
      exact hu
    · intro hw
      exact ⟨w, hw, hcen w hw⟩
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (CFSG.GH74.GLS.Bg.Iii2.L41.eq_of_bar_eq hXt hDc hD hbar)

private theorem oddInter_image_fixed_from_ambient_comm {t r : G} {H : Subgroup G}
    (_hHt : H ≤ centralizer ({t} : Set G)) (hrt : r ∈ centralizer ({t} : Set G))
    (hcomm : ∀ d ∈ H, ⁅d, r⁆ ∈ pPrimeCoreOf 2 (centralizer ({t} : Set G))) :
    ∀ w ∈ bar t H, sbar r hrt * w * (sbar r hrt)⁻¹ = w := by
  rintro _ ⟨m, hm, rfl⟩
  have hmH : (m : G) ∈ H := Subgroup.mem_subgroupOf.mp hm
  have hcY : ⁅(m : G), r⁆ ∈ centralizer ({t} : Set G) := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem m.2 hrt) (inv_mem m.2)) (inv_mem hrt)
  have h2 := CFSG.GH74.GLS.Bg.Pu5.barMk_eq_one_of_mem_pPrimeCoreOf_self
    (hcomm m hmH) hcY
  have h3 : (⟨⁅(m : G), r⁆, hcY⟩ : centralizer ({t} : Set G)) =
      m * ⟨r, hrt⟩ * m⁻¹ * ⟨r, hrt⟩⁻¹ := rfl
  rw [h3] at h2
  simp only [map_mul, map_inv] at h2
  change barMk _ ⟨r, hrt⟩ * barMk _ m * (barMk _ ⟨r, hrt⟩)⁻¹ = barMk _ m
  generalize barMk ↥(centralizer ({t} : Set G)) m = a at h2 ⊢
  generalize barMk ↥(centralizer ({t} : Set G)) ⟨r, hrt⟩ = b at h2 ⊢
  have h5 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h2
  have h4 : a * b = b * a := by
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h5]
  calc b * a * b⁻¹ = (a * b) * b⁻¹ := by rw [h4]
    _ = a := by group

private theorem oddInter_actual_rigid_support [Finite G] {fullQ : Type} [Group fullQ]
    {s t : G} {B M : Subgroup G} (hB : IsRigidOfType fullQ s B)
    (hlt : PumpUpLT 2 s B t M) :
    ∃ D : Subgroup G, IsLam s t B D ∧ bar t D ≤ bar t (Kz fullQ t) := by
  have hst := TwoThin.mem_centralizer_symm hlt.2.2.1
  obtain ⟨eBM⟩ := hB.1.2 t M (LongPumpUp.single' hlt)
  have hcard : hatCard M ≤ hatCard B := (Nat.card_congr eBM.toEquiv).le
  obtain ⟨D, hD, -, -, -, -, hcases⟩ := rigid_step hlt hst hcard
  have hM : IsRigidOfType fullQ t M := P92.isRigidOfType_of_pumpUpLT hB hlt
  have hsfix : s * t * s⁻¹ = t := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hst
    calc s * t * s⁻¹ = t * s * s⁻¹ := by rw [h]
      _ = t := by group
  have hMs : IsRigidOfType fullQ t (cmap s M) := by
    have h := isRigidOfType_conj (Q := fullQ) hM s
    rwa [hsfix] at h
  have hbarM : bar t M ≤ bar t (Kz fullQ t) :=
    CFSG.GH74.GLS.Bg.Pu5.bar_mono (le_sSup hM)
  have hbarMs : bar t (cmap s M) ≤ bar t (Kz fullQ t) :=
    CFSG.GH74.GLS.Bg.Pu5.bar_mono (le_sSup hMs)
  refine ⟨D, hD, ?_⟩
  rcases hcases with ⟨-, hv⟩ | ⟨-, hAB, -, hd⟩
  · rw [hv]; exact hbarM
  · rw [hd]
    have hs2 : orderOf (sbar s hst) = 2 := orderOf_sbar hlt.1.1 hst
    have hinv : (sbar s hst)⁻¹ = sbar s hst := inv_eq_self_of_orderOf_eq_two hs2
    have hconj : conjSub (sbar s hst)⁻¹ (bar t M) = bar t (cmap s M) := by
      rw [hinv]
      exact (CFSG.GH74.GLS.Bg.Iii2.CMEngine.bar_cmap (u := t) (q := s) hst M).symm
    have hother : conjSub (sbar s hst)⁻¹ (bar t M) ≤ bar t (Kz fullQ t) := by
      rw [hconj]; exact hbarMs
    rintro _ ⟨c, rfl⟩
    exact (sup_le hbarM hother) (swapDiag_mem_sup hAB c)

private theorem oddInter_actual_transfer [Finite G] {fullQ : Type} [Group fullQ]
    {s t r : G} {B M : Subgroup G} (hB : IsRigidOfType fullQ s B)
    (hlt : PumpUpLT 2 s B t M)
    (hrs : r ∈ centralizer ({s} : Set G)) (hrt : r ∈ centralizer ({t} : Set G))
    (hrP : r ∈ centralizerSection (Kz fullQ t) (pPrimeCoreOf 2 (Kz fullQ t))) :
    r ∈ centralizerSection B (pPrimeCoreOf 2 B) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD, hsupport⟩ := oddInter_actual_rigid_support hB hlt
  have hPt := kz_le_centralizer (Q := fullQ) (z := t)
  have hPnorm : ((Kz fullQ t).subgroupOf (centralizer ({t} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPt).mpr
      (centralizer_le_normalizer_kz (Q := fullQ) (z := t))
  have hOP := CFSG.GH74.GLS.pPrimeCoreOf_le_of_normal 2 hPt hPnorm
  have hPfixed := oddInter_image_fixed_from_ambient_comm hPt hrt
    (fun d hd => hOP (hrP.2.2 d hd))
  have hDfixed : ∀ w ∈ bar t D, sbar r hrt * w * (sbar r hrt)⁻¹ = w :=
    fun w hw => hPfixed w (hsupport hw)
  have hrX : r ∈ centralizer ({s} : Set G) ⊓ centralizer ({t} : Set G) := ⟨hrs, hrt⟩
  have hrND := oddInter_normalizes_from_fixed_image inf_le_right hD.pcW hrX hDfixed
  have hDB : D ≤ B := hD.le.trans inf_le_left
  have hDt : D ≤ centralizer ({t} : Set G) := hD.le.trans inf_le_right
  have hrD := CFSG.GH74.GLS.Bg.Iii2.L41.mem_cSec_of_bar hDt hrt hrND hDfixed
  have hOD := CFSG.GH74.GLS.Bg.Iii2.L41.pPrimeCoreOf_le_of_cover hDB hD.cover
  have hBc := hB.1.1.2.2
  have hOB := CFSG.GH74.GLS.Th2.Obs.pPrimeCoreOf_le_of_isPCompIn hBc
  have hDs : D ≤ centralizer ({s} : Set G) := hDB.trans hBc.1
  have hDfixeds := oddInter_image_fixed_from_ambient_comm hDs hrs
    (fun d hd => hOB (hOD (hrD.2.2 d hd)))
  have hbars : bar s D = bar s B := by
    apply le_antisymm
    · rintro _ ⟨d, hd, rfl⟩
      exact ⟨d, Subgroup.mem_subgroupOf.mpr (hDB (Subgroup.mem_subgroupOf.mp hd)), rfl⟩
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨d, hd, o, ho, hdo⟩ := hD.cover b (Subgroup.mem_subgroupOf.mp hb)
      have hoC : o ∈ centralizer ({s} : Set G) := hBc.1 (TwoThin.pPrimeCoreOf_le B ho)
      have ho1 := CFSG.GH74.GLS.Bg.Pu5.barMk_eq_one_of_mem_pPrimeCoreOf_self (hOB ho) hoC
      refine ⟨⟨d, hDs hd⟩, Subgroup.mem_subgroupOf.mpr hd, ?_⟩
      have hbdo : b = (⟨d, hDs hd⟩ : centralizer ({s} : Set G)) * ⟨o, hoC⟩ := Subtype.ext hdo
      rw [hbdo, map_mul, ho1, mul_one]
  have hBfixed : ∀ w ∈ bar s B, sbar r hrs * w * (sbar r hrs)⁻¹ = w := by
    rw [← hbars]; exact hDfixeds
  have hrNB := oddInter_normalizes_from_fixed_image le_rfl hBc hrs hBfixed
  exact CFSG.GH74.GLS.Bg.Iii2.L41.mem_cSec_of_bar hBc.1 hrs hrNB hBfixed

private theorem oddInter_transport_original_x [Finite G] {fullQ : Type} [Group fullQ] [IsSimpleGroup G]
    {x v u a : G} {J L S : Subgroup G} (hnonab : ∃ b c : G, b * c ≠ c * b)
    (hJ : J ∈ RigidSet fullQ x) (hL : L ∈ RigidSet fullQ v)
    (hS : IsSylowOf 2 S (centralizer ({x} : Set G))) (hxS : x ∈ S)
    (hxP : x ∈ Kz fullQ x) (hvx : v * x = x * v)
    (hu2 : orderOf u = 2) (huCv : u ∈ centralizer ({v} : Set G))
    (huL : u ∈ centralizerSection L (pPrimeCoreOf 2 L))
    (hRu : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)))
    (ha2 : orderOf a = 2) (haW : a ∈ S ⊓ zStar (Kz fullQ x))
    (haCv : a ∈ centralizer ({v} : Set G)) (haCu : a ∈ centralizer ({u} : Set G))
    (haPu : a ∈ zStar (Kz fullQ u))
    (hmax : ∀ t : G, orderOf t = 2 →
      Nat.card ↥(RigidSet fullQ t) ≤ Nat.card ↥(RigidSet fullQ x)) :
    x ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  obtain ⟨Mu, hMu⟩ := TwoThin.exists_pumpup_of_involution hL.1.1.1 hu2 hL.1.1.2.2
    huCv huL hL.1.1 hRu
  have haL := oddInter_actual_transfer hL hMu haCv haCu haPu.2
  obtain ⟨hW, hxW⟩ := oddInter_original_W hS hxS hxP
  obtain ⟨F, hF⟩ := exists_pump_family_of_mem_zStar_kz hnonab ha2 haW.2
  have hxa : x * a = a * x := Bg.Pu5.comm_of_mem_cSec hS.isPGroup hxS haW.1 hxP haW.2.2
  have hxaC : x ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hxa
  obtain ⟨hcovx, hcova⟩ := rigid_product_coverage F hxaC hF
    (by simpa only [Nat.card_coe_set_eq] using hmax a ha2)
  have hWa := isSylowOf_zStar_kz_of_coverage hW haW hcovx hcova
  have hxZa := hWa.le hxW
  have hRx : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := by simpa [oBound] using hJ.1.1.2.1
  have hRG : 3 ≤ pRank 2 G := hRx.trans (Bg.pRank_subgroup_le (by norm_num) _)
  have hRa := TwoThin.rankThreeCentralizers G (inferInstance : IsSimpleGroup G) hnonab hRG a ha2
  obtain ⟨Ma, hMa⟩ := TwoThin.exists_pumpup_of_involution hL.1.1.1 ha2 hL.1.1.2.2
    haCv haL hL.1.1 hRa
  exact oddInter_actual_transfer hL hMa
    (mem_centralizer_singleton_iff.mpr hvx.symm) hxaC hxZa.2

private theorem oddInter_false_of_original_x_mem_section [Finite G] {fullQ : Type} [Group fullQ] {x v : G}
    {J L : Subgroup G} (hJ : J ∈ RigidSet fullQ x) (hL : L ∈ RigidSet fullQ v)
    (h16 : Nat.card (center fullQ) = 16) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (hxL : x ∈ centralizerSection L (pPrimeCoreOf 2 L)) : False := by
  obtain ⟨w, hwL, hw2, hwCx⟩ := oddInter_fixed_in_intrinsic_center hL h16 hJ.1.1.1 hxL
  have hR : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := by simpa [oBound] using hJ.1.1.2.1
  obtain ⟨M, hM⟩ := TwoThin.exists_pumpup_of_involution hL.1.1.1 hJ.1.1.1 hL.1.1.2.2
    (mem_centralizer_singleton_iff.mpr hvx.symm) hxL hL.1.1 hR
  have hwZx := mem_zStar_kz_of_pumpUpLT hL hM hwL
    (⟨1, by simpa only [pow_one, hw2] using pow_orderOf_eq_one w⟩) hwCx
  have hwZv := zStar_le_zStar_kz_of_mem_rigidSet hL hwL
  apply not_exists_involution_mem_centralizer_pair_sections_of_rigid_actor
    hJ hxv hvx hvact hmax
  refine ⟨w, hw2, ?_, hwZx.2, hwZv.2⟩
  have hwCv := hL.1.1.2.2.1 hwL.1
  apply mem_centralizer_iff.mpr
  intro y hy
  rcases Set.mem_insert_iff.mp hy with rfl | hy
  · exact (mem_centralizer_singleton_iff.mp hwCx).symm
  · have hyv := Set.mem_singleton_iff.mp hy
    subst y
    exact (mem_centralizer_singleton_iff.mp hwCv).symm

theorem odd_card_cxK_inf_cxK_of_rigid_actor
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ CFSG.GH74.GLS.centralizerSection J (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (I : Subgroup G) (hI : I ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (L : Subgroup G) (hL : L ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ v) :
    Odd (Nat.card ↥(CFSG.GH74.GLS.CxK x I ⊓ CFSG.GH74.GLS.CxK v L)) := by
  classical
  by_contra hodd
  have heven : Even (Nat.card ↥(CxK x I ⊓ CxK v L)) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨u, hu2, huCx, huI, huCv, huL⟩ :=
    oddInter_original_intersection_involution heven
  by_cases hux : u = x
  · exact oddInter_false_of_original_x_mem_section hJ hL h16 hxv hvx hvact hmax
      (oddInter_immediate_x_section hL huL (Or.inl hux))
  by_cases huxv : u = x * v
  · exact oddInter_false_of_original_x_mem_section hJ hL h16 hxv hvx hvact hmax
      (oddInter_immediate_x_section hL huL (Or.inr huxv))
  have hux_comm : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp huCx
  have huv_comm : u * v = v * u := Subgroup.mem_centralizer_singleton_iff.mp huCv
  have hRu : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
    oddInter_rank_at_original_u hJ hL hvx hvact hu2 hux_comm huv_comm hux huxv
  have hxx : x * x = 1 := by simpa only [hx2, pow_two] using pow_orderOf_eq_one x
  have hvv : v * v = 1 := by simpa only [hv2, pow_two] using pow_orderOf_eq_one v
  have huu : u * u = 1 := by simpa only [hu2, pow_two] using pow_orderOf_eq_one u
  obtain ⟨S, hS, hxS, hvS, huS⟩ :=
    oddInter_sylow_contains_original_triple hxx hvv huu hvx.symm hux_comm.symm huv_comm.symm
  obtain ⟨hW, hxW⟩ := oddInter_original_W hS hxS hxP
  obtain ⟨a, ha2, haW, haCv, haCu, haZu⟩ :=
    oddInter_actual_orbit_fixed_a hI hS h16 hv2 hu2 hvS huS huv_comm.symm huI hRu
  have hxL := oddInter_transport_original_x hnonab hJ hL hS hxS hxP hvx hu2 huCv huL hRu
    ha2 haW haCv haCu haZu hmax
  exact oddInter_false_of_original_x_mem_section hJ hL h16 hxv hvx hvact hmax hxL

open CFSG.GH74.GLS.Stage1.Thm2.Recip

open CFSG.GH74.GLS.Stage1.Thm3.Sec4

open CFSG.GH74.GLS.TwoThin
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
open CFSG.GH74.GLS.Bg.Iii2.L41 CFSG.LocalAnalysis.ComponentInitial

end CFSG.GH74.GLS.NT44

end
