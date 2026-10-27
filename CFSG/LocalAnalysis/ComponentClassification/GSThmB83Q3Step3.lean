module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3JBar

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

theorem card_le_card_sylow {G : Type*} [Group G] [Finite G] {A : Subgroup G} (hA : IsPGroup 2 A)
    (P : Sylow 2 G) : Nat.card A ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := hA.exists_le_sylow
  rw [show Nat.card P = Nat.card P' by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]]
  exact card_le_of_le hP'

theorem card_le_of_sylow_subgroupOf {G : Type*} [Group G] [Finite G] {S Y A : Subgroup G}
    (hS : ∃ P : Sylow 2 ↥Y, (P : Subgroup Y) = S.subgroupOf Y) (hAY : A ≤ Y)
    (hA : IsPGroup 2 A) : Nat.card A ≤ Nat.card S := by
  obtain ⟨c, -, hc⟩ := exists_conjugate_le_of_sylow hS hAY hA
  rw [← Eight.card_conjugate_eq A c]
  exact card_le_of_le hc

theorem sylow_of_card_ge {G : Type*} [Group G] [Finite G] {Y P : Subgroup G} (hPY : P ≤ Y)
    (hP : IsPGroup 2 P) (hmax : ∀ A : Subgroup G, A ≤ Y → IsPGroup 2 A → Nat.card A ≤ Nat.card P) :
    ∃ T : Sylow 2 ↥Y, (T : Subgroup Y) = P.subgroupOf Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (hP.comap_subtype (K := Y)).exists_le_sylow
  refine ⟨T, (eq_of_le_of_card_ge hT ?_).symm⟩
  have h1 := hmax ((T : Subgroup Y).map Y.subtype) (map_subtype_le _) (T.isPGroup'.map Y.subtype)
  rw [card_map_of_injective Y.subtype_injective] at h1
  have hc : Nat.card (P.subgroupOf Y) = Nat.card P := by
    rw [← card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr hPY]
  exact h1.trans (le_of_eq hc.symm)

theorem exists_isPGroup_le_centralizer {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁]
    [Finite G₂] {φ : G₁ →* G₂} (hφ : ¬ 2 ∣ Nat.card φ.ker) {u : G₁} (hu : u * u = 1)
    {T : Subgroup G₂} (hT : IsPGroup 2 T)
    (hTle : T ≤ φ.range ⊓ centralizer ({φ u} : Set G₂)) :
    ∃ A : Subgroup G₁, A ≤ centralizer ({u} : Set G₁) ∧ IsPGroup 2 A ∧ A.map φ = T := by
  set L : Subgroup G₁ := centralizer ({u} : Set G₁)
  have hLmap : L.map φ = φ.range ⊓ centralizer ({φ u} : Set G₂) := by
    have := Eight.map_centralizer_eq hφ (isPGroup_zpowers_of_mul_self hu)
    rwa [centralizer_zpowers_eq, MonoidHom.map_zpowers, centralizer_zpowers_eq] at this
  let φ' : L →* G₂ := φ.domRestrict L
  have hφ' : ¬ 2 ∣ Nat.card φ'.ker := OddQuot.not_two_dvd_card_ker_domRestrict φ hφ L
  have hrange : φ'.range = L.map φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨A', hA'2, hA'⟩ := Eight.exists_isPGroup_map_eq (φ := φ') hT
    (by rw [hrange, hLmap]; exact hTle)
  refine ⟨A'.map L.subtype, map_subtype_le _, hA'2.map _, ?_⟩
  rw [map_map]
  exact hA'

theorem commutator_sup_zpowers_le {G : Type*} [Group G] {R : Subgroup G} {b : G}
    (hb : b ∈ centralizer (R : Set G)) (hbb : b * b = 1) :
    ⁅R ⊔ zpowers b, R ⊔ zpowers b⁆ ≤ R := by
  have hbN : b ∈ normalizer (R : Set G) := centralizer_le_normalizer _ hb
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨r, hr, hxr⟩ := Eight.mem_sup_zpowers_cases hbN hbb hx
  obtain ⟨s, hs, hys⟩ := Eight.mem_sup_zpowers_cases hbN hbb hy
  have hbr : r * b = b * r := (mem_centralizer_iff.mp hb r hr)
  have hbs : s * b = b * s := (mem_centralizer_iff.mp hb s hs)
  have i1 : b * s * b⁻¹ = s := by rw [← hbs, mul_inv_cancel_right]
  have hbr' : b * r⁻¹ = r⁻¹ * b := by
    calc b * r⁻¹ = r⁻¹ * (r * b) * r⁻¹ := by group
      _ = r⁻¹ * (b * r) * r⁻¹ := by rw [hbr]
      _ = r⁻¹ * b := by group
  have i2 : b * r⁻¹ * b⁻¹ = r⁻¹ := by rw [hbr', mul_inv_cancel_right]
  have key : ⁅x, y⁆ = ⁅r, s⁆ := by
    rcases hxr with hxr | hxr <;> rcases hys with hys | hys <;> rw [hxr, hys] <;>
      simp only [commutatorElement_def, mul_inv_rev]
    · rw [show r * (s * b) * r⁻¹ * (b⁻¹ * s⁻¹) = r * s * (b * r⁻¹ * b⁻¹) * s⁻¹ by group, i2]
    · rw [show r * b * s * (b⁻¹ * r⁻¹) * s⁻¹ = r * (b * s * b⁻¹) * r⁻¹ * s⁻¹ by group, i1]
    · rw [show r * b * (s * b) * (b⁻¹ * r⁻¹) * (b⁻¹ * s⁻¹) =
          r * (b * s * b⁻¹) * (b * r⁻¹ * b⁻¹) * s⁻¹ by group, i1, i2]
  rw [key]
  exact commutator_le_self R (commutator_mem_commutator hr hs)

theorem conjugate_le_centralizer {G : Type*} [Group G] {A : Subgroup G} {u w : G}
    (hA : A ≤ centralizer ({w⁻¹ * u * w} : Set G)) :
    conjugate A w⁻¹ ≤ centralizer ({u} : Set G) := by
  intro y hy
  rw [mem_conjugate_iff, inv_inv] at hy
  have hc := mem_centralizer_singleton_iff.mp (hA hy)
  rw [mem_centralizer_singleton_iff]
  calc y * u = w * ((w⁻¹ * y * w) * (w⁻¹ * u * w)) * w⁻¹ := by group
    _ = w * ((w⁻¹ * u * w) * (w⁻¹ * y * w)) * w⁻¹ := by rw [hc]
    _ = u * y := by group

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

theorem a_x (H : L83Hyp h) : h.x⁻¹ * h.a * h.x = h.a := by
  have hc := Six.comm_a H.C_eq h.x_mem
  calc h.x⁻¹ * h.a * h.x = h.x⁻¹ * (h.a * h.x) := by group
    _ = h.x⁻¹ * (h.x * h.a) := by rw [hc]
    _ = h.a := by group

theorem x_inv (H : L83Hyp h) : h.x⁻¹ = h.x := inv_eq_of_mul_eq_one_right H.x_mul_x

namespace Q3Data

variable (d : Q3Data H)
include d

theorem card_RM (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : Nat.card d.RM = 128 := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have h1 := d.c_props.card_D.2.2
  have h2 : IsPGroup 2 (d.RM.subgroupOf h.M3) := d.isPGroup_RM.comap_subtype
  rw [d.c_R, Eight.card_map_of_isPGroup hker h2,
    ← card_map_of_injective h.M3.subtype_injective, map_subgroupOf_eq_of_le d.RM_le] at h1
  exact h1

theorem centralizer_b_le : centralizer ({d.b} : Set X) ≤ normalizer (h.K : Set X) :=
  d.normalizer_B ▸ H.normalizer_le_normalizer_K

theorem card_le_of_le_centralizer_b {A : Subgroup X} (hA : IsPGroup 2 A)
    (hAC : A ≤ centralizer ({d.b} : Set X)) : Nat.card A ≤ 256 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : A ≤ normalizer (h.K : Set X) := hAC.trans d.centralizer_b_le
  let φ : A →* MulAut (h.K ⧸ pPrimeCore 2 h.K) := (Eight.oddBarAction h.K).comp (inclusion hAN)
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ 128 := by
    obtain ⟨T, hT⟩ := d.c.R_sylow
    have hT' : Nat.card T = 128 := by
      rw [show Nat.card T = Nat.card (T : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))) from rfl,
        hT]
      exact d.c_props.card_D.2.2
    rw [← hT']
    have h2 : IsPGroup 2 φ.range := by
      rw [MonoidHom.range_eq_map]
      exact (hA.to_subgroup ⊤).map φ
    exact card_le_card_sylow h2 T
  have hker : Nat.card φ.ker ≤ 2 := by
    have hk : φ.ker.map A.subtype ≤ coreActionKernel h.V := by
      rintro _ ⟨y, hy, rfl⟩
      rw [H.V_eq_K]
      exact Eight.mem_ker_oddBarAction.mp hy
    have h2 := card_le_of_sylow_subgroupOf H.B_sylow_kernel.2 hk
      ((hA.to_subgroup φ.ker).map A.subtype)
    rw [card_map_of_injective A.subtype_injective, d.card_B] at h2
    exact h2
  have h3 : Nat.card A ≤ 2 * 128 := by
    rw [← h1]
    exact Nat.mul_le_mul hker hrange
  omega

theorem B_le_centralizer_b : h.B ≤ centralizer ({d.b} : Set X) := by
  rw [d.B_eq, zpowers_le, mem_centralizer_singleton_iff]

theorem M3_le_centralizer_b : h.M3 ≤ centralizer ({d.b} : Set X) :=
  d.normalizer_B ▸ h.M3_le_normalizer

theorem b_mem_centralizer_M3 : d.b ∈ centralizer (h.M3 : Set X) := by
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_singleton_iff.mp (d.M3_le_centralizer_b hy))

theorem b_mul_self : d.b * d.b = 1 := by
  rw [← pow_two, ← d.b_ord, pow_orderOf_eq_one]

theorem card_sup_B (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {A : Subgroup X}
    (hAM : A ≤ h.M3) : Nat.card ↥(A ⊔ h.B) = Nat.card A * 2 := by
  have hBN : h.B ≤ normalizer (A : Set X) := by
    rw [d.B_eq, zpowers_le]
    exact centralizer_le_normalizer _ (fun y hy => (mem_centralizer_iff.mp
      d.b_mem_centralizer_M3 y (hAM hy)))
  have hdisj : Disjoint A h.B := by
    rw [disjoint_iff]
    refine eq_bot_iff.mpr fun y hy => ?_
    rcases mem_zpowers_two d.b_ord (d.B_eq ▸ hy.2) with h1 | h1
    · rw [h1]
      exact one_mem _
    · exact absurd (h1 ▸ hAM hy.1) (d.b_not_mem_M3 hCF1 hCF2)
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hBN hdisj, d.card_B]

abbrev R : Subgroup X := d.RM ⊔ h.B

theorem R_le_centralizer_b : d.R ≤ centralizer ({d.b} : Set X) :=
  sup_le (d.RM_le.trans d.M3_le_centralizer_b) d.B_le_centralizer_b

theorem card_R (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : Nat.card d.R = 256 := by
  rw [d.card_sup_B hCF1 hCF2 d.RM_le, d.card_RM hCF1 hCF2]

theorem isPGroup_R (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : IsPGroup 2 d.R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 8) (by rw [d.card_R hCF1 hCF2]; norm_num)

theorem eq_z_of_central (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) (hSC : CFA6SylowCent) {w : X} (hw : w ∈ h.D) (hw1 : w ≠ 1)
    (hwc : ∀ e ∈ h.D, w * e = e * w) : w = d.z := by
  have hC2 := (hSC _ hq.2 h.Dbar (d.card_Dbar hq hCF1 hCF2 hL0)).2
  have hD2 : IsPGroup 2 (h.D.subgroupOf h.J) :=
    ((Six.isPGroup_S h).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype
  set wbar : h.J ⧸ pPrimeCore 2 h.J := ((⟨w, h.sec8_D_le_J hw⟩ : h.J) : h.J ⧸ pPrimeCore 2 h.J)
  have hwC : wbar ∈ centralizer (h.Dbar : Set (h.J ⧸ pPrimeCore 2 h.J)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    simp only [QuotientGroup.coe_mk']
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hwc (e : X) he).symm
  have hw1' : wbar ≠ 1 := by
    intro h1
    have := OddQuot.injOn_of_isPGroup hD2 (show (⟨w, h.sec8_D_le_J hw⟩ : h.J) ∈ h.D.subgroupOf h.J
      from hw) (one_mem _) (h1.trans (QuotientGroup.mk_one _).symm)
    exact hw1 (congrArg Subtype.val this)
  have h1 := eq_of_card_eq_two hC2 hwC d.zbar_mem_centralizer hw1' d.zbar_ne_one
  have := OddQuot.injOn_of_isPGroup hD2 (show (⟨w, h.sec8_D_le_J hw⟩ : h.J) ∈ h.D.subgroupOf h.J
    from hw) (show (⟨d.z, h.sec8_D_le_J d.z_D⟩ : h.J) ∈ h.D.subgroupOf h.J from d.z_D) h1
  exact congrArg Subtype.val this

theorem z_x (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) (hSC : CFA6SylowCent) : h.x⁻¹ * d.z * h.x = d.z := by
  refine d.eq_z_of_central hq hCF1 hCF2 hL0 hSC (x_conj_mem_D d.z_D) ?_ ?_
  · intro h1
    apply d.z_ne
    have := congrArg (fun t => h.x * t * h.x⁻¹) h1
    simpa [mul_assoc] using this
  · intro e he
    have he' : h.x * e * h.x⁻¹ ∈ h.D := by
      have := x_conj_mem_D (h := h) (e := h.x * e * h.x⁻¹)
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem h.x_mem he.1) (inv_mem h.x_mem), ?_⟩
      exact (mem_normalizer_iff.mp h.sec8_x_mem_normalizer_J e).mp he.2
    have hc := d.z_comm _ he'
    calc h.x⁻¹ * d.z * h.x * e = h.x⁻¹ * (d.z * (h.x * e * h.x⁻¹)) * h.x := by group
      _ = h.x⁻¹ * ((h.x * e * h.x⁻¹) * d.z) * h.x := by rw [hc]
      _ = e * (h.x⁻¹ * d.z * h.x) := by group

theorem P_mul_self {p : X} (hp : p ∈ h.P) : p * p = 1 := by
  have haa := Six.a_mul_a_self h
  rcases d.P_mem p hp with rfl | rfl | rfl | rfl
  · rw [one_mul]
  · exact haa
  · exact d.b_mul_self
  · rw [show h.a * d.b * (h.a * d.b) = h.a * (d.b * h.a) * d.b by group, d.ba,
      show h.a * (h.a * d.b) * d.b = (h.a * h.a) * (d.b * d.b) by group, haa, d.b_mul_self,
      one_mul]

theorem tau_x_cases (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) (hDiag : CFA6Diag) (hSC : CFA6SylowCent) (hNC : CFA6NoComm)
    (hII : CFA6InnerInv) :
    h.x⁻¹ * d.tau * h.x = d.tau * d.z ∨ h.x⁻¹ * d.tau * h.x = d.tau * d.z * h.a := by
  obtain ⟨p, hp, hτx⟩ := d.tau_x hq hCF1 hCF2 hL0 hDiag hSC hNC hII
  have hzx := d.z_x hq hCF1 hCF2 hL0 hSC
  have hxi := H.x_inv
  have hp' : h.x⁻¹ * p * h.x ∈ h.P := by
    have := Six.conj_mem_P h (inv_mem h.x_mem) hp
    rwa [inv_inv] at this
  have hzQ : d.z ∈ h.Q := h.sec8_D_le_Q d.z_D
  have key1 : ∀ t : X, h.x⁻¹ * (h.x⁻¹ * t * h.x) * h.x = t := by
    intro t
    rw [show h.x⁻¹ * (h.x⁻¹ * t * h.x) * h.x = (h.x * h.x)⁻¹ * t * (h.x * h.x) by group,
      H.x_mul_x]
    group
  have key2 : ∀ t u v : X, h.x⁻¹ * (t * u * v) * h.x =
      (h.x⁻¹ * t * h.x) * (h.x⁻¹ * u * h.x) * (h.x⁻¹ * v * h.x) := fun t u v => by group
  have h1 : d.tau = d.tau * d.z * p * d.z * (h.x⁻¹ * p * h.x) := by
    calc d.tau = h.x⁻¹ * (h.x⁻¹ * d.tau * h.x) * h.x := (key1 d.tau).symm
      _ = h.x⁻¹ * (d.tau * d.z * p) * h.x := by rw [hτx]
      _ = (h.x⁻¹ * d.tau * h.x) * (h.x⁻¹ * d.z * h.x) * (h.x⁻¹ * p * h.x) := key2 _ _ _
      _ = d.tau * d.z * p * d.z * (h.x⁻¹ * p * h.x) := by rw [hτx, hzx]
  have hpz : p * d.z = d.z * p := d.P_comm_Q hp hzQ
  have h2 : p * (h.x⁻¹ * p * h.x) = 1 := by
    have h3 : d.tau * d.z * p * d.z * (h.x⁻¹ * p * h.x) =
        d.tau * (d.z * d.z) * (p * (h.x⁻¹ * p * h.x)) := by
      rw [show d.tau * d.z * p * d.z * (h.x⁻¹ * p * h.x) =
        d.tau * d.z * (p * d.z) * (h.x⁻¹ * p * h.x) by group, hpz]
      group
    rw [h3, d.z_sq, mul_one] at h1
    have := congrArg (fun t => d.tau⁻¹ * t) h1
    simp only [inv_mul_cancel, inv_mul_cancel_left] at this
    exact this.symm
  have hpx : h.x⁻¹ * p * h.x = p := by
    have := d.P_mul_self hp
    rw [← mul_left_cancel_iff (a := p), h2, this]
  have ha1 : h.a ≠ 1 := by
    intro h1'
    have := h.orderOf_a
    rw [h1', orderOf_one] at this
    norm_num at this
  rcases d.P_mem p hp with rfl | rfl | rfl | rfl
  · left
    rw [hτx, mul_one]
  · right
    exact hτx
  · exfalso
    rw [d.xbx] at hpx
    apply ha1
    have := congrArg (fun t => t * d.b⁻¹) hpx
    simpa using this
  · exfalso
    rw [show h.x⁻¹ * (h.a * d.b) * h.x = (h.x⁻¹ * h.a * h.x) * (h.x⁻¹ * d.b * h.x) by group,
      H.a_x, d.xbx, ← mul_assoc, Six.a_mul_a_self h, one_mul] at hpx
    apply ha1
    have := congrArg (fun t => t * d.b⁻¹) hpx
    simp only [mul_inv_cancel] at this
    exact (mul_inv_cancel_right h.a d.b ▸ this).symm

theorem tz_mem_M3 : d.tau * d.z ∈ h.M3 := mul_mem d.tau_mem.2 (H.D_le_M3 d.z_D)

theorem tau_comm_z (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    d.tau * d.z = d.z * d.tau :=
  d.tau_comm_Q1 hCF1 hCF2 ⟨h.sec8_D_le_Q d.z_D, H.D_le_M3 d.z_D⟩

theorem tz_mul_self (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    d.tau * d.z * (d.tau * d.z) = 1 := by
  rw [show d.tau * d.z * (d.tau * d.z) = d.tau * (d.z * d.tau) * d.z by group,
    ← d.tau_comm_z hCF1 hCF2, show d.tau * (d.tau * d.z) * d.z = (d.tau * d.tau) * (d.z * d.z) by
      group, d.tau_sq, d.z_sq, one_mul]

theorem exists_A_tz (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) :
    ∃ A : Subgroup X, A ≤ h.M3 ∧ A ≤ centralizer ({d.tau * d.z} : Set X) ∧ IsPGroup 2 A ∧
      Nat.card A = 128 ∧ d.tau * d.z ∈ ⁅A, A⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  set u : ↥h.M3 := ⟨d.tau * d.z, d.tz_mem_M3⟩ with hu
  have huu : u * u = 1 := Subtype.ext (d.tz_mul_self hCF1 hCF2)
  have hρu : H.rho u = d.c.tau * d.c.z := by
    rw [← d.rho_tau, d.c_z, ← map_mul]
    rfl
  obtain ⟨T, hT⟩ := d.c_props.tz_central
  have hTle : (T : Subgroup _) ≤ H.rho.range ⊓ centralizer ({H.rho u} : Set _) := by
    rw [H.rho_range hq hCF1 hCF2 hOut, top_inf_eq, hρu]
    exact hT
  obtain ⟨A', hA'C, hA'2, hA'⟩ := exists_isPGroup_le_centralizer hker huu T.isPGroup' hTle
  refine ⟨A'.map h.M3.subtype, map_subtype_le _, ?_, hA'2.map _, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hA'C hy))
  · rw [card_map_of_injective h.M3.subtype_injective, ← Eight.card_map_of_isPGroup hker hA'2, hA']
    obtain ⟨T', hT'⟩ := d.c.R_sylow
    rw [show Nat.card (T : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))) = Nat.card T' by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]]
    rw [show Nat.card T' = Nat.card (T' : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))) from rfl,
      hT']
    exact d.c_props.card_D.2.2
  ·
    have h1 := d.c_props.tz_comm T hT
    rw [← hA', ← map_commutator, ← hρu] at h1
    obtain ⟨w, hw, hwu⟩ := mem_map.mp h1
    have hu2 : IsPGroup 2 ↥(A' ⊔ zpowers u) := isPGroup_sup_zpowers hA'2
      (centralizer_le_normalizer _ (by
        rw [mem_centralizer_iff]
        intro y hy
        exact (mem_centralizer_singleton_iff.mp (hA'C hy)))) (by rw [huu]; exact one_mem _)
    have hwu' : w = u := Eight.injOn_of_isPGroup hker hu2
      ((le_sup_left : A' ≤ A' ⊔ zpowers u) (commutator_le_self A' hw))
      (mem_sup_right (mem_zpowers u)) hwu
    rw [← map_commutator]
    exact ⟨w, hw, by rw [hwu']; rfl⟩

theorem card_le_of_le_centralizer_a (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    {A : Subgroup X} (hA : IsPGroup 2 A) (hAC : A ≤ centralizer ({h.a} : Set X)) :
    Nat.card A ≤ 128 := by
  rw [← d.card_S hCF1 hCF2]
  exact card_le_of_sylow_subgroupOf H.S_sylow_C hAC hA

theorem a_not_conj_tz (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) (w : X) : w⁻¹ * h.a * w ≠ d.tau * d.z := by
  intro hw
  obtain ⟨A, hAM, hAC, hA2, hcA, -⟩ := d.exists_A_tz hq hCF1 hCF2 hOut
  have hAB : A ⊔ h.B ≤ centralizer ({w⁻¹ * h.a * w} : Set X) := by
    rw [hw]
    refine sup_le hAC ?_
    rw [d.B_eq, zpowers_le, mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (d.M3_le_centralizer_b d.tz_mem_M3)).symm
  have hc := d.card_sup_B hCF1 hCF2 hAM
  rw [hcA] at hc
  have h2 : IsPGroup 2 ↥(A ⊔ h.B) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 8) (by rw [hc]; norm_num)
  have h4 : IsPGroup 2 ↥(conjugate (A ⊔ h.B) w⁻¹) := h2.map _
  have h3 := d.card_le_of_le_centralizer_a hCF1 hCF2 h4 (conjugate_le_centralizer hAB)
  rw [Eight.card_conjugate_eq, hc] at h3
  norm_num at h3

theorem a_not_conj_b (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (w : X) :
    w⁻¹ * h.a * w ≠ d.b := by
  intro hw
  have hR : d.R ≤ centralizer ({w⁻¹ * h.a * w} : Set X) := hw ▸ d.R_le_centralizer_b
  have h4 : IsPGroup 2 ↥(conjugate d.R w⁻¹) := (d.isPGroup_R hCF1 hCF2).map _
  have h3 := d.card_le_of_le_centralizer_a hCF1 hCF2 h4 (conjugate_le_centralizer hR)
  rw [Eight.card_conjugate_eq, d.card_R hCF1 hCF2] at h3
  norm_num at h3

theorem conjugate_R_le (w : X) :
    conjugate d.R w ≤ centralizer ({w⁻¹ * d.b * w} : Set X) := by
  intro y hy
  rw [mem_conjugate_iff] at hy
  have hc := mem_centralizer_singleton_iff.mp (d.R_le_centralizer_b hy)
  rw [mem_centralizer_singleton_iff]
  calc y * (w⁻¹ * d.b * w) = w⁻¹ * ((w * y * w⁻¹) * d.b) * w := by group
    _ = w⁻¹ * (d.b * (w * y * w⁻¹)) * w := by rw [hc]
    _ = w⁻¹ * d.b * w * y := by group

theorem b_not_conj_tz (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) (w : X) : w⁻¹ * d.b * w ≠ d.tau * d.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hw
  obtain ⟨A, hAM, hAC, hA2, hcA, hτA⟩ := d.exists_A_tz hq hCF1 hCF2 hOut
  set E' := A ⊔ h.B with hE'
  have hE'C : E' ≤ centralizer ({d.tau * d.z} : Set X) := by
    refine sup_le hAC ?_
    rw [d.B_eq, zpowers_le, mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (d.M3_le_centralizer_b d.tz_mem_M3)).symm
  have hcE : Nat.card E' = 256 := by rw [d.card_sup_B hCF1 hCF2 hAM, hcA]
  have hE'2 : IsPGroup 2 E' := IsPGroup.of_card (n := 8) (by rw [hcE]; norm_num)
  have hbound : ∀ P' : Subgroup X, P' ≤ centralizer ({d.tau * d.z} : Set X) →
      IsPGroup 2 P' → Nat.card P' ≤ Nat.card E' := by
    intro P' hP' hP'2
    rw [hcE, ← Eight.card_conjugate_eq P' w⁻¹]
    rw [← hw] at hP'
    exact d.card_le_of_le_centralizer_b (hP'2.map _) (conjugate_le_centralizer hP')
  obtain ⟨T, hT⟩ := sylow_of_card_ge hE'C hE'2 hbound
  have hRw : conjugate d.R w ≤ centralizer ({d.tau * d.z} : Set X) :=
    hw ▸ d.conjugate_R_le w
  obtain ⟨c, hc, hcle⟩ := exists_conjugate_le_of_sylow ⟨T, hT⟩ hRw
    ((d.isPGroup_R hCF1 hCF2).map _)
  have hceq : conjugate (conjugate d.R w) c = E' := by
    refine eq_of_le_of_card_ge hcle ?_
    rw [hcE, Eight.card_conjugate_eq, Eight.card_conjugate_eq, d.card_R hCF1 hCF2]
  have h1 : d.tau * d.z ∈ ⁅E', E'⁆ := commutator_mono le_sup_left le_sup_left hτA
  rw [← hceq, conjugate_conjugate] at h1
  have h2 : d.tau * d.z ∈ conjugate ⁅d.R, d.R⁆ (w * c) := by
    unfold conjugate at h1 ⊢
    rwa [map_commutator]
  rw [mem_conjugate_iff] at h2
  have hcz : c * (d.tau * d.z) * c⁻¹ = d.tau * d.z := by
    rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have h3 : w * c * (d.tau * d.z) * (w * c)⁻¹ = d.b := by
    rw [show w * c * (d.tau * d.z) * (w * c)⁻¹ = w * (c * (d.tau * d.z) * c⁻¹) * w⁻¹ by group,
      hcz, ← hw]
    group
  rw [h3] at h2
  have h4 : ⁅d.R, d.R⁆ ≤ d.RM := by
    rw [R, d.B_eq]
    exact commutator_sup_zpowers_le (by
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_iff.mp d.b_mem_centralizer_M3 y (d.RM_le hy))) d.b_mul_self
  exact d.b_not_mem_M3 hCF1 hCF2 (d.RM_le (h4 h2))

theorem tau_x_eq (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) (hL0 : CFQ3L0) (hDiag : CFA6Diag) (hSC : CFA6SylowCent)
    (hNC : CFA6NoComm) (hII : CFA6InnerInv) : h.x⁻¹ * d.tau * h.x = d.tau * d.z := by
  rcases d.tau_x_cases hq hCF1 hCF2 hL0 hDiag hSC hNC hII with h1 | h1
  · exact h1
  · exfalso
    have hzx := d.z_x hq hCF1 hCF2 hL0 hSC
    have hza : d.z * h.a = h.a * d.z := H.comm_a_of_mem_Q (h.sec8_D_le_Q d.z_D)
    have h2 : h.x⁻¹ * (d.tau * d.z) * h.x = d.tau * h.a := by
      rw [show h.x⁻¹ * (d.tau * d.z) * h.x = (h.x⁻¹ * d.tau * h.x) * (h.x⁻¹ * d.z * h.x) by
        group, h1, hzx, show d.tau * d.z * h.a * d.z = d.tau * (d.z * h.a) * d.z by group, hza,
        show d.tau * (h.a * d.z) * d.z = d.tau * h.a * (d.z * d.z) by group, d.z_sq, mul_one]
    have h3 : d.g⁻¹ * (d.tau * h.a) * d.g = h.a := by
      rw [show d.g⁻¹ * (d.tau * h.a) * d.g = (d.g⁻¹ * d.tau * d.g) * (d.g⁻¹ * h.a * d.g) by
        group, d.tau_g, d.a_g, ← mul_assoc, d.tau_comm_a, mul_assoc, d.tau_sq, mul_one]
    apply d.a_not_conj_tz hq hCF1 hCF2 hOut (h.x * d.g)⁻¹
    rw [inv_inv, ← h3, ← h2]
    group

theorem z_conj_tau (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) : ∃ k ∈ h.K, k⁻¹ * d.z * k = d.tau := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  obtain ⟨kh, hkInn, hkz⟩ := d.c_props.z_tau
  obtain ⟨k₁, rfl⟩ := H.rho_surjective hq hCF1 hCF2 hOut kh
  have hzM : d.z ∈ h.M3 := H.D_le_M3 d.z_D
  set z' : ↥h.M3 := ⟨d.z, hzM⟩
  set t' : ↥h.M3 := ⟨d.tau, d.tau_mem.2⟩
  have hz2 : z' * z' = 1 := Subtype.ext d.z_sq
  have ht2 : t' * t' = 1 := Subtype.ext d.tau_sq
  have hrel : H.rho t' = (H.rho k₁)⁻¹ * H.rho z' * H.rho k₁ := by
    rw [d.rho_tau, ← hkz, d.c_z]
  obtain ⟨c, hc, hct⟩ := Eight.exists_conj_eq_of_map hker (isPGroup_zpowers_of_mul_self hz2)
    (isPGroup_zpowers_of_mul_self ht2) k₁ hrel
  refine ⟨c, (H.mem_K_iff hCF1 hCF2 c).mpr (hc ▸ hkInn), ?_⟩
  exact (congrArg Subtype.val hct).symm

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
