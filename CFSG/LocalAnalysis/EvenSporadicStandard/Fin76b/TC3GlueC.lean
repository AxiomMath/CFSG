module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3GlueB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3GlueA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Solomon

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

namespace M10Config

variable {K : Type} [Group K] {z : K} {D : Subgroup K}

@[expose] def zC (z : K) : ↥(centralizer ({z} : Set K)) :=
  ⟨z, mem_centralizer_singleton_iff.2 rfl⟩

@[expose] noncomputable def rho (z : K) : ↥(centralizer ({z} : Set K)) →*
    ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} : Set (K ⧸ fusionOddCore K))) ⧸
      fusionOddCore ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
        Set (K ⧸ fusionOddCore K))) :=
  (QuotientGroup.mk' _).comp (cMap z)

@[expose] def Dc (D : Subgroup K) (z : K) : Subgroup ↥(centralizer ({z} : Set K)) :=
  D.subgroupOf (centralizer ({z} : Set K))

@[expose] def Cc (D : Subgroup K) (z : K) : Subgroup ↥(centralizer ({z} : Set K)) :=
  (zpowers z ⊔ D).subgroupOf (centralizer ({z} : Set K))

@[expose] noncomputable def Abar (D : Subgroup K) (z : K) :
    Subgroup (↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K))) ⧸ fusionOddCore ↥(centralizer ({(QuotientGroup.mk z :
        K ⧸ fusionOddCore K)} : Set (K ⧸ fusionOddCore K)))) :=
  (Dc D z).map (rho z)

theorem Dc_le_Cc : Dc D z ≤ Cc D z := fun _ hx =>
  mem_subgroupOf.2 (mem_sup_right (mem_subgroupOf.1 hx))

variable (h : M10Config z D)

include h in
theorem Cc_eq : Cc D z = zpowers (zC z) ⊔ Dc D z := by
  have hz : zpowers z ≤ centralizer ({z} : Set K) :=
    zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
  rw [Cc, Dc, subgroupOf_sup hz h.D_le_C]
  congr 1
  ext c
  rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa [zC] using hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa [zC] using congrArg Subtype.val hk⟩

include h in
theorem map_Cc : (Cc D z).map (rho z) = Abar D z ⊔ zpowers (rho z (zC z)) := by
  rw [h.Cc_eq, Subgroup.map_sup, MonoidHom.map_zpowers, sup_comm]
  rfl

variable [Finite K]

include h in
theorem rho_surjective : Function.Surjective (rho z) :=
  (QuotientGroup.mk'_surjective _).comp (cMap_surjective h.z_order)

include h in
theorem ker_rho : (rho z).ker = (cMap z).ker := by
  ext c
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (QuotientGroup.mk' _ (cMap z c) = 1) ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, h.fusionOddCore_hat_eq_bot, mem_bot]

include h in
theorem ker_rho_le : (rho z).ker ≤ Dc D z := by
  rw [h.ker_rho, h.ker_cMap, Dc]
  intro c hc
  rw [mem_subgroupOf] at hc ⊢
  exact fusionOddCoreOf_le D hc

include h in
theorem rho_mem_iff (c : ↥(centralizer ({z} : Set K))) :
    rho z c ∈ Abar D z ⊔ zpowers (rho z (zC z)) ↔ c ∈ Cc D z := by
  rw [← h.map_Cc]
  constructor
  · rintro ⟨c', hc', hcc'⟩
    have hker : c'⁻¹ * c ∈ (rho z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcc', inv_mul_cancel]
    have hD : c'⁻¹ * c ∈ Cc D z := Dc_le_Cc (h.ker_rho_le hker)
    have : c = c' * (c'⁻¹ * c) := by group
    rw [this]
    exact mul_mem hc' hD
  · intro hc
    exact ⟨c, hc, rfl⟩

include h in
theorem Abar_iso : Nonempty (↥(Abar D z) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := h.quot
  let θ : ↥D →* _ := (rho z).comp (Subgroup.inclusion h.D_le_C)
  have hrange : θ.range = Abar D z := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨Subgroup.inclusion h.D_le_C d, mem_subgroupOf.2 d.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c.1, mem_subgroupOf.1 hc⟩, rfl⟩
  have hker : θ.ker = fusionOddCore ↥D := by
    ext d
    rw [MonoidHom.mem_ker]
    change rho z (Subgroup.inclusion h.D_le_C d) = 1 ↔ _
    rw [← MonoidHom.mem_ker, h.ker_rho, h.ker_cMap, mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyd⟩
      have : y = d := Subtype.ext hyd
      rwa [← this]
    · intro hd
      exact ⟨d, hd, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange θ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans e))⟩

include h in
theorem zbar_not_mem : rho z (zC z) ∉ Abar D z := by
  intro hmem
  obtain ⟨c, hc, hcz⟩ := hmem
  have hker : (zC z)⁻¹ * c ∈ (rho z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcz, inv_mul_cancel]
  have hD : (zC z)⁻¹ * c ∈ Dc D z := h.ker_rho_le hker
  have h1 : (zC z)⁻¹ ∈ Dc D z := by
    have := mul_mem hD (inv_mem hc)
    simpa using this
  have hzD : z ∈ D := by
    have := inv_mem h1
    simpa [Dc, mem_subgroupOf, zC] using this
  have hz : z ∈ zpowers z ⊓ D := ⟨mem_zpowers z, hzD⟩
  rw [h.disjoint.eq_bot, mem_bot] at hz
  exact h.z_ne_one hz

include h in
theorem index_Abar : (Abar D z ⊔ zpowers (rho z (zC z))).index = 2 := by
  rw [← h.map_Cc, Subgroup.index_map_eq (Cc D z) h.rho_surjective (h.ker_rho_le.trans Dc_le_Cc)]
  exact h.index_two

include h in
theorem no_outer_rho (y : ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K))) ⧸ fusionOddCore ↥(centralizer ({(QuotientGroup.mk z :
        K ⧸ fusionOddCore K)} : Set (K ⧸ fusionOddCore K))))
    (hy : y * y ∈ zpowers (rho z (zC z))) : y ∈ Abar D z ⊔ zpowers (rho z (zC z)) := by
  obtain ⟨c, rfl⟩ := h.rho_surjective y
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hy
  rw [h.rho_mem_iff]
  have h1 : rho z ((zC z) ^ j) = rho z (c * c) := by rw [map_zpow, hj, map_mul]
  have h2 : ((zC z) ^ j)⁻¹ * (c * c) ∈ (rho z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [h.ker_rho, h.ker_cMap, mem_subgroupOf] at h2
  have h3 : ((c : K) * c) ∈ zpowers z ⊔ fusionOddCoreOf D := by
    have h4 : (c : K) * c = z ^ j * (((zC z) ^ j)⁻¹ * (c * c) : ↥(centralizer ({z} : Set K))) := by
      simp [zC]
    rw [h4]
    exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers z) j)) (mem_sup_right h2)
  exact mem_subgroupOf.2 (h.no_outer (c : K) c.2 h3)

include h in
theorem a6Pair : A6Pair (Abar D z) (rho z (zC z)) where
  iso := h.Abar_iso
  central := fun y => by
    obtain ⟨c, rfl⟩ := h.rho_surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg (rho z) (Subtype.ext (mem_centralizer_singleton_iff.1 c.2))
  sq := by
    rw [← map_mul]
    have : zC z * zC z = 1 := Subtype.ext h.z_sq
    rw [this, map_one]
  not_mem := h.zbar_not_mem
  index_two := h.index_Abar
  no_outer := h.no_outer_rho

theorem eq_one_of_odd_of_pow_two {X : Type*} [Group X] {x : X} (hodd : Odd (orderOf x)) (n : ℕ)
    (hx : x ^ (2 ^ n) = 1) : x = 1 := by
  have hd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hm] at hodd
  have hm0 : m = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hm0, pow_zero] at hm
  exact orderOf_eq_one_iff.1 hm

include h in
theorem fusionZStar_eq_bot : fusionZStar (K ⧸ fusionOddCore K) = ⊥ := by
  have hbot : fusionOddCore (K ⧸ fusionOddCore K) = ⊥ := fusionOddCore_quotient_eq_bot K
  rw [eq_bot_iff]
  intro g hg
  have hg' : QuotientGroup.mk' (fusionOddCore (K ⧸ fusionOddCore K)) g ∈
      Subgroup.center ((K ⧸ fusionOddCore K) ⧸ fusionOddCore (K ⧸ fusionOddCore K)) := hg
  have hgc : ∀ y : K ⧸ fusionOddCore K, y * g = g * y := by
    intro y
    have h1 : (QuotientGroup.mk (y * g) :
        (K ⧸ fusionOddCore K) ⧸ fusionOddCore (K ⧸ fusionOddCore K)) =
        QuotientGroup.mk (g * y) := mem_center_iff.1 hg' (QuotientGroup.mk' _ y)
    have h2 : (y * g)⁻¹ * (g * y) ∈ fusionOddCore (K ⧸ fusionOddCore K) := QuotientGroup.eq.1 h1
    rw [hbot, mem_bot, inv_mul_eq_one] at h2
    exact h2
  set zb : K ⧸ fusionOddCore K := QuotientGroup.mk z with hzb
  have hgC : g ∈ centralizer ({zb} : Set (K ⧸ fusionOddCore K)) :=
    mem_centralizer_singleton_iff.2 (hgc zb).symm
  let ĝ : ↥(centralizer ({zb} : Set (K ⧸ fusionOddCore K))) := ⟨g, hgC⟩
  have hm : ∀ y : ↥(centralizer ({zb} : Set (K ⧸ fusionOddCore K))) ⧸
      fusionOddCore ↥(centralizer ({zb} : Set (K ⧸ fusionOddCore K))),
      y * QuotientGroup.mk ĝ = QuotientGroup.mk ĝ * y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | _ ŷ =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg QuotientGroup.mk (Subtype.ext (hgc ŷ.1))
  have hcen := h.a6Pair.center_le hm
  rcases mem_zpowers_sq_eq_one h.a6Pair.sq hcen with h1 | h1
  · have h2 : ĝ ∈ fusionOddCore ↥(centralizer ({zb} : Set (K ⧸ fusionOddCore K))) :=
      (QuotientGroup.eq_one_iff _).1 h1
    rw [h.fusionOddCore_hat_eq_bot, mem_bot] at h2
    exact mem_bot.2 (congrArg Subtype.val h2)
  · exfalso
    have h3 := QuotientGroup.eq.1 h1
    rw [h.fusionOddCore_hat_eq_bot, mem_bot, inv_mul_eq_one] at h3
    have hgz : g = zb := congrArg Subtype.val h3
    rw [hgz] at hgc
    obtain ⟨s, hs1, n, hsn⟩ := h.noncentral
    have h5 : (QuotientGroup.mk (z * s * z⁻¹ * s⁻¹) : K ⧸ fusionOddCore K) = 1 := by
      have h6 := hgc (QuotientGroup.mk s)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      calc (QuotientGroup.mk z : K ⧸ fusionOddCore K) * QuotientGroup.mk s *
            (QuotientGroup.mk z)⁻¹ * (QuotientGroup.mk s)⁻¹
          = (QuotientGroup.mk s * zb) * (QuotientGroup.mk z)⁻¹ * (QuotientGroup.mk s)⁻¹ := by
            rw [h6]
        _ = 1 := by rw [hzb]; group
    have h6 : z * s * z⁻¹ * s⁻¹ ∈ fusionOddCore K := (QuotientGroup.eq_one_iff _).1 h5
    have hodd : Odd (orderOf (z * s * z⁻¹ * s⁻¹)) :=
      Odd.of_dvd_nat (odd_natCard_fusionOddCore K) (Subgroup.orderOf_dvd_natCard _ h6)
    exact hs1 (eq_one_of_odd_of_pow_two hodd n hsn)

end M10Config

theorem lemma96_of_solomon {K : Type} [Group K] [Finite K] {z : K} {D : Subgroup K}
    (h : M10Config z D) (hSol : SolomonM10) (hKG : CFSG.SectionRank.IsKGroupCat K) :
    Lemma96Conclusion K (QuotientGroup.mk z) ∧
      ∃ c ∈ centralizer ({z} : Set K), c ∉ zpowers z ⊔ D ∧ c * c ∈ D := by
  have hOodd : Odd (Nat.card (fusionOddCore K)) := odd_natCard_fusionOddCore K
  have hz2 : z ^ 2 = 1 := by rw [← h.z_order]; exact pow_orderOf_eq_one z
  have hzO : z ∉ fusionOddCore K := by
    intro hz
    have h1 : orderOf z ∣ Nat.card (fusionOddCore K) := Subgroup.orderOf_dvd_natCard _ hz
    rw [h.z_order] at h1
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h1)
  have hzb1 : (QuotientGroup.mk z : K ⧸ fusionOddCore K) ≠ 1 := fun h1 =>
    hzO ((QuotientGroup.eq_one_iff z).1 h1)
  have hzb2 : orderOf (QuotientGroup.mk z : K ⧸ fusionOddCore K) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hz2, QuotientGroup.mk_one]) hzb1
  have hconc : SolomonM10Conclusion (K ⧸ fusionOddCore K) (QuotientGroup.mk z) :=
    hSol (K ⧸ fusionOddCore K) (hKG.quotient _) (QuotientGroup.mk z) hzb2 h.fusionZStar_eq_bot
      h.fusionOddCore_hat_eq_bot
      ⟨M10Config.Abar D z, h.Abar_iso, h.zbar_not_mem, h.index_Abar, fun y hy =>
        h.no_outer_rho y hy⟩
  refine ⟨hconc, ?_⟩
  obtain ⟨u, huM, huA⟩ := h.a6Pair.exists_outer_sq hconc.1
  obtain ⟨c, rfl⟩ := h.rho_surjective u
  refine ⟨(c : K), c.2, fun hc => huM ((h.rho_mem_iff c).2 (mem_subgroupOf.2 hc)), ?_⟩
  obtain ⟨d, hd, hdc⟩ := huA
  have h1 : d⁻¹ * (c * c) ∈ (M10Config.rho z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hdc, inv_mul_cancel]
  have h2 : d⁻¹ * (c * c) ∈ M10Config.Dc D z := h.ker_rho_le h1
  have h3 : c * c ∈ M10Config.Dc D z := by
    have := mul_mem hd h2
    simpa using this
  exact mem_subgroupOf.1 h3

end CFSG.EvenSporadicStandard.Fin76b
