module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

structure M10Config {K : Type*} [Group K] (z : K) (D : Subgroup K) : Prop where
  z_order : orderOf z = 2
  disjoint : Disjoint (zpowers z) D
  z_comm : ∀ d ∈ D, d * z = z * d
  odd_central : fusionOddCoreOf D ≤ center K
  quot : Nonempty (↥D ⧸ fusionOddCore ↥D ≃* alternatingGroup (Fin 6))
  index_two : ((zpowers z ⊔ D).subgroupOf (centralizer ({z} : Set K))).index = 2
  no_outer : ∀ c ∈ centralizer ({z} : Set K), c * c ∈ zpowers z ⊔ fusionOddCoreOf D →
    c ∈ zpowers z ⊔ D
  noncentral : ∃ s : K, z * s * z⁻¹ * s⁻¹ ≠ 1 ∧ ∃ n : ℕ, (z * s * z⁻¹ * s⁻¹) ^ (2 ^ n) = 1

theorem mem_of_odd_orderOf_of_index_two {X : Type*} [Group X] {H : Subgroup X}
    (hH : H.index = 2) {x : X} (hx : Odd (orderOf x)) : x ∈ H := by
  obtain ⟨k, hk⟩ := hx
  have hxk : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hx2 : x * x ∈ H := by rw [Subgroup.mul_mem_iff_of_index_two hH]
  have : x = (x * x) ^ (k + 1) := by
    calc x = x ^ (2 * k + 1) * x := by rw [hxk, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
      _ = (x * x) ^ (k + 1) := by rw [pow_mul, sq]
  rw [this]
  exact pow_mem hx2 _

theorem fusionOddCoreOf_le {K : Type*} [Group K] (D : Subgroup K) : fusionOddCoreOf D ≤ D := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem odd_card_fusionOddCoreOf {K : Type*} [Group K] [Finite K] (D : Subgroup K) :
    Odd (Nat.card (fusionOddCoreOf D)) := by
  rw [fusionOddCoreOf, Subgroup.card_map_of_injective D.subtype_injective]
  exact odd_natCard_fusionOddCore D

theorem mem_oddCore_of_mem_O {K : Type*} [Group K] [Finite K] (D : Subgroup K) {d : ↥D}
    (hd : (d : K) ∈ fusionOddCore K) : d ∈ fusionOddCore ↥D := by
  have : ((fusionOddCore K).comap D.subtype).Normal :=
    (inferInstance : (fusionOddCore K).Normal).comap _
  have hodd : Odd (Nat.card ((fusionOddCore K).comap D.subtype)) := by
    have hle : ((fusionOddCore K).comap D.subtype).map D.subtype ≤ fusionOddCore K := by
      rintro _ ⟨m, hm, rfl⟩
      exact hm
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective D.subtype_injective] at h1
    exact Odd.of_dvd_nat (odd_natCard_fusionOddCore K) h1
  exact le_fusionOddCore hodd hd

namespace M10Config

variable {K : Type*} [Group K] {z : K} {D : Subgroup K} (h : M10Config z D)

include h in
theorem z_sq : z * z = 1 := by
  rw [← sq]
  have := pow_orderOf_eq_one z
  rwa [h.z_order] at this

include h in
theorem z_ne_one : z ≠ 1 := fun h1 => by
  have := h.z_order
  rw [h1, orderOf_one] at this
  omega

include h in
theorem D_le_C : D ≤ centralizer ({z} : Set K) := fun d hd =>
  mem_centralizer_singleton_iff.2 (h.z_comm d hd)

include h in
theorem C₀_le_C : zpowers z ⊔ D ≤ centralizer ({z} : Set K) :=
  sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) h.D_le_C

include h in
theorem mem_C₀_of_odd {c : K} (hc : c ∈ centralizer ({z} : Set K)) (hodd : Odd (orderOf c)) :
    c ∈ zpowers z ⊔ D := by
  have h1 := mem_of_odd_orderOf_of_index_two h.index_two
    (x := (⟨c, hc⟩ : ↥(centralizer ({z} : Set K)))) (by rwa [← Subgroup.orderOf_coe])
  exact mem_subgroupOf.1 h1

include h in
theorem mem_D_of_odd {c : K} (hc : c ∈ zpowers z ⊔ D) (hodd : Odd (orderOf c)) : c ∈ D := by
  have hle : D ≤ centralizer (zpowers z : Set K) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (show Commute z d from (h.z_comm d hd).symm) k).eq
  obtain ⟨a, ha, b, hb, hcab⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hc
  obtain ⟨k, hk⟩ := hodd
  have hck : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
  have hab : a * b = b * a := mem_centralizer_iff.1 (hle hb) a ha
  have h1 : a ^ (2 * k + 1) * b ^ (2 * k + 1) = 1 := by
    rw [← Commute.mul_pow (show Commute a b from hab), ← hcab]
    exact hck
  have h2 : a ^ (2 * k + 1) ∈ D := by
    have : a ^ (2 * k + 1) = (b ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem (pow_mem hb _)
  have h3 : a ^ (2 * k + 1) = 1 := Subgroup.disjoint_def.1 h.disjoint (pow_mem ha _) h2
  rcases mem_zpowers_sq_eq_one h.z_sq ha with ha1 | ha1
  · rw [hcab, ha1, one_mul]
    exact hb
  · exfalso
    apply h.z_ne_one
    rw [ha1, pow_succ, pow_mul, sq, h.z_sq, one_pow, one_mul] at h3
    exact h3

include h in
theorem oddCoreOf_normal : (fusionOddCoreOf D).Normal :=
  ⟨fun n hn g => by
    rw [mem_center_iff.1 (h.odd_central hn) g, mul_inv_cancel_right]
    exact hn⟩

variable [Finite K]

include h in
theorem oddCoreOf_le_O : fusionOddCoreOf D ≤ fusionOddCore K := by
  have := h.oddCoreOf_normal
  exact le_fusionOddCore (odd_card_fusionOddCoreOf D)

include h in
theorem centralizer_inf_odd :
    centralizer ({z} : Set K) ⊓ fusionOddCore K = fusionOddCoreOf D := by
  apply le_antisymm
  · rintro x ⟨hxC, hxO⟩
    have hord : Odd (orderOf x) :=
      Odd.of_dvd_nat (odd_natCard_fusionOddCore K) (Subgroup.orderOf_dvd_natCard _ hxO)
    have hxD := h.mem_D_of_odd (h.mem_C₀_of_odd hxC hord) hord
    exact ⟨⟨x, hxD⟩, mem_oddCore_of_mem_O D (d := ⟨x, hxD⟩) hxO, rfl⟩
  · intro x hx
    exact ⟨h.D_le_C (fusionOddCoreOf_le D hx), h.oddCoreOf_le_O hx⟩

end M10Config

@[expose] noncomputable def cMap {K : Type*} [Group K] (z : K) :
    ↥(centralizer ({z} : Set K)) →*
      ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} : Set (K ⧸ fusionOddCore K))) :=
  ((QuotientGroup.mk' (fusionOddCore K)).comp (centralizer ({z} : Set K)).subtype).codRestrict _
    (fun c => by
      rw [mem_centralizer_singleton_iff]
      have h1 := mem_centralizer_singleton_iff.1 c.2
      show (QuotientGroup.mk (c : K) : K ⧸ fusionOddCore K) * QuotientGroup.mk z =
        QuotientGroup.mk z * QuotientGroup.mk (c : K)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1])

theorem cMap_val {K : Type*} [Group K] (z : K) (c : ↥(centralizer ({z} : Set K))) :
    ((cMap z c : ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K)))) : K ⧸ fusionOddCore K) = QuotientGroup.mk (c : K) := rfl

theorem cMap_surjective {K : Type*} [Group K] [Finite K] {z : K} (hz : orderOf z = 2) :
    Function.Surjective (cMap z) := by
  intro y
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz; omega
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  obtain ⟨x, hx, hxy⟩ := CFSG.GorensteinWalter.exists_centralizer_lift_of_odd_kernel
    (fusionOddCore K) (odd_natCard_fusionOddCore K) ⟨hz1, hz2⟩ y.1 y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

namespace M10Config

variable {K : Type*} [Group K] [Finite K] {z : K} {D : Subgroup K} (h : M10Config z D)

include h in
theorem ker_cMap :
    (cMap z).ker = (fusionOddCoreOf D).subgroupOf (centralizer ({z} : Set K)) := by
  ext c
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h1
    have h2 : (QuotientGroup.mk (c : K) : K ⧸ fusionOddCore K) = 1 := congrArg Subtype.val h1
    have hcO : (c : K) ∈ fusionOddCore K := (QuotientGroup.eq_one_iff _).1 h2
    rw [← h.centralizer_inf_odd]
    exact ⟨c.2, hcO⟩
  · intro h1
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).2 (h.oddCoreOf_le_O h1)

include h in
theorem fusionOddCore_C :
    fusionOddCore ↥(centralizer ({z} : Set K)) = (cMap z).ker := by
  rw [h.ker_cMap]
  apply le_antisymm
  · intro y hy
    have hyodd : Odd (orderOf (y : K)) := by
      rw [Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat (odd_natCard_fusionOddCore _) (Subgroup.orderOf_dvd_natCard _ hy)
    have hyD : (y : K) ∈ D :=
      h.mem_D_of_odd (h.mem_C₀_of_odd y.2 hyodd) hyodd
    let W : Subgroup ↥D := (fusionOddCore ↥(centralizer ({z} : Set K))).comap
      (Subgroup.inclusion h.D_le_C)
    have hWn : W.Normal :=
      (inferInstance : (fusionOddCore ↥(centralizer ({z} : Set K))).Normal).comap _
    have hWodd : Odd (Nat.card W) :=
      Odd.of_dvd_nat (odd_natCard_fusionOddCore _)
        (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective h.D_le_C))
    have hWle : W ≤ fusionOddCore ↥D := le_fusionOddCore hWodd
    have hmem : (⟨y, hyD⟩ : ↥D) ∈ fusionOddCore ↥D := hWle (by
      show Subgroup.inclusion h.D_le_C ⟨y, hyD⟩ ∈ fusionOddCore ↥(centralizer ({z} : Set K))
      exact hy)
    rw [mem_subgroupOf]
    exact ⟨⟨y, hyD⟩, hmem, rfl⟩
  · have hN := h.oddCoreOf_normal
    have hNn : ((fusionOddCoreOf D).subgroupOf (centralizer ({z} : Set K))).Normal := inferInstance
    have hodd : Odd (Nat.card ((fusionOddCoreOf D).subgroupOf (centralizer ({z} : Set K)))) := by
      have hle : fusionOddCoreOf D ≤ centralizer ({z} : Set K) :=
        (fusionOddCoreOf_le D).trans h.D_le_C
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact odd_card_fusionOddCoreOf D
    exact le_fusionOddCore hodd

include h in
theorem fusionOddCore_hat_eq_bot :
    fusionOddCore ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K))) = ⊥ := by
  have e : ↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K)) ≃*
      ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
        Set (K ⧸ fusionOddCore K))) :=
    (QuotientGroup.quotientMulEquivOfEq h.fusionOddCore_C).trans
      (QuotientGroup.quotientKerEquivOfSurjective (cMap z) (cMap_surjective h.z_order))
  exact fusionOddCore_eq_bot_of_mulEquiv e.symm (fusionOddCore_quotient_eq_bot _)

end M10Config

end CFSG.EvenSporadicStandard.Fin76b
