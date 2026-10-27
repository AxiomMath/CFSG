module

import CFSG.LocalAnalysis.ZStar
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.StrongClosure
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

namespace CFSG.Goldschmidt

open CFSG.Open

theorem exists_two_pow_not_mem_sq_mem {G : Type*} [Group G] {C : Subgroup G} {a₀ : G}
    (ha₀ : a₀ ∉ C) (h2 : ∃ n : ℕ, a₀ ^ (2 ^ n) = 1) :
    ∃ j : ℕ, a₀ ^ (2 ^ j) ∉ C ∧ (a₀ ^ (2 ^ j)) ^ 2 ∈ C := by
  classical
  have hex : ∃ n : ℕ, a₀ ^ (2 ^ n) ∈ C := by
    obtain ⟨n, hn⟩ := h2
    exact ⟨n, hn ▸ C.one_mem⟩
  have hm : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at this
    exact ha₀ this
  refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
  exact Nat.find_spec hex

theorem conj_eq_of_commute_of_weakClosure {Q : Type*} [Group Q] [Finite Q] (T : Sylow 2 Q)
    {z : Q} (hz : z * z = 1)
    (hwc : ∀ q : Q, q⁻¹ * z * q ∈ (T : Subgroup Q) → q⁻¹ * z * q = z) (q : Q)
    (hcomm : (q * z * q⁻¹) * z = z * (q * z * q⁻¹)) : q * z * q⁻¹ = z := by
  set b := q * z * q⁻¹ with hb
  have hbb : b * b = 1 := by
    calc b * b = q * (z * z) * q⁻¹ := by rw [hb]; group
      _ = 1 := by rw [hz, mul_one, mul_inv_cancel]
  have hzp : ∀ w : Q, w * w = 1 → IsPGroup 2 (Subgroup.zpowers w) := by
    intro w hw
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hw) : orderOf w ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hbC : b ∈ Subgroup.centralizer (Subgroup.zpowers z : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨n, rfl⟩
    exact (Commute.zpow_left hcomm.symm n).eq
  have hP : IsPGroup 2 (Subgroup.zpowers z ⊔ Subgroup.zpowers b : Subgroup Q) :=
    IsPGroup.to_sup_of_normal_left' (hzp z hz) (hzp b hbb)
      ((Subgroup.zpowers_le.mpr hbC).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Q T R
  have hmem : ∀ x ∈ (R : Subgroup Q), c⁻¹ * x * c ∈ (T : Subgroup Q) := by
    intro x hx
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simpa [MulAut.smul_def, MulAut.conj_apply] using hx
  have h1 := hwc c (hmem z (hR (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))))
  have h2 := hwc (q⁻¹ * c) (by
    have := hmem b (hR (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))
    simpa [hb, mul_assoc] using this)
  calc q * z * q⁻¹ = c * ((q⁻¹ * c)⁻¹ * z * (q⁻¹ * c)) * c⁻¹ := by group
    _ = c * (c⁻¹ * z * c) * c⁻¹ := by rw [h2, h1]
    _ = z := by group

theorem conj_eq_of_mem_sup {G : Type*} [Group G] {A H : Subgroup G} (hAab : IsMulCommutative A)
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (hAH : A ⊓ H = ⊥) {a y : G} (ha : a ∈ A)
    (hy : y ∈ H ⊔ A) (hya : y⁻¹ * a * y ∈ A) : y⁻¹ * a * y = a := by
  open scoped Pointwise in
  have hy' : y ∈ ((H : Set G) * (A : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left H A hAN]
    exact hy
  obtain ⟨h, hh, b, hb, rfl⟩ := Set.mem_mul.mp hy'
  have hab : a * b = b * a := congrArg Subtype.val (hAab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h1 : a⁻¹ * h⁻¹ * a ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem ha)) h⁻¹).mp (H.inv_mem hh)
    rwa [inv_inv] at this
  have h2 : b⁻¹ * (a⁻¹ * h⁻¹ * a * h) * b ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem hb)) _).mp (H.mul_mem h1 hh)
    rwa [inv_inv] at this
  have hkey : a⁻¹ * ((h * b)⁻¹ * a * (h * b)) = b⁻¹ * (a⁻¹ * h⁻¹ * a * h) * b := by
    calc a⁻¹ * ((h * b)⁻¹ * a * (h * b)) = (b * a)⁻¹ * (h⁻¹ * a * h) * b := by group
      _ = (a * b)⁻¹ * (h⁻¹ * a * h) * b := by rw [hab]
      _ = b⁻¹ * (a⁻¹ * h⁻¹ * a * h) * b := by group
  have hmem : a⁻¹ * ((h * b)⁻¹ * a * (h * b)) ∈ A ⊓ H :=
    ⟨A.mul_mem (A.inv_mem ha) hya, hkey ▸ h2⟩
  rw [hAH, Subgroup.mem_bot] at hmem
  calc (h * b)⁻¹ * a * (h * b) = a * (a⁻¹ * ((h * b)⁻¹ * a * (h * b))) := by group
    _ = a := by rw [hmem, mul_one]

theorem N6 :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A H : Subgroup G), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
      A ≤ Subgroup.normalizer (H : Set G) → goldschmidtOddCore H = ⊥ → A ⊓ H = ⊥ → ⁅A, H⁆ = ⊥ := by
  intro G _ _ S A H hAS hAab hcl hAN hO hAH
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_contra hle
  have hex : ∃ a ∈ A, a ∉ Subgroup.centralizer (H : Set G) := by
    by_contra hn
    exact hle fun a ha => by
      by_contra ha'
      exact hn ⟨a, ha, ha'⟩
  obtain ⟨a₀, ha₀A, ha₀⟩ := hex
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hAS
  obtain ⟨n, hn⟩ := hA2 ⟨a₀, ha₀A⟩
  obtain ⟨j, hj, hj2⟩ := exists_two_pow_not_mem_sq_mem ha₀
    ⟨n, by simpa using congrArg Subtype.val hn⟩
  set a := a₀ ^ (2 ^ j) with ha_def
  have haA : a ∈ A := A.pow_mem ha₀A _
  set X : Subgroup G := H ⊔ A with hXdef
  have hXN : X ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer hAN
  set C : Subgroup G := A ⊓ Subgroup.centralizer (H : Set G) with hCdef
  set C' : Subgroup X := C.subgroupOf X with hC'def
  have hCX : ∀ c ∈ C, X ≤ Subgroup.centralizer ({c} : Set G) := by
    intro c hc
    refine sup_le (fun h hh => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hc.2 h hh
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hAab.is_comm.comm ⟨b, hb⟩ ⟨c, hc.1⟩)
  have hC'Z : C' ≤ Subgroup.center X := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hCX c (Subgroup.mem_subgroupOf.mp hc) y.2))
  have : C'.Normal := Subgroup.normal_of_le_center hC'Z
  set π := QuotientGroup.mk' C' with hπ
  set a' : X := ⟨a, Subgroup.mem_sup_right haA⟩ with ha'
  have hā1 : π a' ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, hC'def,
      Subgroup.mem_subgroupOf]
    exact fun h => hj h.2
  have hā2 : π a' * π a' = 1 := by
    rw [← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hC'def,
      Subgroup.mem_subgroupOf]
    refine ⟨A.mul_mem haA haA, ?_⟩
    change a * a ∈ Subgroup.centralizer (H : Set G)
    rw [← sq]
    exact hj2
  obtain ⟨T, hAT⟩ := (hA2.comap_subtype (K := X)).exists_le_sylow
  have hW := stronglyClosed_subgroupOf S hcl (le_sup_right : A ≤ X) T hAT
  have hC'T : C' ≤ (T : Subgroup X) := fun c hc =>
    hAT (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hc).1)
  set Tbar : Sylow 2 (X ⧸ C') := T.mapSurjective (QuotientGroup.mk'_surjective C') with hTbar
  have hwc : ∀ q : X ⧸ C', q⁻¹ * π a' * q ∈ (Tbar : Subgroup (X ⧸ C')) →
      q⁻¹ * π a' * q = π a' := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C' q
    rw [← hπ, ← map_inv, ← map_mul, ← map_mul] at hq ⊢
    have hyT : y⁻¹ * a' * y ∈ (T : Subgroup X) := by
      rw [hTbar, Sylow.coe_mapSurjective] at hq
      have h1 : y⁻¹ * a' * y ∈ ((T : Subgroup X).map π).comap π := hq
      rwa [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hC'T] at h1
    have hyA := hW a' (Subgroup.mem_subgroupOf.mpr haA) y hyT
    have heq : (y : G)⁻¹ * a * y = a :=
      conj_eq_of_mem_sup hAab hAN hAH haA y.2 (Subgroup.mem_subgroupOf.mp hyA)
    congr 1
    exact Subtype.ext heq
  let _ : Fintype (X ⧸ C') := Fintype.ofFinite _
  obtain ⟨Nq, hNqn, hNqodd, hNq⟩ := CFSG.ZStar.glauberman_zStar (X ⧸ C') (π a') hā1 hā2
    (conj_eq_of_commute_of_weakClosure Tbar hā2 hwc)
  set H' : Subgroup X := H.subgroupOf X with hH'def
  have hH'n : H'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXN
  set N₀ : Subgroup X := Nq.comap π ⊓ H' with hN₀def
  have hN₀n : N₀.Normal := by
    have := hNqn
    exact Subgroup.normal_inf_normal _ _
  have hN₀H : ∀ x ∈ N₀, (x : G) ∈ H := fun x hx => Subgroup.mem_subgroupOf.mp hx.2
  let f : N₀ →* Nq := (π.comp N₀.subtype).codRestrict Nq fun x => x.2.1
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (x : X) = 1 := congrArg Subtype.val hx
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hC'def,
      Subgroup.mem_subgroupOf] at h1
    have h2 : ((x : X) : G) ∈ A ⊓ H := ⟨h1.1, hN₀H x x.2⟩
    rw [hAH, Subgroup.mem_bot] at h2
    exact Subtype.ext (Subtype.ext h2)
  have hN₀odd : Odd (Nat.card N₀) := hNqodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)
  set N₁ : Subgroup H := (N₀.map X.subtype).subgroupOf H with hN₁def
  have hN₀le : N₀.map X.subtype ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN₀H x hx
  have hN₁n : N₁.Normal := by
    constructor
    intro m hm h
    rw [hN₁def, Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨x, hx, hxm⟩ := hm
    refine ⟨⟨h, Subgroup.mem_sup_left h.2⟩ * x * ⟨h, Subgroup.mem_sup_left h.2⟩⁻¹,
      hN₀n.conj_mem x hx _, ?_⟩
    simpa using hxm
  have hN₁odd : Odd (Nat.card N₁) := by
    rw [hN₁def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀le).toEquiv,
      Subgroup.card_map_of_injective X.subtype_injective]
    exact hN₀odd
  have hN₁bot : N₁ ≤ goldschmidtOddCore H := le_sSup ⟨hN₁n, hN₁odd⟩
  rw [hO] at hN₁bot
  apply hj
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  set h' : X := ⟨h, Subgroup.mem_sup_left hh⟩ with hh'
  set x : X := h' * a' * h'⁻¹ * a'⁻¹ with hx
  have hxH : (x : G) ∈ H := by
    have h1 : a * h⁻¹ * a⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hAN haA) h⁻¹).mp (H.inv_mem hh)
    have h2 : (x : G) = h * (a * h⁻¹ * a⁻¹) := by
      rw [hx]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hh', ha']
      group
    rw [h2]
    exact H.mul_mem hh h1
  have hxN₀ : x ∈ N₀ := by
    refine ⟨?_, Subgroup.mem_subgroupOf.mpr hxH⟩
    change π x ∈ Nq
    have := hNq (π h')
    simpa [hx, map_mul, map_inv] using this
  have hx1 : (⟨(x : G), hxH⟩ : H) ∈ N₁ := by
    rw [hN₁def, Subgroup.mem_subgroupOf]
    exact ⟨x, hxN₀, rfl⟩
  have hx1' := hN₁bot hx1
  rw [Subgroup.mem_bot] at hx1'
  have hx2 : (x : G) = 1 := congrArg Subtype.val hx1'
  have hx3 : (x : G) = h * a * h⁻¹ * a⁻¹ := by
    rw [hx]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hh', ha']
  rw [hx3] at hx2
  calc h * a = (h * a * h⁻¹ * a⁻¹) * a * h := by group
    _ = a * h := by rw [hx2, one_mul]

end CFSG.Goldschmidt
