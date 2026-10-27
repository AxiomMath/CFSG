module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.B11Bender

open Equiv

local notation "t₀" => (swap (0 : Fin 5) 1)
local notation "d₀" => (swap (0 : Fin 5) 1 * swap 2 3)

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_comm_swap : Nat.card {σ : Perm (Fin 5) // σ * t₀ = t₀ * σ} = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_comm_dbl : Nat.card {σ : Perm (Fin 5) // σ * d₀ = d₀ * σ} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem center_comm_dbl : ∀ σ : Perm (Fin 5), σ * d₀ = d₀ * σ →
    (∀ τ : Perm (Fin 5), τ * d₀ = d₀ * τ → σ * τ = τ * σ) → σ = 1 ∨ σ = d₀ := by
  decide +kernel

theorem involution_conj : ∀ σ : Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
    ∃ ρ : Perm (Fin 5), σ = ρ * t₀ * ρ⁻¹ ∨ σ = ρ * d₀ * ρ⁻¹ := by
  decide +kernel

theorem card_dbl : Nat.card {σ : Perm (Fin 5) //
    σ * σ = 1 ∧ σ ≠ 1 ∧ ∀ ρ : Perm (Fin 5), σ ≠ ρ * t₀ * ρ⁻¹} = 15 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_centralizer_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (a : K) :
    Nat.card (Subgroup.centralizer ({e a} : Set K')) =
      Nat.card (Subgroup.centralizer ({a} : Set K)) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem card_centralizer_conj {G : Type*} [Group G] (g a : G) :
    Nat.card (Subgroup.centralizer ({g * a * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) :=
  card_centralizer_mulEquiv (MulAut.conj g) a

theorem dihedral {G : Type*} [Group G] [Finite G] {a v : G} (ha : a * a = 1) (hv : v * v = 1) :
    (∃ z : G, z * z = 1 ∧ z ≠ 1 ∧ z * a = a * z ∧ z * v = v * z) ∨
      ∃ g : G, v = g * a * g⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  obtain ⟨r, hr⟩ : ∃ r : G, a * v = r := ⟨_, rfl⟩
  have har : a * r * a⁻¹ = r⁻¹ := by
    rw [← hr, mul_inv_rev, ha', hv', ← mul_assoc, ha, one_mul]
  have hvr : v * r * v⁻¹ = r⁻¹ := by
    rw [← hr, mul_inv_rev, hv', ha', mul_assoc, mul_assoc, hv, mul_one]
  have hn : 0 < orderOf r := orderOf_pos r
  rcases Nat.even_or_odd (orderOf r) with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    have hm0 : m ≠ 0 := by omega
    have hz1 : r ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0 (by omega)
    have hzz : r ^ m * r ^ m = 1 := by rw [← pow_add, ← hm, pow_orderOf_eq_one]
    have hz' : (r ^ m)⁻¹ = r ^ m := inv_eq_of_mul_eq_one_right hzz
    have h1 : a * r ^ m * a⁻¹ = r ^ m := by rw [← conj_pow, har, inv_pow, hz']
    have h2 : v * r ^ m * v⁻¹ = r ^ m := by rw [← conj_pow, hvr, inv_pow, hz']
    exact ⟨r ^ m, hzz, hz1, (mul_inv_eq_iff_eq_mul.1 h1).symm, (mul_inv_eq_iff_eq_mul.1 h2).symm⟩
  · right
    have h1 : a * r ^ (m + 1) * a⁻¹ = (r ^ (m + 1))⁻¹ := by rw [← conj_pow, har, inv_pow]
    have h2 : r ^ (m + 1) * r ^ (m + 1) = r := by
      rw [← pow_add, show m + 1 + (m + 1) = orderOf r + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    refine ⟨(r ^ (m + 1))⁻¹, ?_⟩
    calc v = (a * v)⁻¹ * a := by rw [mul_inv_rev, hv', ha', mul_assoc, ha, mul_one]
      _ = (r ^ (m + 1) * r ^ (m + 1))⁻¹ * a := by rw [h2, hr]
      _ = (r ^ (m + 1))⁻¹ * (a * r ^ (m + 1) * a⁻¹) * a := by rw [h1, mul_inv_rev]
      _ = (r ^ (m + 1))⁻¹ * a * ((r ^ (m + 1))⁻¹)⁻¹ := by group

structure CentralElevenSym5 {G : Type*} [Group G] (y : G) (ψ : Perm (Fin 5) →* G) : Prop where
  orderOf_eq : orderOf y = 11
  comm : ∀ g : G, g * y = y * g
  injective : Function.Injective ψ

namespace CentralElevenSym5

variable {G : Type*} [Group G] {y : G} {ψ : Perm (Fin 5) →* G} (E : CentralElevenSym5 y ψ)
include E

theorem comm_of_mem {c : G} (hc : c ∈ Subgroup.zpowers y) (g : G) : g * c = c * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have h : Commute g y := E.comm g
  exact (h.zpow_right k).eq

theorem orderOf_map_dvd_120 (σ : Perm (Fin 5)) : orderOf (ψ σ) ∣ 120 :=
  (orderOf_map_dvd ψ σ).trans (card_perm_five ▸ orderOf_dvd_natCard σ)

theorem eq_one_of_pow_eq_one {c : G} (hc : c ∈ Subgroup.zpowers y) {k : ℕ} (hk : c ^ k = 1)
    (hcop : Nat.Coprime k 11) : c = 1 := by
  have h11 : orderOf c ∣ 11 := E.orderOf_eq ▸ orderOf_dvd_of_mem_zpowers hc
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) h11
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h
  exact orderOf_eq_one_iff.1 h

theorem eq_one_of_eq_map {c : G} (hc : c ∈ Subgroup.zpowers y) {ρ : Perm (Fin 5)}
    (h : c = ψ ρ) : c = 1 :=
  E.eq_one_of_pow_eq_one hc (k := 120) (orderOf_dvd_iff_pow_eq_one.1 (h ▸ E.orderOf_map_dvd_120 ρ))
    (by norm_num)

theorem mul_map_inj {c c' : G} (hc : c ∈ Subgroup.zpowers y) (hc' : c' ∈ Subgroup.zpowers y)
    {σ σ' : Perm (Fin 5)} (h : c * ψ σ = c' * ψ σ') : c = c' ∧ σ = σ' := by
  have h1 : c'⁻¹ * c = ψ (σ' * σ⁻¹) := by
    rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]
  have hcc : c = c' :=
    (inv_mul_eq_one.1 (E.eq_one_of_eq_map (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc') hc) h1)).symm
  refine ⟨hcc, E.injective ?_⟩
  rw [hcc] at h
  exact mul_left_cancel h

theorem eq_one_of_mul_map_eq_one {c : G} (hc : c ∈ Subgroup.zpowers y) {σ : Perm (Fin 5)}
    (h : c * ψ σ = 1) : c = 1 ∧ σ = 1 :=
  E.mul_map_inj hc (Subgroup.one_mem _) (by rw [h, map_one, one_mul])

theorem involution_of_mul {c : G} (hc : c ∈ Subgroup.zpowers y) {σ : Perm (Fin 5)}
    (h : c * ψ σ * (c * ψ σ) = 1) : c = 1 ∧ σ * σ = 1 := by
  have hcom : c * ψ σ = ψ σ * c := (E.comm_of_mem hc (ψ σ)).symm
  have h1 : c * c * ψ (σ * σ) = 1 := by
    calc c * c * ψ (σ * σ) = c * (c * ψ σ) * ψ σ := by rw [map_mul]; simp only [mul_assoc]
      _ = c * (ψ σ * c) * ψ σ := by rw [hcom]
      _ = c * ψ σ * (c * ψ σ) := by simp only [mul_assoc]
      _ = 1 := h
  obtain ⟨hcc, hσ⟩ := E.eq_one_of_mul_map_eq_one (Subgroup.mul_mem _ hc hc) h1
  exact ⟨E.eq_one_of_pow_eq_one hc (k := 2) (by rw [pow_two, hcc]) (by norm_num), hσ⟩

theorem mul_map_comm {c : G} (hc : c ∈ Subgroup.zpowers y) {σ σ₀ : Perm (Fin 5)}
    (h : σ * σ₀ = σ₀ * σ) : c * ψ σ * ψ σ₀ = ψ σ₀ * (c * ψ σ) := by
  rw [mul_assoc, ← map_mul ψ, h, map_mul, ← mul_assoc, ← mul_assoc, E.comm_of_mem hc (ψ σ₀)]

theorem eq_of_conj {c : G} (hc : c ∈ Subgroup.zpowers y) {ρ τ : Perm (Fin 5)} {g : G}
    (h : (ψ ρ)⁻¹ * g * ψ ρ = c * ψ τ) : g = c * ψ (ρ * τ * ρ⁻¹) := by
  have hcρ := E.comm_of_mem hc (ψ ρ)
  calc g = ψ ρ * ((ψ ρ)⁻¹ * g * ψ ρ) * (ψ ρ)⁻¹ := by group
    _ = ψ ρ * c * ψ τ * (ψ ρ)⁻¹ := by rw [h]; simp only [mul_assoc]
    _ = c * ψ (ρ * τ * ρ⁻¹) := by rw [hcρ, map_mul, map_mul, map_inv]; simp only [mul_assoc]

variable [Finite G]

theorem centralizer_card (σ₀ : Perm (Fin 5)) {k : ℕ}
    (hk : Nat.card {σ : Perm (Fin 5) // σ * σ₀ = σ₀ * σ} = k) :
    11 * k ≤ Nat.card (Subgroup.centralizer ({ψ σ₀} : Set G)) ∧
      (Nat.card (Subgroup.centralizer ({ψ σ₀} : Set G)) ≤ 11 * k →
        ∀ g : G, g * ψ σ₀ = ψ σ₀ * g →
          ∃ c ∈ Subgroup.zpowers y, ∃ σ : Perm (Fin 5), σ * σ₀ = σ₀ * σ ∧ g = c * ψ σ) := by
  let f : Subgroup.zpowers y × {σ : Perm (Fin 5) // σ * σ₀ = σ₀ * σ} →
      Subgroup.centralizer ({ψ σ₀} : Set G) := fun p =>
    ⟨(p.1 : G) * ψ p.2.1,
      Subgroup.mem_centralizer_singleton_iff.2 (E.mul_map_comm p.1.2 p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨c, σ⟩ ⟨c', σ'⟩ h
    obtain ⟨h1, h2⟩ := E.mul_map_inj c.2 c'.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hcard : Nat.card (Subgroup.zpowers y × {σ : Perm (Fin 5) // σ * σ₀ = σ₀ * σ}) = 11 * k := by
    rw [Nat.card_prod, Nat.card_zpowers, E.orderOf_eq, hk]
  refine ⟨hcard ▸ Nat.card_le_card_of_injective f hf, fun hle g hg => ?_⟩
  have hbij := hf.bijective_of_nat_card_le (by rw [hcard]; exact hle)
  obtain ⟨⟨c, σ⟩, hcσ⟩ := hbij.2 ⟨g, Subgroup.mem_centralizer_singleton_iff.2 hg⟩
  exact ⟨c, c.2, σ.1, σ.2, (congrArg Subtype.val hcσ).symm⟩

theorem mem_of_comm_dbl (hB : Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) ≤ 88) {g : G}
    (hg : g * ψ d₀ = ψ d₀ * g) :
    ∃ c ∈ Subgroup.zpowers y, ∃ σ : Perm (Fin 5), σ * d₀ = d₀ * σ ∧ g = c * ψ σ :=
  (E.centralizer_card d₀ card_comm_dbl).2 hB g hg

theorem eq_dbl_of_comm (hB : Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) ≤ 88) {u : G}
    (hu : u * u = 1) (hu1 : u ≠ 1)
    (hc : ∀ σ : Perm (Fin 5), σ * d₀ = d₀ * σ → u * ψ σ = ψ σ * u) : u = ψ d₀ := by
  obtain ⟨c, hc', σ, hσ, rfl⟩ := E.mem_of_comm_dbl hB (hc d₀ rfl)
  obtain ⟨rfl, -⟩ := E.involution_of_mul hc' hu
  rw [one_mul] at hc hu1 ⊢
  have hcen : ∀ τ : Perm (Fin 5), τ * d₀ = d₀ * τ → σ * τ = τ * σ := fun τ hτ =>
    E.injective (by rw [map_mul, map_mul]; exact hc τ hτ)
  rcases center_comm_dbl σ hσ hcen with rfl | rfl
  · exact absurd (map_one ψ) hu1
  · rfl

theorem card_P0 :
    Nat.card ((Subgroup.centralizer ({d₀} : Set (Perm (Fin 5)))).map ψ) = 8 := by
  rw [Subgroup.card_map_of_injective E.injective, ← card_comm_dbl]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => Subgroup.mem_centralizer_singleton_iff)

theorem eq_P0_of_le (hB : Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) ≤ 88)
    {S : Subgroup G} (hS : IsPGroup 2 S)
    (hle : (Subgroup.centralizer ({d₀} : Set (Perm (Fin 5)))).map ψ ≤ S) :
    S = (Subgroup.centralizer ({d₀} : Set (Perm (Fin 5)))).map ψ := by
  have hdP : ∀ σ : Perm (Fin 5), σ * d₀ = d₀ * σ → ψ σ ∈ S := fun σ hσ =>
    hle ⟨σ, Subgroup.mem_centralizer_singleton_iff.2 hσ, rfl⟩
  have hd1 : ψ d₀ ≠ 1 := fun h =>
    absurd (E.injective (h.trans (map_one ψ).symm)) (by decide)
  haveI : Nontrivial S := ⟨⟨⟨ψ d₀, hdP d₀ rfl⟩, 1, fun h => hd1 (congrArg Subtype.val h)⟩⟩
  have hZ := hS.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := (hS.to_subgroup (Subgroup.center S)).nontrivial_iff_card.1 hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2
    (hn ▸ dvd_pow_self 2 hn0.ne')
  have hzu : orderOf ((z : S) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have huu : ((z : S) : G) * ((z : S) : G) = 1 := by
    rw [← pow_two, ← hzu, pow_orderOf_eq_one]
  have hu1 : ((z : S) : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzu
    exact absurd hzu (by decide)
  have hcomm : ∀ s ∈ S, s * ((z : S) : G) = ((z : S) : G) * s := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨s, hs⟩)
  have hud : ((z : S) : G) = ψ d₀ :=
    E.eq_dbl_of_comm hB huu hu1 fun σ hσ => (hcomm _ (hdP σ hσ)).symm
  refine le_antisymm (fun s hs => ?_) hle
  obtain ⟨c, hc, σ, hσ, rfl⟩ := E.mem_of_comm_dbl hB (g := s) (by rw [← hud]; exact hcomm s hs)
  obtain ⟨k, hk⟩ := hS ⟨_, hs⟩
  have hk' : (c * ψ σ) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hcom : Commute c (ψ σ) := (E.comm_of_mem hc (ψ σ)).symm
  rw [hcom.mul_pow, ← map_pow] at hk'
  obtain ⟨hc1, -⟩ := E.eq_one_of_mul_map_eq_one (Subgroup.pow_mem _ hc _) hk'
  have hc2 : c = 1 := E.eq_one_of_pow_eq_one hc hc1 (Nat.Coprime.pow_left k (by norm_num))
  exact ⟨σ, Subgroup.mem_centralizer_singleton_iff.2 hσ, by rw [hc2, one_mul]⟩

theorem card_centralizer_swap (hA : Nat.card (Subgroup.centralizer ({ψ t₀} : Set G)) ∣ 264)
    (hB : Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) ≤ 88) :
    Nat.card (Subgroup.centralizer ({ψ t₀} : Set G)) = 132 := by
  have h132 := (E.centralizer_card t₀ card_comm_swap).1
  obtain ⟨m, hm⟩ := hA
  have hm2 : m ≤ 2 := by
    by_contra hm3
    have := Nat.mul_le_mul h132 (show 3 ≤ m by omega)
    rw [← hm] at this
    norm_num at this
  interval_cases m
  · omega
  · exfalso
    have h264 : Nat.card (Subgroup.centralizer ({ψ t₀} : Set G)) = 2 ^ 3 * 33 := by omega
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 3)
      (G := Subgroup.centralizer ({ψ t₀} : Set G)) (by rw [h264]; exact Dvd.intro 33 rfl)
    let T : Subgroup G := K.map (Subgroup.centralizer ({ψ t₀} : Set G)).subtype
    have hT : Nat.card T = 8 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
      norm_num
    have hTC : T ≤ Subgroup.centralizer ({ψ t₀} : Set G) := Subgroup.map_subtype_le K
    obtain ⟨Q, hTQ⟩ := (IsPGroup.of_card (p := 2) (n := 3) (by rw [hT]; norm_num) :
      IsPGroup 2 T).exists_le_sylow
    let P : Sylow 2 G :=
      { toSubgroup := (Subgroup.centralizer ({d₀} : Set (Perm (Fin 5)))).map ψ
        isPGroup' := IsPGroup.of_card (n := 3) (by rw [E.card_P0]; norm_num)
        is_maximal' := fun {_} hS hle => E.eq_P0_of_le hB hS hle }
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
    have hQ8 : Nat.card Q = 8 := by
      rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P]
      exact E.card_P0
    have hTQ' : T = Q := Subgroup.eq_of_le_of_card_ge hTQ (by rw [hQ8, hT])
    have hconj : ∀ σ : Perm (Fin 5), σ * d₀ = d₀ * σ →
        g * ψ σ * g⁻¹ ∈ Subgroup.centralizer ({ψ t₀} : Set G) := by
      intro σ hσ
      apply hTC
      rw [hTQ', ← hg, Sylow.coe_subgroup_smul]
      have h := Subgroup.smul_mem_pointwise_smul (ψ σ) (MulAut.conj g) (P : Subgroup G)
        ⟨σ, Subgroup.mem_centralizer_singleton_iff.2 hσ, rfl⟩
      rwa [MulAut.smul_def, MulAut.conj_apply] at h
    have ht : ψ t₀ * ψ t₀ = 1 := by
      rw [← map_mul, show t₀ * t₀ = 1 by decide, map_one]
    have hu : g⁻¹ * ψ t₀ * g = ψ d₀ := by
      refine E.eq_dbl_of_comm hB ?_ ?_ ?_
      · calc g⁻¹ * ψ t₀ * g * (g⁻¹ * ψ t₀ * g) = g⁻¹ * (ψ t₀ * ψ t₀) * g := by group
          _ = 1 := by rw [ht]; group
      · intro h1
        have h2 : ψ t₀ = ψ 1 := by
          calc ψ t₀ = g * (g⁻¹ * ψ t₀ * g) * g⁻¹ := by group
            _ = ψ 1 := by rw [h1, map_one]; group
        exact absurd (E.injective h2) (by decide)
      · intro σ hσ
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hconj σ hσ)
        calc g⁻¹ * ψ t₀ * g * ψ σ = g⁻¹ * (ψ t₀ * (g * ψ σ * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * ψ σ * g⁻¹ * ψ t₀) * g := by rw [h1]
          _ = ψ σ * (g⁻¹ * ψ t₀ * g) := by group
    have hconjtd : ψ t₀ = g * ψ d₀ * g⁻¹ := by rw [← hu]; group
    have := card_centralizer_conj g (ψ d₀)
    rw [← hconjtd] at this
    omega
  · omega

theorem mem_of_comm_involution (hA : Nat.card (Subgroup.centralizer ({ψ t₀} : Set G)) ∣ 264)
    (hB : Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) ≤ 88) {σ : Perm (Fin 5)}
    (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) {g : G} (hg : g * ψ σ = ψ σ * g) :
    ∃ c ∈ Subgroup.zpowers y, ∃ τ : Perm (Fin 5), g = c * ψ τ := by
  have hconj : ∀ ρ σ₀ : Perm (Fin 5), σ = ρ * σ₀ * ρ⁻¹ →
      (ψ ρ)⁻¹ * g * ψ ρ * ψ σ₀ = ψ σ₀ * ((ψ ρ)⁻¹ * g * ψ ρ) := by
    intro ρ σ₀ hρ
    have hψσ : ψ σ = ψ ρ * ψ σ₀ * (ψ ρ)⁻¹ := by rw [hρ, map_mul, map_mul, map_inv]
    calc (ψ ρ)⁻¹ * g * ψ ρ * ψ σ₀ = (ψ ρ)⁻¹ * (g * (ψ ρ * ψ σ₀ * (ψ ρ)⁻¹)) * ψ ρ := by group
      _ = (ψ ρ)⁻¹ * ((ψ ρ * ψ σ₀ * (ψ ρ)⁻¹) * g) * ψ ρ := by rw [← hψσ, hg]
      _ = ψ σ₀ * ((ψ ρ)⁻¹ * g * ψ ρ) := by group
  obtain ⟨ρ, hρ | hρ⟩ := involution_conj σ hσ hσ1
  · obtain ⟨c, hc, τ, -, hτ⟩ := (E.centralizer_card t₀ card_comm_swap).2
      (E.card_centralizer_swap hA hB).le _ (hconj ρ _ hρ)
    exact ⟨c, hc, _, E.eq_of_conj hc hτ⟩
  · obtain ⟨c, hc, τ, -, hτ⟩ := E.mem_of_comm_dbl hB (hconj ρ _ hρ)
    exact ⟨c, hc, _, E.eq_of_conj hc hτ⟩

theorem mem_of_involution (hA : Nat.card (Subgroup.centralizer ({ψ t₀} : Set G)) ∣ 264)
    (hB : Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) ≤ 88) {v : G} (hv : v * v = 1)
    (hv1 : v ≠ 1) : ∃ c ∈ Subgroup.zpowers y, ∃ σ : Perm (Fin 5), v = c * ψ σ := by
  by_contra hvH
  have key : ∀ c ∈ Subgroup.zpowers y, ∀ σ : Perm (Fin 5), c * ψ σ * (c * ψ σ) = 1 →
      c * ψ σ ≠ 1 → c * ψ σ * v = v * (c * ψ σ) → False := by
    intro c hc σ hz hz1 hzv
    obtain ⟨rfl, hσ⟩ := E.involution_of_mul hc hz
    rw [one_mul] at hz1 hzv
    have hσ1 : σ ≠ 1 := fun h => hz1 (by rw [h, map_one])
    exact hvH (E.mem_of_comm_involution hA hB hσ hσ1 hzv.symm)
  have hconj : ∀ σ₀ : Perm (Fin 5), σ₀ * σ₀ = 1 →
      (∀ z : G, z * ψ σ₀ = ψ σ₀ * z →
        ∃ c ∈ Subgroup.zpowers y, ∃ σ : Perm (Fin 5), z = c * ψ σ) →
      ∃ g : G, v = g * ψ σ₀ * g⁻¹ := by
    intro σ₀ hσ₀ hcent
    have hs : ψ σ₀ * ψ σ₀ = 1 := by rw [← map_mul, hσ₀, map_one]
    rcases dihedral hs hv with ⟨z, hz, hz1, hzt, hzv⟩ | h
    · obtain ⟨c, hc, σ, rfl⟩ := hcent z hzt
      exact (key c hc σ hz hz1 hzv).elim
    · exact h
  obtain ⟨g, hg⟩ := hconj t₀ (by decide) fun z hz => by
    obtain ⟨c, hc, σ, -, h⟩ := (E.centralizer_card t₀ card_comm_swap).2
      (E.card_centralizer_swap hA hB).le z hz
    exact ⟨c, hc, σ, h⟩
  obtain ⟨g', hg'⟩ := hconj d₀ (by decide) fun z hz => by
    obtain ⟨c, hc, σ, -, h⟩ := E.mem_of_comm_dbl hB hz
    exact ⟨c, hc, σ, h⟩
  have htd : ψ t₀ = (g⁻¹ * g') * ψ d₀ * (g⁻¹ * g')⁻¹ := by
    calc ψ t₀ = g⁻¹ * (g * ψ t₀ * g⁻¹) * g := by group
      _ = g⁻¹ * (g' * ψ d₀ * g'⁻¹) * g := by rw [← hg, hg']
      _ = (g⁻¹ * g') * ψ d₀ * (g⁻¹ * g')⁻¹ := by group
  have h1 := E.card_centralizer_swap hA hB
  rw [htd, card_centralizer_conj] at h1
  omega

theorem le_card : 1320 ≤ Nat.card G := by
  let f : Subgroup.zpowers y × Perm (Fin 5) → G := fun p => p.1 * ψ p.2
  have hf : Function.Injective f := fun ⟨c, σ⟩ ⟨c', σ'⟩ h => by
    obtain ⟨h1, h2⟩ := E.mul_map_inj c.2 c'.2 h
    exact Prod.ext (Subtype.ext h1) h2
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_zpowers, E.orderOf_eq, card_perm_five] at this

theorem card_le (hA : Nat.card (Subgroup.centralizer ({ψ t₀} : Set G)) ∣ 264)
    (hB : Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) ≤ 88) : Nat.card G ≤ 1320 := by
  have hdd : ψ d₀ * ψ d₀ = 1 := by rw [← map_mul, show d₀ * d₀ = 1 by decide, map_one]
  have hsub : conjugatesOf (ψ d₀) ⊆
      ψ '' {σ | σ * σ = 1 ∧ σ ≠ 1 ∧ ∀ ρ : Perm (Fin 5), σ ≠ ρ * t₀ * ρ⁻¹} := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.1 hx
    have hx2 : g * ψ d₀ * g⁻¹ * (g * ψ d₀ * g⁻¹) = 1 := by
      calc g * ψ d₀ * g⁻¹ * (g * ψ d₀ * g⁻¹) = g * (ψ d₀ * ψ d₀) * g⁻¹ := by group
        _ = 1 := by rw [hdd]; group
    have hx1 : g * ψ d₀ * g⁻¹ ≠ 1 := fun h => by
      have h2 : ψ d₀ = ψ 1 := by
        calc ψ d₀ = g⁻¹ * (g * ψ d₀ * g⁻¹) * g := by group
          _ = ψ 1 := by rw [h, map_one]; group
      exact absurd (E.injective h2) (by decide)
    obtain ⟨c, hc, σ, hxe⟩ := E.mem_of_involution hA hB hx2 hx1
    rw [hxe] at hx2
    obtain ⟨rfl, hσ⟩ := E.involution_of_mul hc hx2
    rw [one_mul] at hxe
    refine ⟨σ, ⟨hσ, fun h => hx1 (by rw [hxe, h, map_one]), fun ρ hρ => ?_⟩, hxe.symm⟩
    have hdt : ψ d₀ = (g⁻¹ * ψ ρ) * ψ t₀ * (g⁻¹ * ψ ρ)⁻¹ := by
      calc ψ d₀ = g⁻¹ * (g * ψ d₀ * g⁻¹) * g := by group
        _ = g⁻¹ * (ψ ρ * ψ t₀ * (ψ ρ)⁻¹) * g := by rw [hxe, hρ, map_mul, map_mul, map_inv]
        _ = (g⁻¹ * ψ ρ) * ψ t₀ * (g⁻¹ * ψ ρ)⁻¹ := by group
    have h1 := E.card_centralizer_swap hA hB
    rw [← card_centralizer_conj (g⁻¹ * ψ ρ) (ψ t₀), ← hdt] at h1
    omega
  have hind : (Subgroup.centralizer ({ψ d₀} : Set G)).index ≤ 15 := by
    rw [Subgroup.index_centralizer_eq_ncard]
    calc (conjugatesOf (ψ d₀)).ncard
        ≤ (ψ '' {σ | σ * σ = 1 ∧ σ ≠ 1 ∧ ∀ ρ : Perm (Fin 5), σ ≠ ρ * t₀ * ρ⁻¹}).ncard :=
          Set.ncard_le_ncard hsub
      _ ≤ {σ : Perm (Fin 5) | σ * σ = 1 ∧ σ ≠ 1 ∧ ∀ ρ : Perm (Fin 5), σ ≠ ρ * t₀ * ρ⁻¹}.ncard :=
          Set.ncard_image_le
      _ = 15 := by rw [← Nat.card_coe_set_eq]; exact card_dbl
  calc Nat.card G = Nat.card (Subgroup.centralizer ({ψ d₀} : Set G)) *
        (Subgroup.centralizer ({ψ d₀} : Set G)).index := (Subgroup.card_mul_index _).symm
    _ ≤ 88 * 15 := Nat.mul_le_mul hB hind
    _ = 1320 := by norm_num

end CentralElevenSym5

theorem card_eq_of_eleven_sym5 {G : Type*} [Group G] [Finite G] {y : G} (hy : orderOf y = 11)
    (hyc : ∀ g : G, g * y = y * g) (ψ : Perm (Fin 5) →* G) (hψ : Function.Injective ψ)
    (hA : Nat.card (Subgroup.centralizer ({ψ (swap 0 1)} : Set G)) ∣ 264)
    (hB : Nat.card (Subgroup.centralizer ({ψ (swap 0 1 * swap 2 3)} : Set G)) ≤ 88) :
    Nat.card G = 1320 :=
  have E : CentralElevenSym5 y ψ := ⟨hy, hyc, hψ⟩
  le_antisymm (E.card_le hA hB) E.le_card

end CFSG.HardMathSupport.Dickson.BMRows.B11Bender
