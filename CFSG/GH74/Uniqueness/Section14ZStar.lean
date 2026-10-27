module

public import CFSG.GH74.Uniqueness.Section14Defs
public import CFSG.GH74.Uniqueness.Section14Primary

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem exists_odd_order_lift {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsPGroup 2 N) {x : G ⧸ N} (hx : Odd (orderOf x)) :
    ∃ w : G, (w : G ⧸ N) = x ∧ Odd (orderOf w) := by
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective x
  set m := orderOf (w₀ : G ⧸ N) with hm
  have hwm : w₀ ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hN ⟨w₀ ^ m, hwm⟩
  have hk' : orderOf (w₀ ^ m) = 2 ^ k := by
    rw [← Subgroup.orderOf_mk (w₀ ^ m) hwm]
    exact hk
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx)
  obtain ⟨a, b, hab⟩ := hcop
  have h0 : (w₀ ^ m) ^ (2 ^ k) = 1 := by
    rw [← hk']
    exact pow_orderOf_eq_one _
  refine ⟨w₀ ^ (a * ((2 ^ k : ℕ) : ℤ)), ?_, ?_⟩
  · rw [QuotientGroup.mk_zpow]
    have e : a * ((2 ^ k : ℕ) : ℤ) = 1 + (-b) * (m : ℤ) := by linarith
    rw [e, zpow_add, zpow_one, zpow_mul', zpow_natCast, hm, pow_orderOf_eq_one, one_zpow,
      mul_one]
  · have h1 : (w₀ ^ (a * ((2 ^ k : ℕ) : ℤ))) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have e : a * ((2 ^ k : ℕ) : ℤ) * (m : ℤ) = ((m * 2 ^ k : ℕ) : ℤ) * a := by push_cast; ring
      rw [e, zpow_mul, zpow_natCast, pow_mul, h0, one_zpow]
    exact Odd.of_dvd_nat hx (orderOf_dvd_of_pow_eq_one h1)

theorem inv_of_fpf_involution {H : Type*} [Group H] [Finite H] {O : Subgroup H} {z : H}
    (hz2 : z * z = 1) (hO : ∀ x ∈ O, z * x * z⁻¹ ∈ O) (hC : ∀ x ∈ O, z * x = x * z → x = 1) :
    ∀ x ∈ O, z * x * z⁻¹ = x⁻¹ := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  let f : O → O := fun x =>
    ⟨(x : H)⁻¹ * (z * x * z⁻¹), O.mul_mem (O.inv_mem x.2) (hO x x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : H)⁻¹ * (z * x * z⁻¹) = (y : H)⁻¹ * (z * y * z⁻¹) := congrArg Subtype.val hxy
    have h2 : (y : H) * (x : H)⁻¹ ∈ O := O.mul_mem y.2 (O.inv_mem x.2)
    have h3 : (y : H) * (x : H)⁻¹ = z * ((y : H) * (x : H)⁻¹) * z⁻¹ := by
      calc (y : H) * (x : H)⁻¹
          = ((y : H) * ((x : H)⁻¹ * (z * x * z⁻¹))) * (z * x * z⁻¹)⁻¹ := by group
        _ = ((y : H) * ((y : H)⁻¹ * (z * y * z⁻¹))) * (z * x * z⁻¹)⁻¹ := by rw [h1]
        _ = z * ((y : H) * (x : H)⁻¹) * z⁻¹ := by group
    have h4 : z * ((y : H) * (x : H)⁻¹) = ((y : H) * (x : H)⁻¹) * z := by
      calc z * ((y : H) * (x : H)⁻¹) = (z * ((y : H) * (x : H)⁻¹) * z⁻¹) * z := by group
        _ = ((y : H) * (x : H)⁻¹) * z := by rw [← h3]
    have h5 := hC _ h2 h4
    have : (y : H) = x := by
      have := congrArg (fun a => a * (x : H)) h5
      simpa using this
    exact (Subtype.ext this).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro a ha
  obtain ⟨x, hx⟩ := hsurj ⟨a, ha⟩
  have hxa : (x : H)⁻¹ * (z * x * z⁻¹) = a := congrArg Subtype.val hx
  rw [← hxa]
  have e1 : z * ((x : H)⁻¹ * (z * x * z⁻¹)) * z⁻¹ = z * (x : H)⁻¹ * z * x * (z * z) := by
    rw [hzi]
    group
  have e2 : ((x : H)⁻¹ * (z * x * z⁻¹))⁻¹ = z * (x : H)⁻¹ * z * x := by
    calc ((x : H)⁻¹ * (z * x * z⁻¹))⁻¹ = z * (x : H)⁻¹ * z⁻¹ * x := by group
      _ = z * (x : H)⁻¹ * z * x := by rw [hzi]
  rw [e1, e2, hz2, mul_one]

theorem exists_normal_sylow_of_zStar {H : Type} [Group H] [Finite H] (Sb : Sylow 2 H)
    (z : (Sb : Subgroup H)) (hzZ : z ∈ Subgroup.center (Sb : Subgroup H)) (hz : orderOf z = 2)
    (hwc : ∀ g : H, g⁻¹ * (z : H) * g ∈ (Sb : Subgroup H) → g⁻¹ * (z : H) * g = z)
    {r : ℕ} (hr : r.Prime) (hrC : ∀ c ∈ centralizer ({(z : H)} : Set H), ¬ r ∣ orderOf c)
    (hCO : ∀ x ∈ CFSG.oddCore H, (z : H) * x = x * (z : H) → x = 1) :
    ∃ Rb : Sylow r H, (Rb : Subgroup H).Normal := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar Sb z hzZ hz hwc
  have hzord : orderOf (z : H) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hzz : (z : H) * z = 1 := by
    have := pow_orderOf_eq_one (z : H)
    rwa [hzord, sq] at this
  have hOn : ∀ x ∈ CFSG.oddCore H, (z : H) * x * (z : H)⁻¹ ∈ CFSG.oddCore H := fun x hx =>
    (CFSG.oddCore_normal (G := H)).conj_mem x hx z
  have hinv := inv_of_fpf_involution hzz hOn hCO
  have hOcomm : ∀ a ∈ CFSG.oddCore H, ∀ b ∈ CFSG.oddCore H, a * b = b * a := by
    intro a ha b hb
    have h1 := hinv (a * b) ((CFSG.oddCore H).mul_mem ha hb)
    have h2 : (z : H) * (a * b) * (z : H)⁻¹ =
        ((z : H) * a * (z : H)⁻¹) * ((z : H) * b * (z : H)⁻¹) := by group
    rw [h2, hinv a ha, hinv b hb, mul_inv_rev] at h1
    have h3 := congrArg (fun y => y⁻¹) h1
    simpa using h3.symm
  set Rp : Subgroup H := primaryComponent (CFSG.oddCore H) hOcomm r with hRp
  have hRpn : Rp.Normal :=
    ⟨fun a ha g => primaryComponent_conj (fun b hb => (CFSG.oddCore_normal (G := H)).conj_mem b hb g)
      ha⟩
  obtain ⟨Pr⟩ : Nonempty (Sylow r H) := inferInstance
  have hPle : (Pr : Subgroup H) ≤ Rp := by
    intro x hx
    obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp Pr.isPGroup' ⟨x, hx⟩
    have hxord : orderOf x = r ^ a := by
      rw [← Subgroup.orderOf_mk x hx]
      exact ha
    obtain ⟨c, hcC, k, hkO, hxck⟩ := hfac x
    have hxO : x ∈ CFSG.oddCore H := by
      have hmk : (QuotientGroup.mk x : H ⧸ CFSG.oddCore H) = QuotientGroup.mk c := by
        rw [hxck, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hkO, mul_one]
      have h1 : orderOf (QuotientGroup.mk x : H ⧸ CFSG.oddCore H) ∣ r ^ a := by
        rw [← hxord]
        exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.oddCore H)) x
      have h2 : orderOf (QuotientGroup.mk x : H ⧸ CFSG.oddCore H) ∣ orderOf c := by
        rw [hmk]
        exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.oddCore H)) c
      have hcop : Nat.Coprime (r ^ a) (orderOf c) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr).mpr (hrC c hcC))
      have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
      exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)
    exact mem_primaryComponent_of_orderOf hxO hxord
  have heq : Rp = (Pr : Subgroup H) := Pr.is_maximal' (isPGroup_primaryComponent hr) hPle
  refine ⟨Pr, ?_⟩
  rw [← heq]
  exact hRpn

theorem exists_sylow_normal_sup {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    {r : ℕ} [Fact r.Prime] (Rb : Sylow r (G ⧸ N)) (hRb : (Rb : Subgroup (G ⧸ N)).Normal) :
    ∃ R : Sylow r G, ∀ g : G, ∀ x ∈ (R : Subgroup G) ⊔ N, g * x * g⁻¹ ∈ (R : Subgroup G) ⊔ N := by
  obtain ⟨R, hR⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective N) r Rb
  have hmap : (R : Subgroup G).map (QuotientGroup.mk' N) = Rb := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N) R, hR]
  refine ⟨R, fun g x hx => ?_⟩
  have hcm : (R : Subgroup G) ⊔ N = (Rb : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N) := by
    rw [← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [hcm] at hx ⊢
  rw [Subgroup.mem_comap] at hx ⊢
  simpa using hRb.conj_mem _ hx (QuotientGroup.mk' N g)

theorem zstar14_abstract {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN2 : IsPGroup 2 N) (T : Sylow 2 G) (hNT : N ≤ (T : Subgroup G)) (v : G)
    (hvT : v ∈ (T : Subgroup G)) (hvN : v ∉ N) (hv2 : v * v ∈ N)
    (hTv : ∀ s ∈ (T : Subgroup G), s * v * s⁻¹ * v⁻¹ ∈ N)
    (hweak : ∀ g : G, g * v * g⁻¹ ∈ (T : Subgroup G) → g * v * g⁻¹ * v⁻¹ ∈ N)
    (hQN : ∀ g : G, g * v * g⁻¹ * v⁻¹ ∈ N → g ∈ normalizer ((T : Subgroup G) : Set G))
    (hodd : ∀ w : G, Odd (orderOf w) → w ∈ normalizer ((T : Subgroup G) : Set G) →
      (∀ s ∈ (T : Subgroup G), w * s * w⁻¹ * s⁻¹ ∈ N) → w = 1)
    {r : ℕ} (hr : r.Prime) (hrQ : ∀ g : G, g * v * g⁻¹ * v⁻¹ ∈ N → ¬ r ∣ orderOf g) :
    ∃ R : Sylow r G, ∀ g : G, ∀ x ∈ (R : Subgroup G) ⊔ N, g * x * g⁻¹ ∈ (R : Subgroup G) ⊔ N := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hcomm_iff : ∀ g : G, g * v * g⁻¹ * v⁻¹ ∈ N ↔
      (v : G ⧸ N) * (g : G ⧸ N) = (g : G ⧸ N) * (v : G ⧸ N) := by
    intro g
    rw [← QuotientGroup.eq_one_iff (N := N), QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul]
    exact eq_comm
  let Sb : Sylow 2 (G ⧸ N) := Sylow.mapSurjective hπ T
  have hSbmem : ∀ y : G ⧸ N, y ∈ (Sb : Subgroup (G ⧸ N)) ↔
      ∃ s ∈ (T : Subgroup G), (s : G ⧸ N) = y := fun y => Subgroup.mem_map
  have hzmem : (v : G ⧸ N) ∈ (Sb : Subgroup (G ⧸ N)) := (hSbmem _).mpr ⟨v, hvT, rfl⟩
  let z : (Sb : Subgroup (G ⧸ N)) := ⟨(v : G ⧸ N), hzmem⟩
  have hzZ : z ∈ Subgroup.center (Sb : Subgroup (G ⧸ N)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨s, hs, hsy⟩ := (hSbmem _).mp y.2
    apply Subtype.ext
    show (y : G ⧸ N) * (v : G ⧸ N) = (v : G ⧸ N) * (y : G ⧸ N)
    rw [← hsy]
    exact ((hcomm_iff s).mp (hTv s hs)).symm
  have hz : orderOf z = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      apply Subtype.ext
      show (v : G ⧸ N) * (v : G ⧸ N) = 1
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff (N := N) _).mpr hv2
    · intro h
      apply hvN
      have h1 : (v : G ⧸ N) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (N := N) _).mp h1
  have hwc : ∀ g : G ⧸ N, g⁻¹ * (z : G ⧸ N) * g ∈ (Sb : Subgroup (G ⧸ N)) →
      g⁻¹ * (z : G ⧸ N) * g = z := by
    intro g hg
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨s, hs, hsg⟩ := (hSbmem _).mp hg
    have h1 : g₀⁻¹ * v * g₀ ∈ (T : Subgroup G) := by
      have h2' : (s : G ⧸ N) = (g₀ : G ⧸ N)⁻¹ * (v : G ⧸ N) * (g₀ : G ⧸ N) := hsg
      have h2 : (s : G ⧸ N) = ((g₀⁻¹ * v * g₀ : G) : G ⧸ N) := by
        rw [h2', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h3 : s⁻¹ * (g₀⁻¹ * v * g₀) ∈ N := QuotientGroup.eq.mp h2
      have h4 := (T : Subgroup G).mul_mem hs (hNT h3)
      simpa using h4
    have h5 := hweak g₀⁻¹ (by simpa using h1)
    have h6 := (QuotientGroup.eq_one_iff (N := N) _).mpr h5
    simp only [inv_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h6
    rw [mul_inv_eq_one] at h6
    exact h6
  have hrC : ∀ c ∈ Subgroup.centralizer ({(z : G ⧸ N)} : Set (G ⧸ N)), ¬ r ∣ orderOf c := by
    intro c hc hrc
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hcomm : (g : G ⧸ N) * (v : G ⧸ N) = (v : G ⧸ N) * (g : G ⧸ N) :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    exact hrQ g ((hcomm_iff g).mpr hcomm.symm)
      (hrc.trans (orderOf_map_dvd (QuotientGroup.mk' N) g))
  have hCO : ∀ x ∈ CFSG.oddCore (G ⧸ N), (z : G ⧸ N) * x = x * (z : G ⧸ N) → x = 1 := by
    intro x hx hxz
    obtain ⟨w, hwx, hwodd⟩ := exists_odd_order_lift hN2 (CFSG.Adapters.odd_orderOf_of_mem_oddCore hx)
    have hwv : w * v * w⁻¹ * v⁻¹ ∈ N := (hcomm_iff w).mpr (by rw [hwx]; exact hxz)
    have hwT : w ∈ normalizer ((T : Subgroup G) : Set G) := hQN w hwv
    have hcen : ∀ s ∈ (T : Subgroup G), w * s * w⁻¹ * s⁻¹ ∈ N := by
      intro s hs
      have haT : w * s * w⁻¹ * s⁻¹ ∈ (T : Subgroup G) := by
        have h1 : w * s * w⁻¹ ∈ (T : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hwT s).mp hs
        exact (T : Subgroup G).mul_mem h1 ((T : Subgroup G).inv_mem hs)
      have haO : ((w * s * w⁻¹ * s⁻¹ : G) : G ⧸ N) ∈ CFSG.oddCore (G ⧸ N) := by
        have e : ((w * s * w⁻¹ * s⁻¹ : G) : G ⧸ N) =
            x * ((s : G ⧸ N) * x⁻¹ * (s : G ⧸ N)⁻¹) := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwx]
          group
        rw [e]
        exact (CFSG.oddCore (G ⧸ N)).mul_mem hx
          ((CFSG.oddCore_normal (G ⧸ N)).conj_mem _ ((CFSG.oddCore (G ⧸ N)).inv_mem hx) _)
      have hodd_a := CFSG.Adapters.odd_orderOf_of_mem_oddCore haO
      have h2 : orderOf ((w * s * w⁻¹ * s⁻¹ : G) : G ⧸ N) ∣ orderOf (w * s * w⁻¹ * s⁻¹) :=
        orderOf_map_dvd (QuotientGroup.mk' N) _
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp T.isPGroup'
      have h3 : orderOf (w * s * w⁻¹ * s⁻¹) ∣ 2 ^ j := by
        rw [← hj]
        exact Subgroup.orderOf_dvd_natCard (T : Subgroup G) haT
      have h5 : orderOf ((w * s * w⁻¹ * s⁻¹ : G) : G ⧸ N) = 1 :=
        Nat.Coprime.eq_one_of_dvd
          (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd_a)).symm (h2.trans h3)
      exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h5)
    have hw1 := hodd w hwodd hwT hcen
    rw [← hwx, hw1, QuotientGroup.mk_one]
  obtain ⟨Rb, hRb⟩ := exists_normal_sylow_of_zStar Sb z hzZ hz hwc hr hrC hCO
  exact exists_sylow_normal_sup N Rb hRb

theorem mem_normalizer_iff_coe {X : Type*} [Group X] {M S : Subgroup X} {Q : Subgroup M}
    (hQ : ∀ s : M, s ∈ Q ↔ (s : X) ∈ S) (hSM : S ≤ M) (w : M) :
    w ∈ normalizer (Q : Set M) ↔ (w : X) ∈ normalizer (S : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ M
    · have := h ⟨x, hx⟩
      rw [hQ, hQ] at this
      exact this
    · constructor
      · intro hxS
        exact absurd (hSM hxS) hx
      · intro hxS
        refine absurd ?_ hx
        have h1 := hSM hxS
        have e : x = (w : X)⁻¹ * ((w : X) * x * (w : X)⁻¹) * (w : X) := by group
        rw [e]
        exact M.mul_mem (M.mul_mem (M.inv_mem w.2) h1) w.2
  · intro h y
    have := h y
    rw [hQ, hQ]
    exact this

theorem zstar14 : ZStar14Stmt := by
  intro X _ _ M V S u r hVM hVn hV2 hS hVS huS huV hu2 hSu hweak hQN hodd hr _ hrQ
  classical
  obtain ⟨Q, hQ⟩ := hS
  have hSM : S ≤ M := by
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have huM : u ∈ M := hSM huS
  have hQmem : ∀ s : M, s ∈ (Q : Subgroup M) ↔ (s : X) ∈ S := by
    intro s
    rw [← hQ, Subgroup.mem_map]
    exact ⟨fun h => ⟨s, h, rfl⟩, fun ⟨y, hy, hys⟩ => by rwa [Subtype.ext hys] at hy⟩
  let N : Subgroup M := V.subgroupOf M
  have hNn : N.Normal := ⟨fun a ha g => hVn g g.2 a ha⟩
  have hN2 : IsPGroup 2 N := hV2.comap_subtype
  have hNT : N ≤ (Q : Subgroup M) := fun n hn => (hQmem n).mpr (hVS hn)
  obtain ⟨R, hR⟩ := zstar14_abstract N hN2 Q hNT ⟨u, huM⟩ ((hQmem _).mpr huS) (fun h => huV h) hu2
    (fun s hs => hSu (s : X) ((hQmem s).mp hs))
    (fun g hg => hweak g g.2 ((hQmem _).mp hg))
    (fun g hg => (mem_normalizer_iff_coe hQmem hSM g).mpr (hQN g g.2 hg))
    (fun w hw hwN hcen => Subtype.ext (hodd w w.2 (by rwa [Subgroup.orderOf_coe])
      ((mem_normalizer_iff_coe hQmem hSM w).mp hwN) (fun s hs => hcen ⟨s, hSM hs⟩
        ((hQmem _).mpr hs))))
    hr (fun g hg => by rw [← Subgroup.orderOf_coe]; exact hrQ g g.2 hg)
  have hsup : ((R : Subgroup M) ⊔ N).map M.subtype = (R : Subgroup M).map M.subtype ⊔ V := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hVM]
  refine ⟨(R : Subgroup M).map M.subtype, ⟨R, rfl⟩, fun g hg x hx => ?_⟩
  rw [← hsup] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hR ⟨g, hg⟩ y hy, rfl⟩

end CFSG.GH74.Uniqueness
