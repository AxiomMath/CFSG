
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Q

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def d5Rho : Perm (Fin 5) := swap 1 2 * swap 3 4

theorem d5Rho_alt : d5Rho ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem d5Rho_sq : d5Rho * d5Rho = 1 := by
  decide +kernel

theorem d5Rho_ne_one : d5Rho ≠ 1 := by
  decide +kernel

theorem a0_d5Rho_cube : (a0 * d5Rho) ^ 3 = 1 := by
  decide +kernel

theorem a0_d5Rho_ne_one : a0 * d5Rho ≠ 1 := by
  decide +kernel

theorem a0_ne_one : a0 ≠ 1 := by
  decide +kernel

theorem a0_pow_five : a0 ^ 5 = 1 := by
  decide +kernel

theorem a0_fixed_zero : ∀ u : Fin 5 → ZMod 2, isEven u → pact a0 u = u → u = 0 := by
  decide +kernel

theorem d5Rho_tate : ∀ u : Fin 5 → ZMod 2, isEven u → pact d5Rho u = u →
    ∃ w : Fin 5 → ZMod 2, isEven w ∧ u = w + pact d5Rho w := by
  decide +kernel

theorem a0_d5Rho_fixed : ∃ u : Fin 5 → ZMod 2, isEven u ∧ u ≠ 0 ∧ pact (a0 * d5Rho) u = u := by
  decide +kernel

theorem zmod_two_self_add (t : ZMod 2) : t + t = 0 := by
  revert t
  decide

theorem zmod_two_four_terms (a b : ZMod 2) : a + (b + a) + b = 0 := by
  revert a b
  decide

@[expose] def d5Rho' : Alt5 := ⟨d5Rho, d5Rho_alt⟩

theorem closure_eq_top_of_orders {s t : Alt5} (hs : orderOf s = 5) (ht : orderOf t = 2)
    (hst : orderOf (s * t) = 3) : Subgroup.closure ({s, t} : Set Alt5) = ⊤ := by
  set N : Subgroup Alt5 := Subgroup.closure ({s, t} : Set Alt5) with hN
  have hsN : s ∈ N := Subgroup.subset_closure (by simp)
  have htN : t ∈ N := Subgroup.subset_closure (by simp)
  have hstN : s * t ∈ N := N.mul_mem hsN htN
  have d5 : 5 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hsN
    rwa [hs] at this
  have d2 : 2 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N htN
    rwa [ht] at this
  have d3 : 3 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hstN
    rwa [hst] at this
  have h30 : 30 ∣ Nat.card N := by omega
  have hdvd : Nat.card N ∣ 60 := by
    rw [← a5_card]
    exact Subgroup.card_subgroup_dvd_card N
  have hle : Nat.card N ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hcases : Nat.card N = 30 ∨ Nat.card N = 60 := by
    obtain ⟨k, hk⟩ := h30
    omega
  have hsimple : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
  rcases hcases with h | h
  · exfalso
    have hidx : N.index = 2 := by
      have := N.card_mul_index
      rw [a5_card, h] at this
      omega
    have hnorm : N.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · rw [h1] at h
      simp at h
    · rw [h1] at hidx
      simp at hidx
  · exact (Subgroup.card_eq_iff_eq_top N).mp (by rw [h, a5_card])

theorem closure_a0_d5Rho : Subgroup.closure ({a0', d5Rho'} : Set Alt5) = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine closure_eq_top_of_orders ?_ ?_ ?_
  · exact orderOf_eq_prime (Subtype.ext a0_pow_five) fun h => a0_ne_one (congrArg Subtype.val h)
  · exact orderOf_eq_prime (Subtype.ext d5Rho_sq) fun h => d5Rho_ne_one (congrArg Subtype.val h)
  · exact orderOf_eq_prime (Subtype.ext a0_d5Rho_cube)
      fun h => a0_d5Rho_ne_one (congrArg Subtype.val h)

theorem d5Core_config {G : Type} [Group G] {L : Subgroup G} (hD : D5Core L) :
    ∃ (V : Subgroup G) (x d : G), V ≤ L ∧ x ∈ L ∧ d ∈ L ∧ Nat.card V = 16 ∧
      (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧ (∀ a ∈ V, a * a = 1) ∧ orderOf x = 5 ∧ d * d = 1 ∧
      (∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧ (∀ v ∈ V, d * v * d⁻¹ ∈ V) ∧
      (∀ v ∈ V, x * v = v * x → v = 1) ∧ (x * d) ^ 3 ∈ V ∧
      (∃ v ∈ V, v ≠ 1 ∧ (x * d) * v = v * (x * d)) ∧
      (∀ y : G, x * y = y * x → d * y = y * d → (∀ v ∈ V, v * y = y * v) →
        ∀ l ∈ L, l * y = y * l) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨V, hVL, hV2, hLV, α, hα, hαV, β, hβ⟩ := hD
  have hconjV : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V := fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.1 (hLV hl) v).1 hv
  have hnorm : ∀ (l : ↥L) (v : ↥V), (l : G) * (v : G) * (l : G)⁻¹ ∈ V := fun l v =>
    hconjV l l.2 v v.2
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have h : β ⟨a, ha⟩ * β ⟨b, hb⟩ = β ⟨b, hb⟩ * β ⟨a, ha⟩ := mul_comm _ _
    have h' : (⟨a, ha⟩ : ↥V) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      β.injective (by rw [map_mul, map_mul]; exact h)
    exact congrArg Subtype.val h'
  have hVsq : ∀ a ∈ V, a * a = 1 := by
    intro a ha
    have h : β ⟨a, ha⟩ * β ⟨a, ha⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul]
      generalize Multiplicative.toAdd (β ⟨a, ha⟩) = u
      apply Subtype.ext
      funext i
      exact zmod_two_self_add (u.1 i)
    have h' : (⟨a, ha⟩ : ↥V) * ⟨a, ha⟩ = 1 := β.injective (by rw [map_mul, h, map_one])
    exact congrArg Subtype.val h'
  have hfixvec : ∀ (l : ↥L) (v : ↥V), (l : G) * v = v * l →
      vact ((α l : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β v)) =
        Multiplicative.toAdd (β v) := by
    intro l v h
    refine (hβ l v v ?_).symm
    show (v : G) = (l : G) * (v : G) * (l : G)⁻¹
    rw [h]
    group
  have hcommvec : ∀ (l : ↥L) (v : ↥V), vact ((α l : Alt5) : Perm (Fin 5))
      (Multiplicative.toAdd (β v)) = Multiplicative.toAdd (β v) → (l : G) * v = v * l := by
    intro l v h
    have h1 : β ⟨(l : G) * v * (l : G)⁻¹, hnorm l v⟩ = β v := by
      apply Multiplicative.toAdd.injective
      rw [hβ l v _ rfl, h]
    have h2 : (l : G) * v * (l : G)⁻¹ = v := congrArg Subtype.val (β.injective h1)
    rwa [mul_inv_eq_iff_eq_mul] at h2
  obtain ⟨l0, hl0⟩ := hα a0'
  have ha5 : a0' ^ 5 = 1 := Subtype.ext a0_pow_five
  have hl05 : l0 ^ 5 * l0 ^ 5 = 1 := by
    have h1 : α (l0 ^ 5) = 1 := by rw [map_pow, hl0, ha5]
    have h2 := hVsq _ ((hαV _).1 h1)
    exact Subtype.ext (by simpa using h2)
  have hl010 : l0 ^ 10 = 1 := by
    rw [show 10 = 5 + 5 from rfl, pow_add]
    exact hl05
  have hαx : α (l0 ^ 6) = a0' := by
    rw [map_pow, hl0, show 6 = 5 + 1 from rfl, pow_add, ha5, one_mul, pow_one]
  have hx5 : (l0 ^ 6) ^ 5 = 1 := by
    calc (l0 ^ 6) ^ 5 = (l0 ^ 10) ^ 3 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hl010, one_pow]
  have hx1 : l0 ^ 6 ≠ 1 := by
    intro h
    rw [h, map_one] at hαx
    exact a0_ne_one (congrArg Subtype.val hαx.symm)
  have hordx : orderOf ((l0 ^ 6 : ↥L) : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx5 hx1
  obtain ⟨d0, hd0⟩ := hα d5Rho'
  have hss : α (d0 * d0) = 1 := by
    rw [map_mul, hd0]
    exact Subtype.ext d5Rho_sq
  have hsV : ((d0 * d0 : ↥L) : G) ∈ V := (hαV _).1 hss
  have hsfix : vact d5Rho (Multiplicative.toAdd (β ⟨((d0 * d0 : ↥L) : G), hsV⟩)) =
      Multiplicative.toAdd (β ⟨((d0 * d0 : ↥L) : G), hsV⟩) := by
    have h := hfixvec d0 ⟨((d0 * d0 : ↥L) : G), hsV⟩ (by
      show (d0 : G) * ((d0 : G) * (d0 : G)) = ((d0 : G) * (d0 : G)) * (d0 : G)
      group)
    rw [hd0] at h
    exact h
  obtain ⟨w, hwe, hw⟩ := d5Rho_tate
    (Multiplicative.toAdd (β ⟨((d0 * d0 : ↥L) : G), hsV⟩)).1
    (Multiplicative.toAdd (β ⟨((d0 * d0 : ↥L) : G), hsV⟩)).2 (congrArg Subtype.val hsfix)
  set wE : ↥(evenWeight 5) := ⟨w, hwe⟩ with hwE
  set v' : ↥V := β.symm (Multiplicative.ofAdd wE) with hv'
  have hβv' : Multiplicative.toAdd (β v') = wE := by simp [hv']
  set c1 : ↥V := ⟨(d0 : G) * (v' : G) * (d0 : G)⁻¹, hnorm d0 v'⟩ with hc1
  have hβc1 : Multiplicative.toAdd (β c1) = vact d5Rho wE := by
    have h := hβ d0 v' c1 rfl
    rw [hd0, hβv'] at h
    exact h
  set sV : ↥V := ⟨((d0 * d0 : ↥L) : G), hsV⟩ with hsVdef
  have hβs : Multiplicative.toAdd (β sV) = wE + vact d5Rho wE := Subtype.ext hw
  have hdd : ((d0 : G) * v') * ((d0 : G) * v') = 1 := by
    have h1 : ((d0 : G) * v') * ((d0 : G) * v') = (c1 : G) * (sV : G) * (v' : G) := by
      show ((d0 : G) * v') * ((d0 : G) * v') =
        ((d0 : G) * (v' : G) * (d0 : G)⁻¹) * ((d0 : G) * (d0 : G)) * (v' : G)
      group
    have h2 : c1 * sV * v' = 1 := by
      apply β.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul β (c1 * sV) v', map_mul β c1 sV, toAdd_mul, toAdd_mul, hβc1, hβs, hβv',
        map_one]
      apply Subtype.ext
      funext i
      exact zmod_two_four_terms _ _
    rw [h1]
    exact congrArg Subtype.val h2
  have hdL : (d0 : G) * (v' : G) ∈ L := L.mul_mem d0.2 (hVL v'.2)
  have hαd : α ⟨(d0 : G) * (v' : G), hdL⟩ = d5Rho' := by
    have h1 : (⟨(d0 : G) * (v' : G), hdL⟩ : ↥L) = d0 * ⟨(v' : G), hVL v'.2⟩ := rfl
    rw [h1, map_mul, hd0, (hαV ⟨(v' : G), hVL v'.2⟩).2 v'.2, mul_one]
  have h3 : α ((l0 ^ 6 * ⟨(d0 : G) * (v' : G), hdL⟩) ^ 3) = 1 := by
    rw [map_pow, map_mul, hαx, hαd]
    exact Subtype.ext a0_d5Rho_cube
  have hxd3 : (((l0 ^ 6 : ↥L) : G) * ((d0 : G) * (v' : G))) ^ 3 ∈ V := by
    have := (hαV _).1 h3
    simpa using this
  obtain ⟨u, hue, hu0, huf⟩ := a0_d5Rho_fixed
  set uE : ↥(evenWeight 5) := ⟨u, hue⟩ with huE
  set vv : ↥V := β.symm (Multiplicative.ofAdd uE) with hvv
  have hβvv : Multiplicative.toAdd (β vv) = uE := by simp [hvv]
  have hvv1 : (vv : G) ≠ 1 := by
    intro h
    have h' : vv = 1 := Subtype.ext h
    rw [h', map_one] at hβvv
    exact hu0 (congrArg Subtype.val hβvv.symm)
  have hxdvv : ((l0 ^ 6 * ⟨(d0 : G) * (v' : G), hdL⟩ : ↥L) : G) * vv =
      vv * ((l0 ^ 6 * ⟨(d0 : G) * (v' : G), hdL⟩ : ↥L) : G) := by
    apply hcommvec
    rw [map_mul, hαx, hαd, hβvv]
    exact Subtype.ext huf
  refine ⟨V, ((l0 ^ 6 : ↥L) : G), (d0 : G) * (v' : G), hVL, (l0 ^ 6).2, hdL, card_V β, hVcomm,
    hVsq, hordx, hdd, fun v hv => hconjV _ (l0 ^ 6).2 v hv,
    fun v hv => hconjV _ hdL v hv, ?_, hxd3, ⟨vv, vv.2, hvv1, hxdvv⟩, ?_⟩
  · intro v hv hcomm
    have h1 := hfixvec (l0 ^ 6) ⟨v, hv⟩ hcomm
    rw [hαx] at h1
    have h2 : (Multiplicative.toAdd (β ⟨v, hv⟩)).1 = 0 :=
      a0_fixed_zero _ ((mem_evenWeight_iff _).1 (Multiplicative.toAdd (β ⟨v, hv⟩)).2)
        (congrArg Subtype.val h1)
    have h3 : β ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective (Subtype.ext h2)
    have h4 : (⟨v, hv⟩ : ↥V) = 1 := β.injective (by rw [h3, map_one])
    exact congrArg Subtype.val h4
  · intro y hxy hdy hVy l hl
    set S : Subgroup ↥L := (Subgroup.centralizer ({y} : Set G)).subgroupOf L with hS
    have hmemS : ∀ m : ↥L, m ∈ S ↔ y * (m : G) = (m : G) * y := by
      intro m
      rw [hS, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      simp
    have hxS : l0 ^ 6 ∈ S := (hmemS _).2 hxy.symm
    have hdS : (⟨(d0 : G) * (v' : G), hdL⟩ : ↥L) ∈ S := (hmemS _).2 hdy.symm
    have hmap : S.map α = ⊤ := by
      rw [eq_top_iff, ← closure_a0_d5Rho, Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨l0 ^ 6, hxS, hαx⟩
      · exact ⟨⟨(d0 : G) * (v' : G), hdL⟩, hdS, hαd⟩
    obtain ⟨s, hsS, hsl⟩ := Subgroup.mem_map.1 (show α ⟨l, hl⟩ ∈ S.map α by rw [hmap]; trivial)
    have hker : α (s⁻¹ * ⟨l, hl⟩) = 1 := by
      rw [map_mul, map_inv, hsl, inv_mul_cancel]
    have hVmem : ((s⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ V := (hαV _).1 hker
    have hkS : s⁻¹ * ⟨l, hl⟩ ∈ S := (hmemS _).2 (hVy _ hVmem).symm
    have hlS : (⟨l, hl⟩ : ↥L) ∈ S := by
      have := S.mul_mem hsS hkS
      rwa [mul_inv_cancel_left] at this
    exact ((hmemS _).1 hlS).symm

end CFSG.QuasithinUnique.A5
