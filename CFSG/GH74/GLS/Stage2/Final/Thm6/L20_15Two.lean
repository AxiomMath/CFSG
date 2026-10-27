module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Core
public import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass
public import CFSG.GH74.Uniqueness.SU.SU1MaxClassShape
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup

variable {G : Type} [Group G]

section Q4

variable {z y : G}

theorem zyz_eq (hz2 : z * z = 1) (hzy : z * y = y * z) : z * (y * z) = y := by
  calc z * (y * z) = (z * y) * z := by group
    _ = (y * z) * z := by rw [hzy]
    _ = y * (z * z) := by group
    _ = y := by rw [hz2]; group

theorem yzy_eq (hy2 : y * y = 1) (hzy : z * y = y * z) : (y * z) * y = z := by
  calc (y * z) * y = y * (z * y) := by group
    _ = y * (y * z) := by rw [hzy]
    _ = (y * y) * z := by group
    _ = z := by rw [hy2]; group

theorem yzyz_eq (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) : (y * z) * (y * z) = 1 := by
  calc (y * z) * (y * z) = y * (z * (y * z)) := by group
    _ = y * y := by rw [zyz_eq hz2 hzy]
    _ = 1 := hy2

theorem yzz_eq (hz2 : z * z = 1) : (y * z) * z = y := by
  calc (y * z) * z = y * (z * z) := by group
    _ = y := by rw [hz2]; group

theorem yyz_eq (hy2 : y * y = 1) : y * (y * z) = z := by
  calc y * (y * z) = (y * y) * z := by group
    _ = z := by rw [hy2]; group

@[expose] def Q4 (z y : G) (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) : Subgroup G where
  carrier := {x | x = 1 ∨ x = z ∨ x = y ∨ x = y * z}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; simp
    · right; left; simp
    · left; exact hz2
    · right; right; right; exact hzy
    · right; right; left; exact zyz_eq hz2 hzy
    · right; right; left; simp
    · right; right; right; rfl
    · left; exact hy2
    · right; left; exact yyz_eq hy2
    · right; right; right; simp
    · right; right; left; exact yzz_eq hz2
    · right; left; exact yzy_eq hy2 hzy
    · left; exact yzyz_eq hz2 hy2 hzy
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl)
    · left; simp
    · right; left; exact inv_eq_of_mul_eq_one_right hz2
    · right; right; left; exact inv_eq_of_mul_eq_one_right hy2
    · right; right; right; exact inv_eq_of_mul_eq_one_right (yzyz_eq hz2 hy2 hzy)

theorem mem_Q4 (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) {x : G} :
    x ∈ Q4 z y hz2 hy2 hzy ↔ x = 1 ∨ x = z ∨ x = y ∨ x = y * z := Iff.rfl

end Q4

theorem card_le_four_of_subset [Finite G] {P : Subgroup G} {z y : G}
    (h : ∀ x ∈ P, x = 1 ∨ x = z ∨ x = y ∨ x = y * z) : Nat.card P ≤ 4 := by
  classical
  have hsub : (P : Set G) ⊆ (({1, z, y, y * z} : Finset G) : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact h x hx
  calc Nat.card P = (P : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ (({1, z, y, y * z} : Finset G) : Set G).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({1, z, y, y * z} : Finset G).card := Set.ncard_coe_finset _
    _ ≤ 4 := Finset.card_le_four

section Central

variable [Finite G]

theorem exists_central_involution {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : 1 < Nat.card P) :
    ∃ w ∈ P, (∀ v ∈ P, v * w = w * v) ∧ w * w = 1 ∧ w ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hP1
  have : Nontrivial (center P) := hP.center_nontrivial
  have hZ : IsPGroup 2 (center P) := hP.to_subgroup _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : Nat.card (center P) = 1 := by rw [hk]; simp
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' this
  have h2 : 2 ∣ Nat.card (center P) := by rw [hk]; exact dvd_pow_self 2 hk0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 h2
  refine ⟨((c : P) : G), (c : P).2, fun v hv => ?_, ?_, ?_⟩
  · have := Subgroup.mem_center_iff.mp c.2 ⟨v, hv⟩
    exact congrArg Subtype.val this
  · have h := pow_orderOf_eq_one c
    rw [hc, sq] at h
    exact congrArg (fun t : center P => (((t : P)) : G)) h
  · intro h1
    have : c = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)


theorem central_unique {P : Subgroup G} (hP : IsPGroup 2 P) {z y : G} (hzP : z ∈ P) (hyP : y ∈ P)
    (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) (hne : z ≠ y) (hz1 : z ≠ 1)
    (hC : ∀ x ∈ P, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z)
    (hconj : ¬ IsConj z (y * z)) (h4 : 4 < Nat.card P) :
    ∀ w ∈ P, (∀ v ∈ P, v * w = w * v) → w * w = 1 → w ≠ 1 → w = y * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro w hwP hwc hw2 hw1
  rcases hC w hwP (hwc z hzP) with h | h | h | h
  · exact absurd h hw1
  · exfalso
    rw [h] at hwc
    have hall : ∀ x ∈ P, x = 1 ∨ x = z ∨ x = y ∨ x = y * z :=
      fun x hx => hC x hx (hwc x hx).symm
    have := card_le_four_of_subset hall
    omega
  · exfalso
    rw [h] at hwc
    set Q := Q4 z y hz2 hy2 hzy with hQ
    have hQP : Q ≤ P := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact P.one_mem
      · exact hzP
      · exact hyP
      · exact P.mul_mem hyP hzP
    have hQ4 : Nat.card Q ≤ 4 := card_le_four_of_subset (P := Q) (z := z) (y := y) fun x hx => hx
    have hex : ∃ x ∈ P, x ∈ normalizer (Q : Set G) ∧ x ∉ Q := by
      by_contra hno
      have hno' : ∀ x ∈ P, x ∈ normalizer (Q : Set G) → x ∈ Q := by
        intro x hx hxn
        by_contra hxQ
        exact hno ⟨x, hx, hxn, hxQ⟩
      have hQeq := eq_of_normalizer_eq_pGroup 2 hP hQP hno'
      rw [hQeq] at hQ4
      omega
    obtain ⟨x, hxP, hxN, hxQ⟩ := hex
    have hzQ : z ∈ Q := Or.inr (Or.inl rfl)
    have hxz : x * z * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzQ
    rcases hxz with h1 | h1 | h1 | h1
    · apply hz1
      have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
      rw [this, h1]; group
    · apply hxQ
      have hxc : z * x = x * z := by
        calc z * x = (x * z * x⁻¹) * x := by rw [h1]
          _ = x * z := by group
      rcases hC x hxP hxc with h2 | h2 | h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h2))
    · apply hne
      have h3 := hwc x hxP
      have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
      rw [this, h1]
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
        _ = x⁻¹ * (x * y) := by rw [← h3]
        _ = y := by group
    · exact hconj (isConj_iff.mpr ⟨x, h1⟩)
  · exact h

end Central


section Cyclic

variable [Finite G]

theorem card_cen_le_four {P : Subgroup G} {z y : G} (hzP : z ∈ P)
    (hC : ∀ x ∈ P, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z) :
    Nat.card (centralizer ({(⟨z, hzP⟩ : ↥P)} : Set ↥P)) ≤ 2 ^ 2 := by
  set T : Subgroup ↥P := centralizer ({(⟨z, hzP⟩ : ↥P)} : Set ↥P) with hT
  have h1 : Nat.card (T.map P.subtype) = Nat.card T := Subgroup.card_map_of_injective P.subtype_injective
  have h2 : Nat.card (T.map P.subtype) ≤ 4 := by
    refine card_le_four_of_subset (z := z) (y := y) ?_
    rintro _ ⟨v, hv, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hv
    have := congrArg Subtype.val hcomm
    exact hC v v.2 (by simpa using this.symm)
  rw [← h1]
  simpa using h2

theorem nilpotencyClass_of_lcs {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P) {m : ℕ} (hm : 3 ≤ m)
    (h : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥) : m - 1 ≤ Group.nilpotencyClass P := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  by_contra hcon
  apply h
  rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  omega

theorem exists_cyclic_relIndex_le_two {P : Subgroup G} (hP : IsPGroup 2 P) {z y : G} (hzP : z ∈ P)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hC : ∀ x ∈ P, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z) :
    ∃ M : Subgroup G, M ≤ P ∧ IsCyclic M ∧ M.relIndex P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h4 : Nat.card P ≤ 4
  · refine ⟨zpowers z, (Subgroup.zpowers_le).mpr hzP, inferInstance, ?_⟩
    have hle : zpowers z ≤ P := (Subgroup.zpowers_le).mpr hzP
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    have hcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
    have h1 := Subgroup.card_mul_index ((zpowers z).subgroupOf P)
    have h2 : Nat.card ((zpowers z).subgroupOf P) = Nat.card (zpowers z) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [h2, hcard] at h1
    have : (zpowers z).relIndex P = ((zpowers z).subgroupOf P).index := rfl
    omega
  · push Not at h4
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    have hk3 : 3 ≤ k := by
      by_contra hcon
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h8 : 2 ^ 3 ≤ Nat.card P := by
      rw [hk]; exact Nat.pow_le_pow_right (by norm_num) hk3
    obtain ⟨m, hm, hγ⟩ := CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer 2 Nat.prime_two
      ↥P hP h8 ⟨z, hzP⟩ (card_cen_le_four hzP hC)
    have hm3 : 3 ≤ m := by
      have : 2 ^ k = 2 ^ m := by rw [← hk, hm]
      have := Nat.pow_right_injective (le_refl 2) this
      omega
    have hcl := nilpotencyClass_of_lcs hP hm3 hγ
    obtain ⟨M, hMi, hMc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_cyclic_index_two m hm3 ↥P hm hcl
    refine ⟨M.map P.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · have := hMc
      exact isCyclic_of_surjective (Subgroup.equivMapOfInjective M P.subtype P.subtype_injective)
        (Subgroup.equivMapOfInjective M P.subtype P.subtype_injective).surjective
    · have : (M.map P.subtype).subgroupOf P = M :=
        Subgroup.comap_map_eq_self_of_injective P.subtype_injective M
      show ((M.map P.subtype).subgroupOf P).index ≤ 2
      rw [this, hMi]

theorem exists_involution_of_ne_bot {K : Subgroup G} (hK : IsPGroup 2 K) (hne : K ≠ ⊥) :
    ∃ w ∈ K, w * w = 1 ∧ w ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  have h2 : 2 ∣ Nat.card K := by rw [hk]; exact dvd_pow_self 2 hk0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  refine ⟨(c : G), c.2, ?_, ?_⟩
  · have h := pow_orderOf_eq_one c
    rw [hc, sq] at h
    exact congrArg Subtype.val h
  · intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)

theorem exists_central_involution_of_normal {V N : Subgroup G} (hVp : IsPGroup 2 V) (hNV : N ≤ V)
    (hN : ∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ ∈ N) (hN1 : N ≠ ⊥) :
    ∃ w ∈ N, (∀ v ∈ V, v * w = w * v) ∧ w * w = 1 ∧ w ≠ 1 := by
  have hnil : Group.IsNilpotent ↥V := hVp.isNilpotent
  have hN''n : (N.subgroupOf V).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN g g.2 n hn⟩
  have hN''ne : N.subgroupOf V ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNV hx⟩ : V) ∈ N.subgroupOf V := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hK := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥V) (H := N.subgroupOf V) hN''ne
  set K : Subgroup G := (N.subgroupOf V ⊓ center ↥V).map V.subtype with hKdef
  have hKp : IsPGroup 2 K := hVp.to_le (Subgroup.map_subtype_le _)
  have hKne : K ≠ ⊥ := by
    intro hbot
    apply hK
    rw [hKdef] at hbot
    exact Subgroup.map_injective V.subtype_injective (hbot.trans (Subgroup.map_bot _).symm)
  obtain ⟨w, hwK, hw2, hw1⟩ := exists_involution_of_ne_bot hKp hKne
  obtain ⟨w', ⟨hw'N, hw'c⟩, rfl⟩ := hwK
  refine ⟨(w' : G), hw'N, fun v hv => ?_, hw2, hw1⟩
  have := Subgroup.mem_center_iff.mp hw'c ⟨v, hv⟩
  exact congrArg Subtype.val this

omit [Finite G] in
theorem isCyclic_inf_left {M P : Subgroup G} (hM : IsCyclic M) : IsCyclic ↥(M ⊓ P) := by
  have h1 : IsCyclic ↥((M ⊓ P).subgroupOf M) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ P ≤ M))
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ P ≤ M)).surjective

end Cyclic


section Abstract

variable {P : Type} [Group P]

theorem eq_of_sq_eq_one_of_mem_zpowers [Finite P] {a s t : P} (hs : s ∈ zpowers a) (ht : t ∈ zpowers a)
    (hs2 : s * s = 1) (ht2 : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1) : s = t := by
  classical
  by_contra hst
  let _ : Fintype (zpowers a) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := zpowers a) (n := 2) (by norm_num)
  have hsub : ({1, ⟨s, hs⟩, ⟨t, ht⟩} : Finset (zpowers a)) ⊆ Finset.univ.filter (fun x : zpowers a => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · exact Subtype.ext (by simpa [sq] using hs2)
    · exact Subtype.ext (by simpa [sq] using ht2)
  have h3 : ({1, ⟨s, hs⟩, ⟨t, ht⟩} : Finset (zpowers a)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      intro h
      exact hst (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hs1 ?_, fun h => ht1 ?_⟩
      · exact (congrArg Subtype.val h).symm
      · exact (congrArg Subtype.val h).symm
  have := Finset.card_le_card hsub
  omega

theorem inv_mul_mem_of_index_two' {M : Subgroup P} (hM : M.index = 2) {x z : P} (hx : x ∉ M) (hz : z ∉ M) :
    z⁻¹ * x ∈ M := by
  rw [Subgroup.mul_mem_iff_of_index_two hM, inv_mem_iff]
  exact iff_of_false hz hx

theorem conj_eq_of_not_mem {a z x : P} (hM : (zpowers a).index = 2) (hz : z ∉ zpowers a) (hx : x ∉ zpowers a) :
    x * a * x⁻¹ = z * a * z⁻¹ := by
  have hb := inv_mul_mem_of_index_two' hM hx hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hx' : x = z * a ^ k := by
    rw [hk]; group
  have hcomm : Commute (a ^ k) a := (Commute.refl a).zpow_left k
  rw [hx']
  calc z * a ^ k * a * (z * a ^ k)⁻¹ = z * (a ^ k * a * (a ^ k)⁻¹) * z⁻¹ := by group
    _ = z * a * z⁻¹ := by rw [hcomm.eq]; group

theorem sq_mem_of_cover {R : Subgroup P} {z : P} (hz2 : z * z = 1) (hcov : ∀ x : P, x ∈ R ∨ x * z ∈ R)
    (hRn : ∀ q : P, ∀ r ∈ R, q * r * q⁻¹ ∈ R) (x : P) : x * x ∈ R := by
  rcases hcov x with h | h
  · exact R.mul_mem h h
  · have h2 := hRn z _ h
    have e : x * x = (x * z) * (z * (x * z) * z⁻¹) := by
      calc x * x = (x * (z * z)) * x := by rw [hz2]; group
        _ = (x * z) * (z * (x * z) * z⁻¹) := by
          have : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          rw [this]
          calc x * (z * z) * x = x * z * (z * x) := by group
            _ = x * z * (z * (x * z) * z) := by
              congr 1
              calc z * x = z * x * (z * z) := by rw [hz2]; group
                _ = z * (x * z) * z := by group
    rw [e]
    exact R.mul_mem h h2

theorem sd_unique_involution [Finite P] {n : ℕ} (hn : 4 ≤ n) {a z : P}
    (ha : orderOf a = 2 ^ (n - 1)) (hM : (zpowers a).index = 2) (hz2 : z * z = 1)
    (hza : z * a * z⁻¹ = a ^ (2 ^ (n - 2) - 1))
    {R : Subgroup P} (hcov : ∀ x : P, x ∈ R ∨ x * z ∈ R) (hRn : ∀ q : P, ∀ r ∈ R, q * r * q⁻¹ ∈ R)
    (hzR : z ∉ R) {u : P} (hu2 : u * u = 1) (hu1 : u ≠ 1) (huc : ∀ v : P, v * u = u * v) :
    ∀ s ∈ R, s ≠ 1 → s * s = 1 → s = u := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have h2n : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
  have h4 : 4 ≤ 2 ^ (n - 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnc : z * a * z⁻¹ ≠ a := by
    intro h
    rw [hza] at h
    have h' : a ^ (2 ^ (n - 2) - 1) = a ^ 1 := by rw [pow_one]; exact h
    have := pow_inj_mod.mp h'
    rw [ha] at this
    have hlt : 2 ^ (n - 2) - 1 < 2 ^ (n - 1) := by omega
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (n - 1))] at this
    omega
  have hz : z ∉ zpowers a := by
    intro hzm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzm
    have hcomm : Commute z a := by
      rw [← hk]; exact (Commute.refl a).zpow_left k
    apply hnc
    calc z * a * z⁻¹ = a * z * z⁻¹ := by rw [hcomm.eq]
      _ = a := by group
  have hu : u ∈ zpowers a := by
    by_contra hu
    have := conj_eq_of_not_mem hM hz hu
    have hc : u * a * u⁻¹ = a := by
      have := huc a
      calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [← this]
        _ = a := by group
    exact hnc (this ▸ hc)
  intro s hsR hs1 hs2
  by_cases hs : s ∈ zpowers a
  · exact eq_of_sq_eq_one_of_mem_zpowers hs hu hs2 hu2 hs1 hu1
  · exfalso
    set c := z⁻¹ * s with hc
    have hcM : c ∈ zpowers a := inv_mul_mem_of_index_two' hM hs hz
    obtain ⟨i, hi⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_pow_eq_of_mem_zpowers hcM
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have h1 : z * c * z⁻¹ = c⁻¹ := by
      rw [hc, mul_inv_rev, inv_inv, hsinv, hzi]
      calc z * (z * s) * z = (z * z) * s * z := by group
        _ = s * z := by rw [hz2]; group
    have h2 : z * c * z⁻¹ = c ^ (2 ^ (n - 2) - 1) := by
      rw [← hi, ← conj_pow, hza, ← pow_mul, ← pow_mul, mul_comm]
    have h3 : c ^ (2 ^ (n - 2)) = 1 := by
      have h4' : c⁻¹ = c ^ (2 ^ (n - 2) - 1) := h1.symm.trans h2
      have : c * c ^ (2 ^ (n - 2) - 1) = 1 := by rw [← h4']; group
      calc c ^ (2 ^ (n - 2)) = c * c ^ (2 ^ (n - 2) - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ = 1 := this
    have hci : a ^ (i * 2 ^ (n - 2)) = 1 := by
      rw [← hi, ← pow_mul] at h3
      exact h3
    have hdvd : 2 ^ (n - 1) ∣ i * 2 ^ (n - 2) := by
      rw [← ha]; exact orderOf_dvd_of_pow_eq_one hci
    rw [h2n] at hdvd
    have h2i : 2 ∣ i := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < 2 ^ (n - 2)) hdvd
    obtain ⟨j, hj⟩ := h2i
    have hcR : c ∈ R := by
      have : c = a ^ j * a ^ j := by rw [← hi, hj, ← pow_add]; congr 1; omega
      rw [this]
      exact sq_mem_of_cover hz2 hcov hRn (a ^ j)
    apply hzR
    have e : z = s * c⁻¹ := by
      rw [hc]; group
    rw [e]
    exact R.mul_mem hsR (R.inv_mem hcR)

theorem exists_gen_cyclic_index_two [Finite P] {m : ℕ} (hm : 3 ≤ m) (hP : Nat.card P = 2 ^ m)
    (hcl : m - 1 ≤ Group.nilpotencyClass P) : ∃ a : P, orderOf a = 2 ^ (m - 1) ∧ (zpowers a).index = 2 := by
  obtain ⟨M, hMidx, hMcyc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_cyclic_index_two m hm P hP hcl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
  set a : P := (g : P) with ha_def
  have hzM : zpowers a = M := by
    refine le_antisymm (Subgroup.zpowers_le.mpr g.2) (fun x hx => ?_)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hMcard : Nat.card M = 2 ^ (m - 1) := by
    have h1 := Subgroup.card_mul_index M
    rw [hMidx, hP] at h1
    have : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_right two_pos h1
  refine ⟨a, ?_, hzM ▸ hMidx⟩
  rw [← hMcard, ha_def, Subgroup.orderOf_coe]
  exact orderOf_eq_card_of_forall_mem_zpowers hg



theorem conj_cases_four [Finite P] {a y : P} (ha : orderOf a = 4) (hM : (zpowers a).index = 2) :
    y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a⁻¹ := by
  obtain ⟨r, hr⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_conj_pow y hM
  have ha4 : a ^ 4 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hr' : y * a * y⁻¹ = a ^ (r % 4) := by rw [hr, pow_eq_pow_mod r ha4]
  have hrlt : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hord : orderOf (y * a * y⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) a
    simpa [ha] using this
  rw [hr'] at hord ⊢
  interval_cases hrr : r % 4
  · rw [pow_zero, orderOf_one] at hord
    omega
  · left; rw [pow_one]
  · exfalso
    have h2 : orderOf (a ^ 2) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]; exact ha4
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · right
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]; exact ha4

end Abstract


section Dihedral

variable [Finite G]

omit [Finite G] in
theorem card_Q4 {z y : G} (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) (hz1 : z ≠ 1)
    (hy1 : y ≠ 1) (hne : z ≠ y) : Nat.card (Q4 z y hz2 hy2 hzy) = 4 := by
  classical
  have hset : ((Q4 z y hz2 hy2 hzy : Subgroup G) : Set G) = (({1, z, y, y * z} : Finset G) : Set G) := by
    ext x
    simp only [SetLike.mem_coe, mem_Q4, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have hyz1 : y * z ≠ 1 := by
    intro h
    apply hne
    have : y = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]; exact (inv_eq_of_mul_eq_one_right hz2).symm ▸ rfl
  have n3 : y ∉ ({y * z} : Finset G) := by
    simp only [Finset.mem_singleton]
    intro h
    apply hz1
    calc z = y⁻¹ * (y * z) := by group
      _ = y⁻¹ * y := by rw [← h]
      _ = 1 := by group
  have n2 : z ∉ ({y, y * z} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => hne h, fun h => hy1 ?_⟩
    calc y = z⁻¹ * (z * y) := by group
      _ = z⁻¹ * (y * z) := by rw [hzy]
      _ = z⁻¹ * z := by rw [← h]
      _ = 1 := by group
  have n1 : (1 : G) ∉ ({z, y, y * z} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hz1 h.symm, fun h => hy1 h.symm, fun h => hyz1 h.symm⟩
  have hcard : ({1, z, y, y * z} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n3,
      Finset.card_singleton]
  calc Nat.card (Q4 z y hz2 hy2 hzy) = ((Q4 z y hz2 hy2 hzy : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ = (({1, z, y, y * z} : Finset G) : Set G).ncard := by rw [hset]
    _ = ({1, z, y, y * z} : Finset G).card := Set.ncard_coe_finset _
    _ = 4 := hcard


theorem dihedral_of_card_le_four {Q : Subgroup G} {z y : G} (hzQ : z ∈ Q) (hyQ : y ∈ Q)
    (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) (hne : z ≠ y) (hz1 : z ≠ 1) (hy1 : y ≠ 1)
    (h4 : Nat.card Q ≤ 4) : Nonempty (↥Q ≃* DihedralGroup 2) := by
  have hQ4le : Q4 z y hz2 hy2 hzy ≤ Q := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact Q.one_mem
    · exact hzQ
    · exact hyQ
    · exact Q.mul_mem hyQ hzQ
  have hcard := card_Q4 hz2 hy2 hzy hz1 hy1 hne
  have heq : Q4 z y hz2 hy2 hzy = Q := Subgroup.eq_of_le_of_card_ge hQ4le (by omega)
  have hmem : ∀ x ∈ Q, x = 1 ∨ x = z ∨ x = y ∨ x = y * z := by
    intro x hx
    rw [← heq] at hx
    exact hx
  set ρ : ↥Q := ⟨y, hyQ⟩ with hρ
  set σ : ↥Q := ⟨z, hzQ⟩ with hσ
  have hρ2 : ρ * ρ = 1 := Subtype.ext hy2
  have hσ2 : σ * σ = 1 := Subtype.ext hz2
  have hρσ : σ * ρ = ρ * σ := Subtype.ext hzy
  have hρ1 : ρ ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hord : orderOf ρ = 2 := orderOf_eq_prime (by rw [sq]; exact hρ2) hρ1
  have hgen : (⊤ : Subgroup ↥Q) = zpowers ρ ⊔ zpowers σ := by
    rw [eq_comm, eq_top_iff]
    intro x _
    rcases hmem x x.2 with h | h | h | h
    · have : x = 1 := Subtype.ext h
      rw [this]; exact Subgroup.one_mem _
    · have : x = σ := Subtype.ext h
      rw [this]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
    · have : x = ρ := Subtype.ext h
      rw [this]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ)
    · have : x = ρ * σ := Subtype.ext h
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    have : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
    rw [this, hρσ]; group
  have hσρ : σ ∉ zpowers ρ := by
    intro hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hρk : ρ ^ k = ρ ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
      rw [zpow_add, zpow_mul, show ρ ^ (2 : ℤ) = 1 by rw [zpow_two]; exact hρ2, one_zpow, mul_one]
    rw [hρk] at hk
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h] at hk
      exact hz1 (congrArg Subtype.val (by simpa using hk.symm))
    · rw [h] at hk
      exact hne (congrArg Subtype.val (by simpa using hk.symm))
  have := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen (by rw [sq]; exact hσ2) hrel hσρ
  rwa [hord] at this


theorem dihedral_of_card_gt_four {Q : Subgroup G} (hQ : IsPGroup 2 Q) {z y : G} (hzQ : z ∈ Q) (hyQ : y ∈ Q)
    (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) (hne : z ≠ y) (hz1 : z ≠ 1)
    (hC : ∀ x ∈ Q, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z) (hconj : ¬ IsConj z (y * z))
    (h4 : 4 < Nat.card Q) {R : Subgroup G} (hRQ : R ≤ Q) (hcov : ∀ x ∈ Q, x ∈ R ∨ x * z ∈ R)
    (hRn : ∀ q ∈ Q, ∀ r ∈ R, q * r * q⁻¹ ∈ R) (hzR : z ∉ R)
    (hno : (∀ s ∈ R, s ≠ 1 → s * s = 1 → s = y * z) → False) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥Q ≃* DihedralGroup (2 ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hk3 : 3 ≤ k := by
    by_contra hcon
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 2 ^ 3 ≤ Nat.card Q := by rw [hk]; exact Nat.pow_le_pow_right (by norm_num) hk3
  obtain ⟨m, hm, hγ⟩ := CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer 2 Nat.prime_two
    ↥Q hQ h8 ⟨z, hzQ⟩ (card_cen_le_four hzQ hC)
  have hm3 : 3 ≤ m := by
    have : 2 ^ k = 2 ^ m := by rw [← hk, hm]
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  have hcl := nilpotencyClass_of_lcs hQ hm3 hγ
  obtain ⟨a, ha, hM⟩ := exists_gen_cyclic_index_two hm3 hm hcl
  set z' : ↥Q := ⟨z, hzQ⟩ with hz'
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hsq1 : ∀ x : ↥Q, z' * x = x * z' → x * x = 1 := by
    intro x hx
    have hx' : z * (x : G) = (x : G) * z := congrArg Subtype.val hx
    apply Subtype.ext
    show (x : G) * (x : G) = 1
    rcases hC x x.2 hx' with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact hz2
    · rw [h]; exact hy2
    · rw [h]; exact yzyz_eq hz2 hy2 hzy
  have ha1 : a ^ (2 ^ (m - 1)) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hordge : 4 ≤ 2 ^ (m - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnc : z' * a * z'⁻¹ ≠ a := by
    intro h
    have hc : z' * a = a * z' := by
      calc z' * a = (z' * a * z'⁻¹) * z' := by group
        _ = a * z' := by rw [h]
    have := hsq1 a hc
    have hd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact this)
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hdih : z' * a * z'⁻¹ = a⁻¹ → ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥Q ≃* DihedralGroup (2 ^ m)) := by
    intro hrel
    have hn : (zpowers a).Normal := Subgroup.normal_of_index_eq_two hM
    have hz'a : z' ∉ zpowers a := by
      intro hz
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hcomm : Commute z' a := by
        rw [← hj]; exact (Commute.refl a).zpow_left j
      apply hnc
      calc z' * a * z'⁻¹ = a * z' * z'⁻¹ := by rw [hcomm.eq]
        _ = a := by group
    have hgen : (⊤ : Subgroup ↥Q) = zpowers a ⊔ zpowers z' := by
      rw [eq_comm, eq_top_iff]
      intro x _
      by_cases hx : x ∈ zpowers a
      · exact Subgroup.mem_sup_left hx
      · have h1 := inv_mul_mem_of_index_two' hM hx hz'a
        have : x = z' * (z'⁻¹ * x) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers z'))
          (Subgroup.mem_sup_left h1)
    have := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem a z' hgen (by rw [sq]; exact hz'2) hrel hz'a
    rw [ha] at this
    exact ⟨m - 1, by omega, this⟩
  by_cases hm4 : m = 3
  · subst hm4
    have ha4 : orderOf a = 4 := by rw [ha]; norm_num
    rcases conj_cases_four (y := z') ha4 hM with h | h
    · exact absurd h hnc
    · exact hdih h
  · have hm4' : 4 ≤ m := by omega
    rcases CFSG.GH74.Uniqueness.SU.SU1.conj_exponent_cases hm4' ha hM z' with h | h | h | h
    · exact absurd h hnc
    · exfalso
      have hc2 : z' * a ^ 2 * z'⁻¹ = a ^ 2 := by
        have h2m : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by rw [← pow_succ']; congr 1; omega
        have e : (2 ^ (m - 2) + 1) * 2 = 2 ^ (m - 1) + 2 := by omega
        rw [← conj_pow, h, ← pow_mul, e, pow_add, ha1, one_mul]
      have hc : z' * a ^ 2 = a ^ 2 * z' := by
        calc z' * a ^ 2 = (z' * a ^ 2 * z'⁻¹) * z' := by group
          _ = a ^ 2 * z' := by rw [hc2]
      have := hsq1 (a ^ 2) hc
      have hd : orderOf (a ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact this)
      have h2 : orderOf (a ^ 2) = orderOf a / 2 := orderOf_pow_of_dvd (n := 2) (by norm_num) (by
        rw [ha]; exact dvd_pow_self 2 (by omega))
      have := Nat.le_of_dvd (by norm_num) hd
      rw [h2, ha] at this
      have h8' : 8 ≤ 2 ^ (m - 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exfalso
      apply hno
      have hcen : ∃ w ∈ Q, (∀ v ∈ Q, v * w = w * v) ∧ w * w = 1 ∧ w ≠ 1 :=
        exists_central_involution hQ (by omega)
      obtain ⟨w, hwQ, hwc, hw2, hw1⟩ := hcen
      have hwu : w = y * z := central_unique hQ hzQ hyQ hz2 hy2 hzy hne hz1 hC hconj h4 w hwQ hwc hw2 hw1
      have hu1 : y * z ≠ 1 := by rw [← hwu]; exact hw1
      set u' : ↥Q := ⟨y * z, hwu ▸ hwQ⟩ with hu'
      have hu'2 : u' * u' = 1 := Subtype.ext (by show (y * z) * (y * z) = 1; rw [← hwu]; exact hw2)
      have hu'1 : u' ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
      have hu'c : ∀ v : ↥Q, v * u' = u' * v := fun v => Subtype.ext (by
        show (v : G) * (y * z) = (y * z) * (v : G)
        rw [← hwu]; exact hwc v v.2)
      have hsd := sd_unique_involution (P := ↥Q) hm4' (a := a) (z := z') ha hM hz'2 h
        (R := R.subgroupOf Q) (fun x => hcov x x.2) (fun q r hr => hRn q q.2 r hr)
        (fun hz => hzR hz) hu'2 hu'1 hu'c
      intro s hsR hs1 hs2
      have := hsd ⟨s, hRQ hsR⟩ hsR (fun h => hs1 (congrArg Subtype.val h)) (Subtype.ext hs2)
      exact congrArg Subtype.val this
    · exact hdih h

theorem dihedral_sylow {Q : Subgroup G} (hQ : IsPGroup 2 Q) {z y : G} (hzQ : z ∈ Q) (hyQ : y ∈ Q)
    (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) (hne : z ≠ y) (hz1 : z ≠ 1) (hy1 : y ≠ 1)
    (hC : ∀ x ∈ Q, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z) (hconj : ¬ IsConj z (y * z))
    {R : Subgroup G} (hRQ : R ≤ Q) (hcov : ∀ x ∈ Q, x ∈ R ∨ x * z ∈ R)
    (hRn : ∀ q ∈ Q, ∀ r ∈ R, q * r * q⁻¹ ∈ R) (hzR : z ∉ R)
    (hno : (∀ s ∈ R, s ≠ 1 → s * s = 1 → s = y * z) → False) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥Q ≃* DihedralGroup (2 ^ m)) := by
  by_cases h4 : Nat.card Q ≤ 4
  · exact ⟨1, le_refl 1, by simpa using dihedral_of_card_le_four hzQ hyQ hz2 hy2 hzy hne hz1 hy1 h4⟩
  · exact dihedral_of_card_gt_four hQ hzQ hyQ hz2 hy2 hzy hne hz1 hC hconj (by omega) hRQ hcov hRn hzR hno

end Dihedral



end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
