module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117E

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem sec11c_eq_of_orderOf_eq_two_of_isCyclic {G : Type*} [Group G] {K : Subgroup G}
    [Finite K] (hK : IsCyclic K) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : x = y := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : 2 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← hx2]
    exact Subgroup.orderOf_dvd_natCard K hx
  have h := IsCyclic.card_orderOf_eq_totient (α := K) h2
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : (⟨x, hx⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  have hya : (⟨y, hy⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  rw [Finset.mem_singleton] at hxa hya
  exact congrArg Subtype.val (hxa.trans hya.symm)

private theorem sec11c_eq_one_or_eq_of_sq_eq_one_of_isCyclic [Finite G] {K : Subgroup G}
    (hK : IsCyclic K) {t x : G} (ht : t ∈ K) (ht2 : orderOf t = 2) (hx : x ∈ K)
    (hx2 : x ^ 2 = 1) : x = 1 ∨ x = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : x = 1
  · exact Or.inl h1
  · exact Or.inr
      (sec11c_eq_of_orderOf_eq_two_of_isCyclic hK hx ht (orderOf_eq_prime hx2 h1) ht2)

private theorem sec11c_mul_comm_of_isCyclic {K : Subgroup G} (hK : IsCyclic K) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) : x * y = y * x := by
  haveI := hK
  have h := (IsCyclic.isMulCommutative (α := K)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using congrArg Subtype.val h

private theorem sec11c_exists_orderOf_eq_four_of_isCyclic [Finite G] {K : Subgroup G}
    (hK : IsCyclic K) (hK2 : IsPGroup 2 K) (hcard : 2 < Nat.card K) :
    ∃ a ∈ K, orderOf a = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hK
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK2
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have h4 : 4 ∣ Nat.card K := by
    rw [hn]
    have h2n : 2 ≤ n := by
      by_contra h
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;> rw [hn] at hcard <;> norm_num at hcard
    exact (pow_dvd_pow 2 h2n : 2 ^ 2 ∣ 2 ^ n)
  refine ⟨((γ ^ (orderOf γ / 4) : K) : G), (γ ^ (orderOf γ / 4)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (by rw [hγ]; exact Nat.card_pos.ne') (by rw [hγ]; exact h4)

private theorem sec11c_eq_or_eq_inv_of_orderOf_eq_four [Finite G] {K : Subgroup G}
    (hK : IsCyclic K) {a x : G} (ha : a ∈ K) (hx : x ∈ K) (ha4 : orderOf a = 4)
    (hx4 : orderOf x = 4) : x = a ∨ x = a⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h4 : 4 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← ha4]
    exact Subgroup.orderOf_dvd_natCard K ha
  have h := IsCyclic.card_orderOf_eq_totient (α := K) h4
  rw [show Nat.totient 4 = 2 by decide] at h
  have hne : (⟨a, ha⟩ : K) ≠ ⟨a⁻¹, K.inv_mem ha⟩ := by
    intro he
    have h1 : a * a = 1 := by
      have h' : a = a⁻¹ := congrArg Subtype.val he
      calc a * a = a * a⁻¹ := by rw [← h']
        _ = 1 := mul_inv_cancel a
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h1])
    rw [ha4] at h2
    exact absurd h2 (by decide)
  have hsub : ({⟨a, ha⟩, ⟨a⁻¹, K.inv_mem ha⟩} : Finset K) ⊆
      Finset.univ.filter fun y : K => orderOf y = 4 := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_filter]
    rcases hy with rfl | rfl
    · exact ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, ha4]⟩
    · exact ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, orderOf_inv, ha4]⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h, Finset.card_pair hne])
  have hxm : (⟨x, hx⟩ : K) ∈ Finset.univ.filter fun y : K => orderOf y = 4 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, hx4]⟩
  rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hxm
  rcases hxm with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

theorem sec11c_card_le_four_of_cyclic [Finite G] {X Y : Subgroup G} {z : G} (hY : IsCyclic Y)
    (hXY : X ≤ Y) (hz2 : z * z = 1) (hX : ∀ x ∈ X, x * x ∈ zpowers z) : Nat.card X ≤ 4 := by
  classical
  haveI := hY
  haveI : IsCyclic X := Subgroup.isCyclic_of_le hXY
  haveI : Fintype X := Fintype.ofFinite X
  have hz2z : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  have h4 : ∀ a : X, a ^ 4 = 1 := by
    intro a
    apply Subtype.ext
    change (a : G) ^ 4 = 1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hX a a.2)
    have e : (a : G) ^ 4 = ((a : G) * a) * ((a : G) * a) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [e, ← hk, ← zpow_add, ← two_mul, zpow_mul, hz2z, one_zpow]
  have hcard : (Finset.univ.filter (fun a : X => a ^ 4 = 1)).card = Nat.card X := by
    rw [Finset.filter_true_of_mem (fun a _ => h4 a), Finset.card_univ, Nat.card_eq_fintype_card]
  have h := IsCyclic.card_pow_eq_one_le (α := X) (n := 4) (by norm_num)
  rwa [hcard] at h

theorem sec11c_card_le_eight [Finite G] {D Y X : Subgroup G} {z : G} (hY : IsCyclic Y)
    (hYD : Y ≤ D) (hYi : Y.relIndex D = 2) (hz2 : z * z = 1) (hXD : X ≤ D)
    (hX : IsElemAbelianMod z X) : Nat.card X ≤ 8 := by
  classical
  have hcardYsub : Nat.card ↥(Y.subgroupOf X) = Nat.card ↥(Y ⊓ X) := by
    rw [← Subgroup.card_map_of_injective (K := Y.subgroupOf X) X.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have hcardX : Nat.card ↥X = Nat.card ↥(Y ⊓ X) * Y.relIndex X := by
    rw [← Subgroup.card_mul_index (H := Y.subgroupOf X), hcardYsub]
    rfl
  have h1 : Nat.card ↥(Y ⊓ X) ≤ 4 :=
    sec11c_card_le_four_of_cyclic hY inf_le_left hz2 (fun x hx => (hX x hx.2 x hx.2).2)
  have h2 : Y.relIndex X ≤ 2 := by
    have hne : Y.relIndex D ≠ 0 := by rw [hYi]; norm_num
    calc Y.relIndex X ≤ Y.relIndex D := Subgroup.relIndex_le_of_le_right hXD hne
      _ = 2 := hYi
  calc Nat.card ↥X = Nat.card ↥(Y ⊓ X) * Y.relIndex X := hcardX
    _ ≤ 4 * 2 := Nat.mul_le_mul h1 h2
    _ = 8 := by norm_num

theorem sec11c_le_closure_compl {D Y : Subgroup G} (hYD : Y ≤ D) (hYi : Y.relIndex D = 2) :
    D ≤ Subgroup.closure {u : G | u ∈ D ∧ u ∉ Y} := by
  have hex : ∃ u0 ∈ D, u0 ∉ Y := by
    by_contra h
    push Not at h
    have hle : D ≤ Y := fun u hu => h u hu
    have h1 : Y.relIndex D = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [h1] at hYi
    norm_num at hYi
  obtain ⟨u0, hu0D, hu0Y⟩ := hex
  intro d hdD
  by_cases hdY : d ∈ Y
  · have hne : u0 * d ∉ Y := by
      intro hmem
      apply hu0Y
      have hde : u0 = (u0 * d) * d⁻¹ := by group
      rw [hde]
      exact Y.mul_mem hmem (Y.inv_mem hdY)
    have hgen : u0 * d ∈ Subgroup.closure {u : G | u ∈ D ∧ u ∉ Y} :=
      Subgroup.subset_closure ⟨D.mul_mem hu0D hdD, hne⟩
    have hu0gen : u0 ∈ Subgroup.closure {u : G | u ∈ D ∧ u ∉ Y} :=
      Subgroup.subset_closure ⟨hu0D, hu0Y⟩
    have hdu : d = u0⁻¹ * (u0 * d) := by group
    rw [hdu]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu0gen) hgen
  · exact Subgroup.subset_closure ⟨hdD, hdY⟩

theorem sec11c_exists_X_abstract {P : Type} [Group P] [Finite P] (hP2 : IsPGroup 2 P)
    {Y : Subgroup P} (hY : IsCyclic Y) (hYi : Y.index = 2) {z d : P} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ x : P, x * z = z * x) (hnab : ∃ a b : P, a * b ≠ b * a)
    (hdY : d ∉ Y) (hd4 : d ^ 4 = 1) :
    ∃ X : Subgroup P, d ∈ X ∧ z ∈ X ∧ IsElemAbelianMod z X ∧ 8 ≤ Nat.card X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hYnorm : Y.Normal := Subgroup.normal_of_index_eq_two hYi
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a :=
    fun a ha b hb => sec11c_mul_comm_of_isCyclic hY ha hb
  have hzY : z ∈ Y := by
    by_contra hznot
    have hdec : ∀ x : P, x ∈ Y ∨ ∃ y ∈ Y, x = z * y := by
      intro x
      by_cases hx : x ∈ Y
      · exact Or.inl hx
      · right
        have hzx : z * x ∈ Y :=
          (Subgroup.mul_mem_iff_of_index_two hYi (a := z) (b := x)).2
            (iff_of_false hznot hx)
        exact ⟨z * x, hzx, by rw [← mul_assoc, hz2, one_mul]⟩
    have hcommall : ∀ a b : P, a * b = b * a := by
      intro a b
      rcases hdec a with ha | ⟨ya, hya, rfl⟩
      · rcases hdec b with hb | ⟨yb, hyb, rfl⟩
        · exact hYcomm a ha b hb
        · calc a * (z * yb) = (a * z) * yb := by rw [mul_assoc]
            _ = (z * a) * yb := by rw [hzc a]
            _ = z * (a * yb) := by rw [mul_assoc]
            _ = z * (yb * a) := by rw [hYcomm a ha yb hyb]
            _ = (z * yb) * a := by rw [mul_assoc]
      · rcases hdec b with hb | ⟨yb, hyb, rfl⟩
        · calc (z * ya) * b = z * (ya * b) := by rw [mul_assoc]
            _ = z * (b * ya) := by rw [hYcomm ya hya b hb]
            _ = (z * b) * ya := by rw [mul_assoc]
            _ = (b * z) * ya := by rw [← hzc b]
            _ = b * (z * ya) := by rw [mul_assoc]
        · have hstep : ya * (z * yb) = z * (ya * yb) := by
            rw [← mul_assoc, hzc ya, mul_assoc]
          have h1 : (z * ya) * (z * yb) = ya * yb := by
            calc (z * ya) * (z * yb) = z * (ya * (z * yb)) := by rw [mul_assoc]
              _ = z * (z * (ya * yb)) := by rw [hstep]
              _ = (z * z) * (ya * yb) := by rw [← mul_assoc]
              _ = 1 * (ya * yb) := by rw [hz2]
              _ = ya * yb := by rw [one_mul]
          have hstep' : yb * (z * ya) = z * (yb * ya) := by
            rw [← mul_assoc, hzc yb, mul_assoc]
          have h2 : (z * yb) * (z * ya) = ya * yb := by
            calc (z * yb) * (z * ya) = z * (yb * (z * ya)) := by rw [mul_assoc]
              _ = z * (z * (yb * ya)) := by rw [hstep']
              _ = (z * z) * (yb * ya) := by rw [← mul_assoc]
              _ = 1 * (yb * ya) := by rw [hz2]
              _ = yb * ya := by rw [one_mul]
              _ = ya * yb := hYcomm yb hyb ya hya
          rw [h1, h2]
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (hcommall a b)
  have hY2 : IsPGroup 2 Y := hP2.to_subgroup Y
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY2
  have hk0 : k ≠ 0 := by
    rintro rfl
    have huniq : Subsingleton Y :=
      (Nat.card_eq_one_iff_unique.mp (by rw [hk]; norm_num)).1
    exact hz1 (congrArg Subtype.val (Subsingleton.elim (⟨z, hzY⟩ : Y) ⟨1, Y.one_mem⟩))
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hcardP : Nat.card P = 4 := by
      rw [← Subgroup.card_mul_index Y, hk, hYi]
      norm_num
    haveI : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcardP
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsMulCommutative.is_comm.comm a b)
  have hk2 : 2 ≤ k := by omega
  have hYbig : 2 < Nat.card Y := by
    rw [hk]
    have h4le : 4 ≤ 2 ^ k := by
      have := pow_le_pow_right' (a := 2) (by norm_num : 1 ≤ 2) hk2
      simpa using this
    omega
  obtain ⟨e, heY, heord⟩ : ∃ e ∈ Y, orderOf e = 4 :=
    sec11c_exists_orderOf_eq_four_of_isCyclic hY hY2 hYbig
  have hzord : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hee2 : orderOf (e * e) = 2 := by
    rw [← pow_two, orderOf_pow, heord]
    norm_num
  have hee : e * e = z :=
    sec11c_eq_of_orderOf_eq_two_of_isCyclic hY (Y.mul_mem heY heY) hzY hee2 hzord
  have hddY : d * d ∈ Y :=
    (Subgroup.mul_mem_iff_of_index_two hYi (a := d) (b := d)).2 Iff.rfl
  have hdd2 : (d * d) ^ 2 = 1 := by
    rw [← pow_two d, ← pow_mul, show 2 * 2 = 4 from rfl, hd4]
  have hdd : d * d ∈ zpowers z := by
    rcases sec11c_eq_one_or_eq_of_sq_eq_one_of_isCyclic hY hzY hzord hddY hdd2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  have hdedY : d * e * d⁻¹ ∈ Y := hYnorm.conj_mem e heY d
  have hded4 : orderOf (d * e * d⁻¹) = 4 := by
    have h4eq : (d * e * d⁻¹) ^ 4 = 1 := by
      rw [conj_pow, ← heord, pow_orderOf_eq_one]
      simp
    have h2ne : (d * e * d⁻¹) ^ 2 ≠ 1 := by
      intro h
      rw [conj_pow] at h
      have he2 : e ^ 2 = 1 := by
        calc e ^ 2 = d⁻¹ * (d * e ^ 2 * d⁻¹) * d := by group
          _ = 1 := by rw [h]; group
      have hdvd : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one he2
      rw [heord] at hdvd
      norm_num at hdvd
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2ne) (by simpa using h4eq)
  have hcase : d * e * d⁻¹ = e ∨ d * e * d⁻¹ = e⁻¹ :=
    sec11c_eq_or_eq_inv_of_orderOf_eq_four hY heY hdedY heord hded4
  have hcomm1 : d * e * d⁻¹ * e⁻¹ ∈ zpowers z := by
    rcases hcase with h | h
    · rw [h, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h]
      have hzz : e⁻¹ * e⁻¹ = z := by
        rw [← mul_inv_rev, hee, inv_eq_of_mul_eq_one_left hz2]
      rw [hzz]
      exact Subgroup.mem_zpowers z
  have hcomm2 : e * d * e⁻¹ * d⁻¹ ∈ zpowers z := by
    have h := Subgroup.inv_mem _ hcomm1
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  let X : Subgroup P := Subgroup.closure ({d, e} : Set P)
  have hdX : d ∈ X := Subgroup.subset_closure (by simp)
  have heX : e ∈ X := Subgroup.subset_closure (by simp)
  have hzX : z ∈ X := by
    have h : e * e ∈ X := X.mul_mem heX heX
    rwa [hee] at h
  have hmod : IsElemAbelianMod z X := by
    change IsElemAbelianMod z (Subgroup.closure ({d, e} : Set P))
    refine sec11_isElemAbelianMod_closure ?_ ?_ ?_
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]
        exact hzc d
      · rw [ha]
        exact hzc e
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]
        exact hdd
      · rw [ha, hee]
        exact Subgroup.mem_zpowers z
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb, show d * d * d⁻¹ * d⁻¹ = 1 by group]
        exact Subgroup.one_mem _
      · rw [ha, hb]
        exact hcomm1
      · rw [ha, hb]
        exact hcomm2
      · rw [ha, hb, show e * e * e⁻¹ * e⁻¹ = 1 by group]
        exact Subgroup.one_mem _
  refine ⟨X, hdX, hzX, hmod, ?_⟩
  have hzpe : Nat.card (zpowers e) = 4 := by rw [Nat.card_zpowers, heord]
  have hle : zpowers e ≤ X := zpowers_le.mpr heX
  have hdvd : 4 ∣ Nat.card X := by
    rw [← hzpe]
    exact Subgroup.card_dvd_of_le hle
  have hne : Nat.card X ≠ 4 := by
    intro h4
    have heq : zpowers e = X := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [h4, hzpe]
    have hdmem : d ∈ zpowers e := heq ▸ hdX
    exact hdY (zpowers_le.mpr heY hdmem)
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · omega
      · omega
    · exact h
  omega

theorem sec11c_exists_X_of_cyclic [Finite G] {D Y : Subgroup G} {z d : G} (hD2 : IsPGroup 2 D)
    (hYD : Y ≤ D) (hY : IsCyclic Y) (hYi : Y.relIndex D = 2) (hzD : z ∈ D) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ x ∈ D, x * z = z * x) (hnab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a)
    (hdD : d ∈ D) (hdY : d ∉ Y) (hd4 : d ^ 4 = 1) :
    ∃ X : Subgroup G, X ≤ D ∧ d ∈ X ∧ z ∈ X ∧ IsElemAbelianMod z X ∧ 8 ≤ Nat.card X := by
  classical
  have hY' : IsCyclic (Y.subgroupOf D) :=
    (Subgroup.subgroupOfEquivOfLe hYD).isCyclic.mpr hY
  have hYi' : (Y.subgroupOf D).index = 2 := by
    simpa only [Subgroup.relIndex] using hYi
  have hz2' : (⟨z, hzD⟩ : D) * ⟨z, hzD⟩ = 1 := Subtype.ext hz2
  have hz1' : (⟨z, hzD⟩ : D) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzc' : ∀ x : D, x * ⟨z, hzD⟩ = ⟨z, hzD⟩ * x := fun x => Subtype.ext (hzc x x.2)
  have hnab' : ∃ a b : D, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (by simpa using congrArg Subtype.val h)⟩
  have hdY' : (⟨d, hdD⟩ : D) ∉ Y.subgroupOf D := by
    intro h
    exact hdY (Subgroup.mem_subgroupOf.mp h)
  have hd4' : (⟨d, hdD⟩ : D) ^ 4 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hd4
  obtain ⟨X', hdX', hzX', hmod', hcard'⟩ :=
    sec11c_exists_X_abstract (P := D) hD2 hY' hYi' hz2' hz1' hzc' hnab' hdY' hd4'
  refine ⟨X'.map D.subtype, Subgroup.map_subtype_le X', ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨d, hdD⟩, hdX', rfl⟩
  · exact ⟨⟨z, hzD⟩, hzX', rfl⟩
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨hc, hs⟩ := hmod' a' ha' b' hb'
    refine ⟨?_, ?_⟩
    · have hmap : D.subtype a' * D.subtype b' * (D.subtype a')⁻¹ * (D.subtype b')⁻¹ =
          D.subtype (a' * b' * a'⁻¹ * b'⁻¹) := by simp
      rw [hmap]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      rw [← hk, map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
    · have hmap : D.subtype a' * D.subtype a' = D.subtype (a' * a') := by simp
      rw [hmap]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      rw [← hk, map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  · rw [Subgroup.card_map_of_injective (K := X') D.subtype_injective]
    exact hcard'

end CFSG.OddStandard.SmallF3.Omega
