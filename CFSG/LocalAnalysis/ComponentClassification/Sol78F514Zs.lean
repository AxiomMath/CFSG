module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514E

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.Quasithin

variable {G : Type} [Group G]

theorem isPGroup_closure_pair {z w : G} (hz : z * z = 1) (hw : w * w = 1)
    (hzw : (z * w) ^ 4 = 1) : IsPGroup 2 (closure ({z, w} : Set G)) := by
  set u := z * w with hu
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzu : ∀ k : ℤ, z * u ^ k = u ^ (-k) * z := fun k => by
    have h1 : z * u * z⁻¹ = u⁻¹ := by
      rw [hu, hzinv, mul_inv_rev, inv_eq_of_mul_eq_one_right hw, hzinv,
        show z * (z * w) * z = (z * z) * w * z by group, hz, one_mul]
    have h2 : z * u ^ k * z⁻¹ = u ^ (-k) := by
      rw [← conj_zpow, h1, inv_zpow, zpow_neg]
    calc z * u ^ k = (z * u ^ k * z⁻¹) * z := by group
      _ = u ^ (-k) * z := by rw [h2]
  let M : Subgroup G :=
    { carrier := {x | ∃ k : ℤ, x = u ^ k ∨ x = u ^ k * z}
      one_mem' := ⟨0, Or.inl (by simp)⟩
      mul_mem' := by
        rintro x y ⟨a, rfl | rfl⟩ ⟨b, rfl | rfl⟩
        · exact ⟨a + b, Or.inl (by rw [zpow_add])⟩
        · exact ⟨a + b, Or.inr (by rw [zpow_add]; group)⟩
        · exact ⟨a - b, Or.inr (by rw [mul_assoc, hzu, ← mul_assoc, ← zpow_add, sub_eq_add_neg])⟩
        · refine ⟨a - b, Or.inl ?_⟩
          rw [show u ^ a * z * (u ^ b * z) = u ^ a * (z * u ^ b) * z by group, hzu,
            show u ^ a * (u ^ (-b) * z) * z = u ^ a * u ^ (-b) * (z * z) by group, hz, mul_one,
            ← zpow_add, sub_eq_add_neg]
      inv_mem' := by
        rintro x ⟨a, rfl | rfl⟩
        · exact ⟨-a, Or.inl (by rw [zpow_neg])⟩
        · refine ⟨a, Or.inr ?_⟩
          rw [mul_inv_rev, hzinv, ← zpow_neg, hzu, neg_neg] }
  have hle : closure ({z, w} : Set G) ≤ M := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [← hzu, zpow_one, hu, ← mul_assoc, hz, one_mul]
  intro x
  obtain ⟨k, hk | hk⟩ := hle x.2
  · refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, hk, Subgroup.coe_one, show 2 ^ 2 = 4 by norm_num, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzw, one_zpow]
  · refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, hk, Subgroup.coe_one, pow_one, sq, show u ^ k * z * (u ^ k * z) =
      u ^ k * (z * u ^ k) * z by group, hzu, show u ^ k * (u ^ (-k) * z) * z =
      (u ^ k * u ^ (-k)) * (z * z) by group, hz, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

omit [Group G] in
theorem two_mul_half_succ_of_odd {o : ℕ} (ho : Odd o) : 2 * ((o + 1) / 2) = o + 1 := by
  obtain ⟨k, rfl⟩ := ho
  omega

omit [Group G] in
theorem exists_mem_mul_centralizer {X : Type*} [Group X] [Finite X] {zb : X}
    (hzb2 : zb * zb = 1) {N : Subgroup X} (hNodd : Odd (Nat.card N))
    (hN : ∀ g : X, g * zb * g⁻¹ * zb⁻¹ ∈ N) :
    ∀ g : X, ∃ k ∈ N, k⁻¹ * g ∈ centralizer ({zb} : Set X) := by
  have hzbinv : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hzb2
  intro g
  set m := g * zb * g⁻¹ * zb⁻¹ with hm
  have hmN : m ∈ N := hN g
  have hmzb : m * zb = g * zb * g⁻¹ := by rw [hm]; group
  have h1 : m * zb * (m * zb) = 1 := by
    rw [hmzb, show g * zb * g⁻¹ * (g * zb * g⁻¹) = g * (zb * zb) * g⁻¹ by group, hzb2]
    group
  have hmz : zb * m * zb⁻¹ = m⁻¹ := by
    rw [hzbinv]
    calc zb * m * zb = m⁻¹ * (m * zb * (m * zb)) := by group
      _ = m⁻¹ := by rw [h1, mul_one]
  have ho : Odd (orderOf m) := Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hmN)
  set k := m ^ ((orderOf m + 1) / 2) with hk
  have hkN : k ∈ N := pow_mem hmN _
  have hk2 : k * k = m := by
    rw [hk, ← pow_add, ← two_mul, two_mul_half_succ_of_odd ho, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hkz : zb * k * zb⁻¹ = k⁻¹ := by
    rw [hk, ← conj_pow, hmz, inv_pow]
  refine ⟨k, hkN, mem_centralizer_singleton_iff.mpr ?_⟩
  have hzk : zb * k⁻¹ = k * zb := by
    have h3 : zb * k⁻¹ * zb⁻¹ = k := by
      rw [show zb * k⁻¹ * zb⁻¹ = (zb * k * zb⁻¹)⁻¹ by group, hkz, inv_inv]
    calc zb * k⁻¹ = zb * k⁻¹ * zb⁻¹ * zb := by group
      _ = k * zb := by rw [h3]
  have h2 : k * zb * k⁻¹ = g * zb * g⁻¹ := by
    calc k * zb * k⁻¹ = k * (zb * k⁻¹) := by group
      _ = k * k * zb := by rw [hzk, ← mul_assoc]
      _ = g * zb * g⁻¹ := by rw [hk2, hmzb]
  calc k⁻¹ * g * zb = k⁻¹ * (g * zb * g⁻¹) * g := by group
    _ = k⁻¹ * (k * zb * k⁻¹) * g := by rw [h2]
    _ = zb * (k⁻¹ * g) := by group

theorem isSolvable_of_isolated_pair [Finite G] {z t : G} (hz : z * z = 1) (ht : t * t = 1)
    (hz1 : z ≠ 1) (ht1 : t ≠ 1)
    (hCZ : Group.IsSolvable ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)))
    {X : Subgroup G} (hXd : X ≤ centralizer ({z * t} : Set G)) (hzX : z ∈ X) (htX : t ∈ X)
    {P : Subgroup G} (hP : ABGLocalTools.IsSylowOf 2 P X)
    (hcl : ∀ x ∈ X, x⁻¹ * z * x ∈ P → x⁻¹ * z * x = z ∨ x⁻¹ * z * x = t) :
    Group.IsSolvable X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdX : z * t ∈ X := mul_mem hzX htX
  have hdc : ∀ x ∈ X, x * (z * t) = z * t * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (hXd hx)
  have htzd : t = z * (z * t) := by rw [← mul_assoc, hz, one_mul]
  have hzt : z * t = t * z := by
    have h1 := hdc z hzX
    calc z * t = z⁻¹ * (z * (z * t)) := by group
      _ = z⁻¹ * (z * t * z) := by rw [h1]
      _ = t * z := by group
  set d' : X := ⟨z * t, hdX⟩ with hd'
  set z' : X := ⟨z, hzX⟩ with hz'
  set D : Subgroup X := zpowers d' with hD
  have hdc' : ∀ x : X, x * d' = d' * x := fun x => Subtype.ext (hdc x x.2)
  have hDn : D.Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have : g * d' ^ k * g⁻¹ = d' ^ k := by
      rw [← conj_zpow, show g * d' * g⁻¹ = d' by rw [hdc' g]; group]
    rw [this]; exact zpow_mem (mem_zpowers d') k⟩
  set π := QuotientGroup.mk' D with hπ
  set zb := π z' with hzb
  have hd'2 : d' * d' = 1 := Subtype.ext (by
    show z * t * (z * t) = 1
    calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt]
      _ = 1 := by rw [← mul_assoc, hz, one_mul, ht])
  have hmemD : ∀ x : X, x ∈ D → x = 1 ∨ x = d' := fun x hx =>
    eq_one_or_eq_of_mem_zpowers_two hd'2 hx
  have hπeq : ∀ a b : X, π a = π b ↔ a⁻¹ * b ∈ D := fun a b => QuotientGroup.eq
  have hzb1 : zb ≠ 1 := by
    intro h1
    have h2 : z' ∈ D := by
      rw [← QuotientGroup.eq_one_iff (N := D)]; exact h1
    rcases hmemD z' h2 with h3 | h3
    · exact hz1 (congrArg Subtype.val h3)
    · apply ht1
      have h4 : z = z * t := congrArg Subtype.val h3
      calc t = z⁻¹ * (z * t) := by group
        _ = z⁻¹ * z := by rw [← h4]
        _ = 1 := inv_mul_cancel z
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← map_mul, show z' * z' = 1 from Subtype.ext hz, map_one]
  have hiso : ∀ g : X ⧸ D, g * zb * g⁻¹ * zb = zb * (g * zb * g⁻¹) → g * zb * g⁻¹ = zb := by
    intro g hg
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective D g
    set w := (g' : G) * z * (g' : G)⁻¹ with hw
    have hwX : w ∈ X := mul_mem (mul_mem g'.2 hzX) (inv_mem g'.2)
    set w' : X := ⟨w, hwX⟩ with hw'
    have hwg : g' * z' * g'⁻¹ = w' := Subtype.ext (by simp [hw', hw, hz'])
    rw [← map_mul, ← map_inv, ← map_mul, hwg] at hg ⊢
    rw [← map_mul, ← map_mul, hπeq] at hg
    have hc : (w' * z')⁻¹ * (z' * w') = 1 ∨ (w' * z')⁻¹ * (z' * w') = d' := hmemD _ hg
    have hw2 : w * w = 1 := by
      rw [hw, show (g' : G) * z * (g' : G)⁻¹ * ((g' : G) * z * (g' : G)⁻¹) =
        (g' : G) * (z * z) * (g' : G)⁻¹ by group, hz]; group
    have h4 : (z * w) ^ 4 = 1 := by
      have hc' : (w * z)⁻¹ * (z * w) = 1 ∨ (w * z)⁻¹ * (z * w) = z * t := by
        rcases hc with h | h
        · left; exact congrArg Subtype.val h
        · right; exact congrArg Subtype.val h
      have hzw2 : (z * w) * (z * w) = 1 ∨ (z * w) * (z * w) = z * t := by
        have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
        have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
        have he : (w * z)⁻¹ * (z * w) = z * w * (z * w) := by
          rw [mul_inv_rev, hzinv, hwinv]
        rw [← he]; exact hc'
      have hdd : z * t * (z * t) = 1 := congrArg Subtype.val hd'2
      have h4e : (z * w) ^ 4 = (z * w) * (z * w) * ((z * w) * (z * w)) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rcases hzw2 with h | h
      · rw [h4e, h, one_mul]
      · rw [h4e, h, hdd]
    have hcp := isPGroup_closure_pair hz hw2 h4
    have hcX : closure ({z, w} : Set G) ≤ X := by
      rw [closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hzX
      · exact hwX
    obtain ⟨k, hkX, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hP hcX hcp
    have hkz := hcl k hkX (hk z (subset_closure (by simp)))
    have hkw : (g'⁻¹ * ⟨k, hkX⟩ : X)⁻¹ * z * ((g'⁻¹ * ⟨k, hkX⟩ : X) : G) ∈ P := by
      have := hk w (subset_closure (by simp))
      convert this using 1
      simp [hw]; group
    have hkw' := hcl _ (g'⁻¹ * ⟨k, hkX⟩ : X).2 hkw
    have hkw'' : k⁻¹ * w * k = z ∨ k⁻¹ * w * k = t := by
      have he : ((g'⁻¹ * ⟨k, hkX⟩ : X) : G)⁻¹ * z * ((g'⁻¹ * ⟨k, hkX⟩ : X) : G) = k⁻¹ * w * k := by
        simp [hw]; group
      rw [he] at hkw'; exact hkw'
    have hkd : k⁻¹ * (z * t) * k = z * t := by
      have := hdc k hkX
      calc k⁻¹ * (z * t) * k = k⁻¹ * (k * (z * t)) := by rw [this]; group
        _ = z * t := by group
    have hkt : ∀ u : G, k⁻¹ * u * k = z ∨ k⁻¹ * u * k = t → u = z ∨ u = t := by
      intro u hu
      have inv_eq : ∀ a b : G, k⁻¹ * a * k = b → a = k * b * k⁻¹ := fun a b h => by
        rw [← h]; group
      have hkz' : k⁻¹ * t * k = (k⁻¹ * z * k) * (z * t) := by
        calc k⁻¹ * t * k = k⁻¹ * (z * (z * t)) * k := by rw [← htzd]
          _ = (k⁻¹ * z * k) * (k⁻¹ * (z * t) * k) := by group
          _ = (k⁻¹ * z * k) * (z * t) := by rw [hkd]
      rcases hkz with h1 | h1
      ·
        have h2 : k⁻¹ * t * k = t := by rw [hkz', h1, ← htzd]
        rcases hu with h3 | h3
        · left; rw [inv_eq u z h3, ← inv_eq z z h1]
        · right; rw [inv_eq u t h3, ← inv_eq t t h2]
      ·
        have h2 : k⁻¹ * t * k = z := by
          rw [hkz', h1]
          calc t * (z * t) = (z * t) * t := by rw [← mul_assoc, ← hzt]
            _ = z := by rw [mul_assoc, ht, mul_one]
        rcases hu with h3 | h3
        · right; rw [inv_eq u z h3, ← inv_eq t z h2]
        · left; rw [inv_eq u t h3, ← inv_eq z t h1]
    rcases hkt w hkw'' with h1 | h1
    · rw [hzb]; congr 1; exact Subtype.ext h1
    · rw [hzb, hπeq]
      have h2 : w'⁻¹ * z' = d' := Subtype.ext (by
        show w⁻¹ * z = z * t
        rw [h1, inv_eq_of_mul_eq_one_right ht, ← hzt])
      rw [h2]; exact mem_zpowers d'
  let : Fintype (X ⧸ D) := Fintype.ofFinite _
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar (X ⧸ D) zb hzb1 hzb2 hiso
  have hcover := exists_mem_mul_centralizer hzb2 hNodd hN
  set M := (centralizer ({zb} : Set (X ⧸ D))).comap π with hM
  set Kx := centralizer ({z'} : Set X) with hKx
  have hmemM : ∀ g ∈ M, g⁻¹ * z' * g = z' ∨ g⁻¹ * z' * g = z' * d' := by
    intro g hg
    rw [hM, mem_comap, mem_centralizer_singleton_iff, hzb, ← map_mul, ← map_mul, hπeq] at hg
    rcases hmemD _ hg with h1 | h1
    · left
      have h2 : z' * g = g * z' := by
        calc z' * g = (g * z') * ((g * z')⁻¹ * (z' * g)) := by group
          _ = g * z' := by rw [h1, mul_one]
      calc g⁻¹ * z' * g = g⁻¹ * (z' * g) := by group
        _ = z' := by rw [h2]; group
    · right
      have h2 : z' * g = g * z' * d' := by
        calc z' * g = (g * z') * ((g * z')⁻¹ * (z' * g)) := by group
          _ = g * z' * d' := by rw [h1]
      calc g⁻¹ * z' * g = g⁻¹ * (z' * g) := by group
        _ = z' * d' := by rw [h2]; group
  have hfwd : ∀ g ∈ M, ∀ y ∈ Kx, g * y * g⁻¹ ∈ Kx := by
    intro g hg y hy
    have hyz : y * z' = z' * y := mem_centralizer_singleton_iff.mp hy
    have hyd : y * d' = d' * y := hdc' y
    rw [hKx, mem_centralizer_singleton_iff]
    have h1 : y * (g⁻¹ * z' * g) = (g⁻¹ * z' * g) * y := by
      rcases hmemM g hg with h | h <;> rw [h]
      · exact hyz
      · rw [← mul_assoc, hyz, mul_assoc, hyd, mul_assoc]
    calc g * y * g⁻¹ * z' = g * (y * (g⁻¹ * z' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z' * g) * y) * g⁻¹ := by rw [h1]
      _ = z' * (g * y * g⁻¹) := by group
  have hMn : M ≤ normalizer (Kx : Set X) := fun g hg => mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => hfwd g hg y hy, fun hy => by
      have := hfwd g⁻¹ (inv_mem hg) _ hy
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this⟩
  have hKx_solv : Group.IsSolvable Kx := by
    have hle : ∀ x : Kx, ((x : X) : G) ∈
        centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
      intro x
      have hxz : ((x : X) : G) * z = z * ((x : X) : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.2)
      have hxd : ((x : X) : G) * (z * t) = z * t * ((x : X) : G) := hdc _ (x : X).2
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hxz,
        mem_centralizer_singleton_iff.mpr ?_⟩
      calc ((x : X) : G) * t = ((x : X) : G) * (z * (z * t)) := by rw [← htzd]
        _ = z * (((x : X) : G) * (z * t)) := by rw [← mul_assoc, hxz, mul_assoc]
        _ = z * (z * t * ((x : X) : G)) := by rw [hxd]
        _ = t * ((x : X) : G) := by rw [← mul_assoc, ← htzd]
    let f : Kx →* ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) :=
      { toFun := fun x => ⟨((x : X) : G), hle x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) (fun a b h => by
      have h1 := congrArg
        (fun y : ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) => (y : G)) h
      exact Subtype.ext (Subtype.ext h1))
  have hMsolv : Group.IsSolvable M := by
    by_cases hall : ∀ g ∈ M, g ∈ Kx
    · exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hall)
        (Subgroup.inclusion_injective hall)
    · push Not at hall
      obtain ⟨g₀, hg₀M, hg₀K⟩ := hall
      have hzg₀ : g₀⁻¹ * z' * g₀ = z' * d' := by
        rcases hmemM g₀ hg₀M with h | h
        · exfalso; apply hg₀K
          rw [hKx, mem_centralizer_singleton_iff]
          calc g₀ * z' = g₀ * (g₀⁻¹ * z' * g₀) := by rw [h]
            _ = z' * g₀ := by group
        · exact h
      have hle : M ≤ Kx ⊔ zpowers g₀ := by
        intro g hg
        by_cases hgK : g ∈ Kx
        · exact mem_sup_left hgK
        · have hzg : g⁻¹ * z' * g = z' * d' := by
            rcases hmemM g hg with h | h
            · exfalso; apply hgK
              rw [hKx, mem_centralizer_singleton_iff]
              calc g * z' = g * (g⁻¹ * z' * g) := by rw [h]
                _ = z' * g := by group
            · exact h
          have hgg : g * g₀⁻¹ ∈ Kx := by
            rw [hKx, mem_centralizer_singleton_iff]
            have h1 : g₀ * z' * g₀⁻¹ = z' * d' := by
              have h2 : z' = g₀ * (z' * d') * g₀⁻¹ := by rw [← hzg₀]; group
              calc g₀ * z' * g₀⁻¹ = g₀ * z' * g₀⁻¹ * (d' * d') := by rw [hd'2, mul_one]
                _ = (g₀ * (z' * d') * g₀⁻¹) * d' := by
                    rw [show g₀ * (z' * d') * g₀⁻¹ = g₀ * z' * g₀⁻¹ * (g₀ * d' * g₀⁻¹) by group,
                      show g₀ * d' * g₀⁻¹ = d' by rw [hdc' g₀]; group]
                    group
                _ = z' * d' := by rw [← h2]
            have h3 : (g * g₀⁻¹)⁻¹ * z' * (g * g₀⁻¹) = z' := by
              calc (g * g₀⁻¹)⁻¹ * z' * (g * g₀⁻¹) = g₀ * (g⁻¹ * z' * g) * g₀⁻¹ := by group
                _ = g₀ * (z' * d') * g₀⁻¹ := by rw [hzg]
                _ = g₀ * z' * g₀⁻¹ * (g₀ * d' * g₀⁻¹) := by group
                _ = z' * d' * d' := by
                    rw [h1, show g₀ * d' * g₀⁻¹ = d' by rw [hdc' g₀]; group]
                _ = z' := by rw [mul_assoc, hd'2, mul_one]
            calc g * g₀⁻¹ * z' = g * g₀⁻¹ * ((g * g₀⁻¹)⁻¹ * z' * (g * g₀⁻¹)) := by rw [h3]
              _ = z' * (g * g₀⁻¹) := by group
          have : g = (g * g₀⁻¹) * g₀ := by group
          rw [this]
          exact mul_mem (mem_sup_left hgg) (mem_sup_right (mem_zpowers g₀))
      have hzp : Group.IsSolvable (zpowers g₀) := Group.isSolvable_of_comm fun a b => by
        obtain ⟨_, i, rfl⟩ := a
        obtain ⟨_, j, rfl⟩ := b
        exact Subtype.ext (Commute.zpow_zpow_self g₀ i j).eq
      have hsup : Group.IsSolvable ↥(Kx ⊔ zpowers g₀) :=
        A3.isSolvable_sup_of_le_normalizer ((zpowers_le_of_mem (hMn hg₀M)))
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
  have hCsolv : Group.IsSolvable (centralizer ({zb} : Set (X ⧸ D))) := by
    have hCM : (centralizer ({zb} : Set (X ⧸ D))) = M.map π := by
      rw [hM, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D)]
    rw [hCM]
    exact Group.isSolvable_of_surjective (f := π.subgroupMap M) (π.subgroupMap_surjective M)
  have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hNnorm : centralizer ({zb} : Set (X ⧸ D)) ≤ normalizer (N : Set (X ⧸ D)) :=
    fun g _ => mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => hNn.conj_mem h hh g, fun hh => by
        have := hNn.conj_mem _ hh g⁻¹
        rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this⟩
  have hsup : Group.IsSolvable ↥(N ⊔ centralizer ({zb} : Set (X ⧸ D))) :=
    A3.isSolvable_sup_of_le_normalizer hNnorm
  have htop : N ⊔ centralizer ({zb} : Set (X ⧸ D)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨k, hkN, hkC⟩ := hcover g
    rw [show g = k * (k⁻¹ * g) by group]
    exact mul_mem (mem_sup_left hkN) (mem_sup_right hkC)
  have hXb : Group.IsSolvable (X ⧸ D) := by
    rw [htop] at hsup
    exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := X ⧸ D)).toMonoidHom)
      (Subgroup.topEquiv (G := X ⧸ D)).surjective
  have hDsolv : Group.IsSolvable D := Group.isSolvable_of_comm fun a b => by
    obtain ⟨_, i, rfl⟩ := a
    obtain ⟨_, j, rfl⟩ := b
    exact Subtype.ext (Commute.zpow_zpow_self d' i j).eq
  exact Group.isSolvable_of_ker_le_range D.subtype π (by
    rw [hπ, QuotientGroup.ker_mk', range_subtype])

end CFSG.ComponentClassification.Sol78.F514
