module

public import CFSG.GH74.Uniqueness.Section4XData
public import CFSG.GH74.Uniqueness.Section4Simple
public import CFSG.GH74.Uniqueness.Section4Bender
public import CFSG.GH74.Uniqueness.Section4Lift

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Structure

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M L D O : Subgroup X} {u : X}

theorem XData.isStronglyEmbedded (hD : XData Z M L D O u) :
    IsStronglyEmbedded (M.subgroupOf D) := by
  obtain ⟨K, instK, φ, hsurj, hker, hB, S, hS⟩ := hD.bar
  have : Finite K := Finite.of_surjective φ hsurj
  refine isStronglyEmbedded_of_map φ hsurj ?_ ?_ ?_
  · rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD.O_le).toEquiv]
    exact hD.O_odd
  · rw [hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hD.O_M hx
  · rw [hS]
    exact isStronglyEmbedded_normalizer_of_isBenderGroup hB S

theorem XData.exists_conj_involutions
    (hD : XData Z M L D O u) {a b : X} (ha : a ∈ D) (hb : b ∈ D)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : ∃ d ∈ D, d⁻¹ * a * d = b := by
  have ha2' : orderOf (⟨a, ha⟩ : ↥D) = 2 := by rw [Subgroup.orderOf_mk]; exact ha2
  have hb2' : orderOf (⟨b, hb⟩ : ↥D) = 2 := by rw [Subgroup.orderOf_mk]; exact hb2
  obtain ⟨g, hg⟩ := Simple.exists_conj_of_isStronglyEmbedded hD.isStronglyEmbedded ha2' hb2'
  refine ⟨g, g.2, ?_⟩
  exact congrArg Subtype.val hg

omit [Finite X] in
theorem mem_zpowers_involution_cases {t x : X} (ht : t * t = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  have hk : k = k % 2 + 2 * (k / 2) := (Int.emod_add_mul_ediv k 2).symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [hk, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem XData.mem_normalizer_O (hD : XData Z M L D O u) {g : X} (hg : g ∈ L) :
    g ∈ normalizer (O : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hD.O_norm g (Subgroup.le_normalizer hg) x hx, fun hx => ?_⟩
  have := hD.O_norm g⁻¹ (Subgroup.le_normalizer (L.inv_mem hg)) _ hx
  simpa [mul_assoc] using this

theorem XData.conj_mem_O (hD : XData Z M L D O u) {g x : X} (hg : g ∈ L) (hx : x ∈ O) :
    g * x * g⁻¹ ∈ O :=
  (Subgroup.mem_normalizer_iff.mp (hD.mem_normalizer_O hg) x).mp hx

theorem XData.comm_D (hD : XData Z M L D O u) {a : X} (ha : a ∈ D) : a * u * a⁻¹ * u⁻¹ ∈ O := by
  have h := O.inv_mem (hD.comm a ha)
  have e : (u * a * u⁻¹ * a⁻¹)⁻¹ = a * u * a⁻¹ * u⁻¹ := by group
  rwa [e] at h

theorem XData.comm_L (hD : XData Z M L D O u) {a : X} (ha : a ∈ L) : a * u * a⁻¹ * u⁻¹ ∈ O := by
  have hnorm : ∀ x ∈ D, u * x * u⁻¹ ∈ D := fun x hx =>
    hD.D_norm u (Subgroup.le_normalizer hD.mem) x hx
  rw [hD.sup] at ha
  rcases mem_sup_zpowers_of_involution hD.sq hnorm ha with h | h
  · exact hD.comm_D h
  · have h' := hD.comm_D h
    have e : a * u * a⁻¹ * u⁻¹ = (a * u) * u * (a * u)⁻¹ * u⁻¹ := by group
    rw [e]
    exact h'

theorem XData.eq_one_or_orderOf_eq_two (hD : XData Z M L D O u) : u = 1 ∨ orderOf u = 2 := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  · exact Or.inr (orderOf_eq_prime (by rw [pow_two]; exact hD.sq) hu1)

theorem XData.of_mem_coset (hD : XData Z M L D O u) {u₀ : X} (hu₀L : u₀ ∈ L) (hu₀M : u₀ ∈ M)
    (hu₀2 : u₀ * u₀ = 1) (hu₀ : u₀ * u⁻¹ ∈ O) : XData Z M L D O u₀ := by
  obtain ⟨o, hoO, rfl⟩ : ∃ o ∈ O, u₀ = o * u := ⟨u₀ * u⁻¹, hu₀, by group⟩
  have hoD : o ∈ D := hD.O_le hoO
  have hu_sup : u ∈ D ⊔ zpowers (o * u) := by
    have h1 : o⁻¹ * (o * u) ∈ D ⊔ zpowers (o * u) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (D.inv_mem hoD))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rwa [inv_mul_cancel_left] at h1
  have hsup : L = D ⊔ zpowers (o * u) :=
    le_antisymm (hD.sup ▸ sup_le le_sup_left (Subgroup.zpowers_le.mpr hu_sup))
      (sup_le hD.D_le (Subgroup.zpowers_le.mpr hu₀L))
  have hinf : D ⊓ zpowers (o * u) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxz⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_involution_cases hu₀2 hxz with h | h
    · exact h
    · have hu₀D : o * u ∈ D := h ▸ hxD
      have huD : u ∈ D := by
        have h1 : o⁻¹ * (o * u) ∈ D := D.mul_mem (D.inv_mem hoD) hu₀D
        rwa [inv_mul_cancel_left] at h1
      have hu1 : u = 1 := by
        have : u ∈ D ⊓ zpowers u := Subgroup.mem_inf.mpr ⟨huD, Subgroup.mem_zpowers u⟩
        rw [hD.inf, Subgroup.mem_bot] at this
        exact this
      rw [hu1, mul_one] at h
      have hoo : o * o = 1 := by simpa [hu1] using hu₀2
      have ho1 : o = 1 := by
        by_contra hne
        have h2 : orderOf o = 2 := orderOf_eq_prime (by rw [pow_two]; exact hoo) hne
        exact CFSG.OddInversion.notMem_of_odd_card hD.O_odd h2 hoO
      rw [h, ho1]
  refine ⟨hD.D_le, hD.O_le, hu₀L, hu₀M, hu₀2, hsup, hinf, hD.D_norm, hD.O_norm, hD.O_odd, ?_,
    hD.O_M, hD.bar, ?_⟩
  · intro d hd
    have hdL : d ∈ L := hD.D_le hd
    have e : o * u * d * (o * u)⁻¹ * d⁻¹ =
        o * (u * d * u⁻¹ * d⁻¹) * (d * o⁻¹ * d⁻¹) := by group
    rw [e]
    exact O.mul_mem (O.mul_mem hoO (hD.comm d hd)) (hD.conj_mem_O hdL (O.inv_mem hoO))
  · intro z hz hzL
    obtain ⟨⟨d, hdD, hzd⟩, hzO⟩ := hD.zset z hz hzL
    have hconj : u⁻¹ * o⁻¹ * u ∈ O := by
      simpa using hD.conj_mem_O (L.inv_mem hD.mem) (O.inv_mem hoO)
    refine ⟨⟨u⁻¹ * o⁻¹ * u * d, D.mul_mem (hD.O_le hconj) hdD, ?_⟩, ?_⟩
    · rw [hzd]
      group
    · intro o' ho' hzo
      apply hzO (u⁻¹ * o * u * o')
      · have : u⁻¹ * o * u ∈ O := by
          simpa using hD.conj_mem_O (L.inv_mem hD.mem) hoO
        exact O.mul_mem this ho'
      · rw [hzo]
        group

omit [Finite X] in
theorem mem_of_mul_inv_mem_of_involution {Z : Set X} (hZ : IsInvariantInvolutionSet Z)
    {O : Subgroup X} (hO : Odd (Nat.card O)) {z w : X} (hz : z ∈ Z)
    (hzO : z ∈ normalizer (O : Set X)) (hw2 : orderOf w = 2) (hwz : w * z⁻¹ ∈ O) : w ∈ Z := by
  have hz2 := hZ.1 z hz
  have hcoset := (CFSG.OddInversion.odd_inversion_coset_count hO hzO
    (CFSG.OddInversion.notMem_of_odd_card hO hz2) hz2).1
  have hmem : w ∈ {v : X | v * z⁻¹ ∈ O ∧ orderOf v = 2} := ⟨hwz, hw2⟩
  rw [hcoset] at hmem
  obtain ⟨d, -, rfl⟩ := hmem
  exact hZ.2 z hz d

theorem XData.exists_mul_centralizer_L (hD : XData Z M L D O u) {l : X} (hl : l ∈ L) :
    ∃ o ∈ O, ∃ c ∈ L, u * c = c * u ∧ l = o * c := by
  rcases hD.eq_one_or_orderOf_eq_two with hu1 | hu2
  · exact ⟨1, O.one_mem, l, hl, by rw [hu1, one_mul, mul_one], (one_mul l).symm⟩
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_centralizer hu2 (hD.O_le.trans hD.D_le)
    (hD.mem_normalizer_O hD.mem) hD.O_odd (fun a ha => hD.comm_L ha) hl
  obtain ⟨hcL, hcu⟩ := Subgroup.mem_inf.mp hc
  exact ⟨n, hn, c, hcL, (Subgroup.mem_centralizer_singleton_iff.mp hcu).symm, rfl⟩

theorem XData.exists_mul_centralizer_D (hD : XData Z M L D O u) {d : X} (hd : d ∈ D) :
    ∃ o ∈ O, ∃ c ∈ D, u * c = c * u ∧ d = o * c := by
  rcases hD.eq_one_or_orderOf_eq_two with hu1 | hu2
  · exact ⟨1, O.one_mem, d, hd, by rw [hu1, one_mul, mul_one], (one_mul d).symm⟩
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_centralizer hu2 hD.O_le
    (hD.mem_normalizer_O hD.mem) hD.O_odd (fun a ha => hD.comm_D ha) hd
  obtain ⟨hcD, hcu⟩ := Subgroup.mem_inf.mp hc
  exact ⟨n, hn, c, hcD, (Subgroup.mem_centralizer_singleton_iff.mp hcu).symm, rfl⟩

theorem XData.exists_mem_Z_centralizer (hD : XData Z M L D O u) (hZ : IsInvariantInvolutionSet Z)
    {z : X} (hz : z ∈ Z) (hzL : z ∈ L) :
    ∃ y ∈ Z, y ∈ L ∧ u * y = y * u ∧ y * z⁻¹ ∈ O := by
  obtain ⟨o, hoO, c, hcL, huc, hzoc⟩ := hD.exists_mul_centralizer_L hzL
  have hz2 : orderOf z = 2 := hZ.1 z hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hcz : c = o⁻¹ * z := by rw [hzoc]; group
  have hcc : c * c ∈ O := by
    have e : c * c = o⁻¹ * (z * o⁻¹ * z⁻¹) * (z * z) := by rw [hcz]; group
    rw [e, hzz, mul_one]
    exact O.mul_mem (O.inv_mem hoO) (hD.conj_mem_O hzL (O.inv_mem hoO))
  have hcO : c ∉ O := by
    intro hc
    refine CFSG.OddInversion.notMem_of_odd_card hD.O_odd hz2 ?_
    rw [hzoc]
    exact O.mul_mem hoO hc
  obtain ⟨y, hy, hy2, hyc⟩ := exists_involution_mem_zpowers_coset hD.O_odd hcc hcO
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyL : y ∈ L := Subgroup.zpowers_le.mpr hcL hy
  have huy : u * y = y * u := by
    rw [← hk]
    exact ((show Commute u c from huc).zpow_right k).eq
  have hyz : y * z⁻¹ ∈ O := by
    have e : y * z⁻¹ = (y * c⁻¹) * o⁻¹ := by rw [hzoc]; group
    rw [e]
    exact O.mul_mem hyc (O.inv_mem hoO)
  exact ⟨y, mem_of_mul_inv_mem_of_involution hZ hD.O_odd hz (hD.mem_normalizer_O hzL) hy2 hyz,
    hyL, huy, hyz⟩

section Hom

variable {K : Type*} [Group K] {φ : ↥D →* K}

omit [Finite X] in
theorem map_eq_one_iff_mem_of_ker (hker : φ.ker = O.subgroupOf D) {a : X} (ha : a ∈ D) :
    φ ⟨a, ha⟩ = 1 ↔ a ∈ O := by
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

omit [Finite X] in
theorem map_eq_map_iff_of_ker (hker : φ.ker = O.subgroupOf D) {a b : X} (ha : a ∈ D) (hb : b ∈ D) :
    φ ⟨a, ha⟩ = φ ⟨b, hb⟩ ↔ a * b⁻¹ ∈ O := by
  rw [← map_eq_one_iff_mem_of_ker hker (D.mul_mem ha (D.inv_mem hb))]
  change _ ↔ φ (⟨a, ha⟩ * ⟨b, hb⟩⁻¹) = 1
  rw [map_mul, map_inv, mul_inv_eq_one]

end Hom

theorem XData.mem_of_involution
    (hD : XData Z M L D O u) (hZ : IsInvariantInvolutionSet Z)
    (hne : ∃ z ∈ Z, z ∈ L) {y : X} (hy2 : y * y = 1) (hyD : ∃ d ∈ D, y = u * d)
    (hyO : ∀ o ∈ O, y ≠ u * o) : y ∈ Z := by
  obtain ⟨z₀, hz₀, hz₀L⟩ := hne
  obtain ⟨⟨dz, hdzD, hz₀d⟩, hz₀O⟩ := hD.zset z₀ hz₀ hz₀L
  obtain ⟨dy, hdyD, hydy⟩ := hyD
  obtain ⟨K, instK, φ, hsurj, hker, hB, -⟩ := hD.bar
  have : Finite K := Finite.of_surjective φ hsurj
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hD.sq
  have key : ∀ (d : X) (hd : d ∈ D), (u * d) * (u * d) = 1 → d ∉ O →
      orderOf (φ ⟨d, hd⟩) = 2 := by
    intro d hd hsq hdO
    have hmem : d * d ∈ O := by
      have hc := hD.comm d hd
      have h1 : u * d * u⁻¹ * d⁻¹ * (d * d) = 1 := by
        calc u * d * u⁻¹ * d⁻¹ * (d * d) = (u * d) * (u⁻¹ * d) := by group
          _ = (u * d) * (u * d) := by rw [hui]
          _ = 1 := hsq
      have h2 : d * d = (u * d * u⁻¹ * d⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact O.inv_mem hc
    have h1 : φ ⟨d, hd⟩ ^ 2 = 1 := by
      rw [pow_two, ← map_mul]
      exact (map_eq_one_iff_mem_of_ker hker (D.mul_mem hd hd)).mpr hmem
    have h2 : φ ⟨d, hd⟩ ≠ 1 := fun h => hdO ((map_eq_one_iff_mem_of_ker hker hd).mp h)
    exact orderOf_eq_prime h1 h2
  have hyy : (u * dy) * (u * dy) = 1 := by rw [← hydy]; exact hy2
  have hz₀2 : orderOf z₀ = 2 := hZ.1 z₀ hz₀
  have hz₀z₀ : z₀ * z₀ = 1 := by rw [← pow_two, ← hz₀2, pow_orderOf_eq_one]
  have hzz : (u * dz) * (u * dz) = 1 := by rw [← hz₀d]; exact hz₀z₀
  have hdyO : dy ∉ O := fun h => hyO dy h hydy
  have hdzO : dz ∉ O := fun h => hz₀O dz h hz₀d
  have hodz := key dz hdzD hzz hdzO
  have hody := key dy hdyD hyy hdyO
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_involutions_of_isBenderGroup hB hodz hody)
  obtain ⟨⟨e, heD⟩, rfl⟩ := hsurj c
  have heL : e ∈ L := hD.D_le heD
  have hedz : e * dz * e⁻¹ ∈ D := D.mul_mem (D.mul_mem heD hdzD) (D.inv_mem heD)
  have hconj : (e * dz * e⁻¹) * dy⁻¹ ∈ O := by
    refine (map_eq_map_iff_of_ker hker hedz hdyD).mp ?_
    have h : φ ⟨e * dz * e⁻¹, hedz⟩ = φ (⟨e, heD⟩ * ⟨dz, hdzD⟩ * ⟨e, heD⟩⁻¹) := rfl
    rw [h, map_mul, map_mul, map_inv]
    exact hc
  obtain ⟨w, hw⟩ : ∃ w, w = e * z₀ * e⁻¹ := ⟨_, rfl⟩
  have hwZ : w ∈ Z := by
    have := hZ.2 z₀ hz₀ e⁻¹
    rwa [inv_inv, ← hw] at this
  have hwL : w ∈ L := by
    rw [hw]
    exact L.mul_mem (L.mul_mem heL hz₀L) (L.inv_mem heL)
  have hwy : w * y⁻¹ ∈ O := by
    have e1 : w * y⁻¹ = (e * u * e⁻¹ * u⁻¹) * (u * ((e * dz * e⁻¹) * dy⁻¹) * u⁻¹) := by
      rw [hw, hz₀d, hydy]
      group
    rw [e1]
    exact O.mul_mem (hD.comm_L heL) (hD.conj_mem_O hD.mem hconj)
  have hy1 : y ≠ 1 := by
    intro h1
    have h3 : u * dy = 1 := by rw [← hydy]; exact h1
    have hdy : dy = u⁻¹ := eq_inv_of_mul_eq_one_right h3
    have huD : u ∈ D := by
      have : u⁻¹ ∈ D := hdy ▸ hdyD
      simpa using this
    have hu1 : u = 1 := by
      have : u ∈ D ⊓ zpowers u := Subgroup.mem_inf.mpr ⟨huD, Subgroup.mem_zpowers u⟩
      rw [hD.inf, Subgroup.mem_bot] at this
      exact this
    apply hdyO
    rw [hdy, hu1, inv_one]
    exact O.one_mem
  have hy2' : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hyw : y * w⁻¹ ∈ O := by
    have e2 : y * w⁻¹ = (w * y⁻¹)⁻¹ := by group
    rw [e2]
    exact O.inv_mem hwy
  exact mem_of_mul_inv_mem_of_involution hZ hD.O_odd hwZ (hD.mem_normalizer_O hwL) hy2' hyw

theorem center_eq_bot_of_isBenderGroup
    {K : Type*} [Group K] [Finite K]
    (hB : CFSG.BenderSuzuki.IsBenderGroup K) : center K = ⊥ := by
  have hsimple := isSimpleGroup_of_isBenderGroup hB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_not_commute_of_isBenderGroup hB
    apply hab
    have ha : a ∈ center K := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem XData.exists_commuting_involutions (hD : XData Z M L D O u) :
    ∃ a ∈ D, ∃ b ∈ D, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a ∧
      u * a = a * u ∧ u * b = b * u := by
  obtain ⟨K, instK, φ, hsurj, hker, hB, -⟩ := hD.bar
  have : Finite K := Finite.of_surjective φ hsurj
  have hrank : 2 ≤ Open.pRank 2 (⊤ : Subgroup K) := two_le_twoRank_of_isBenderGroup hB
  obtain ⟨ka, kb, -, -, hka, hkb, hkne, hkcomm⟩ := exists_commuting_involutions_of_two_le_pRank hrank
  have lift : ∀ k : K, orderOf k = 2 →
      ∃ (a : X) (ha : a ∈ D), orderOf a = 2 ∧ φ ⟨a, ha⟩ = k := by
    intro k hk
    obtain ⟨⟨c, hcD⟩, hck⟩ := hsurj k
    have hk2 : k * k = 1 := by rw [← pow_two, ← hk, pow_orderOf_eq_one]
    have hcc : c * c ∈ O := by
      refine (map_eq_one_iff_mem_of_ker hker (D.mul_mem hcD hcD)).mp ?_
      have h : φ ⟨c * c, D.mul_mem hcD hcD⟩ = φ ⟨c, hcD⟩ * φ ⟨c, hcD⟩ := by
        rw [← map_mul]
        rfl
      rw [h, hck, hk2]
    have hcO : c ∉ O := by
      intro h
      have h1 := (map_eq_one_iff_mem_of_ker hker hcD).mpr h
      rw [hck] at h1
      rw [h1, orderOf_one] at hk
      exact absurd hk (by norm_num)
    obtain ⟨y, hy, hy2, hyc⟩ := exists_involution_mem_zpowers_coset hD.O_odd hcc hcO
    have hyD : y ∈ D := Subgroup.zpowers_le.mpr hcD hy
    exact ⟨y, hyD, hy2, by rw [(map_eq_map_iff_of_ker hker hyD hcD).mpr hyc, hck]⟩
  have lift_comm : ∀ k : K, orderOf k = 2 →
      ∃ (a : X) (ha : a ∈ D), orderOf a = 2 ∧ u * a = a * u ∧ φ ⟨a, ha⟩ = k := by
    intro k hk
    obtain ⟨a₀, ha₀D, ha₀2, ha₀k⟩ := lift k hk
    obtain ⟨b, hbO, hb⟩ := exists_commuting_involution_conj hD.O_odd hD.sq ha₀2
      (hD.mem_normalizer_O hD.mem) (hD.mem_normalizer_O (hD.D_le ha₀D)) (hD.comm a₀ ha₀D)
    have haD : b⁻¹ * a₀ * b ∈ D :=
      D.mul_mem (D.mul_mem (D.inv_mem (hD.O_le hbO)) ha₀D) (hD.O_le hbO)
    refine ⟨b⁻¹ * a₀ * b, haD, ?_, hb, ?_⟩
    · have := orderOf_conj_eq ha₀2 b⁻¹
      rwa [inv_inv] at this
    · rw [← ha₀k]
      refine (map_eq_map_iff_of_ker hker haD ha₀D).mpr ?_
      have e : b⁻¹ * a₀ * b * a₀⁻¹ = b⁻¹ * (a₀ * b * a₀⁻¹) := by group
      rw [e]
      exact O.mul_mem (O.inv_mem hbO) (hD.conj_mem_O (hD.D_le ha₀D) hbO)
  obtain ⟨a, haD, ha2, hua, hak⟩ := lift_comm ka hka
  obtain ⟨b₁, hb₁D, hb₁2, hub₁, hb₁k⟩ := lift_comm kb hkb
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hcua : Commute u a := hua
  have hcub₁ : Commute u b₁ := hub₁
  have hN : Odd (Nat.card ↥(O ⊓ centralizer ({u} : Set X))) :=
    Odd.of_dvd_nat hD.O_odd (Subgroup.card_dvd_of_le inf_le_left)
  have hxN : a ∈ normalizer ((O ⊓ centralizer ({u} : Set X) : Subgroup X) : Set X) :=
    mem_normalizer_inf (hD.mem_normalizer_O (hD.D_le haD))
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hua.symm))
  have hyN : b₁ ∈ normalizer ((O ⊓ centralizer ({u} : Set X) : Subgroup X) : Set X) :=
    mem_normalizer_inf (hD.mem_normalizer_O (hD.D_le hb₁D))
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hub₁.symm))
  have hcommD : a * b₁ * a⁻¹ * b₁⁻¹ ∈ D :=
    D.mul_mem (D.mul_mem (D.mul_mem haD hb₁D) (D.inv_mem haD)) (D.inv_mem hb₁D)
  have hcommO : a * b₁ * a⁻¹ * b₁⁻¹ ∈ O := by
    refine (map_eq_one_iff_mem_of_ker hker hcommD).mp ?_
    have h : φ ⟨a * b₁ * a⁻¹ * b₁⁻¹, hcommD⟩ =
        φ ⟨a, haD⟩ * φ ⟨b₁, hb₁D⟩ * (φ ⟨a, haD⟩)⁻¹ * (φ ⟨b₁, hb₁D⟩)⁻¹ := by
      change φ (⟨a, haD⟩ * ⟨b₁, hb₁D⟩ * ⟨a, haD⟩⁻¹ * ⟨b₁, hb₁D⟩⁻¹) = _
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [h, hak, hb₁k, hkcomm]
    group
  have hxy : a * b₁ * a⁻¹ * b₁⁻¹ ∈ O ⊓ centralizer ({u} : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨hcommO, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have : Commute u (a * b₁ * a⁻¹ * b₁⁻¹) :=
      (((hcua.mul_right hcub₁).mul_right hcua.inv_right).mul_right hcub₁.inv_right)
    exact this.eq.symm
  obtain ⟨n, hn, hnab⟩ := exists_commuting_involution_conj hN haa hb₁2 hxN hyN hxy
  obtain ⟨hnO, hnu⟩ := Subgroup.mem_inf.mp hn
  have hcun : Commute u n := (Subgroup.mem_centralizer_singleton_iff.mp hnu).symm
  have hbD : n⁻¹ * b₁ * n ∈ D :=
    D.mul_mem (D.mul_mem (D.inv_mem (hD.O_le hnO)) hb₁D) (hD.O_le hnO)
  refine ⟨a, haD, n⁻¹ * b₁ * n, hbD, ha2, ?_, ?_, hnab, hua, ?_⟩
  · have := orderOf_conj_eq hb₁2 n⁻¹
    rwa [inv_inv] at this
  · intro hab
    have hφb : φ ⟨n⁻¹ * b₁ * n, hbD⟩ = kb := by
      rw [← hb₁k]
      refine (map_eq_map_iff_of_ker hker hbD hb₁D).mpr ?_
      have e : n⁻¹ * b₁ * n * b₁⁻¹ = n⁻¹ * (b₁ * n * b₁⁻¹) := by group
      rw [e]
      exact O.mul_mem (O.inv_mem hnO) (hD.conj_mem_O (hD.D_le hb₁D) hnO)
    apply hkne
    rw [← hak, ← hφb]
    congr 1
    exact Subtype.ext hab
  · exact (hcun.inv_right.mul_right hcub₁ |>.mul_right hcun).eq

theorem XData.of_central
    (hD : XData Z M L D O u) {u₀ : X} (hu₀L : u₀ ∈ L)
    (hc : ∀ l ∈ L, u₀ * l = l * u₀) (h2 : orderOf u₀ = 2) (hM : u₀ ∈ M) :
    XData Z M L D O u₀ := by
  have hu₀2 : u₀ * u₀ = 1 := by rw [← pow_two, ← h2, pow_orderOf_eq_one]
  obtain ⟨K, instK, φ, hsurj, hker, hB, -⟩ := hD.bar
  have : Finite K := Finite.of_surjective φ hsurj
  have hcen : ∀ (d : X) (hd : d ∈ D), (∀ e ∈ D, d * e * d⁻¹ * e⁻¹ ∈ O) → d ∈ O := by
    intro d hd h
    have hz : φ ⟨d, hd⟩ ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨⟨e, heD⟩, rfl⟩ := hsurj k
      have hmem : d * e * d⁻¹ * e⁻¹ ∈ D :=
        D.mul_mem (D.mul_mem (D.mul_mem hd heD) (D.inv_mem hd)) (D.inv_mem heD)
      have h1 := (map_eq_one_iff_mem_of_ker hker hmem).mpr (h e heD)
      change φ (⟨d, hd⟩ * ⟨e, heD⟩ * ⟨d, hd⟩⁻¹ * ⟨e, heD⟩⁻¹) = 1 at h1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h3 : φ ⟨d, hd⟩ * φ ⟨e, heD⟩ = φ ⟨e, heD⟩ * φ ⟨d, hd⟩ := by
        rw [mul_inv_eq_one] at h1
        exact mul_inv_eq_iff_eq_mul.mp h1
      exact h3.symm
    rw [center_eq_bot_of_isBenderGroup hB, Subgroup.mem_bot] at hz
    exact (map_eq_one_iff_mem_of_ker hker hd).mp hz
  have hnorm : ∀ x ∈ D, u * x * u⁻¹ ∈ D := fun x hx =>
    hD.D_norm u (Subgroup.le_normalizer hD.mem) x hx
  have hu₀sup : u₀ ∈ D ⊔ zpowers u := hD.sup ▸ hu₀L
  rcases mem_sup_zpowers_of_involution hD.sq hnorm hu₀sup with hu₀D | hu₀uD
  · exfalso
    have hO : u₀ ∈ O := by
      refine hcen u₀ hu₀D fun e he => ?_
      have h := hc e (hD.D_le he)
      have e1 : u₀ * e * u₀⁻¹ * e⁻¹ = 1 := by rw [h]; group
      rw [e1]
      exact O.one_mem
    exact CFSG.OddInversion.notMem_of_odd_card hD.O_odd h2 hO
  · refine hD.of_mem_coset hu₀L hM hu₀2 ?_
    rw [inv_eq_of_mul_eq_one_right hD.sq]
    refine hcen _ hu₀uD fun e he => ?_
    have h := hc (u * e * u⁻¹)
      (L.mul_mem (L.mul_mem hD.mem (hD.D_le he)) (L.inv_mem hD.mem))
    have e1 : (u₀ * u) * e * (u₀ * u)⁻¹ * e⁻¹ = u * e * u⁻¹ * e⁻¹ :=
      calc (u₀ * u) * e * (u₀ * u)⁻¹ * e⁻¹ = (u₀ * (u * e * u⁻¹)) * u₀⁻¹ * e⁻¹ := by group
        _ = ((u * e * u⁻¹) * u₀) * u₀⁻¹ * e⁻¹ := by rw [h]
        _ = u * e * u⁻¹ * e⁻¹ := by group
    rw [e1]
    exact hD.comm e he

end Structure

end CFSG.GH74.Uniqueness
