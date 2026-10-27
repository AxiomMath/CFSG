module

public import CFSG.CGT.Foote81L6.MainRank

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

@[expose] def zred (b : ℕ) : ZMod (2 ^ (b + 1)) →+* ZMod (2 ^ b) :=
  ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ b)) (ZMod (2 ^ b))

theorem zred_natCast (b k : ℕ) : zred b k = k := map_natCast _ k

theorem zred_surjective (b : ℕ) : Function.Surjective (zred b) := by
  intro x
  haveI : NeZero (2 ^ b) := ⟨by positivity⟩
  exact ⟨(x.val : ZMod (2 ^ (b + 1))), by rw [zred_natCast, ZMod.natCast_zmod_val]⟩

theorem zred_eq_zero_iff (b : ℕ) {i : ZMod (2 ^ (b + 1))} :
    zred b i = 0 ↔ i = 0 ∨ i = ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) := by
  haveI : NeZero (2 ^ (b + 1)) := ⟨by positivity⟩
  constructor
  · intro h
    have hv : zred b (i.val : ZMod (2 ^ (b + 1))) = 0 := by rwa [ZMod.natCast_zmod_val]
    rw [zred_natCast, ZMod.natCast_eq_zero_iff] at hv
    obtain ⟨c, hc⟩ := hv
    have hlt : i.val < 2 ^ (b + 1) := ZMod.val_lt i
    have hc2 : c < 2 := by
      by_contra hcon
      have : 2 ^ b * 2 ≤ 2 ^ b * c := Nat.mul_le_mul_left _ (by omega)
      rw [← hc, ← pow_succ] at this
      omega
    interval_cases c
    · left
      rw [← ZMod.natCast_zmod_val i, hc, mul_zero, Nat.cast_zero]
    · right
      rw [← ZMod.natCast_zmod_val i, hc, mul_one]
  · rintro (rfl | rfl)
    · exact map_zero _
    · rw [zred_natCast, ZMod.natCast_self]

@[expose] def dihedralReduce (b : ℕ) : DihedralGroup (2 ^ (b + 1)) →* DihedralGroup (2 ^ b) where
  toFun g := match g with
    | r i => r (zred b i)
    | sr i => sr (zred b i)
  map_one' := by
    rw [one_def, one_def]
    show r (zred b 0) = r 0
    rw [map_zero]
  map_mul' g h := by
    rcases g with i | i <;> rcases h with j | j
    · rw [r_mul_r]
      show r (zred b (i + j)) = r (zred b i) * r (zred b j)
      rw [r_mul_r, map_add]
    · rw [r_mul_sr]
      show sr (zred b (j - i)) = r (zred b i) * sr (zred b j)
      rw [r_mul_sr, map_sub]
    · rw [sr_mul_r]
      show sr (zred b (i + j)) = sr (zred b i) * r (zred b j)
      rw [sr_mul_r, map_add]
    · rw [sr_mul_sr]
      show r (zred b (j - i)) = sr (zred b i) * sr (zred b j)
      rw [sr_mul_sr, map_sub]

@[simp] theorem dihedralReduce_r (b : ℕ) (i : ZMod (2 ^ (b + 1))) :
    dihedralReduce b (r i) = r (zred b i) := rfl

@[simp] theorem dihedralReduce_sr (b : ℕ) (i : ZMod (2 ^ (b + 1))) :
    dihedralReduce b (sr i) = sr (zred b i) := rfl

theorem dihedralReduce_surjective (b : ℕ) : Function.Surjective (dihedralReduce b) := by
  rintro (j | j)
  · obtain ⟨i, rfl⟩ := zred_surjective b j
    exact ⟨r i, rfl⟩
  · obtain ⟨i, rfl⟩ := zred_surjective b j
    exact ⟨sr i, rfl⟩

theorem dihedralReduce_eq_one_iff (b : ℕ) {g : DihedralGroup (2 ^ (b + 1))} :
    dihedralReduce b g = 1 ↔ g = 1 ∨ g = zc (b + 1) := by
  have hzc : zc (b + 1) = r ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) := by
    rw [← rho_pow (by omega : 1 ≤ b + 1), r_pow, one_mul, Nat.add_sub_cancel]
  rcases g with i | i
  · rw [dihedralReduce_r, one_def, one_def, hzc]
    constructor
    · intro h
      rcases (zred_eq_zero_iff b).1 (r.inj h) with h0 | h1
      · exact Or.inl (by rw [h0])
      · exact Or.inr (by rw [h1])
    · rintro (h | h)
      · rw [r.inj h, map_zero]
      · rw [r.inj h, (zred_eq_zero_iff b).2 (Or.inr rfl)]
  · rw [dihedralReduce_sr, one_def, one_def, hzc]
    constructor
    · intro h
      cases h
    · rintro (h | h) <;> cases h

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem isConj_or_isConj_mul_of_isConj_mk_sup {O : Subgroup G} [O.Normal]
    (hO : Odd (Nat.card O)) {a : G} (ha2 : a * a = 1) (haO : ∀ g : G, g * a * g⁻¹ * a⁻¹ ∈ O)
    {M : Subgroup G} [M.Normal] (hM : M = O ⊔ zpowers a) {x y : G}
    (hx : ∃ k : ℕ, x ^ (2 ^ k) = 1) (hy : ∃ k : ℕ, y ^ (2 ^ k) = 1) (hya : y * a = a * y)
    (hxy : IsConj (QuotientGroup.mk x : G ⧸ M) (QuotientGroup.mk y)) :
    IsConj x y ∨ IsConj x (y * a) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hxy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at hg
  set x' := g * x * g⁻¹ with hx'
  set Y : Subgroup G := zpowers y ⊔ zpowers a
  have hcYa : ∀ u ∈ zpowers y, ∀ v ∈ zpowers a, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
    exact ((Commute.zpow_left hya i).zpow_right j).eq
  have hYab : ∀ u ∈ Y, ∀ v ∈ Y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcYa)).1 hu
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcYa)).1 hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu₁
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu₂
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hv₁
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hv₂
    have h1 := (Commute.zpow_zpow hya.symm j k).eq
    have h2 := (Commute.zpow_zpow hya i l).eq
    calc y ^ i * a ^ j * (y ^ k * a ^ l) = y ^ i * (a ^ j * y ^ k) * a ^ l := by group
      _ = y ^ i * (y ^ k * a ^ j) * a ^ l := by rw [← h1]
      _ = y ^ k * (y ^ i * a ^ j) * a ^ l := by
          rw [← mul_assoc, ← mul_assoc, ← zpow_add, ← zpow_add, add_comm]
      _ = y ^ k * (y ^ i * (a ^ j * a ^ l)) := by group
      _ = y ^ k * (y ^ i * (a ^ l * a ^ j)) := by rw [← zpow_add, ← zpow_add, add_comm]
      _ = y ^ k * ((y ^ i * a ^ l) * a ^ j) := by group
      _ = y ^ k * ((a ^ l * y ^ i) * a ^ j) := by rw [h2]
      _ = y ^ k * a ^ l * (y ^ i * a ^ j) := by group
  obtain ⟨k₁, hk₁⟩ := hy
  have hY2 : IsPGroup 2 Y := by
    rintro ⟨u, hu⟩
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcYa)).1 hu
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu₁
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu₂
    refine ⟨k₁ + 1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    have hc : Commute (y ^ i) (a ^ j) := (Commute.zpow_zpow hya i j)
    rw [hc.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i,
      mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    have h1 : y ^ (2 ^ (k₁ + 1)) = 1 := by rw [pow_succ, pow_mul, hk₁, one_pow]
    have h2 : a ^ (2 ^ (k₁ + 1)) = 1 := by
      rw [pow_succ', pow_mul, sq, ha2, one_pow]
    rw [h1, h2, one_zpow, one_zpow, one_mul]
  set L : Subgroup G := O ⊔ Y
  have hOY : O ⊓ Y = ⊥ := by
    have hcop : Nat.Coprime (Nat.card O) (Nat.card Y) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY2
      rw [hk]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hO)
    exact Subgroup.inf_eq_bot_of_coprime hcop
  have hYL : Y ≤ L := le_sup_right
  have hcardL : Nat.card L = Nat.card O * Nat.card Y :=
    card_sup_of_le_normalizer (by rw [normalizer_eq_top]; exact le_top) hOY
  have hindex : ¬ 2 ∣ (Y.subgroupOf L).index := by
    have h := card_mul_index (Y.subgroupOf L)
    rw [hcardL, Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv] at h
    have hY0 : 0 < Nat.card Y := Nat.card_pos
    have : (Y.subgroupOf L).index = Nat.card O := by
      have := h
      rw [mul_comm (Nat.card O)] at this
      exact Nat.eq_of_mul_eq_mul_left hY0 this
    rw [this]
    exact Odd.not_two_dvd_nat hO
  have hY2' : IsPGroup 2 (Y.subgroupOf L) := hY2.comap_subtype
  set SY : Sylow 2 L := hY2'.toSylow hindex
  have hMle : M ≤ L := by
    rw [hM]
    exact sup_le le_sup_left (le_sup_of_le_right le_sup_right)
  have hx'L : x' ∈ L := by
    have h1 : x'⁻¹ * y ∈ M := hg
    have : x' = y * (x'⁻¹ * y)⁻¹ := by group
    rw [this]
    exact mul_mem (hYL (mem_sup_left (mem_zpowers y))) (inv_mem (hMle h1))
  have hx'2 : IsPGroup 2 (zpowers (⟨x', hx'L⟩ : L)) := by
    obtain ⟨k, hk⟩ := hx
    rintro ⟨u, hu⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx']
    have : (g * x * g⁻¹) ^ (2 ^ k) = 1 := by rw [conj_pow, hk, mul_one, mul_inv_cancel]
    rw [this, one_zpow]
  obtain ⟨c, hc⟩ := exists_conj_mem_of_isPGroup SY hx'2
  have hw := hc _ (mem_zpowers _)
  have hwY : (c : G) * x' * (c : G)⁻¹ ∈ Y := by
    have := hw
    rw [show (SY : Subgroup L) = Y.subgroupOf L from IsPGroup.toSylow_coe _ _,
      mem_subgroupOf] at this
    simpa using this
  have hm : x'⁻¹ * y ∈ O ⊔ zpowers a := hM ▸ hg
  obtain ⟨o, ho, w, hw', how⟩ := (mem_sup_iff_of_le_normalizer
    (by rw [normalizer_eq_top]; exact le_top : zpowers a ≤ normalizer (O : Set G))).1 hm
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw'
  have hj : a ^ j = 1 ∨ a ^ j = a := by
    rw [zpow_eq_zpow_emod' j (show a ^ 2 = 1 by rw [sq]; exact ha2)]
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
  obtain ⟨o', ho', y', hy', hcoy⟩ := (mem_sup_iff_of_le_normalizer
    (by rw [normalizer_eq_top]; exact le_top : Y ≤ normalizer (O : Set G))).1 c.2
  have hyaY : y * (a ^ j)⁻¹ ∈ Y :=
    mul_mem (mem_sup_left (mem_zpowers y)) (inv_mem (mem_sup_right (zpow_mem (mem_zpowers a) j)))
  have hx'eq : x' = y * (a ^ j)⁻¹ * o⁻¹ := by
    have : x'⁻¹ = o * a ^ j * y⁻¹ := by
      calc x'⁻¹ = x'⁻¹ * y * y⁻¹ := by group
        _ = o * a ^ j * y⁻¹ := by rw [how]
    calc x' = (x'⁻¹)⁻¹ := by group
      _ = y * (a ^ j)⁻¹ * o⁻¹ := by rw [this]; group
  have hyc : y' * (y * (a ^ j)⁻¹) = (y * (a ^ j)⁻¹) * y' := hYab _ hy' _ hyaY
  have hdiff : ((c : G) * x' * (c : G)⁻¹) * (y * (a ^ j)⁻¹)⁻¹ ∈ O ⊓ Y := by
    refine mem_inf.2 ⟨?_, mul_mem hwY (inv_mem hyaY)⟩
    rw [hcoy, hx'eq]
    have e : o' * y' * (y * (a ^ j)⁻¹ * o⁻¹) * (o' * y')⁻¹ * (y * (a ^ j)⁻¹)⁻¹ =
        o' * ((y * (a ^ j)⁻¹) * ((y' * o⁻¹ * y'⁻¹) * o'⁻¹) * (y * (a ^ j)⁻¹)⁻¹) := by
      calc o' * y' * (y * (a ^ j)⁻¹ * o⁻¹) * (o' * y')⁻¹ * (y * (a ^ j)⁻¹)⁻¹
          = o' * (y' * (y * (a ^ j)⁻¹)) * o⁻¹ * y'⁻¹ * o'⁻¹ * (y * (a ^ j)⁻¹)⁻¹ := by group
        _ = o' * ((y * (a ^ j)⁻¹) * y') * o⁻¹ * y'⁻¹ * o'⁻¹ * (y * (a ^ j)⁻¹)⁻¹ := by rw [hyc]
        _ = o' * ((y * (a ^ j)⁻¹) * ((y' * o⁻¹ * y'⁻¹) * o'⁻¹) * (y * (a ^ j)⁻¹)⁻¹) := by group
    rw [e]
    refine mul_mem ho' ((inferInstance : O.Normal).conj_mem _ (mul_mem
      ((inferInstance : O.Normal).conj_mem _ (inv_mem ho) _) (inv_mem ho')) _)
  rw [hOY, mem_bot] at hdiff
  have hfinal : (c : G) * g * x * ((c : G) * g)⁻¹ = y * (a ^ j)⁻¹ := by
    have := mul_inv_eq_one.1 hdiff
    rw [← this, hx']
    group
  rcases hj with h1 | h1
  · left
    rw [h1, inv_one, mul_one] at hfinal
    exact isConj_iff.2 ⟨(c : G) * g, hfinal⟩
  · right
    rw [h1, inv_eq_of_mul_eq_one_right ha2] at hfinal
    exact isConj_iff.2 ⟨(c : G) * g, hfinal⟩

end Lift

end CFSG.CGT.Foote81L6
