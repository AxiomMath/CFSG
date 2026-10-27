module

public import CFSG.GroupTheory.WielandtProductLocal

public section

namespace CFSG.GroupTheory.WielandtProduct

open Subgroup
open scoped Pointwise

namespace MinCounter

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G} (h : MinCounter G A B)
include h

theorem zpowers_eq_of_mem_normalizer {x y : G} (hxA : x ∈ A) (hxN : x ∈ normalizer (B : Set G))
    (hyA : y ∈ A) (hyN : y ∈ normalizer (B : Set G)) {p : ℕ} (hp : p.Prime)
    (hx : orderOf x = p) (hy : orderOf y = p) : zpowers x = zpowers y := by
  have := h.nilA
  have := h.nilB
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have := isNilpotent_of_le (inf_le_left : A ⊓ normalizer (B : Set G) ≤ A)
  have hxS : x ∈ sylowOf (A ⊓ normalizer (B : Set G)) p := mem_sylowOf_of_orderOf_eq ⟨hxA, hxN⟩ hx
  have hyS : y ∈ sylowOf (A ⊓ normalizer (B : Set G)) p := mem_sylowOf_of_orderOf_eq ⟨hyA, hyN⟩ hy
  have hx1 : x ≠ 1 := fun h1 => hp.one_lt.ne' (by rw [← hx, h1, orderOf_one])
  have hSb : sylowOf (A ⊓ normalizer (B : Set G)) p ≠ ⊥ := fun hb => hx1 (by
    rw [hb, mem_bot] at hxS
    exact hxS)
  obtain ⟨z, hzS, hzo, hzc⟩ := exists_orderOf_eq_commute_of_isPGroup isPGroup_sylowOf hSb
  obtain ⟨u, huS, huo, hune⟩ : ∃ u ∈ sylowOf (A ⊓ normalizer (B : Set G)) p,
      orderOf u = p ∧ zpowers u ≠ zpowers z := by
    by_cases hxz : zpowers x = zpowers z
    · exact ⟨y, hyS, hy, fun hyz => hne (hxz.trans hyz.symm)⟩
    · exact ⟨x, hxS, hx, hxz⟩
  have huAN := sylowOf_le huS
  have hzAN := sylowOf_le hzS
  have huz : Commute u z := (hzc u huS).symm
  have hzu : z ∉ zpowers u := by
    intro hz
    apply hune
    have hle : zpowers z ≤ zpowers u := zpowers_le.mpr hz
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, hzo])).symm
  have hnorm : ∀ c ∈ normalizer (B : Set G), c ∈ normalizer ((zOf B : Subgroup G) : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro w
    rw [mem_zOf, mem_zOf]
    constructor
    · rintro ⟨hwB, hwc⟩
      refine ⟨(mem_normalizer_iff.mp hc w).mp hwB, fun v hv => ?_⟩
      have hv' : c⁻¹ * v * c ∈ B := by
        have := (mem_normalizer_iff.mp (inv_mem hc) v).mp hv
        simpa using this
      have := (hwc _ hv').map (MulAut.conj c)
      simpa [MulAut.conj_apply, mul_assoc] using this
    · rintro ⟨hwB, hwc⟩
      refine ⟨(mem_normalizer_iff.mp hc w).mpr hwB, fun v hv => ?_⟩
      have hv' : c * v * c⁻¹ ∈ B := (mem_normalizer_iff.mp hc v).mp hv
      have := (hwc _ hv').map (MulAut.conj c⁻¹)
      simpa [MulAut.conj_apply, mul_assoc] using this
  have huV := hnorm u huAN.2
  have hzV := hnorm z hzAN.2
  let : CommGroup (zOf B) :=
    { (inferInstance : Group (zOf B)) with
      mul_comm := fun v w => Subtype.ext ((mem_zOf.mp v.2).2 w (mem_zOf.mp w.2).1).eq }
  let φ := normalizerConj (zOf B)
  have hcop : Nat.Coprime p (Nat.card (zOf B)) := by
    have hpA : p ∣ Nat.card A := hx ▸ Subgroup.orderOf_dvd_natCard A hxA
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => h.not_dvd_right hp hpA
      (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hαβ : Commute (φ ⟨u, huV⟩) (φ ⟨z, hzV⟩) :=
    (show Commute (⟨u, huV⟩ : normalizer _) ⟨z, hzV⟩ from Subtype.ext huz.eq).map φ
  have hpow : ∀ c : normalizer ((zOf B : Subgroup G) : Set G), (c : G) ^ p = 1 → φ c ^ p = 1 := by
    intro c hc
    rw [← map_pow]
    have : c ^ p = 1 := Subtype.ext (by simpa using hc)
    rw [this, map_one]
  have hα := hpow ⟨u, huV⟩ (by rw [← huo, pow_orderOf_eq_one])
  have hβ := hpow ⟨z, hzV⟩ (by rw [← hzo, pow_orderOf_eq_one])
  have hfpf : ∀ i j : ℕ, i < p → j < p → (i ≠ 0 ∨ j ≠ 0) → ∀ w : zOf B,
      (φ ⟨u, huV⟩ ^ i * φ ⟨z, hzV⟩ ^ j) w = w → w = 1 := by
    intro i j hi hj hij w hw
    rw [← map_pow, ← map_pow, ← map_mul] at hw
    have hw' := congrArg Subtype.val hw
    rw [coe_normalizerConj_apply] at hw'
    have hc : (((⟨u, huV⟩ : normalizer _) ^ i * ⟨z, hzV⟩ ^ j : normalizer _) : G) =
        u ^ i * z ^ j := by simp
    rw [hc] at hw'
    by_contra hw1
    have hw1' : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
    have hC := h.symm.centralizer_eq w.2 hw1'
    have hcB : u ^ i * z ^ j ∈ B := by
      rw [← hC, mem_centralizer_singleton_iff]
      calc u ^ i * z ^ j * w = u ^ i * z ^ j * w * (u ^ i * z ^ j)⁻¹ * (u ^ i * z ^ j) := by
            group
        _ = w * (u ^ i * z ^ j) := by rw [hw']
    have hcA : u ^ i * z ^ j ∈ A := A.mul_mem (pow_mem huAN.1 i) (pow_mem hzAN.1 j)
    have hc1 : u ^ i * z ^ j = 1 := by
      have hm : u ^ i * z ^ j ∈ A ⊓ B := ⟨hcA, hcB⟩
      rwa [h.inf_eq_bot, mem_bot] at hm
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      have hi0 : i ≠ 0 := hij.resolve_right (by simp)
      rw [pow_zero, mul_one] at hc1
      exact pow_ne_one_of_lt_orderOf hi0 (huo ▸ hi) hc1
    · have hzj : z ^ j ∈ zpowers u := by
        have : z ^ j = (u ^ i)⁻¹ := eq_inv_of_mul_eq_one_right hc1
        rw [this]
        exact inv_mem (pow_mem (mem_zpowers u) i)
      have hzz : z ∈ zpowers (z ^ j) := by
        rw [mem_zpowers_pow_iff, hzo]
        exact Nat.Coprime.gcd_eq_one
          ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hj0 hj)).symm
      exact hzu (zpowers_le.mpr hzj hzz)
  have hV1 := eq_one_of_fixedPointFree_sq hp hcop _ _ hαβ hα hβ hfpf
  obtain ⟨r, hr, hrB⟩ := Nat.exists_prime_and_dvd fun h1 =>
    h.ne_bot_right (Subgroup.card_eq_one.mp h1)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hbZ, hbo⟩ := h.symm.exists_mem_zOf_orderOf hrB
  have hb1 := congrArg Subtype.val (hV1 ⟨b, hbZ⟩)
  have : b = 1 := hb1
  exact hr.one_lt.ne' (by rw [← hbo, this, orderOf_one])

theorem index_subgroupOf_normalizer_dvd :
    (A.subgroupOf (normalizer (A : Set G))).index ∣ Nat.card B := by
  have hfac := factorized_of_le h.mul (le_normalizer : A ≤ normalizer (A : Set G))
  set NA := normalizer (A : Set G)
  have hAn : (A.subgroupOf NA).Normal := normal_in_normalizer
  let f := QuotientGroup.mk' (A.subgroupOf NA)
  have hsurj : ((B ⊓ NA).subgroupOf NA).map f = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨a, ⟨ha, haN⟩, b, ⟨hb, hbN⟩, hy⟩ := hfac y y.2
    refine ⟨⟨b, hbN⟩, ⟨hb, hbN⟩, ?_⟩
    have hyab : y = ⟨a, haN⟩ * ⟨b, hbN⟩ := Subtype.ext hy
    rw [hyab, map_mul]
    have : f ⟨a, haN⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [this, one_mul]
  have h1 : Nat.card (NA ⧸ A.subgroupOf NA) ∣ Nat.card ((B ⊓ NA).subgroupOf NA) := by
    have := Subgroup.card_map_dvd ((B ⊓ NA).subgroupOf NA) f
    rwa [hsurj, Subgroup.card_top] at this
  have h2 : Nat.card ((B ⊓ NA).subgroupOf NA) ∣ Nat.card B := by
    rw [card_subgroupOf_eq]
    exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
  rw [Subgroup.index_eq_card]
  exact h1.trans h2

theorem mem_normalizer_of_mem_inf_conj {x g : G} (hxA : x ∈ A)
    (hxN : x ∈ normalizer (B : Set G)) (hx1 : x ≠ 1) (hgx : g⁻¹ * x * g ∈ A) :
    g ∈ normalizer (A : Set G) := by
  have := h.nilA
  have := h.nilB
  have := h.isSimpleGroup
  obtain ⟨k, hk⟩ := exists_pow_prime_orderOf hx1
  have : Fact (orderOf (x ^ k)).Prime := ⟨hk⟩
  set a := x ^ k with ha_def
  have haA : a ∈ A := pow_mem hxA k
  have haN : a ∈ normalizer (B : Set G) := pow_mem hxN k
  have ha1 : a ≠ 1 := fun h1 => hk.one_lt.ne' (by rw [h1, orderOf_one])
  have hga : g⁻¹ * a * g ∈ A := by
    have hconj : g⁻¹ * x ^ k * g = (g⁻¹ * x * g) ^ k := by
      have := conj_pow (a := g⁻¹) (b := x) (i := k)
      simpa using this.symm
    rw [ha_def, hconj]
    exact pow_mem hgx k
  have hpA : orderOf a ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A haA
  have haP : a ∈ sylowOf A (orderOf a) := mem_sylowOf_of_orderOf_eq haA rfl
  obtain ⟨r, hr, hrA, hrp⟩ := h.exists_prime_ne hk
  have : Fact r.Prime := ⟨hr⟩
  have hHN : zpowers a ≤ normalizer (B : Set G) := zpowers_le.mpr haN
  have hfac : ∀ y ∈ normalizer ((zpowers a : Subgroup G) : Set G),
      ∃ a' ∈ A ⊓ normalizer ((zpowers a : Subgroup G) : Set G),
      ∃ b ∈ B ⊓ normalizer ((zpowers a : Subgroup G) : Set G), y = a' * b := by
    refine factorized_normalizer h.mul fun a' ha' b hb hab => ?_
    have hdA : a'⁻¹ * a * a' ∈ A := A.mul_mem (A.mul_mem (A.inv_mem ha') haA) ha'
    have hbd : b⁻¹ * (a'⁻¹ * a * a') * b ∈ zpowers a := by
      have := (mem_normalizer_iff.mp hab (b⁻¹ * (a'⁻¹ * a * a') * b)).mpr
      apply this
      have e : a' * b * (b⁻¹ * (a'⁻¹ * a * a') * b) * (a' * b)⁻¹ = a := by group
      rw [e]
      exact mem_zpowers a
    have hdN : a'⁻¹ * a * a' ∈ normalizer (B : Set G) := by
      have h1 := mul_mem (mul_mem (le_normalizer hb) (hHN hbd)) (le_normalizer (inv_mem hb))
      have e : b * (b⁻¹ * (a'⁻¹ * a * a') * b) * b⁻¹ = a'⁻¹ * a * a' := by group
      rwa [e] at h1
    have hdo : orderOf (a'⁻¹ * a * a') = orderOf a := by
      have := orderOf_injective (MulAut.conj a'⁻¹).toMonoidHom (MulAut.conj a'⁻¹).injective a
      simpa using this
    have hHd := h.zpowers_eq_of_mem_normalizer hdA hdN haA haN hk hdo rfl
    intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hHd ▸ mem_zpowers a : a ∈ zpowers (a'⁻¹ * a * a'))
    have e1 : a' * a * a'⁻¹ = a ^ m := by
      calc a' * a * a'⁻¹ = a' * (a'⁻¹ * a * a') ^ m * a'⁻¹ := by rw [hm]
        _ = (a' * (a'⁻¹ * a * a') * a'⁻¹) ^ m := (conj_zpow).symm
        _ = a ^ m := by group
    rw [show a' * a ^ n * a'⁻¹ = (a' * a * a'⁻¹) ^ n from (conj_zpow).symm, e1]
    exact zpow_mem (zpow_mem (mem_zpowers a) m) n
  have hK : normalizer ((zpowers a : Subgroup G) : Set G) ≠ ⊤ :=
    h.normalizer_ne_top (fun hb => ha1 (zpowers_eq_bot.mp hb)) (Or.inl (zpowers_le.mpr haA))
  have hsolv := h.isSolvable_of_factorized hK hfac
  set K := normalizer ((zpowers a : Subgroup G) : Set G) with hKdef
  have hPK : sylowOf A r ≤ K := by
    intro y hy
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((commute_of_mem_sylowOf_of_ne (A := A) hrp hy haP).zpow_right n).eq.symm
  have hQ : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → sylowOf B q ⊓ K ≤ normalizer (A : Set G) := by
    intro q hq hqB
    have : Fact q.Prime := ⟨hq⟩
    have hrq : r ≠ q := fun he => h.not_dvd_right hr hrA (he ▸ hqB)
    have hsw := h.swap_of_factorized hK hfac hrA hqB
    have hPX : sylowOf A r ≤ (sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) :=
      le_sup_of_le_left (le_inf le_rfl hPK)
    have hXK : (sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) ≤ K := sup_le inf_le_right inf_le_right
    have hXs : Group.IsSolvable ((sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXK)
    obtain ⟨z, hzP, -, hz1, -⟩ := h.exists_mem_sylowOf_zOf hrA
    have hXb : (⊤ : Subgroup ((sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) : Subgroup G)) ≠ ⊥ := by
      intro h0
      have hm := mem_top (⟨z, hPX hzP⟩ : ((sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) : Subgroup G))
      rw [h0, mem_bot] at hm
      exact hz1 (congrArg Subtype.val hm)
    obtain ⟨N', hN'n, hN'b, -, s, hs, hN's⟩ := exists_isPGroup_normal_le hXs inferInstance hXb
    have : Fact s.Prime := ⟨hs⟩
    set N := N'.map ((sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K)).subtype with hNdef
    have hNX : N ≤ (sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) := map_subtype_le N'
    have hXN : (sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) ≤ normalizer (N : Set G) := by
      intro x hx
      have hxn : (⟨x, hx⟩ : ((sylowOf A r ⊓ K) ⊔ (sylowOf B q ⊓ K) : Subgroup G)) ∈
          normalizer ((N' : Subgroup _) : Set _) := by
        rw [normalizer_eq_top_iff.mpr hN'n]
        exact mem_top _
      exact mem_normalizer_map_subtype hxn
    have hNb : N ≠ ⊥ := fun hb =>
      hN'b ((map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hb)
    rcases le_or_le_of_isPGroup hrq (isPGroup_sylowOf.to_le inf_le_left)
        (isPGroup_sylowOf.to_le inf_le_left) hsw hNX hXN (hN's.map _) hNb with hNP | hNQ
    · obtain ⟨n, hnN, hn1, hnc⟩ := exists_mem_commute_of_le_of_isPGroup
        (isPGroup_sylowOf (A := A) (p := r)) (hNP.trans inf_le_left) (hPX.trans hXN) hNb
      have hnP : n ∈ sylowOf A r := (hNP hnN).1
      have hnZ : n ∈ zOf A := mem_zOf.2 ⟨sylowOf_le hnP, fun y hy =>
        (mem_centralizer_singleton_iff.mp (le_centralizer_of_mem_sylowOf hnP hnc hy)).symm⟩
      intro y hy
      have hyN : y * n * y⁻¹ ∈ N :=
        (mem_normalizer_iff.mp (hXN (mem_sup_right hy)) n).mp hnN
      have hyA : y * n * y⁻¹ ∈ A := sylowOf_le (hNP hyN).1
      have := h.mem_normalizer_of_mem_zOf_conj (g := y⁻¹) hnZ hn1 (by simpa using hyA)
      simpa using inv_mem this
    · exfalso
      obtain ⟨t, ht, htB, htq⟩ := h.symm.exists_prime_ne hq
      have : Fact t.Prime := ⟨ht⟩
      have hle : sylowOf A r ⊔ sylowOf B t ≤ normalizer (N : Set G) :=
        sup_le (hPX.trans hXN) (h.symm.sylowOf_le_normalizer htq (hNQ.trans inf_le_left))
      exact h.normalizer_ne_top hNb (Or.inr (hNQ.trans (inf_le_left.trans sylowOf_le)))
        (top_le_iff.mp ((h.sylowOf_sup_sylowOf hrA htB) ▸ hle))
  have hBK : B ⊓ K ≤ normalizer (A : Set G) := by
    have := isNilpotent_of_le (inf_le_left : B ⊓ K ≤ B)
    refine le_of_forall_sylowOf_le fun q hq => ?_
    have : Fact q.Prime := ⟨hq⟩
    rw [sylowOf_inf]
    by_cases hqB : q ∣ Nat.card B
    · exact hQ q hq hqB
    · have hc := WielandtProduct.card_sylowOf (A := B) (p := q)
      rw [Nat.factorization_eq_zero_of_not_dvd hqB, pow_zero, Subgroup.card_eq_one] at hc
      rw [hc, bot_inf_eq]
      exact bot_le
  have hKN : K ≤ normalizer (A : Set G) := by
    intro y hy
    obtain ⟨a₁, ⟨ha₁, -⟩, b₁, hb₁, rfl⟩ := hfac y hy
    exact mul_mem (le_normalizer ha₁) (hBK hb₁)
  set W : Subgroup G := (zOf A).map (MulAut.conj g).toMonoidHom with hWdef
  have hWK : W ≤ K := by
    rintro _ ⟨w, hw, rfl⟩
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro v hv
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hv
    have hc : Commute w (g⁻¹ * a * g) := (mem_zOf.mp hw).2 _ hga
    have hc' : Commute (g * w * g⁻¹) a := by
      have := hc.map (MulAut.conj g)
      simpa [MulAut.conj_apply, mul_assoc] using this
    have := (hc'.zpow_right n).eq.symm
    simpa [MulAut.conj_apply] using this
  have hWNA : W ≤ normalizer (A : Set G) := hWK.trans hKN
  have hAn : (A.subgroupOf (normalizer (A : Set G))).Normal := normal_in_normalizer
  have hcop : Nat.Coprime (Nat.card (W.subgroupOf (normalizer (A : Set G))))
      (A.subgroupOf (normalizer (A : Set G))).index := by
    have h1 : Nat.card (W.subgroupOf (normalizer (A : Set G))) ∣ Nat.card A := by
      rw [card_subgroupOf_eq, inf_eq_left.mpr hWNA, hWdef,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.of_dvd h1 h.index_subgroupOf_normalizer_dvd h.cop
  have hWA : W ≤ A := by
    intro w hw
    exact le_of_coprime_index hcop (show (⟨w, hWNA hw⟩ : normalizer (A : Set G)) ∈
      W.subgroupOf (normalizer (A : Set G)) from hw)
  obtain ⟨z, hzZ, hzo⟩ := h.exists_mem_zOf_orderOf hpA
  have hz1 : z ≠ 1 := fun h1 => hk.one_lt.ne' (by rw [← hzo, h1, orderOf_one])
  refine h.mem_normalizer_of_conj_mem_zOf (x := g * z * g⁻¹) (hWA ⟨z, hzZ, rfl⟩) ?_ ?_
  · intro h1
    apply hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h1]
    group
  · have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [this]
    exact hzZ

theorem mem_normalizer_of_commute {a₁ w : G} (hw1 : w ≠ 1) (hwB : w ∈ B)
    (hwN : w ∈ normalizer (A : Set G)) (hc : Commute a₁ w) : a₁ ∈ normalizer (B : Set G) := by
  refine h.symm.mem_normalizer_of_mem_inf_conj hwB hwN hw1 ?_
  have : a₁⁻¹ * w * a₁ = w := by
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [this]
  exact hwB

theorem exists_mem_conj {K : Subgroup G} (hZK : zOf A ≤ K) (hKA : ¬ K ≤ A) :
    ∃ a ∈ A, ∃ w : G, w ≠ 1 ∧ w ∈ B ∧ w ∈ normalizer (A : Set G) ∧ a * w * a⁻¹ ∈ K := by
  have := h.nilA
  have := h.nilB
  have hN : ¬ ∀ r : ℕ, r.Prime → r ∣ Nat.card A → ∀ x ∈ K,
      x ∈ normalizer ((sylowOf A r ⊓ K : Subgroup G) : Set G) → x ∈ A :=
    fun hall => hKA (h.le_of_normalizer_le hZK hall)
  push Not at hN
  obtain ⟨r, hr, hrA, x, hxK, hxN, hxA⟩ := hN
  have : Fact r.Prime := ⟨hr⟩
  set M := K ⊓ normalizer ((sylowOf A r ⊓ K : Subgroup G) : Set G) with hMdef
  have hAM : A ⊓ K ≤ M := by
    intro y hy
    refine mem_inf.mpr ⟨hy.2, ?_⟩
    rw [mem_normalizer_iff]
    intro v
    rw [mem_inf, mem_inf]
    exact and_congr ((mem_normalizer_iff.mp (le_normalizer_sylowOf hy.1)) v)
      ((mem_normalizer_iff.mp (le_normalizer hy.2)) v)
  have hMA : ¬ M ≤ A := fun hle => hxA (hle ⟨hxK, hxN⟩)
  have hpr : ¬ ∀ q : ℕ, q.Prime → q ∣ Nat.card M → q ∣ Nat.card A :=
    fun hall => hMA (h.le_of_forall_prime_dvd hZK inf_le_left hAM hall)
  push Not at hpr
  obtain ⟨q, hq, hqM, hqA⟩ := hpr
  have : Fact q.Prime := ⟨hq⟩
  have := Fintype.ofFinite M
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card (G := M) q (by rwa [← Nat.card_eq_fintype_card])
  have hyo' : orderOf (y : G) = q := by rw [Subgroup.orderOf_coe, hyo]
  have hy1 : (y : G) ≠ 1 := fun h1 => hq.one_lt.ne' (by rw [← hyo', h1, orderOf_one])
  obtain ⟨z, hzP, hzZ, hz1, -⟩ := h.exists_mem_sylowOf_zOf hrA
  have hyN : (y : G)⁻¹ * z * (y : G) ∈ sylowOf A r ⊓ K := by
    have := (mem_normalizer_iff.mp (inv_mem (mem_inf.mp y.2).2) z).mp ⟨hzP, hZK hzZ⟩
    simpa using this
  have hyNA := h.mem_normalizer_of_mem_zOf_conj hzZ hz1 (sylowOf_le hyN.1)
  have hqB : q ∣ Nat.card B := by
    have : q ∣ Nat.card A * Nat.card B :=
      h.card_eq ▸ (hyo' ▸ orderOf_dvd_natCard (y : G))
    exact ((Nat.Prime.dvd_mul hq).1 this).resolve_left hqA
  have hyq : IsPGroup q (zpowers (y : G)) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, ← hyo', pow_orderOf_eq_one])
  obtain ⟨S'', hS''⟩ := hyq.exists_le_sylow
  obtain ⟨x', hx'⟩ := MulAction.exists_smul_eq G (h.symm.sylow hqB) S''
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mul x'
  have h1 := hS'' (mem_zpowers (y : G))
  rw [← hx', Sylow.coe_subgroup_smul, mem_conj_smul_iff, h.symm.coe_sylow] at h1
  have h2 := (mem_normalizer_iff.mp (le_normalizer_sylowOf (A := B) (p := q) hb) _).mp h1
  have e : b * ((a * b)⁻¹ * y * (a * b)) * b⁻¹ = a⁻¹ * y * a := by group
  rw [e] at h2
  refine ⟨a, ha, a⁻¹ * y * a, ?_, sylowOf_le h2, ?_, ?_⟩
  · intro h3
    apply hy1
    have : (y : G) = a * (a⁻¹ * y * a) * a⁻¹ := by group
    rw [this, h3]
    group
  · exact mul_mem (mul_mem (le_normalizer (inv_mem ha)) hyNA) (le_normalizer ha)
  · have : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
    rw [this]
    exact (mem_inf.mp y.2).1

theorem eq_one_of_mem_inf_conj {g : G} (hg : g ∉ normalizer (A : Set G)) {x : G} (hxA : x ∈ A)
    (hgx : g⁻¹ * x * g ∈ A) : x = 1 := by
  have := h.nilA
  set K : Subgroup G := zOf A ⊔ (zOf A).map (MulAut.conj g).toMonoidHom with hKdef
  have hKA : ¬ K ≤ A := by
    intro hle
    obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd fun h1 =>
      h.ne_bot_left (Subgroup.card_eq_one.mp h1)
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hzZ, hzo⟩ := h.exists_mem_zOf_orderOf hpA
    have hz1 : z ≠ 1 := fun h1 => hp.one_lt.ne' (by rw [← hzo, h1, orderOf_one])
    have hgz : g * z * g⁻¹ ∈ A := hle (mem_sup_right ⟨z, hzZ, rfl⟩)
    refine hg (h.mem_normalizer_of_conj_mem_zOf hgz ?_ ?_)
    · intro h1
      apply hz1
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h1]
      group
    · have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [this]
      exact hzZ
  obtain ⟨a, ha, w, hw1, hwB, hwN, hwK⟩ := h.exists_mem_conj le_sup_left hKA
  have hKc : ∀ k ∈ K, Commute k x := by
    intro k hk
    have hle : K ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun z hz => ?_) ?_
      · rw [mem_centralizer_singleton_iff]
        exact ((mem_zOf.mp hz).2 x hxA).eq
      · rintro _ ⟨z, hz, rfl⟩
        rw [mem_centralizer_singleton_iff]
        have hc : Commute z (g⁻¹ * x * g) := (mem_zOf.mp hz).2 _ hgx
        have := hc.map (MulAut.conj g)
        have e : (MulAut.conj g) (g⁻¹ * x * g) = x := by simp [mul_assoc]
        rw [e] at this
        exact this.eq
    exact mem_centralizer_singleton_iff.mp (hle hk)
  have hc : Commute (a⁻¹ * x * a) w := by
    have := (hKc _ hwK).map (MulAut.conj a⁻¹)
    have e1 : (MulAut.conj a⁻¹) (a * w * a⁻¹) = w := by simp [mul_assoc]
    have e2 : (MulAut.conj a⁻¹) x = a⁻¹ * x * a := by simp
    rw [e1, e2] at this
    exact this.symm
  have hx'N := h.mem_normalizer_of_commute hw1 hwB hwN hc
  by_contra hx1
  have hx'1 : a⁻¹ * x * a ≠ 1 := fun h1 => hx1 (by
    have : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    rw [this, h1]
    group)
  have hx'A : a⁻¹ * x * a ∈ A := A.mul_mem (A.mul_mem (A.inv_mem ha) hxA) ha
  have hgx' : (a⁻¹ * g)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * g) ∈ A := by
    have : (a⁻¹ * g)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * g) = g⁻¹ * x * g := by group
    rw [this]
    exact hgx
  have hag := h.mem_normalizer_of_mem_inf_conj hx'A hx'N hx'1 hgx'
  apply hg
  have : g = a * (a⁻¹ * g) := by group
  rw [this]
  exact mul_mem (le_normalizer ha) hag

theorem false_of_lt (hBA : Nat.card B < Nat.card A) : False := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ normalizer (A : Set G) := by
    by_contra hall
    push Not at hall
    exact h.normalizer_ne_top h.ne_bot_left (Or.inl le_rfl)
      (eq_top_iff.mpr fun g _ => hall g)
  let f : A × A → G := fun p => (p.1 : G) * (g * p.2 * g⁻¹)
  have hf : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
    simp only [f] at hxy
    have hu : (x' : G)⁻¹ * x = g * ((y' : G) * (y : G)⁻¹) * g⁻¹ := by
      calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * (g * y * g⁻¹)) * (g * y * g⁻¹)⁻¹ := by group
        _ = (x' : G)⁻¹ * (x' * (g * y' * g⁻¹)) * (g * y * g⁻¹)⁻¹ := by rw [hxy]
        _ = g * ((y' : G) * (y : G)⁻¹) * g⁻¹ := by group
    have huA : (x' : G)⁻¹ * x ∈ A := A.mul_mem (A.inv_mem x'.2) x.2
    have hgu : g⁻¹ * ((x' : G)⁻¹ * x) * g ∈ A := by
      rw [hu]
      have : g⁻¹ * (g * ((y' : G) * (y : G)⁻¹) * g⁻¹) * g = (y' : G) * (y : G)⁻¹ := by group
      rw [this]
      exact A.mul_mem y'.2 (A.inv_mem y.2)
    have hu1 := h.eq_one_of_mem_inf_conj hg huA hgu
    have hxx : x = x' := Subtype.ext (by
      rw [inv_mul_eq_one] at hu1
      exact hu1.symm)
    subst hxx
    have hyy : y = y' := Subtype.ext (by
      have h1 := mul_left_cancel hxy
      have h2 : g * (y : G) * g⁻¹ = g * (y' : G) * g⁻¹ := h1
      simpa using h2)
    rw [hyy]
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, h.card_eq] at hle
  exact absurd (Nat.le_of_mul_le_mul_left hle Nat.card_pos) (not_le.mpr hBA)

theorem false : False := by
  rcases lt_trichotomy (Nat.card B) (Nat.card A) with hlt | heq | hgt
  · exact h.false_of_lt hlt
  · have hc := h.cop
    rw [heq, Nat.coprime_self] at hc
    exact h.ne_bot_right (Subgroup.card_eq_one.mp (heq ▸ hc))
  · exact h.symm.false_of_lt hgt

end MinCounter

theorem wielandtFor (X : Type) [Group X] [Finite X] : WielandtFor X := by
  suffices hall : ∀ n : ℕ, ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n → WielandtFor Y from
    hall _ X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y _ _ hn A B hA hB hcop hmul
    by_contra hs
    exact MinCounter.false ⟨hA, hB, hcop, hmul, hs, fun Z _ _ hZ => ih _ (hn ▸ hZ) Z rfl⟩

theorem wielandt_coprime_product {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hA : Group.IsNilpotent A) (hB : Group.IsNilpotent B)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) : Group.IsSolvable G := by
  let φ : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have : Finite (Shrink.{0} G) := Finite.of_equiv G (equivShrink.{0} G)
  have eA : A ≃* A.map φ.symm.toMonoidHom := φ.symm.subgroupMap A
  have eB : B ≃* B.map φ.symm.toMonoidHom := φ.symm.subgroupMap B
  have hS := wielandtFor (Shrink.{0} G) _ _ (Group.nilpotent_of_mulEquiv eA)
    (Group.nilpotent_of_mulEquiv eB)
    (by rw [← Nat.card_congr eA.toEquiv, ← Nat.card_congr eB.toEquiv]; exact hcop) fun g => by
      obtain ⟨a, ha, b, hb, hg⟩ := hAB (φ g)
      refine ⟨φ.symm a, ⟨a, ha, rfl⟩, φ.symm b, ⟨b, hb, rfl⟩, ?_⟩
      rw [← map_mul, ← hg, MulEquiv.symm_apply_apply]
  exact Group.isSolvable_of_surjective (f := φ.toMonoidHom) φ.surjective

end CFSG.GroupTheory.WielandtProduct
