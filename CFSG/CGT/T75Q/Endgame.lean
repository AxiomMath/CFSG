module

public import CFSG.CGT.T75P.Dihedral81
public import CFSG.CGT.Timmesfeld75.Sec6TwoSetup

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P

variable {G : Type} [Group G]

structure DihHyp (T Y : Subgroup G) : Prop where
  wc : IsWC T
  h66 : ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T
  closed : ∀ d ∈ classD T, d ∈ Y → ∀ x ∈ classD T, x * d = d * x → x ∈ Y
  F1inv : ∀ c ∈ Subgroup.centralizer (Y : Set G), c ≠ 1 → c * c = 1 →
    ∀ d ∈ classD T, c * d = d * c → d ∈ Y
  Z : ∀ c ∈ Y ⊓ Subgroup.centralizer (Y : Set G), c * c = 1 → c = 1

structure EndHyp (T Y : Subgroup G) : Prop where
  wc : IsWC T
  h66 : ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T
  closed : ∀ d ∈ classD T, d ∈ Y → ∀ x ∈ classD T, x * d = d * x → x ∈ Y
  F1 : ∀ c ∈ Subgroup.centralizer (Y : Set G), c ≠ 1 → ∀ d ∈ classD T, c * d = d * c → d ∈ Y
  Z : ∀ c ∈ Y ⊓ Subgroup.centralizer (Y : Set G), c * c = 1 → c = 1
  TIa : ∀ g h d : G, d ∈ classD T → d ∈ conjSubgroup g Y → d ∈ conjSubgroup h Y →
    Subgroup.centralizer (conjSubgroup g Y : Set G) =
      Subgroup.centralizer (conjSubgroup h Y : Set G)
  TIb : ∀ g d : G, d ∈ classD T → d ∈ Y → d ∈ conjSubgroup g Y → conjSubgroup g Y ≤ Y

theorem EndHyp.toDih {T Y : Subgroup G} (h : EndHyp T Y) : DihHyp T Y :=
  ⟨h.wc, h.h66, h.closed, fun c hc hc1 _ => h.F1 c hc hc1, h.Z⟩

section Aux

theorem exists_fixed_of_involutive_odd {α : Type*} [Finite α] (f : α → α) (hf : ∀ a, f (f a) = a)
    (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  classical
  have := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf' : Function.Involutive f := hf
  let π : Equiv.Perm α := hf'.toPerm f
  have h2 : π ^ 2 ^ 1 = 1 := by
    ext a
    simp [pow_two, π, hf]
  have hn : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hodd
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hn h2
  exact ⟨a, ha⟩

theorem odd_card_of_odd_fixed [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) {S : Set G}
    (hS : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S)
    (hodd : Odd (Nat.card {s : G // s ∈ S ∧ ∀ p ∈ P, p * s * p⁻¹ = s})) : Odd (Nat.card S) := by
  classical
  let _ : SMul ↥P ↥S := ⟨fun p s => ⟨(p : G) * s * (p : G)⁻¹, hS p p.2 s s.2⟩⟩
  let _ : MulAction ↥P ↥S :=
    { one_smul := fun s => Subtype.ext (by
        show ((1 : ↥P) : G) * (s : G) * ((1 : ↥P) : G)⁻¹ = s
        simp)
      mul_smul := fun p q s => Subtype.ext (by
        show ((p * q : ↥P) : G) * (s : G) * ((p * q : ↥P) : G)⁻¹ =
          (p : G) * ((q : G) * (s : G) * (q : G)⁻¹) * (p : G)⁻¹
        simp [mul_assoc]) }
  have h := hP.card_modEq_card_fixedPoints ↥S
  have e : Nat.card (MulAction.fixedPoints ↥P ↥S) =
      Nat.card {s : G // s ∈ S ∧ ∀ p ∈ P, p * s * p⁻¹ = s} := by
    refine Nat.card_congr
      { toFun := fun s => ⟨(s.1 : G), s.1.2, fun p hp => ?_⟩
        invFun := fun s => ⟨⟨s.1, s.2.1⟩, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    · have := MulAction.mem_fixedPoints.1 s.2 ⟨p, hp⟩
      exact congrArg Subtype.val this
    · rw [MulAction.mem_fixedPoints]
      intro p
      exact Subtype.ext (s.2.2 p p.2)
  rw [e] at h
  have h1 : Nat.card S % 2 = Nat.card {s : G // s ∈ S ∧ ∀ p ∈ P, p * s * p⁻¹ = s} % 2 := h
  rw [Nat.odd_iff, h1]
  exact Nat.odd_iff.1 hodd

end Aux

section Basic

variable {T Y : Subgroup G}

theorem DihHyp.sq_eq_one (h : DihHyp T Y) {x : G} (hx : x ∈ classD T) : x * x = 1 :=
  mul_self_eq_one_of_mem_classD h.wc.1 hx

theorem DihHyp.F1_conj (h : DihHyp T Y) (g : G) {c : G}
    (hc : c ∈ Subgroup.centralizer (conjSubgroup g Y : Set G)) (hc1 : c ≠ 1) (hcc : c * c = 1)
    {d : G}
    (hd : d ∈ classD T) (hcd : c * d = d * c) : d ∈ conjSubgroup g Y := by
  have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hu : g * y * g⁻¹ ∈ conjSubgroup g Y := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hy
    have := Subgroup.mem_centralizer_iff.1 hc _ hu
    calc y * (g⁻¹ * c * g) = g⁻¹ * ((g * y * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * y * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * c * g * y := by group
  have hc1' : g⁻¹ * c * g ≠ 1 := by
    intro h1
    apply hc1
    calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hcc' : (g⁻¹ * c * g) * (g⁻¹ * c * g) = 1 := by
    calc (g⁻¹ * c * g) * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [hcc]; group
  have hd' : g⁻¹ * d * g ∈ classD T := classD_conj hd g
  have hcd' : (g⁻¹ * c * g) * (g⁻¹ * d * g) = (g⁻¹ * d * g) * (g⁻¹ * c * g) := by
    calc (g⁻¹ * c * g) * (g⁻¹ * d * g) = g⁻¹ * (c * d) * g := by group
      _ = g⁻¹ * (d * c) * g := by rw [hcd]
      _ = (g⁻¹ * d * g) * (g⁻¹ * c * g) := by group
  exact mem_conjSubgroup.2 (h.F1inv _ hc' hc1' hcc' _ hd' hcd')

theorem DihHyp.not_mem_classD (h : DihHyp T Y) {t : G} (ht : t ∈ Subgroup.centralizer (Y : Set G))
    (htt : t * t = 1) (ht1 : t ≠ 1) : t ∉ classD T := by
  intro htD
  have htY : t ∈ Y := h.F1inv t ht ht1 htt t htD rfl
  exact ht1 (h.Z t ⟨htY, ht⟩ htt)

end Basic


section Cases

variable {T Y : Subgroup G}

theorem DihHyp.false_of_eight_dvd (h : DihHyp T Y) {x c : G} (hx : x ∈ classD T) (hxY : x ∉ Y)
    (hc : c ∈ Subgroup.centralizer (Y : Set G)) (hcc : c * c = 1) (hc1 : c ≠ 1) {q : ℕ}
    (hq : 0 < q) (hN : orderOf (x * c) = 8 * q) : False := by
  have hx2 := h.sq_eq_one hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  set ρ := x * c with hρ
  have hxρ : x * ρ * x⁻¹ = ρ⁻¹ := left_invol_inverts hx2 hcc
  have hcρ : c * ρ * c⁻¹ = ρ⁻¹ := right_invol_inverts hx2 hcc
  have hρN : ρ ^ (8 * q) = 1 := by rw [← hN]; exact pow_orderOf_eq_one _
  have he : (ρ ^ q)⁻¹ * x * ρ ^ q ∈ classD T := classD_conj hx (ρ ^ q)
  have he' : (ρ ^ q)⁻¹ * x * ρ ^ q = (ρ ^ (2 * q))⁻¹ * x :=
    inv_pow_mul_mul_pow_of_inverts hxρ q
  have h1 : x * ρ ^ (2 * q) * x⁻¹ = (ρ ^ (2 * q))⁻¹ := by rw [← conj_pow, hxρ, inv_pow]
  have hxe : x * ((ρ ^ q)⁻¹ * x * ρ ^ q) = ρ ^ (2 * q) := by
    rw [he']
    calc x * ((ρ ^ (2 * q))⁻¹ * x) = x * (ρ ^ (2 * q))⁻¹ * x⁻¹ := by rw [← mul_assoc, hxinv]
      _ = (x * ρ ^ (2 * q) * x⁻¹)⁻¹ := by group
      _ = ρ ^ (2 * q) := by rw [h1, inv_inv]
  have hq2 : 2 * q ≠ 0 := by omega
  have hord : orderOf (ρ ^ (2 * q)) = 4 := by
    rw [orderOf_pow' (x := ρ) hq2, hN, Nat.gcd_eq_right ⟨4, by ring⟩]
    exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)
  have hz : (ρ ^ (4 * q)) ∈ classD T := by
    have := h.h66 x hx _ he (by rw [hxe]; exact hord)
    rwa [hxe, ← pow_mul, show 2 * q * 2 = 4 * q by ring] at this
  have hzz : ρ ^ (4 * q) * ρ ^ (4 * q) = 1 := by
    rw [← pow_add, show 4 * q + 4 * q = 8 * q by ring]
    exact hρN
  have hzinv : (ρ ^ (4 * q))⁻¹ = ρ ^ (4 * q) := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * ρ ^ (4 * q) = ρ ^ (4 * q) * x := by
    have h2 : x * ρ ^ (4 * q) * x⁻¹ = ρ ^ (4 * q) := by rw [← conj_pow, hxρ, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hcz : c * ρ ^ (4 * q) = ρ ^ (4 * q) * c := by
    have h2 : c * ρ ^ (4 * q) * c⁻¹ = ρ ^ (4 * q) := by rw [← conj_pow, hcρ, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hzY : ρ ^ (4 * q) ∈ Y := h.F1inv c hc hc1 hcc _ hz hcz
  exact hxY (h.closed _ hz hzY x hx hxz)

end Cases


section FourMulOdd

variable {T Y : Subgroup G}

theorem DihHyp.false_of_four_mul_odd [Finite G] (h : DihHyp T Y) {x c : G} (hx : x ∈ classD T)
    (hxY : x ∉ Y) (hc : c ∈ Subgroup.centralizer (Y : Set G)) (hcc : c * c = 1) (hc1 : c ≠ 1)
    {m : ℕ} (hm : Odd m) (hN : orderOf (x * c) = 4 * m) : False := by
  classical
  have hx2 := h.sq_eq_one hx
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcY : ∀ u ∈ Y, u * c = c * u := fun u hu => Subgroup.mem_centralizer_iff.1 hc u hu
  obtain ⟨j, hj⟩ := hm
  have hm0 : m ≠ 0 := by omega
  set ρ := x * c with hρ
  have hxρ : x * ρ * x⁻¹ = ρ⁻¹ := left_invol_inverts hx2 hcc
  have hcρ : c * ρ * c⁻¹ = ρ⁻¹ := right_invol_inverts hx2 hcc
  have hρN : ρ ^ (4 * m) = 1 := by rw [← hN]; exact pow_orderOf_eq_one _
  set z := ρ ^ (2 * m) with hzdef
  have hzz : z * z = 1 := by
    rw [hzdef, ← pow_add, show 2 * m + 2 * m = 4 * m by ring]
    exact hρN
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * z = z * x := by
    have h1 : x * z * x⁻¹ = z := by rw [hzdef, ← conj_pow, hxρ, inv_pow, ← hzdef, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hcz : c * z = z * c := by
    have h1 : c * z * c⁻¹ = z := by rw [hzdef, ← conj_pow, hcρ, inv_pow, ← hzdef, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  set g := ρ ^ (j + 1) with hg
  set y := g⁻¹ * x * g with hy
  have hyD : y ∈ classD T := classD_conj hx g
  have hy' : y = (ρ ^ (2 * (j + 1)))⁻¹ * x := inv_pow_mul_mul_pow_of_inverts hxρ (j + 1)
  have hyc : y * c = (ρ ^ m)⁻¹ := by
    rw [hy']
    calc (ρ ^ (2 * (j + 1)))⁻¹ * x * c = (ρ ^ (2 * (j + 1)))⁻¹ * ρ := by rw [mul_assoc]
      _ = (ρ ^ m)⁻¹ := by
        rw [show 2 * (j + 1) = m + 1 by omega, pow_succ]
        group
  have hw : orderOf (y * c) = 4 := by
    rw [hyc, orderOf_inv, orderOf_pow' (x := ρ) hm0, hN, Nat.gcd_eq_right ⟨4, by ring⟩]
    exact Nat.mul_div_cancel 4 (Nat.pos_of_ne_zero hm0)
  have hyc2 : (y * c) ^ 2 = z := by
    calc (y * c) ^ 2 = ((ρ ^ m) ^ 2)⁻¹ := by rw [hyc, inv_pow]
      _ = (ρ ^ (2 * m))⁻¹ := by rw [← pow_mul, mul_comm]
      _ = z := hzinv
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 : (y * c) ^ 2 = 1 := by rw [hyc2, h1]
    have h4 := orderOf_dvd_of_pow_eq_one h2
    rw [hw] at h4
    omega
  have hyY : y ∉ Y := by
    intro hyY
    have hyc' : y * c = c * y := hcY y hyY
    have h2 : (y * c) ^ 2 = 1 := by
      rw [pow_two]
      calc y * c * (y * c) = y * (c * y) * c := by group
        _ = y * (y * c) * c := by rw [← hyc']
        _ = (y * y) * (c * c) := by group
        _ = 1 := by rw [h.sq_eq_one hyD, hcc, mul_one]
    have h4 := orderOf_dvd_of_pow_eq_one h2
    rw [hw] at h4
    omega
  have hzD : z ∉ classD T := by
    intro hzD
    have hzY : z ∈ Y := h.F1inv c hc hc1 hcc z hzD hcz
    exact hxY (h.closed z hzD hzY x hx hxz)
  have hycD : c * y * c⁻¹ ∈ classD T := by
    have := classD_conj hyD c⁻¹
    simpa using this
  have hyy : y * (c * y * c⁻¹) = z := by
    rw [← hyc2, pow_two, hcinv]
    group
  have hyc_comm : y * (c * y * c⁻¹) = (c * y * c⁻¹) * y := by
    have hI : (c * y * c⁻¹) * (c * y * c⁻¹) = 1 := h.sq_eq_one hycD
    have hy2 : y * y = 1 := h.sq_eq_one hyD
    have hinv1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hinv2 : (c * y * c⁻¹)⁻¹ = c * y * c⁻¹ := inv_eq_of_mul_eq_one_right hI
    have h3 : (c * y * c⁻¹) * y = (y * (c * y * c⁻¹))⁻¹ := by rw [mul_inv_rev, hinv1, hinv2]
    rw [h3, hyy, hzinv]
  obtain ⟨a, ha⟩ := exists_mem_conj_of_mem_classD hyD
  have hy3 : c * y * c⁻¹ ∈ conjSubgroup (c * a) T := by
    rw [mem_conjSubgroup]
    have h1 := mem_conjSubgroup.1 ha
    have e : (c * a)⁻¹ * (c * y * c⁻¹) * (c * a) = a⁻¹ * y * a := by group
    rw [e]
    exact h1
  have hne3 : conjSubgroup (c * a) T ≠ conjSubgroup a T := by
    intro heq
    have hyc3 : c * y * c⁻¹ ∈ conjSubgroup a T := heq ▸ hy3
    have hzmem : z ∈ conjSubgroup a T := by
      rw [← hyy]
      exact Subgroup.mul_mem _ ha hyc3
    exact hzD (mem_classD_of_mem_conjSubgroup hzmem hz1)
  have hwc2 : IsWC (conjSubgroup a T) := h.wc.conj a
  have hwc3 : IsWC (conjSubgroup (c * a) T) := h.wc.conj (c * a)
  have hyN : y ∈ Subgroup.normalizer (conjSubgroup (c * a) T : Set G) :=
    hwc3.centralizer_le_normalizer hy3 (ne_one_of_mem_classD hycD)
      (Subgroup.mem_centralizer_singleton_iff.2 hyc_comm)
  have hyL : y ∈ normIn (conjSubgroup a T) (conjSubgroup (c * a) T) := mem_normIn.2 ⟨ha, hyN⟩
  have hLne : normIn (conjSubgroup a T) (conjSubgroup (c * a) T) ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.mem_bot] at hyL
    exact ne_one_of_mem_classD hyD hyL
  have hcfg : Cfg (conjSubgroup a T) (conjSubgroup (c * a) T) :=
    cfg_of_conj_conj h.wc ⟨a, rfl⟩ ⟨c * a, rfl⟩ hne3 hLne
  have hc2 : conjSubgroup c (conjSubgroup a T) = conjSubgroup (c * a) T :=
    conjSubgroup_conjSubgroup c a T
  have hc3 : conjSubgroup c (conjSubgroup (c * a) T) = conjSubgroup a T := by
    rw [conjSubgroup_conjSubgroup, ← mul_assoc, hcc, one_mul]
  have hMc : conjSubgroup c (cfgM (conjSubgroup a T) (conjSubgroup (c * a) T)) =
      cfgM (conjSubgroup a T) (conjSubgroup (c * a) T) := by
    rw [← cfgM_conj, hc2, hc3]
    exact sup_comm _ _
  set M := cfgM (conjSubgroup a T) (conjSubgroup (c * a) T) with hM
  set Ωs : Set G := {s | s ∈ M ∧ s ∈ classD T} with hΩ
  have hcΩ : ∀ s ∈ Ωs, c * s * c⁻¹ ∈ Ωs := by
    rintro s ⟨hsM, hsD⟩
    refine ⟨?_, ?_⟩
    · have h1 : c * s * c⁻¹ ∈ conjSubgroup c M := by
        rw [mem_conjSubgroup]
        have e : c⁻¹ * (c * s * c⁻¹) * c = s := by group
        rw [e]
        exact hsM
      rwa [hMc] at h1
    · have := classD_conj hsD c⁻¹
      simpa using this
  have hT₂Ω : ∀ p ∈ conjSubgroup a T, ∀ s ∈ Ωs, p * s * p⁻¹ ∈ Ωs := by
    rintro p hp s ⟨hsM, hsD⟩
    refine ⟨hcfg.conj_mem_cfgM (Subgroup.mem_sup_left hp) hsM, ?_⟩
    have := classD_conj hsD p⁻¹
    simpa using this
  have hfixset : {s : G | s ∈ Ωs ∧ ∀ p ∈ conjSubgroup a T, p * s * p⁻¹ = s} =
      (normIn (conjSubgroup a T) (conjSubgroup (c * a) T) : Set G) \ {1} := by
    ext s
    constructor
    · rintro ⟨⟨hsM, hsD⟩, hfix⟩
      obtain ⟨k, hk⟩ := exists_mem_conj_of_mem_classD hsD
      have hs1 := ne_one_of_mem_classD hsD
      have hwck : IsWC (conjSubgroup k T) := h.wc.conj k
      have hT₂N : conjSubgroup a T ≤ Subgroup.normalizer (conjSubgroup k T : Set G) := by
        intro p hp
        have hps : p * s = s * p := by
          have := hfix p hp
          calc p * s = (p * s * p⁻¹) * p := by group
            _ = s * p := by rw [this]
        exact hwck.centralizer_le_normalizer hk hs1
          (Subgroup.mem_centralizer_singleton_iff.2 hps)
      have hP : IsPGroup 2 ↥(conjSubgroup a T ⊔ conjSubgroup k T) :=
        (isPGroup_two_of_isElemAbelian hwc2.1).to_sup_of_normal_right'
          (isPGroup_two_of_isElemAbelian hwck.1) hT₂N
      have hconj : conjSubgroup (a * k⁻¹) (conjSubgroup k T) ≤
          conjSubgroup a T ⊔ conjSubgroup k T := by
        rw [conjSubgroup_conjSubgroup, show a * k⁻¹ * k = a by group]
        exact le_sup_left
      have heq := eq_of_conj_le_pGroup hwck hP le_sup_right hconj
      rw [conjSubgroup_conjSubgroup, show a * k⁻¹ * k = a by group] at heq
      have hsT₂ : s ∈ conjSubgroup a T := by rw [heq]; exact hk
      have : s ∈ conjSubgroup a T ⊓ M := ⟨hsT₂, hsM⟩
      rw [hcfg.inf_cfgM] at this
      exact ⟨this, hs1⟩
    · rintro ⟨hsL, hs1⟩
      have hs1' : s ≠ 1 := hs1
      have hsT₂ : s ∈ conjSubgroup a T := normIn_le _ _ hsL
      refine ⟨⟨Cfg.normIn_le_cfgM_left _ _ hsL, mem_classD_of_mem_conjSubgroup hsT₂ hs1'⟩, ?_⟩
      intro p hp
      have hcomm := elemAbelian_mul_comm hwc2.1 hp hsT₂
      calc p * s * p⁻¹ = s * p * p⁻¹ := by rw [hcomm]
        _ = s := by group
  have hLeven : Even (Nat.card ↥(normIn (conjSubgroup a T) (conjSubgroup (c * a) T))) := by
    have hP2 : IsPGroup 2 ↥(normIn (conjSubgroup a T) (conjSubgroup (c * a) T)) :=
      (isPGroup_two_of_isElemAbelian hwc2.1).to_le (normIn_le _ _)
    obtain ⟨n', hn'⟩ := IsPGroup.iff_card.1 hP2
    have hn0 : n' ≠ 0 := by
      rintro rfl
      have : Nat.card ↥(normIn (conjSubgroup a T) (conjSubgroup (c * a) T)) = 1 := by
        rw [hn', pow_zero]
      rw [Subgroup.card_eq_one] at this
      exact hLne this
    rw [hn']
    exact (Nat.even_pow.2 ⟨even_two, hn0⟩)
  have hFixOdd : Odd (Nat.card {s : G // s ∈ Ωs ∧ ∀ p ∈ conjSubgroup a T, p * s * p⁻¹ = s}) := by
    have e1 : Nat.card {s : G // s ∈ Ωs ∧ ∀ p ∈ conjSubgroup a T, p * s * p⁻¹ = s} =
        Nat.card ↥((normIn (conjSubgroup a T) (conjSubgroup (c * a) T) : Set G) \ {1}) :=
      congrArg (fun S : Set G => Nat.card ↥S) hfixset
    rw [e1, Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)]
    have e2 : ((normIn (conjSubgroup a T) (conjSubgroup (c * a) T) : Set G)).ncard =
        Nat.card ↥(normIn (conjSubgroup a T) (conjSubgroup (c * a) T)) :=
      (Nat.card_coe_set_eq _).symm
    rw [e2]
    have hpos : 0 < Nat.card ↥(normIn (conjSubgroup a T) (conjSubgroup (c * a) T)) :=
      Nat.card_pos
    obtain ⟨r, hr⟩ := hLeven
    exact ⟨r - 1, by omega⟩
  have hOmOdd : Odd (Nat.card Ωs) :=
    odd_card_of_odd_fixed (isPGroup_two_of_isElemAbelian hwc2.1) hT₂Ω hFixOdd
  obtain ⟨b, hb⟩ := exists_fixed_of_involutive_odd
    (fun s : Ωs => (⟨c * s * c⁻¹, hcΩ s s.2⟩ : Ωs))
    (fun s => Subtype.ext (by
      show c * (c * (s : G) * c⁻¹) * c⁻¹ = s
      rw [hcinv]
      calc c * (c * (s : G) * c) * c = (c * c) * s * (c * c) := by group
        _ = s := by rw [hcc]; group)) hOmOdd
  have hbc : c * (b : G) * c⁻¹ = b := congrArg Subtype.val hb
  have hbD : (b : G) ∈ classD T := b.2.2
  have hcb : c * (b : G) = (b : G) * c := by
    calc c * (b : G) = (c * b * c⁻¹) * c := by group
      _ = (b : G) * c := by rw [hbc]
  have hbY : (b : G) ∈ Y := h.F1inv c hc hc1 hcc b hbD hcb
  have hyM : y ∈ M := Cfg.normIn_le_cfgM_left _ _ hyL
  have hyb : y * (b : G) = (b : G) * y :=
    elemAbelian_mul_comm hcfg.isElemAbelian_cfgM hyM b.2.1
  exact hyY (h.closed b hbD hbY y hyD hyb)

end FourMulOdd

section Order

variable {T Y : Subgroup G}

theorem DihHyp.orderOf_eq_two_mul_odd [Finite G] (h : DihHyp T Y) {x c : G} (hx : x ∈ classD T)
    (hxY : x ∉ Y) (hc : c ∈ Subgroup.centralizer (Y : Set G)) (hcc : c * c = 1) (hc1 : c ≠ 1) :
    ∃ m : ℕ, Odd m ∧ orderOf (x * c) = 2 * m := by
  have hx2 := h.sq_eq_one hx
  have hpos : 0 < orderOf (x * c) := orderOf_pos _
  obtain ⟨s, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  rcases Nat.lt_or_ge s 3 with hs | hs
  · interval_cases s
    · exfalso
      have hodd : Odd (orderOf (x * c)) := by
        rw [hN]
        simpa using hm
      obtain ⟨k, hk⟩ := dih_odd hx2 hcc hodd
      have hcD : c ∈ classD T := hk ▸ classD_conj hx ((x * c) ^ k)
      exact h.not_mem_classD hc hcc hc1 hcD
    · exact ⟨m, hm, by simpa using hN⟩
    · exfalso
      exact h.false_of_four_mul_odd hx hxY hc hcc hc1 hm (by simpa using hN)
  · exfalso
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
    have hq : 0 < 2 ^ t * m := Nat.mul_pos (by positivity) hm.pos
    exact h.false_of_eight_dvd hx hxY hc hcc hc1 hq
      (by rw [hN, pow_add]; ring)

end Order

section Final

variable {T Y : Subgroup G}

theorem mem_centralizer_conjSubgroup {g c : G} (hc : c ∈ Subgroup.centralizer (Y : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (conjSubgroup g Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : g⁻¹ * u * g ∈ Y := mem_conjSubgroup.1 hu
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hu'
  calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * u := by group

theorem DihHyp.exists_data [Finite G] (h : DihHyp T Y) {x c : G} (hx : x ∈ classD T) (hxY : x ∉ Y)
    (hc : c ∈ Subgroup.centralizer (Y : Set G)) (hcc : c * c = 1) (hc1 : c ≠ 1) :
    ∃ z g : G, z * z = 1 ∧ x * z = z * x ∧ c * z = z * c ∧ g⁻¹ * x * g = c * z ∧ c * z ∈ Y ∧
      (∀ u : G, u * x = x * u → u * c = c * u → u * g = g * u) := by
  obtain ⟨m, hm, hN⟩ := h.orderOf_eq_two_mul_odd hx hxY hc hcc hc1
  obtain ⟨z, hzz, hxz, hcz, k, hk⟩ := dih_two_mod_four (h.sq_eq_one hx) hcc hm hN
  have hd : c * z ∈ classD T := by
    rw [← hk]
    exact classD_conj hx ((x * c) ^ k)
  have hdc : c * (c * z) = c * z * c := by rw [mul_assoc, ← hcz]
  refine ⟨z, (x * c) ^ k, hzz, hxz, hcz, hk, h.F1inv c hc hc1 hcc (c * z) hd hdc, ?_⟩
  intro u hux huc
  have hρ : u * (x * c) = (x * c) * u := by
    calc u * (x * c) = (u * x) * c := by group
      _ = (x * u) * c := by rw [hux]
      _ = x * (u * c) := by group
      _ = x * (c * u) := by rw [huc]
      _ = (x * c) * u := by group
  exact (Commute.pow_right (show Commute u (x * c) from hρ) k).eq

theorem DihHyp.dihedral_data [Finite G] (h : DihHyp T Y) {x t τ : G} (hx : x ∈ classD T)
    (hxY : x ∉ Y) (ht : t ∈ Subgroup.centralizer (Y : Set G))
    (hτ : τ ∈ Subgroup.centralizer (Y : Set G)) (ht2 : t * t = 1) (hτ2 : τ * τ = 1)
    (ht1 : t ≠ 1) (hτ1 : τ ≠ 1) (htτ : t ≠ τ) (hcomm : t * τ = τ * t) :
    ∃ z₁ z₂ g₁ g₂ : G, z₁ * z₁ = 1 ∧ z₂ * z₂ = 1 ∧ z₁ * z₂ ≠ 1 ∧
      g₁⁻¹ * x * g₁ = t * z₁ ∧ g₂⁻¹ * x * g₂ = τ * z₂ ∧ t * z₁ ∈ Y ∧ τ * z₂ ∈ Y ∧
      (g₁ * t * g₁⁻¹) * (g₂ * τ * g₂⁻¹) = z₁ * z₂ ∧
      (z₁ * z₂) * x = x * (z₁ * z₂) ∧
      (z₁ * z₂) * (g₁⁻¹ * x * g₁) = (g₁⁻¹ * x * g₁) * (z₁ * z₂) ∧
      (z₁ * z₂) * (g₂⁻¹ * x * g₂) = (g₂⁻¹ * x * g₂) * (z₁ * z₂) ∧
      (z₁ * z₂) * t = t * (z₁ * z₂) ∧ (z₁ * z₂) * τ = τ * (z₁ * z₂) ∧
      z₁ * z₂ = z₂ * z₁ ∧ (z₁ * z₂) * (z₁ * z₂) = 1 := by
  have hx2 := h.sq_eq_one hx
  obtain ⟨z₁, g₁, hz₁, hxz₁, htz₁, hg₁, hd₁, hgc₁⟩ := h.exists_data hx hxY ht ht2 ht1
  obtain ⟨z₂, g₂, hz₂, hxz₂, hτz₂, hg₂, hd₂, hgc₂⟩ := h.exists_data hx hxY hτ hτ2 hτ1
  have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁
  have hz₂inv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hgz₁ : g₁ * z₁ = z₁ * g₁ := (hgc₁ z₁ hxz₁.symm htz₁.symm).symm
  have hgz₂ : g₂ * z₂ = z₂ * g₂ := (hgc₂ z₂ hxz₂.symm hτz₂.symm).symm
  have hxα : x = (g₁ * t * g₁⁻¹) * z₁ := by
    calc x = g₁ * (g₁⁻¹ * x * g₁) * g₁⁻¹ := by group
      _ = g₁ * (t * z₁) * g₁⁻¹ := by rw [hg₁]
      _ = (g₁ * t * g₁⁻¹) * (g₁ * z₁ * g₁⁻¹) := by group
      _ = (g₁ * t * g₁⁻¹) * z₁ := by rw [hgz₁]; group
  have hxβ : x = (g₂ * τ * g₂⁻¹) * z₂ := by
    calc x = g₂ * (g₂⁻¹ * x * g₂) * g₂⁻¹ := by group
      _ = g₂ * (τ * z₂) * g₂⁻¹ := by rw [hg₂]
      _ = (g₂ * τ * g₂⁻¹) * (g₂ * z₂ * g₂⁻¹) := by group
      _ = (g₂ * τ * g₂⁻¹) * z₂ := by rw [hgz₂]; group
  have hα' : g₁ * t * g₁⁻¹ = x * z₁ := by
    calc g₁ * t * g₁⁻¹ = (g₁ * t * g₁⁻¹ * z₁) * z₁⁻¹ := by group
      _ = x * z₁⁻¹ := by rw [← hxα]
      _ = x * z₁ := by rw [hz₁inv]
  have hβ' : g₂ * τ * g₂⁻¹ = x * z₂ := by
    calc g₂ * τ * g₂⁻¹ = (g₂ * τ * g₂⁻¹ * z₂) * z₂⁻¹ := by group
      _ = x * z₂⁻¹ := by rw [← hxβ]
      _ = x * z₂ := by rw [hz₂inv]
  have hγeq : (g₁ * t * g₁⁻¹) * (g₂ * τ * g₂⁻¹) = z₁ * z₂ := by
    rw [hα', hβ']
    calc x * z₁ * (x * z₂) = (z₁ * x) * (x * z₂) := by rw [hxz₁]
      _ = z₁ * (x * x) * z₂ := by group
      _ = z₁ * z₂ := by rw [hx2, mul_one]
  have hYt : ∀ u ∈ Y, u * t = t * u := fun u hu => Subgroup.mem_centralizer_iff.1 ht u hu
  have hYτ : ∀ u ∈ Y, u * τ = τ * u := fun u hu => Subgroup.mem_centralizer_iff.1 hτ u hu
  have hz₁eq : z₁ = (t * z₁) * t := by
    calc z₁ = (t * t) * z₁ := by rw [ht2, one_mul]
      _ = t * (t * z₁) := by group
      _ = t * (z₁ * t) := by rw [htz₁]
      _ = (t * z₁) * t := by group
  have hz₁τ : z₁ * τ = τ * z₁ := by
    have h1 : (t * z₁) * τ = τ * (t * z₁) := hYτ (t * z₁) hd₁
    calc z₁ * τ = ((t * z₁) * t) * τ := by rw [← hz₁eq]
      _ = (t * z₁) * (t * τ) := by group
      _ = (t * z₁) * (τ * t) := by rw [hcomm]
      _ = ((t * z₁) * τ) * t := by group
      _ = (τ * (t * z₁)) * t := by rw [h1]
      _ = τ * ((t * z₁) * t) := by group
      _ = τ * z₁ := by rw [← hz₁eq]
  have hz₂t : z₂ * t = t * z₂ := by
    have h1 : (τ * z₂) * t = t * (τ * z₂) := hYt (τ * z₂) hd₂
    have hz₂eq : z₂ = τ * (τ * z₂) := by
      calc z₂ = (τ * τ) * z₂ := by rw [hτ2, one_mul]
        _ = τ * (τ * z₂) := by group
    calc z₂ * t = (τ * (τ * z₂)) * t := by rw [← hz₂eq]
      _ = τ * ((τ * z₂) * t) := by group
      _ = τ * (t * (τ * z₂)) := by rw [h1]
      _ = (τ * t) * (τ * z₂) := by group
      _ = (t * τ) * (τ * z₂) := by rw [← hcomm]
      _ = t * (τ * (τ * z₂)) := by group
      _ = t * z₂ := by rw [← hz₂eq]
  have hz12 : z₁ * z₂ ≠ 1 := by
    intro h12
    have hz₂z₁ : z₂ = z₁ := by
      rw [eq_inv_of_mul_eq_one_right h12, hz₁inv]
    have hd₂' : τ * z₁ ∈ Y := by rw [← hz₂z₁]; exact hd₂
    have hcz : Commute z₁ (t * τ) :=
      Commute.mul_right (show Commute z₁ t from htz₁.symm) (show Commute z₁ τ from hz₁τ)
    have hw : (t * z₁)⁻¹ * (τ * z₁) = t * τ := by
      calc (t * z₁)⁻¹ * (τ * z₁) = (z₁⁻¹ * t⁻¹) * (τ * z₁) := by rw [mul_inv_rev]
        _ = (z₁ * t) * (τ * z₁) := by rw [hz₁inv, htinv]
        _ = (z₁ * (t * τ)) * z₁ := by group
        _ = ((t * τ) * z₁) * z₁ := by rw [hcz.eq]
        _ = t * τ := by rw [mul_assoc, hz₁, mul_one]
    have htτY : t * τ ∈ Y := by
      rw [← hw]
      exact Y.mul_mem (Y.inv_mem hd₁) hd₂'
    have htτsq : (t * τ) * (t * τ) = 1 := by
      calc t * τ * (t * τ) = t * (τ * t) * τ := by group
        _ = t * (t * τ) * τ := by rw [← hcomm]
        _ = (t * t) * (τ * τ) := by group
        _ = 1 := by rw [ht2, hτ2, mul_one]
    have h1 := h.Z (t * τ) ⟨htτY, Subgroup.mul_mem _ ht hτ⟩ htτsq
    apply htτ
    rw [eq_inv_of_mul_eq_one_left h1, hτinv]
  have hz₂g₁ : z₂ * g₁ = g₁ * z₂ := hgc₁ z₂ hxz₂.symm hz₂t
  have hz₁g₂ : z₁ * g₂ = g₂ * z₁ := hgc₂ z₁ hxz₁.symm hz₁τ
  have hcomm_conj : ∀ (z g : G), z * g = g * z → z * x = x * z →
      z * (g⁻¹ * x * g) = (g⁻¹ * x * g) * z := by
    intro z g hzg hzx
    have hc1' : Commute z g := hzg
    have hc2' : Commute z x := hzx
    exact (((hc1'.inv_right).mul_right hc2').mul_right hc1').eq
  have hz₁x : z₁ * x = x * z₁ := hxz₁.symm
  have hz₂x : z₂ * x = x * z₂ := hxz₂.symm
  have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := by
    have h1 : z₂ * (g₁⁻¹ * x * g₁) = (g₁⁻¹ * x * g₁) * z₂ := hcomm_conj z₂ g₁ hz₂g₁ hz₂x
    rw [hg₁] at h1
    have h2 : z₂ * z₁ = z₁ * z₂ := by
      have : t * (z₂ * z₁) = t * (z₁ * z₂) := by
        calc t * (z₂ * z₁) = (t * z₂) * z₁ := by group
          _ = (z₂ * t) * z₁ := by rw [hz₂t]
          _ = z₂ * (t * z₁) := by group
          _ = (t * z₁) * z₂ := h1
          _ = t * (z₁ * z₂) := by group
      exact mul_left_cancel this
    exact h2.symm
  refine ⟨z₁, z₂, g₁, g₂, hz₁, hz₂, hz12, hg₁, hg₂, hd₁, hd₂, hγeq, ?_, ?_, ?_, ?_, ?_, hz₁z₂, ?_⟩
  · calc (z₁ * z₂) * x = z₁ * (z₂ * x) := by group
      _ = z₁ * (x * z₂) := by rw [hz₂x]
      _ = (z₁ * x) * z₂ := by group
      _ = (x * z₁) * z₂ := by rw [hz₁x]
      _ = x * (z₁ * z₂) := by group
  · have hA := hcomm_conj z₁ g₁ hgz₁.symm hz₁x
    have hB := hcomm_conj z₂ g₁ hz₂g₁ hz₂x
    calc (z₁ * z₂) * (g₁⁻¹ * x * g₁) = z₁ * (z₂ * (g₁⁻¹ * x * g₁)) := by group
      _ = z₁ * ((g₁⁻¹ * x * g₁) * z₂) := by rw [hB]
      _ = (z₁ * (g₁⁻¹ * x * g₁)) * z₂ := by group
      _ = ((g₁⁻¹ * x * g₁) * z₁) * z₂ := by rw [hA]
      _ = (g₁⁻¹ * x * g₁) * (z₁ * z₂) := by group
  · have hA := hcomm_conj z₁ g₂ hz₁g₂ hz₁x
    have hB := hcomm_conj z₂ g₂ hgz₂.symm hz₂x
    calc (z₁ * z₂) * (g₂⁻¹ * x * g₂) = z₁ * (z₂ * (g₂⁻¹ * x * g₂)) := by group
      _ = z₁ * ((g₂⁻¹ * x * g₂) * z₂) := by rw [hB]
      _ = (z₁ * (g₂⁻¹ * x * g₂)) * z₂ := by group
      _ = ((g₂⁻¹ * x * g₂) * z₁) * z₂ := by rw [hA]
      _ = (g₂⁻¹ * x * g₂) * (z₁ * z₂) := by group
  · calc (z₁ * z₂) * t = z₁ * (z₂ * t) := by group
      _ = z₁ * (t * z₂) := by rw [hz₂t]
      _ = (z₁ * t) * z₂ := by group
      _ = (t * z₁) * z₂ := by rw [htz₁]
      _ = t * (z₁ * z₂) := by group
  · calc (z₁ * z₂) * τ = z₁ * (z₂ * τ) := by group
      _ = z₁ * (τ * z₂) := by rw [hτz₂]
      _ = (z₁ * τ) * z₂ := by group
      _ = (τ * z₁) * z₂ := by rw [hz₁τ]
      _ = τ * (z₁ * z₂) := by group
  · calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← hz₁z₂]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [hz₁, hz₂, mul_one]

theorem endgame_false [Finite G] {T Y : Subgroup G} (h : EndHyp T Y) (hD : ∃ x ∈ classD T, x ∉ Y)
    {t τ : G} (ht : t ∈ Subgroup.centralizer (Y : Set G))
    (hτ : τ ∈ Subgroup.centralizer (Y : Set G)) (ht2 : t * t = 1) (hτ2 : τ * τ = 1)
    (ht1 : t ≠ 1) (hτ1 : τ ≠ 1) (htτ : t ≠ τ) (hcomm : t * τ = τ * t) : False := by
  obtain ⟨x, hx, hxY⟩ := hD
  obtain ⟨z₁, z₂, g₁, g₂, hz₁, hz₂, hz12, hg₁, hg₂, hd₁, hd₂, hγeq, hγx, hγd, hγe, hγt, hγτ, -,
      hγ2⟩ := h.toDih.dihedral_data hx hxY ht hτ ht2 hτ2 ht1 hτ1 htτ hcomm
  have hD₁D : g₁⁻¹ * x * g₁ ∈ classD T := classD_conj hx g₁
  have hD₁Y : g₁⁻¹ * x * g₁ ∈ Y := by rw [hg₁]; exact hd₁
  have hxg₁ : x ∈ conjSubgroup g₁ Y := mem_conjSubgroup.2 hD₁Y
  have hxg₂ : x ∈ conjSubgroup g₂ Y := mem_conjSubgroup.2 (by rw [hg₂]; exact hd₂)
  have hTIa := h.TIa g₁ g₂ x hx hxg₁ hxg₂
  have hα : g₁ * t * g₁⁻¹ ∈ Subgroup.centralizer (conjSubgroup g₁ Y : Set G) :=
    mem_centralizer_conjSubgroup ht
  have hβ : g₂ * τ * g₂⁻¹ ∈ Subgroup.centralizer (conjSubgroup g₁ Y : Set G) := by
    rw [hTIa]
    exact mem_centralizer_conjSubgroup hτ
  have hγ : (g₁ * t * g₁⁻¹) * (g₂ * τ * g₂⁻¹) ∈
      Subgroup.centralizer (conjSubgroup g₁ Y : Set G) := Subgroup.mul_mem _ hα hβ
  have hγ1 : (g₁ * t * g₁⁻¹) * (g₂ * τ * g₂⁻¹) ≠ 1 := by rw [hγeq]; exact hz12
  have hdconj : g₁⁻¹ * x * g₁ ∈ conjSubgroup g₁ Y := by
    refine h.toDih.F1_conj g₁ hγ hγ1 (by rw [hγeq]; exact hγ2) hD₁D ?_
    rw [hγeq]
    exact hγd
  have hsub := h.TIb g₁ (g₁⁻¹ * x * g₁) hD₁D hD₁Y hdconj
  exact hxY (hsub hxg₁)

end Final

end CFSG.CGT.T75Q
