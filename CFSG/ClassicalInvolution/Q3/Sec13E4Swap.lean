module

public import CFSG.ClassicalInvolution.Q3.Sec13E4Pair

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem two_lt_card_of_three {H : Subgroup G} {a b c : G} (ha : a ∈ H) (hb : b ∈ H)
    (hc : c ∈ H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 2 < Nat.card ↥H := by
  have h1 : Nat.card ↥H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
  rw [h1]
  exact (Set.two_lt_ncard_iff (Set.toFinite _)).2 ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩

private theorem two_lt_card_inf_of_sq_ne_one {M P : Subgroup G} {u : G} (hM : u ∈ M) (hP : u ∈ P)
    (hu : u * u ≠ 1) : 2 < Nat.card ↥(M ⊓ P) := by
  refine two_lt_card_of_three (a := 1) (b := u) (c := u * u) (one_mem _) ⟨hM, hP⟩
    ⟨M.mul_mem hM hM, P.mul_mem hP hP⟩ ?_ ?_ ?_
  · intro h1
    apply hu
    rw [← h1, one_mul]
  · exact fun h1 => hu h1.symm
  · intro h1
    apply hu
    have h2 : u * u = u * 1 := by rw [mul_one]; exact h1.symm
    rw [mul_left_cancel h2, one_mul]

private theorem comm_of_mem_uniqueInvolution {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) {u : G} (hu : u ∈ K) : u * z = z * u :=
  mul_inv_eq_iff_eq_mul.mp (hz.conj_eq (conjSub_eq_self_of_mem hu))

private theorem comm_of_sq_eq_one {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) {x : G}
    (hx : x ∈ K) (hx2 : x * x = 1) {y : G} (hy : y ∈ K) : x * y = y * x := by
  rcases hz.unique x hx hx2 with rfl | rfl
  · rw [one_mul, mul_one]
  · exact (comm_of_mem_uniqueInvolution hz hy).symm

private theorem le_normalizer_of_commutes' {A B : Subgroup G} (hc : Commutes A B) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 : conjSub x⁻¹ B = B := conjSub_eq_of_mem_of_commutes (A.inv_mem hx) hc
  have h2 : y ∈ conjSub x⁻¹ B ↔ y ∈ B := by rw [h1]
  rw [mem_conjSub_iff, inv_inv] at h2
  exact h2.symm

private theorem mem_normalizer_of_conjSub_eq' {K : Subgroup G} {t : G} (h : conjSub t K = K) :
    t ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : conjSub t⁻¹ K = K := by
    conv_lhs => rw [← h]
    exact conjSub_inv_conjSub t K
  have h2 : x ∈ conjSub t⁻¹ K ↔ x ∈ K := by rw [h1]
  rw [mem_conjSub_iff, inv_inv] at h2
  exact h2.symm

theorem exists_comm_of_conj_mod {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hnab : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) {t : G}
    (ht : ∀ k ∈ K, t * k * t⁻¹ = k ∨ t * k * t⁻¹ = k * z) :
    ∃ u ∈ K, u * u ≠ 1 ∧ t * u = u * t := by
  by_contra hcon
  push Not at hcon
  have hzc : ∀ k ∈ K, k * z = z * k := fun k hk => comm_of_mem_uniqueInvolution hz hk
  have hact : ∀ x ∈ K, x * x ≠ 1 → t * x * t⁻¹ = x * z := by
    intro x hx hx2
    rcases ht x hx with h1 | h1
    · exact absurd (mul_inv_eq_iff_eq_mul.mp h1) (hcon x hx hx2)
    · exact h1
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  have hx2 : x * x ≠ 1 := fun h1 => hxy (comm_of_sq_eq_one hz hx h1 hy)
  have hy2 : y * y ≠ 1 := fun h1 => hxy (comm_of_sq_eq_one hz hy h1 hx).symm
  have hxy2 : (x * y) * (x * y) ≠ 1 := by
    intro h1
    rcases hz.unique _ (K.mul_mem hx hy) h1 with h2 | h2
    · apply hxy
      have h3 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h2
      rw [h3, mul_inv_cancel, inv_mul_cancel]
    · apply hxy
      have h3 : y * x = z := by
        calc y * x = x⁻¹ * (x * y) * x := by group
          _ = x⁻¹ * z * x := by rw [h2]
          _ = z := by rw [mul_assoc, ← hzc x hx, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h2, h3]
  refine hcon (x * y) (K.mul_mem hx hy) hxy2 ?_
  have h1 : t * (x * y) * t⁻¹ = x * y := by
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = (x * z) * (y * z) := by rw [hact x hx hx2, hact y hy hy2]
      _ = x * (z * y) * z := by group
      _ = x * (y * z) * z := by rw [← hzc y hy]
      _ = x * y * (z * z) := by group
      _ = x * y := by rw [hz.sq, mul_one]
  exact mul_inv_eq_iff_eq_mul.mp h1

namespace E4Hyp

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
include h

theorem nonabelian {L : Subgroup G} (hL : L ∈ Ω) : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  obtain ⟨-, P, ⟨hPL, -, hmax⟩, hnc⟩ := h.thmD.hyp.omega1 L hL
  have hLP : L = P := hmax L le_rfl (h.isPGroup hL) hPL
  by_contra hcon
  push Not at hcon
  apply hnc
  rw [← hLP]
  exact ⟨⟨fun a b => Subtype.ext (hcon a a.2 b b.2)⟩⟩

private theorem sq_sq_eq_one {K : Subgroup G} (hK : K ∈ Ω) {x : G} (hx : x ∈ K) :
    x * x * (x * x) = 1 := by
  by_contra hne
  have hord : orderOf x ∣ 2 ^ 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard K hx
    rwa [h.card_eq hK] at h1
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hk3 : k = 3 := by
    by_contra hk3
    have hk2 : k ≤ 2 := by omega
    have h1 : orderOf x ∣ 2 ^ 2 := by
      rw [hk']
      exact pow_dvd_pow 2 hk2
    apply hne
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    calc x * x * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by simpa using h2
  subst hk3
  have hcyc : IsCyclic ↥K := isCyclic_of_orderOf_eq_card (⟨x, hx⟩ : ↥K) (by
    rw [Subgroup.orderOf_mk, hk', h.card_eq hK]
    norm_num)
  obtain ⟨a, ha, b, hb, hab⟩ := h.nonabelian hK
  exact hab (congrArg Subtype.val
    ((IsCyclic.commutative (α := ↥K)).is_comm.comm (⟨a, ha⟩ : ↥K) ⟨b, hb⟩))

private theorem sq_eq_of_sq_ne_one {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {x : G} (hx : x ∈ K) (hx2 : x * x ≠ 1) : x * x = z :=
  (hz.unique _ (K.mul_mem hx hx) (h.sq_sq_eq_one hK hx)).resolve_left hx2

private theorem not_forall_comm {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : u ∈ K)
    (hu2 : u * u ≠ 1) : ¬ ∀ w ∈ K, u * w = w * u := by
  intro hcen
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hK
  have huz : u * u = z := h.sq_eq_of_sq_ne_one hK hz hu hu2
  have hle : ∀ x ∈ K, x ∈ Subgroup.zpowers u := by
    intro x hx
    by_cases hx2 : x * x = 1
    · rcases hz.unique x hx hx2 with rfl | rfl
      · exact one_mem _
      · rw [← huz]
        exact (Subgroup.zpowers u).mul_mem (Subgroup.mem_zpowers u) (Subgroup.mem_zpowers u)
    · have hxz : x * x = z := h.sq_eq_of_sq_ne_one hK hz hx hx2
      have h1 : (x * u) * (x * u) = 1 := by
        calc x * u * (x * u) = x * (u * x) * u := by group
          _ = x * (x * u) * u := by rw [hcen x hx]
          _ = (x * x) * (u * u) := by group
          _ = 1 := by rw [hxz, huz, hz.sq]
      rcases hz.unique _ (K.mul_mem hx hu) h1 with h2 | h2
      · have h3 : x = u⁻¹ := eq_inv_of_mul_eq_one_left h2
        rw [h3]
        exact (Subgroup.zpowers u).inv_mem (Subgroup.mem_zpowers u)
      · have h3 : x = u := mul_right_cancel (h2.trans huz.symm)
        rw [h3]
        exact Subgroup.mem_zpowers u
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian hK
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle x hx)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle y hy)
  exact hxy (Commute.zpow_zpow_self u i j).eq

theorem conj_eq_or_of_mem_pCore {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) {t : G} (ht : t ∈ pCore 2 G)
    (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    ∀ k ∈ L, t * k * t⁻¹ = k ∨ t * k * t⁻¹ = k * z := by
  intro k hk
  have hcL : t * k * t⁻¹ * k⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp htL k).mp hk) (L.inv_mem hk)
  have hcQ : t * k * t⁻¹ * k⁻¹ ∈ pCore 2 G := by
    have h1 : t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) := by group
    rw [h1]
    exact (pCore 2 G).mul_mem ht
      ((CFSG.pCore_normal (p := 2) (G := G)).conj_mem t⁻¹ ((pCore 2 G).inv_mem ht) k)
  have hcard := h.card_inf_pCore_le hL
  have hzQ := h.mem_pCore hL hz
  have h2 : t * k * t⁻¹ * k⁻¹ = 1 ∨ t * k * t⁻¹ * k⁻¹ = z := by
    by_contra hne
    push Not at hne
    have h3 := two_lt_card_of_three (H := L ⊓ pCore 2 G) (a := 1) (b := z)
      (c := t * k * t⁻¹ * k⁻¹) (one_mem _) ⟨hz.mem, hzQ⟩ ⟨hcL, hcQ⟩ hz.ne_one.symm
      (Ne.symm hne.1) (Ne.symm hne.2)
    omega
  rcases h2 with h2 | h2
  · exact Or.inl (mul_inv_eq_one.mp h2)
  · right
    rw [mul_inv_eq_iff_eq_mul] at h2
    rw [h2]
    exact (comm_of_mem_uniqueInvolution hz hk).symm

theorem normalizes_of_comm {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) (hKL : K ≠ L) {u : G}
    (hu : u ∈ K) (hu2 : u * u ≠ 1) {t : G} (ht : IsUniqueInvolution L t) (hut : u * t = t * u) :
    u ∈ Subgroup.normalizer (L : Set G) :=
  h.thmD.hyp.omega5 L hL K hK hKL.symm t ht u hu (h.not_forall_comm hK hu hu2)
    ((h.isPGroup hK).to_le (Subgroup.zpowers_le.mpr hu)) hut

private theorem false_of_three_of_isPGroup {L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ Ω) (h₂ : L₂ ∈ Ω)
    (h₃ : L₃ ∈ Ω) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) {P : Subgroup G}
    (hP : IsPGroup 2 ↥P) (hc₁ : 2 < Nat.card ↥(L₁ ⊓ P)) (hc₂ : 2 < Nat.card ↥(L₂ ⊓ P))
    (hc₃ : 2 < Nat.card ↥(L₃ ⊓ P)) : False := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact h.false_of_three S h₁ h₂ h₃ h12 h13 h23
    (hc₁.trans_le (Subgroup.card_le_of_le (inf_le_inf_left L₁ hS)))
    (hc₂.trans_le (Subgroup.card_le_of_le (inf_le_inf_left L₂ hS)))
    (hc₃.trans_le (Subgroup.card_le_of_le (inf_le_inf_left L₃ hS)))

theorem swap {A B : Subgroup G} (hp : Paired Ω A B) {L : Subgroup G} (hL : L ∈ Ω)
    (hLA : L ≠ A) (hLB : L ≠ B) {t : G} (ht : IsUniqueInvolution L t) :
    conjSub t A = B := by
  obtain ⟨S, hAS, hBS⟩ := h.exists_sylow_of_paired hp
  have htQ : t ∈ pCore 2 G := h.mem_pCore hL ht
  have htS : t ∈ (S : Subgroup G) :=
    IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := G)) S htQ
  have hconj : ∀ M : Subgroup G, M ≤ (S : Subgroup G) → conjSub t M ≤ (S : Subgroup G) := by
    intro M hM x hx
    rw [mem_conjSub_iff] at hx
    have h1 : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [h1]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem htS (hM hx))
      ((S : Subgroup G).inv_mem htS)
  have hA' : conjSub t A ∈ Ω := h.thmD.hyp.conjInvariant t A hp.1
  have hB' : conjSub t B ∈ Ω := h.thmD.hyp.conjInvariant t B hp.2.1
  have h1 : conjSub t A = A ∨ conjSub t A = B :=
    h.eq_or_eq_of_paired hp hAS hBS hA' (h.two_lt_card_inf_of_le hA' (hconj A hAS))
  have h2 : conjSub t B = A ∨ conjSub t B = B :=
    h.eq_or_eq_of_paired hp hAS hBS hB' (h.two_lt_card_inf_of_le hB' (hconj B hBS))
  have hne : conjSub t A ≠ conjSub t B := fun he => hp.2.2.1 (conjSub_injective t he)
  rcases h1 with h1 | h1
  · exfalso
    have h2' : conjSub t B = B := by
      rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · exact h2
    obtain ⟨a, ha⟩ := h.exists_uniqueInvolution hp.1
    obtain ⟨b, hb⟩ := h.exists_uniqueInvolution hp.2.1
    obtain ⟨u, hu, hu2, hut⟩ := exists_comm_of_conj_mod ha (h.nonabelian hp.1)
      (h.conj_eq_or_of_mem_pCore hp.1 ha htQ (mem_normalizer_of_conjSub_eq' h1))
    obtain ⟨u', hu', hu2', hut'⟩ := exists_comm_of_conj_mod hb (h.nonabelian hp.2.1)
      (h.conj_eq_or_of_mem_pCore hp.2.1 hb htQ (mem_normalizer_of_conjSub_eq' h2'))
    have huN := h.normalizes_of_comm hp.1 hL hLA.symm hu hu2 ht hut.symm
    have hu'N := h.normalizes_of_comm hp.2.1 hL hLB.symm hu' hu2' ht hut'.symm
    have hcomm : Commutes (Subgroup.zpowers u) (Subgroup.zpowers u') := by
      rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
      exact (Commute.zpow_zpow (hp.2.2.2 u hu u' hu') i j).eq
    have hz1 : IsPGroup 2 ↥(Subgroup.zpowers u) :=
      (h.isPGroup hp.1).to_le (Subgroup.zpowers_le.mpr hu)
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers u') :=
      (h.isPGroup hp.2.1).to_le (Subgroup.zpowers_le.mpr hu')
    have hH : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers u') :=
      IsPGroup.to_sup_of_normal_right' hz1 hz2 (le_normalizer_of_commutes' hcomm)
    have hP : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers u' ⊔ L) :=
      IsPGroup.to_sup_of_normal_right' hH (h.isPGroup hL)
        (sup_le (Subgroup.zpowers_le.mpr huN) (Subgroup.zpowers_le.mpr hu'N))
    exact h.false_of_three_of_isPGroup hp.1 hp.2.1 hL hp.2.2.1 hLA.symm hLB.symm hP
      (two_lt_card_inf_of_sq_ne_one hu
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))) hu2)
      (two_lt_card_inf_of_sq_ne_one hu'
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u'))) hu2')
      (h.two_lt_card_inf_of_le hL le_sup_right)
  · exact h1

theorem partner_unique {A B C : Subgroup G} (hp : Paired Ω A B) (hp' : Paired Ω A C) :
    B = C := by
  by_contra hBC
  obtain ⟨c, hc⟩ := h.exists_uniqueInvolution hp'.2.1
  have hs := h.swap hp hp'.2.1 (Ne.symm hp'.2.2.1) (Ne.symm hBC) hc
  rw [conjSub_eq_of_mem_of_commutes hc.mem hp'.2.2.2.symm] at hs
  exact hp.2.2.1 hs

theorem le_sup_pCore {A B : Subgroup G} (hp : Paired Ω A B) : B ≤ A ⊔ pCore 2 G := by
  obtain ⟨L, hL, hLA, hLB⟩ := h.exists_third hp
  obtain ⟨t, ht⟩ := h.exists_uniqueInvolution hL
  have hs := h.swap hp hL hLA hLB ht
  have htQ := h.mem_pCore hL ht
  intro x hx
  rw [← hs, mem_conjSub_iff] at hx
  obtain ⟨y, hyA, rfl⟩ : ∃ y ∈ A, x = t * y * t⁻¹ := ⟨t⁻¹ * x * t, hx, by group⟩
  have h1 : t * y * t⁻¹ = (t * (y * t⁻¹ * y⁻¹)) * y := by group
  rw [h1, sup_comm]
  exact Subgroup.mul_mem_sup ((pCore 2 G).mul_mem htQ
    ((CFSG.pCore_normal (p := 2) (G := G)).conj_mem t⁻¹ ((pCore 2 G).inv_mem htQ) y)) hyA

theorem eq_or_eq_of_le_sup {A B : Subgroup G} (hp : Paired Ω A B) {L : Subgroup G} (hL : L ∈ Ω)
    (hle : L ≤ A ⊔ pCore 2 G) : L = A ∨ L = B := by
  have hP : IsPGroup 2 ↥(A ⊔ pCore 2 G) :=
    IsPGroup.to_sup_of_normal_right' (h.isPGroup hp.1) (CFSG.pCore_isPGroup (p := 2) (G := G))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact h.eq_or_eq_of_paired hp (le_sup_left.trans hS) ((h.le_sup_pCore hp).trans hS) hL
    (h.two_lt_card_inf_of_le hL (hle.trans hS))

theorem inv_eq {A B : Subgroup G} (hp : Paired Ω A B) {a b : G} (ha : IsUniqueInvolution A a)
    (hb : IsUniqueInvolution B b) : a = b := by
  have key : ∀ (A' B' : Subgroup G) (a' b' : G), Paired Ω A' B' → IsUniqueInvolution A' a' →
      IsUniqueInvolution B' b' → a' * b' = a * b := by
    intro A' B' a' b' hp' ha' hb'
    by_cases hAA : A' = A
    · subst hAA
      have hBB : B = B' := h.partner_unique hp hp'
      subst hBB
      rw [ha.eq ha', hb.eq hb']
    · by_cases hAB : A' = B
      · subst hAB
        have hBA : A = B' := h.partner_unique hp.symm hp'
        subst hBA
        rw [hb.eq ha', ha.eq hb']
        exact hp'.2.2.2 a' ha'.mem b' hb'.mem
      · have hBA' : B' ≠ A := by
          intro hBA
          subst hBA
          exact hAB (h.partner_unique hp hp'.symm).symm
        have hBB' : B' ≠ B := by
          intro hBB
          subst hBB
          exact hAA (h.partner_unique hp.symm hp'.symm).symm
        have e1 : conjSub a' A = B := h.swap hp hp'.1 hAA hAB ha'
        have e2 : conjSub a A' = B' := h.swap hp' hp.1 (Ne.symm hAA) (Ne.symm hBA') ha
        have f1 : a' * a * a'⁻¹ = b := by
          have := ha.conj a'
          rw [e1] at this
          exact (hb.eq this).symm
        have f2 : a * a' * a⁻¹ = b' := by
          have := ha'.conj a
          rw [e2] at this
          exact (hb'.eq this).symm
        rw [inv_eq_of_mul_eq_one_right ha'.sq] at f1
        rw [inv_eq_of_mul_eq_one_right ha.sq] at f2
        calc a' * b' = b' * a' := hp'.2.2.2 a' ha'.mem b' hb'.mem
          _ = (a * a' * a) * a' := by rw [f2]
          _ = a * (a' * a * a') := by group
          _ = a * b := by rw [f1]
  have hab : a * b ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := key (conjSub g A) (conjSub g B) (g * a * g⁻¹) (g * b * g⁻¹)
      (hp.conj h.thmD.hyp.conjInvariant g) (ha.conj g) (hb.conj g)
    calc g * (a * b) = (g * a * g⁻¹) * (g * b * g⁻¹) * g := by group
      _ = (a * b) * g := by rw [hg]
  rw [h.center, Subgroup.mem_bot] at hab
  rw [eq_inv_of_mul_eq_one_left hab]
  exact inv_eq_of_mul_eq_one_right hb.sq

end E4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
