module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P D : Subgroup X} {z : X}

omit [Finite X] in
private theorem pow_eq_pow_mod_three {g : X} (hg : g ^ 3 = 1) (b : ℕ) : g ^ b = g ^ (b % 3) := by
  conv_lhs => rw [← Nat.mod_add_div b 3, pow_add, pow_mul, hg, one_pow, mul_one]

private theorem exists_pow_mul_pow_of_mem_sup {d e : X} (hzd : z * d = d * z)
    (he : e ∈ zpowers z ⊔ zpowers d) : ∃ a b : ℕ, e = z ^ a * d ^ b := by
  have hle : zpowers d ≤ normalizer (zpowers z : Set X) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun g hg => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    exact ((Commute.zpow_left (show Commute z d from hzd) k)).eq
  have h1 : e ∈ (↑(zpowers z ⊔ zpowers d) : Set X) := he
  rw [coe_mul_of_right_le_normalizer_left _ _ hle] at h1
  obtain ⟨u, hu, v, hv, rfl⟩ := h1
  obtain ⟨a, ha⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hu)
  obtain ⟨b, hb⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hv)
  exact ⟨a, b, by rw [ha, hb]⟩

omit [Finite X] in
private theorem isMulCommutative_zpowers_sup {a b : X} (hab : a * b = b * a) :
    IsMulCommutative (zpowers a ⊔ zpowers b : Subgroup X) := by
  have hs : zpowers a ⊔ zpowers b = closure {a, b} := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union, Set.insert_eq]
  rw [hs]
  refine isMulCommutative_closure ?_
  intro x hx y hy _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    first | exact Commute.refl _ | exact hab | exact hab.symm

omit [Finite X] in
private theorem isMulCommutative_of_le_mul_cyclic {Q N C R : Subgroup X} (hNQ : N ≤ Q)
    (hCQ : C ≤ Q) (hRQ : R ≤ Q) (hQN : Q ≤ normalizer (N : Set X)) (hC : IsCyclic C)
    (hRNC : ∀ r ∈ R, ∃ n ∈ N, ∃ c ∈ C, r = n * c)
    (hcen : ∀ r ∈ R, r ∈ N → ∀ s ∈ R, s * r = r * s) : IsMulCommutative R := by
  have : (N.subgroupOf Q).Normal := (normal_subgroupOf_iff_le_normalizer hNQ).2 hQN
  let q : ↥Q →* ↥Q ⧸ N.subgroupOf Q := QuotientGroup.mk' _
  let g : ↥C →* ↥Q ⧸ N.subgroupOf Q := q.comp (inclusion hCQ)
  let f : ↥R →* ↥Q ⧸ N.subgroupOf Q := q.comp (inclusion hRQ)
  have hf : ∀ r, f r ∈ g.range := by
    intro r
    obtain ⟨n, hn, c, hc, hrc⟩ := hRNC r.1 r.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show ((⟨c, hCQ hc⟩ : ↥Q) : ↥Q ⧸ N.subgroupOf Q) = ((⟨r.1, hRQ r.2⟩ : ↥Q) : ↥Q ⧸ N.subgroupOf Q)
    rw [QuotientGroup.eq, mem_subgroupOf]
    show c⁻¹ * r.1 ∈ N
    rw [hrc, ← mul_assoc]
    exact (mem_normalizer_iff''.1 (hQN (hCQ hc)) n).1 hn
  have : IsCyclic g.range := isCyclic_of_surjective g.rangeRestrict g.rangeRestrict_surjective
  let f' : ↥R →* g.range := f.codRestrict g.range hf
  refine f'.isMulCommutative_of_isCyclic_of_ker_le_center fun r hr => ?_
  have h1 : f r = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hr)
    simpa [f'] using this
  have h2 : (⟨r.1, hRQ r.2⟩ : ↥Q) ∈ N.subgroupOf Q := (QuotientGroup.eq_one_iff _).1 h1
  rw [mem_center_iff]
  intro s
  exact Subtype.ext (hcen r.1 r.2 h2 s.1 s.2)

omit [Finite X] in
private theorem conj_mem_zpowers_of_pow_three_pow {x d : X} (hd3 : d ^ 3 = 1)
    (hzd : z * d = d * z) (hzx : z * x = x * z) {n : ℕ} (hxn : x ^ 3 ^ n = 1)
    (he : ∃ a b : ℕ, x * d * x⁻¹ = z ^ a * d ^ b) : x * d * x⁻¹ * d⁻¹ ∈ zpowers z := by
  by_cases hdz : d ∈ zpowers z
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hdz
    have : x * z ^ k = z ^ k * x := ((Commute.zpow_left (show Commute z x from hzx) k).eq).symm
    rw [this, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · obtain ⟨a, b, hab⟩ := he
    rw [pow_eq_pow_mod_three hd3 b] at hab
    have hwx : z ^ a * x = x * z ^ a := (Commute.pow_left (show Commute z x from hzx) a).eq
    have hwd : z ^ a * d = d * z ^ a := (Commute.pow_left (show Commute z d from hzd) a).eq
    have hwmem : z ^ a ∈ zpowers z := pow_mem (mem_zpowers z) a
    have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hb with hb | hb | hb
    · exfalso
      apply hdz
      rw [hb, pow_zero, mul_one] at hab
      have : d = z ^ a := by
        calc d = x⁻¹ * (x * d * x⁻¹) * x := by group
          _ = x⁻¹ * z ^ a * x := by rw [hab]
          _ = z ^ a := by rw [mul_assoc, hwx, inv_mul_cancel_left]
      rw [this]
      exact hwmem
    · rw [hb, pow_one] at hab
      rw [hab, mul_assoc, mul_inv_cancel, mul_one]
      exact hwmem
    · exfalso
      apply hdz
      rw [hb] at hab
      have hd1 : d * d ^ 2 = 1 := by rw [← pow_succ']; exact hd3
      have hdinv : d ^ 2 = d⁻¹ := (inv_eq_of_mul_eq_one_right hd1).symm
      rw [hdinv] at hab
      have hxz : MulAut.conj x (z ^ a) = z ^ a := by
        show x * z ^ a * x⁻¹ = z ^ a
        rw [← hwx, mul_inv_cancel_right]
      have hsq : x * (x * d * x⁻¹) * x⁻¹ = d := by
        have h1 : x * (x * d * x⁻¹) * x⁻¹ = MulAut.conj x (z ^ a * d⁻¹) := by rw [hab]; rfl
        rw [h1, map_mul, map_inv, hxz]
        show z ^ a * (x * d * x⁻¹)⁻¹ = d
        rw [hab, mul_inv_rev, inv_inv, ← mul_assoc, hwd, mul_inv_cancel_right]
      have hxx : x * x * d = d * (x * x) :=
        calc x * x * d = (x * (x * d * x⁻¹) * x⁻¹) * (x * x) := by group
          _ = d * (x * x) := by rw [hsq]
      obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow ⟨1, by norm_num⟩
      rw [hm, pow_succ, pow_mul] at hxn
      have hcd : Commute (x ^ 2) d := by
        show x ^ 2 * d = d * x ^ 2
        rw [pow_two]
        exact hxx
      have hxd : Commute x d := by
        have h1 : x = ((x ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hxn
        have h2 : Commute ((x ^ 2) ^ m)⁻¹ d := (hcd.pow_left m).inv_left
        rwa [← h1] at h2
      have h2 : x * d * x⁻¹ = d := by rw [hxd.eq, mul_inv_cancel_right]
      rw [h2] at hab
      have h3 : d * d = z ^ a :=
        calc d * d = z ^ a * d⁻¹ * d := by rw [← hab]
          _ = z ^ a := by rw [inv_mul_cancel_right]
      have h4 : d⁻¹ = d * d :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← pow_succ']; exact hd3)
      rw [← inv_inv d, h4, h3]
      exact inv_mem hwmem

theorem PlaneData.inf_plane (h : PlaneData P D z)
    (hω : ∀ c ∈ P, (∀ d ∈ D, c * d = d * c) → c ^ 3 = 1 → c ∈ zpowers z)
    (hcyc : IsCyclic ↥(P ⊓ centralizer (D : Set X)))
    (hz : ∀ N : Subgroup X, N ≤ P → P ≤ normalizer (N : Set X) → N ≠ ⊥ → z ∈ N)
    (hinv : ∃ B : Subgroup X, B ≤ D ∧ Nat.card B = 9 ∧ IsElemAbelian 3 B ∧ z ∈ B ∧
      P ≤ normalizer (B : Set X))
    (hinner : ∀ x ∈ P, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ zpowers z) →
      ∃ δ ∈ D, ∀ d ∈ D, δ⁻¹ * x * d = d * (δ⁻¹ * x))
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) :
    ∀ R : Subgroup X, R ≤ P → P ≤ normalizer (R : Set X) → ¬ IsMulCommutative R →
      ∃ B : Subgroup X, B ≤ R ∧ B ≤ D ∧ Nat.card B = 9 ∧ IsElemAbelian 3 B ∧ z ∈ B ∧
        P ≤ normalizer (B : Set X) := by
  have _ := hω
  have _ := hcomm
  intro R hRP hPR hRnc
  have hDP : D ≤ P := h.plane.1
  have hRbot : R ≠ ⊥ := by
    rintro rfl
    exact hRnc inferInstance
  have hzR : z ∈ R := hz R hRP hPR hRbot
  have hzRD : z ∈ R ⊓ D := mem_inf.2 ⟨hzR, h.zD⟩
  have hPRD : P ≤ normalizer ((R ⊓ D : Subgroup X) : Set X) :=
    le_trans (le_inf hPR h.normal) inf_normalizer_le_normalizer_inf
  have hex : ∃ d₀ ∈ R ⊓ D, d₀ ∉ zpowers z := by
    by_contra hno
    push Not at hno
    refine hRnc (isMulCommutative_of_le_mul_cyclic (N := D) (C := P ⊓ centralizer (D : Set X))
      hDP inf_le_left hRP h.normal hcyc ?_ ?_)
    · intro r hr
      have hrP : r ∈ P := hRP hr
      have hcomm' : ∀ d ∈ D, r * d * r⁻¹ * d⁻¹ ∈ zpowers z := by
        intro d hd
        apply hno
        refine mem_inf.2 ⟨?_, ?_⟩
        · have h1 : d * r⁻¹ * d⁻¹ ∈ R :=
            (mem_normalizer_iff.1 (hPR (hDP hd)) r⁻¹).1 (inv_mem hr)
          have h2 := mul_mem hr h1
          rwa [← mul_assoc, ← mul_assoc] at h2
        · have h1 : r * d * r⁻¹ ∈ D := (mem_normalizer_iff.1 (h.normal hrP) d).1 hd
          exact mul_mem h1 (inv_mem hd)
      obtain ⟨δ, hδ, hc⟩ := hinner r hrP hcomm'
      have hcP : δ⁻¹ * r ∈ P := mul_mem (inv_mem (hDP hδ)) hrP
      have hcC : δ⁻¹ * r ∈ centralizer (D : Set X) :=
        mem_centralizer_iff.2 fun d hd => (hc d hd).symm
      exact ⟨δ, hδ, δ⁻¹ * r, mem_inf.2 ⟨hcP, hcC⟩, by group⟩
    · intro r hr hrD s hs
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (hno r (mem_inf.2 ⟨hr, hrD⟩))
      exact ((Commute.zpow_left (show Commute z s from h.zc s (hRP hs)) k).eq).symm
  obtain ⟨d₀, hd₀, hd₀z⟩ := hex
  have hd₀D : d₀ ∈ D := (mem_inf.1 hd₀).2
  have hd₀3 : d₀ ^ 3 = 1 := h.plane.2.2.1 d₀ hd₀D
  have hzd : z * d₀ = d₀ * z := h.zc d₀ (hDP hd₀D)
  have hB₀RD : zpowers z ⊔ zpowers d₀ ≤ R ⊓ D := sup_le (zpowers_le.2 hzRD) (zpowers_le.2 hd₀)
  have hB₀card : Nat.card ↥(zpowers z ⊔ zpowers d₀) = 9 := by
    have h1 := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers z) hd₀3
      hd₀z (fun e he => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 he
        exact (Commute.zpow_left (show Commute z d₀ from hzd) k).eq)
    rw [h1, Nat.card_zpowers, h.zo]
  have hB₀el : IsElemAbelian 3 (zpowers z ⊔ zpowers d₀) :=
    ⟨isMulCommutative_zpowers_sup hzd, fun x hx => h.plane.2.2.1 x (mem_inf.1 (hB₀RD hx)).2⟩
  have hdvd1 : 9 ∣ Nat.card ↥(R ⊓ D) := hB₀card ▸ Subgroup.card_dvd_of_le hB₀RD
  have hdvd2 : Nat.card ↥(R ⊓ D) ∣ 3 ^ 3 := h.card ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcases : Nat.card ↥(R ⊓ D) = 9 ∨ Nat.card ↥(R ⊓ D) = 27 := by
    obtain ⟨m, hm⟩ := hdvd1
    rw [hm] at hdvd2 ⊢
    have hm3 : m ≤ 3 := by
      have := Nat.le_of_dvd (by norm_num) hdvd2
      omega
    interval_cases m <;> omega
  rcases hcases with hc | hc
  · have heq : zpowers z ⊔ zpowers d₀ = R ⊓ D :=
      eq_of_le_of_card_ge hB₀RD (by rw [hB₀card, hc])
    refine ⟨zpowers z ⊔ zpowers d₀, hB₀RD.trans inf_le_left, hB₀RD.trans inf_le_right, hB₀card,
      hB₀el, mem_sup_left (mem_zpowers z), ?_⟩
    rw [heq]
    exact hPRD
  · have heq : R ⊓ D = D := eq_of_le_of_card_ge inf_le_right (by rw [hc, h.card]; norm_num)
    have hDR : D ≤ R := heq ▸ inf_le_left
    obtain ⟨B, hBD, hBc, hBe, hzB, hPB⟩ := hinv
    exact ⟨B, hBD.trans hDR, hBD, hBc, hBe, hzB, hPB⟩

theorem PlaneData.not_normal (h : PlaneData P D z)
    (hinner : ∀ x ∈ P, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ zpowers z) →
      ∃ δ ∈ D, ∀ d ∈ D, δ⁻¹ * x * d = d * (δ⁻¹ * x))
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) :
    ∃ D' : Subgroup X, D' ≤ P ∧ (∀ x ∈ D', x ^ 3 = 1) ∧ z ∈ D' ∧
      ¬ P ≤ normalizer (D' : Set X) := by
  have _ := hcomm
  by_contra hcon
  push Not at hcon
  have hDP : D ≤ P := h.plane.1
  have key : ∀ x ∈ P, ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ zpowers z := by
    intro x hx d hd
    have hBD : zpowers z ⊔ zpowers d ≤ D := sup_le (zpowers_le.2 h.zD) (zpowers_le.2 hd)
    have hnorm := hcon (zpowers z ⊔ zpowers d) (hBD.trans hDP)
      (fun y hy => h.plane.2.2.1 y (hBD hy)) (mem_sup_left (mem_zpowers z))
    have hxe : x * d * x⁻¹ ∈ zpowers z ⊔ zpowers d :=
      (mem_normalizer_iff.1 (hnorm hx) d).1 (mem_sup_right (mem_zpowers d))
    obtain ⟨n, hn⟩ := h.pgroup ⟨x, hx⟩
    have hxn : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hzd : z * d = d * z := h.zc d (hDP hd)
    exact conj_mem_zpowers_of_pow_three_pow (h.plane.2.2.1 d hd) hzd (h.zc x hx) hxn
      (exists_pow_mul_pow_of_mem_sup hzd hxe)
  have hle : P ≤ D ⊔ (P ⊓ centralizer (D : Set X)) := by
    intro x hx
    obtain ⟨δ, hδ, hc⟩ := hinner x hx (key x hx)
    have hx' : x = δ * (δ⁻¹ * x) := by group
    have hcP : δ⁻¹ * x ∈ P := mul_mem (inv_mem (hDP hδ)) hx
    have hcC : δ⁻¹ * x ∈ centralizer (D : Set X) :=
      mem_centralizer_iff.2 fun d hd => (hc d hd).symm
    rw [hx']
    exact mul_mem_sup hδ (mem_inf.2 ⟨hcP, hcC⟩)
  have h1 := pRank_mono 3 (by norm_num) hle
  have h2 := h.plane.2.2.2
  have h3 := h.rank
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
