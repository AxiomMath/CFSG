module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Rank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem eq_one_of_pow_eq_one {f p n : ℕ} [Fact f.Prime] (hp : p.Prime) (hpf : p ≠ f)
    {G : Type*} [Group G] (hG : IsPGroup f G) {y : G} (hy : y ^ (p ^ n) = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hG y
  have h1 : f ^ k ∣ p ^ n := hk ▸ orderOf_dvd_of_pow_eq_one hy
  have hcop : Nat.Coprime (f ^ k) (p ^ n) :=
    Nat.Coprime.pow k n ((Nat.coprime_primes (Fact.out : f.Prime) hp).mpr hpf.symm)
  have h2 : f ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop h1
  exact orderOf_eq_one_iff.mp (by rw [hk, h2])

theorem isPGroup_zpowers_of_pow_eq_one {p n : ℕ} (hp : p.Prime) {t : K} (htn : t ^ (p ^ n) = 1) :
    IsPGroup p (zpowers t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : orderOf t ∣ p ^ n := orderOf_dvd_of_pow_eq_one htn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem pow_eq_one_of_commute {t x : K} {m : ℕ} (htm : t ^ m = 1)
    (hty : t * (x⁻¹ * (t * x * t⁻¹)) = (x⁻¹ * (t * x * t⁻¹)) * t) :
    (x⁻¹ * (t * x * t⁻¹)) ^ m = 1 := by
  set y : K := x⁻¹ * (t * x * t⁻¹) with hy
  have hty' : t * y * t⁻¹ = y := by rw [hty]; group
  have hxy : t * x * t⁻¹ = x * y := by rw [hy]; group
  have hk : ∀ k : ℕ, t ^ k * x * (t ^ k)⁻¹ = x * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc t ^ (k + 1) * x * (t ^ (k + 1))⁻¹ = t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹ := by group
        _ = t * (x * y ^ k) * t⁻¹ := by rw [ih]
        _ = (t * x * t⁻¹) * (t * y ^ k * t⁻¹) := by group
        _ = (x * y) * y ^ k := by rw [hxy, ← conj_pow, hty']
        _ = x * y ^ (k + 1) := by rw [pow_succ', mul_assoc]
  have h1 := hk m
  rw [htm] at h1
  have h2 : x * y ^ m = x := by simpa using h1.symm
  simpa using h2

theorem centralizes_of_critical_pElt {f p n : ℕ} [Fact f.Prime] (hp : p.Prime) (hpf : p ≠ f)
    {X : Subgroup K} (hX : IsPGroup f X) (C₀ : Subgroup ↥X)
    (hC₀ : CFSG.SectionRank.Ccomm.IsThompsonCritical C₀)
    {t : K} (htn : t ^ (p ^ n) = 1) (htX : t ∈ normalizer (X : Set K))
    (htC : ∀ x ∈ C₀.map X.subtype, t * x = x * t) : ∀ x ∈ X, t * x = x * t := by
  obtain ⟨-, -, hcomm, hcent⟩ := hC₀
  intro x hx
  have huX : t * x * t⁻¹ ∈ X := (mem_normalizer_iff.mp htX x).mp hx
  have hyX : x⁻¹ * (t * x * t⁻¹) ∈ X := X.mul_mem (X.inv_mem hx) huX
  have htC' : ∀ c ∈ C₀, t * (c : K) = (c : K) * t := fun c hc => htC c ⟨c, hc, rfl⟩
  have hyc : (⟨x⁻¹ * (t * x * t⁻¹), hyX⟩ : ↥X) ∈ centralizer (C₀ : Set ↥X) := by
    rw [mem_centralizer_iff]
    intro c hc
    apply Subtype.ext
    have hd : ⁅(⟨x, hx⟩ : ↥X), c⁆ ∈ C₀ :=
      (hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hc)).1
    have hdt : t * ⁅x, (c : K)⁆ = ⁅x, (c : K)⁆ * t := htC' _ hd
    exact frattini_commute_of_commutator (htC' c hc) hdt
  have hyC : (⟨x⁻¹ * (t * x * t⁻¹), hyX⟩ : ↥X) ∈ C₀ := (hcent.le hyc).1
  have hyt : t * (x⁻¹ * (t * x * t⁻¹)) = (x⁻¹ * (t * x * t⁻¹)) * t := htC' _ hyC
  have hy1 : (x⁻¹ * (t * x * t⁻¹)) ^ (p ^ n) = 1 := pow_eq_one_of_commute htn hyt
  have hy : (⟨x⁻¹ * (t * x * t⁻¹), hyX⟩ : ↥X) = 1 :=
    eq_one_of_pow_eq_one hp hpf hX (Subtype.ext (by simpa using hy1))
  have hy' : x⁻¹ * (t * x * t⁻¹) = 1 := congrArg Subtype.val hy
  have hx' : x = t * x * t⁻¹ := inv_mul_eq_one.mp hy'
  calc t * x = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [← hx']

theorem fixed_of_pow_fixed {f p n : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (hp : p.Prime) (hpf : p ≠ f)
    {C : Subgroup K} (hC : IsPGroup f C)
    (hP' : ∀ x ∈ C, ∀ y ∈ C, ∀ w ∈ C, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hPf : ∀ x ∈ C, ∀ w ∈ C, w * x ^ f = x ^ f * w)
    {t : K} (htn : t ^ (p ^ n) = 1) (htC : t ∈ normalizer (C : Set K))
    (hΩ : ∀ y ∈ C, y ^ f = 1 → t * y = y * t) : ∀ x ∈ C, t * x = x * t := by
  have hf : f.Prime := Fact.out
  have key : ∀ k : ℕ, ∀ x ∈ C, x ^ (f ^ k) = 1 → t * x = x * t := by
    intro k
    induction k with
    | zero =>
      intro x _ hx1
      have : x = 1 := by simpa using hx1
      subst this
      simp
    | succ k ih =>
      intro x hx hxk
      have hxf : x ^ f ∈ C := C.pow_mem hx f
      have hxf1 : (x ^ f) ^ (f ^ k) = 1 := by rw [← pow_mul, ← pow_succ']; exact hxk
      have htxf : t * x ^ f = x ^ f * t := ih _ hxf hxf1
      have huC : t * x * t⁻¹ ∈ C := (mem_normalizer_iff.mp htC x).mp hx
      have hyC : x⁻¹ * (t * x * t⁻¹) ∈ C := C.mul_mem (C.inv_mem hx) huC
      have hyf : (x⁻¹ * (t * x * t⁻¹)) ^ f = 1 := by
        rw [pow_mul_of_central hf hf2 hP' hPf (C.inv_mem hx) huC, inv_pow, conj_pow]
        have : t * x ^ f * t⁻¹ = x ^ f := by rw [htxf]; group
        rw [this, inv_mul_cancel]
      have hyt : t * (x⁻¹ * (t * x * t⁻¹)) = (x⁻¹ * (t * x * t⁻¹)) * t := hΩ _ hyC hyf
      have hy1 : (x⁻¹ * (t * x * t⁻¹)) ^ (p ^ n) = 1 := pow_eq_one_of_commute htn hyt
      have hy : (⟨x⁻¹ * (t * x * t⁻¹), hyC⟩ : ↥C) = 1 :=
        eq_one_of_pow_eq_one hp hpf hC (Subtype.ext (by simpa using hy1))
      have hy' : x⁻¹ * (t * x * t⁻¹) = 1 := congrArg Subtype.val hy
      have hx' : x = t * x * t⁻¹ := inv_mul_eq_one.mp hy'
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [← hx']
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hC ⟨x, hx⟩
  exact key k x hx (by
    have := pow_orderOf_eq_one (⟨x, hx⟩ : ↥C)
    rw [hk] at this
    simpa using congrArg Subtype.val this)

def trivOnQuot (C M₀ : Subgroup K) : Subgroup K where
  carrier := {s | s ∈ normalizer (C : Set K) ∧ ∀ x ∈ C, x⁻¹ * (s * x * s⁻¹) ∈ M₀}
  mul_mem' := by
    rintro s₁ s₂ ⟨hs₁, h₁⟩ ⟨hs₂, h₂⟩
    refine ⟨mul_mem hs₁ hs₂, fun x hx => ?_⟩
    have hx' : s₂ * x * s₂⁻¹ ∈ C := (mem_normalizer_iff.mp hs₂ x).mp hx
    have e : x⁻¹ * (s₁ * s₂ * x * (s₁ * s₂)⁻¹) =
        (x⁻¹ * (s₂ * x * s₂⁻¹)) *
          ((s₂ * x * s₂⁻¹)⁻¹ * (s₁ * (s₂ * x * s₂⁻¹) * s₁⁻¹)) := by group
    rw [e]
    exact M₀.mul_mem (h₂ x hx) (h₁ _ hx')
  one_mem' := ⟨one_mem _, fun x _ => by simpa using M₀.one_mem⟩
  inv_mem' := by
    rintro s ⟨hs, h⟩
    refine ⟨inv_mem hs, fun x hx => ?_⟩
    have hx'' : s⁻¹ * x * s⁻¹⁻¹ ∈ C := (mem_normalizer_iff.mp (inv_mem hs) x).mp hx
    have h1 := h _ hx''
    have e1 : s * (s⁻¹ * x * s⁻¹⁻¹) * s⁻¹ = x := by group
    rw [e1] at h1
    have h2 : x⁻¹ * (s⁻¹ * x * s⁻¹⁻¹) = ((s⁻¹ * x * s⁻¹⁻¹)⁻¹ * x)⁻¹ := by group
    rw [h2]
    exact M₀.inv_mem h1

theorem eq_of_trivial_on_quotient_pElt {f p n : ℕ} [Fact f.Prime] (hp : p.Prime) (hpf : p ≠ f)
    {C M₀ : Subgroup K} (hC : IsPGroup f C) (hM : M₀ ≤ C)
    (hMn : ∀ x ∈ C, ∀ m ∈ M₀, x * m * x⁻¹ ∈ M₀) (hfr : M₀.subgroupOf C ≤ frattini ↥C)
    {t : K} (htn : t ^ (p ^ n) = 1) (htC : t ∈ normalizer (C : Set K))
    (htM : t ∈ normalizer (M₀ : Set K))
    (htriv : ∀ x ∈ C, x⁻¹ * (t * x * t⁻¹) ∈ M₀) : ∀ x ∈ C, t * x = x * t := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hM0 : IsPGroup f M₀ := hC.to_le hM
  have hq : ¬ p ∣ Nat.card M₀ := by
    obtain ⟨k, hk⟩ := hM0.exists_card_eq
    rw [hk]
    intro h
    exact hpf ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : f.Prime)).mp (hp.dvd_of_dvd_pow h))
  have hzp : IsPGroup p (zpowers t) := isPGroup_zpowers_of_pow_eq_one hp htn
  have hex : ∀ x ∈ C, ∃ m ∈ M₀, t * (x * m) * t⁻¹ = x * m := by
    intro x hx
    have hS : zpowers t ≤ trivOnQuot C M₀ := zpowers_le.mpr ⟨htC, htriv⟩
    obtain ⟨m, hm, hfix⟩ := exists_fixed_in_coset (q := p) hzp
      (zpowers_le.mpr htM) hq (x := x) (fun s hs => (hS hs).2 x hx)
    exact ⟨m, hm, hfix t (mem_zpowers t)⟩
  let H : Subgroup ↥C := (centralizer ({t} : Set K)).subgroupOf C
  have hsup : H ⊔ frattini ↥C = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨m, hm, hfix⟩ := hex g g.2
    have hmC : m ∈ C := hM hm
    have h1 : (⟨(g : K) * m, C.mul_mem g.2 hmC⟩ : ↥C) ∈ H := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      change (g : K) * m * t = t * ((g : K) * m)
      calc (g : K) * m * t = t * (g * m) * t⁻¹ * t := by rw [hfix]
        _ = t * ((g : K) * m) := by group
    have h2 : (⟨m, hmC⟩ : ↥C)⁻¹ ∈ frattini ↥C :=
      inv_mem (hfr (Subgroup.mem_subgroupOf.mpr hm))
    have hg : g = (⟨(g : K) * m, C.mul_mem g.2 hmC⟩ : ↥C) * (⟨m, hmC⟩ : ↥C)⁻¹ := by
      apply Subtype.ext
      simp
    rw [hg]
    exact Subgroup.mul_mem_sup h1 h2
  have htop : H = ⊤ := frattini_nongenerating hsup
  intro x hx
  have hxH : (⟨x, hx⟩ : ↥C) ∈ H := by rw [htop]; exact Subgroup.mem_top _
  have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hxH)
  exact this.symm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
