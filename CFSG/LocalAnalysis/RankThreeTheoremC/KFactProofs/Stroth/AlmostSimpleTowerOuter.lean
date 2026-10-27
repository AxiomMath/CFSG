module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerSylow
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LieType.SeitzGeneration.OrthThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem mul_pow_mul_inv_pow_mem {G : Type*} [Group G] {D : Subgroup G} [D.Normal] {c : G}
    (hc : c ∈ D) (f : G) (m : ℕ) : (c * f) ^ m * (f ^ m)⁻¹ ∈ D := by
  induction m with
  | zero => simp [D.one_mem]
  | succ m ih =>
    have : (c * f) ^ (m + 1) * (f ^ (m + 1))⁻¹ =
        ((c * f) ^ m * (f ^ m)⁻¹) * (f ^ m * c * (f ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [this]
    exact D.mul_mem ih (‹D.Normal›.conj_mem c hc (f ^ m))

theorem apply_eq_self_iff_commute_conj_of_injective {P : Type*} [Group P]
    (hconj : Function.Injective (MulAut.conj : P →* MulAut P)) (α : MulAut P) (y : P) :
    α y = y ↔ α * MulAut.conj y = MulAut.conj y * α := by
  have h : α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
    ext z
    simp [MulAut.conj_apply]
  constructor
  · intro hy
    rw [hy] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hc
    apply hconj
    rw [← h, hc, mul_inv_cancel_right]

section Abstract

variable {P : Type} [Group P] [Finite P] {Γ : Type*} [Group Γ]

theorem exists_fld_conj_of_pElement (fld : Γ →* MulAut P) (D : Subgroup (MulAut P)) [hDn : D.Normal]
    {p : ℕ} (hp : p.Prime) (hIDle : inner P ≤ D)
    (hDI : ∀ w ∈ D, (∃ k : ℕ, w ^ (p ^ k) = 1) → w ∈ inner P)
    (hfld : ∀ σ : Γ, fld σ ∈ D → σ = 1)
    (hdec : ∀ z : MulAut P, (∃ k : ℕ, z ^ (p ^ k) = 1) → ∃ c ∈ D, ∃ σ : Γ, z = c * fld σ)
    {α : MulAut P} (hα : ∃ k : ℕ, α ^ (p ^ k) = 1) (hαI : α ∉ inner P) :
    ∃ (s : ℕ) (ι d : MulAut P) (τ : Γ), ι ∈ inner P ∧ d ∈ D ∧ orderOf τ = p ∧
      α ^ (p ^ s) = ι * (d * fld τ * d⁻¹) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut P) := CFSG.RankThree.PartOne.OutStructure.instFiniteMulAut' _
  haveI hIn : (inner P).Normal := inner_normal _
  obtain ⟨k, hk⟩ := hα
  have hαD : α ∉ D := fun h => hαI (hDI α h ⟨k, hk⟩)
  have hex : ∃ t : ℕ, α ^ (p ^ t) ∈ D := ⟨k, by rw [hk]; exact one_mem _⟩
  have ht : α ^ (p ^ Nat.find hex) ∈ D := Nat.find_spec hex
  have ht0 : Nat.find hex ≠ 0 := fun h0 => hαD (by
    have := ht
    rwa [h0, pow_zero, pow_one] at this)
  obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := Nat.exists_eq_succ_of_ne_zero ht0
  have hzD : α ^ (p ^ s) ∉ D := Nat.find_min hex (by omega)
  have hzp : (α ^ (p ^ s)) ^ p ∈ D := by
    rw [← pow_mul, ← pow_succ, ← hs]
    exact ht
  have hsk : s + 1 ≤ k := hs ▸ Nat.find_min' hex (by rw [hk]; exact one_mem _)
  have hzpow : (α ^ (p ^ s)) ^ (p ^ (k - s)) = 1 := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]
    exact hk
  obtain ⟨c, hcD, σ, hzcσ⟩ := hdec (α ^ (p ^ s)) ⟨k - s, hzpow⟩
  set z := α ^ (p ^ s) with hz
  set f := fld σ with hf
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hzD
    rw [hzcσ, hf, map_one, mul_one]
    exact hcD
  have hfp : f ^ p ∈ D := by
    have h1 := mul_pow_mul_inv_pow_mem hcD f p
    rw [← hzcσ] at h1
    have : f ^ p = (z ^ p * (f ^ p)⁻¹)⁻¹ * z ^ p := by group
    rw [this]
    exact D.mul_mem (D.inv_mem h1) hzp
  have hσp : σ ^ p = 1 := hfld _ (by rw [map_pow]; exact hfp)
  have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hfp1 : f ^ p = 1 := by rw [hf, ← map_pow, hσp, map_one]
  set G₁ : Subgroup (MulAut P) := D ⊔ Subgroup.zpowers f with hG₁
  have hfG : f ∈ G₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hDG : D ≤ G₁ := le_sup_left
  have hzG : z ∈ G₁ := by
    rw [hzcσ]
    exact G₁.mul_mem (hDG hcD) hfG
  let Dg : Subgroup G₁ := D.subgroupOf G₁
  let Ig : Subgroup G₁ := (inner P).subgroupOf G₁
  haveI : Dg.Normal := Subgroup.Normal.subgroupOf hDn G₁
  haveI : Ig.Normal := Subgroup.Normal.subgroupOf hIn G₁
  have hIDg : Ig ≤ Dg := fun x hx => hIDle hx
  have hDIg : ∀ w ∈ Dg, (∃ k : ℕ, w ^ (p ^ k) = 1) → w ∈ Ig := by
    rintro w hw ⟨m, hm⟩
    exact hDI w hw ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hfg1 : (⟨f, hfG⟩ : G₁) ^ p = 1 := Subtype.ext (by simpa using hfp1)
  have hGg : ∀ x : G₁, ∃ d ∈ Dg, ∃ i : ℕ, x = d * (⟨f, hfG⟩ : G₁) ^ i := by
    rintro ⟨x, hx⟩
    obtain ⟨d, hd, y, hy, hdy⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    have hy' : y ∈ Submonoid.powers f := by
      rw [mem_powers_iff_mem_zpowers]
      exact hy
    obtain ⟨i, rfl⟩ := hy'
    refine ⟨⟨d, hDG hd⟩, hd, i, Subtype.ext ?_⟩
    simp [← hdy]
  have hzg : ∃ m : ℕ, (⟨z, hzG⟩ : G₁) ^ (p ^ m) = 1 :=
    ⟨k - s, Subtype.ext (by exact hzpow)⟩
  have hzDg : (⟨z, hzG⟩ : G₁) ∉ Dg := fun h => hzD (Subgroup.mem_subgroupOf.1 h)
  obtain ⟨d, hd, i, hpi, ι, hι, hzdι⟩ := exists_conj_pow_of_pElement hIDg hDIg hfg1 hGg hzg hzDg
  have hzeq : z = (ι : MulAut P) * ((d : MulAut P) * f ^ i * (d : MulAut P)⁻¹) := by
    have := congrArg Subtype.val hzdι
    simpa using this
  have hcop : Nat.Coprime p i := (Nat.Prime.coprime_iff_not_dvd hp).2 hpi
  refine ⟨s, ι, d, σ ^ i, Subgroup.mem_subgroupOf.1 hι, Subgroup.mem_subgroupOf.1 hd, ?_, ?_⟩
  · rw [Nat.Coprime.orderOf_pow (by rw [hσo]; exact hcop), hσo]
  · rw [map_pow]
    exact hzeq

theorem pElements_inner_of_two_indep (fld : Γ →* MulAut P) (D : Subgroup (MulAut P))
    [D.Normal] {p : ℕ} (hp : p.Prime) (hIDle : inner P ≤ D)
    (hDI : ∀ w ∈ D, (∃ k : ℕ, w ^ (p ^ k) = 1) → w ∈ inner P)
    (hfld : ∀ σ : Γ, fld σ ∈ D → σ = 1)
    (hdec : ∀ z : MulAut P, (∃ k : ℕ, z ^ (p ^ k) = 1) → ∃ c ∈ D, ∃ σ : Γ, z = c * fld σ)
    (hconj : Function.Injective (MulAut.conj : P →* MulAut P))
    (hTwo : ∀ τ : Γ, orderOf τ = p → ∃ x₁ x₂ : P, Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      fld τ x₁ = x₁ ∧ fld τ x₂ = x₂)
    {X : Type} [Group X] [Finite X] (hrk : CFSG.LieType.SeitzGeneration.RankLE2 p X)
    (ψ : X →* MulAut P) (hψ : Function.Injective ψ) (L : Subgroup X)
    (hL : ∀ y : P, ∃ l ∈ L, ψ l = MulAut.conj y)
    {x : X} (hx : ∃ k : ℕ, x ^ (p ^ k) = 1) : ψ x ∈ inner P := by
  classical
  by_contra hαI
  have hαp : ∃ k : ℕ, (ψ x) ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨s, ι, d, τ, hιI, hdD, hτ, hz⟩ :=
    exists_fld_conj_of_pElement fld D hp hIDle hDI hfld hdec hαp hαI
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₁, x₂, hc, h1, h2, hi, hfix1, hfix2⟩ := hTwo τ hτ
  have hτp : τ ^ p = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ
    exact hp.one_lt.ne hτ
  set a : MulAut P := d * fld τ * d⁻¹ with ha
  have hap : a ^ p = 1 := by
    rw [ha, conj_pow, ← map_pow, hτp, map_one]
    group
  have haD : a ∉ D := by
    intro h
    have : fld τ ∈ D := by
      have h' : d⁻¹ * a * d ∈ D := D.mul_mem (D.mul_mem (D.inv_mem hdD) h) hdD
      have : d⁻¹ * a * d = fld τ := by rw [ha]; group
      rwa [this] at h'
    exact hτ1 (hfld τ this)
  have haI : a ∉ inner P := fun h => haD (hIDle h)
  obtain ⟨yι, hyι⟩ := hιI
  obtain ⟨l₁, hl₁L, hl₁⟩ := hL yι
  obtain ⟨l₂, hl₂L, hl₂⟩ := hL (d x₁)
  obtain ⟨l₃, hl₃L, hl₃⟩ := hL (d x₂)
  obtain ⟨e₁, hψe₁⟩ : ∃ e₁ : X, ψ e₁ = a := ⟨l₁⁻¹ * x ^ (p ^ s), by
    rw [map_mul, map_inv, map_pow, hl₁, hyι, hz]
    group⟩
  have hfa : ∀ y : P, fld τ y = y → a * MulAut.conj (d y) = MulAut.conj (d y) * a := by
    intro y hy
    refine (apply_eq_self_iff_commute_conj_of_injective hconj a (d y)).1 ?_
    simp [ha, MulAut.mul_apply, hy]
  have hconjmul : ∀ u v : P, Commute u v →
      MulAut.conj (d u) * MulAut.conj (d v) = MulAut.conj (d v) * MulAut.conj (d u) := by
    intro u v huv
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, huv.eq]
  have hpow : ∀ u : P, u ^ p = 1 → (MulAut.conj (d u)) ^ p = 1 := by
    intro u hu
    rw [← map_pow, ← map_pow, hu, map_one, map_one]
  refine CFSG.LieType.SeitzGeneration.false_of_three_independent hp hrk (e₁ := e₁) (e₂ := l₂)
    (e₃ := l₃) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine hψ ?_
    rw [map_mul, map_mul, hψe₁, hl₂]
    exact hfa x₁ hfix1
  · refine hψ ?_
    rw [map_mul, map_mul, hψe₁, hl₃]
    exact hfa x₂ hfix2
  · refine hψ ?_
    rw [map_mul, map_mul, hl₂, hl₃]
    exact hconjmul x₁ x₂ hc
  · refine hψ ?_
    rw [map_pow, hψe₁, map_one, hap]
  · refine hψ ?_
    rw [map_pow, hl₂, map_one]
    exact hpow x₁ h1
  · refine hψ ?_
    rw [map_pow, hl₃, map_one]
    exact hpow x₂ h2
  · intro i j k hijk
    have hψ1 := congrArg ψ hijk
    rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, hψe₁, hl₂, hl₃, map_one] at hψ1
    have hun : (MulAut.conj (d x₁)) ^ j * (MulAut.conj (d x₂)) ^ k =
        MulAut.conj ((d x₁) ^ j * (d x₂) ^ k) := by
      rw [map_mul, map_zpow, map_zpow]
    have hai : a ^ i = (MulAut.conj ((d x₁) ^ j * (d x₂) ^ k))⁻¹ := by
      rw [← hun]
      exact eq_inv_of_mul_eq_one_left (by rwa [mul_assoc] at hψ1)
    have hpi : (p : ℤ) ∣ i := by
      by_contra hpi
      have hcop : IsCoprime (p : ℤ) i :=
        (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.2 hpi
      obtain ⟨u, v, huv⟩ := hcop
      have hainner : a ^ i ∈ inner P := by
        rw [hai]
        exact (inner P).inv_mem ⟨_, rfl⟩
      have : a = (a ^ i) ^ v := by
        rw [← zpow_mul, mul_comm i v]
        have h5 : v * i = 1 + (p : ℤ) * (-u) := by linarith
        rw [h5, zpow_add, zpow_one, zpow_mul, zpow_natCast, hap, one_zpow, mul_one]
      exact haI (this ▸ (inner P).zpow_mem hainner v)
    obtain ⟨c', hc'⟩ := id hpi
    have hai1 : a ^ i = 1 := by
      rw [hc', zpow_mul, zpow_natCast, hap, one_zpow]
    have hconj1 : MulAut.conj ((d x₁) ^ j * (d x₂) ^ k) = 1 := by
      rw [hai1] at hai
      exact inv_eq_one.1 hai.symm
    have hy1 : (d x₁) ^ j * (d x₂) ^ k = 1 := hconj (hconj1.trans (map_one _).symm)
    have hx1 : x₁ ^ j * x₂ ^ k = 1 := by
      apply d.injective
      rw [map_mul, map_zpow, map_zpow, hy1, map_one]
    obtain ⟨hj, hk⟩ := hi j k hx1
    exact ⟨hpi, hj, hk⟩

end Abstract

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
