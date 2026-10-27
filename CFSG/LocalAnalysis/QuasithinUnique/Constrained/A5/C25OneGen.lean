module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ACore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.CharTwoLocal

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Fixed

variable {X : Type*} [Group X]

theorem exists_fixed_elt' {p : ℕ} (hp : p.Prime) {N : Subgroup X} [Finite N]
    (hpN : p ∣ Nat.card N) {z : X} (hz : orderOf z = p)
    (hzN : z ∈ Subgroup.normalizer (N : Set X)) :
    ∃ u ∈ N, orderOf u = p ∧ z * u = u * z :=
  Vol2Native.L122A.exists_fixed_elt hp hpN hz hzN

theorem exists_fixed_pair_aux {K : Subgroup X} [Finite K] {a b : X} (hab : a * b = b * a)
    (haN : a ∈ Subgroup.normalizer (K : Set X)) :
    a ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({b} : Set X) : Subgroup X) : Set X) := by
  have hCfin : Finite ↥(K ⊓ Subgroup.centralizer ({b} : Set X)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left : (K ⊓ Subgroup.centralizer ({b} : Set X)) ≤ K))
      (Subgroup.inclusion_injective _)
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  obtain ⟨hxK, hxb⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.1 haN x).1 hxK, ?_⟩
  have hxb' : x ∈ Subgroup.centralizer ({b} : Set X) := hxb
  show a * x * a⁻¹ ∈ Subgroup.centralizer ({b} : Set X)
  rw [Subgroup.mem_centralizer_singleton_iff] at hxb' ⊢
  calc a * x * a⁻¹ * b = a * x * (a⁻¹ * b) := by group
    _ = a * x * (b * a⁻¹) := by
        have : a⁻¹ * b = b * a⁻¹ := by
          calc a⁻¹ * b = a⁻¹ * b * a * a⁻¹ := by group
            _ = a⁻¹ * (b * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * b) * a⁻¹ := by rw [hab]
            _ = b * a⁻¹ := by group
        rw [this]
    _ = a * (x * b) * a⁻¹ := by group
    _ = a * (b * x) * a⁻¹ := by rw [hxb']
    _ = (a * b) * x * a⁻¹ := by group
    _ = (b * a) * x * a⁻¹ := by rw [hab]
    _ = b * (a * x * a⁻¹) := by group

theorem exists_fixed_pair {K : Subgroup X} [Finite K] (hK : 3 ∣ Nat.card K) {a b : X}
    (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : a * b = b * a)
    (haN : a ∈ Subgroup.normalizer (K : Set X)) (hbN : b ∈ Subgroup.normalizer (K : Set X)) :
    ∃ c ∈ K, orderOf c = 3 ∧ c * a = a * c ∧ c * b = b * c := by
  obtain ⟨c₀, hc₀K, hc₀, hc₀b⟩ := exists_fixed_elt' Nat.prime_three hK hb hbN
  have hCfin : Finite ↥(K ⊓ Subgroup.centralizer ({b} : Set X)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left : (K ⊓ Subgroup.centralizer ({b} : Set X)) ≤ K))
      (Subgroup.inclusion_injective _)
  have hc₀C : c₀ ∈ K ⊓ Subgroup.centralizer ({b} : Set X) :=
    ⟨hc₀K, Subgroup.mem_centralizer_singleton_iff.2 hc₀b.symm⟩
  have h3C : 3 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({b} : Set X)) := by
    have h1 : orderOf (⟨c₀, hc₀C⟩ : ↥(K ⊓ Subgroup.centralizer ({b} : Set X))) = 3 := by
      rw [← Subgroup.orderOf_coe]; exact hc₀
    rw [← h1]
    exact orderOf_dvd_natCard _
  obtain ⟨c, hcC, hc, hca⟩ :=
    exists_fixed_elt' Nat.prime_three h3C ha (exists_fixed_pair_aux hab haN)
  exact ⟨c, hcC.1, hc, hca.symm, (Subgroup.mem_centralizer_singleton_iff.1 hcC.2)⟩

end Fixed

section Powers

variable {X : Type*} [Group X]

theorem pow_eq_one_of_dvd {a : X} (ha3 : orderOf a = 3) {i : ℕ} (hi : 3 ∣ i) : a ^ i = 1 :=
  orderOf_dvd_iff_pow_eq_one.1 (ha3 ▸ hi)

theorem orderOf_pow_of_not_dvd {a : X} (ha3 : orderOf a = 3) {i : ℕ} (hi : ¬ 3 ∣ i) :
    orderOf (a ^ i) = 3 := by
  have hcop : (orderOf a).Coprime i := by
    rw [ha3]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hi
  rw [hcop.orderOf_pow, ha3]

theorem pow_mem_of_pow_ne {b c : X} (hb3 : orderOf b = 3) {j : ℕ} (hj : ¬ 3 ∣ j) (hc : c = b ^ j) :
    b ∈ Subgroup.zpowers c := by
  have hcop : Nat.Coprime j (orderOf b) := by
    rw [hb3]; exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hj).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, hc]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m

variable [Finite X]

theorem zpowers_eq_of_mem {c d : X} (hc : orderOf c = 3) (hd : orderOf d = 3)
    (h : d ∈ Subgroup.zpowers c) : Subgroup.zpowers c = Subgroup.zpowers d := by
  have hle : Subgroup.zpowers d ≤ Subgroup.zpowers c := (Subgroup.zpowers_le).2 h
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hc, hd])).symm

end Powers

section Comp

variable {X : Type*} [Group X] [Finite X] {Cs : Set (Subgroup X)}

theorem le_normalizer_of_mem {K : Subgroup X} (hK : K ∈ Cs)
    (hcomm : ∀ K ∈ Cs, ∀ K' ∈ Cs, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) :
    sSup Cs ≤ Subgroup.normalizer (K : Set X) := by
  refine sSup_le fun K' hK' => ?_
  by_cases hKK : K' = K
  · subst hKK; exact Subgroup.le_normalizer
  · intro k' hk'
    apply Subgroup.mem_normalizer_fintype
    intro h hh
    have hc : h * k' = k' * h := hcomm K hK K' hK' (Ne.symm hKK) h hh k' hk'
    have : k' * h * k'⁻¹ = h := by rw [← hc]; group
    rw [this]; exact hh

omit [Finite X] in
theorem le_centralizer_sSup_diff {K : Subgroup X} (hK : K ∈ Cs)
    (hcomm : ∀ K ∈ Cs, ∀ K' ∈ Cs, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) :
    sSup (Cs \ {K}) ≤ Subgroup.centralizer (K : Set X) := by
  refine sSup_le fun K' hK' => ?_
  intro k' hk'
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact hcomm K hK K' hK'.1 (fun h => hK'.2 h.symm) h hh k' hk'

omit [Finite X] in
theorem sSup_eq_sup_diff {K : Subgroup X} (hK : K ∈ Cs) : sSup Cs = K ⊔ sSup (Cs \ {K}) := by
  have hCs : Cs = insert K (Cs \ {K}) := by
    ext s
    by_cases hs : s = K
    · subst hs; simp [hK]
    · simp [hs]
  calc sSup Cs = sSup (insert K (Cs \ {K})) := congrArg sSup hCs
    _ = K ⊔ sSup (Cs \ {K}) := sSup_insert

omit [Finite X] in
theorem exists_mul_of_mem_sSup {K : Subgroup X} (hK : K ∈ Cs)
    (hcomm : ∀ K ∈ Cs, ∀ K' ∈ Cs, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) {y : X}
    (hy : y ∈ sSup Cs) : ∃ k ∈ K, ∃ β ∈ sSup (Cs \ {K}), y = k * β := by
  have hB : sSup (Cs \ {K}) ≤ Subgroup.normalizer (K : Set X) :=
    (le_centralizer_sSup_diff hK hcomm).trans (Subgroup.centralizer_le_normalizer _)
  rw [sSup_eq_sup_diff hK, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left K _ hB] at hy
  obtain ⟨k, hk, β, hβ, rfl⟩ := hy
  exact ⟨k, hk, β, hβ, rfl⟩

omit [Finite X] in
theorem comm_mem_centralizer {K : Subgroup X} {l a : X} (hl : l⁻¹ ∈ Subgroup.normalizer (K : Set X))
    (ha : ∀ k ∈ K, a * k = k * a) : l * a * l⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : l⁻¹ * k * l ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 hl k).1 hk
    simpa using this
  have h1 : a * (l⁻¹ * k * l) = (l⁻¹ * k * l) * a := ha _ hk'
  have h2 : k * (l * a * l⁻¹) = (l * a * l⁻¹) * k := by
    calc k * (l * a * l⁻¹) = l * (l⁻¹ * k * l) * a * l⁻¹ := by group
      _ = l * (a * (l⁻¹ * k * l)) * l⁻¹ := by rw [h1]; group
      _ = (l * a * l⁻¹) * k := by group
  have h3 : k * a⁻¹ = a⁻¹ * k := by
    have := ha k hk
    calc k * a⁻¹ = a⁻¹ * (a * k) * a⁻¹ := by group
      _ = a⁻¹ * (k * a) * a⁻¹ := by rw [this]
      _ = a⁻¹ * k := by group
  calc k * (l * a * l⁻¹ * a⁻¹) = (k * (l * a * l⁻¹)) * a⁻¹ := by group
    _ = ((l * a * l⁻¹) * k) * a⁻¹ := by rw [h2]
    _ = (l * a * l⁻¹) * (k * a⁻¹) := by group
    _ = (l * a * l⁻¹) * (a⁻¹ * k) := by rw [h3]
    _ = l * a * l⁻¹ * a⁻¹ * k := by group

omit [Finite X] in
theorem false_of_all_cen {Lb : Subgroup X} (hLJ : Lb ≤ sSup Cs) (hLperf : ⁅Lb, Lb⁆ = Lb)
    (hall : ∀ K ∈ Cs, ∀ l ∈ Lb, ∀ k ∈ K, l * k = k * l) {a : X} (ha : a ∈ Lb) (ha1 : a ≠ 1) :
    False := by
  have hJ : sSup Cs ≤ Subgroup.centralizer (Lb : Set X) := by
    refine sSup_le fun K hK k hk => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hall K hK l hl k hk
  have : ⁅Lb, Lb⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hLJ.trans hJ)
  rw [hLperf] at this
  rw [this] at ha
  exact ha1 ((Subgroup.mem_bot).1 ha)

omit [Finite X] in
theorem cen_of_cen_a {Lb : Subgroup X} {a : X} (ha1 : a ≠ 1)
    (hB : ∀ x ∈ Subgroup.zpowers a, x ≠ 1 → ∀ N : Subgroup X,
      (∀ l ∈ Lb, l * x * l⁻¹ * x⁻¹ ∈ N) → Lb ≤ N)
    {K : Subgroup X} (hLn : Lb ≤ Subgroup.normalizer (K : Set X))
    (haK : ∀ k ∈ K, a * k = k * a) : ∀ l ∈ Lb, ∀ k ∈ K, l * k = k * l := by
  have := hB a (Subgroup.mem_zpowers a) ha1 (Subgroup.centralizer (K : Set X)) fun l hl =>
    comm_mem_centralizer (hLn (Lb.inv_mem hl)) haK
  intro l hl k hk
  exact (Subgroup.mem_centralizer_iff.1 (this hl) k hk).symm

omit [Finite X] in
theorem three_dvd_card {a : X} {K : Subgroup X} (hK : K ∈ Cs)
    (hcomm : ∀ K ∈ Cs, ∀ K' ∈ Cs, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    (haJ : a ∈ sSup Cs) (ha3 : orderOf a = 3) (hna : ¬ ∀ k ∈ K, a * k = k * a) :
    3 ∣ Nat.card K := by
  obtain ⟨κ, hκ, β, hβ, haeq⟩ := exists_mul_of_mem_sSup hK hcomm haJ
  have hβc : β ∈ Subgroup.centralizer (K : Set X) := le_centralizer_sSup_diff hK hcomm hβ
  have hβk : ∀ k ∈ K, β * k = k * β := fun k hk => (Subgroup.mem_centralizer_iff.1 hβc k hk).symm
  have hκnc : ¬ ∀ k ∈ K, κ * k = k * κ := by
    intro h
    apply hna
    intro k hk
    rw [haeq]
    calc κ * β * k = κ * (β * k) := by group
      _ = κ * (k * β) := by rw [hβk k hk]
      _ = (κ * k) * β := by group
      _ = (k * κ) * β := by rw [h k hk]
      _ = k * (κ * β) := by group
  have hκβ : Commute κ β := (hβk κ hκ).symm
  have hcube : κ ^ 3 * β ^ 3 = 1 := by
    have h1 : (κ * β) ^ 3 = 1 := by rw [← haeq, ← ha3]; exact pow_orderOf_eq_one a
    rwa [hκβ.mul_pow] at h1
  have hκ3 : κ ^ 3 ∈ Subgroup.centralizer (K : Set X) := by
    have : κ ^ 3 = (β ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hcube
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hβc 3)
  have h3 : 3 ∣ orderOf κ := by
    by_contra h
    have hcop : Nat.Coprime 3 (orderOf κ) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    apply hκnc
    have : κ ∈ Subgroup.centralizer (K : Set X) := by
      rw [← hm]
      exact Subgroup.pow_mem _ hκ3 m
    intro k hk
    exact (Subgroup.mem_centralizer_iff.1 this k hk).symm
  have hord : orderOf (⟨κ, hκ⟩ : K) = orderOf κ := Subgroup.orderOf_coe (⟨κ, hκ⟩ : K) ▸ rfl
  exact h3.trans (hord ▸ orderOf_dvd_natCard _)

theorem uniq_of_not_cen
    (hcomm : ∀ K ∈ Cs, ∀ K' ∈ Cs, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    {Lb : Subgroup X} (hLJ : Lb ≤ sSup Cs)
    {a b : X} (ha : a ∈ Lb) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hab : a * b = b * a)
    (hbL : ∀ l ∈ Lb, l * b = b * l)
    (hanorm : ∀ K ∈ Cs, a ∈ Subgroup.normalizer (K : Set X))
    (hbnorm : ∀ K ∈ Cs, b ∈ Subgroup.normalizer (K : Set X))
    (hB : ∀ x ∈ Subgroup.zpowers a, x ≠ 1 → ∀ N : Subgroup X,
      (∀ l ∈ Lb, l * x * l⁻¹ * x⁻¹ ∈ N) → Lb ≤ N)
    (hdeg : ∀ K₁ ∈ Cs, ∀ K₂ ∈ Cs, K₁ ≠ K₂ → b ∈ K₁ → b ∈ K₂ → False)
    (hrank : ∀ c : X, orderOf c = 3 → c * a = a * c → c * b = b * c →
      ∃ i j : ℕ, c = a ^ i * b ^ j)
    (hLn : ∀ K ∈ Cs, Lb ≤ Subgroup.normalizer (K : Set X)) (ha1 : a ≠ 1)
    {K₁ K₂ : Subgroup X} (hK₁ : K₁ ∈ Cs) (hK₂ : K₂ ∈ Cs)
    (hc₁ : ¬ ∀ l ∈ Lb, ∀ k ∈ K₁, l * k = k * l) (hc₂ : ¬ ∀ l ∈ Lb, ∀ k ∈ K₂, l * k = k * l) :
    K₁ = K₂ := by
  by_contra hne
  have hna₁ : ¬ ∀ k ∈ K₁, a * k = k * a := fun h => hc₁ (cen_of_cen_a ha1 hB (hLn K₁ hK₁) h)
  have hna₂ : ¬ ∀ k ∈ K₂, a * k = k * a := fun h => hc₂ (cen_of_cen_a ha1 hB (hLn K₂ hK₂) h)
  have haJ : a ∈ sSup Cs := hLJ ha
  have h3₁ := three_dvd_card hK₁ hcomm haJ ha3 hna₁
  have h3₂ := three_dvd_card hK₂ hcomm haJ ha3 hna₂
  obtain ⟨c₁, hc₁K, hc₁3, hc₁a, hc₁b⟩ :=
    exists_fixed_pair h3₁ ha3 hb3 hab (hanorm K₁ hK₁) (hbnorm K₁ hK₁)
  obtain ⟨c₂, hc₂K, hc₂3, hc₂a, hc₂b⟩ :=
    exists_fixed_pair h3₂ ha3 hb3 hab (hanorm K₂ hK₂) (hbnorm K₂ hK₂)
  obtain ⟨i₁, j₁, hc₁eq⟩ := hrank c₁ hc₁3 hc₁a hc₁b
  obtain ⟨i₂, j₂, hc₂eq⟩ := hrank c₂ hc₂3 hc₂a hc₂b
  have hbj : ∀ l ∈ Lb, ∀ j : ℕ, l * b ^ j = b ^ j * l := fun l hl j =>
    (Commute.pow_right (hbL l hl) j)
  have claimA : ∀ {K : Subgroup X}, K ∈ Cs → ∀ {c : X}, c ∈ K → ∀ {i j : ℕ}, c = a ^ i * b ^ j →
      ¬ 3 ∣ i → Lb ≤ K := by
    intro K hK c hcK i j hcij hi
    have hai : orderOf (a ^ i) = 3 := orderOf_pow_of_not_dvd ha3 hi
    have hai1 : a ^ i ≠ 1 := fun h => by rw [h, orderOf_one] at hai; omega
    refine hB (a ^ i) (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i) hai1 K fun l hl => ?_
    have e : l * a ^ i * l⁻¹ * (a ^ i)⁻¹ = l * c * l⁻¹ * c⁻¹ := by
      have h1 : b ^ j * l⁻¹ = l⁻¹ * b ^ j := (hbj l⁻¹ (Lb.inv_mem hl) j).symm
      rw [hcij]
      calc l * a ^ i * l⁻¹ * (a ^ i)⁻¹ = l * a ^ i * (l⁻¹ * b ^ j) * (b ^ j)⁻¹ * (a ^ i)⁻¹ := by group
        _ = l * a ^ i * (b ^ j * l⁻¹) * (b ^ j)⁻¹ * (a ^ i)⁻¹ := by rw [h1]
        _ = l * (a ^ i * b ^ j) * l⁻¹ * (a ^ i * b ^ j)⁻¹ := by group
    rw [e]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hLn K hK hl) c).1 hcK) (K.inv_mem hcK)
  by_cases hcc : c₂ ∈ Subgroup.zpowers c₁
  · have heq := zpowers_eq_of_mem hc₁3 hc₂3 hcc
    have hc₁K₂ : c₁ ∈ K₂ := by
      have : c₁ ∈ Subgroup.zpowers c₂ := heq ▸ Subgroup.mem_zpowers c₁
      exact (Subgroup.zpowers_le.2 hc₂K) this
    have hcent : ∀ y ∈ sSup Cs, c₁ * y = y * c₁ := by
      have : sSup Cs ≤ Subgroup.centralizer ({c₁} : Set X) := by
        refine sSup_le fun K hK k hk => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        by_cases hKK : K = K₁
        · subst hKK
          exact hcomm K hK K₂ hK₂ hne k hk c₁ hc₁K₂
        · exact (hcomm K₁ hK₁ K hK (Ne.symm hKK) c₁ hc₁K k hk).symm
      intro y hy
      exact (Subgroup.mem_centralizer_singleton_iff.1 (this hy)).symm
    have hLcomm : ∀ l ∈ Lb, l * c₁ = c₁ * l := fun l hl => (hcent l (hLJ hl)).symm
    have hai : ∀ l ∈ Lb, l * a ^ i₁ = a ^ i₁ * l := by
      intro l hl
      have h1 : l * (a ^ i₁ * b ^ j₁) = (a ^ i₁ * b ^ j₁) * l := hc₁eq ▸ hLcomm l hl
      have : (l * a ^ i₁) * b ^ j₁ = (a ^ i₁ * l) * b ^ j₁ := by
        calc (l * a ^ i₁) * b ^ j₁ = l * (a ^ i₁ * b ^ j₁) := by group
          _ = (a ^ i₁ * b ^ j₁) * l := h1
          _ = a ^ i₁ * (b ^ j₁ * l) := by group
          _ = a ^ i₁ * (l * b ^ j₁) := by rw [hbj l hl j₁]
          _ = (a ^ i₁ * l) * b ^ j₁ := by group
      exact mul_right_cancel this
    have hai1 : a ^ i₁ = 1 := by
      by_contra h1
      have := hB (a ^ i₁) (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i₁) h1 ⊥ (fun l hl => by
        rw [Subgroup.mem_bot]
        calc l * a ^ i₁ * l⁻¹ * (a ^ i₁)⁻¹ = (a ^ i₁ * l) * l⁻¹ * (a ^ i₁)⁻¹ := by rw [hai l hl]
          _ = 1 := by group)
      exact ha1 (Subgroup.mem_bot.1 (this ha))
    have hc₁b' : c₁ = b ^ j₁ := by rw [hc₁eq, hai1, one_mul]
    have hj₁ : ¬ 3 ∣ j₁ := by
      intro h3
      have : c₁ = 1 := by rw [hc₁b', pow_eq_one_of_dvd hb3 h3]
      rw [this, orderOf_one] at hc₁3
      omega
    have hbc₁ : b ∈ Subgroup.zpowers c₁ := pow_mem_of_pow_ne hb3 hj₁ hc₁b'
    have hbK₁ : b ∈ K₁ := (Subgroup.zpowers_le.2 hc₁K) hbc₁
    have hbK₂ : b ∈ K₂ := by
      have : b ∈ Subgroup.zpowers c₂ := heq ▸ hbc₁
      exact (Subgroup.zpowers_le.2 hc₂K) this
    exact hdeg K₁ hK₁ K₂ hK₂ hne hbK₁ hbK₂
  · by_cases hi₁ : 3 ∣ i₁
    · have hc₁b' : c₁ = b ^ j₁ := by rw [hc₁eq, pow_eq_one_of_dvd ha3 hi₁, one_mul]
      have hj₁ : ¬ 3 ∣ j₁ := by
        intro h3
        have : c₁ = 1 := by rw [hc₁b', pow_eq_one_of_dvd hb3 h3]
        rw [this, orderOf_one] at hc₁3
        omega
      have hbc₁ : b ∈ Subgroup.zpowers c₁ := pow_mem_of_pow_ne hb3 hj₁ hc₁b'
      by_cases hi₂ : 3 ∣ i₂
      · have hc₂b' : c₂ = b ^ j₂ := by rw [hc₂eq, pow_eq_one_of_dvd ha3 hi₂, one_mul]
        exact hcc (by rw [hc₂b']; exact Subgroup.pow_mem _ hbc₁ j₂)
      · have hLK₂ := claimA hK₂ hc₂K hc₂eq hi₂
        apply hc₁
        intro l hl k hk
        exact (hcomm K₁ hK₁ K₂ hK₂ hne k hk l (hLK₂ hl)).symm
    · have hLK₁ := claimA hK₁ hc₁K hc₁eq hi₁
      apply hc₂
      intro l hl k hk
      exact hcomm K₁ hK₁ K₂ hK₂ hne l (hLK₁ hl) k hk

theorem exists_mem_of_commuting
    (hcomm : ∀ K ∈ Cs, ∀ K' ∈ Cs, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    {Lb : Subgroup X} (hLJ : Lb ≤ sSup Cs) (hLperf : ⁅Lb, Lb⁆ = Lb)
    {a b : X} (ha : a ∈ Lb) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hab : a * b = b * a)
    (hbL : ∀ l ∈ Lb, l * b = b * l)
    (hanorm : ∀ K ∈ Cs, a ∈ Subgroup.normalizer (K : Set X))
    (hbnorm : ∀ K ∈ Cs, b ∈ Subgroup.normalizer (K : Set X))
    (hB : ∀ x ∈ Subgroup.zpowers a, x ≠ 1 → ∀ N : Subgroup X,
      (∀ l ∈ Lb, l * x * l⁻¹ * x⁻¹ ∈ N) → Lb ≤ N)
    (hdeg : ∀ K₁ ∈ Cs, ∀ K₂ ∈ Cs, K₁ ≠ K₂ → b ∈ K₁ → b ∈ K₂ → False)
    (hrank : ∀ c : X, orderOf c = 3 → c * a = a * c → c * b = b * c →
      ∃ i j : ℕ, c = a ^ i * b ^ j) :
    ∃ K ∈ Cs, Lb ≤ K := by
  by_contra hno
  push Not at hno
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha3; omega
  have hLn : ∀ K ∈ Cs, Lb ≤ Subgroup.normalizer (K : Set X) :=
    fun K hK => hLJ.trans (le_normalizer_of_mem hK hcomm)
  obtain ⟨K₀, hK₀, hc₀⟩ : ∃ K ∈ Cs, ¬ ∀ l ∈ Lb, ∀ k ∈ K, l * k = k * l := by
    by_contra h
    push Not at h
    exact false_of_all_cen hLJ hLperf (fun K hK => h K hK) ha ha1
  have hcen : ∀ K ∈ Cs, K ≠ K₀ → ∀ l ∈ Lb, ∀ k ∈ K, l * k = k * l := by
    intro K hK hne
    by_contra h
    exact hne (uniq_of_not_cen hcomm hLJ ha ha3 hb3 hab hbL hanorm hbnorm hB hdeg hrank hLn ha1
      hK hK₀ h hc₀)
  apply hno K₀ hK₀
  have hB' : sSup (Cs \ {K₀}) ≤ Subgroup.centralizer (Lb : Set X) := by
    refine sSup_le fun K hK k hk => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hcen K hK.1 hK.2 l hl k hk
  have hsub : ⁅Lb, Lb⁆ ≤ K₀ := by
    rw [Subgroup.commutator_le]
    intro l hl l' hl'
    obtain ⟨κ, hκ, β, hβ, hleq⟩ := exists_mul_of_mem_sSup hK₀ hcomm (hLJ hl)
    obtain ⟨κ', hκ', β', hβ', hl'eq⟩ := exists_mul_of_mem_sSup hK₀ hcomm (hLJ hl')
    have hβl' : l' * β = β * l' := Subgroup.mem_centralizer_iff.1 (hB' hβ) l' hl'
    have hβ'κ : κ * β' = β' * κ :=
      Subgroup.mem_centralizer_iff.1 (le_centralizer_sSup_diff hK₀ hcomm hβ') κ hκ
    have e : l * l' * l⁻¹ * l'⁻¹ = κ * κ' * κ⁻¹ * κ'⁻¹ := by
      have h1 : β * l' * β⁻¹ = l' := by rw [← hβl']; group
      have h2 : β' * κ⁻¹ * β'⁻¹ = κ⁻¹ := by
        have hcinv : Commute κ⁻¹ β' := (show Commute κ β' from hβ'κ).inv_left
        rw [← hcinv.eq]; group
      calc l * l' * l⁻¹ * l'⁻¹ = κ * (β * l' * β⁻¹) * κ⁻¹ * l'⁻¹ := by rw [hleq]; group
        _ = κ * l' * κ⁻¹ * l'⁻¹ := by rw [h1]
        _ = κ * (κ' * β') * κ⁻¹ * (κ' * β')⁻¹ := by rw [← hl'eq]
        _ = κ * κ' * (β' * κ⁻¹ * β'⁻¹) * κ'⁻¹ := by group
        _ = κ * κ' * κ⁻¹ * κ'⁻¹ := by rw [h2]
    rw [commutatorElement_def, e]
    exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hκ hκ') (K₀.inv_mem hκ)) (K₀.inv_mem hκ')
  calc Lb = ⁅Lb, Lb⁆ := hLperf.symm
    _ ≤ K₀ := hsub

end Comp

section Rank

variable {X : Type*} [Group X] [Finite X]

theorem hrank_of_pRank (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {a b : X} (ha3 : orderOf a = 3)
    (hb3 : orderOf b = 3) (hab : a * b = b * a) (hbna : b ∉ Subgroup.zpowers a) :
    ∀ c : X, orderOf c = 3 → c * a = a * c → c * b = b * c → ∃ i j : ℕ, c = a ^ i * b ^ j := by
  intro c hc3 hca hcb
  by_contra hno
  have hnat : ∀ {x : X} {d : X}, orderOf d = 3 → x ∈ Subgroup.zpowers d → ∃ i : ℕ, x = d ^ i := by
    intro x d hd hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨(m % 3).toNat, ?_⟩
    have h0 : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
    have h1 : d ^ (m % (orderOf d : ℤ)) = d ^ m := zpow_mod_orderOf d m
    have h2 : (orderOf d : ℤ) = 3 := by rw [hd]; norm_num
    rw [h2] at h1
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    exact h1.symm
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_zpow (show Commute a b from hab) m n)).eq
  have hdisj : ∀ x ∈ Subgroup.zpowers a, x ∈ Subgroup.zpowers b → x = 1 := by
    intro x hxa hxb
    by_contra hx1
    have hx3 : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := by
        rw [← ha3]
        exact orderOf_dvd_of_mem_zpowers hxa
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hx1
      · exact h
    have h1 := zpowers_eq_of_mem ha3 hx3 hxa
    have h2 := zpowers_eq_of_mem hb3 hx3 hxb
    apply hbna
    have : b ∈ Subgroup.zpowers x := h2 ▸ Subgroup.mem_zpowers b
    exact h1 ▸ this
  have hzN : c ∉ Vol2Native.L122A.prodSub (Subgroup.zpowers a) (Subgroup.zpowers b) hcomm := by
    rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨i, rfl⟩ := hnat ha3 hx
    obtain ⟨j, rfl⟩ := hnat hb3 hy
    exact hno ⟨i, j, hxy⟩
  have := Vol2Native.L122A.three_le_pRank Nat.prime_three hcomm hdisj hc3 ha3 hb3
    (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b) hzN hca hcb
  omega

end Rank

end CFSG.QuasithinUnique.A5.C25
