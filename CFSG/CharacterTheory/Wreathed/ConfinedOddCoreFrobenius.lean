module

public import CFSG.GroupTheory.OddInversion
public import CFSG.Adapters.FrobeniusKernel

public section

open scoped Pointwise commutatorElement

namespace CFSG.Wreathed.ConfinedOddCore

open CFSG.OddInversion

variable {G : Type*} [Group G]

theorem commute_of_sq_commute {g a : G} (hg : Odd (orderOf g)) (h : Commute (g ^ 2) a) :
    Commute g a := by
  obtain ⟨k, hk⟩ := hg
  have hg' : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hg']
  exact h.pow_left _

theorem odd_orderOf_of_mem {R : Subgroup G} (hR : Odd (Nat.card R)) {g : G} (hg : g ∈ R) :
    Odd (orderOf g) :=
  hR.of_dvd_nat (R.orderOf_dvd_natCard hg)

theorem eq_one_of_sq_eq_one {R : Subgroup G} (hR : Odd (Nat.card R)) {g : G} (hg : g ∈ R)
    (h2 : g ^ 2 = 1) : g = 1 := by
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hodd := odd_orderOf_of_mem hR hg
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem eq_one_of_inverted_of_fixed {R : Subgroup G} (hR : Odd (Nat.card R)) {y g : G}
    (hg : g ∈ R) (hinv : y * g * y⁻¹ = g⁻¹) (hfix : y * g = g * y) : g = 1 := by
  apply eq_one_of_sq_eq_one hR hg
  have h1 : y * g * y⁻¹ = g := by rw [hfix, mul_inv_cancel_right]
  rw [h1] at hinv
  rw [sq]
  nth_rewrite 2 [hinv]
  exact mul_inv_cancel g

theorem exists_inverted_mul_fixed {R : Subgroup G} (hR : Odd (Nat.card R)) {y : G}
    (hy : orderOf y = 2) (hyR : y ∈ Subgroup.normalizer (R : Set G)) {K : Subgroup G}
    (hKR : K ≤ R) (hyK : y ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    ∃ i ∈ K, y * i * y⁻¹ = i⁻¹ ∧ ∃ c ∈ K, y * c = c * y ∧ k = i * c := by
  have h := ((odd_involution_product_decomposition hR hy hyR).2.2 K hKR hyK).1
  have hk' : k ∈ (K : Set G) := hk
  rw [h] at hk'
  obtain ⟨i, ⟨hiK, -, hiinv⟩, c, hc, hic⟩ := Set.mem_mul.mp hk'
  obtain ⟨hcK, hcy⟩ := Subgroup.mem_inf.mp hc
  exact ⟨i, hiK, hiinv, c, hcK, (Subgroup.mem_centralizer_singleton_iff.mp hcy).symm, hic.symm⟩

theorem mem_normalizer_inf_centralizer {R : Subgroup G} {y c : G}
    (hyR : y ∈ Subgroup.normalizer (R : Set G)) (hyc : y * c = c * y) :
    y ∈ Subgroup.normalizer ((R ⊓ Subgroup.centralizer {c} : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hc : c = y * c * y⁻¹ := by rw [hyc, mul_inv_cancel_right]
  have hcent : h * c = c * h ↔ y * h * y⁻¹ * c = c * (y * h * y⁻¹) := by
    constructor
    · intro hh
      calc y * h * y⁻¹ * c = y * h * y⁻¹ * (y * c * y⁻¹) := by rw [← hc]
        _ = y * (h * c) * y⁻¹ := by group
        _ = y * (c * h) * y⁻¹ := by rw [hh]
        _ = y * c * y⁻¹ * (y * h * y⁻¹) := by group
        _ = c * (y * h * y⁻¹) := by rw [← hc]
    · intro hh
      have h1 : y * (h * c) * y⁻¹ = y * (c * h) * y⁻¹ := by
        calc y * (h * c) * y⁻¹ = y * h * y⁻¹ * (y * c * y⁻¹) := by group
          _ = y * h * y⁻¹ * c := by rw [← hc]
          _ = c * (y * h * y⁻¹) := hh
          _ = y * c * y⁻¹ * (y * h * y⁻¹) := by rw [← hc]
          _ = y * (c * h) * y⁻¹ := by group
      simpa using h1
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr ((Subgroup.mem_normalizer_iff.mp hyR) h) hcent

section Inverted

variable {R : Subgroup G}

theorem centralizer_eq_fixed (hR : Odd (Nat.card R)) {y : G} (hy : orderOf y = 2)
    (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hA : ∀ a ∈ R ⊓ Subgroup.centralizer {y}, ∀ b ∈ R ⊓ Subgroup.centralizer {y}, a * b = b * a)
    (hP : ∀ c ∈ R ⊓ Subgroup.centralizer {y}, c ≠ 1 → ∀ v ∈ R, y * v * y⁻¹ = v⁻¹ →
      v * c = c * v → v = 1)
    {c : G} (hc : c ∈ R ⊓ Subgroup.centralizer {y}) (hc1 : c ≠ 1) :
    R ⊓ Subgroup.centralizer {c} = R ⊓ Subgroup.centralizer {y} := by
  have hcy : y * c = c * y := (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
  apply le_antisymm
  · intro g hg
    obtain ⟨i, hiK, hiinv, f, hfK, hfy, rfl⟩ := exists_inverted_mul_fixed hR hy hyR
      (inf_le_left : R ⊓ Subgroup.centralizer {c} ≤ R) (mem_normalizer_inf_centralizer hyR hcy) hg
    have hi1 : i = 1 := hP c hc hc1 i hiK.1 hiinv
      (Subgroup.mem_centralizer_singleton_iff.mp hiK.2)
    rw [hi1, one_mul]
    exact ⟨hfK.1, Subgroup.mem_centralizer_singleton_iff.mpr hfy.symm⟩
  · intro g hg
    exact ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.mpr (hA g hg c hc)⟩

theorem normalizer_eq_fixed (hR : Odd (Nat.card R)) {y : G} (hy : orderOf y = 2)
    (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hA : ∀ a ∈ R ⊓ Subgroup.centralizer {y}, ∀ b ∈ R ⊓ Subgroup.centralizer {y}, a * b = b * a)
    (hP : ∀ c ∈ R ⊓ Subgroup.centralizer {y}, c ≠ 1 → ∀ v ∈ R, y * v * y⁻¹ = v⁻¹ →
      v * c = c * v → v = 1)
    (hne : R ⊓ Subgroup.centralizer {y} ≠ ⊥) :
    R ⊓ Subgroup.normalizer ((R ⊓ Subgroup.centralizer {y} : Subgroup G) : Set G) =
      R ⊓ Subgroup.centralizer {y} := by
  set A₀ := R ⊓ Subgroup.centralizer {y} with hA₀
  have hyinv : y⁻¹ = y := CFSG.OddInversion.inv_eq_self_of_orderOf_eq_two hy
  have hAy : ∀ a ∈ A₀, y * a * y⁻¹ = a := fun a ha => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm, mul_inv_cancel_right]
  have hyA : y ∈ Subgroup.normalizer (A₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hAy h hh]
      exact hh
    · intro hh
      have h1 := hAy _ hh
      rw [CFSG.OddInversion.conj_conj_of_orderOf_eq_two hy h] at h1
      rw [h1]
      exact hh
  have hyN : y ∈ Subgroup.normalizer
      ((R ⊓ Subgroup.normalizer (A₀ : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_inf]
    refine and_congr ((Subgroup.mem_normalizer_iff.mp hyR) h) ?_
    constructor
    · intro hh
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyA hh) (Subgroup.inv_mem _ hyA)
    · intro hh
      have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyA) hh) hyA
      rwa [show y⁻¹ * (y * h * y⁻¹) * y = h by group] at h1
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hcent := centralizer_eq_fixed hR hy hyR hA hP c.2 (fun h => hc1 (Subtype.ext h))
  apply le_antisymm
  · intro g hg
    obtain ⟨i, hiK, hiinv, f, hfK, hfy, rfl⟩ := exists_inverted_mul_fixed hR hy hyR
      (inf_le_left : R ⊓ Subgroup.normalizer (A₀ : Set G) ≤ R) hyN hg
    have hiA : ∀ a ∈ A₀, i * a = a * i := by
      intro a ha
      have hia : i * a * i⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.mp hiK.2 a).mp ha
      have h1 : i⁻¹ * a * i = i * a * i⁻¹ := by
        calc i⁻¹ * a * i = (y * i * y⁻¹) * a * (y * i * y⁻¹)⁻¹ := by rw [hiinv, inv_inv]
          _ = y * i * (y⁻¹ * a * y) * i⁻¹ * y⁻¹ := by group
          _ = y * i * a * i⁻¹ * y⁻¹ := by
              rw [show y⁻¹ * a * y = a by
                rw [hyinv]; nth_rewrite 2 [← hyinv]; exact hAy a ha]
          _ = y * (i * a * i⁻¹) * y⁻¹ := by group
          _ = i * a * i⁻¹ := hAy _ hia
      have h2 : Commute (i ^ 2) a := by
        rw [sq]
        change i * i * a = a * (i * i)
        calc i * i * a = i * (i * a * i⁻¹) * i := by group
          _ = i * (i⁻¹ * a * i) * i := by rw [h1]
          _ = a * (i * i) := by group
      exact commute_of_sq_commute (odd_orderOf_of_mem hR hiK.1) h2
    have hiC : i ∈ R ⊓ Subgroup.centralizer {(c : G)} :=
      ⟨hiK.1, Subgroup.mem_centralizer_singleton_iff.mpr (hiA c c.2)⟩
    rw [hcent] at hiC
    have hi1 : i = 1 := eq_one_of_inverted_of_fixed hR hiK.1 hiinv
      (Subgroup.mem_centralizer_singleton_iff.mp hiC.2).symm
    rw [hi1, one_mul]
    exact ⟨hfK.1, Subgroup.mem_centralizer_singleton_iff.mpr hfy.symm⟩
  · intro g hg
    exact ⟨hg.1, Subgroup.le_normalizer hg⟩

theorem eq_one_of_mem_conj_fixed (hR : Odd (Nat.card R)) {y : G} (hy : orderOf y = 2)
    (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hA : ∀ a ∈ R ⊓ Subgroup.centralizer {y}, ∀ b ∈ R ⊓ Subgroup.centralizer {y}, a * b = b * a)
    (hP : ∀ c ∈ R ⊓ Subgroup.centralizer {y}, c ≠ 1 → ∀ v ∈ R, y * v * y⁻¹ = v⁻¹ →
      v * c = c * v → v = 1)
    (hne : R ⊓ Subgroup.centralizer {y} ≠ ⊥) {r : G} (hr : r ∈ R)
    (hrA : r ∉ R ⊓ Subgroup.centralizer {y}) {c : G} (hcA : c ∈ R ⊓ Subgroup.centralizer {y})
    (hcr : r⁻¹ * c * r ∈ R ⊓ Subgroup.centralizer {y}) : c = 1 := by
  by_contra hc1
  have hc'1 : r⁻¹ * c * r ≠ 1 := by
    intro h
    apply hc1
    calc c = r * (r⁻¹ * c * r) * r⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hcent := centralizer_eq_fixed hR hy hyR hA hP hcA hc1
  have hcent' := centralizer_eq_fixed hR hy hyR hA hP hcr hc'1
  apply hrA
  rw [← normalizer_eq_fixed hR hy hyR hA hP hne]
  refine ⟨hr, Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  ·
    have h1 := hA a ha _ hcr
    have h2 : r * a * r⁻¹ ∈ R ⊓ Subgroup.centralizer {c} := by
      refine ⟨R.mul_mem (R.mul_mem hr ha.1) (R.inv_mem hr),
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc r * a * r⁻¹ * c = r * (a * (r⁻¹ * c * r)) * r⁻¹ := by group
        _ = r * ((r⁻¹ * c * r) * a) * r⁻¹ := by rw [h1]
        _ = c * (r * a * r⁻¹) := by group
    rwa [hcent] at h2
  · have h1 := hA _ ha c hcA
    have h2 : a ∈ R ⊓ Subgroup.centralizer {r⁻¹ * c * r} := by
      have haR : a ∈ R := by
        have h3 := R.mul_mem (R.mul_mem (R.inv_mem hr) ha.1) hr
        rwa [show r⁻¹ * (r * a * r⁻¹) * r = a by group] at h3
      refine ⟨haR, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc a * (r⁻¹ * c * r) = r⁻¹ * ((r * a * r⁻¹) * c) * r := by group
        _ = r⁻¹ * (c * (r * a * r⁻¹)) * r := by rw [h1]
        _ = r⁻¹ * c * r * a := by group
    rwa [hcent'] at h2

theorem exists_inverted_subgroup_of_frobenius {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : Odd (Nat.card R)) {y : G} (hy : orderOf y = 2)
    (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hA : ∀ a ∈ R ⊓ Subgroup.centralizer {y}, ∀ b ∈ R ⊓ Subgroup.centralizer {y}, a * b = b * a)
    (hP : ∀ c ∈ R ⊓ Subgroup.centralizer {y}, c ≠ 1 → ∀ v ∈ R, y * v * y⁻¹ = v⁻¹ →
      v * c = c * v → v = 1)
    (h1 : R ⊓ Subgroup.centralizer {y} ≠ ⊥) (h2 : R ⊓ Subgroup.centralizer {y} ≠ R) :
    ∃ B : Subgroup G, (∀ g, g ∈ B ↔ g ∈ R ∧ y * g * y⁻¹ = g⁻¹) ∧
      ∀ r ∈ R, ∃ b ∈ B, ∃ a ∈ R ⊓ Subgroup.centralizer {y}, r = b * a := by
  set A₀ := R ⊓ Subgroup.centralizer {y} with hA₀def
  have hA₀R : A₀ ≤ R := inf_le_left
  have hyinv : y⁻¹ = y := CFSG.OddInversion.inv_eq_self_of_orderOf_eq_two hy
  have hAy : ∀ a ∈ A₀, y * a * y⁻¹ = a := fun a ha => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm, mul_inv_cancel_right]
  have hyR' : ∀ g : G, g ∈ R → y * g * y⁻¹ ∈ R :=
    fun g hg => (Subgroup.mem_normalizer_iff.mp hyR g).mp hg
  let H : Subgroup R := A₀.subgroupOf R
  have hH1 : H ≠ ⊥ := by
    intro h
    apply h1
    rw [eq_bot_iff]
    intro g hg
    have hgH : (⟨g, hA₀R hg⟩ : R) ∈ H := hg
    rw [h, Subgroup.mem_bot] at hgH
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hgH)
  have hHG : H ≠ ⊤ := by
    intro h
    apply h2
    apply le_antisymm hA₀R
    intro g hg
    have hgH : (⟨g, hg⟩ : R) ∈ H := h ▸ Subgroup.mem_top _
    exact hgH
  have hconj : ∀ a g : R, g ∈ MulAut.conj a • H ↔ a⁻¹ * g * a ∈ H := by
    intro a g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv]
  have hfrob : ∀ g : R, g ∉ H → H ⊓ (MulAut.conj g • H) = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    obtain ⟨hcH, hcg⟩ := Subgroup.mem_inf.mp hc
    rw [hconj] at hcg
    apply Subtype.ext
    exact eq_one_of_mem_conj_fixed hR hy hyR hA hP h1 g.2 hg hcH hcg
  obtain ⟨K, hKset, hKnormal, hKH, hKinf, -⟩ := CFSG.Adapters.frobenius_kernel H hH1 hHG hfrob
  have hKmem : ∀ k : R, k ∈ K ↔ k = 1 ∨ ∀ g : R, k ∉ MulAut.conj g • H := by
    intro k
    rw [← SetLike.mem_coe, hKset, Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff,
      Set.mem_iUnion]
    simp only [Set.mem_univ, true_and, not_exists, SetLike.mem_coe]
  have hyR'' : ∀ g : G, g ∈ R → y⁻¹ * g * y ∈ R := fun g hg => by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyR) g).mp hg
  have hKy : ∀ k : R, k ∈ K → (⟨y * k * y⁻¹, hyR' k k.2⟩ : R) ∈ K := by
    intro k hk
    rcases (hKmem k).mp hk with hk1 | hk1
    · rw [hKmem]
      left
      apply Subtype.ext
      simp [hk1]
    · rw [hKmem]
      right
      intro g hg
      apply hk1 ⟨y⁻¹ * g * y, hyR'' g g.2⟩
      rw [hconj] at hg ⊢
      have hg' : (g : G)⁻¹ * (y * k * y⁻¹) * g ∈ A₀ := hg
      have h3 := hAy _ hg'
      show (y⁻¹ * (g : G) * y)⁻¹ * k * (y⁻¹ * g * y) ∈ A₀
      have h4 : (y⁻¹ * (g : G) * y)⁻¹ * k * (y⁻¹ * g * y) =
          (g : G)⁻¹ * (y * k * y⁻¹) * g := by
        calc (y⁻¹ * (g : G) * y)⁻¹ * k * (y⁻¹ * g * y) =
            y⁻¹ * ((g : G)⁻¹ * (y * k * y⁻¹) * g) * y := by group
          _ = y⁻¹ * (y * ((g : G)⁻¹ * (y * k * y⁻¹) * g) * y⁻¹) * y := by rw [h3]
          _ = (g : G)⁻¹ * (y * k * y⁻¹) * g := by group
      rw [h4]
      exact hg'
  set B : Subgroup G := K.map R.subtype with hBdef
  have hBR : B ≤ R := Subgroup.map_subtype_le K
  have hyB : y ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, hKy k hk, rfl⟩
    · intro hh
      obtain ⟨k, hk, hkh⟩ := hh
      refine ⟨_, hKy k hk, ?_⟩
      change y * (k : G) * y⁻¹ = h
      have hkh' : (k : G) = y * h * y⁻¹ := hkh
      rw [hkh', hyinv, show y * (y * h * y) * y = y * y * h * (y * y) by group]
      have hyy : y * y = 1 := by
        calc y * y = y⁻¹ * y := by rw [hyinv]
          _ = 1 := inv_mul_cancel y
      rw [hyy, one_mul, mul_one]
  have hBA : ∀ g ∈ B, g ∈ A₀ → g = 1 := by
    rintro _ ⟨k, hk, rfl⟩ hkA
    have hkH : k ∈ H := hkA
    have hkK : k ∈ K ⊓ H := ⟨hk, hkH⟩
    rw [hKinf, Subgroup.mem_bot] at hkK
    rw [hkK]
    rfl
  have hBinv : ∀ g ∈ B, y * g * y⁻¹ = g⁻¹ := by
    intro g hg
    obtain ⟨i, hiB, hiinv, f, hfB, hfy, rfl⟩ := exists_inverted_mul_fixed hR hy hyR hBR hyB hg
    have hf1 : f = 1 := hBA f hfB ⟨hBR hfB, Subgroup.mem_centralizer_singleton_iff.mpr hfy.symm⟩
    rw [hf1, mul_one]
    exact hiinv
  refine ⟨B, fun g => ⟨fun hg => ⟨hBR hg, hBinv g hg⟩, fun hg => ?_⟩, fun r hr => ?_⟩
  ·
    obtain ⟨k, hk, h, hh, hkh⟩ := hKH ⟨g, hg.1⟩
    have hkB : (k : G) ∈ B := ⟨k, hk, rfl⟩
    have hhA : (h : G) ∈ A₀ := hh
    have hgkh : g = k * h := congrArg Subtype.val hkh
    have hky : y * (k : G) * y⁻¹ = (k : G)⁻¹ := hBinv k hkB
    have hhy : y * (h : G) * y⁻¹ = h := hAy h hhA
    have hsq : (h : G) ^ 2 = ((h : G) * k * (h : G)⁻¹) * (k : G)⁻¹ := by
      have hrel : (k : G)⁻¹ * h = (h : G)⁻¹ * (k : G)⁻¹ := by
        have h5 : y * g * y⁻¹ = (k : G)⁻¹ * h := by
          rw [hgkh, show y * ((k : G) * h) * y⁻¹ = (y * k * y⁻¹) * (y * h * y⁻¹) by group,
            hky, hhy]
        rw [← h5, hg.2, hgkh, mul_inv_rev]
      calc (h : G) ^ 2 = (h : G) * k * ((k : G)⁻¹ * h) := by rw [sq]; group
        _ = (h : G) * k * ((h : G)⁻¹ * (k : G)⁻¹) := by rw [hrel]
        _ = ((h : G) * k * (h : G)⁻¹) * (k : G)⁻¹ := by group
    have hsqK : h ^ 2 ∈ K := by
      have h6 : h * k * h⁻¹ * k⁻¹ ∈ K := K.mul_mem (hKnormal.conj_mem k hk h) (K.inv_mem hk)
      have h7 : h ^ 2 = h * k * h⁻¹ * k⁻¹ := Subtype.ext (by
        simp only [SubgroupClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hsq)
      rw [h7]
      exact h6
    have hsq1 : h ^ 2 = 1 := by
      have h8 : h ^ 2 ∈ K ⊓ H := ⟨hsqK, H.pow_mem hh 2⟩
      rw [hKinf, Subgroup.mem_bot] at h8
      exact h8
    have hh1 : (h : G) = 1 := eq_one_of_sq_eq_one hR h.2
      (by rw [← SubgroupClass.coe_pow, hsq1]; rfl)
    rw [hgkh, hh1, mul_one]
    exact hkB
  · obtain ⟨k, hk, h, hh, hkh⟩ := hKH ⟨r, hr⟩
    exact ⟨k, ⟨k, hk, rfl⟩, h, hh, congrArg Subtype.val hkh⟩

theorem eq_one_or_eq_of_mem_zpowers {y g : G} (hy : orderOf y = 2) (hg : g ∈ Subgroup.zpowers y) :
    g = 1 ∨ g = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, hy]
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem exists_inverted_subgroup {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : Odd (Nat.card R)) {y : G} (hy : orderOf y = 2)
    (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hA : ∀ a ∈ R ⊓ Subgroup.centralizer {y}, ∀ b ∈ R ⊓ Subgroup.centralizer {y}, a * b = b * a)
    (hP : ∀ c ∈ R ⊓ Subgroup.centralizer {y}, c ≠ 1 → ∀ v ∈ R, y * v * y⁻¹ = v⁻¹ →
      v * c = c * v → v = 1) :
    ∃ B : Subgroup G, (∀ g, g ∈ B ↔ g ∈ R ∧ y * g * y⁻¹ = g⁻¹) ∧
      ∀ r ∈ R, ∃ b ∈ B, ∃ a ∈ R ⊓ Subgroup.centralizer {y}, r = b * a := by
  by_cases h1 : R ⊓ Subgroup.centralizer {y} = ⊥
  · refine ⟨R, fun g => ⟨fun hg => ⟨hg, ?_⟩, fun hg => hg.1⟩,
      fun r hr => ⟨r, hr, 1, Subgroup.one_mem _, (mul_one r).symm⟩⟩
    obtain ⟨i, -, hiinv, f, hfK, hfy, rfl⟩ := exists_inverted_mul_fixed hR hy hyR le_rfl hyR hg
    have hfA : f ∈ R ⊓ Subgroup.centralizer {y} :=
      ⟨hfK, Subgroup.mem_centralizer_singleton_iff.mpr hfy.symm⟩
    rw [h1, Subgroup.mem_bot] at hfA
    rw [hfA, mul_one]
    exact hiinv
  by_cases h2 : R ⊓ Subgroup.centralizer {y} = R
  · refine ⟨⊥, fun g => ⟨fun hg => ?_, fun hg => ?_⟩,
      fun r hr => ⟨1, Subgroup.one_mem _, r, by rw [h2]; exact hr, (one_mul r).symm⟩⟩
    · rw [Subgroup.mem_bot] at hg
      subst hg
      exact ⟨R.one_mem, by simp⟩
    · have hgA : g ∈ R ⊓ Subgroup.centralizer {y} := by rw [h2]; exact hg.1
      rw [Subgroup.mem_bot]
      exact eq_one_of_inverted_of_fixed hR hg.1 hg.2
        (Subgroup.mem_centralizer_singleton_iff.mp hgA.2).symm
  · exact exists_inverted_subgroup_of_frobenius hR hy hyR hA hP h1 h2

theorem inverted_kernel_structure {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : Odd (Nat.card R)) {y : G} (hy : orderOf y = 2)
    (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hA : ∀ a ∈ R ⊓ Subgroup.centralizer {y}, ∀ b ∈ R ⊓ Subgroup.centralizer {y}, a * b = b * a)
    (hP : ∀ c ∈ R ⊓ Subgroup.centralizer {y}, c ≠ 1 → ∀ v ∈ R, y * v * y⁻¹ = v⁻¹ →
      v * c = c * v → v = 1) :
    ∃ B : Subgroup G, (∀ g, g ∈ B ↔ g ∈ R ∧ y * g * y⁻¹ = g⁻¹) ∧ B ≤ R ∧
      IsMulCommutative B ∧ (B.subgroupOf R).Normal ∧ (B.subgroupOf R).Characteristic ∧
      B ⊓ (R ⊓ Subgroup.centralizer {y}) = ⊥ ∧ B ⊔ (R ⊓ Subgroup.centralizer {y}) = R ∧
      (R : Set G) = (B : Set G) * ((R ⊓ Subgroup.centralizer {y} : Subgroup G) : Set G) ∧
      B = ⁅R, Subgroup.zpowers y⁆ ∧
      (R ⊓ Subgroup.centralizer {y} ≠ ⊥ →
        (∀ a ∈ R ⊓ Subgroup.centralizer {y}, a ≠ 1 →
          R ⊓ Subgroup.centralizer {a} = R ⊓ Subgroup.centralizer {y}) ∧
        ∀ a ∈ R ⊓ Subgroup.centralizer {y}, a ≠ 1 → ∀ b ∈ B, a * b * a⁻¹ = b → b = 1) := by
  obtain ⟨B, hBmem, hfact⟩ := exists_inverted_subgroup hR hy hyR hA hP
  set A₀ := R ⊓ Subgroup.centralizer {y} with hA₀def
  have hBR : B ≤ R := fun g hg => ((hBmem g).mp hg).1
  have hBinv : ∀ g ∈ B, y * g * y⁻¹ = g⁻¹ := fun g hg => ((hBmem g).mp hg).2
  have hAy : ∀ a ∈ A₀, y * a * y⁻¹ = a := fun a ha => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm, mul_inv_cancel_right]
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
      rw [← hBinv _ (B.mul_mem ha hb), ← hBinv a ha, ← hBinv b hb]
      group
    have h2 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by rw [← mul_inv_rev, h1]
    have h3 := congrArg (·⁻¹) h2
    simpa [mul_inv_rev] using h3
  have hBcomm : IsMulCommutative B := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  have hBA : B ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact eq_one_of_inverted_of_fixed hR hg.2.1 (hBinv g hg.1)
      (Subgroup.mem_centralizer_singleton_iff.mp hg.2.2).symm
  have hAB : ∀ a ∈ A₀, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    rw [hBmem]
    refine ⟨R.mul_mem (R.mul_mem ha.1 (hBR hb)) (R.inv_mem ha.1), ?_⟩
    calc y * (a * b * a⁻¹) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) * (y * a * y⁻¹)⁻¹ := by group
      _ = (a * b * a⁻¹)⁻¹ := by rw [hAy a ha, hBinv b hb]; group
  have hBnormal : (B.subgroupOf R).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨b, hb, a, ha, hba⟩ := hfact g g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hba, show b * a * (n : G) * (b * a)⁻¹ = b * (a * n * a⁻¹) * b⁻¹ by group]
    exact B.mul_mem (B.mul_mem hb (hAB a ha _ hn)) (B.inv_mem hb)
  have hsup : B ⊔ A₀ = R := by
    apply le_antisymm (sup_le hBR inf_le_left)
    intro r hr
    obtain ⟨b, hb, a, ha, rfl⟩ := hfact r hr
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right ha)
  have hset : (R : Set G) = (B : Set G) * (A₀ : Set G) := by
    ext r
    constructor
    · intro hr
      obtain ⟨b, hb, a, ha, rfl⟩ := hfact r hr
      exact Set.mem_mul.mpr ⟨b, hb, a, ha, rfl⟩
    · intro hr
      obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp hr
      exact R.mul_mem (hBR hb) ha.1
  have hcommutator : B = ⁅R, Subgroup.zpowers y⁆ := by
    apply le_antisymm
    · intro b hb
      obtain ⟨d, hd, hdb⟩ := exists_sq_eq_of_mem_invertedSet hR (show b ∈ invertedSet R y from
        (hBmem b).mp hb)
      have h1 : ⁅d, y⁆ = b := by
        rw [commutatorElement_def, ← hdb, sq]
        calc d * y * d⁻¹ * y⁻¹ = d * (y * d * y⁻¹)⁻¹ := by group
          _ = d * d := by rw [hd.2, inv_inv]
      rw [← h1]
      exact Subgroup.commutator_mem_commutator hd.1 (Subgroup.mem_zpowers y)
    · rw [Subgroup.commutator_le]
      intro g hg k hk
      rcases eq_one_or_eq_of_mem_zpowers hy hk with rfl | rfl
      · rw [commutatorElement_one_right]
        exact B.one_mem
      · obtain ⟨b, hb, a, ha, rfl⟩ := hfact g hg
        have hay : a * k = k * a := (Subgroup.mem_centralizer_singleton_iff.mp ha.2)
        have h1 : ⁅b * a, k⁆ = b * b := by
          rw [commutatorElement_def]
          calc b * a * k * (b * a)⁻¹ * k⁻¹ = b * (a * k) * a⁻¹ * b⁻¹ * k⁻¹ := by group
            _ = b * (k * a) * a⁻¹ * b⁻¹ * k⁻¹ := by rw [hay]
            _ = b * (k * b * k⁻¹)⁻¹ := by group
            _ = b * b := by rw [hBinv b hb, inv_inv]
        rw [h1]
        exact B.mul_mem hb hb
  have hcases : A₀ ≠ ⊥ → (∀ a ∈ A₀, a ≠ 1 → R ⊓ Subgroup.centralizer {a} = A₀) ∧
      ∀ a ∈ A₀, a ≠ 1 → ∀ b ∈ B, a * b * a⁻¹ = b → b = 1 := by
    intro _
    have hcent : ∀ a ∈ A₀, a ≠ 1 → R ⊓ Subgroup.centralizer {a} = A₀ :=
      fun a ha ha1 => centralizer_eq_fixed hR hy hyR hA hP ha ha1
    refine ⟨hcent, fun a ha ha1 b hb hab => ?_⟩
    have hbC : b ∈ R ⊓ Subgroup.centralizer {a} := by
      refine ⟨hBR hb, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc b * a = (a * b * a⁻¹) * a := by rw [hab]
        _ = a * b := by group
    rw [hcent a ha ha1] at hbC
    have hbBA : b ∈ B ⊓ A₀ := ⟨hb, hbC⟩
    rw [hBA, Subgroup.mem_bot] at hbBA
    exact hbBA
  have hchar : (B.subgroupOf R).Characteristic := by
    by_cases hA0 : A₀ = ⊥
    · have hBR' : B = R := by
        rw [← hsup, hA0, sup_bot_eq]
      have htop : B.subgroupOf R = ⊤ := by
        rw [hBR']
        exact Subgroup.subgroupOf_self R
      rw [htop]
      infer_instance
    · obtain ⟨hcent, hfpf⟩ := hcases hA0
      obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA0
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      have heq : B.subgroupOf R = commutator R := by
        apply le_antisymm
        ·
          intro x hx
          have hxB : (x : G) ∈ B := hx
          let φ : B → B := fun b => ⟨(b : G)⁻¹ * (a * b * a⁻¹),
            B.mul_mem (B.inv_mem b.2) (hAB a ha _ b.2)⟩
          have hφ : Function.Injective φ := by
            intro b₁ b₂ h12
            have h3 : (b₁ : G)⁻¹ * (a * b₁ * a⁻¹) = (b₂ : G)⁻¹ * (a * b₂ * a⁻¹) :=
              congrArg Subtype.val h12
            have h4 : a * ((b₂ : G) * (b₁ : G)⁻¹) * a⁻¹ = (b₂ : G) * (b₁ : G)⁻¹ := by
              calc a * ((b₂ : G) * (b₁ : G)⁻¹) * a⁻¹ =
                  (b₂ : G) * ((b₂ : G)⁻¹ * (a * b₂ * a⁻¹)) * ((b₁ : G)⁻¹ * (a * b₁ * a⁻¹))⁻¹ *
                    (b₁ : G)⁻¹ := by group
                _ = (b₂ : G) * (b₁ : G)⁻¹ := by rw [h3]; group
            have h5 := hfpf a ha ha1' _ (B.mul_mem b₂.2 (B.inv_mem b₁.2)) h4
            apply Subtype.ext
            exact (mul_inv_eq_one.mp h5).symm
          obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨x, hxB⟩
          have hbx : (b : G)⁻¹ * (a * b * a⁻¹) = x := congrArg Subtype.val hb
          have hx' : x = ⁅(⟨(b : G)⁻¹, R.inv_mem (hBR b.2)⟩ : R), (⟨a, ha.1⟩ : R)⁆ := by
            apply Subtype.ext
            rw [← hbx]
            simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
            group
          rw [hx', commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        ·
          rw [commutator_def, Subgroup.commutator_le]
          intro g₁ _ g₂ _
          obtain ⟨b₁, hb₁, a₁, ha₁, h₁⟩ := hfact g₁ g₁.2
          obtain ⟨b₂, hb₂, a₂, ha₂, h₂⟩ := hfact g₂ g₂.2
          let φ := QuotientGroup.mk' (B.subgroupOf R)
          have hφb : ∀ b ∈ B, ∀ hbR : b ∈ R, φ ⟨b, hbR⟩ = 1 := fun b hb hbR =>
            (QuotientGroup.eq_one_iff _).mpr hb
          have hg₁ : φ g₁ = φ ⟨a₁, ha₁.1⟩ := by
            have : g₁ = ⟨b₁, hBR hb₁⟩ * ⟨a₁, ha₁.1⟩ := Subtype.ext h₁
            rw [this, map_mul, hφb b₁ hb₁ (hBR hb₁), one_mul]
          have hg₂ : φ g₂ = φ ⟨a₂, ha₂.1⟩ := by
            have : g₂ = ⟨b₂, hBR hb₂⟩ * ⟨a₂, ha₂.1⟩ := Subtype.ext h₂
            rw [this, map_mul, hφb b₂ hb₂ (hBR hb₂), one_mul]
          have hcomm12 : ⁅(⟨a₁, ha₁.1⟩ : R), (⟨a₂, ha₂.1⟩ : R)⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact Subtype.ext (hA a₁ ha₁ a₂ ha₂)
          apply (QuotientGroup.eq_one_iff _).mp
          change φ ⁅g₁, g₂⁆ = 1
          rw [map_commutatorElement, hg₁, hg₂, ← map_commutatorElement, hcomm12, map_one]
      rw [heq]
      infer_instance
  exact ⟨B, hBmem, hBR, hBcomm, hBnormal, hchar, hBA, hsup, hset, hcommutator, hcases⟩

end Inverted

end CFSG.Wreathed.ConfinedOddCore
