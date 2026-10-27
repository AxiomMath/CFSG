module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

variable {Y : Type*} [Group Y]

theorem le_centralizer_of_odd_of_normalizes [Finite Y] {X D : Subgroup Y}
    (hXodd : Odd (Nat.card X)) (hXD : X ≤ normalizer (D : Set Y)) (hDX : D ≤ normalizer (X : Set Y))
    (hDp : ⁅D, D⁆ = D)
    (hcen : ∀ U : Subgroup Y, U ≤ D → D ≤ normalizer (U : Set Y) → Odd (Nat.card U) →
      ∀ u ∈ U, ∀ d ∈ D, u * d = d * u) :
    D ≤ centralizer (X : Set Y) := by
  have hU := hcen (X ⊓ D) inf_le_right
    (fun d hd => mem_normalizer_iff.mpr fun z => by
      constructor
      · intro hz
        exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hDX hd) z).mp (mem_inf.mp hz).1,
          (mem_normalizer_iff.mp (le_normalizer hd) z).mp (mem_inf.mp hz).2⟩
      · intro hz
        exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hDX hd) z).mpr (mem_inf.mp hz).1,
          (mem_normalizer_iff.mp (le_normalizer hd) z).mpr (mem_inf.mp hz).2⟩)
    (Odd.of_dvd_nat hXodd (card_dvd_of_le inf_le_left))
  have hcomm : ⁅X, D⁆ ≤ centralizer (D : Set Y) := by
    rw [commutator_le]
    intro x hx d hd
    have h1 : ⁅x, d⁆ ∈ X ⊓ D := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def, show x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) by group]
        exact mul_mem hx ((mem_normalizer_iff.mp (hDX hd) x⁻¹).mp (inv_mem hx))
      · rw [commutatorElement_def]
        exact mul_mem ((mem_normalizer_iff.mp (hXD hx) d).mp hd) (inv_mem hd)
    rw [mem_centralizer_iff]
    intro d' hd'
    exact (hU _ h1 d' hd').symm
  have h1 : ⁅⁅D, X⁆, D⁆ = ⊥ := by
    rw [commutator_comm D X, eq_bot_iff, commutator_le]
    intro c hc d hd
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.mp (hcomm hc) d hd).symm
  have h2 : ⁅⁅X, D⁆, D⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro c hc d hd
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.mp (hcomm hc) d hd).symm
  have h3 : ⁅⁅D, D⁆, X⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hDp] at h3
  intro d hd
  rw [mem_centralizer_iff]
  intro x hx
  have h4 : ⁅d, x⁆ ∈ ⁅D, X⁆ := commutator_mem_commutator hd hx
  rw [h3, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
  exact h4.symm

theorem le_center_or_eq_top_of_normal {K : Type*} [Group K] (hK : CFSG.IsQuasisimple K)
    {N : Subgroup K} (hN : N.Normal) : N ≤ center K ∨ N = ⊤ := by
  obtain ⟨hperf, hsimp, -⟩ := hK
  set π := QuotientGroup.mk' (center K) with hπ
  have hNm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have := hsimp
  have := hNm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro n hn
    have h1 : π n ∈ N.map π := mem_map_of_mem π hn
    rw [h, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff n).mp h1
  · right
    have hdec : ∀ g : K, ∃ n ∈ N, ∃ z ∈ center K, g = n * z := by
      intro g
      have hg : π g ∈ N.map π := by rw [h]; exact mem_top _
      obtain ⟨n, hn, hng⟩ := mem_map.mp hg
      refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
      have : π (n⁻¹ * g) = 1 := by rw [map_mul, map_inv, hng, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, commutator_le]
    intro g _ g' _
    obtain ⟨n, hn, z, hz, rfl⟩ := hdec g
    obtain ⟨n', hn', z', hz', rfl⟩ := hdec g'
    set ρ := QuotientGroup.mk' N with hρ
    have h1 : ρ ⁅n * z, n' * z'⁆ = 1 := by
      rw [map_commutatorElement, map_mul, map_mul,
        show ρ n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,
        show ρ n' = 1 from (QuotientGroup.eq_one_iff n').mpr hn', one_mul, one_mul,
        commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul,
        (mem_center_iff.mp hz z').symm]
    exact (QuotientGroup.eq_one_iff _).mp h1

theorem commutatorElement_mul_mul_eq {a b z w : Y} (hzb : z * b = b * z) (hzw : z * w = w * z)
    (hwa : w * a = a * w) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hwa' : w * a⁻¹ = a⁻¹ * w := (Commute.inv_right (show Commute w a from hwa)).eq
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * (z * w) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (w * z) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hwa']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem conj_eq_of_inv_mul_conj_mem {K K' : Subgroup Y} (hKp : ⁅K, K⁆ = K)
    (hKK' : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) {y : Y} (hyK : y ∈ normalizer (K : Set Y))
    (hy : ∀ k ∈ K, k⁻¹ * (y * k * y⁻¹) ∈ K') : ∀ k ∈ K, y * k * y⁻¹ = k := by
  have hzK : ∀ k ∈ K, k⁻¹ * (y * k * y⁻¹) ∈ K := fun k hk =>
    mul_mem (inv_mem hk) ((mem_normalizer_iff.mp hyK k).mp hk)
  have hconj : ∀ k ∈ K, y * k * y⁻¹ = k * (k⁻¹ * (y * k * y⁻¹)) := fun k _ => by group
  set T := K ⊓ centralizer ({y} : Set Y) with hT
  have hKT : ⁅K, K⁆ ≤ T := by
    rw [commutator_le]
    intro k₁ hk₁ k₂ hk₂
    refine mem_inf.mpr ⟨commutator_mem_commutator hk₁ hk₂ |> fun h => hKp ▸ h, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : y * ⁅k₁, k₂⁆ * y⁻¹ = ⁅k₁, k₂⁆ := by
      rw [show y * ⁅k₁, k₂⁆ * y⁻¹ = ⁅y * k₁ * y⁻¹, y * k₂ * y⁻¹⁆ by
        rw [commutatorElement_def, commutatorElement_def]; group, hconj k₁ hk₁, hconj k₂ hk₂]
      exact commutatorElement_mul_mul_eq (hKK' _ hk₂ _ (hy k₁ hk₁)).symm
        (hKK' _ (hzK k₂ hk₂) _ (hy k₁ hk₁)).symm (hKK' _ hk₁ _ (hy k₂ hk₂)).symm
    calc ⁅k₁, k₂⁆ * y = y * ⁅k₁, k₂⁆ * y⁻¹ * y := by rw [h1]
      _ = y * ⁅k₁, k₂⁆ := by group
  rw [hKp] at hKT
  intro k hk
  have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hKT hk)).2
  calc y * k * y⁻¹ = k * y * y⁻¹ := by rw [h1]
    _ = k := by group

theorem le_centralizer_of_diagonal [Finite Y] {K K' X : Subgroup Y} (hK : CFSG.IsQuasisimple K)
    (hKnc : ∃ k₁ ∈ K, ∃ k₂ ∈ K, k₁ * k₂ ≠ k₂ * k₁)
    (hgen : ∀ (g : ↥K →* Y) (U : Subgroup Y), Odd (Nat.card U) → g.range ≤ U → g.range = ⊥)
    {b : Y} (hb : b * b = 1) (hKK' : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    (hbK : ∀ k ∈ K, b⁻¹ * k * b ∈ K') (hXodd : Odd (Nat.card X))
    (hXK : X ≤ normalizer (K : Set Y)) (hCb : centralizer ({b} : Set Y) ≤ normalizer (X : Set Y))
    (hXb : X ≤ centralizer ({b} : Set Y)) : K ≤ centralizer (X : Set Y) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hKp : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  let f : ↥K →* Y :=
    { toFun := fun k => (k : Y) * (b⁻¹ * k * b)
      map_one' := by simp
      map_mul' := fun k₁ k₂ => by
        simp only [Subgroup.coe_mul]
        have h := hKK' _ k₂.2 _ (hbK _ k₁.2)
        calc (k₁ : Y) * k₂ * (b⁻¹ * (k₁ * k₂) * b)
            = k₁ * (k₂ * (b⁻¹ * k₁ * b)) * (b⁻¹ * k₂ * b) := by group
          _ = k₁ * ((b⁻¹ * k₁ * b) * k₂) * (b⁻¹ * k₂ * b) := by rw [h]
          _ = k₁ * (b⁻¹ * k₁ * b) * (k₂ * (b⁻¹ * k₂ * b)) := by group }
  have hf : ∀ k : ↥K, f k = (k : Y) * (b⁻¹ * k * b) := fun _ => rfl
  have hΔb : f.range ≤ centralizer ({b} : Set Y) := by
    rintro _ ⟨k, rfl⟩
    rw [mem_centralizer_singleton_iff, hf]
    have h := hKK' _ k.2 _ (hbK _ k.2)
    calc (k : Y) * (b⁻¹ * k * b) * b = (b⁻¹ * k * b) * k * b := by rw [h]
      _ = b * (k * (b⁻¹ * k * b)) := by rw [hbinv]; simp only [mul_assoc]
  have hfconj : ∀ x ∈ X, ∀ (k : Y) (hk : k ∈ K) (hk' : x * k * x⁻¹ ∈ K),
      x * f ⟨k, hk⟩ * x⁻¹ = f ⟨x * k * x⁻¹, hk'⟩ := by
    intro x hx k hk hk'
    have hxb : x * b = b * x := mem_centralizer_singleton_iff.mp (hXb hx)
    have h1 : x⁻¹ * b⁻¹ * x = b⁻¹ := by
      rw [(Commute.inv_inv (show Commute x b from hxb)).eq]; group
    have h2 : x⁻¹ * b = b * x⁻¹ := (Commute.inv_left (show Commute x b from hxb)).eq
    rw [hf, hf]
    calc x * (k * (b⁻¹ * k * b)) * x⁻¹ = x * k * b⁻¹ * k * (b * x⁻¹) := by group
      _ = x * k * (x⁻¹ * b⁻¹ * x) * k * (x⁻¹ * b) := by rw [h1, h2]
      _ = x * k * x⁻¹ * (b⁻¹ * (x * k * x⁻¹) * b) := by group
  have hXK' : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk =>
    (mem_normalizer_iff.mp (hXK hx) k).mp hk
  have hXΔ : X ≤ normalizer (f.range : Set Y) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro n
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      rw [hfconj x hx k hk (hXK' x hx k hk)]
      exact ⟨_, rfl⟩
    · rintro ⟨⟨k, hk⟩, hkn⟩
      have h1 := hfconj x⁻¹ (inv_mem hx) k hk (hXK' _ (inv_mem hx) k hk)
      rw [hkn, show x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n by group] at h1
      rw [h1]
      exact ⟨_, rfl⟩
  have hΔp : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hK.1.commutator_eq_top]
  have hcen : ∀ U : Subgroup Y, U ≤ f.range → f.range ≤ normalizer (U : Set Y) →
      Odd (Nat.card U) → ∀ u ∈ U, ∀ d ∈ f.range, u * d = d * u := by
    intro U hUΔ hΔU hUodd u hu d hd
    have hW : (U.comap f).Normal := ⟨fun w hw k => by
      show f (k * w * k⁻¹) ∈ U
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hΔU ⟨k, rfl⟩) (f w)).mp hw⟩
    rcases le_center_or_eq_top_of_normal hK hW with h | h
    · obtain ⟨w, rfl⟩ := hUΔ hu
      obtain ⟨k, rfl⟩ := hd
      have hwc := mem_center_iff.mp (h (show w ∈ U.comap f from hu)) k
      rw [← map_mul, ← map_mul, hwc]
    · exfalso
      have h1 : f.range ≤ U := by
        rintro _ ⟨k, rfl⟩
        exact (show k ∈ U.comap f from h ▸ mem_top k)
      have h2 := hgen f U hUodd h1
      have hKK : ∀ k ∈ K, k ∈ K' := fun k hk => by
        have h3 : f ⟨k, hk⟩ = 1 := by
          have h4 : f ⟨k, hk⟩ ∈ f.range := ⟨_, rfl⟩
          rwa [h2, mem_bot] at h4
        rw [hf] at h3
        have h5 : k = (b⁻¹ * k * b)⁻¹ := eq_inv_of_mul_eq_one_left h3
        rw [h5]
        exact inv_mem (hbK k hk)
      obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := hKnc
      exact hne (hKK' k₁ hk₁ k₂ (hKK k₂ hk₂))
  have hΔX := le_centralizer_of_odd_of_normalizes hXodd hXΔ (hΔb.trans hCb) hΔp hcen
  intro k hk
  rw [mem_centralizer_iff]
  intro x hx
  have hy : ∀ k ∈ K, k⁻¹ * (x * k * x⁻¹) ∈ K' := by
    intro k hk
    have hm := hXK' x hx k hk
    have h1 : f ⟨x * k * x⁻¹, hm⟩ = f ⟨k, hk⟩ := by
      rw [← hfconj x hx k hk hm]
      have h2 := mem_centralizer_iff.mp (hΔX ⟨⟨k, hk⟩, rfl⟩) x hx
      rw [h2]
      group
    rw [hf, hf] at h1
    have h3 : k⁻¹ * (x * k * x⁻¹) = b⁻¹ * (k * (x * k * x⁻¹)⁻¹) * b := by
      calc k⁻¹ * (x * k * x⁻¹)
          = k⁻¹ * ((x * k * x⁻¹) * (b⁻¹ * (x * k * x⁻¹) * b)) * (b⁻¹ * (x * k * x⁻¹) * b)⁻¹ := by
            group
        _ = k⁻¹ * (k * (b⁻¹ * k * b)) * (b⁻¹ * (x * k * x⁻¹) * b)⁻¹ := by rw [h1]
        _ = b⁻¹ * (k * (x * k * x⁻¹)⁻¹) * b := by group
    rw [h3]
    exact hbK _ (mul_mem hk (inv_mem hm))
  have h := conj_eq_of_inv_mul_conj_mem hKp hKK' (hXK hx) hy k hk
  calc x * k = x * k * x⁻¹ * x := by group
    _ = k * x := by rw [h]

end CFSG.ComponentClassification.FooteLit
