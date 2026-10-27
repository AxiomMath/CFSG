module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Isolated

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

section General

variable {X : Type} [Group X]

theorem centralizer_zpowers_eq_centralizer (y : X) :
    centralizer ((zpowers y : Subgroup X) : Set X) = centralizer ({y} : Set X) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem mul_self_eq_one_of_orderOf_eq_two {x : X} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← sq, ← hx, pow_orderOf_eq_one]

theorem eq_one_or_eq_of_mem_zpowers {z x : X} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {s x : X} (hs : orderOf s = 3)
    (hx : x ∈ zpowers s) : x = 1 ∨ x = s ∨ x = s⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hs, Nat.cast_ofNat]
  have h3 : s ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, ← hs, pow_orderOf_eq_one]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero s)
  · exact Or.inr (Or.inl (zpow_one s))
  · refine Or.inr (Or.inr (eq_inv_of_mul_eq_one_left ?_))
    rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, h3]

theorem normalizer_le_normalizer_centralizer (A : Subgroup X) :
    normalizer (A : Set X) ≤ normalizer (centralizer (A : Set X) : Set X) := by
  intro n hn
  have hA := mem_normalizer_iff.mp hn
  refine mem_normalizer_iff.mpr fun x => ?_
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hx a ha
    have ha' : n⁻¹ * a * n ∈ A := (hA _).mpr (by rwa [show n * (n⁻¹ * a * n) * n⁻¹ = a by group])
    calc a * (n * x * n⁻¹) = n * ((n⁻¹ * a * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * a * n)) * n⁻¹ := by rw [hx _ ha']
      _ = n * x * n⁻¹ * a := by group
  · intro hx a ha
    have h := hx _ ((hA a).mp ha)
    calc a * x = n⁻¹ * ((n * a * n⁻¹) * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * (n * a * n⁻¹)) * n := by rw [h]
      _ = x * a := by group

theorem normalizer_le_centralizer_of_involution {R : Subgroup X} {z : X} (hzR : z ∈ R)
    (hz : orderOf z = 2) (h : ∀ x ∈ R, orderOf x = 2 → x = z) :
    normalizer (R : Set X) ≤ centralizer ({z} : Set X) := by
  intro n hn
  have h1 : n * z * n⁻¹ = z :=
    h _ ((mem_normalizer_iff.mp hn z).mp hzR) (by rw [orderOf_conj_eq, hz])
  rw [mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [h1]

theorem normalizer_le_centralizer_of_center {R : Subgroup X} {z : X} (hzR : z ∈ R)
    (hz1 : z ≠ 1) (hzc : ∀ y ∈ R, z * y = y * z)
    (h : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x = 1 ∨ x = z) :
    normalizer (R : Set X) ≤ centralizer ({z} : Set X) := by
  intro n hn
  have hmem := mem_normalizer_iff.mp hn
  have hcen : ∀ y ∈ R, n * z * n⁻¹ * y = y * (n * z * n⁻¹) := by
    intro y hy
    have hy' : n⁻¹ * y * n ∈ R :=
      (hmem _).mpr (by rwa [show n * (n⁻¹ * y * n) * n⁻¹ = y by group])
    calc n * z * n⁻¹ * y = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by rw [hzc _ hy']
      _ = y * (n * z * n⁻¹) := by group
  rcases h _ ((hmem z).mp hzR) hcen with h1 | h1
  · rw [mul_inv_eq_one, mul_eq_left] at h1
    exact absurd h1 hz1
  · rw [mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h1]

variable [Finite X] {p : ℕ} [Fact p.Prime]

theorem isSylowOf_of_card {K P : Subgroup X} (hPK : P ≤ K) {n : ℕ} (hP : Nat.card P = p ^ n)
    (hK : ¬ p ^ (n + 1) ∣ Nat.card K) : IsSylowOf K p P := by
  have hpr : p.Prime := Fact.out
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have h1 := (hpr.pow_dvd_iff_le_factorization hK0).mp (hP ▸ Subgroup.card_dvd_of_le hPK)
  have h2 : ¬ n + 1 ≤ (Nat.card K).factorization p := fun h =>
    hK ((hpr.pow_dvd_iff_le_factorization hK0).mpr h)
  refine ⟨Sylow.ofCard (P.subgroupOf K) ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hP]
    congr 1
    omega
  · rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPK]

theorem isSylowOf_of_normalizer_le {K P W : Subgroup X} (hPK : P ≤ K)
    (hNW : normalizer (P : Set X) ≤ W) {n : ℕ} (hP : Nat.card P = p ^ n)
    (hK : ¬ p ^ (n + 1) ∣ Nat.card (K ⊓ W : Subgroup X)) : IsSylowOf K p P :=
  isSylowOf_of_isSylowOf_inf_normalizer hPK <| isSylowOf_of_card
    (le_inf hPK Subgroup.le_normalizer) hP fun h =>
      hK (h.trans (Subgroup.card_dvd_of_le (inf_le_inf_left _ hNW)))

omit [Fact p.Prime] in
theorem isSylowOf_of_forall_card_le {K P : Subgroup X} (hPK : P ≤ K) (hP : IsPGroup p P)
    (h : ∀ Q : Subgroup X, IsPGroup p Q → Q ≤ K → Nat.card Q ≤ Nat.card P) :
    IsSylowOf K p P := by
  obtain ⟨Q₀, hQ₀⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  have hPQ : P ≤ (Q₀ : Subgroup K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
    exact Subgroup.map_mono hQ₀
  exact ⟨Q₀, (Subgroup.eq_of_le_of_card_ge hPQ (h _ (Q₀.isPGroup'.map _)
    (Subgroup.map_subtype_le _))).symm⟩

theorem card_le_card_inf_of_isSylowOf {K N D Q : Subgroup X} (hD : IsSylowOf K p D)
    (hNK : N ≤ K) (hKN : K ≤ normalizer (N : Set X)) (hQ : IsPGroup p Q) (hQN : Q ≤ N) :
    Nat.card Q ≤ Nat.card (D ⊓ N : Subgroup X) := by
  obtain ⟨Q₁, hQ₁⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  have hQK : Q ≤ K := hQN.trans hNK
  have hQQ₁ : Q ≤ (Q₁ : Subgroup K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
    exact Subgroup.map_mono hQ₁
  obtain ⟨k, hkK, hk⟩ := exists_map_conj_eq_of_isSylowOf (⟨Q₁, rfl⟩ : IsSylowOf K p _) hD
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom)
    (MulAut.conj k).injective]
  refine Subgroup.card_le_of_le (le_inf ?_ ?_)
  · rw [← hk]
    exact Subgroup.map_mono hQQ₁
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp (hKN hkK) x).mp (hQN hx)

theorem card_le_of_isConj {a b : X} (hab : IsConj a b) {R S : Subgroup X} (hR : IsPGroup p R)
    (hRa : R ≤ centralizer ({a} : Set X)) (hS : IsSylowOf (centralizer ({b} : Set X)) p S) :
    Nat.card R ≤ Nat.card S := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  refine card_le_of_isSylowOf hS (hR.map _) ?_
  rw [centralizer_conj]
  exact Subgroup.map_mono hRa

end General

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
