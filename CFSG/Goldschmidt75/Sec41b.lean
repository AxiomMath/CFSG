module

public import CFSG.Goldschmidt75.Sig31Main

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_center_of_stronglyClosed_zpowers (T : Sylow 2 G) {a : G} (ha : orderOf a = 2)
    (hcl : fusionStronglyClosed ((zpowers a : Subgroup G) : Set G) T)
    (hO : goldschmidtOddCore G = ⊥) : a ∈ center G := by
  let : Fintype G := Fintype.ofFinite G
  have ha1 : a ≠ 1 := ne_one_of_orderOf_eq_two ha
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hiso : ∀ g : G, (g * a * g⁻¹) * a = a * (g * a * g⁻¹) → g * a * g⁻¹ = a := by
    intro g hcomm
    have hb2 : orderOf (g * a * g⁻¹) = 2 := by rw [orderOf_conj_eq]; exact ha
    have hpa := isPGroup_zpowers ha
    have hpb := isPGroup_zpowers hb2
    have hnorm : zpowers a ≤ normalizer ((zpowers (g * a * g⁻¹) : Subgroup G) : Set G) := by
      rw [zpowers_le]
      exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        exact (Commute.zpow_left hcomm k).eq)
    obtain ⟨Q, hQ⟩ := (IsPGroup.to_sup_of_normal_right' hpa hpb hnorm).exists_le_sylow
    have hclQ := stronglyClosed_of_le_sylow T Q hcl (fun x hx => hQ (mem_sup_left hx))
    have hbQ : (g⁻¹)⁻¹ * a * g⁻¹ ∈ (Q : Subgroup G) := by
      rw [inv_inv]
      exact hQ (mem_sup_right (mem_zpowers _))
    have hmem := hclQ a (mem_zpowers a) _ hbQ
    rw [inv_inv] at hmem
    rcases eq_one_or_eq_of_mem_zpowers ha hmem with h1 | h1
    · exfalso
      apply ha1
      have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
      rw [this, h1]
      group
    · exact h1
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G a ha1 haa hiso
  have hNO : N ≤ goldschmidtOddCore G := le_oddCore hNn hNodd
  rw [hO] at hNO
  rw [mem_center_iff]
  intro g
  have h1 := hNO (hN g)
  rw [mem_bot] at h1
  have h2 : g * a * g⁻¹ = a := by
    calc g * a * g⁻¹ = g * a * g⁻¹ * a⁻¹ * a := by group
      _ = a := by rw [h1, one_mul]
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [h2]

theorem exists_minimal_normal {N : Subgroup G} (hNn : N.Normal) (hN : N ≠ ⊥) :
    ∃ N₀ : Subgroup G, N₀.Normal ∧ N₀ ≠ ⊥ ∧ N₀ ≤ N ∧
      ∀ M : Subgroup G, M.Normal → M ≤ N₀ → M = ⊥ ∨ M = N₀ := by
  suffices key : ∀ k, ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → Nat.card N = k →
      ∃ N₀ : Subgroup G, N₀.Normal ∧ N₀ ≠ ⊥ ∧ N₀ ≤ N ∧
        ∀ M : Subgroup G, M.Normal → M ≤ N₀ → M = ⊥ ∨ M = N₀ from key _ N hNn hN rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro N hNn hN hk
  by_cases hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N
  · exact ⟨N, hNn, hN, le_rfl, hmin⟩
  · push Not at hmin
    obtain ⟨M, hMn, hMN, hM1, hMN'⟩ := hmin
    have hlt : Nat.card M < k := by
      rw [← hk]
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hMN) fun h => hMN' ?_
      exact Subgroup.eq_of_le_of_card_ge hMN h.ge
    obtain ⟨N₀, h1, h2, h3, h4⟩ := ih _ hlt M hMn hM1 rfl
    exact ⟨N₀, h1, h2, h3.trans hMN, h4⟩

omit [Finite G] in
theorem exists_two_pow_mem {H S : Subgroup G} [H.Normal] (hS : IsPGroup 2 S) (hG : H ⊔ S = ⊤)
    (g : G) : ∃ k : ℕ, g ^ (2 ^ k) ∈ H := by
  have hg : g ∈ ((S ⊔ H : Subgroup G) : Set G) := by
    rw [sup_comm, hG]
    exact Subgroup.mem_top g
  rw [mul_normal] at hg
  obtain ⟨s, hs, x, hx, rfl⟩ := hg
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff x).mpr hx, mul_one, ← QuotientGroup.mk_pow]
  have : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  rw [this, QuotientGroup.mk_one]

omit [Finite G] in
theorem isNilpotent_of_commutator_le_center {D : Subgroup G} (hD : ⁅D, D⁆ ≤ center G) :
    Group.IsNilpotent D := by
  have hc : ∀ x y : D, (x * y)⁻¹ * (y * x) ∈ center D := by
    intro x y
    have h1 : (((x * y)⁻¹ * (y * x) : D) : G) ∈ center G := by
      have e : (((x * y)⁻¹ * (y * x) : D) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e]
      exact hD (commutator_mem_commutator (inv_mem y.2) (inv_mem x.2))
    rw [mem_center_iff]
    intro z
    exact Subtype.ext (mem_center_iff.mp h1 z)
  have hcomm : IsMulCommutative (D ⧸ center D) := by
    refine isMulCommutative_iff.mpr fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center D) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center D) b
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    exact hc x y
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (center D))
    (QuotientGroup.ker_mk' (center D)).le

end CFSG.Goldschmidt75
