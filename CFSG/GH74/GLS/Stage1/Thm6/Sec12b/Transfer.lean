module

public import Mathlib.GroupTheory.Archimedean
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

theorem transfer_conj {G : Type} [Group G] [Finite G] (hIG : IG_15_15) (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {S N : Subgroup G} {u : G} (hS : IsSylow2In S ⊤)
    (hNS : N ≤ S) (hnorm : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N) (hne : N ≠ S)
    (hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ N) (huS : u ∈ S) (huN : u ∉ N)
    (hord : ∀ v ∈ S, v ∉ N → orderOf u ≤ orderOf v)
    (hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * u * g = y) → IsExtremal S y → y ∈ N ∨ u⁻¹ * y ∈ N) :
    ∃ g : G, g⁻¹ * u * g ∈ N ∧ IsExtremal S (g⁻¹ * u * g) := by
  rcases hIG G S N u hS hNS hnorm hne hcyc huS huN hord hext with
    ⟨M, hMn, hMcyc, _, huM⟩ | ⟨g, hgN, hgext, _⟩
  · exfalso
    have := hMn
    rcases hsimple.eq_bot_or_eq_top_of_normal M with e | e
    · subst e
      obtain ⟨a, b, hab⟩ := hnab
      have hcycG : IsCyclic G := isCyclic_of_surjective
        (QuotientGroup.quotientBot (G := G)).toMonoidHom
        (QuotientGroup.quotientBot (G := G)).surjective
      have hc : IsMulCommutative G := IsCyclic.isMulCommutative
      exact hab (hc.is_comm.comm a b)
    · exact huM (e ▸ Subgroup.mem_top u)
  · exact ⟨g, hgN, hgext⟩

theorem uniq_inv_coset {G : Type*} [Group G] {S N : Subgroup G}
    (hnorm : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N) {g₀ : G} (hg₀ : g₀ ∈ S)
    (hcyc : ∀ t ∈ S, ∃ k : ℤ, (g₀ ^ k)⁻¹ * t ∈ N) {v₁ v₂ : G} (h1 : v₁ ∈ S) (h2 : v₂ ∈ S)
    (h1N : v₁ ∉ N) (h2N : v₂ ∉ N) (h1sq : v₁ * v₁ ∈ N) (h2sq : v₂ * v₂ ∈ N) :
    v₁⁻¹ * v₂ ∈ N := by
  let K : AddSubgroup ℤ :=
    { carrier := {k | g₀ ^ k ∈ N}
      add_mem' := by
        intro a b ha hb
        have ha' : g₀ ^ a ∈ N := ha
        have hb' : g₀ ^ b ∈ N := hb
        show g₀ ^ (a + b) ∈ N
        rw [zpow_add]; exact N.mul_mem ha' hb'
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        have ha' : g₀ ^ a ∈ N := ha
        show g₀ ^ (-a) ∈ N
        rw [zpow_neg]; exact N.inv_mem ha' }
  obtain ⟨n, hn⟩ := Int.subgroup_cyclic K
  have hK : ∀ k : ℤ, g₀ ^ k ∈ N ↔ n ∣ k := by
    intro k
    have : k ∈ K ↔ k ∈ AddSubgroup.closure {n} := by rw [hn]
    rw [AddSubgroup.mem_closure_singleton] at this
    constructor
    · intro hk
      obtain ⟨m, hm⟩ := this.1 hk
      exact ⟨m, by rw [← hm]; simp [mul_comm]⟩
    · rintro ⟨m, rfl⟩
      exact this.2 ⟨m, by simp [mul_comm]⟩
  have key : ∀ v ∈ S, v ∉ N → v * v ∈ N → ∃ k : ℤ, ∃ m ∈ N, v = g₀ ^ k * m ∧ ¬ n ∣ k ∧ n ∣ 2 * k := by
    intro v hv hvN hvsq
    obtain ⟨k, hk⟩ := hcyc v hv
    refine ⟨k, (g₀ ^ k)⁻¹ * v, hk, by simp, ?_, ?_⟩
    · rw [← hK]
      intro hgk
      apply hvN
      have : v = g₀ ^ k * ((g₀ ^ k)⁻¹ * v) := by group
      rw [this]; exact N.mul_mem hgk hk
    · rw [← hK]
      have hconj : g₀ ^ (-k) * ((g₀ ^ k)⁻¹ * v) * g₀ ^ k ∈ N := by
        have := hnorm (g₀ ^ (-k)) (S.zpow_mem hg₀ _) _ hk
        simpa [zpow_neg] using this
      have e1 : g₀ ^ (2 * k) = (v * v) * (((g₀ ^ (-k) * ((g₀ ^ k)⁻¹ * v) * g₀ ^ k)) * ((g₀ ^ k)⁻¹ * v))⁻¹ := by
        have e2 : v = g₀ ^ k * ((g₀ ^ k)⁻¹ * v) := by group
        calc g₀ ^ (2 * k) = g₀ ^ k * g₀ ^ k := by rw [two_mul, zpow_add]
          _ = (g₀ ^ k * ((g₀ ^ k)⁻¹ * v)) * (g₀ ^ k * ((g₀ ^ k)⁻¹ * v)) *
              (((g₀ ^ (-k) * ((g₀ ^ k)⁻¹ * v) * g₀ ^ k)) * ((g₀ ^ k)⁻¹ * v))⁻¹ := by
              rw [zpow_neg]; group
          _ = _ := by rw [← e2]
      rw [e1]
      exact N.mul_mem hvsq (N.inv_mem (N.mul_mem hconj hk))
  obtain ⟨k₁, m₁, hm₁, e₁, hk₁, hd₁⟩ := key v₁ h1 h1N h1sq
  obtain ⟨k₂, m₂, hm₂, e₂, hk₂, hd₂⟩ := key v₂ h2 h2N h2sq
  obtain ⟨a, ha⟩ := hd₁
  obtain ⟨b, hb⟩ := hd₂
  have hdiv : n ∣ k₂ - k₁ := by
    rcases Int.even_or_odd' a with ⟨a', rfl | rfl⟩
    · exact absurd ⟨a', by linarith⟩ hk₁
    rcases Int.even_or_odd' b with ⟨b', rfl | rfl⟩
    · exact absurd ⟨b', by linarith⟩ hk₂
    exact ⟨b' - a', by linarith⟩
  have hgd : g₀ ^ (k₂ - k₁) ∈ N := (hK _).2 hdiv
  have e : v₁⁻¹ * v₂ = m₁⁻¹ * g₀ ^ (k₂ - k₁) * m₂ := by rw [e₁, e₂]; group
  rw [e]
  exact N.mul_mem (N.mul_mem (N.inv_mem hm₁) hgd) hm₂

theorem relIndex_extremal {G : Type*} [Group G] [Finite G] {x y g : G} {S T : Subgroup G}
    (hT : IsSylow2In T (Subgroup.centralizer ({x} : Set G))) (hg : g⁻¹ * x * g = y)
    (hext : IsExtremal S y) (hTS : T ≤ S) :
    (S ⊓ Subgroup.centralizer ({y} : Set G)).relIndex S = T.relIndex S := by
  have h1 := sylow2_conj hT g
  rw [Hconj_centralizer, hg] at h1
  have hc : Nat.card ↥(S ⊓ Subgroup.centralizer ({y} : Set G)) = Nat.card ↥T := by
    rw [sylow2_card_eq hext h1, Hconj_card]
  have e1 := Subgroup.relIndex_mul_card (S ⊓ Subgroup.centralizer ({y} : Set G)) S
  have e2 := Subgroup.relIndex_mul_card T S
  rw [inf_eq_left.2 hTS] at e2
  have e3 : (S ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ S =
      S ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [inf_eq_left.2 inf_le_left]
  rw [e3, hc] at e1
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)

theorem pigeon_of_relIndex_two {G : Type*} [Group G] {S H : Subgroup G}
    (h2 : H.relIndex S = 2) {d₁ d₂ : G} (h1 : d₁ ∈ S) (h2' : d₂ ∈ S) :
    d₁ ∈ H ∨ d₂ ∈ H ∨ d₁⁻¹ * d₂ ∈ H := by
  have hidx : (H.subgroupOf S).index = 2 := h2
  by_cases hd1 : d₁ ∈ H
  · exact Or.inl hd1
  by_cases hd2 : d₂ ∈ H
  · exact Or.inr (Or.inl hd2)
  right; right
  have hn1 : (⟨d₁, h1⟩ : S) ∉ H.subgroupOf S := hd1
  have hn2 : (⟨d₂, h2'⟩ : S) ∉ H.subgroupOf S := hd2
  have hn1' : (⟨d₁, h1⟩ : S)⁻¹ ∉ H.subgroupOf S := fun h => hn1 ((H.subgroupOf S).inv_mem_iff.1 h)
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨d₁, h1⟩ : S)⁻¹)
    (b := ⟨d₂, h2'⟩)).2 (iff_of_false hn1' hn2)
  exact this

theorem four_le_orderOf {G : Type*} [Group G] {S : Subgroup G} (hS : IsPGroup 2 ↥S) {v : G}
    (hv : v ∈ S) (h1 : v ≠ 1) (h2 : v * v ≠ 1) : 4 ≤ orderOf v := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨v, hv⟩
  have hk' : orderOf v = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk v hv).symm
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    interval_cases k
    · apply h1; exact orderOf_eq_one_iff.1 (by simpa using hk')
    · apply h2
      have h3 : v ^ orderOf v = 1 := pow_orderOf_eq_one v
      rw [hk'] at h3
      simpa [pow_two] using h3
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      _ = orderOf v := hk'.symm

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
