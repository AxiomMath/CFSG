module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

private abbrev wmodDecEq : DecidableEq WMod := WMod.equivProd.decidableEq

attribute [local instance 2000] wmodDecEq

private def mY : WMod := WMod.wx₁ ^ 2

private def mZ : WMod := (WMod.wx₁ * WMod.wx₂) ^ 2

private def mU : WMod := WMod.wx₁⁻¹ * WMod.wx₂ * WMod.wlam

private abbrev Quad (p q g : WMod) : Prop := g = 1 ∨ g = p ∨ g = q ∨ g = p * q

private lemma wmod_conj_ne_inv_aux :
    ∀ (a b : Fin 4) (i : Fin 2),
      (⟨a, b, i⟩ : WMod) * WMod.wx₁ * (⟨a, b, i⟩ : WMod)⁻¹ ≠ WMod.wx₁⁻¹ := by
  decide +kernel

private lemma wmod_pair_aux :
    ∀ (a b : Fin 4) (i : Fin 2) (c d : Fin 4) (j : Fin 2),
      (⟨a, b, i⟩ : WMod) * ⟨a, b, i⟩ = 1 → (⟨c, d, j⟩ : WMod) * ⟨c, d, j⟩ = 1 →
      (⟨a, b, i⟩ : WMod) * ⟨c, d, j⟩ = ⟨c, d, j⟩ * ⟨a, b, i⟩ →
      (Quad mY mZ ⟨a, b, i⟩ ∧ Quad mY mZ ⟨c, d, j⟩) ∨
      (Quad mZ WMod.wlam ⟨a, b, i⟩ ∧ Quad mZ WMod.wlam ⟨c, d, j⟩) ∨
      (Quad mZ mU ⟨a, b, i⟩ ∧ Quad mZ mU ⟨c, d, j⟩) := by
  decide +kernel

private lemma wmod_gen_facts :
    (mY * mY = 1 ∧ mZ * mZ = 1 ∧ mY * mZ = mZ * mY) ∧
    (mZ * mZ = 1 ∧ WMod.wlam * WMod.wlam = 1 ∧ mZ * WMod.wlam = WMod.wlam * mZ) ∧
    (mZ * mZ = 1 ∧ mU * mU = 1 ∧ mZ * mU = mU * mZ) := by
  decide +kernel

section Transport

variable {G : Type*} [Group G] {x₁ x₂ lam : G}

private theorem mem_closure_of_quad {a b g : G} (h : g = 1 ∨ g = a ∨ g = b ∨ g = a * b) :
    g ∈ closure ({a, b} : Set G) := by
  rcases h with h | h | h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.subset_closure (by simp)
  · rw [h]
    exact Subgroup.subset_closure (by simp)
  · rw [h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

theorem wreath_conj_x₁_ne_inv (hw : WreathRel x₁ x₂ lam) {u : G}
    (hu : u ∈ wreathGrp x₁ x₂ lam) : u * x₁ * u⁻¹ ≠ x₁⁻¹ := by
  obtain ⟨φ, hinj, hrange, hx₁, hx₂, hl⟩ := hw.exists_embedding
  rw [← hrange] at hu
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hu
  intro heq
  have h1 : m * WMod.wx₁ * m⁻¹ = WMod.wx₁⁻¹ := by
    apply hinj
    rw [map_mul, map_mul, map_inv, map_inv, hx₁]
    exact heq
  obtain ⟨a, b, i⟩ := m
  exact wmod_conj_ne_inv_aux a b i h1

theorem wreath_pair_cases (hw : WreathRel x₁ x₂ lam) {a b : G} (ha : a ∈ wreathGrp x₁ x₂ lam)
    (hb : b ∈ wreathGrp x₁ x₂ lam) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) :
    (a ∈ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) ∧
        b ∈ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G)) ∨
      (a ∈ closure ({(x₁ * x₂) ^ 2, lam} : Set G) ∧
        b ∈ closure ({(x₁ * x₂) ^ 2, lam} : Set G)) ∨
      (a ∈ closure ({(x₁ * x₂) ^ 2, x₁⁻¹ * x₂ * lam} : Set G) ∧
        b ∈ closure ({(x₁ * x₂) ^ 2, x₁⁻¹ * x₂ * lam} : Set G)) := by
  obtain ⟨φ, hinj, hrange, hx₁, hx₂, hl⟩ := hw.exists_embedding
  rw [← hrange] at ha hb
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hb
  have hm2 : m * m = 1 := hinj (by rw [map_mul, map_one]; exact ha2)
  have hn2 : n * n = 1 := hinj (by rw [map_mul, map_one]; exact hb2)
  have hmn : m * n = n * m := hinj (by rw [map_mul, map_mul]; exact hab)
  have hY : φ mY = x₁ ^ 2 := by rw [mY, map_pow, hx₁]
  have hZ : φ mZ = (x₁ * x₂) ^ 2 := by rw [mZ, map_pow, map_mul, hx₁, hx₂]
  have hU : φ mU = x₁⁻¹ * x₂ * lam := by
    rw [mU, map_mul, map_mul, map_inv, hx₁, hx₂, hl]
  have tr : ∀ {p q : WMod} {P Q : G}, φ p = P → φ q = Q → ∀ g : WMod, Quad p q g →
      φ g ∈ closure ({P, Q} : Set G) := by
    intro p q P Q hp hq g hg
    apply mem_closure_of_quad
    rcases hg with hg | hg | hg | hg
    · left
      rw [hg]
      exact map_one φ
    · right
      left
      rw [hg]
      exact hp
    · right
      right
      left
      rw [hg]
      exact hq
    · right
      right
      right
      rw [hg, map_mul, hp, hq]
  obtain ⟨a', b', i'⟩ := m
  obtain ⟨c', d', j'⟩ := n
  rcases wmod_pair_aux a' b' i' c' d' j' hm2 hn2 hmn with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨tr hY hZ _ h1, tr hY hZ _ h2⟩
  · exact Or.inr (Or.inl ⟨tr hZ hl _ h1, tr hZ hl _ h2⟩)
  · exact Or.inr (Or.inr ⟨tr hZ hU _ h1, tr hZ hU _ h2⟩)

theorem wreath_gen_facts (hw : WreathRel x₁ x₂ lam) :
    (x₁ ^ 2 * x₁ ^ 2 = 1 ∧ (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 ∧
        x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2) ∧
      ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 ∧ lam * lam = 1 ∧
        (x₁ * x₂) ^ 2 * lam = lam * (x₁ * x₂) ^ 2) ∧
      ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 ∧
        (x₁⁻¹ * x₂ * lam) * (x₁⁻¹ * x₂ * lam) = 1 ∧
        (x₁ * x₂) ^ 2 * (x₁⁻¹ * x₂ * lam) = (x₁⁻¹ * x₂ * lam) * (x₁ * x₂) ^ 2) := by
  obtain ⟨φ, hinj, hrange, hx₁, hx₂, hl⟩ := hw.exists_embedding
  have hY : φ mY = x₁ ^ 2 := by rw [mY, map_pow, hx₁]
  have hZ : φ mZ = (x₁ * x₂) ^ 2 := by rw [mZ, map_pow, map_mul, hx₁, hx₂]
  have hU : φ mU = x₁⁻¹ * x₂ * lam := by
    rw [mU, map_mul, map_mul, map_inv, hx₁, hx₂, hl]
  obtain ⟨⟨a1, a2, a3⟩, ⟨-, b2, b3⟩, ⟨-, c2, c3⟩⟩ := wmod_gen_facts
  have e1 := congrArg φ a1
  have e2 := congrArg φ a2
  have e3 := congrArg φ a3
  have e4 := congrArg φ b2
  have e5 := congrArg φ b3
  have e6 := congrArg φ c2
  have e7 := congrArg φ c3
  rw [map_mul, map_one, hY] at e1
  rw [map_mul, map_one, hZ] at e2
  rw [map_mul, map_mul, hY, hZ] at e3
  rw [map_mul, map_one, hl] at e4
  rw [map_mul, map_mul, hZ, hl] at e5
  rw [map_mul, map_one, hU] at e6
  rw [map_mul, map_mul, hZ, hU] at e7
  exact ⟨⟨e1, e2, e3⟩, ⟨e2, e4, e5⟩, ⟨e2, e6, e7⟩⟩

end Transport

section Card

variable {G : Type} [Group G] [Finite G] {x₁ x₂ lam : G}

theorem card_closure_pair_le_four {a b : G} (hab : a * b = b * a) (ha : a * a = 1)
    (hb : b * b = 1) : Nat.card (closure ({a, b} : Set G)) ≤ 4 := by
  have hsub : ((closure ({a, b} : Set G) : Subgroup G) : Set G) ⊆ ({1, a, b, a * b} : Set G) := by
    intro x hx
    rcases mem_closure_pair_cases hab ha hb hx with h | h | h | h <;> simp [h]
  have h4 : ({1, a, b, a * b} : Set G).ncard ≤ 4 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    have h3 : ({a, b, a * b} : Set G).ncard ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      have h2 : ({b, a * b} : Set G).ncard ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
      omega
    omega
  calc Nat.card (closure ({a, b} : Set G))
      = ((closure ({a, b} : Set G) : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, a, b, a * b} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := h4

theorem wreath_elem_four_cases (hw : WreathRel x₁ x₂ lam) {D : Subgroup G}
    (hDT : D ≤ wreathGrp x₁ x₂ lam) (hDe : CFSG.Open.IsElemAbelian 2 D)
    (hcard : Nat.card D = 4) :
    D = closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) ∨
      D = closure ({(x₁ * x₂) ^ 2, lam} : Set G) ∨
      D = closure ({(x₁ * x₂) ^ 2, x₁⁻¹ * x₂ * lam} : Set G) := by
  have hsq : ∀ d ∈ D, d * d = 1 := fun d hd => by
    rw [← pow_two]
    exact hDe.2 d hd
  haveI : IsMulCommutative D := hDe.1
  have hcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d := fun d hd e he =>
    congrArg Subtype.val (mul_comm' (⟨d, hd⟩ : D) ⟨e, he⟩)
  obtain ⟨a, haD, ha1⟩ : ∃ a ∈ D, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr hcon
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq a haD) ha1
  have hcardA : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers, ha2]
  obtain ⟨b, hbD, hbA⟩ : ∃ b ∈ D, b ∉ zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ zpowers a := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hb1 : b ≠ 1 := fun h1 => hbA (by rw [h1]; exact Subgroup.one_mem _)
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq b hbD) hb1
  have hcardB : Nat.card (zpowers b) = 2 := by rw [Nat.card_zpowers, hb2]
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    rcases pt_eq_one_or_of_mem_zpowers ha2 hxa with h1 | h1
    · exact h1
    · exfalso
      rcases pt_eq_one_or_of_mem_zpowers hb2 hxb with h2 | h2
      · exact ha1 (h1.symm.trans h2)
      · apply hbA
        rw [← h2, h1]
        exact Subgroup.mem_zpowers a
  have hcommAB : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (hcomm a haD b hbD) m n).eq
  have hcardAB : Nat.card ↥(zpowers a ⊔ zpowers b) = 4 := by
    rw [card_sup_of_commute hcommAB hinf, hcardA, hcardB]
  have hAB : zpowers a ⊔ zpowers b = D :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr haD) (Subgroup.zpowers_le.mpr hbD))
      (by rw [hcardAB, hcard])
  obtain ⟨⟨hyy, hzz, hyz⟩, ⟨hzz', hll, hzl⟩, ⟨hzz'', huu, hzu⟩⟩ := wreath_gen_facts hw
  rcases wreath_pair_cases hw (hDT haD) (hDT hbD) (hsq a haD) (hsq b hbD)
      (hcomm a haD b hbD) with ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
  · left
    have hle : D ≤ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) := by
      rw [← hAB]
      exact sup_le (Subgroup.zpowers_le.mpr h1a) (Subgroup.zpowers_le.mpr h1b)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard]; exact card_closure_pair_le_four hyz hyy hzz)
  · right
    left
    have hle : D ≤ closure ({(x₁ * x₂) ^ 2, lam} : Set G) := by
      rw [← hAB]
      exact sup_le (Subgroup.zpowers_le.mpr h2a) (Subgroup.zpowers_le.mpr h2b)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard]; exact card_closure_pair_le_four hzl hzz' hll)
  · right
    right
    have hle : D ≤ closure ({(x₁ * x₂) ^ 2, x₁⁻¹ * x₂ * lam} : Set G) := by
      rw [← hAB]
      exact sup_le (Subgroup.zpowers_le.mpr h3a) (Subgroup.zpowers_le.mpr h3b)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard]; exact card_closure_pair_le_four hzu hzz'' huu)

end Card

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
