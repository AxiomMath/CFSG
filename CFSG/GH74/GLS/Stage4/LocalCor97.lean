module

public import CFSG.GH74.GLS.Stage4.LocalRankOne
public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
open scoped Pointwise

variable {G : Type} [Group G]

structure Cor97 (p : ℕ) (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G) :
    Prop where
  prime : p.Prime
  p_ne_two : p ≠ 2
  comm_H : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  conj_H₁ : ∀ h ∈ H, r₁ * h * r₁⁻¹ ∈ H
  conj_H₂ : ∀ h ∈ H, r₂ * h * r₂⁻¹ ∈ H
  sq₁ : r₁ * r₁ ∈ H
  sq₂ : r₂ * r₂ ∈ H
  pow : (r₁ * r₂) ^ 6 ∈ H
  H_pPrime : ∀ h ∈ H, ¬ p ∣ orderOf h
  U_pGroup : IsPGroup p U
  U_gen : U = ⨆ k ∈ Set.Icc (1 : ℤ) 6, root k
  ne_bot : ∀ i, IsRoot 6 i → root i ≠ ⊥
  root_comm : ∀ i, IsRoot 6 i → ∀ x ∈ root i, ∀ y ∈ root i, x * y = y * x
  root_exp : ∀ i, IsRoot 6 i → ∀ x ∈ root i, x ^ p = 1
  invariant : ∀ i, IsRoot 6 i → ∀ h ∈ H, ∀ x ∈ root i, h * x * h⁻¹ ∈ root i
  act₁ : conjBy r₁⁻¹ (root 1) = root (-1) ∧ conjBy r₁⁻¹ (root (-1)) = root 1 ∧
    ∀ i : ℤ, 2 ≤ i → i ≤ 6 → conjBy r₁⁻¹ (root i) = root (8 - i) ∧
      conjBy r₁⁻¹ (root (-i)) = root (-(8 - i))
  act₂ : conjBy r₂⁻¹ (root 6) = root (-6) ∧ conjBy r₂⁻¹ (root (-6)) = root 6 ∧
    ∀ i : ℤ, 1 ≤ i → i ≤ 5 → conjBy r₂⁻¹ (root i) = root (6 - i) ∧
      conjBy r₂⁻¹ (root (-i)) = root (-(6 - i))
  opp : U ⊓ conjBy ((r₁ * r₂) ^ 3) U = ⊥
  L92 : ∀ Z : Subgroup G, Z ≤ U → (∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z) →
    ∀ l : List ℤ, l.Nodup → (∀ i, i ∈ l ↔ IsRoot 6 i ∧ root i ≤ Z) →
      (Z : Set G) = chainProd root l ∧ Nat.card Z = (l.map fun i => Nat.card (root i)).prod
  sl2₁ : SL2Pair H r₁ (root 1) (root (-1))
  sl2₆ : SL2Pair H r₂ (root 6) (root (-6))


theorem iff_of_conjBy {m : G} {A B : Subgroup G} (h : conjBy m⁻¹ A = B) (x : G) :
    x ∈ A ↔ m * x * m⁻¹ ∈ B := by
  rw [← h, mem_conjBy_iff]
  simp [mul_assoc]

@[expose] def ActsAs (root : ℤ → Subgroup G) (u : G) (σ : ℤ → ℤ) : Prop :=
  ∀ q : ℤ, ∀ x : G, x ∈ root (Rt 6 q) ↔ u * x * u⁻¹ ∈ root (Rt 6 (σ q))

theorem ActsAs.mul {root : ℤ → Subgroup G} {u v : G} {σ τ : ℤ → ℤ} (hu : ActsAs root u σ)
    (hv : ActsAs root v τ) : ActsAs root (u * v) (fun q => σ (τ q)) := by
  intro q x
  rw [hv q x, hu (τ q) (v * x * v⁻¹)]
  have e : u * (v * x * v⁻¹) * u⁻¹ = u * v * x * (u * v)⁻¹ := by group
  rw [e]

theorem ActsAs.congr {root : ℤ → Subgroup G} {u : G} {σ τ : ℤ → ℤ} (h : ActsAs root u σ)
    (hστ : ∀ q, σ q = τ q) : ActsAs root u τ := by
  intro q x
  rw [← hστ q]
  exact h q x

theorem ActsAs.one {root : ℤ → Subgroup G} : ActsAs root (1 : G) (fun q => q) := by
  intro q x
  simp

theorem Rt6_val0 : Rt 6 0 = 1 := by decide
theorem Rt6_val1 : Rt 6 1 = 2 := by decide
theorem Rt6_val2 : Rt 6 2 = 3 := by decide
theorem Rt6_val3 : Rt 6 3 = 4 := by decide
theorem Rt6_val4 : Rt 6 4 = 5 := by decide
theorem Rt6_val5 : Rt 6 5 = 6 := by decide
theorem Rt6_val6 : Rt 6 6 = -1 := by decide
theorem Rt6_val7 : Rt 6 7 = -2 := by decide
theorem Rt6_val8 : Rt 6 8 = -3 := by decide
theorem Rt6_val9 : Rt 6 9 = -4 := by decide
theorem Rt6_val10 : Rt 6 10 = -5 := by decide
theorem Rt6_val11 : Rt 6 11 = -6 := by decide

theorem Rt6_emod (q : ℤ) : Rt 6 q = Rt 6 (q % 12) := Rt_congr (by simp)


theorem actsAs_r₁ {root : ℤ → Subgroup G} {r₁ : G}
    (h : conjBy r₁⁻¹ (root 1) = root (-1) ∧ conjBy r₁⁻¹ (root (-1)) = root 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ 6 → conjBy r₁⁻¹ (root i) = root (8 - i) ∧
        conjBy r₁⁻¹ (root (-i)) = root (-(8 - i))) :
    ActsAs root r₁ (fun q => 6 - q) := by
  obtain ⟨a1, a2, a3⟩ := h
  intro q x
  have hq : Rt 6 q = Rt 6 (q % 12) := Rt6_emod q
  have hq' : Rt 6 (6 - q) = Rt 6 ((6 - q % 12) % 12) := by
    rw [Rt6_emod (6 - q)]
    congr 1
    omega
  show x ∈ root (Rt 6 q) ↔ r₁ * x * r₁⁻¹ ∈ root (Rt 6 (6 - q))
  rw [hq, hq']
  have h0 := Int.emod_nonneg q (by norm_num : (12 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos q (by norm_num : (0 : ℤ) < 12)
  generalize q % 12 = v at *
  interval_cases v
  · norm_num [Rt6_val0, Rt6_val6]
    exact iff_of_conjBy a1 x
  · norm_num [Rt6_val1, Rt6_val5]
    exact iff_of_conjBy (a3 2 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val2, Rt6_val4]
    exact iff_of_conjBy (a3 3 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val3]
    exact iff_of_conjBy (a3 4 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val4, Rt6_val2]
    exact iff_of_conjBy (a3 5 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val5, Rt6_val1]
    exact iff_of_conjBy (a3 6 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val6, Rt6_val0]
    exact iff_of_conjBy a2 x
  · norm_num [Rt6_val7, Rt6_val11]
    exact iff_of_conjBy (a3 2 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val8, Rt6_val10]
    exact iff_of_conjBy (a3 3 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val9]
    exact iff_of_conjBy (a3 4 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val10, Rt6_val8]
    exact iff_of_conjBy (a3 5 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val11, Rt6_val7]
    exact iff_of_conjBy (a3 6 (by norm_num) (by norm_num)).2 x


theorem actsAs_r₂ {root : ℤ → Subgroup G} {r₂ : G}
    (h : conjBy r₂⁻¹ (root 6) = root (-6) ∧ conjBy r₂⁻¹ (root (-6)) = root 6 ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 5 → conjBy r₂⁻¹ (root i) = root (6 - i) ∧
        conjBy r₂⁻¹ (root (-i)) = root (-(6 - i))) :
    ActsAs root r₂ (fun q => 4 - q) := by
  obtain ⟨b1, b2, b3⟩ := h
  intro q x
  have hq : Rt 6 q = Rt 6 (q % 12) := Rt6_emod q
  have hq' : Rt 6 (4 - q) = Rt 6 ((4 - q % 12) % 12) := by
    rw [Rt6_emod (4 - q)]
    congr 1
    omega
  show x ∈ root (Rt 6 q) ↔ r₂ * x * r₂⁻¹ ∈ root (Rt 6 (4 - q))
  rw [hq, hq']
  have h0 := Int.emod_nonneg q (by norm_num : (12 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos q (by norm_num : (0 : ℤ) < 12)
  generalize q % 12 = v at *
  interval_cases v
  · norm_num [Rt6_val0, Rt6_val4]
    exact iff_of_conjBy (b3 1 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val1, Rt6_val3]
    exact iff_of_conjBy (b3 2 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val2]
    exact iff_of_conjBy (b3 3 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val3, Rt6_val1]
    exact iff_of_conjBy (b3 4 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val4, Rt6_val0]
    exact iff_of_conjBy (b3 5 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt6_val5, Rt6_val11]
    exact iff_of_conjBy b1 x
  · norm_num [Rt6_val6, Rt6_val10]
    exact iff_of_conjBy (b3 1 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val7, Rt6_val9]
    exact iff_of_conjBy (b3 2 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val8]
    exact iff_of_conjBy (b3 3 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val9, Rt6_val7]
    exact iff_of_conjBy (b3 4 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val10, Rt6_val6]
    exact iff_of_conjBy (b3 5 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt6_val11, Rt6_val5]
    exact iff_of_conjBy b2 x

theorem actsAs_rot {root : ℤ → Subgroup G} {r₁ r₂ : G} (h₁ : ActsAs root r₁ (fun q => 6 - q))
    (h₂ : ActsAs root r₂ (fun q => 4 - q)) (k : ℕ) :
    ActsAs root ((r₁ * r₂) ^ k) (fun q => q + 2 * (k : ℤ)) := by
  induction k with
  | zero =>
    simpa using (ActsAs.one : ActsAs root (1 : G) (fun q => q))
  | succ k ih =>
    rw [pow_succ]
    refine (ih.mul (h₁.mul h₂)).congr (fun q => ?_)
    push_cast
    ring


theorem Rt6_of_lt {q : ℤ} (h0 : 0 ≤ q) (h1 : q ≤ 5) : Rt 6 q = q + 1 :=
  Rt_of_lt h0 (by push_cast; omega)

theorem Rt6_of_ge {q : ℤ} (h0 : 6 ≤ q) (h1 : q ≤ 11) : Rt 6 q = -(q - 5) := by
  rw [Rt_of_ge (by push_cast; omega) (by push_cast; omega)]
  push_cast
  ring

theorem Rt6_isRoot (q : ℤ) : IsRoot 6 (Rt 6 q) := Rt_isRoot (by norm_num) q

theorem exists_mem_normalizer_of_lt [Finite G] {p : ℕ} [Fact p.Prime] {V V' : Subgroup G}
    (hV' : IsPGroup p V') (hlt : V < V') : ∃ x ∈ V', x ∈ normalizer (V : Set G) ∧ x ∉ V := by
  have hnil : Group.IsNilpotent V' := IsPGroup.isNilpotent hV'
  have hc : NormalizerCondition V' := Group.normalizerCondition_of_isNilpotent
  have hlt' : V.subgroupOf V' < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro h
    have : V' ≤ V := by
      intro x hx
      have := (Subgroup.mem_top (⟨x, hx⟩ : V'))
      rw [← h] at this
      exact this
    exact absurd hlt (not_lt_of_ge this)
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt (hc _ hlt')
  refine ⟨x, x.2, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ V'
    · have := (mem_normalizer_iff.1 hx) ⟨g, hg⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hgV
        exact absurd (hlt.le hgV) hg
      · intro h
        have := hlt.le h
        have h2 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x ∈ V' :=
          V'.mul_mem (V'.mul_mem (V'.inv_mem x.2) this) x.2
        have e : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x = g := by group
        rw [e] at h2
        exact absurd h2 hg
  · exact fun h => hxn (by simpa [Subgroup.mem_subgroupOf] using h)

theorem normalizer_inv_of_inv {H V : Subgroup G} (hV : ∀ h ∈ H, ∀ z ∈ V, h * z * h⁻¹ ∈ V) {h : G}
    (hh : h ∈ H) {y : G} (hy : y ∈ normalizer (V : Set G)) :
    h * y * h⁻¹ ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff] at hy ⊢
  intro g
  have e1 := inv_iff_of_inv hV hh (y * (h⁻¹ * g * h) * y⁻¹)
  have e2 := inv_iff_of_inv hV hh g
  have e3 := inv_iff_of_inv hV (H.inv_mem hh) g
  have e : h * (y * (h⁻¹ * g * h) * y⁻¹) * h⁻¹ = h * y * h⁻¹ * g * (h * y * h⁻¹)⁻¹ := by group
  rw [e] at e1
  rw [← e1, ← hy (h⁻¹ * g * h)]
  simpa using e3

theorem card_mul_le [Finite G] (S T : Set G) : Nat.card ↥(S * T) ≤ Nat.card S * Nat.card T := by
  have : Finite S := Set.toFinite S
  have : Finite T := Set.toFinite T
  let f : S × T → ↥(S * T) := fun st => ⟨st.1 * st.2, Set.mul_mem_mul st.1.2 st.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(S * T) ≤ Nat.card (S × T) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card S * Nat.card T := Nat.card_prod S T

theorem card_chainProd_le [Finite G] (A : ℤ → Subgroup G) :
    ∀ l : List ℤ, Nat.card (chainProd A l) ≤ (l.map fun k => Nat.card (A k)).prod
  | [] => by simp [chainProd]
  | k :: l => by
    have h1 := card_chainProd_le A l
    have h2 := card_mul_le (A k : Set G) (chainProd A l)
    simp only [chainProd_cons, List.map_cons, List.prod_cons]
    exact h2.trans (Nat.mul_le_mul le_rfl h1)

theorem prod_mem_chainProd (A : ℤ → Subgroup G) (f : ℤ → G) :
    ∀ l : List ℤ, (∀ k ∈ l, f k ∈ A k) → (l.map f).prod ∈ chainProd A l
  | [], _ => by simp [chainProd]
  | k :: l, h => by
    simp only [chainProd_cons, List.map_cons, List.prod_cons]
    exact Set.mul_mem_mul (h k (by simp)) (prod_mem_chainProd A f l (fun m hm => h m (by simp [hm])))

theorem unique_of_card [Finite G] (A : ℤ → Subgroup G) : ∀ (l : List ℤ),
    Nat.card (chainProd A l) = (l.map fun k => Nat.card (A k)).prod →
    ∀ f g : ℤ → G, (∀ k ∈ l, f k ∈ A k) → (∀ k ∈ l, g k ∈ A k) →
      (l.map f).prod = (l.map g).prod → ∀ k ∈ l, f k = g k
  | [] => by
    intro _ f g _ _ _ k hk
    simp at hk
  | k :: l => by
    intro hcard f g hf hg hprod m hm
    have hT := card_chainProd_le A l
    have hS : Nat.card ↥((A k : Set G) * chainProd A l) ≤ Nat.card (A k) * Nat.card (chainProd A l) :=
      card_mul_le (A k : Set G) (chainProd A l)
    simp only [chainProd_cons, List.map_cons, List.prod_cons] at hcard
    have hAk : 0 < Nat.card (A k) := Nat.card_pos
    have hTeq : Nat.card (chainProd A l) = (l.map fun k => Nat.card (A k)).prod := by
      by_contra hne
      have hlt := lt_of_le_of_ne hT hne
      have := Nat.mul_lt_mul_of_pos_left hlt hAk
      omega
    have hSeq : Nat.card ↥((A k : Set G) * chainProd A l) =
        Nat.card (A k) * Nat.card (chainProd A l) := by rw [hcard, hTeq]
    have : Finite (A k) := Set.toFinite _
    have : Finite (chainProd A l) := Set.toFinite _
    let φ : (A k) × (chainProd A l) → ↥((A k : Set G) * chainProd A l) :=
      fun st => ⟨st.1 * st.2, Set.mul_mem_mul st.1.2 st.2.2⟩
    have hφs : Function.Surjective φ := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    have hφb : Function.Bijective φ :=
      hφs.bijective_of_nat_card_le (by rw [Nat.card_prod, hSeq])
    have hf' : ∀ k' ∈ l, f k' ∈ A k' := fun k' hk' => hf k' (by simp [hk'])
    have hg' : ∀ k' ∈ l, g k' ∈ A k' := fun k' hk' => hg k' (by simp [hk'])
    have hpf := prod_mem_chainProd A f l hf'
    have hpg := prod_mem_chainProd A g l hg'
    have heq : φ (⟨f k, hf k (by simp)⟩, ⟨(l.map f).prod, hpf⟩) =
        φ (⟨g k, hg k (by simp)⟩, ⟨(l.map g).prod, hpg⟩) := by
      apply Subtype.ext
      simp only [List.map_cons, List.prod_cons] at hprod
      exact hprod
    have hpair := hφb.1 heq
    have hfk : f k = g k := by
      have := congrArg (fun st => (st.1 : G)) hpair
      simpa using this
    have hlp : (l.map f).prod = (l.map g).prod := by
      have := congrArg (fun st => (st.2 : G)) hpair
      simpa using this
    rcases List.mem_cons.1 hm with rfl | hml
    · exact hfk
    · exact unique_of_card A l hTeq f g hf' hg' hlp m hml

namespace Cor97

variable {p : ℕ} {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G} {root : ℤ → Subgroup G}
  (D : Cor97 p H r₁ r₂ U root)

include D in
theorem actsAs₁ : ActsAs root r₁ (fun q => 6 - q) := actsAs_r₁ D.act₁

include D in
theorem actsAs₂ : ActsAs root r₂ (fun q => 4 - q) := actsAs_r₂ D.act₂

include D in
theorem root_le_U {k : ℤ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) : root k ≤ U := by
  rw [D.U_gen]
  exact le_iSup₂_of_le k ⟨hk1, hk6⟩ le_rfl

include D in
theorem pos_mod_le_five {q : ℤ} (hq : ∀ x ∈ root (Rt 6 q), x ∈ U) : q % 12 ≤ 5 := by
  by_contra hcon
  have hcon' : 6 ≤ q % 12 := by omega
  have h0 := Int.emod_nonneg q (by norm_num : (12 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos q (by norm_num : (0 : ℤ) < 12)
  have hw := actsAs_rot D.actsAs₁ D.actsAs₂ 3
  have hbot : root (Rt 6 q) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ root (Rt 6 (q % 12)) := by rwa [← Rt6_emod]
    have e : (r₁ * r₂) ^ 3 * (((r₁ * r₂) ^ 3)⁻¹ * y * (r₁ * r₂) ^ 3) * ((r₁ * r₂) ^ 3)⁻¹ = y := by
      group
    have hx : ((r₁ * r₂) ^ 3)⁻¹ * y * (r₁ * r₂) ^ 3 ∈ root (Rt 6 (q % 12 - 6)) := by
      rw [hw (q % 12 - 6), e]
      have : q % 12 - 6 + 2 * ((3 : ℕ) : ℤ) = q % 12 := by push_cast; ring
      show y ∈ root (Rt 6 (q % 12 - 6 + 2 * ((3 : ℕ) : ℤ)))
      rw [this]
      exact hy'
    have hxU : ((r₁ * r₂) ^ 3)⁻¹ * y * (r₁ * r₂) ^ 3 ∈ U := by
      refine D.root_le_U (k := Rt 6 (q % 12 - 6)) ?_ ?_ hx
      · rw [Rt6_of_lt (by omega) (by omega)]; omega
      · rw [Rt6_of_lt (by omega) (by omega)]; omega
    have hxc : ((r₁ * r₂) ^ 3)⁻¹ * y * (r₁ * r₂) ^ 3 ∈ conjBy ((r₁ * r₂) ^ 3) U := by
      rw [mem_conjBy_iff, e]
      exact hq y hy
    have hx1 : ((r₁ * r₂) ^ 3)⁻¹ * y * (r₁ * r₂) ^ 3 = 1 := by
      have : ((r₁ * r₂) ^ 3)⁻¹ * y * (r₁ * r₂) ^ 3 ∈ U ⊓ conjBy ((r₁ * r₂) ^ 3) U := ⟨hxU, hxc⟩
      rw [D.opp] at this
      exact this
    have : y = 1 := by
      rw [hx1] at e
      simpa using e.symm
    simp [this]
  exact D.ne_bot _ (Rt6_isRoot q) hbot


include D in
theorem exists_window (c : ℕ) : ∃ u : G,
    (∀ j : ℤ, 0 ≤ j → j ≤ 5 → ∀ x ∈ root (Rt 6 (c + j)), u⁻¹ * x * u ∈ U) ∧
    (∀ m : ℤ, (∀ x ∈ root (Rt 6 m), u⁻¹ * x * u ∈ U) →
      ∃ j : ℤ, 0 ≤ j ∧ j ≤ 5 ∧ (m - c - j) % 12 = 0) := by
  have hrU : ∀ q : ℤ, 0 ≤ q → q ≤ 5 → root (Rt 6 q) ≤ U := fun q h0 h1 =>
    D.root_le_U (by rw [Rt6_of_lt h0 h1]; omega) (by rw [Rt6_of_lt h0 h1]; omega)
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' c
  ·
    have hr := actsAs_rot D.actsAs₁ D.actsAs₂ k
    refine ⟨(r₁ * r₂) ^ k, ?_, ?_⟩
    · intro j hj0 hj5 x hx
      have hy : ((r₁ * r₂) ^ k)⁻¹ * x * (r₁ * r₂) ^ k ∈ root (Rt 6 j) := by
        rw [hr j]
        have e : (r₁ * r₂) ^ k * (((r₁ * r₂) ^ k)⁻¹ * x * (r₁ * r₂) ^ k) * ((r₁ * r₂) ^ k)⁻¹ = x := by
          group
        rw [e]
        have : j + 2 * (k : ℤ) = (c : ℤ) + j := by rw [hk]; push_cast; ring
        show x ∈ root (Rt 6 (j + 2 * (k : ℤ)))
        rw [this]
        exact hx
      exact hrU j hj0 hj5 hy
    · intro m hm
      have hq : ∀ y ∈ root (Rt 6 (m - 2 * (k : ℤ))), y ∈ U := by
        intro y hy
        have hx : (r₁ * r₂) ^ k * y * ((r₁ * r₂) ^ k)⁻¹ ∈ root (Rt 6 m) := by
          have := (hr (m - 2 * (k : ℤ)) y).1 hy
          have e : m - 2 * (k : ℤ) + 2 * (k : ℤ) = m := by ring
          simpa only [e] using this
        have := hm _ hx
        simpa [mul_assoc] using this
      have h5 := D.pos_mod_le_five hq
      have h0 := Int.emod_nonneg (m - 2 * (k : ℤ)) (by norm_num : (12 : ℤ) ≠ 0)
      refine ⟨(m - 2 * (k : ℤ)) % 12, h0, h5, ?_⟩
      rw [hk]
      push_cast
      omega
  ·
    have hr := (actsAs_rot D.actsAs₁ D.actsAs₂ k).mul D.actsAs₁
    refine ⟨(r₁ * r₂) ^ k * r₁, ?_, ?_⟩
    · intro j hj0 hj5 x hx
      have hy : ((r₁ * r₂) ^ k * r₁)⁻¹ * x * ((r₁ * r₂) ^ k * r₁) ∈ root (Rt 6 (5 - j)) := by
        rw [hr (5 - j)]
        have e : ((r₁ * r₂) ^ k * r₁) * (((r₁ * r₂) ^ k * r₁)⁻¹ * x * ((r₁ * r₂) ^ k * r₁)) *
            ((r₁ * r₂) ^ k * r₁)⁻¹ = x := by
          group
        rw [e]
        have : (6 - (5 - j)) + 2 * (k : ℤ) = (c : ℤ) + j := by rw [hk]; push_cast; ring
        show x ∈ root (Rt 6 ((6 - (5 - j)) + 2 * (k : ℤ)))
        rw [this]
        exact hx
      exact hrU (5 - j) (by omega) (by omega) hy
    · intro m hm
      have hq : ∀ y ∈ root (Rt 6 (6 + 2 * (k : ℤ) - m)), y ∈ U := by
        intro y hy
        have hx : ((r₁ * r₂) ^ k * r₁) * y * ((r₁ * r₂) ^ k * r₁)⁻¹ ∈ root (Rt 6 m) := by
          have := (hr (6 + 2 * (k : ℤ) - m) y).1 hy
          have e : (6 - (6 + 2 * (k : ℤ) - m)) + 2 * (k : ℤ) = m := by ring
          simpa only [e] using this
        have := hm _ hx
        simpa [mul_assoc] using this
      have h5 := D.pos_mod_le_five hq
      have h0 := Int.emod_nonneg (6 + 2 * (k : ℤ) - m) (by norm_num : (12 : ℤ) ≠ 0)
      refine ⟨5 - (6 + 2 * (k : ℤ) - m) % 12, by omega, by omega, ?_⟩
      rw [hk]
      push_cast
      omega


@[expose] def Zij (root : ℤ → Subgroup G) (i j : ℤ) : Subgroup G := ⨆ k ∈ Set.Icc i j, root k

theorem le_Zij {root : ℤ → Subgroup G} {i j k : ℤ} (hk : i ≤ k ∧ k ≤ j) :
    root k ≤ Zij root i j :=
  le_iSup₂_of_le k hk le_rfl

theorem Rt6_add12 (q : ℤ) : Rt 6 (q + 12) = Rt 6 q := by
  have := Rt_add_mul 6 q 1
  simpa using this

include D in
theorem Zij_le_U {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 6) : Zij root i j ≤ U :=
  iSup₂_le fun k hk => D.root_le_U (by have := hk.1; omega) (by have := hk.2; omega)

include D in
theorem Zij_inv {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 6) :
    ∀ h ∈ H, ∀ z ∈ Zij root i j, h * z * h⁻¹ ∈ Zij root i j := by
  intro h hh z hz
  have : Zij root i j ≤ (Zij root i j).comap (MulAut.conj h).toMonoidHom := by
    refine iSup₂_le fun k hk x hx => ?_
    rw [Subgroup.mem_comap]
    have hk' : IsRoot 6 k := ⟨by have := hk.1; omega, by have := hk.1; have := hk.2; omega⟩
    exact le_Zij hk (D.invariant k hk' h hh x hx)
  have h2 := this hz
  rw [Subgroup.mem_comap] at h2
  simpa [MulAut.conj_apply] using h2

theorem Zij_conj_mem {i j : ℤ} {u : G}
    (h : ∀ k : ℤ, i ≤ k → k ≤ j → ∀ x ∈ root k, u⁻¹ * x * u ∈ U) :
    ∀ z ∈ Zij root i j, u⁻¹ * z * u ∈ U := by
  have : Zij root i j ≤ U.comap (MulAut.conj u⁻¹).toMonoidHom := by
    refine iSup₂_le fun k hk x hx => ?_
    rw [Subgroup.mem_comap]
    simpa [MulAut.conj_apply] using h k hk.1 hk.2 x hx
  intro z hz
  have h2 := this hz
  rw [Subgroup.mem_comap] at h2
  simpa [MulAut.conj_apply] using h2

include D in
theorem root_le_Zij_iff {i j k : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 6) (hk : IsRoot 6 k) :
    root k ≤ Zij root i j ↔ i ≤ k ∧ k ≤ j := by
  refine ⟨fun hle => ?_, fun h => le_Zij h⟩
  have hk0 := hk.1
  have hk6 : k.natAbs ≤ 6 := hk.2
  obtain ⟨uA, hA1, hA2⟩ := D.exists_window (j + 6).toNat
  obtain ⟨uB, hB1, hB2⟩ := D.exists_window (i - 1).toNat
  have hgenA : ∀ l : ℤ, i ≤ l → l ≤ j → ∀ x ∈ root l, uA⁻¹ * x * uA ∈ U := by
    intro l hl1 hl2 x hx
    have := hA1 (l - j + 5) (by omega) (by omega) x
    refine this ?_
    have e : (((j + 6).toNat : ℕ) : ℤ) + (l - j + 5) = (l - 1) + 12 := by omega
    rw [e, Rt6_add12, Rt6_of_lt (by omega) (by omega)]
    have : l - 1 + 1 = l := by ring
    rw [this]
    exact hx
  have hgenB : ∀ l : ℤ, i ≤ l → l ≤ j → ∀ x ∈ root l, uB⁻¹ * x * uB ∈ U := by
    intro l hl1 hl2 x hx
    have := hB1 (l - i) (by omega) (by omega) x
    refine this ?_
    have e : (((i - 1).toNat : ℕ) : ℤ) + (l - i) = l - 1 := by omega
    rw [e, Rt6_of_lt (by omega) (by omega)]
    have : l - 1 + 1 = l := by ring
    rw [this]
    exact hx
  have hZA := Zij_conj_mem hgenA
  have hZB := Zij_conj_mem hgenB
  obtain ⟨P, hP, hPk⟩ : ∃ P : ℤ, Rt 6 P = k ∧ (0 < k → P = k - 1) ∧ (k < 0 → P = 5 - k) := by
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · refine ⟨5 - k, ?_, fun h => by omega, fun _ => rfl⟩
      rw [Rt6_of_ge (by omega) (by omega)]
      ring
    · refine ⟨k - 1, ?_, fun _ => rfl, fun h => by omega⟩
      rw [Rt6_of_lt (by omega) (by omega)]
      ring
  obtain ⟨j₁, hj₁0, hj₁5, hj₁⟩ := hA2 P (fun x hx => hZA _ (hle (hP ▸ hx)))
  obtain ⟨j₂, hj₂0, hj₂5, hj₂⟩ := hB2 P (fun x hx => hZB _ (hle (hP ▸ hx)))
  have hPk' := hPk.1
  have hPk'' := hPk.2
  have hk' : -6 ≤ k ∧ k ≤ 6 := by omega
  have e1 : (((j + 6).toNat : ℕ) : ℤ) = j + 6 := by omega
  have e2 : (((i - 1).toNat : ℕ) : ℤ) = i - 1 := by omega
  rw [e1] at hj₁
  rw [e2] at hj₂
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · have := hPk'' hneg
    omega
  · have := hPk' hpos
    omega


theorem nodup_intList (i j : ℤ) : (intList i j).Nodup := by
  unfold intList
  refine (List.nodup_range).map (fun a b h => ?_)
  have : (a : ℤ) = b := by simpa using h
  exact_mod_cast this

include D in
theorem Zij_eq_chainProd {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 6) (l : List ℤ)
    (hl : l.Nodup) (hlm : ∀ k, k ∈ l ↔ i ≤ k ∧ k ≤ j) :
    (Zij root i j : Set G) = chainProd root l ∧
      Nat.card (Zij root i j) = (l.map fun k => Nat.card (root k)).prod := by
  refine D.L92 _ (D.Zij_le_U hi hj) (D.Zij_inv hi hj) l hl ?_
  intro k
  rw [hlm k]
  constructor
  · intro h
    exact ⟨⟨by omega, by omega⟩, le_Zij h⟩
  · rintro ⟨hk, hle⟩
    exact (D.root_le_Zij_iff hi hij hj hk).1 hle

include D in
theorem Zij_one_six : Zij root 1 6 = U := D.U_gen.symm


include D in
theorem root_le_normalizer [Finite G] {i j i' j' k : ℤ} (hi' : 1 ≤ i') (hii' : i' ≤ i)
    (hij : i ≤ j) (hjj' : j ≤ j') (hj' : j' ≤ 6) (hk : IsRoot 6 k) (hkV' : i' ≤ k ∧ k ≤ j')
    (hkV : ¬ (i ≤ k ∧ k ≤ j)) (hrest : ∀ l, i' ≤ l → l ≤ j' → l ≠ k → i ≤ l ∧ l ≤ j) :
    root k ≤ normalizer (Zij root i j : Set G) := by
  have hi : 1 ≤ i := le_trans hi' hii'
  have hj : j ≤ 6 := le_trans hjj' hj'
  have hij' : i' ≤ j' := le_trans hii' (le_trans hij hjj')
  have hVV' : Zij root i j ≤ Zij root i' j' :=
    iSup₂_le fun l hl => le_Zij ⟨le_trans hii' hl.1, le_trans hl.2 hjj'⟩
  have hp' : IsPGroup p (Zij root i' j') := D.U_pGroup.to_le (D.Zij_le_U hi' hj')
  have : Fact p.Prime := ⟨D.prime⟩
  have hlt : Zij root i j < Zij root i' j' := by
    refine lt_of_le_of_ne hVV' ?_
    intro heq
    apply hkV
    have h1 : root k ≤ Zij root i' j' := le_Zij hkV'
    rw [← heq] at h1
    exact (D.root_le_Zij_iff hi hij hj hk).1 h1
  obtain ⟨x₀, hx₀V', hx₀n, hx₀V⟩ := exists_mem_normalizer_of_lt hp' hlt
  by_cases hkN : root k ≤ normalizer (Zij root i j : Set G) ⊓ Zij root i' j'
  · exact hkN.trans inf_le_left
  · exfalso
    have hVinv := D.Zij_inv hi hj
    have hV'inv := D.Zij_inv hi' hj'
    have hNinv : ∀ h ∈ H, ∀ z ∈ normalizer (Zij root i j : Set G) ⊓ Zij root i' j',
        h * z * h⁻¹ ∈ normalizer (Zij root i j : Set G) ⊓ Zij root i' j' :=
      fun h hh z hz => ⟨normalizer_inv_of_inv hVinv hh hz.1, hV'inv h hh z hz.2⟩
    have hNp : IsPGroup p ↥(normalizer (Zij root i j : Set G) ⊓ Zij root i' j') :=
      hp'.to_le inf_le_right
    have hNroots : ∀ l, l ∈ intList i j ↔ IsRoot 6 l ∧
        root l ≤ normalizer (Zij root i j : Set G) ⊓ Zij root i' j' := by
      intro l
      rw [mem_intList_iff]
      constructor
      · intro hl
        refine ⟨⟨by omega, by omega⟩, le_inf ((le_Zij hl).trans (Subgroup.le_normalizer)) ?_⟩
        exact (le_Zij hl).trans hVV'
      · rintro ⟨hl, hle⟩
        have h1 := (D.root_le_Zij_iff hi' hij' hj' hl).1 (hle.trans inf_le_right)
        by_cases hlk : l = k
        · exact absurd (hlk ▸ hle) hkN
        · exact hrest l h1.1 h1.2 hlk
    have hN := D.L92 _ (inf_le_right.trans (D.Zij_le_U hi' hj')) hNinv (intList i j)
      (nodup_intList i j) hNroots
    have hV := (D.Zij_eq_chainProd hi hij hj (intList i j) (nodup_intList i j)
      (fun l => mem_intList_iff)).1
    have hx : x₀ ∈ normalizer (Zij root i j : Set G) ⊓ Zij root i' j' := ⟨hx₀n, hx₀V'⟩
    have hx2 : x₀ ∈ (Zij root i j : Set G) := by
      rw [hV, ← hN.1]
      exact hx
    exact hx₀V hx2


include D in
theorem subgroup_aux [Finite G] (i j : ℤ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 6) :
    ∃ V : Subgroup G, (V : Set G) = chainProd root (intList i j) ∧ V ≤ U ∧
      (1 < i → ∀ x ∈ root (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < 6 → ∀ x ∈ root (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) := by
  refine ⟨Zij root i j,
    (D.Zij_eq_chainProd hi hij hj _ (nodup_intList i j) (fun l => mem_intList_iff)).1,
    D.Zij_le_U hi hj, ?_, ?_⟩
  · intro hi1 x hx v hv
    have hnorm : root (i - 1) ≤ normalizer (Zij root i j : Set G) :=
      D.root_le_normalizer (i := i) (j := j) (i' := i - 1) (j' := j) (k := i - 1) (by omega)
        (by omega) hij le_rfl hj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        (by intro l h1 h2 h3; omega)
    exact (mem_normalizer_iff.1 (hnorm hx) v).1 hv
  · intro hj1 x hx v hv
    have hnorm : root (j + 1) ≤ normalizer (Zij root i j : Set G) :=
      D.root_le_normalizer (i := i) (j := j) (i' := i) (j' := j + 1) (k := j + 1) hi le_rfl hij
        (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        (by intro l h1 h2 h3; omega)
    exact (mem_normalizer_iff.1 (hnorm hx) v).1 hv

include D in
theorem reverse_eq_aux (i j : ℤ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 6) :
    chainProd root (intList i j) = chainProd root (intList i j).reverse := by
  have h1 := (D.Zij_eq_chainProd hi hij hj (intList i j) (nodup_intList i j)
    (fun l => mem_intList_iff)).1
  have h2 := (D.Zij_eq_chainProd hi hij hj (intList i j).reverse
    (List.nodup_reverse.2 (nodup_intList i j))
    (fun l => by rw [List.mem_reverse]; exact mem_intList_iff)).1
  rw [← h1, ← h2]

include D in
theorem U_inv : ∀ h ∈ H, ∀ z ∈ U, h * z * h⁻¹ ∈ U := by
  rw [← D.Zij_one_six]
  exact D.Zij_inv le_rfl le_rfl

include D in
theorem H_le_normalizer_U : H ≤ normalizer (U : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  exact fun u => inv_iff_of_inv D.U_inv hh u

include D in
theorem coe_sup_HU : ((H ⊔ U : Subgroup G) : Set G) = (H : Set G) * (U : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right H U D.H_le_normalizer_U

include D in
theorem eq_one_of_pow_eq_one {h : G} (hh : h ∈ H) {k : ℕ} (hk : h ^ (p ^ k) = 1) : h = 1 := by
  have : Fact p.Prime := ⟨D.prime⟩
  have h1 : orderOf h ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨a, ha, hord⟩ := (Nat.dvd_prime_pow D.prime).1 h1
  by_cases ha0 : a = 0
  · rw [ha0, pow_zero] at hord
    exact orderOf_eq_one_iff.1 hord
  · exact absurd (hord ▸ dvd_pow_self p ha0) (D.H_pPrime h hh)

include D in
theorem U_inf_H : U ⊓ H = ⊥ := by
  have : Fact p.Prime := ⟨D.prime⟩
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxH⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 D.U_pGroup ⟨x, hxU⟩
  have : x ^ (p ^ k) = 1 := by
    have h2 : orderOf x = p ^ k := by simpa using hk
    rw [← h2]
    exact pow_orderOf_eq_one x
  exact D.eq_one_of_pow_eq_one hxH this

include D in
theorem mem_U_of_pow_eq_one {x : G} (hxB : x ∈ H ⊔ U) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x ∈ U := by
  have : Fact p.Prime := ⟨D.prime⟩
  rw [← SetLike.mem_coe, D.coe_sup_HU] at hxB
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hxB
  have key : ∀ m : ℕ, ∃ u' ∈ U, (h * u) ^ m = h ^ m * u' := by
    intro m
    induction m with
    | zero => exact ⟨1, U.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨u', hu', he⟩ := ih
      refine ⟨h⁻¹ * u' * h * u, ?_, ?_⟩
      · have h1 : h⁻¹ * u' * h⁻¹⁻¹ ∈ U := D.U_inv h⁻¹ (H.inv_mem hh) u' hu'
        simpa using U.mul_mem h1 hu
      · rw [pow_succ, he]
        group
  obtain ⟨u', hu', he⟩ := key (p ^ k)
  rw [hxk] at he
  have hhm : h ^ (p ^ k) = 1 := by
    have : h ^ (p ^ k) = u'⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      have h3 := he.symm
      rw [mul_eq_one_iff_eq_inv] at h3
      rw [h3]
      simp
    have hmemU : h ^ (p ^ k) ∈ U := by rw [this]; exact U.inv_mem hu'
    have hmemH : h ^ (p ^ k) ∈ H := H.pow_mem hh _
    have : h ^ (p ^ k) ∈ U ⊓ H := ⟨hmemU, hmemH⟩
    rw [D.U_inf_H] at this
    exact this
  have h1 : h = 1 := D.eq_one_of_pow_eq_one hh hhm
  subst h1
  simpa using hu

include D in
theorem meet_one_aux : ∀ x ∈ H ⊔ U, x ∈ conjBy ((r₁ * r₂) ^ 3) U → x = 1 := by
  intro x hxB hxc
  have : Fact p.Prime := ⟨D.prime⟩
  rw [mem_conjBy_iff] at hxc
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 D.U_pGroup ⟨_, hxc⟩
  have hk' : orderOf ((r₁ * r₂) ^ 3 * x * ((r₁ * r₂) ^ 3)⁻¹) = p ^ k := by simpa using hk
  have hxk : x ^ (p ^ k) = 1 := by
    have h2 : orderOf x = p ^ k := by
      rw [← hk']
      exact (orderOf_injective (MulAut.conj ((r₁ * r₂) ^ 3)).toMonoidHom
        (MulAut.conj ((r₁ * r₂) ^ 3)).injective x).symm
    rw [← h2]
    exact pow_orderOf_eq_one _
  have hxU : x ∈ U := D.mem_U_of_pow_eq_one hxB hxk
  have h2 : x ∈ U ⊓ conjBy ((r₁ * r₂) ^ 3) U := ⟨hxU, mem_conjBy_iff.2 hxc⟩
  rw [D.opp] at h2
  exact h2

include D in
theorem negGen_le_conj : negGen 6 root ≤ conjBy ((r₁ * r₂) ^ 3) U := by
  have hw := actsAs_rot D.actsAs₁ D.actsAs₂ 3
  refine iSup₂_le fun k hk x hx => ?_
  have hk1 : 1 ≤ k := hk.1
  have hk6 : k ≤ 6 := by have := hk.2; exact_mod_cast this
  rw [mem_conjBy_iff]
  have hx' : x ∈ root (Rt 6 (k + 5)) := by
    rw [Rt6_of_ge (by omega) (by omega)]
    have : -(k + 5 - 5) = -k := by ring
    rw [this]
    exact hx
  have h1 := (hw (k + 5) x).1 hx'
  have e : Rt 6 (k + 5 + 2 * ((3 : ℕ) : ℤ)) = k := by
    have : k + 5 + 2 * ((3 : ℕ) : ℤ) = (k - 1) + 12 := by push_cast; ring
    rw [this, Rt6_add12, Rt6_of_lt (by omega) (by omega)]
    ring
  have h2 : (r₁ * r₂) ^ 3 * x * ((r₁ * r₂) ^ 3)⁻¹ ∈ root k := by
    have := h1
    simp only [] at this
    rw [e] at this
    exact this
  exact D.root_le_U hk1 hk6 h2

include D in
theorem meet_one : ∀ x ∈ H ⊔ U, x ∈ negGen 6 root → x = 1 :=
  fun x hx hn => D.meet_one_aux x hx (D.negGen_le_conj hn)

include D in
theorem unique_aux [Finite G] :
    ∀ f g : ℤ → G, (∀ k ∈ intList 1 6, f k ∈ root k) → (∀ k ∈ intList 1 6, g k ∈ root k) →
      ((intList 1 6).map f).prod = ((intList 1 6).map g).prod → ∀ k ∈ intList 1 6, f k = g k := by
  have h := D.Zij_eq_chainProd (i := 1) (j := 6) le_rfl (by norm_num) le_rfl (intList 1 6)
    (nodup_intList 1 6) (fun l => mem_intList_iff)
  rw [D.Zij_one_six] at h
  apply unique_of_card root (intList 1 6)
  rw [← h.2]
  rw [← h.1]
  rfl


include D in
theorem phi₁ : SL2Phi H r₁ (root 1) (root (-1)) :=
  D.sl2₁.toSL2Phi (D.invariant 1 ⟨by norm_num, by norm_num⟩)
    (D.invariant (-1) ⟨by norm_num, by norm_num⟩)

include D in
theorem phi₆ : SL2Phi H r₂ (root 6) (root (-6)) :=
  D.sl2₆.toSL2Phi (D.invariant 6 ⟨by norm_num, by norm_num⟩)
    (D.invariant (-6) ⟨by norm_num, by norm_num⟩)

include D in
theorem bruhat₁_aux : ∀ y ∈ root (-1), y ≠ 1 →
    y ∈ (root 1 : Set G) * (H : Set G) * {r₁} * (root 1 : Set G) :=
  D.phi₁.bruhat D.conj_H₁

include D in
theorem bruhat₂_aux : ∀ y ∈ root (-6), y ≠ 1 →
    y ∈ (root 6 : Set G) * (H : Set G) * {r₂} * (root 6 : Set G) :=
  D.phi₆.bruhat D.conj_H₂

include D in
theorem carrier_eq_aux [Finite G] : (U : Set G) = chainProd root (intList 1 6) := by
  have h := D.Zij_eq_chainProd (i := 1) (j := 6) le_rfl (by norm_num) le_rfl (intList 1 6)
    (nodup_intList 1 6) (fun l => mem_intList_iff)
  rw [D.Zij_one_six] at h
  exact h.1

include D in
theorem toRGD2 [Finite G] : RGD2 6 H r₁ r₂ U root where
  three_le := by norm_num
  comm_H := D.comm_H
  nilpotent := by
    have : Fact p.Prime := ⟨D.prime⟩
    exact IsPGroup.isNilpotent D.U_pGroup
  conj_H₁ := D.conj_H₁
  conj_H₂ := D.conj_H₂
  sq₁ := D.sq₁
  sq₂ := D.sq₂
  pow := D.pow
  U_inf_H := D.U_inf_H
  ne_bot := D.ne_bot
  invariant := D.invariant
  carrier_eq := D.carrier_eq_aux
  unique := D.unique_aux
  reverse_eq := fun i j hi hij hj => D.reverse_eq_aux i j hi hij (by exact_mod_cast hj)
  subgroup := fun i j hi hij hj => D.subgroup_aux i j hi hij (by exact_mod_cast hj)
  act₁ := by
    obtain ⟨a1, a2, a3⟩ := D.act₁
    refine ⟨a1, a2, fun i h1 h2 => ?_⟩
    have := a3 i h1 (by exact_mod_cast h2)
    have e : ((6 : ℕ) : ℤ) + 2 - i = 8 - i := by push_cast; ring
    rw [e]
    exact this
  act₂ := by
    obtain ⟨b1, b2, b3⟩ := D.act₂
    refine ⟨b1, b2, fun i h1 h2 => ?_⟩
    have := b3 i h1 (by omega)
    have e : ((6 : ℕ) : ℤ) - i = 6 - i := by push_cast; ring
    rw [e]
    exact this
  meet_one := D.meet_one
  rank₁ := D.bruhat₁_aux
  rank₂ := D.bruhat₂_aux


include D in
theorem conj_inv_H₁ {h : G} (hh : h ∈ H) : r₁⁻¹ * h * r₁ ∈ H := by
  have hsq : r₁⁻¹ * r₁⁻¹ ∈ H := by
    have := H.inv_mem D.sq₁
    simpa [mul_inv_rev] using this
  have h1 := H.mul_mem (H.mul_mem hsq (D.conj_H₁ h hh)) D.sq₁
  have e : r₁⁻¹ * r₁⁻¹ * (r₁ * h * r₁⁻¹) * (r₁ * r₁) = r₁⁻¹ * h * r₁ := by group
  rwa [e] at h1

include D in
theorem conj_inv_H₂ {h : G} (hh : h ∈ H) : r₂⁻¹ * h * r₂ ∈ H := by
  have hsq : r₂⁻¹ * r₂⁻¹ ∈ H := by
    have := H.inv_mem D.sq₂
    simpa [mul_inv_rev] using this
  have h1 := H.mul_mem (H.mul_mem hsq (D.conj_H₂ h hh)) D.sq₂
  have e : r₂⁻¹ * r₂⁻¹ * (r₂ * h * r₂⁻¹) * (r₂ * r₂) = r₂⁻¹ * h * r₂ := by group
  rwa [e] at h1

include D in
theorem sl2At₁ : SL2At H (Subgroup.closure ((H : Set G) ∪ {r₁, r₂})) root 1 :=
  D.phi₁.toSL2At (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
    (fun _ hh => Subgroup.subset_closure (Or.inl hh))

include D in
theorem sl2At₄ : SL2At H (Subgroup.closure ((H : Set G) ∪ {r₁, r₂})) root 4 := by
  obtain ⟨F, hF, hFin, hc, φ, hinj, hU, hL, hD, h, hh, hW⟩ := D.phi₆
  have hn := actsAs_rot D.actsAs₁ D.actsAs₂ 1
  have hx4 : ∀ x, x ∈ root 4 ↔ (r₁ * r₂) * x * (r₁ * r₂)⁻¹ ∈ root 6 := by
    intro x
    have := hn 3 x
    simpa [Rt6_val3, Rt6_val5, pow_one] using this
  have hx4' : ∀ x, x ∈ root (-4) ↔ (r₁ * r₂) * x * (r₁ * r₂)⁻¹ ∈ root (-6) := by
    intro x
    have := hn 9 x
    have e : (9 : ℤ) + 2 * ((1 : ℕ) : ℤ) = 11 := by norm_num
    simpa [Rt6_val9, Rt6_val11, pow_one, e] using this
  have hNr₁ : r₁ ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hNr₂ : r₂ ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) :=
    Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hNn : r₁ * r₂ ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) := Subgroup.mul_mem _ hNr₁ hNr₂
  have hHN : H ≤ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) := fun _ hh =>
    Subgroup.subset_closure (Or.inl hh)
  have hcard : Nat.card F = Nat.card (root 4) := by
    have hmap : (root 4).map (MulAut.conj (r₁ * r₂)).toMonoidHom = root 6 := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hx4 x).1 hx
      · intro hz
        refine ⟨(r₁ * r₂)⁻¹ * z * (r₁ * r₂), (hx4 _).2 (by simpa [mul_assoc] using hz), ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    have : Nat.card ((root 4).map (MulAut.conj (r₁ * r₂)).toMonoidHom) = Nat.card (root 4) :=
      Subgroup.card_map_of_injective (MulAut.conj (r₁ * r₂)).injective
    rw [hmap] at this
    rw [hc, this]
  refine ⟨F, hF, hFin, hcard,
    (MulAut.conj (r₁ * r₂)⁻¹).toMonoidHom.comp φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj (r₁ * r₂)⁻¹).injective.comp hinj
  · intro x
    rw [hx4]
    constructor
    · intro hx
      obtain ⟨c, hcx⟩ := (hU _).1 hx
      refine ⟨c, ?_⟩
      simp [hcx, mul_assoc]
    · rintro ⟨c, hcx⟩
      apply (hU _).2
      refine ⟨c, ?_⟩
      have : (r₁ * r₂)⁻¹ * φ (sl2U c) * (r₁ * r₂) = x := by
        simpa [MulAut.conj_apply, mul_assoc] using hcx
      rw [← this]
      simp [mul_assoc]
  · intro x
    rw [hx4']
    constructor
    · intro hx
      obtain ⟨c, hcx⟩ := (hL _).1 hx
      refine ⟨c, ?_⟩
      simp [hcx, mul_assoc]
    · rintro ⟨c, hcx⟩
      apply (hL _).2
      refine ⟨c, ?_⟩
      have : (r₁ * r₂)⁻¹ * φ (sl2L c) * (r₁ * r₂) = x := by
        simpa [MulAut.conj_apply, mul_assoc] using hcx
      rw [← this]
      simp [mul_assoc]
  · intro t
    rw [MonoidHom.comp_apply]
    show (r₁ * r₂)⁻¹ * φ (sl2D t) * ((r₁ * r₂)⁻¹)⁻¹ ∈ H
    rw [inv_inv]
    have h1 := D.conj_inv_H₁ (hD t)
    have h2 := D.conj_inv_H₂ h1
    simpa [mul_assoc] using h2
  · rw [MonoidHom.comp_apply]
    show (r₁ * r₂)⁻¹ * φ (sl2W F) * ((r₁ * r₂)⁻¹)⁻¹ ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂})
    rw [inv_inv, hW]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hNn) (Subgroup.mul_mem _ hNr₂
      (hHN hh))) hNn

end Cor97

end CFSG.GH74.GLS.Stage4
