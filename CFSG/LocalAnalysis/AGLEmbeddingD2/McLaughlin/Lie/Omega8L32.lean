module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.LeviThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8Cover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8ParabolicSplit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.GL32

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

theorem posRoot_supp_cases {γ : Fin 4 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanD 4) ∅) {x : Fin 4} (hx : x ≠ 1)
    (hsupp : ∀ k, k ≠ 1 → k ≠ x → γ k = 0) (hpos : 0 < ht γ) :
    γ = Pi.single 1 1 ∨ γ = Pi.single x 1 ∨ γ = Pi.single 1 1 + Pi.single x 1 := by
  have hht : 0 < γ 0 + γ 1 + γ 2 + γ 3 := by
    simpa [ht, Fin.sum_univ_four] using hpos
  rw [rootsD_eq (n := 4) (by norm_num)] at hγ
  obtain ⟨i, j, s, t, hij, hs, ht', h⟩ := hγ
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  simp only [toStdD] at e0 e1 e2 e3
  norm_num at e0 e1 e2 e3
  have hfun : ∀ a b c d : ℤ, γ 0 = a → γ 1 = b → γ 2 = c → γ 3 = d →
      γ = fun k => ![a, b, c, d] k := fun a b c d h0 h1 h2 h3 => funext fun k => by
    fin_cases k <;> simp [h0, h1, h2, h3]
  clear h
  fin_cases x
  · have h2 := hsupp 2 (by decide) (by decide)
    have h3 := hsupp 3 (by decide) (by decide)
    have key : (γ 0 = 0 ∧ γ 1 = 1) ∨ (γ 0 = 1 ∧ γ 1 = 0) ∨ (γ 0 = 1 ∧ γ 1 = 1) := by
      fin_cases i <;> fin_cases j <;> simp at e0 e1 e2 e3 hij ⊢ <;>
        rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl <;> omega
    rcases key with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [hfun _ _ _ _ a b h2 h3]; funext k; fin_cases k <;> rfl
    · right; left; rw [hfun _ _ _ _ a b h2 h3]; funext k; fin_cases k <;> rfl
    · right; right; rw [hfun _ _ _ _ a b h2 h3]; funext k; fin_cases k <;> rfl
  · exact absurd rfl hx
  · have h0 := hsupp 0 (by decide) (by decide)
    have h3 := hsupp 3 (by decide) (by decide)
    have key : (γ 1 = 1 ∧ γ 2 = 0) ∨ (γ 1 = 0 ∧ γ 2 = 1) ∨ (γ 1 = 1 ∧ γ 2 = 1) := by
      fin_cases i <;> fin_cases j <;> simp at e0 e1 e2 e3 hij ⊢ <;>
        rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl <;> omega
    rcases key with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [hfun _ _ _ _ h0 a b h3]; funext k; fin_cases k <;> rfl
    · right; left; rw [hfun _ _ _ _ h0 a b h3]; funext k; fin_cases k <;> rfl
    · right; right; rw [hfun _ _ _ _ h0 a b h3]; funext k; fin_cases k <;> rfl
  · have h0 := hsupp 0 (by decide) (by decide)
    have h2 := hsupp 2 (by decide) (by decide)
    have key : (γ 1 = 1 ∧ γ 3 = 0) ∨ (γ 1 = 0 ∧ γ 3 = 1) ∨ (γ 1 = 1 ∧ γ 3 = 1) := by
      fin_cases i <;> fin_cases j <;> simp at e0 e1 e2 e3 hij ⊢ <;>
        rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl <;> omega
    rcases key with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [hfun _ _ _ _ h0 a h2 b]; funext k; fin_cases k <;> rfl
    · right; left; rw [hfun _ _ _ _ h0 a h2 b]; funext k; fin_cases k <;> rfl
    · right; right; rw [hfun _ _ _ _ h0 a h2 b]; funext k; fin_cases k <;> rfl

structure LeafData (x : Fin 4) where
  L : LeviFrame
  p : Fin 4
  q : Fin 4
  hpq : (p = 1 ∧ q = x) ∨ (p = x ∧ q = 1)
  h01 : toStdD 4 (Pi.single p 1) =
    Pi.single (L.ι 0) (boolSign (L.σ 0)) + Pi.single (L.ι 1) (boolSign (!L.σ 1))
  h10 : toStdD 4 (-Pi.single p 1) =
    Pi.single (L.ι 1) (boolSign (L.σ 1)) + Pi.single (L.ι 0) (boolSign (!L.σ 0))
  h12 : toStdD 4 (Pi.single q 1) =
    Pi.single (L.ι 1) (boolSign (L.σ 1)) + Pi.single (L.ι 2) (boolSign (!L.σ 2))
  h21 : toStdD 4 (-Pi.single q 1) =
    Pi.single (L.ι 2) (boolSign (L.σ 2)) + Pi.single (L.ι 1) (boolSign (!L.σ 1))
  h02 : toStdD 4 (Pi.single p 1 + Pi.single q 1) =
    Pi.single (L.ι 0) (boolSign (L.σ 0)) + Pi.single (L.ι 2) (boolSign (!L.σ 2))

@[expose] def leafData0 : LeafData 0 where
  L := ⟨![0, 1, 2], ![true, true, true], 3, by decide, by decide, by decide⟩
  p := 0
  q := 1
  hpq := Or.inr ⟨rfl, rfl⟩
  h01 := by decide
  h10 := by decide
  h12 := by decide
  h21 := by decide
  h02 := by decide

@[expose] def leafData2 : LeafData 2 where
  L := ⟨![1, 2, 3], ![true, true, true], 0, by decide, by decide, by decide⟩
  p := 1
  q := 2
  hpq := Or.inl ⟨rfl, rfl⟩
  h01 := by decide
  h10 := by decide
  h12 := by decide
  h21 := by decide
  h02 := by decide

@[expose] def leafData3 : LeafData 3 where
  L := ⟨![1, 2, 3], ![true, true, false], 0, by decide, by decide, by decide⟩
  p := 1
  q := 3
  hpq := Or.inl ⟨rfl, rfl⟩
  h01 := by decide
  h10 := by decide
  h12 := by decide
  h21 := by decide
  h02 := by decide

theorem nonempty_leafData {x : Fin 4} (hx : x ≠ 1) : Nonempty (LeafData x) := by
  fin_cases x
  · exact ⟨leafData0⟩
  · exact absurd rfl hx
  · exact ⟨leafData2⟩
  · exact ⟨leafData3⟩

section Leaf

variable {F : Type} [Field F]

theorem LeviFrame.rootGroup_eq_range (L : LeviFrame) {k l : Fin 3} (hkl : k ≠ l)
    {γ : Fin 4 → ℤ} (h : toStdD 4 γ =
      Pi.single (L.ι k) (boolSign (L.σ k)) + Pi.single (L.ι l) (boolSign (!L.σ l))) :
    (plusDatum 4 F three_le_four).rootGroup γ =
      ((frame4 F).longRoot (L.inj.ne hkl) (L.σ k) (!L.σ l)).range :=
  plusRootGroup_eq three_le_four (L.inj.ne hkl) _ _ h

theorem LeviFrame.range_le_levi (L : LeviFrame) {k l : Fin 3} (hkl : k ≠ l) :
    ((frame4 F).longRoot (L.inj.ne hkl) (L.σ k) (!L.σ l)).range ≤ L.levi F := by
  rintro _ ⟨a, rfl⟩
  exact L.y_mem_levi hkl (Multiplicative.toAdd a)

theorem LeviFrame.y_mem_range (L : LeviFrame) {k l : Fin 3} (hkl : k ≠ l) (c : F) :
    L.y hkl c ∈ ((frame4 F).longRoot (L.inj.ne hkl) (L.σ k) (!L.σ l)).range :=
  ⟨Multiplicative.ofAdd c, rfl⟩

variable {x : Fin 4} (d : LeafData x)

theorem LeafData.rankOne_p_le :
    rankOne (plusDatum 4 F three_le_four).rootGroup d.p ≤ d.L.levi F :=
  sup_le ((d.L.rootGroup_eq_range (by decide : (0 : Fin 3) ≠ 1) d.h01).le.trans
      (d.L.range_le_levi (by decide : (0 : Fin 3) ≠ 1)))
    ((d.L.rootGroup_eq_range (by decide : (1 : Fin 3) ≠ 0) d.h10).le.trans
      (d.L.range_le_levi (by decide : (1 : Fin 3) ≠ 0)))

theorem LeafData.rankOne_q_le :
    rankOne (plusDatum 4 F three_le_four).rootGroup d.q ≤ d.L.levi F :=
  sup_le ((d.L.rootGroup_eq_range (by decide : (1 : Fin 3) ≠ 2) d.h12).le.trans
      (d.L.range_le_levi (by decide : (1 : Fin 3) ≠ 2)))
    ((d.L.rootGroup_eq_range (by decide : (2 : Fin 3) ≠ 1) d.h21).le.trans
      (d.L.range_le_levi (by decide : (2 : Fin 3) ≠ 1)))

theorem LeafData.levi_le :
    d.L.levi F ≤ rankOne (plusDatum 4 F three_le_four).rootGroup d.p ⊔
      rankOne (plusDatum 4 F three_le_four).rootGroup d.q := by
  set Λ := rankOne (plusDatum 4 F three_le_four).rootGroup d.p ⊔
    rankOne (plusDatum 4 F three_le_four).rootGroup d.q with hΛ
  have m01 : ∀ c : F, d.L.y (by decide : (0 : Fin 3) ≠ 1) c ∈ Λ := fun c =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left
      ((d.L.rootGroup_eq_range (by decide : (0 : Fin 3) ≠ 1) d.h01).ge (d.L.y_mem_range _ c)))
  have m10 : ∀ c : F, d.L.y (by decide : (1 : Fin 3) ≠ 0) c ∈ Λ := fun c =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right
      ((d.L.rootGroup_eq_range (by decide : (1 : Fin 3) ≠ 0) d.h10).ge (d.L.y_mem_range _ c)))
  have m12 : ∀ c : F, d.L.y (by decide : (1 : Fin 3) ≠ 2) c ∈ Λ := fun c =>
    Subgroup.mem_sup_right (Subgroup.mem_sup_left
      ((d.L.rootGroup_eq_range (by decide : (1 : Fin 3) ≠ 2) d.h12).ge (d.L.y_mem_range _ c)))
  have m21 : ∀ c : F, d.L.y (by decide : (2 : Fin 3) ≠ 1) c ∈ Λ := fun c =>
    Subgroup.mem_sup_right (Subgroup.mem_sup_right
      ((d.L.rootGroup_eq_range (by decide : (2 : Fin 3) ≠ 1) d.h21).ge (d.L.y_mem_range _ c)))
  have hcomm : ∀ a ∈ Λ, ∀ b ∈ Λ, ⁅a, b⁆ ∈ Λ := fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have m02 : ∀ c : F, d.L.y (by decide : (0 : Fin 3) ≠ 2) c ∈ Λ := fun c => by
    have h := d.L.y_eq_commutator (k := 0) (l := 1) (m := 2) (by decide) (by decide) (by decide)
      c 1
    rw [mul_one] at h
    rw [h]
    exact hcomm _ (m01 c) _ (m12 1)
  have m20 : ∀ c : F, d.L.y (by decide : (2 : Fin 3) ≠ 0) c ∈ Λ := fun c => by
    have h := d.L.y_eq_commutator (k := 2) (l := 1) (m := 0) (by decide) (by decide) (by decide)
      c 1
    rw [mul_one] at h
    rw [h]
    exact hcomm _ (m21 c) _ (m10 1)
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨k, l, hkl, c, rfl⟩
  fin_cases k <;> fin_cases l
  · exact absurd rfl hkl
  · exact m01 c
  · exact m02 c
  · exact m10 c
  · exact absurd rfl hkl
  · exact m12 c
  · exact m20 c
  · exact m21 c
  · exact absurd rfl hkl

theorem LeafData.levi_eq :
    d.L.levi F = rankOne (plusDatum 4 F three_le_four).rootGroup (1 : Fin 4) ⊔
      rankOne (plusDatum 4 F three_le_four).rootGroup x := by
  have h := le_antisymm (d.levi_le (F := F)) (sup_le d.rankOne_p_le d.rankOne_q_le)
  rcases d.hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [h, hp, hq]
  · rw [h, hp, hq, sup_comm]

theorem LeafData.rootGroup_add_le :
    (plusDatum 4 F three_le_four).rootGroup (Pi.single (1 : Fin 4) 1 + Pi.single x 1) ≤
      d.L.levi F := by
  have h := (d.L.rootGroup_eq_range (F := F) (by decide : (0 : Fin 3) ≠ 2) d.h02).le.trans
    (d.L.range_le_levi (by decide : (0 : Fin 3) ≠ 2))
  rcases d.hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq] at h
    exact h
  · rw [hp, hq, add_comm] at h
    exact h

end Leaf

theorem d4_clique_cases (I : Set (Fin 4)) (h : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → cartanD 4 i j ≠ 0) :
    (∃ k, I ⊆ {k}) ∨ ∃ x : Fin 4, x ≠ 1 ∧ (1 : Fin 4) ∈ I ∧ x ∈ I ∧ I ⊆ {1, x} := by
  have h02 : ¬ ((0 : Fin 4) ∈ I ∧ (2 : Fin 4) ∈ I) := fun hh =>
    h 0 hh.1 2 hh.2 (by decide) (cartanD_four_leaves (by decide) (by decide) (by decide))
  have h03 : ¬ ((0 : Fin 4) ∈ I ∧ (3 : Fin 4) ∈ I) := fun hh =>
    h 0 hh.1 3 hh.2 (by decide) (cartanD_four_leaves (by decide) (by decide) (by decide))
  have h23 : ¬ ((2 : Fin 4) ∈ I ∧ (3 : Fin 4) ∈ I) := fun hh =>
    h 2 hh.1 3 hh.2 (by decide) (cartanD_four_leaves (by decide) (by decide) (by decide))
  clear h
  by_cases h1 : (1 : Fin 4) ∈ I
  · by_cases h0 : (0 : Fin 4) ∈ I
    · exact Or.inr ⟨0, by decide, h1, h0, fun k hk => by fin_cases k <;> simp_all⟩
    by_cases h2 : (2 : Fin 4) ∈ I
    · exact Or.inr ⟨2, by decide, h1, h2, fun k hk => by fin_cases k <;> simp_all⟩
    by_cases h3 : (3 : Fin 4) ∈ I
    · exact Or.inr ⟨3, by decide, h1, h3, fun k hk => by fin_cases k <;> simp_all⟩
    exact Or.inl ⟨1, fun k hk => by fin_cases k <;> simp_all⟩
  · by_cases h0 : (0 : Fin 4) ∈ I
    · exact Or.inl ⟨0, fun k hk => by fin_cases k <;> simp_all⟩
    by_cases h2 : (2 : Fin 4) ∈ I
    · exact Or.inl ⟨2, fun k hk => by fin_cases k <;> simp_all⟩
    exact Or.inl ⟨3, fun k hk => by fin_cases k <;> simp_all⟩

section Small

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_card_nine {L₁ L₂ : Subgroup G} (h₁ : Nat.card L₁ = 6)
    (hnc₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {c₁ c₂ : G} (hc₁ : c₁ ∈ L₁) (hc₂ : c₂ ∈ L₂) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1) (h1' : c₁ ^ 3 = 1)
    (h2' : c₂ ^ 3 = 1) :
    ∃ E : Subgroup G, E ≤ L₁ ⊔ L₂ ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : ∀ c : G, c ≠ 1 → c ^ 3 = 1 → Nat.card (Subgroup.zpowers c) = 3 := fun c hc hc3 => by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc]
  have hZ₁ : Subgroup.zpowers c₁ ≤ L₁ := (Subgroup.zpowers_le).mpr hc₁
  have hZ₂ : Subgroup.zpowers c₂ ≤ L₂ := (Subgroup.zpowers_le).mpr hc₂
  have c12 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_commute (A := Subgroup.zpowers c₁) (B := Subgroup.zpowers c₂)
      fun a ha b hb => h12 a (hZ₁ ha) b (hZ₂ hb))
  have hi12 : Subgroup.zpowers c₁ ⊓ Subgroup.zpowers c₂ = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf hZ₁ hZ₂).trans (inf_eq_bot_of_commutes_of_card_six h₁ hnc₁ h12).le)
  rw [hi12, Subgroup.card_bot, mul_one, hz _ h1 h1', hz _ h2 h2'] at c12
  refine ⟨Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂, sup_le_sup hZ₁ hZ₂, ?_, by rw [c12]⟩
  have hcl : Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ = Subgroup.closure {c₁, c₂} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  rw [hcl]
  refine isElemAbelian_three_closure_of_pairwise ?_ ?_
  · have k12 : Commute c₁ c₂ := h12 _ hc₁ _ hc₂
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> assumption

omit [Finite G] in
theorem eq_bot_of_perfect_of_isSolvable' {B : Subgroup G} (hB : ⁅B, B⁆ = B)
    [Group.IsSolvable B] : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

theorem eq_bot_of_perfect_of_card_dvd {J : Subgroup G} (hJ : ⁅J, J⁆ = J) {m : ℕ}
    (hd : Nat.card J ∣ 3 * 2 ^ m) : J = ⊥ := by
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp hd
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show y ∣ 3 ^ 1 by rw [pow_one]; exact hy)
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hz
  have := Fintype.ofFinite J
  have : Group.IsSolvable J :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_three
      Nat.prime_two (by norm_num) (by rw [← Nat.card_eq_fintype_card, hyz])
  exact eq_bot_of_perfect_of_isSolvable' hJ

end Small

section Quotient

variable {K : Type} [Group K] [Finite K]

theorem isLThreeTwo_quot_pCore_of_levi {A Λ U : Subgroup K} (hΛA : Λ ≤ A) (hUA : U ≤ A)
    (hA : A ≤ Λ ⊔ U) (hΛU : Λ ≤ Subgroup.normalizer (U : Set K)) (hU2 : IsPGroup 2 U)
    (hΛ : IsLThreeTwo ↥Λ) : IsLThreeTwo (↥A ⧸ CFSG.pCore 2 ↥A) := by
  have hsimple := isLThreeTwo_simple hΛ
  have h3 := isLThreeTwo_three_dvd_card hΛ
  have hnorm : (U.subgroupOf Λ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hΛU g.2) n).mp hn
    simpa using this⟩
  have hΛU' : Λ ⊓ U = ⊥ := by
    have := hnorm
    rcases hsimple.eq_bot_or_eq_top_of_normal (U.subgroupOf Λ) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_iff.mp h.symm
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hU2.to_le h)
      rw [hk] at h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have hAU : A ≤ Subgroup.normalizer (U : Set K) := hA.trans (sup_le hΛU Subgroup.le_normalizer)
  have hU'n : (U.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUA).mpr hAU
  set ψ₀ : ↥Λ →* ↥A ⧸ U.subgroupOf A :=
    (QuotientGroup.mk' (U.subgroupOf A)).comp (Subgroup.inclusion hΛA) with hψ₀
  have hinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    rw [hψ₀, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hl
    have hl' : (l : K) ∈ Λ ⊓ U := ⟨l.2, hl⟩
    rw [hΛU', Subgroup.mem_bot] at hl'
    exact Subtype.ext hl'
  have hsurj : Function.Surjective ψ₀ := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf A) q
    have ha : (a : K) ∈ ((Λ ⊔ U : Subgroup K) : Set K) := hA a.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Λ U hΛU] at ha
    obtain ⟨l, hl, u, hu, he⟩ := ha
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hψ₀, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hΛA ⟨l, hl⟩)⁻¹ * a : ↥A) = (u : K) := by
      simp [← he]
    rw [this]
    exact hu
  set e := MulEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩ with he
  set ψ : ↥A →* ↥Λ := e.symm.toMonoidHom.comp (QuotientGroup.mk' (U.subgroupOf A)) with hψ
  have hψs : Function.Surjective ψ :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective (U.subgroupOf A))
  refine isLThreeTwo_quot_pCore_of_surj hΛ ψ hψs fun y hy => ?_
  have hy' : y ∈ U.subgroupOf A := by
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    exact hy
  obtain ⟨k, hk⟩ := hU2 ⟨y, hy'⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

end Quotient

section SpinL32

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem spin_L32_core (hF : Nat.card F = 2) (hGL : IsLThreeTwo (GL (Fin 3) F))
    {A : Subgroup (spinGroup (quadPlus 4 F))}
    (hBA : borel (plusDatum 4 F three_le_four) (fun k => (torusD F three_le_four k).range) ≤ A)
    (h9 : ∀ E : Subgroup (spinGroup (quadPlus 4 F)), E ≤ A → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E ≠ 9)
    (hJ : ∃ J : Subgroup (spinGroup (quadPlus 4 F)), J ≤ A ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J) :
    IsLThreeTwo (↥A ⧸ CFSG.pCore 2 ↥A) := by
  have := finite_spinFour (F := F)
  have hct := spinFour_ct (F := F)
  have hext := spinFour_extras (F := F)
  have hH := torusD_range_eq_bot hF
  have hU2 := posUnipotent_spinFour_isPGroup (F := F)
  have hfacts := rankOne_spin_facts hF
  have hAeq := eq_borel_sup_rankOne hct hext hBA
  set D := plusDatum 4 F three_le_four with hD
  set B := borel D (fun k => (torusD F three_le_four k).range) with hB
  have hLA : ∀ i ∈ negIndices D A, rankOne D.rootGroup i ≤ A := fun i hi =>
    rankOne_le_of_mem_negIndices hBA hi
  have hAS : ∀ S : Set (Fin D.rank), negIndices D A ⊆ S →
      A ≤ B ⊔ ⨆ k ∈ S, rankOne D.rootGroup k :=
    fun S hS => hAeq.le.trans (sup_le_sup_left (biSup_mono fun k hk => hS hk) _)
  have hadj : ∀ i ∈ negIndices D A, ∀ j ∈ negIndices D A, i ≠ j → cartanD 4 i j ≠ 0 := by
    intro i hi j hj hij hA
    obtain ⟨ci, hci, hci1, hci3⟩ := (hfacts i).2.2
    obtain ⟨cj, hcj, hcj1, hcj3⟩ := (hfacts j).2.2
    obtain ⟨E, hE, hEel, hE9⟩ := exists_elemAbelian_card_nine (hfacts i).1 (hfacts i).2.1
      (commutes_rankOne_of_cartan_eq_zero hext hij hA) hci hcj hci1 hcj1 hci3 hcj3
    exact h9 E (hE.trans (sup_le (hLA i hi) (hLA j hj))) hEel hE9
  obtain ⟨J, hJA, hJp, hJ3⟩ := hJ
  rcases d4_clique_cases (negIndices D A) hadj with ⟨k, hk⟩ | ⟨x, hx1, h1, hx, hsub⟩
  ·
    exfalso
    have hAk : A ≤ B ⊔ rankOne D.rootGroup k :=
      (hAS {k} hk).trans (sup_le_sup_left iSup_singleton.le _)
    have hcard := card_borel_sup_rankOne_of hct hext hH hU2 k (hfacts k).1 (hfacts k).2.1
    have hBU : B ≤ posUnipotent D := sup_le (iSup_le fun j => (hH j).le.trans bot_le) le_rfl
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hU2.to_le hBU)
    have hdvd : Nat.card J ∣ 3 * 2 ^ m := by
      rw [← hm, ← hcard]
      exact Subgroup.card_dvd_of_le (hJA.trans hAk)
    have hJ1 := eq_bot_of_perfect_of_card_dvd hJp hdvd
    rw [hJ1, Subgroup.card_bot] at hJ3
    omega
  ·
    obtain ⟨d⟩ := nonempty_leafData hx1
    have hΛeq := d.levi_eq (F := F)
    have hΛA : d.L.levi F ≤ A := hΛeq ▸ sup_le (hLA (1 : Fin 4) h1) (hLA x hx)
    have hUA : (⨆ k ∈ ({(1 : Fin 4), x} : Set (Fin D.rank))ᶜ, radical D k) ≤ A :=
      ((iSup₂_le fun j _ => radical_le_posUnipotent j).trans posUnipotent_le_borel).trans hBA
    have hroots : ∀ γ ∈ D.roots, 0 < ht γ →
        (∀ j ∉ ({(1 : Fin 4), x} : Set (Fin D.rank)), γ j = 0) → D.rootGroup γ ≤ d.L.levi F := by
      intro γ hγ hpos hvan
      have hsupp : ∀ k : Fin 4, k ≠ 1 → k ≠ x → γ k = 0 := fun k hk1 hkx =>
        hvan k fun hm =>
          (Set.mem_insert_iff.mp hm).elim hk1 fun e => hkx (Set.mem_singleton_iff.mp e)
      rcases posRoot_supp_cases hγ hx1 hsupp hpos with rfl | rfl | rfl
      · exact (le_sup_left : D.rootGroup (Pi.single (1 : Fin 4) 1) ≤
          rankOne D.rootGroup (1 : Fin 4)).trans (hΛeq ▸ le_sup_left)
      · exact (le_sup_left : D.rootGroup (Pi.single x 1) ≤ rankOne D.rootGroup x).trans
          (hΛeq ▸ le_sup_right)
      · exact d.rootGroup_add_le
    have hBΛU := borel_le_sup_radicals hH ({(1 : Fin 4), x} : Set (Fin D.rank)) (d.L.levi F) hroots
    have hAΛU : A ≤ d.L.levi F ⊔ ⨆ k ∈ ({(1 : Fin 4), x} : Set (Fin D.rank))ᶜ, radical D k := by
      refine (hAS {(1 : Fin 4), x} hsub).trans (sup_le hBΛU ?_)
      refine iSup_pair.le.trans ?_
      rw [← hΛeq]
      exact le_sup_left
    have hΛU : d.L.levi F ≤ Subgroup.normalizer
        ((⨆ k ∈ ({(1 : Fin 4), x} : Set (Fin D.rank))ᶜ, radical D k : Subgroup _) : Set _) := by
      rw [hΛeq]
      refine sup_le ?_ ?_
      · exact le_normalizer_sup_radicals _ fun j hj => rankOne_le_normalizer_radical hext
          fun h => hj (h ▸ Set.mem_insert _ _)
      · exact le_normalizer_sup_radicals _ fun j hj => rankOne_le_normalizer_radical hext
          fun h => hj (h ▸ Set.mem_insert_of_mem _ rfl)
    have hU2' := sup_radicals_isPGroup hU2 ({(1 : Fin 4), x} : Set (Fin D.rank))
    have := Fintype.ofFinite F
    have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hΛL : IsLThreeTwo ↥(d.L.levi F) := IsLThreeTwo.of_mulEquiv
      (MulEquiv.ofBijective (d.L.leviHom F) (d.L.leviHom_bijective hF' h2)).symm hGL
    exact isLThreeTwo_quot_pCore_of_levi hΛA hUA hAΛU hΛU hU2' hΛL

end SpinL32

end CFSG.AGLEmbeddingD2.McLaughlin.Lie

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem kFactOmega8ParabolicL32_of_GL (hGL2 : IsLThreeTwo (GL (Fin 3) (ZMod 2))) :
    KFactOmega8ParabolicL32 := by
  intro X _ _ Lb P hΩ hP hr hJ
  obtain ⟨hPL, T₀, hT₀, hN⟩ := hP
  obtain ⟨T, hT⟩ := Lie.exists_sylow_of_isSylowTwoOf hT₀
  have hT₀L : T₀ ≤ Lb := hT₀.1
  have hNJ : Subgroup.normalizer ((T : Subgroup ↥Lb) : Set ↥Lb) ≤ P.subgroupOf Lb := by
    intro y hy
    rw [hT, mem_normalizer_iff_map, Subgroup.map_subgroupOf_eq_of_le hT₀L] at hy
    exact Subgroup.mem_subgroupOf.mpr (hN ⟨y.2, hy⟩)
  obtain ⟨⟨-, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := Lie.statedClassicalModel_of_isOmegaEightPlus hΩ
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have := Lie.finite_spinFour (F := F)
  have hGL : IsLThreeTwo (GL (Fin 3) F) := by
    have hc : Fintype.card F = Fintype.card (ZMod 2) := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hF2]
    let φF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
    exact IsLThreeTwo.of_mulEquiv (Units.mapEquiv (RingEquiv.mapMatrix φF).toMulEquiv).symm hGL2
  have h := borelQuotient_spinPlus Lie.three_le_four e
  obtain ⟨π', hπ', hker, hTπ⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient (plusDatum 4 F Lie.three_le_four) (weylD F Lie.three_le_four)
      (fun k => (torusD F Lie.three_le_four k).range) π' (Nat.card F - 1) :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hTπ] at hNπ
  have hBP : (borel (plusDatum 4 F Lie.three_le_four)
      (fun k => (torusD F Lie.three_le_four k).range)).map π' ≤ P.subgroupOf Lb := hNπ ▸ hNJ
  have hinj : Function.Injective π' := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, eq_bot_iff]
    intro z hz
    have := h.ker_pow z hz
    rw [hF2] at this
    simpa using this
  set φ : ↥(spinGroup (quadPlus 4 F)) →* X := Lb.subtype.comp π' with hφ
  have hφinj : Function.Injective φ := Lb.subtype_injective.comp hinj
  have hrange : ∀ x ∈ Lb, ∃ k, φ k = x := fun x hx => by
    obtain ⟨k, hk⟩ := hπ' ⟨x, hx⟩
    exact ⟨k, by rw [hφ, MonoidHom.comp_apply, hk]; rfl⟩
  have hPr : P ≤ φ.range := fun x hx => by
    obtain ⟨k, hk⟩ := hrange x (hPL hx)
    exact ⟨k, hk⟩
  set A := P.comap φ with hA
  have hBA : borel (plusDatum 4 F Lie.three_le_four)
      (fun k => (torusD F Lie.three_le_four k).range) ≤ A := fun b hb =>
    Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mp (hBP ⟨b, hb, rfl⟩))
  have h9 : ∀ E : Subgroup ↥(spinGroup (quadPlus 4 F)), E ≤ A → IsElemAbelian 3 E →
      Nat.card E ≠ 9 := by
    intro E hEA hEel hE9
    have hel := elementary_map_injective 3 E φ hφinj hEel
    have hc : Nat.card (E.map φ) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective hφinj, hE9]
      norm_num
    have := CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.map_le_iff_le_comap.mpr hEA) hel hc
    omega
  have hJK : ∃ J : Subgroup ↥(spinGroup (quadPlus 4 F)), J ≤ A ∧ ⁅J, J⁆ = J ∧
      3 ∣ Nat.card J := by
    obtain ⟨J, hJP, hJp, hJ3⟩ := hJ
    have hJr : J ≤ φ.range := hJP.trans hPr
    have hmapJ : (J.comap φ).map φ = J := Subgroup.map_comap_eq_self hJr
    refine ⟨J.comap φ, Subgroup.comap_mono hJP, ?_, ?_⟩
    · apply Subgroup.map_injective hφinj
      rw [Subgroup.map_commutator, hmapJ, hJp]
    · have := (Subgroup.card_map_of_injective hφinj : Nat.card ((J.comap φ).map φ) = _)
      rw [hmapJ] at this
      rwa [← this]
  have hcore := Lie.spin_L32_core hF2 hGL hBA h9 hJK
  have hmapP : A.map φ = P := Subgroup.map_comap_eq_self hPr
  let eAP : ↥A ≃* ↥P := (A.equivMapOfInjective φ hφinj).trans (MulEquiv.subgroupCongr hmapP)
  refine ⟨P, le_rfl, ?_, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  · exact IsLThreeTwo.of_mulEquiv (QuotientGroup.congr _ _ eAP (CFSG.pCore_map_iso 2 eAP)) hcore

theorem kFactOmega8ParabolicL32_proved : KFactOmega8ParabolicL32 :=
  kFactOmega8ParabolicL32_of_GL Lie.isLThreeTwo_GL_three_two

end CFSG.AGLEmbeddingD2.McLaughlin
