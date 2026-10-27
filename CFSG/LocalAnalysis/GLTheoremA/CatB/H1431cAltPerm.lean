module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open Equiv Equiv.Perm

theorem altS_pow_eq_one_of_mem_closure {G : Type*} [Group G] {S : Set G} {p : ℕ}
    (hcomm : S.Pairwise Commute) (hS : ∀ s ∈ S, s ^ p = 1) {x : G}
    (hx : x ∈ Subgroup.closure S) : x ^ p = 1 := by
  have hc : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hcomm
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y :=
      congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem altS_isElemAbelian_closure {G : Type*} [Group G] {S : Set G} {p : ℕ}
    (hcomm : S.Pairwise Commute) (hS : ∀ s ∈ S, s ^ p = 1) :
    IsElemAbelian p (Subgroup.closure S) :=
  ⟨Subgroup.isMulCommutative_closure hcomm, fun _ hx =>
    altS_pow_eq_one_of_mem_closure hcomm hS hx⟩

theorem altS_isPGroup_closure {G : Type*} [Group G] {S : Set G} {p : ℕ}
    (hcomm : S.Pairwise Commute) (hS : ∀ s ∈ S, s ^ p = 1) : IsPGroup p (Subgroup.closure S) :=
  fun x => ⟨1, Subtype.ext (by
    simpa using altS_pow_eq_one_of_mem_closure hcomm hS x.2)⟩

theorem altS_mem_normalizer_closure {G : Type*} [Group G] [Finite G] {S : Set G} {x : G}
    (h : ∀ s ∈ S, x * s * x⁻¹ ∈ Subgroup.closure S) :
    x ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hn' : n ∈ Subgroup.closure S := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ iha ihb
  | inv a ha ih =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

theorem altS_closure_le_normalizer_closure {G : Type*} [Group G] [Finite G] {S T : Set G}
    (h : ∀ t ∈ T, ∀ s ∈ S, t * s * t⁻¹ ∈ Subgroup.closure S) :
    Subgroup.closure T ≤ Subgroup.normalizer (Subgroup.closure S : Set G) :=
  (Subgroup.closure_le _).2 fun t ht => altS_mem_normalizer_closure (h t ht)

private def kleinA : Perm (Fin 13) := swap 0 1 * swap 2 3

private def kleinB : Perm (Fin 13) := swap 0 2 * swap 1 3

private def cyc : Fin 4 → Perm (Fin 13) :=
  ![swap 0 1 * swap 1 2, swap 4 5 * swap 5 6, swap 7 8 * swap 8 9, swap 10 11 * swap 11 12]

private theorem sign_kleinA : sign kleinA = 1 := by decide

private theorem sign_kleinB : sign kleinB = 1 := by decide

private theorem sign_cyc : ∀ i : Fin 4, sign (cyc i) = 1 := by decide

private def gA : alternatingGroup (Fin 13) := ⟨kleinA, mem_alternatingGroup.2 sign_kleinA⟩

private def gB : alternatingGroup (Fin 13) := ⟨kleinB, mem_alternatingGroup.2 sign_kleinB⟩

private def gC (i : Fin 4) : alternatingGroup (Fin 13) :=
  ⟨cyc i, mem_alternatingGroup.2 (sign_cyc i)⟩

private theorem gA_ne_one : gA ≠ 1 := by decide

private theorem commute_gA_gB : Commute gA gB := Subtype.ext (by decide)

private theorem gA_sq : gA ^ 2 = 1 := Subtype.ext (by decide)

private theorem gB_sq : gB ^ 2 = 1 := Subtype.ext (by decide)

private theorem commute_gC : ∀ i j : Fin 4, Commute (gC i) (gC j) := fun i j =>
  Subtype.ext (by revert i j; decide)

private theorem gC_cube : ∀ i : Fin 4, gC i ^ 3 = 1 := fun i =>
  Subtype.ext (by revert i; decide)

private theorem conj_gA : ∀ i : Fin 4,
    gC i * gA * (gC i)⁻¹ = gA ∨ gC i * gA * (gC i)⁻¹ = gA * gB := fun i => by
  rcases (by revert i; decide : ∀ i : Fin 4, (cyc i * kleinA * (cyc i)⁻¹ = kleinA ∨
    cyc i * kleinA * (cyc i)⁻¹ = kleinA * kleinB)) i with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private theorem conj_gB : ∀ i : Fin 4,
    gC i * gB * (gC i)⁻¹ = gB ∨ gC i * gB * (gC i)⁻¹ = gA := fun i => by
  rcases (by revert i; decide : ∀ i : Fin 4, (cyc i * kleinB * (cyc i)⁻¹ = kleinB ∨
    cyc i * kleinB * (cyc i)⁻¹ = kleinA)) i with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private def prodC (a b c d : Fin 3) : alternatingGroup (Fin 13) :=
  gC 0 ^ a.val * gC 1 ^ b.val * gC 2 ^ c.val * gC 3 ^ d.val

private theorem prodC_apply : ∀ a b c d : Fin 3,
    (((prodC a b c d : alternatingGroup (Fin 13)) : Perm (Fin 13)) 0).val = a.val ∧
    (((prodC a b c d : alternatingGroup (Fin 13)) : Perm (Fin 13)) 4).val = 4 + b.val ∧
    (((prodC a b c d : alternatingGroup (Fin 13)) : Perm (Fin 13)) 7).val = 7 + c.val ∧
    (((prodC a b c d : alternatingGroup (Fin 13)) : Perm (Fin 13)) 10).val = 10 + d.val := by
  decide

theorem altS_exists_rank_four_config {Y : Type*} [Group Y] [Finite Y]
    (Ξ : alternatingGroup (Fin 13) →* Y) (hΞ : Function.Injective Ξ) :
    ∃ U E : Subgroup Y, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set Y) ∧
      IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E := by
  have key : ∀ g h : alternatingGroup (Fin 13), Ξ g * Ξ h * (Ξ g)⁻¹ = Ξ (g * h * g⁻¹) :=
    fun g h => by simp [map_mul, map_inv]
  have hU : ({Ξ gA, Ξ gB} : Set Y).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact commute_gA_gB.map Ξ
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (commute_gA_gB.map Ξ).symm
    · rw [Set.mem_singleton_iff] at hx hy
      subst hx
      subst hy
      exact absurd rfl hxy
  have hU2 : ∀ s ∈ ({Ξ gA, Ξ gB} : Set Y), s ^ 2 = 1 := by
    rintro s (rfl | hs)
    · rw [← map_pow, gA_sq, map_one]
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      rw [← map_pow, gB_sq, map_one]
  have hE : (Set.range fun i => Ξ (gC i)).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact (commute_gC i j).map Ξ
  have hE3 : ∀ s ∈ Set.range fun i => Ξ (gC i), s ^ 3 = 1 := by
    rintro _ ⟨i, rfl⟩
    rw [← map_pow, gC_cube, map_one]
  refine ⟨Subgroup.closure {Ξ gA, Ξ gB}, Subgroup.closure (Set.range fun i => Ξ (gC i)), ?_,
    altS_isPGroup_closure hU hU2, ?_,
    altS_isElemAbelian_closure hE hE3, ?_⟩
  · intro h
    have hmem : Ξ gA ∈ Subgroup.closure ({Ξ gA, Ξ gB} : Set Y) :=
      Subgroup.subset_closure (Or.inl rfl)
    rw [h, Subgroup.mem_bot] at hmem
    exact gA_ne_one (hΞ (hmem.trans (map_one Ξ).symm))
  · refine altS_closure_le_normalizer_closure ?_
    rintro _ ⟨i, rfl⟩ s hs
    have hgA : Ξ gA ∈ Subgroup.closure ({Ξ gA, Ξ gB} : Set Y) :=
      Subgroup.subset_closure (Or.inl rfl)
    have hgB : Ξ gB ∈ Subgroup.closure ({Ξ gA, Ξ gB} : Set Y) :=
      Subgroup.subset_closure (Or.inr rfl)
    rcases hs with rfl | hs
    · rw [key]
      rcases conj_gA i with h | h
      · rw [h]
        exact hgA
      · rw [h, map_mul]
        exact Subgroup.mul_mem _ hgA hgB
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      rw [key]
      rcases conj_gB i with h | h
      · rw [h]
        exact hgB
      · rw [h]
        exact hgA
  · set E := Subgroup.closure (Set.range fun i => Ξ (gC i)) with hEdef
    have hmem : ∀ i, Ξ (gC i) ∈ E := fun i => Subgroup.subset_closure ⟨i, rfl⟩
    have hprod : ∀ a b c d : Fin 3, Ξ (prodC a b c d) ∈ E := by
      intro a b c d
      simp only [prodC, map_mul, map_pow]
      exact E.mul_mem (E.mul_mem (E.mul_mem (E.pow_mem (hmem 0) _) (E.pow_mem (hmem 1) _))
        (E.pow_mem (hmem 2) _)) (E.pow_mem (hmem 3) _)
    let F : Fin 3 × Fin 3 × Fin 3 × Fin 3 → E := fun x =>
      ⟨Ξ (prodC x.1 x.2.1 x.2.2.1 x.2.2.2), hprod _ _ _ _⟩
    have hF : Function.Injective F := by
      intro x y hxy
      have h1 : prodC x.1 x.2.1 x.2.2.1 x.2.2.2 = prodC y.1 y.2.1 y.2.2.1 y.2.2.2 :=
        hΞ (congrArg Subtype.val hxy)
      have h2 : ((prodC x.1 x.2.1 x.2.2.1 x.2.2.2 : alternatingGroup (Fin 13)) : Perm (Fin 13)) =
          ((prodC y.1 y.2.1 y.2.2.1 y.2.2.2 : alternatingGroup (Fin 13)) : Perm (Fin 13)) :=
        congrArg Subtype.val h1
      obtain ⟨hx0, hx4, hx7, hx10⟩ := prodC_apply x.1 x.2.1 x.2.2.1 x.2.2.2
      obtain ⟨hy0, hy4, hy7, hy10⟩ := prodC_apply y.1 y.2.1 y.2.2.1 y.2.2.2
      rw [h2] at hx0 hx4 hx7 hx10
      refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))) <;>
        omega
    have hcard := Nat.card_le_card_of_injective F hF
    have h81 : Nat.card (Fin 3 × Fin 3 × Fin 3 × Fin 3) = 3 ^ 4 := by
      simp [Nat.card_prod]
    rwa [h81] at hcard

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
