module

public import CFSG.CGT.Foote81L6.Lemma11Main
public import CFSG.CGT.Foote81L6.Final
public import CFSG.CGT.Foote81L6.TheoremOneInputs
public import CFSG.CGT.Foote81L6.MainL6Bridge

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

@[expose] def FooteLemma3One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (D : FooteCore G T m n),
    ∀ x ∈ D.Zab, ∀ y ∈ D.Zab, IsConj x y → x = y ∨ (x = D.b₀ ∧ y = D.b₁) ∨
      (x = D.b₁ ∧ y = D.b₀) ∨ (x = D.a * D.b₀ ∧ y = D.a * D.b₁) ∨ (x = D.a * D.b₁ ∧ y = D.a * D.b₀)

@[expose] def FooteLemma3Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteCore G T 2 n),
    D.a ∈ center G → ∀ {a₁ : G}, a₁ ∈ D.A → a₁ ≠ 1 → a₁ ≠ D.a →
      ¬ IsConj a₁ (a₁ * D.b) ∧ ¬ IsConj a₁ (D.a * a₁ * D.b)

@[expose] def FooteLemma3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (D : FooteCore G T m n),
    ∀ y ∈ D.Zab, IsConj D.a y → y = D.a

@[expose] def FooteNotConjB₀B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (D : FooteCore G T m n),
    ¬ IsConj D.b₀ D.b

@[expose] def FooteLemma4OneLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (D : FooteCore G T m n), 4 ≤ n →
    ∀ g : G, g * D.a * g⁻¹ ∈ (T : Subgroup G) → g * D.a * g⁻¹ ∈ D.T₁

@[expose] def FooteLemma4OneFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteCore G T 2 n),
    ∀ g : G, g * D.a * g⁻¹ ∈ (T : Subgroup G) → g * D.a * g⁻¹ ∉ D.T₁ →
      ∃ y : G, y * D.a * y⁻¹ ∈ D.T₁ ∧ y * D.a * y⁻¹ ∉ D.A ∧ y * D.a * y⁻¹ ∉ D.Astar

@[expose] def FooteLemma4Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteCore G T 2 n),
    D.a ∈ center G → ∀ {a₁ : G}, a₁ ∈ D.A → a₁ ≠ 1 → a₁ ≠ D.a → ∀ g : G,
      g * a₁ * g⁻¹ ∈ (T : Subgroup G) → g * a₁ * g⁻¹ ∈ D.T₁

@[expose] def FooteLemma5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (_ : FooteCore G T m n),
    ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ g : G,
      E.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ (T : Subgroup G), E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom

@[expose] def FooteLemma5Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (_ : FooteCore G T m n),
    ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∃ Q : Sylow 2 ↥(normalizer (E : Set G)),
      (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (E : Set G))

@[expose] def FooteLemma8To10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteCore G T 2 n),
    ¬ StronglyInvolutionClosed D.A T → ¬ StronglyInvolutionClosed D.Astar T → D.NBarDichotomy

section Lemma3

variable {G : Type} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

private theorem a_mem_Zab : D.a ∈ D.Zab := subset_closure (Set.mem_insert _ _)

private theorem b₀_mem_Zab : D.b₀ ∈ D.Zab :=
  subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

private theorem b₁_mem_Zab : D.b₁ ∈ D.Zab :=
  subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

private theorem b_mem_Zab : D.b ∈ D.Zab := mul_mem (b₀_mem_Zab D) (b₁_mem_Zab D)

private theorem eq_one_of_mem_A_of_mem_B {x : G} (hxA : x ∈ D.A) (hxB : x ∈ D.B) : x = 1 := by
  have h : x ∈ D.A ⊓ D.B := mem_inf.2 ⟨hxA, hxB⟩
  rwa [D.A_inf_B, mem_bot] at h

private theorem a_ne_b₀ : D.a ≠ D.b₀ := fun h =>
  D.a_ne_one (eq_one_of_mem_A_of_mem_B D D.a_mem (h ▸ D.B₀_le_B D.b₀_mem))

private theorem a_ne_b₁ : D.a ≠ D.b₁ := fun h =>
  D.a_ne_one (eq_one_of_mem_A_of_mem_B D D.a_mem (h ▸ D.B₁_le_B D.b₁_mem))

private theorem ne_mul_self {x y : G} (hy : y ≠ 1) : x ≠ x * y := fun h =>
  hy (mul_left_cancel (h.symm.trans (mul_one x).symm))

end Lemma3

theorem footeLemma3_of_one (h : FooteLemma3One) : FooteLemma3 := by
  intro G _ _ T m n D y hy hc
  rcases h G T m n D _ (a_mem_Zab D) y hy hc with h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact h'.symm
  · exact absurd h' (a_ne_b₀ D)
  · exact absurd h' (a_ne_b₁ D)
  · exact absurd h' (ne_mul_self D.b₀_ne_one)
  · exact absurd h' (ne_mul_self D.b₁_ne_one)

theorem footeNotConjAB_of_one (h : FooteLemma3One) : FooteNotConjAB := by
  intro G _ _ T m n D hc
  rcases h G T m n D _ (a_mem_Zab D) _ (mul_mem (a_mem_Zab D) (b_mem_Zab D)) hc with
    h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact ne_mul_self D.b_ne_one h'
  · exact absurd h' (a_ne_b₀ D)
  · exact absurd h' (a_ne_b₁ D)
  · exact absurd h' (ne_mul_self D.b₀_ne_one)
  · exact absurd h' (ne_mul_self D.b₁_ne_one)

theorem footeNotConjB₀B_of_one (h : FooteLemma3One) : FooteNotConjB₀B := by
  intro G _ _ T m n D hc
  rcases h G T m n D _ (b₀_mem_Zab D) _ (b_mem_Zab D) hc with
    h' | ⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact ne_mul_self D.b₁_ne_one (show D.b₀ = D.b₀ * D.b₁ from h')
  · exact D.b₀_ne_one (mul_right_cancel (show D.b₀ * D.b₁ = 1 * D.b₁ from
      h'.trans (one_mul D.b₁).symm))
  · exact D.b₀_ne_b₁ h'
  · exact D.a_ne_one (mul_right_cancel (h'.symm.trans (one_mul D.b₀).symm))
  ·
    have ha : D.a = D.b₀ * D.b₁⁻¹ := by rw [h']; group
    exact D.a_ne_one (eq_one_of_mem_A_of_mem_B D D.a_mem (ha ▸ mul_mem (D.B₀_le_B D.b₀_mem)
      (inv_mem (D.B₁_le_B D.b₁_mem))))

theorem footeNotConjAAstar_of_two (h : FooteLemma3Two) : FooteNotConjAAstar := by
  intro G _ _ T n D hcen g hg
  have hlt : zpowers D.a < D.A := by
    refine lt_of_le_of_ne (zpowers_le.2 D.a_mem) fun h' => ?_
    have hcard := D.card_A
    rw [← h', Nat.card_zpowers, D.a_order] at hcard
    norm_num at hcard
  obtain ⟨a₁, ha₁, ha₁Z⟩ := SetLike.exists_of_lt hlt
  have ha₁1 : a₁ ≠ 1 := fun h' => ha₁Z (h' ▸ one_mem _)
  have ha₁a : a₁ ≠ D.a := fun h' => ha₁Z (h' ▸ mem_zpowers _)
  have hy : g * a₁ * g⁻¹ ∈ D.Astar := by
    rw [← hg]
    exact ⟨a₁, ha₁, by simp [MulAut.conj_apply]⟩
  have hga : g * D.a * g⁻¹ = D.a := by rw [mem_center_iff.1 hcen g, mul_inv_cancel_right]
  have hy1 : g * a₁ * g⁻¹ ≠ 1 := fun h' => ha₁1 (conj_eq_one_iff.1 h')
  have hya : g * a₁ * g⁻¹ ≠ D.a := fun h' => by
    rw [← hga] at h'
    exact ha₁a (mul_left_cancel (mul_right_cancel h'))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : orderOf (g * a₁ * g⁻¹) = 2 := by
    refine orderOf_eq_prime ?_ hy1
    calc (g * a₁ * g⁻¹) ^ 2 = g * (a₁ * a₁) * g⁻¹ := by rw [sq]; group
      _ = 1 := by rw [D.mul_self_of_two ha₁, mul_one, mul_inv_cancel]
  obtain ⟨x, hx, hx2, hxa, hxy⟩ := D.exists_of_involution_Astar hy hy2 hya
  rcases D.mem_A_of_two ha₁ ha₁1 ha₁a hx with rfl | rfl | rfl | rfl
  · rw [orderOf_one] at hx2
    exact absurd hx2 (by decide)
  · exact hxa rfl
  · exact (h G T n D hcen ha₁ ha₁1 ha₁a).1 (isConj_iff.2 ⟨g, hxy⟩)
  · exact (h G T n D hcen ha₁ ha₁1 ha₁a).2 (isConj_iff.2 ⟨g, hxy⟩)

section Inputs

variable (h3 : FooteLemma3) (h41 : FooteLemma4OneLarge) (h41w : FooteLemma4OneFour)
  (h42 : FooteLemma4Two) (h5 : FooteLemma5) (h5s : FooteLemma5Sylow) (h810 : FooteLemma8To10)

include h3 h41 h5 h5s in
theorem footeLemma6Key_of_inputs : FooteLemma6Key := by
  intro G _ _ T k n D hx
  exact D.lemma6Key_of (fun E => (D.typ E).1 = (D.typ E).2) (h3 G T (k + 3) n D)
    (h41 G T (k + 3) n D (by have := D.m_lt_n; omega)) (h5 G T (k + 3) n D)
    (h5s G T (k + 3) n D)
    (fun E hE x c hx hxN htv hmove => D.transvection_E64 hE hx hxN htv hmove)
    (fun E hE hsym => D.exists_s_normalizer hE hsym)
    (fun x hx hx2 => D.exists_symm_E64_of_mem hx hx2) hx

include h3 h41w h5 h5s h810 in
theorem footeLemma11_of_inputs : FooteLemma11 := by
  intro G _ _ T n D hnA hnAs
  exact D.lemma11_of (h3 G T 2 n D.toFooteCore) (h41w G T n D.toFooteCore)
    (h5 G T 2 n D.toFooteCore) (h5s G T 2 n D.toFooteCore)
    (h810 G T n D.toFooteCore hnA hnAs)

include h42 h5 h5s h810 in
theorem footeFinalHalf_of_inputs : FooteFinalHalf := by
  intro G _ _ T n D hcen hnA hnAs
  exact D.finalHalf_of hcen (h42 G T n D hcen) (h5 G T 2 n D) (h5s G T 2 n D)
    (h810 G T n D hnA hnAs) hnA

end Inputs

theorem footeTheorem1_of_inputs (h3 : FooteLemma3) (h3ab : FooteNotConjAB)
    (h3s : FooteNotConjAAstar) (h41 : FooteLemma4OneLarge) (h41w : FooteLemma4OneFour)
    (h42 : FooteLemma4Two) (h5 : FooteLemma5) (h5s : FooteLemma5Sylow)
    (h810 : FooteLemma8To10) : FooteTheorem1 :=
  footeTheorem1_of (footeLemma6_of_key (footeLemma6Key_of_inputs h3 h41 h5 h5s) h3ab)
    (footeCaseFour_of (footeLemma11_of_inputs h3 h41w h5 h5s h810)
      (footeFinal_of (footeFinalHalf_of_inputs h42 h5 h5s h810) h3s))
    footeB₀Commutes_holds

theorem footeMainL6_of_inputs
    (h3 : FooteLemma3) (h3ab : FooteNotConjAB) (h3s : FooteNotConjAAstar)
    (h41 : FooteLemma4OneLarge) (h41w : FooteLemma4OneFour) (h42 : FooteLemma4Two)
    (h5 : FooteLemma5) (h5s : FooteLemma5Sylow) (h810 : FooteLemma8To10) :
    CFSG.OddStandard.HigherRank.YamadaG23.FooteMainL6 :=
  footeMainL6_of footeL6Bridge_holds
    (footeTheorem1_of_inputs h3 h3ab h3s h41 h41w h42 h5 h5s h810)

end CFSG.CGT.Foote81L6
