module

public import CFSG.LieType.Ree.SuzukiBruhatFactorization
public import CFSG.LieType.Ree.SuzukiBorelStructure
public import CFSG.LieType.Ree.SuzukiOvoidWeyl

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped Pointwise

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiWElt_mul_self : suzukiWElt a K * suzukiWElt a K = 1 :=
  suzukiSElt_ext (suzukiW_mul_self K)

theorem suzukiWElt_inv : (suzukiWElt a K)⁻¹ = suzukiWElt a K :=
  inv_eq_of_mul_eq_one_right suzukiWElt_mul_self

theorem suzukiWElt_D_W
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) :
    suzukiWElt a K * suzukiDElt a K l * suzukiWElt a K = suzukiDElt a K l⁻¹ :=
  suzukiSElt_ext ((suzuki_torus_identities a hK).2.2.2.2.2 l)

theorem exists_W_S_W
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {u v : K}
    (huv : (u, v) ≠ (0, 0)) : ∃ (u₁ v₁ : K) (l : Kˣ) (c d : K),
      suzukiWElt a K * suzukiSElt a K u v * suzukiWElt a K =
        suzukiSElt a K u₁ v₁ * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d := by
  obtain ⟨hN, hfac⟩ := suzuki_bruhat_factorization hK u v huv
  exact ⟨_, _, _, _, _, suzukiSElt_ext (hfac (Units.mk0 _ hN) rfl)⟩

@[expose] noncomputable def suzukiBigCell
    (a : ℕ) (K : Type) [Field K] :
    Set (suzukiGroup a K) :=
  {g | ∃ b ∈ suzukiB a K, ∃ x ∈ suzukiU a K, g = b * suzukiWElt a K * x}

theorem mem_suzukiB_iff
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : suzukiGroup a K} :
    g ∈ suzukiB a K ↔ ∃ (u v : K) (l : Kˣ), g = suzukiSElt a K u v * suzukiDElt a K l := by
  constructor
  · intro hg
    obtain ⟨p, hp, -⟩ := (suzuki_borel_structure hK).2.2.2.2.2.2.1 g hg
    exact ⟨p.1.1, p.1.2, p.2, hp⟩
  · rintro ⟨u, v, l, rfl⟩
    exact mul_mem (suzukiU_le_suzukiB a K (suzukiSElt_mem_suzukiU a K u v))
      (suzukiT_le_suzukiB a K (suzukiDElt_mem_suzukiT a K l))

theorem mem_suzukiBigCell_iff
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} : g ∈ suzukiBigCell a K ↔ ∃ (u v : K) (l : Kˣ) (c d : K),
      g = suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d := by
  constructor
  · rintro ⟨b, hb, x, hx, rfl⟩
    obtain ⟨u, v, l, rfl⟩ := (mem_suzukiB_iff hK).1 hb
    obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hx
    exact ⟨u, v, l, c, d, rfl⟩
  · rintro ⟨u, v, l, c, d, rfl⟩
    exact ⟨_, (mem_suzukiB_iff hK).2 ⟨u, v, l, rfl⟩, _, suzukiSElt_mem_suzukiU a K c d, rfl⟩

theorem mul_mem_cells_of_mem_U {g x : suzukiGroup a K}
    (hg : g ∈ (suzukiB a K : Set _) ∪ suzukiBigCell a K) (hx : x ∈ suzukiU a K) :
    g * x ∈ (suzukiB a K : Set _) ∪ suzukiBigCell a K := by
  rcases hg with hg | ⟨b, hb, y, hy, rfl⟩
  · exact Or.inl (mul_mem hg (suzukiU_le_suzukiB a K hx))
  · exact Or.inr ⟨b, hb, y * x, mul_mem hy hx, by group⟩

theorem mul_mem_cells_of_mem_T
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} (hg : g ∈ (suzukiB a K : Set _) ∪ suzukiBigCell a K) (l : Kˣ) :
    g * suzukiDElt a K l ∈ (suzukiB a K : Set _) ∪ suzukiBigCell a K := by
  rcases hg with hg | ⟨b, hb, y, hy, rfl⟩
  · exact Or.inl (mul_mem hg (suzukiT_le_suzukiB a K (suzukiDElt_mem_suzukiT a K l)))
  · refine Or.inr ⟨b * suzukiDElt a K l⁻¹, mul_mem hb
      (suzukiT_le_suzukiB a K (suzukiDElt_mem_suzukiT a K _)),
      (suzukiDElt a K l)⁻¹ * y * suzukiDElt a K l, ?_, ?_⟩
    · obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
      rw [suzukiDElt_conj hK]
      exact suzukiSElt_mem_suzukiU a K _ _
    · rw [← suzukiWElt_D_W hK]
      have hW := suzukiWElt_mul_self (a := a) (K := K)
      rw [show b * (suzukiWElt a K * suzukiDElt a K l * suzukiWElt a K) * suzukiWElt a K *
          ((suzukiDElt a K l)⁻¹ * y * suzukiDElt a K l) = b * suzukiWElt a K * suzukiDElt a K l *
          (suzukiWElt a K * suzukiWElt a K) * (suzukiDElt a K l)⁻¹ * y * suzukiDElt a K l by group,
        hW]
      group

theorem mul_mem_cells_W [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} (hg : g ∈ (suzukiB a K : Set _) ∪ suzukiBigCell a K) :
    g * suzukiWElt a K ∈ (suzukiB a K : Set _) ∪ suzukiBigCell a K := by
  rcases hg with hg | ⟨b, hb, y, hy, rfl⟩
  · exact Or.inr ⟨g, hg, 1, one_mem _, by rw [mul_one]⟩
  · obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
    by_cases hcd : (c, d) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcd
      left
      rw [suzukiSElt_zero_zero hK, mul_one, mul_assoc, suzukiWElt_mul_self, mul_one]
      exact hb
    · obtain ⟨u₁, v₁, l, c₁, d₁, h⟩ := exists_W_S_W hK hcd
      refine Or.inr ⟨b * (suzukiSElt a K u₁ v₁ * suzukiDElt a K l), mul_mem hb
        ((mem_suzukiB_iff hK).2 ⟨u₁, v₁, l, rfl⟩), suzukiSElt a K c₁ d₁,
        suzukiSElt_mem_suzukiU a K _ _, ?_⟩
      calc b * suzukiWElt a K * suzukiSElt a K c d * suzukiWElt a K
          = b * (suzukiWElt a K * suzukiSElt a K c d * suzukiWElt a K) := by group
        _ = _ := by rw [h]; group

theorem suzukiGroup_mem_cells
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (g : suzukiGroup a K) : g ∈ (suzukiB a K : Set _) ∪ suzukiBigCell a K := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction_right with
  | one => exact Or.inl (one_mem _)
  | mul_right x hx y hy ih =>
    have e : (⟨x * y, mul_mem hx (Subgroup.subset_closure hy)⟩ : suzukiGroup a K) =
        ⟨x, hx⟩ * ⟨y, Subgroup.subset_closure hy⟩ := rfl
    rw [e]
    rcases hy with ⟨u, v, hy⟩ | ⟨l, hy⟩ | hy
    · have : (⟨y, Subgroup.subset_closure (Or.inl ⟨u, v, hy⟩)⟩ : suzukiGroup a K) =
          suzukiSElt a K u v := suzukiSElt_ext hy
      rw [this]
      exact mul_mem_cells_of_mem_U ih (suzukiSElt_mem_suzukiU a K u v)
    · have : (⟨y, Subgroup.subset_closure (Or.inr (Or.inl ⟨l, hy⟩))⟩ : suzukiGroup a K) =
          suzukiDElt a K l := suzukiSElt_ext hy
      rw [this]
      exact mul_mem_cells_of_mem_T hK ih l
    · have : (⟨y, Subgroup.subset_closure (Or.inr (Or.inr hy))⟩ : suzukiGroup a K) =
          suzukiWElt a K := suzukiSElt_ext hy
      rw [this]
      exact mul_mem_cells_W hK ih
  | mul_inv_cancel x hx y hy ih =>
    have e : (⟨x * y⁻¹, mul_mem hx (inv_mem (Subgroup.subset_closure hy))⟩ : suzukiGroup a K) =
        ⟨x, hx⟩ * (⟨y, Subgroup.subset_closure hy⟩ : suzukiGroup a K)⁻¹ := rfl
    rw [e]
    rcases hy with ⟨u, v, hy⟩ | ⟨l, hy⟩ | hy
    · have : (⟨y, Subgroup.subset_closure (Or.inl ⟨u, v, hy⟩)⟩ : suzukiGroup a K) =
          suzukiSElt a K u v := suzukiSElt_ext hy
      rw [this]
      exact mul_mem_cells_of_mem_U ih (inv_mem (suzukiSElt_mem_suzukiU a K u v))
    · have : (⟨y, Subgroup.subset_closure (Or.inr (Or.inl ⟨l, hy⟩))⟩ : suzukiGroup a K) =
          suzukiDElt a K l := suzukiSElt_ext hy
      rw [this, suzukiDElt_inv]
      exact mul_mem_cells_of_mem_T hK ih l⁻¹
    · have : (⟨y, Subgroup.subset_closure (Or.inr (Or.inr hy))⟩ : suzukiGroup a K) =
          suzukiWElt a K := suzukiSElt_ext hy
      rw [this, suzukiWElt_inv]
      exact mul_mem_cells_W hK ih

theorem suzukiD_eq_explicit (l : Kˣ) : suzukiD a l =
    !![((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K), 0, 0, 0; 0, ((l ^ (2 ^ a : ℤ) : Kˣ) : K), 0, 0;
      0, 0, ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K), 0; 0, 0, 0, ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)] := by
  rw [suzukiD]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem suzuki_bigCell_row_zero (u v c d : K) (l : Kˣ) (j : Fin 4) :
    ((((suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d :
      suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 0 j =
      ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) * suzukiS a c d 3 j := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_suzukiSElt, coe_suzukiDElt, coe_suzukiWElt]
  rw [suzukiD_eq_explicit, suzukiW_eq, suzukiS, suzukiS]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem suzuki_borel_row_zero (u v : K) (l : Kˣ) :
    ((((suzukiSElt a K u v * suzukiDElt a K l : suzukiGroup a K) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) 0 3 = 0 := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_suzukiSElt, coe_suzukiDElt]
  rw [suzukiD_eq_explicit, suzukiS]
  simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem suzuki_bruhat_normal_form
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (g : suzukiGroup a K) :
    ((∃ (u v : K) (l : Kˣ), g = suzukiSElt a K u v * suzukiDElt a K l) ∨
      ∃ (u v : K) (l : Kˣ) (c d : K),
        g = suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d) ∧
    ¬((∃ (u v : K) (l : Kˣ), g = suzukiSElt a K u v * suzukiDElt a K l) ∧
      ∃ (u v : K) (l : Kˣ) (c d : K),
        g = suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d) ∧
    (∀ (u v u' v' : K) (l l' : Kˣ), g = suzukiSElt a K u v * suzukiDElt a K l →
      g = suzukiSElt a K u' v' * suzukiDElt a K l' → u = u' ∧ v = v' ∧ l = l') ∧
    ∀ (u v c d u' v' c' d' : K) (l l' : Kˣ),
      g = suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d →
      g = suzukiSElt a K u' v' * suzukiDElt a K l' * suzukiWElt a K * suzukiSElt a K c' d' →
      u = u' ∧ v = v' ∧ l = l' ∧ c = c' ∧ d = d' := by
  have hB := (suzuki_borel_structure hK).2.2.2.2.2.2.1
  refine ⟨?_, ?_, fun u v u' v' l l' h h' => ?_, fun u v c d u' v' c' d' l l' h h' => ?_⟩
  · rcases suzukiGroup_mem_cells hK g with hg | hg
    · exact Or.inl ((mem_suzukiB_iff hK).1 hg)
    · exact Or.inr ((mem_suzukiBigCell_iff hK).1 hg)
  · rintro ⟨⟨u, v, l, h⟩, ⟨u', v', l', c, d, h'⟩⟩
    have e1 := suzuki_borel_row_zero (a := a) u v l
    have e2 := suzuki_bigCell_row_zero (a := a) u' v' c d l' 3
    rw [← h] at e1
    rw [← h', e1, show suzukiS a c d 3 3 = 1 from rfl, mul_one] at e2
    exact Units.ne_zero _ e2.symm
  · have hmem : g ∈ suzukiB a K := (mem_suzukiB_iff hK).2 ⟨u, v, l, h⟩
    obtain ⟨p, -, hp⟩ := hB g hmem
    have e1 := hp ((u, v), l) h
    have e2 := hp ((u', v'), l') h'
    rw [← e2] at e1
    simp only [Prod.mk.injEq] at e1
    exact ⟨e1.1.1, e1.1.2, e1.2⟩
  · have hrow : ∀ j, ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) * suzukiS a c d 3 j =
        ((l' ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) * suzukiS a c' d' 3 j := fun j => by
      rw [← suzuki_bigCell_row_zero u v c d l j, ← suzuki_bigCell_row_zero u' v' c' d' l' j,
        ← h, ← h']
    have h3 := hrow 3
    rw [show suzukiS a c d 3 3 = 1 from rfl, show suzukiS a c' d' 3 3 = 1 from rfl, mul_one,
      mul_one] at h3
    have hll : l = l' := by
      have hbij := (suzuki_frobenius_exponents a K hK).2.2.2.2.2.2.2.2.2.2.2.2
      exact hbij.1 (Units.ext h3)
    subst hll
    have hl0 : ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h2 := mul_left_cancel₀ hl0 (hrow 2)
    have h1 := mul_left_cancel₀ hl0 (hrow 1)
    rw [show suzukiS a c d 3 2 = c from rfl, show suzukiS a c' d' 3 2 = c' from rfl] at h2
    rw [show suzukiS a c d 3 1 = c ^ (2 ^ (a + 1) + 1) + d from rfl,
      show suzukiS a c' d' 3 1 = c' ^ (2 ^ (a + 1) + 1) + d' from rfl] at h1
    subst h2
    have hd : d = d' := add_left_cancel h1
    subst hd
    rw [h] at h'
    have hS := mul_right_cancel (mul_right_cancel (mul_right_cancel h'))
    obtain ⟨rfl, rfl⟩ := suzukiSElt_inj.1 hS
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end CFSG.LieType.Ree
