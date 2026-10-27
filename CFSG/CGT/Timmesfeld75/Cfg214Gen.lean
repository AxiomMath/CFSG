module

public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.CGT.Timmesfeld75.StrongClosure

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem dihedral_central_of_even_order_mem {x y : G} (hx : x * x = 1) (hy : y * y = 1) {m : ℕ}
    (hm0 : 0 < m) (hm : orderOf (x * y) = 2 * m) :
    ∃ z : G, z * z = 1 ∧ z ≠ 1 ∧ x * z = z * x ∧ y * z = z * y ∧
      ((∃ g ∈ Subgroup.closure ({x, y} : Set G), y * z = g⁻¹ * x * g) ∨
        ∃ g ∈ Subgroup.closure ({x, y} : Set G), y * z = g⁻¹ * y * g) := by
  have hw : x * y ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert x {y}))
      (Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y)))
  have hzz : (x * y) ^ m * (x * y) ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hm]
    exact pow_orderOf_eq_one _
  have hzinv : ((x * y) ^ m)⁻¹ = (x * y) ^ m := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * (x * y) ^ m = (x * y) ^ m * x := by
    have h1 : x * (x * y) ^ m * x⁻¹ = (x * y) ^ m := by
      rw [← conj_pow, left_invol_inverts hx hy, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hxw : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have hyz : y * (x * y) ^ m = (x * y) ^ m * y := by
    calc y * (x * y) ^ m = x * (x * y) * (x * y) ^ m := by rw [hxw]
      _ = x * ((x * y) * (x * y) ^ m) := mul_assoc _ _ _
      _ = x * ((x * y) ^ m * (x * y)) := by rw [(Commute.self_pow (x * y) m).eq]
      _ = (x * (x * y) ^ m) * (x * y) := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * x) * (x * y) := by rw [hxz]
      _ = (x * y) ^ m * (x * (x * y)) := mul_assoc _ _ _
      _ = (x * y) ^ m * y := by rw [hxw]
  refine ⟨(x * y) ^ m, hzz, pow_ne_one_of_lt_orderOf hm0.ne' (by omega), hxz, hyz, ?_⟩
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · right
    refine ⟨(x * y) ^ k, Subgroup.pow_mem _ hw k, ?_⟩
    rw [inv_pow_mul_mul_pow_of_inverts (right_invol_inverts hx hy) k,
      show 2 * k = m by omega, hzinv, hyz]
  · left
    refine ⟨(x * y) ^ (k + 1), Subgroup.pow_mem _ hw (k + 1), ?_⟩
    have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hx hy) (k + 1)
    calc y * (x * y) ^ m = (x * y)⁻¹ * x * (x * y) ^ m := by rw [← invol_eq_inv_mul_mul hy]
      _ = (x * y)⁻¹ * ((x * y) ^ m * x) := by rw [mul_assoc, hxz]
      _ = (x * y)⁻¹ * (x * y) ^ m * x := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * (x * y))⁻¹ * x := by rw [mul_inv_rev ((x * y) ^ m) (x * y), hzinv]
      _ = ((x * y) ^ (2 * (k + 1)))⁻¹ * x := by
        rw [show 2 * (k + 1) = m + 1 by omega, pow_succ]
      _ = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := h1.symm

theorem Cfg.odd_orderOf_mul_gen [Finite G] (c : Cfg T T₁)
    (hconj : ∃ x ∈ T ⊔ T₁, T₁ = conjSubgroup x T) {a b : G} (ha : a ∈ T)
    (haL : a ∉ normIn T T₁) (hb : b ∈ T₁) (hbL : b ∉ normIn T₁ T) :
    Odd (orderOf (a * b)) := by
  rcases Nat.even_or_odd (orderOf (a * b)) with ⟨m, hm⟩ | hodd
  swap
  · exact hodd
  exfalso
  have haa : a * a = 1 := elemAbelian_mul_self c.wc.1 ha
  have hbb : b * b = 1 := elemAbelian_mul_self c.wc₁.1 hb
  have hm0 : 0 < m := by
    have := orderOf_pos (a * b)
    omega
  have hord : orderOf (b * a) = 2 * m := by
    have h1 : b * a = (a * b)⁻¹ := by
      rw [mul_inv_rev, elemAbelian_inv c.wc.1 ha, elemAbelian_inv c.wc₁.1 hb]
    rw [h1, orderOf_inv]
    omega
  obtain ⟨z, -, hz1, hbz, haz, hconjz⟩ := dihedral_central_of_even_order_mem hbb haa hm0 hord
  have hclX : Subgroup.closure ({b, a} : Set G) ≤ T ⊔ T₁ := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Subgroup.mem_sup_right hb, Subgroup.mem_sup_left ha⟩
  have haM : a ∉ cfgM T T₁ := fun h => haL (by rw [← c.inf_cfgM]; exact ⟨ha, h⟩)
  have hstar : ∀ t ∈ T, t ∉ normIn T T₁ → ∀ h ∈ T ⊔ T₁, a * z = h⁻¹ * t * h → a * z ∈ T := by
    intro t ht htL h hhX hh
    have hc : a * z * a = a * (a * z) :=
      calc a * z * a = a * (z * a) := mul_assoc _ _ _
        _ = a * (a * z) := by rw [haz]
    have hcomm : ⁅h⁻¹ * t * h, a⁆ ∈ cfgM T T₁ := by
      rw [← hh, commutatorElement_eq_one_iff_mul_comm.2 hc]
      exact (cfgM T T₁).one_mem
    have := c.strongly_closed_star ha haM hhX ht htL hcomm
    rwa [← hh] at this
  have hazT : a * z ∈ T := by
    rcases hconjz with ⟨g, hgX, hg⟩ | ⟨g, hgX, hg⟩
    · obtain ⟨x, hxX, hx⟩ := hconj
      have hb' : b ∈ conjSubgroup x T := by rw [← hx]; exact hb
      have hbT : x⁻¹ * b * x ∈ T := mem_conjSubgroup.1 hb'
      have htL : x⁻¹ * b * x ∉ normIn T T₁ := by
        intro hL
        have hM : x⁻¹ * b * x ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁ hL
        have hM' := c.conj_mem_cfgM hxX hM
        have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
        rw [e] at hM'
        exact hbL (by rw [← c.inf_cfgM_right]; exact ⟨hb, hM'⟩)
      exact hstar (x⁻¹ * b * x) hbT htL (x⁻¹ * g)
        ((T ⊔ T₁).mul_mem ((T ⊔ T₁).inv_mem hxX) (hclX hgX)) (by rw [hg]; group)
    · exact hstar a ha haL g (hclX hgX) hg
  have hzT : z ∈ T := by
    have := T.mul_mem ha hazT
    rwa [← mul_assoc, haa, one_mul] at this
  have hbN : b ∈ Subgroup.normalizer (T : Set G) :=
    c.wc.centralizer_le_normalizer hzT hz1 (Subgroup.mem_centralizer_singleton_iff.2 hbz)
  exact hbL (mem_normIn.2 ⟨hb, hbN⟩)

end CFSG.CGT.Timmesfeld75
