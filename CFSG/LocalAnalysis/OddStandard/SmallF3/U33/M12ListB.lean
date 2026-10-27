module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.DihedralRec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12Model

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G] {x₁ x₂ lam tau : G}

private instance instDecEqM12 : DecidableEq M12Mod := fun a b =>
  if h : M12Mod.equivProd a = M12Mod.equivProd b then isTrue (M12Mod.equivProd.injective h)
  else isFalse (fun hab => h (by rw [hab]))

private instance : Fintype M12Mod :=
  Fintype.ofEquiv (Fin 4 × Fin 4 × Fin 2 × Fin 2) M12Mod.equivProd.symm

private lemma orderOf_map_of_injective {M H : Type*} [Group M] [Group H]
    (f : M →* H) (hf : Function.Injective f) (a : M) : orderOf (f a) = orderOf a := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, pow_orderOf_eq_one, map_one]
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact hf (by rw [map_pow, map_one, pow_orderOf_eq_one])

private lemma map_mem_zpowers_iff {M H : Type*} [Group M] [Group H]
    (f : M →* H) (hf : Function.Injective f) (a m : M) :
    f m ∈ zpowers (f a) ↔ m ∈ zpowers a := by
  constructor
  · intro hm
    rw [Subgroup.mem_zpowers_iff] at hm ⊢
    obtain ⟨n, hn⟩ := hm
    exact ⟨n, hf (by rw [map_zpow]; exact hn)⟩
  · intro hm
    rw [Subgroup.mem_zpowers_iff] at hm ⊢
    obtain ⟨n, hn⟩ := hm
    exact ⟨n, by rw [← map_zpow, hn]⟩

private lemma range_inf_eq_map_comap (φ : M12Mod →* G) (K : Subgroup G) :
    φ.range ⊓ K = (K.comap φ).map φ := by
  rw [← Subgroup.map_comap_eq_self (f := φ) (H := φ.range ⊓ K) inf_le_left]
  rw [Subgroup.comap_inf, MonoidHom.comap_range_self, top_inf_eq]

private lemma comap_centralizer_singleton (φ : M12Mod →* G) (hφ : Function.Injective φ)
    (m : M12Mod) :
    (Subgroup.centralizer ({φ m} : Set G)).comap φ =
      Subgroup.centralizer ({m} : Set M12Mod) := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply hφ
    rw [map_mul, map_mul]
    exact h
  · intro h
    rw [← map_mul, ← map_mul, h]

private lemma centralizer_range_inf (φ : M12Mod →* G) (hφ : Function.Injective φ)
    (m : M12Mod) :
    φ.range ⊓ Subgroup.centralizer ({φ m} : Set G) =
      (Subgroup.centralizer ({m} : Set M12Mod)).map φ := by
  rw [range_inf_eq_map_comap, comap_centralizer_singleton φ hφ]

namespace M12Mod

private def ma : M12Mod := mx₁ ^ 2 * mlam

private lemma four_mul_check :
    ∀ (a b : Fin 4) (i j : Fin 2) (c d : Fin 4) (k l : Fin 2),
      (i = 0 ∧ j = 0 ∧ (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2)) →
      (k = 0 ∧ l = 0 ∧ (c = 0 ∨ c = 2) ∧ (d = 0 ∨ d = 2)) →
      ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).i = 0 ∧
        ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).j = 0 ∧
        (((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).a = 0 ∨
          ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).a = 2) ∧
        (((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).b = 0 ∨
          ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).b = 2) := by
  decide +kernel

private lemma four_inv_check :
    ∀ (a b : Fin 4) (i j : Fin 2), (i = 0 ∧ j = 0 ∧ (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2)) →
      ((⟨a, b, i, j⟩ : M12Mod)⁻¹).i = 0 ∧ ((⟨a, b, i, j⟩ : M12Mod)⁻¹).j = 0 ∧
        (((⟨a, b, i, j⟩ : M12Mod)⁻¹).a = 0 ∨ ((⟨a, b, i, j⟩ : M12Mod)⁻¹).a = 2) ∧
        (((⟨a, b, i, j⟩ : M12Mod)⁻¹).b = 0 ∨ ((⟨a, b, i, j⟩ : M12Mod)⁻¹).b = 2) := by
  decide +kernel

private lemma pow_mx1_even_mem (a : Fin 4) (ha : a = 0 ∨ a = 2) :
    mx₁ ^ a.val ∈ fourGrp mx₁ mx₂ := by
  rcases ha with rfl | rfl
  · change mx₁ ^ (0 : Fin 4).val ∈ fourGrp mx₁ mx₂
    simp
  · change mx₁ ^ (2 : Fin 4).val ∈ fourGrp mx₁ mx₂
    exact Subgroup.subset_closure (by simp)

private lemma pow_mx2_even_mem (b : Fin 4) (hb : b = 0 ∨ b = 2) :
    mx₂ ^ b.val ∈ fourGrp mx₁ mx₂ := by
  rcases hb with rfl | rfl
  · change mx₂ ^ (0 : Fin 4).val ∈ fourGrp mx₁ mx₂
    simp
  · change mx₂ ^ 2 ∈ fourGrp mx₁ mx₂
    have h2 : mx₂ ^ 2 = (mx₁ * mx₂) ^ 2 * mx₁ ^ 2 := by decide +kernel
    rw [h2]
    exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private lemma mem_fourGrp_iff (m : M12Mod) :
    m ∈ fourGrp mx₁ mx₂ ↔
      m.i = 0 ∧ m.j = 0 ∧ (m.a = 0 ∨ m.a = 2) ∧ (m.b = 0 ∨ m.b = 2) := by
  constructor
  · intro hm
    change m ∈ closure ({mx₁ ^ 2, (mx₁ * mx₂) ^ 2} : Set M12Mod) at hm
    refine Subgroup.closure_induction
      (p := fun g (_ : g ∈ closure ({mx₁ ^ 2, (mx₁ * mx₂) ^ 2} : Set M12Mod)) =>
        g.i = 0 ∧ g.j = 0 ∧ (g.a = 0 ∨ g.a = 2) ∧ (g.b = 0 ∨ g.b = 2)) ?_ ?_ ?_ ?_ hm
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> decide +kernel
    · decide +kernel
    · intro x y hx hy ihx ihy
      obtain ⟨a, b, i, j⟩ := x
      obtain ⟨c, d, k, l⟩ := y
      exact four_mul_check a b i j c d k l ihx ihy
    · intro x hx ih
      obtain ⟨a, b, i, j⟩ := x
      exact four_inv_check a b i j ih
  · intro hm
    obtain ⟨a, b, i, j⟩ := m
    obtain ⟨hi, hj, ha, hb⟩ := hm
    have hi' : i = 0 := hi
    have hj' : j = 0 := hj
    subst hi'
    subst hj'
    rw [eq_pow_mul (⟨a, b, 0, 0⟩ : M12Mod)]
    simp only [Fin.val_zero, pow_zero, mul_one]
    exact mul_mem (pow_mx1_even_mem a ha) (pow_mx2_even_mem b hb)

private lemma wreath_mul_check :
    ∀ (a b : Fin 4) (i j : Fin 2) (c d : Fin 4) (k l : Fin 2),
      j = 0 → l = 0 → ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).j = 0 := by
  decide +kernel

private lemma wreath_inv_check :
    ∀ (a b : Fin 4) (i j : Fin 2), j = 0 → ((⟨a, b, i, j⟩ : M12Mod)⁻¹).j = 0 := by
  decide +kernel

private lemma mem_wreathGrp_iff (m : M12Mod) :
    m ∈ wreathGrp mx₁ mx₂ mlam ↔ m.j = 0 := by
  constructor
  · intro hm
    change m ∈ closure ({mx₁, mx₂, mlam} : Set M12Mod) at hm
    refine Subgroup.closure_induction
      (p := fun g (_ : g ∈ closure ({mx₁, mx₂, mlam} : Set M12Mod)) => g.j = 0) ?_ ?_ ?_ ?_ hm
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · intro x y hx hy ihx ihy
      obtain ⟨a, b, i, j⟩ := x
      obtain ⟨c, d, k, l⟩ := y
      exact wreath_mul_check a b i j c d k l ihx ihy
    · intro x hx ih
      obtain ⟨a, b, i, j⟩ := x
      exact wreath_inv_check a b i j ih
  · intro hj
    obtain ⟨a, b, i, j⟩ := m
    have hj' : j = 0 := hj
    subst hj'
    rw [eq_pow_mul (⟨a, b, i, 0⟩ : M12Mod)]
    simp only [Fin.val_zero, pow_zero, mul_one]
    exact mul_mem (mul_mem (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) a.val)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) b.val))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) i.val)

private lemma j0_decomp :
    ∀ (a b : Fin 4) (i : Fin 2), (⟨a, b, i, 0⟩ : M12Mod) = ⟨a, b, 0, 0⟩ * mlam ^ i.val := by
  decide +kernel

private lemma j_decomp :
    ∀ (a b : Fin 4) (i j : Fin 2),
      (⟨a, b, i, j⟩ : M12Mod) = (⟨a, b, 0, 0⟩ * mlam ^ i.val) * mtau ^ j.val := by
  decide +kernel

private lemma orderOf_mtau : orderOf mtau = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private lemma mem_zpowers_mtau_iff (x : M12Mod) :
    x ∈ zpowers mtau ↔ x = 1 ∨ x = mtau := by
  rw [mem_zpowers_iff_mem_range_orderOf (x := mtau), orderOf_mtau]
  have himg : (Finset.range 2).image (mtau ^ ·) = ({1, mtau} : Finset M12Mod) := by
    decide +kernel
  rw [himg, Finset.mem_insert, Finset.mem_singleton]

private lemma cent_mtau_fwd :
    ∀ (a b : Fin 4) (i j : Fin 2),
      (⟨a, b, i, j⟩ : M12Mod) * mtau = mtau * (⟨a, b, i, j⟩ : M12Mod) →
        (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2) := by
  decide +kernel

private lemma centralizer_mtau_model :
    Subgroup.centralizer ({mtau} : Set M12Mod) =
      (fourGrp mx₁ mx₂ ⊔ zpowers mlam) ⊔ zpowers mtau := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, i, j⟩ := x
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨ha, hb⟩ := cent_mtau_fwd a b i j hx
    have hE : (⟨a, b, 0, 0⟩ : M12Mod) ∈ fourGrp mx₁ mx₂ :=
      (mem_fourGrp_iff _).mpr ⟨rfl, rfl, ha, hb⟩
    rw [j_decomp a b i j]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hE))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers mlam i.val))))
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers mtau j.val))
  · apply sup_le
    · apply sup_le
      · rw [show fourGrp mx₁ mx₂ = closure ({mx₁ ^ 2, (mx₁ * mx₂) ^ 2} : Set M12Mod) from rfl,
          Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)

private lemma wreath_cen_tau_model :
    wreathGrp mx₁ mx₂ mlam ⊓ Subgroup.centralizer ({mtau} : Set M12Mod) =
      fourGrp mx₁ mx₂ ⊔ zpowers mlam := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, i, j⟩ := x
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hw, hc⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hj : j = 0 := (mem_wreathGrp_iff _).mp hw
    obtain ⟨ha, hb⟩ := cent_mtau_fwd a b i j hc
    subst hj
    have hE : (⟨a, b, 0, 0⟩ : M12Mod) ∈ fourGrp mx₁ mx₂ :=
      (mem_fourGrp_iff _).mpr ⟨rfl, rfl, ha, hb⟩
    rw [j0_decomp a b i]
    exact mul_mem (Subgroup.mem_sup_left hE)
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers mlam i.val))
  · apply sup_le
    · apply le_inf
      · rw [show fourGrp mx₁ mx₂ = closure ({mx₁ ^ 2, (mx₁ * mx₂) ^ 2} : Set M12Mod) from rfl,
          Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact (mem_wreathGrp_iff _).mpr (by decide +kernel)
        · exact (mem_wreathGrp_iff _).mpr (by decide +kernel)
      · rw [show fourGrp mx₁ mx₂ = closure ({mx₁ ^ 2, (mx₁ * mx₂) ^ 2} : Set M12Mod) from rfl,
          Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
    · rw [Subgroup.zpowers_le]
      refine ⟨(mem_wreathGrp_iff mlam).mpr (by decide +kernel), ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)

private lemma elam_le_wreath : fourGrp mx₁ mx₂ ⊔ zpowers mlam ≤ wreathGrp mx₁ mx₂ mlam := by
  apply sup_le
  · rw [show fourGrp mx₁ mx₂ = closure ({mx₁ ^ 2, (mx₁ * mx₂) ^ 2} : Set M12Mod) from rfl,
      Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (mem_wreathGrp_iff _).mpr (by decide +kernel)
    · exact (mem_wreathGrp_iff _).mpr (by decide +kernel)
  · rw [Subgroup.zpowers_le]
    exact (mem_wreathGrp_iff mlam).mpr (by decide +kernel)

private lemma elam_inf_mtau_model :
    (fourGrp mx₁ mx₂ ⊔ zpowers mlam) ⊓ zpowers mtau = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [Subgroup.mem_bot]
  rcases (mem_zpowers_mtau_iff x).mp hx.2 with h | h
  · exact h
  · exfalso
    rw [h] at hx
    exact absurd ((mem_wreathGrp_iff mtau).mp (elam_le_wreath hx.1)) (by decide +kernel)

private lemma orderOf_ma : orderOf ma = 4 := by
  have h := orderOf_eq_prime_pow (x := ma) (p := 2) (n := 1)
    (by decide +kernel) (by decide +kernel)
  rw [h]; norm_num

private lemma mlam_conj_ma : mlam * ma * mlam⁻¹ = ma⁻¹ := by decide +kernel

private lemma mlam_not_mem_zpowers_ma : mlam ∉ zpowers ma := by
  rw [mem_zpowers_iff_mem_range_orderOf (x := ma), orderOf_ma]
  decide +kernel

private lemma ma_eq_y_mul_lam : mx₁ ^ 2 = ma * mlam := by decide +kernel

private lemma ma_sq_eq_z : (mx₁ * mx₂) ^ 2 = ma ^ 2 := by decide +kernel

private lemma closure_ma_mlam_eq :
    closure ({ma, mlam} : Set M12Mod) = fourGrp mx₁ mx₂ ⊔ zpowers mlam := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro s (rfl | rfl)
    · show ma ∈ fourGrp mx₁ mx₂ ⊔ zpowers mlam
      rw [show ma = mx₁ ^ 2 * mlam from rfl]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers mlam))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers mlam)
  · rw [sup_le_iff]
    constructor
    · rw [show fourGrp mx₁ mx₂ = closure ({mx₁ ^ 2, (mx₁ * mx₂) ^ 2} : Set M12Mod) from rfl,
        Subgroup.closure_le]
      rintro s (rfl | rfl)
      · show mx₁ ^ 2 ∈ closure ({ma, mlam} : Set M12Mod)
        rw [ma_eq_y_mul_lam]
        exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      · show (mx₁ * mx₂) ^ 2 ∈ closure ({ma, mlam} : Set M12Mod)
        rw [ma_sq_eq_z]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)

end M12Mod

theorem M12Rel.centralizer_tau (h : M12Rel x₁ x₂ lam tau) :
    m12Grp x₁ x₂ lam tau ⊓ centralizer ({tau} : Set G) =
        (fourGrp x₁ x₂ ⊔ zpowers lam) ⊔ zpowers tau ∧
      (fourGrp x₁ x₂ ⊔ zpowers lam) ⊓ zpowers tau = ⊥ ∧
      Nonempty (↥(fourGrp x₁ x₂ ⊔ zpowers lam) ≃* DihedralGroup 4) := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hmap_four : (fourGrp M12Mod.mx₁ M12Mod.mx₂).map φ = fourGrp x₁ x₂ := by
    rw [show fourGrp M12Mod.mx₁ M12Mod.mx₂ =
        closure ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2} : Set M12Mod) from rfl,
      show fourGrp x₁ x₂ = closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) from rfl,
      MonoidHom.map_closure]
    congr 1
    rw [Set.image_pair]
    rw [show φ (M12Mod.mx₁ ^ 2) = x₁ ^ 2 by rw [map_pow, h1],
      show φ ((M12Mod.mx₁ * M12Mod.mx₂) ^ 2) = (x₁ * x₂) ^ 2 by rw [map_pow, map_mul, h1, h2]]
  have hmap_elam : (fourGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mlam).map φ =
      fourGrp x₁ x₂ ⊔ zpowers lam := by
    rw [Subgroup.map_sup, hmap_four, MonoidHom.map_zpowers, h3]
  have hmap_tau : (zpowers M12Mod.mtau).map φ = zpowers tau := by
    rw [MonoidHom.map_zpowers, h4]
  have hmap_sup : ((fourGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mlam) ⊔
      zpowers M12Mod.mtau).map φ = (fourGrp x₁ x₂ ⊔ zpowers lam) ⊔ zpowers tau := by
    rw [Subgroup.map_sup, hmap_elam, hmap_tau]
  refine ⟨?_, ?_, ?_⟩
  · have hL : m12Grp x₁ x₂ lam tau ⊓ centralizer ({tau} : Set G) =
        (Subgroup.centralizer ({M12Mod.mtau} : Set M12Mod)).map φ := by
      rw [← hrange, ← h4]
      exact centralizer_range_inf φ hinj M12Mod.mtau
    rw [hL, M12Mod.centralizer_mtau_model, ← hmap_sup]
  · rw [← hmap_elam, ← hmap_tau, ← Subgroup.map_inf _ _ φ hinj,
      M12Mod.elam_inf_mtau_model, Subgroup.map_bot]
  · have ha : φ M12Mod.ma = x₁ ^ 2 * lam := by
      rw [show M12Mod.ma = M12Mod.mx₁ ^ 2 * M12Mod.mlam from rfl, map_mul, map_pow, h1, h3]
    have hord : orderOf (x₁ ^ 2 * lam) = 4 := by
      rw [← ha, orderOf_map_of_injective φ hinj, M12Mod.orderOf_ma]
    have hb : lam ^ 2 = 1 := by
      rw [← h.ord_lam]; exact pow_orderOf_eq_one lam
    have hconj : lam * (x₁ ^ 2 * lam) * lam⁻¹ = (x₁ ^ 2 * lam)⁻¹ := by
      have hcongr := congrArg φ M12Mod.mlam_conj_ma
      simp only [map_mul, map_inv, h3, ha] at hcongr
      exact hcongr
    have hnot : lam ∉ zpowers (x₁ ^ 2 * lam) := by
      intro hmem
      have hmem' : φ M12Mod.mlam ∈ zpowers (φ M12Mod.ma) := by
        simpa only [h3, ha] using hmem
      exact M12Mod.mlam_not_mem_zpowers_ma
        ((map_mem_zpowers_iff φ hinj M12Mod.ma M12Mod.mlam).mp hmem')
    have hclos : closure ({x₁ ^ 2 * lam, lam} : Set G) = fourGrp x₁ x₂ ⊔ zpowers lam := by
      have hLmap : (closure ({M12Mod.ma, M12Mod.mlam} : Set M12Mod)).map φ =
          closure ({x₁ ^ 2 * lam, lam} : Set G) := by
        rw [MonoidHom.map_closure]
        congr 1
        rw [Set.image_pair]
        rw [ha, h3]
      rw [← hLmap, ← hmap_elam, M12Mod.closure_ma_mlam_eq]
    rw [← hclos]
    exact nonempty_mulEquiv_dihedral_four hord hb hconj hnot

theorem M12Rel.centralizer_tau_inf_wreathGrp (h : M12Rel x₁ x₂ lam tau) :
    wreathGrp x₁ x₂ lam ⊓ centralizer ({tau} : Set G) = fourGrp x₁ x₂ ⊔ zpowers lam := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hmap_four : (fourGrp M12Mod.mx₁ M12Mod.mx₂).map φ = fourGrp x₁ x₂ := by
    rw [show fourGrp M12Mod.mx₁ M12Mod.mx₂ =
        closure ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2} : Set M12Mod) from rfl,
      show fourGrp x₁ x₂ = closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) from rfl,
      MonoidHom.map_closure]
    congr 1
    rw [Set.image_pair]
    rw [show φ (M12Mod.mx₁ ^ 2) = x₁ ^ 2 by rw [map_pow, h1],
      show φ ((M12Mod.mx₁ * M12Mod.mx₂) ^ 2) = (x₁ * x₂) ^ 2 by rw [map_pow, map_mul, h1, h2]]
  have hmap_elam : (fourGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mlam).map φ =
      fourGrp x₁ x₂ ⊔ zpowers lam := by
    rw [Subgroup.map_sup, hmap_four, MonoidHom.map_zpowers, h3]
  have hmap_wreath : (wreathGrp M12Mod.mx₁ M12Mod.mx₂ M12Mod.mlam).map φ =
      wreathGrp x₁ x₂ lam := by
    rw [show wreathGrp M12Mod.mx₁ M12Mod.mx₂ M12Mod.mlam =
        closure ({M12Mod.mx₁, M12Mod.mx₂, M12Mod.mlam} : Set M12Mod) from rfl,
      show wreathGrp x₁ x₂ lam = closure ({x₁, x₂, lam} : Set G) from rfl,
      MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl | rfl), hz⟩
      · exact Or.inl (by rw [← hz, h1])
      · exact Or.inr (Or.inl (by rw [← hz, h2]))
      · exact Or.inr (Or.inr (by rw [← hz, h3]))
    · rintro (hg | hg | hg)
      · exact ⟨M12Mod.mx₁, Or.inl rfl, by rw [h1, hg]⟩
      · exact ⟨M12Mod.mx₂, Or.inr (Or.inl rfl), by rw [h2, hg]⟩
      · exact ⟨M12Mod.mlam, Or.inr (Or.inr rfl), by rw [h3, hg]⟩
  have hle_wm : wreathGrp x₁ x₂ lam ≤ m12Grp x₁ x₂ lam tau := by
    rw [show wreathGrp x₁ x₂ lam = closure ({x₁, x₂, lam} : Set G) from rfl,
      show m12Grp x₁ x₂ lam tau = closure ({x₁, x₂, lam, tau} : Set G) from rfl,
      Subgroup.closure_le]
    intro y hy
    apply Subgroup.subset_closure
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  have hL : wreathGrp x₁ x₂ lam ⊓ centralizer ({tau} : Set G) =
      (wreathGrp M12Mod.mx₁ M12Mod.mx₂ M12Mod.mlam ⊓
        Subgroup.centralizer ({M12Mod.mtau} : Set M12Mod)).map φ := by
    rw [Subgroup.map_inf _ _ φ hinj, hmap_wreath, ← centralizer_range_inf φ hinj M12Mod.mtau,
      h4, hrange]
    rw [← inf_assoc, inf_eq_left.mpr hle_wm]
  rw [hL, M12Mod.wreath_cen_tau_model, hmap_elam]

end CFSG.OddStandard.SmallF3.HarrisU33
