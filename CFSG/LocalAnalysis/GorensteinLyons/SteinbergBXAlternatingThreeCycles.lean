module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXAlternatingPCycles

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Equiv Equiv.Perm Subgroup

universe u

variable {n : ℕ}

theorem exists_alternating_conj_sq_of_threeCycle {c d : Perm (Fin n)} (hc : c.IsThreeCycle)
    (hd : d.IsThreeCycle) (hcd : Disjoint c.support d.support) :
    ∃ g : alternatingGroup (Fin n), (g : Perm (Fin n)) * c * (g : Perm (Fin n))⁻¹ = c ^ 2 ∧
      ∀ x, x ∉ c.support → x ∉ d.support → (g : Perm (Fin n)) x = x := by
  obtain ⟨h, hh, hfix⟩ := exists_conj_pow_support hc.isCycle (m := 2)
    (by rw [hc.orderOf]; norm_num)
  obtain ⟨x₀, hx₀⟩ : d.support.Nonempty := Finset.card_pos.mp (by rw [hd.card_support]; norm_num)
  have hdx₀ : d x₀ ≠ x₀ := mem_support.mp hx₀
  set τ := swap x₀ (d x₀) with hτ
  have hτfix : ∀ x ∉ d.support, τ x = x := fun x hx =>
    swap_apply_of_ne_of_ne (fun h => hx (h ▸ hx₀)) (fun h => hx (h ▸ apply_mem_support.mpr hx₀))
  have hτc : Commute τ c := commute_of_apply_eq_self hcd.symm hτfix fun x hx =>
    notMem_support.mp hx
  rcases Int.units_eq_one_or (sign h) with hs | hs
  · exact ⟨⟨h, mem_alternatingGroup.mpr hs⟩, hh, fun x hx _ => hfix x hx⟩
  · have hmem : h * τ ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, map_mul, hs, hτ, sign_swap hdx₀.symm]
      decide
    refine ⟨⟨h * τ, hmem⟩, ?_, fun x hx hx' => ?_⟩
    · change h * τ * c * (h * τ)⁻¹ = c ^ 2
      calc h * τ * c * (h * τ)⁻¹ = h * (τ * c * τ⁻¹) * h⁻¹ := by group
        _ = h * c * h⁻¹ := by rw [hτc.eq, mul_inv_cancel_right]
        _ = c ^ 2 := hh
    · change (h * τ) x = x
      rw [Perm.mul_apply, hτfix x hx', hfix x hx]

theorem exists_fin_ne_ne {k : ℕ} (hk : 3 ≤ k) (i j : Fin k) : ∃ l : Fin k, l ≠ i ∧ l ≠ j := by
  have h2 : ({i, j} : Finset (Fin k)).card < (Finset.univ : Finset (Fin k)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact ((Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])).trans_lt
      (by omega)
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  exact ⟨l, hl.1, hl.2⟩

theorem alternating_central_cover_injective_disjoint_three_cycles {k : ℕ} (hk : 3 ≤ k)
    (_hn : 3 * k ≤ n) {K : Type*} [Group K] [Finite K] (π : K →* alternatingGroup (Fin n))
    (hπ : Function.Surjective π) (hZ : π.ker ≤ center K) (c : Fin k → alternatingGroup (Fin n))
    (hc : ∀ i, (c i : Perm (Fin n)).IsThreeCycle)
    (hdisj : Pairwise fun i j => (c i : Perm (Fin n)).Disjoint (c j)) :
    (∀ x ∈ (closure (Set.range c)).comap π, ∀ y ∈ (closure (Set.range c)).comap π,
        Commute x y) ∧
      (∃ V : Subgroup K, CFSG.IsElementaryAbelian 3 V ∧ Nat.card V = 3 ^ k ∧ Set.InjOn π V ∧
        V.map π = closure (Set.range c)) ∧
      ∀ (T : Type u) [Group T] [Finite T], IsPGroup 2 T → ∀ α : T →* MulAut K,
        (∀ t, ∀ x ∈ (closure (Set.range c)).comap π, α t x ∈ (closure (Set.range c)).comap π) →
        (∀ t, ∀ x ∈ (closure (Set.range c)).comap π, π (α t x) = π x) →
        ∃ V : Subgroup K, CFSG.IsElementaryAbelian 3 V ∧ Nat.card V = 3 ^ k ∧ Set.InjOn π V ∧
          V.map π = closure (Set.range c) ∧ ∀ t, ∀ x ∈ V, α t x = x := by
  have hord : ∀ i, orderOf (c i) = 3 := fun i => by rw [← orderOf_coe, (hc i).orderOf]
  have hcp : ∀ i, c i ^ 3 = 1 := fun i => hord i ▸ pow_orderOf_eq_one (c i)
  have hc1 : ∀ i, c i ≠ 1 := fun i h => by
    have := hord i
    rw [h, orderOf_one] at this
    omega
  have hdisj' : Pairwise fun i j =>
      Disjoint (c i : Perm (Fin n)).support (c j : Perm (Fin n)).support :=
    fun i j hij => disjoint_iff_disjoint_support.mp (hdisj hij)
  have hsupp : ∀ i, ∀ x ∉ (c i : Perm (Fin n)).support, (c i : Perm (Fin n)) x = x :=
    fun i x hx => notMem_support.mp hx
  have hcomm : ∀ i j, Commute (c i) (c j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact commute_of_coe_commute (hdisj hij).commute
  have hind : iSupIndep fun i => zpowers (c i) :=
    iSupIndep_zpowers_of_apply_eq_self (alternatingGroup (Fin n)).subtype Subtype.val_injective
      c (fun i => (c i : Perm (Fin n)).support) hdisj' hsupp
  have hg : ∀ i j, ∃ g : alternatingGroup (Fin n), g * c i * g⁻¹ = c i ^ (2 : ℤ) ∧
      (i ≠ j → g * c j * g⁻¹ = c j) := by
    intro i j
    obtain ⟨l, hli, hlj⟩ := exists_fin_ne_ne hk i j
    obtain ⟨g, hgc, hgfix⟩ := exists_alternating_conj_sq_of_threeCycle (hc i) (hc l)
      (hdisj' hli.symm)
    refine ⟨g, Subtype.ext ?_, fun hij => ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv, zpow_ofNat, Subgroup.coe_pow] using hgc
    · have hgj : Commute g (c j) := by
        refine commute_of_coe_commute (commute_of_apply_eq_self
          (s := (c i : Perm (Fin n)).support ∪ (c l : Perm (Fin n)).support)
          (t := (c j : Perm (Fin n)).support) ?_ ?_ (hsupp j))
        · exact Finset.disjoint_union_left.mpr ⟨hdisj' hij, hdisj' hlj⟩
        · intro x hx
          rw [Finset.mem_union, not_or] at hx
          exact hgfix x hx.1 hx.2
      rw [hgj.eq, mul_inv_cancel_right]
  have hinv : ∀ i, ∃ g : alternatingGroup (Fin n), ∃ a : ℤ, ¬ ((3 : ℕ) : ℤ) ∣ 1 - a ∧
      g * c i * g⁻¹ = c i ^ a := by
    intro i
    obtain ⟨g, hgc, -⟩ := hg i i
    exact ⟨g, 2, by norm_num, hgc⟩
  have hpair : ∀ i j, i ≠ j → ∃ g : alternatingGroup (Fin n),
      (∃ a b : ℤ, ¬ ((3 : ℕ) : ℤ) ∣ a * b - 1 ∧ g * c i * g⁻¹ = c i ^ a ∧
        g * c j * g⁻¹ = c j ^ b) ∨ (g * c i * g⁻¹ = c j ∧ g * c j * g⁻¹ = c i) := by
    intro i j hij
    obtain ⟨g, hgc, hgj⟩ := hg i j
    exact ⟨g, Or.inl ⟨2, 1, by norm_num, hgc, by rw [zpow_one]; exact hgj hij⟩⟩
  obtain ⟨v, -, -, -, hEA, hcard, hinj, hmap, hab⟩ :=
    exists_lift_of_weyl (by norm_num) π hπ hZ c hcp hc1 hcomm hind hinv hpair
  rw [Fintype.card_fin] at hcard
  refine ⟨hab, ⟨_, hEA, hcard, hinj, hmap⟩, fun T _ _ hT α _ hfix => ?_⟩
  have hker : ∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker := by
    intro t z hz
    have hzA : z ∈ (closure (Set.range c)).comap π := by
      rw [mem_comap, MonoidHom.mem_ker.mp hz]; exact one_mem _
    rw [MonoidHom.mem_ker, hfix t z hzA, MonoidHom.mem_ker.mp hz]
  obtain ⟨w, -, -, hwfix, hEA', hcard', hinj', hmap'⟩ :=
    exists_fixed_lift_of_weyl (by norm_num) π hπ hZ c hcp hc1 hcomm hind hinv hpair hT α hker hfix
  rw [Fintype.card_fin] at hcard'
  refine ⟨_, hEA', hcard', hinj', hmap', fun t x hx => ?_⟩
  induction hx using closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hwfix t i
  | one => exact map_one _
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]
  | inv y _ hy => rw [map_inv, hy]

end CFSG.LocalAnalysis.GorensteinLyons
