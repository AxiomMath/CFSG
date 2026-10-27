module

public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusCentralizer
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeQOddRestriction
public import CFSG.CharacterTheory.Semidihedral.Principal.ColumnAverageBound
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicNineFourGroupTraces

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem exists_scalar_of_fixed_line {G : Type*} [Group G] [Finite G]
    (θ : FiniteComplexRepresentation G) (P : Subgroup G) [Fintype P] {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G))
    (hdim : ∑ u : P, θ.character u = Nat.card P) :
    ∃ μ : ℂ, μ ^ orderOf g = 1 ∧ ∑ u : P, θ.character (g * u) = Nat.card P * μ := by
  set e := CFSG.LyonsUnitaryFour.subgroupAverage θ.representation P with he
  have hidem := CFSG.LyonsUnitaryFour.subgroupAverage_idempotent θ.representation P
  have hP0 : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have htr : ∀ x : G, LinearMap.trace ℂ θ.vector (θ.representation x * e) =
      (Nat.card P : ℂ)⁻¹ * ∑ u : P, θ.character (x * u) :=
    fun x => CFSG.LyonsUnitaryFour.trace_mul_subgroupAverage θ.representation P x
  have htr1 : LinearMap.trace ℂ θ.vector e = 1 := by
    have h := htr 1
    rw [map_one, one_mul] at h
    rw [h]
    simp only [one_mul]
    rw [hdim, inv_mul_cancel₀ hP0]
  have hrank : Module.finrank ℂ (LinearMap.range e) = 1 := by
    have h := (LinearMap.IsIdempotentElem.isProj_range e hidem).trace
    rw [htr1] at h
    exact_mod_cast h.symm
  have hcomm : θ.representation g * e = e * θ.representation g := by
    have hmemP : ∀ u ∈ P, g * u * g⁻¹ ∈ P := fun u hu =>
      (Subgroup.mem_normalizer_iff.mp hg u).mp hu
    have hmemP' : ∀ u ∈ P, g⁻¹ * u * g ∈ P := fun u hu => by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
      simpa using h
    let σ : P ≃ P :=
      { toFun := fun u => ⟨g * u * g⁻¹, hmemP u u.2⟩
        invFun := fun u => ⟨g⁻¹ * u * g, hmemP' u u.2⟩
        left_inv := fun u => Subtype.ext (by simp [mul_assoc])
        right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
    have hsum : ∑ u : P, θ.representation (g * u) =
        ∑ u : P, θ.representation ((u : G) * g) := by
      rw [← Equiv.sum_comp σ (fun u : P => θ.representation ((u : G) * g))]
      refine Finset.sum_congr rfl fun u _ => ?_
      change θ.representation (g * u) = θ.representation (g * u * g⁻¹ * g)
      rw [inv_mul_cancel_right]
    rw [he, CFSG.LyonsUnitaryFour.subgroupAverage, mul_smul_comm, smul_mul_assoc,
      Finset.mul_sum, Finset.sum_mul]
    congr 1
    simp only [← map_mul]
    exact hsum
  obtain ⟨b, hb0, hbspan⟩ := finrank_eq_one_iff'.mp hrank
  have hgb : θ.representation g (b : θ.vector) ∈ LinearMap.range e := by
    obtain ⟨v, hv⟩ := b.2
    refine ⟨θ.representation g v, ?_⟩
    have h := congrArg (fun T : Module.End ℂ θ.vector => T v) hcomm
    simp only [Module.End.mul_apply] at h
    rw [← h, hv]
  obtain ⟨μ, hμ⟩ := hbspan ⟨_, hgb⟩
  have hμ' : θ.representation g (b : θ.vector) = μ • (b : θ.vector) := by
    have h := congrArg Subtype.val hμ
    simp only [SetLike.val_smul] at h
    exact h.symm
  have hscalar : θ.representation g * e = μ • e := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨c, hc⟩ := hbspan ⟨e v, ⟨v, rfl⟩⟩
    have hc' : c • (b : θ.vector) = e v := congrArg Subtype.val hc
    rw [Module.End.mul_apply, LinearMap.smul_apply, ← hc', map_smul, hμ', smul_comm]
  refine ⟨μ, ?_, ?_⟩
  · have hpow : ∀ k : ℕ, θ.representation (g ^ k) (b : θ.vector) = μ ^ k • (b : θ.vector) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', map_mul, Module.End.mul_apply, ih, map_smul, hμ', smul_smul,
          pow_succ]
    have h := hpow (orderOf g)
    rw [pow_orderOf_eq_one, map_one, Module.End.one_apply] at h
    have h' : (μ ^ orderOf g - 1) • (b : θ.vector) = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd (Subtype.ext h'') hb0
  · have h := htr g
    rw [hscalar, map_smul, htr1, smul_eq_mul, mul_one] at h
    rw [h, mul_inv_cancel_left₀ hP0]

theorem norm_sq_character_le_card_centralizer {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) (g : G) :
    ‖(basis.representation χ).character g‖ ^ 2 ≤
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
  have h := CFSG.Wreathed.complete_complex_character_column_sum basis g g
  rw [CFSG.Wreathed.conjugatorCount_self] at h
  have hterm : ∀ l : basis.index, (basis.representation l).character g *
      starRingEnd ℂ ((basis.representation l).character g) =
        ((‖(basis.representation l).character g‖ ^ 2 : ℝ) : ℂ) := by
    intro l
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hterm] at h
  have h' : (∑ l : basis.index, ‖(basis.representation l).character g‖ ^ 2 : ℝ) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    exact_mod_cast h
  rw [← h']
  exact Finset.single_le_sum (f := fun l => ‖(basis.representation l).character g‖ ^ 2)
    (fun l _ => sq_nonneg _) (Finset.mem_univ χ)

theorem centralizer_eq_self_of_vanishing_character {G : Type*} [Group G] [Fintype G]
    (θ : FiniteComplexRepresentation G) (hfaith : Function.Injective θ.representation)
    (hrat : ∀ g, ∃ q : ℚ, θ.character g = q) (hcenter : Subgroup.center G = ⊥)
    {p : ℕ} (hp : p.Prime) (P : Subgroup G) (hP : Nat.card P = p) (hp2 : ¬ p ^ 2 ∣ Nat.card G)
    (hvan : ∀ x : G, p ∣ orderOf x → θ.character x = 0) (hdeg : Module.finrank ℂ θ.vector = p) :
    Subgroup.centralizer (P : Set G) = P := by
  have : Fact p.Prime := ⟨hp⟩
  have hθ1 : θ.character 1 = p := by
    rw [FiniteComplexRepresentation.character, Representation.char_one, hdeg]
  have hord : ∀ u : P, u ≠ 1 → orderOf (u : G) = p := fun u hu => by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime_of_mem_of_card_eq (H := ⊤) (by rw [Subgroup.card_top, hP])
      (Subgroup.mem_top u) hu
  have hdim : ∑ u : P, θ.character u = Nat.card P := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : P)), Finset.sum_eq_zero, add_zero,
      OneMemClass.coe_one, hθ1, hP]
    intro u hu
    exact hvan _ (by rw [hord u (Finset.ne_of_mem_erase hu)])
  have hcop : ∀ y ∈ Subgroup.centralizer (P : Set G), Nat.Coprime (orderOf y) p → y = 1 := by
    intro y hy hyp
    obtain ⟨μ, hμ, hsum⟩ := exists_scalar_of_fixed_line θ P
      (Subgroup.centralizer_le_normalizer _ hy) hdim
    have hsum' : ∑ u : P, θ.character (y * u) = θ.character y := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : P)), Finset.sum_eq_zero, add_zero,
        OneMemClass.coe_one, mul_one]
      intro u hu
      apply hvan
      have hcomm : Commute y (u : G) := (Subgroup.mem_centralizer_iff.mp hy u u.2).symm
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by
        rw [hord u (Finset.ne_of_mem_erase hu)]; exact hyp)]
      rw [hord u (Finset.ne_of_mem_erase hu)]
      exact dvd_mul_left p _
    rw [hsum', hP] at hsum
    obtain ⟨q, hq⟩ := hrat y
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hμq : μ = ((q / p : ℚ) : ℂ) := by
      push_cast
      rw [← hq, hsum]
      field_simp
    have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
    have hqp : q / p = 1 ∨ q / p = -1 := by
      have h1 : ((q / p) ^ orderOf y : ℚ) = 1 := by
        have h := hμ
        rw [hμq] at h
        exact_mod_cast h
      have habs : |q / p| = 1 := by
        have h2 : |q / p| ^ orderOf y = 1 := by rw [← abs_pow, h1, abs_one]
        exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hy0).mp h2
      exact (abs_eq zero_le_one).mp habs
    have hp0' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    rcases hqp with h | h
    ·
      have hθy : θ.character y = θ.character 1 := by
        rw [hq, hθ1]
        have : q = p := by
          field_simp at h
          linarith
        rw [this]
        push_cast
        rfl
      by_contra hy1
      exact character_ne_one_of_not_mem_ker θ (g := y) (fun hmem =>
        hy1 (hfaith (by rw [MonoidHom.mem_ker.mp hmem, map_one]))) hθy
    ·
      exfalso
      have hqv : q = -p := by
        field_simp at h
        linarith
      have hneg : -θ.representation y = 1 := by
        apply CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank _ (n := 2 * orderOf y)
          (by positivity)
        · have hy2 : (y ^ 2) ^ orderOf y = 1 := by
            rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
          rw [pow_mul, neg_sq, ← map_pow, ← map_pow, hy2, map_one]
        · rw [map_neg, hdeg]
          change -θ.character y = _
          rw [hq, hqv]
          push_cast
          ring
      have hρy : θ.representation y = -1 := by
        rw [← neg_neg (θ.representation y), hneg]
      have hyc : y ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply hfaith
        rw [map_mul, map_mul, hρy, neg_one_mul, mul_neg_one]
      rw [hcenter, Subgroup.mem_bot] at hyc
      rw [hyc, map_one] at hρy
      have hV : Nontrivial θ.vector := Module.nontrivial_of_finrank_pos (by rw [hdeg]; exact hp.pos)
      obtain ⟨v, hv⟩ := exists_ne (0 : θ.vector)
      have h2 := congrArg (fun T : Module.End ℂ θ.vector => T v) hρy
      simp only [Module.End.one_apply, LinearMap.neg_apply] at h2
      have h3 : (2 : ℂ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; rw [neg_add_cancel]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · norm_num at h4
      · exact hv h4
  have hpgrp : IsPGroup p (Subgroup.centralizer (P : Set G)) := by
    rw [IsPGroup.iff_orderOf]
    intro x
    set k := p ^ (orderOf (x : G)).factorization p with hk
    have hkdvd : k ∣ orderOf (x : G) := Nat.ordProj_dvd _ _
    have hk0 : k ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hx1 := hcop ((x : G) ^ k) (Subgroup.pow_mem _ x.2 k) (by
      rw [orderOf_pow_of_dvd hk0 hkdvd]
      exact (Nat.coprime_ordCompl hp (orderOf_pos _).ne').symm)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hx1)
    exact ⟨j, by rw [← Subgroup.orderOf_coe, hj]⟩
  have hPC : P ≤ Subgroup.centralizer (P : Set G) := by
    have : IsCyclic P := isCyclic_of_prime_card hP
    intro x hx y hy
    exact congrArg Subtype.val (IsCyclic.isMulCommutative.is_comm.comm (⟨y, hy⟩ : P) ⟨x, hx⟩)
  symm
  apply Subgroup.eq_of_le_of_card_ge hPC
  obtain ⟨n, hn⟩ := hpgrp.exists_card_eq
  rw [hn, hP]
  have hdvd : p ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card _
  have hn1 : n ≤ 1 := by
    by_contra hn1
    push Not at hn1
    exact hp2 ((pow_dvd_pow p hn1).trans hdvd)
  calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hn1
    _ = p := pow_one p

theorem conj_eq_inv_of_involution_mem_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (P : Subgroup G) (hP : Nat.card P = p) {v : G}
    (hvN : v ∈ Subgroup.normalizer (P : Set G)) (hv2 : v ^ 2 = 1)
    (hvC : v ∉ Subgroup.centralizer (P : Set G)) : ∀ u ∈ P, v * u * v⁻¹ = u⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  have hgo : orderOf (g : G) = p := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hP]
  have hgen : ∀ u ∈ P, ∃ j : ℤ, (g : G) ^ j = u := by
    intro u hu
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨u, hu⟩)
    exact ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hv2)
  obtain ⟨k, hk⟩ := hgen _ ((Subgroup.mem_normalizer_iff.mp hvN g).mp g.2)
  have hvv : (g : G) ^ (k * k) = (g : G) ^ (1 : ℤ) := by
    rw [zpow_mul, hk, conj_zpow, hk, zpow_one]
    calc v * (v * ↑g * v⁻¹) * v⁻¹ = (v * v) * ↑g * (v⁻¹ * v⁻¹) := by group
      _ = ↑g := by rw [hvinv, ← sq, hv2, one_mul, mul_one]
  rw [zpow_eq_zpow_iff_modEq, hgo] at hvv
  have hdvd : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    have h := Int.ModEq.dvd hvv.symm
    have h' : (k - 1) * (k + 1) = k * k - 1 := by ring
    rw [h']
    exact h
  rcases Int.Prime.dvd_mul' hp hdvd with h1 | h1
  · exfalso
    apply hvC
    have hfix : v * (g : G) * v⁻¹ = g := by
      rw [← hk]
      conv_rhs => rw [← zpow_one (g : G)]
      apply zpow_eq_zpow_iff_modEq.mpr
      rw [hgo]
      exact (Int.modEq_iff_dvd.mpr h1).symm
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨j, rfl⟩ := hgen u hu
    have h' : v * (g : G) ^ j * v⁻¹ = (g : G) ^ j := by rw [← conj_zpow, hfix]
    calc (g : G) ^ j * v = v * (g : G) ^ j * v⁻¹ * v := by rw [h']
      _ = v * (g : G) ^ j := by group
  · intro u hu
    obtain ⟨j, rfl⟩ := hgen u hu
    rw [← conj_zpow, ← hk, ← zpow_mul, ← zpow_neg]
    apply zpow_eq_zpow_iff_modEq.mpr
    rw [hgo]
    apply (Int.modEq_iff_dvd).mpr
    have h' : -j - k * j = -(j * (k + 1)) := by ring
    rw [h']
    exact (Int.dvd_neg).mpr (Dvd.dvd.mul_left h1 j)

theorem isCyclic_of_le_normalizer_of_inf_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (P Q : Subgroup G) (hP : Nat.card P = p)
    (hQN : Q ≤ Subgroup.normalizer (P : Set G))
    (hQC : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥) : IsCyclic Q := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  let φ : Q →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hQN)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxC : (x : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h := congrArg (fun ψ : MulAut P => ((ψ ⟨u, hu⟩ : P) : G)) (MonoidHom.mem_ker.mp hx)
      change ((P.normalizerMonoidHom (Subgroup.inclusion hQN x)) ⟨u, hu⟩ : G) = u at h
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] at h
      calc u * (x : G) = (x : G) * u * (x : G)⁻¹ * x := by rw [h]
        _ = x * u := by group
    have hmem : (x : G) ∈ Q ⊓ Subgroup.centralizer (P : Set G) := ⟨x.2, hxC⟩
    rw [hQC, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hAut : IsCyclic (MulAut P) := by
    let autEquiv : MulAut P ≃* (ZMod (Nat.card P))ˣ := IsCyclic.mulAutMulEquiv (G := P)
    have hUnits : IsCyclic (ZMod (Nat.card P))ˣ := by
      rw [hP]
      exact ZMod.isCyclic_units_prime hp
    exact isCyclic_of_injective autEquiv.toMonoidHom autEquiv.injective
  exact isCyclic_of_injective φ hφinj

theorem isCyclic_of_card_nine_of_nineteen_column {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (hcenter : Subgroup.center G = ⊥)
    (h19 : (Nat.card G).factorization 19 = 1) (h3 : (Nat.card G).factorization 3 = 2)
    (χ₁ : basis.index) (hfaith : Function.Injective (basis.representation χ₁).representation)
    (hrat : ∀ g, ∃ q : ℚ, (basis.representation χ₁).character g = q)
    (hdeg : Module.finrank ℂ (basis.representation χ₁).vector = 19)
    (hvan : ∀ x : G, 19 ∣ orderOf x → (basis.representation χ₁).character x = 0)
    (hinvol : ∀ x : G, orderOf x = 2 → (basis.representation χ₁).character x = -5)
    (Λ : Finset basis.index) (hΛ : Λ.card = 5) (c : basis.index → ℂ)
    (hc : ∀ χ ∈ Λ, ∀ u : G, orderOf u = 19 → (basis.representation χ).character u = c χ)
    (hcnorm : ∀ χ ∈ Λ, ‖c χ‖ = 1) :
    ∀ Q : Subgroup G, Nat.card Q = 9 → IsCyclic Q := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp19 : Nat.Prime 19 := by norm_num
  obtain ⟨P⟩ : Nonempty (Sylow 19 G) := inferInstance
  have hP : Nat.card (P : Subgroup G) = 19 := by rw [Sylow.card_eq_multiplicity, h19, pow_one]
  have hp2 : ¬ 19 ^ 2 ∣ Nat.card G := by
    intro h
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp19 Nat.card_pos.ne').mp h
    omega
  have hCP : Subgroup.centralizer ((P : Subgroup G) : Set G) = P :=
    centralizer_eq_self_of_vanishing_character (basis.representation χ₁) hfaith hrat hcenter hp19
      P hP hp2 hvan hdeg
  have hord : ∀ u ∈ (P : Subgroup G), u ≠ 1 → orderOf u = 19 := fun u hu hu1 =>
    orderOf_eq_prime_of_mem_of_card_eq hP hu hu1
  have hθ1 : (basis.representation χ₁).character 1 = 19 := by
    rw [FiniteComplexRepresentation.character, Representation.char_one, hdeg]
    norm_num
  have hdim : ∑ u : (P : Subgroup G), (basis.representation χ₁).character u =
      Nat.card (P : Subgroup G) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : (P : Subgroup G))), Finset.sum_eq_zero,
      add_zero, OneMemClass.coe_one, hθ1, hP]
    · norm_num
    intro u hu
    exact hvan _ (by rw [hord u u.2 (fun h => Finset.ne_of_mem_erase hu (Subtype.ext h))])
  set N := Subgroup.normalizer ((P : Subgroup G) : Set G) with hNdef
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hNcard : Nat.card N = 19 * (P : Subgroup G).relIndex N := by
    have h := Subgroup.card_mul_index ((P : Subgroup G).subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv, hP] at h
    exact h.symm
  set e := (P : Subgroup G).relIndex N with he
  have he18 : e ∣ 18 := by
    have : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card hP
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (P : Subgroup G).normalizerMonoidHom.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      Subgroup.normalizerMonoidHom_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer _)).toEquiv, hCP, hP, hNcard] at h1
    have hrange : Nat.card (P : Subgroup G).normalizerMonoidHom.range = e := by
      have : 19 * e = 19 * Nat.card (P : Subgroup G).normalizerMonoidHom.range := by
        rw [h1]
        ring
      omega
    rw [← hrange]
    have h18 : Nat.card (MulAut (P : Subgroup G)) = 18 := by
      rw [IsCyclic.card_mulAut, hP, Nat.totient_prime hp19]
    rw [← h18]
    exact Subgroup.card_subgroup_dvd_card _
  have heodd : ¬ 2 ∣ e := by
    intro h2
    have hN2 : 2 ∣ Nat.card N := hNcard ▸ Dvd.dvd.mul_left h2 19
    have : Fintype N := Fintype.ofFinite N
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card (G := N) 2
      (by rwa [← Nat.card_eq_fintype_card])
    have hv2 : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe, hv]
    have hvC : (v : G) ∉ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
      rw [hCP]
      intro hvP
      have := Subgroup.orderOf_dvd_natCard _ hvP
      rw [hv2, hP] at this
      norm_num at this
    have hvsq : (v : G) ^ 2 = 1 := by rw [← hv2]; exact pow_orderOf_eq_one _
    have hinvP := conj_eq_inv_of_involution_mem_normalizer hp19 P hP v.2 hvsq hvC
    obtain ⟨μ, hμ, hsum⟩ := exists_scalar_of_fixed_line (basis.representation χ₁) P v.2 hdim
    have hvu : ∀ u : (P : Subgroup G), (basis.representation χ₁).character ((v : G) * u) = -5 := by
      intro u
      apply hinvol
      have hvinv : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hvsq)
      have hsq : ((v : G) * u) ^ 2 = 1 := by
        rw [sq]
        calc (v : G) * u * ((v : G) * u) = ((v : G) * u * (v : G)⁻¹) * u := by rw [hvinv]; group
          _ = 1 := by rw [hinvP u u.2, inv_mul_cancel]
      have hne : (v : G) * u ≠ 1 := by
        intro h1
        have hvP : (v : G) ∈ (P : Subgroup G) := by
          rw [mul_eq_one_iff_eq_inv.mp h1]
          exact (P : Subgroup G).inv_mem u.2
        exact hvC (by rw [hCP]; exact hvP)
      exact orderOf_eq_prime hsq hne
    simp only [hvu, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hP,
      nsmul_eq_mul] at hsum
    rw [hv2] at hμ
    have hμ5 : μ = -5 := by
      have h19c : (19 : ℂ) ≠ 0 := by norm_num
      push_cast at hsum
      have h' : (19 : ℂ) * μ = 19 * (-5) := by linear_combination (-1 : ℂ) * hsum
      exact mul_left_cancel₀ h19c h'
    rw [hμ5] at hμ
    norm_num at hμ
  have he5 : 5 ≤ e := by
    have hPcyc : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card hP
    have hle : e ≤ 18 := Nat.le_of_dvd (by norm_num) he18
    have he17 : e < 19 - 1 := by
      rcases Nat.lt_or_ge e 18 with h | h
      · exact h
      · exfalso
        have : e = 18 := le_antisymm hle h
        rw [this] at heodd
        exact heodd (by norm_num)
    obtain ⟨-, -, hbound⟩ := selfcentralizing_prime_subgroup_column_average_constant_row_bound
      basis hp19 P hPcyc hP hCP he Λ c
      (fun χ hχ u hu hu1 => hc χ hχ u (hord u hu hu1))
    have := hbound hcnorm he17
    omega
  have he9 : e = 9 := by
    have hle : e ≤ 18 := Nat.le_of_dvd (by norm_num) he18
    interval_cases e <;> first | rfl | omega
  have hN171 : Nat.card N = 171 := by rw [hNcard, he9]
  obtain ⟨Q₀⟩ : Nonempty (Sylow 3 N) := inferInstance
  have hQ₀card : Nat.card (Q₀ : Subgroup N) = 9 := by
    rw [Sylow.card_eq_multiplicity, hN171]
    have : (171 : ℕ).factorization 3 = 2 := by
      rw [show (171 : ℕ) = 3 ^ 2 * 19 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this]
    norm_num
  set Q₁ := (Q₀ : Subgroup N).map N.subtype with hQ₁
  have hQ₁card : Nat.card Q₁ = 9 := by
    rw [hQ₁, Subgroup.card_map_of_injective N.subtype_injective, hQ₀card]
  have hQ₁cyc : IsCyclic Q₁ := by
    apply isCyclic_of_le_normalizer_of_inf_centralizer hp19 P Q₁ hP (Subgroup.map_subtype_le _)
    rw [hCP, eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxP⟩ := Subgroup.mem_inf.mp hx
    have h9 := Subgroup.orderOf_dvd_natCard Q₁ hxQ
    have h19' := Subgroup.orderOf_dvd_natCard _ hxP
    rw [hQ₁card] at h9
    rw [hP] at h19'
    have := Nat.dvd_gcd h9 h19'
    rw [show Nat.gcd 9 19 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact Subgroup.mem_bot.mpr this
  intro Q hQ
  let SQ₁ : Sylow 3 G := Sylow.ofCard Q₁ (by rw [hQ₁card, h3]; norm_num)
  let SQ : Sylow 3 G := Sylow.ofCard Q (by rw [hQ, h3]; norm_num)
  have : IsCyclic (SQ₁ : Subgroup G) := hQ₁cyc
  have hcyc : IsCyclic (SQ : Subgroup G) :=
    isCyclic_of_surjective (Sylow.equiv SQ₁ SQ) (Sylow.equiv SQ₁ SQ).surjective
  exact hcyc

theorem card_sylow_five_fixed_eq_zero {Γ : Type*} [Group Γ] [Finite Γ] (L : Subgroup Γ)
    [IsSimpleGroup L] (hL60 : Nat.card L = 60) (hLidx : L.index = 2) {γ : Γ}
    (hγ : orderOf γ = 3) :
    Nat.card {P : Sylow 5 L // ((P : Subgroup L).map L.subtype).map
      (MulAut.conj γ).toMonoidHom = (P : Subgroup L).map L.subtype} = 0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hγL : γ ∈ L := by
    have h2 : L.relIndex ⊤ = 2 := by rw [Subgroup.relIndex_top_right, hLidx]
    have hle := le_of_odd_card_of_relIndex_eq_two h2 (le_top : Subgroup.zpowers γ ≤ ⊤)
      (by rw [Nat.card_zpowers, hγ]; decide)
    exact hle (Subgroup.mem_zpowers γ)
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨P, hP⟩ => ?_⟩
  have hnorm : (⟨γ, hγL⟩ : L) ∈ Subgroup.normalizer ((P : Subgroup L) : Set L) := by
    have hfwd : ∀ x : L, x ∈ (P : Subgroup L) → (⟨γ, hγL⟩ : L) * x * (⟨γ, hγL⟩ : L)⁻¹ ∈
        (P : Subgroup L) := by
      intro x hx
      have hmem : γ * (x : Γ) * γ⁻¹ ∈ ((P : Subgroup L).map L.subtype).map
          (MulAut.conj γ).toMonoidHom := ⟨x, ⟨x, hx, rfl⟩, by simp⟩
      rw [hP] at hmem
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
      have : y = (⟨γ, hγL⟩ : L) * x * (⟨γ, hγL⟩ : L)⁻¹ := Subtype.ext (by simpa using hyx)
      exact this ▸ hy
    have hbwd : ∀ x : L, x ∈ (P : Subgroup L) → (⟨γ, hγL⟩ : L)⁻¹ * x * (⟨γ, hγL⟩ : L) ∈
        (P : Subgroup L) := by
      intro x hx
      have hmem : (x : Γ) ∈ ((P : Subgroup L).map L.subtype).map
          (MulAut.conj γ).toMonoidHom := by
        rw [hP]
        exact ⟨x, hx, rfl⟩
      obtain ⟨z, ⟨y, hy, rfl⟩, hzx⟩ := hmem
      have : y = (⟨γ, hγL⟩ : L)⁻¹ * x * (⟨γ, hγL⟩ : L) := Subtype.ext (by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype] at hzx
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hzx]
        group)
      exact this ▸ hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd x, fun hx => ?_⟩
    have h := hbwd _ hx
    simpa [mul_assoc] using h
  have hPcard : Nat.card (P : Subgroup L) = 5 := by
    rw [Sylow.card_eq_multiplicity, hL60]
    have : (60 : ℕ).factorization 5 = 1 := by
      rw [show (60 : ℕ) = 5 ^ 1 * 12 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow (by norm_num),
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this, pow_one]
  have hmod0 := card_sylow_modEq_one 5 L
  rw [Sylow.card_eq_index_normalizer P] at hmod0
  have hmod : (Subgroup.normalizer ((P : Subgroup L) : Set L)).index % 5 = 1 % 5 := hmod0
  have hcm := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup L) : Set L))
  rw [hL60] at hcm
  have h5 : 5 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup L) : Set L)) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup L)))
    rw [hPcard] at h
    exact h
  have hnot1 : (Subgroup.normalizer ((P : Subgroup L) : Set L)).index ≠ 1 := by
    intro h1
    have htop := Subgroup.index_eq_one.mp h1
    have hn : (P : Subgroup L).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup L) with hb | ht
    · rw [hb, Subgroup.card_bot] at hPcard
      norm_num at hPcard
    · rw [ht, Subgroup.card_top, hL60] at hPcard
      norm_num at hPcard
  obtain ⟨m, hm⟩ := h5
  rw [hm] at hcm
  have hN10 : Nat.card (Subgroup.normalizer ((P : Subgroup L) : Set L)) = 10 := by
    have hmi : m * (Subgroup.normalizer ((P : Subgroup L) : Set L)).index = 12 := by
      have : 5 * (m * (Subgroup.normalizer ((P : Subgroup L) : Set L)).index) = 5 * 12 := by
        rw [← mul_assoc, hcm]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    have hm12 : m ≤ 12 := Nat.le_of_dvd (by norm_num) (Dvd.intro _ hmi)
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hmi)
    rw [hm]
    interval_cases m <;> omega
  have hdvd := Subgroup.orderOf_dvd_natCard _ hnorm
  rw [hN10, Subgroup.orderOf_mk, hγ] at hdvd
  norm_num at hdvd


theorem local_parameter_five_trivial_core_nineteen_excluded_of_family
    {G : Type} [Group G]
    [Fintype G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = 5) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hOF : ActualPrincipalOrderFormulas G t (fS (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector))
    (hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G), v ≠ 1 →
      ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t)
    (hN : N t = ⊥) : Nat.card G ≠ 68400 := by
  intro hG68400
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hn4, hCt, -, hrows⟩ := local_parameter_five_rows_of_family n hn S fS t ht hnonab
    hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal q hq e he φ δ₁
    δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg hOF
  have hNcard : Nat.card (N t) = 1 := by rw [hN, Subgroup.card_bot]
  have ha1 : Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
      (N t)) = 1 := Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.card_subgroup_dvd_card _)
  have hb1 : (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
      (N t)).index = 1 := Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.index_dvd_card _)
  rw [ha1, hb1, mul_one] at hCt
  rcases hrows with ⟨hδ₁, hδ₂, hδ₃, hf₁, hf₂, hf₃, -⟩ | ⟨-, -, -, -, -, -, hX⟩ |
    ⟨-, -, -, -, -, -, hX⟩
  rotate_left
  · have h := congrArg Prod.fst hX
    simp only [ha1, hb1] at h
    omega
  · have h := congrArg Prod.fst hX
    simp only [ha1, hb1] at h
    omega
  subst hq
  have he1 : e = 1 := by rw [he]; rfl
  subst he1 hδ₁ hδ₂ hδ₃ hn4
  obtain ⟨hlφ, -, -, -, -, hnd, -, hνinj, hψx, hνx, hνψ, hB, -, -, hsec, hrel⟩ := hfam
  obtain ⟨-, -, -, -, -, -, hf₄, -, -⟩ := hdeg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨lφ, hlφB, -, hφchar, hφdeg, hφker⟩ := hlφ
  have hφ1 : φ 1 = 5 := by
    rw [← hφchar, (basis_character_one localBasis lφ).1, hφdeg]
    norm_num
  obtain ⟨hsec₁, hsec₂, -⟩ := hsec 1 (by rw [orderOf_one]; exact odd_one)
  rw [OneMemClass.coe_one, mul_one, hφ1] at hsec₁ hsec₂
  have htval₁ : (basis.representation χ₁).character t = -5 := by rw [hsec₁]; norm_num
  have htval₂ : (basis.representation χ₂).character t = -5 := by rw [hsec₂]; norm_num
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hdeg1 : ∀ c : basis.index, (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) :=
    fun c => (basis_character_one basis c).1
  have hχ₁1 : (basis.representation χ₁).character 1 = 19 := by rw [hdeg1, hf₁]; norm_num
  have hχ₂1 : (basis.representation χ₂).character 1 = 75 := by rw [hdeg1, hf₂]; norm_num
  obtain ⟨hψ1, hν1, -, -⟩ := hrel 1 (by rw [orderOf_one]; exact odd_one)
  have hψdeg : ∀ j ∈ Finset.Icc 1 (2 ^ (4 - 3) - 1),
      (basis.representation (ψ j)).character 1 = 18 := by
    intro j hj
    rw [hψ1 j hj, hχ₁1]
    norm_num
  have hνdeg : ∀ i ∈ Finset.range (2 ^ (4 - 3)),
      (basis.representation (ν i)).character 1 = 18 := by
    intro i hi
    rw [hν1 i hi, hχ₁1]
    norm_num
  have h76 : (Module.finrank ℂ (basis.representation χ₄).vector : ℂ) = 76 := by
    have h : (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = 76 := by
      rw [hf₄, hf₂]
      norm_num
    exact_mod_cast h
  have hdegB : ∀ b ∈ B, (basis.representation b).character 1 = 1 ∨
      (basis.representation b).character 1 = 18 ∨ (basis.representation b).character 1 = 57 ∨
      (basis.representation b).character 1 = 76 ∨ b = χ₁ ∨ b = χ₂ := by
    intro b hb
    have hb' : b ∈ B := hb
    rw [hB] at hb'
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at hb'
    rcases hb' with ((h | h | h | h | h) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
    · left
      rw [h, hprincipal]
      rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · right; right; left
      rw [h, hdeg1, hf₃]
      norm_num
    · right; right; right; left
      rw [h, hdeg1, h76]
    · right; left
      exact hψdeg j hj
    · right; left
      exact hνdeg i hi
  have hratOf : ∀ (χ : basis.index) (d : ℕ), χ ∈ B → (basis.representation χ).character 1 = d →
      d ≠ 1 → d ≠ 18 → d ≠ 57 → d ≠ 76 →
      ((basis.representation χ₁).character 1 = d → χ = χ₁) →
      ((basis.representation χ₂).character 1 = d → χ = χ₂) →
      ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q := by
    intro χ d hχB hχd hd1 hd18 hd57 hd76 h1 h2 g
    apply CFSG.LyonsUnitaryFour.character_rat_of_isolated_principal_block basis ideal hprincipal
      hχB {1} (fun x hx => ⟨d, by rw [Set.mem_singleton_iff.mp hx, hχd]; norm_num⟩)
    intro b hb hbval
    have hb1 := hbval 1 (Set.mem_singleton 1)
    rw [hχd] at hb1
    rcases hdegB b hb with h | h | h | h | h | h
    · rw [h] at hb1
      exact absurd (by exact_mod_cast hb1.symm) hd1
    · rw [h] at hb1
      exact absurd (by exact_mod_cast hb1.symm) hd18
    · rw [h] at hb1
      exact absurd (by exact_mod_cast hb1.symm) hd57
    · rw [h] at hb1
      exact absurd (by exact_mod_cast hb1.symm) hd76
    · rw [h] at hb1 ⊢
      exact (h1 hb1).symm
    · rw [h] at hb1 ⊢
      exact (h2 hb1).symm
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hrat₁ : ∀ g, ∃ q : ℚ, (basis.representation χ₁).character g = q :=
    hratOf χ₁ 19 hχ₁B (by rw [hχ₁1]; norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (fun _ => rfl) (fun h => by rw [hχ₂1] at h; norm_num at h)
  have hrat₂ : ∀ g, ∃ q : ℚ, (basis.representation χ₂).character g = q :=
    hratOf χ₂ 75 hχ₂B (by rw [hχ₂1]; norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (fun h => by rw [hχ₁1] at h; norm_num at h) (fun _ => rfl)
  have hfaith : Function.Injective (basis.representation χ₁).representation := by
    rcases (MonoidHom.normal_ker (basis.representation χ₁).representation).eq_bot_or_eq_top
      with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).mp h
    · exfalso
      have htker : t ∈ MonoidHom.ker (basis.representation χ₁).representation := h ▸ trivial
      have h1 : (basis.representation χ₁).character t =
          (basis.representation χ₁).character 1 := by
        change LinearMap.trace ℂ _ ((basis.representation χ₁).representation t) =
          LinearMap.trace ℂ _ ((basis.representation χ₁).representation 1)
        rw [MonoidHom.mem_ker.mp htker, (basis.representation χ₁).representation.map_one]
      rw [htval₁, hχ₁1] at h1
      norm_num at h1
  have hinvol : ∀ (χ : basis.index) (x : G), orderOf x = 2 →
      (basis.representation χ).character x = (basis.representation χ).character t := by
    intro χ x hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_orderOf_eq_two le_rfl S fS ht hx)
    rw [← hg]
    exact (Representation.char_conj (basis.representation χ).representation x g).symm
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hGnonab
      have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hfac19 : (Nat.card G).factorization 19 = 1 := by
    rw [hG68400, show (68400 : ℕ) = 19 ^ 1 * 3600 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfac3 : (Nat.card G).factorization 3 = 2 := by
    rw [hG68400, show (68400 : ℕ) = 3 ^ 2 * 7600 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨⟨ideal19, hmax19, h19⟩, hchar19⟩ :=
    CFSG.BlockBasics.residue_prime_existence 19 (by norm_num)
  have : ideal19.IsMaximal := hmax19
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal19) 19 := hchar19 ideal19 hmax19 h19
  have hvan₁ := (full_prime_part_character_degree_singleton_block_singular_vanishing basis ideal19
    19 χ₁ (by rw [hfac19, pow_one, hf₁])).2
  have hvan₃ := (full_prime_part_character_degree_singleton_block_singular_vanishing basis ideal19
    19 χ₃ (by rw [hfac19, pow_one, hf₃]; norm_num)).2
  have hodd19 : ∀ u : G, orderOf u = 19 → Odd (orderOf u) := fun u hu => by
    rw [hu]
    decide
  have hval19 : ∀ u : G, orderOf u = 19 → (basis.representation χ₁).character u = 0 ∧
      (basis.representation χ₃).character u = 0 := fun u hu =>
    ⟨hvan₁ u (by rw [hu]), hvan₃ u (by rw [hu])⟩
  have hχ₂19 : ∀ u : G, orderOf u = 19 → (basis.representation χ₂).character u = -1 := by
    intro u hu
    obtain ⟨-, -, hlin, -⟩ := hrel u (hodd19 u hu)
    rw [(hval19 u hu).1, (hval19 u hu).2] at hlin
    push_cast at hlin
    linear_combination hlin
  have hψ19 : ∀ u : G, orderOf u = 19 → (basis.representation (ψ 1)).character u = -1 := by
    intro u hu
    obtain ⟨hψ, -, -, -⟩ := hrel u (hodd19 u hu)
    rw [hψ 1 (by simp), (hval19 u hu).1]
    norm_num
  have hν19 : ∀ i ∈ Finset.range 2, ∀ u : G, orderOf u = 19 →
      (basis.representation (ν i)).character u = -1 := by
    intro i hi u hu
    obtain ⟨-, hν, -, -⟩ := hrel u (hodd19 u hu)
    rw [hν i (by simpa using hi), (hval19 u hu).1]
    norm_num
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or] at hnd'
  obtain ⟨⟨-, hp2, -, -⟩, -⟩ := hnd'
  obtain ⟨hψp, -, hψ2, -, -⟩ := hψx 1 (by simp)
  obtain ⟨hν0p, -, hν02, -, -⟩ := hνx 0 (by simp)
  obtain ⟨hν1p, -, hν12, -, -⟩ := hνx 1 (by simp)
  have hν0ψ := hνψ 0 (by simp) 1 (by simp)
  have hν1ψ := hνψ 1 (by simp) 1 (by simp)
  have hν01 : ν 0 ≠ ν 1 := fun h => by
    have := hνinj (by simp : (0 : ℕ) ∈ (Finset.range (2 ^ (4 - 3)) : Set ℕ))
      (by simp : (1 : ℕ) ∈ (Finset.range (2 ^ (4 - 3)) : Set ℕ)) h
    norm_num at this
  set Λ : Finset basis.index := [principal, χ₂, ψ 1, ν 0, ν 1].toFinset with hΛdef
  have hΛnd : [principal, χ₂, ψ 1, ν 0, ν 1].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true, not_or]
    exact ⟨⟨hp2, Ne.symm hψp, Ne.symm hν0p, Ne.symm hν1p⟩, ⟨Ne.symm hψ2, Ne.symm hν02,
      Ne.symm hν12⟩, ⟨Ne.symm hν0ψ, Ne.symm hν1ψ⟩, hν01, not_false⟩
  have hΛcard : Λ.card = 5 := by rw [hΛdef, List.toFinset_card_of_nodup hΛnd]; rfl
  set c : basis.index → ℂ := fun χ => if χ = principal then 1 else -1 with hcdef
  have hc : ∀ χ ∈ Λ, ∀ u : G, orderOf u = 19 → (basis.representation χ).character u = c χ := by
    intro χ hχ u hu
    rw [hΛdef, List.mem_toFinset] at hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with h | h | h | h | h
    · rw [h, hprincipal]
      simp [hcdef]
    · rw [h, hχ₂19 u hu]
      simp [hcdef, Ne.symm hp2]
    · rw [h, hψ19 u hu]
      simp [hcdef, hψp]
    · rw [h, hν19 0 (by simp) u hu]
      simp [hcdef, hν0p]
    · rw [h, hν19 1 (by simp) u hu]
      simp [hcdef, hν1p]
  have hcnorm : ∀ χ ∈ Λ, ‖c χ‖ = 1 := by
    intro χ _
    simp only [hcdef]
    split_ifs <;> simp
  have hcyc9 := isCyclic_of_card_nine_of_nineteen_column basis hcenter hfac19 hfac3 χ₁ hfaith
    hrat₁ hf₁ hvan₁ (fun x hx => by rw [hinvol χ₁ x hx, htval₁]) Λ hΛcard c hc hcnorm
  obtain ⟨-, ht2, -, hsC, -, -⟩ := supplied_t_s_facts le_rfl fS ht
  have hnode2 := perfect_parameter_five_trivial_core_three_torus_inversion_normalizer 4 le_rfl S
    fS t ht hnonab hcentral hnc hmodel hN
  obtain ⟨-, -, -, hW3, ⟨hsup, -, -⟩, hD12, hCK, -, -, -, -, -, -, hMH, hM72, -, -⟩ := hnode2
  have hnode4 := perfect_parameter_five_trivial_core_three_torus_centralizer_quotient 4 le_rfl S
    fS t ht hnonab hcentral hnc hmodel hN
  obtain ⟨-, -, -, -, -, hbound⟩ := hnode4
  set s₀ : G := (fS (s 4) : G) with hs₀
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ with hVdef
  have hV : IsKleinFour V := supplied_four_group_isKleinFour le_rfl fS ht
  set D := Subgroup.centralizer (V : Set G) with hDdef
  set W := (CFSG.pPrimeCore 2 D).map D.subtype with hWdef
  have hWD : W ≤ D := hsup ▸ le_sup_right
  obtain ⟨-, -, -, -, hchar⟩ := klein_centralizer_twelve_core V W hV hD12 hWD hW3
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hDC : D ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx t htV).symm
  set M := Subgroup.normalizer (V : Set G) with hMdef
  obtain ⟨Q⟩ : Nonempty (Sylow 3 M) := inferInstance
  have hQcard : Nat.card (Q : Subgroup M) = 9 := by
    rw [Sylow.card_eq_multiplicity, hM72]
    have : (72 : ℕ).factorization 3 = 2 := by
      rw [show (72 : ℕ) = 3 ^ 2 * 8 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this]
    norm_num
  set QG := (Q : Subgroup M).map M.subtype with hQGdef
  have hQGcard : Nat.card QG = 9 := by
    rw [hQGdef, Subgroup.card_map_of_injective M.subtype_injective, hQcard]
  have : IsCyclic QG := hcyc9 QG hQGcard
  obtain ⟨g₉, hg₉⟩ := IsCyclic.exists_generator (α := QG)
  set c : G := (g₉ : G) with hcdef'
  have hc9 : orderOf c = 9 := by
    rw [hcdef', Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₉, hQGcard]
  have hcM : c ∈ M := Subgroup.map_subtype_le _ g₉.2
  have hD12' : Nat.card D = 12 := hD12
  have hcenterV : ∀ x : M, V.normalizerMonoidHom x = 1 → (x : G) ∈ D := by
    intro x hx v hv
    have h := congrArg (fun ψ : MulAut V => ((ψ ⟨v, hv⟩ : V) : G)) hx
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h
    calc v * (x : G) = (x : G) * v * (x : G)⁻¹ * x := by rw [h]
      _ = x * v := by group
  have hφ : orderOf (V.normalizerMonoidHom ⟨c, hcM⟩) = 3 := by
    have h9 : orderOf (V.normalizerMonoidHom ⟨c, hcM⟩) ∣ 9 :=
      (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk, hc9])
    have h6 : orderOf (V.normalizerMonoidHom ⟨c, hcM⟩) ∣ 6 := by
      rw [← (CFSG.Semidihedral.Local.kleinFour_automorphism_action (V := V)).2.1]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (V.normalizerMonoidHom ⟨c, hcM⟩) ∣ 3 := by
      have := Nat.dvd_gcd h9 h6
      rwa [show Nat.gcd 9 6 = 3 by norm_num] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3'
    · exfalso
      have hcD := hcenterV ⟨c, hcM⟩ (orderOf_eq_one_iff.mp h1)
      have hdvd := Subgroup.orderOf_dvd_natCard D hcD
      rw [hc9, hD12'] at hdvd
      norm_num at hdvd
    · exact h3'
  set w : G := c ^ 3 with hwdef
  have hw3 : orderOf w = 3 := by
    rw [hwdef, orderOf_pow_of_dvd (by norm_num) (by rw [hc9]; norm_num), hc9]
  have hwD : w ∈ D := by
    have hpow : V.normalizerMonoidHom ⟨w, M.pow_mem hcM 3⟩ = 1 := by
      have h := pow_orderOf_eq_one (V.normalizerMonoidHom ⟨c, hcM⟩)
      rw [hφ, ← map_pow] at h
      exact h
    exact hcenterV _ hpow
  have hwW : w ∈ W := hchar w hwD (by rw [← hw3]; exact pow_orderOf_eq_one w)
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw3
    norm_num at hw3
  set L := CFSG.generalizedFitting (Gamma t) with hLdef
  have hL60 : Nat.card L = 60 := by
    obtain ⟨-, K, hK, hKfin, hKcard, ⟨eL⟩⟩ := hmodel
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inr (by rw [hKcard, pow_one]))
    rw [Nat.card_congr (eL.trans e5).toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hNZ : Nat.card (NZ t) = 2 := by
    have h : NZ t = Z t := by
      change N t ⊔ Z t = Z t
      rw [hN, bot_sup_eq]
    rw [h, Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact ht2
  have hΓ : Nat.card (Gamma t) = 120 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (NZ t)
    rw [hCt, hNZ] at h
    change 240 = Nat.card (Gamma t) * 2 at h
    omega
  have hLidx : L.index = 2 := by
    have h := Subgroup.card_mul_index L
    rw [hL60, hΓ] at h
    omega
  have hrig := local_degree_q_principal_odd_restriction_rigidity 4 le_rfl S fS hG t ht2 hnonab
    hcentral hnc 5 1 (by norm_num) (by decide) le_rfl hmodel ideal localBasis localPrincipal
    hlocalPrincipal lφ hlφB (by rw [hφdeg, pow_one]) hφker
  have hφ3 : ∀ y : C t, orderOf (y : G) = 3 → φ y = -1 := by
    intro y hy
    have hyord : orderOf y = 3 := by rw [← Subgroup.orderOf_coe, hy]
    have hyodd : Odd (orderOf y) := by rw [hyord]; decide
    have hκ : orderOf (kappa t y) = 3 := by
      have hne : kappa t y ≠ 1 := by
        intro h1
        have hmem : y ∈ NZ t := by
          rw [← QuotientGroup.ker_mk' (NZ t)]
          exact h1
        have hdvd := Subgroup.orderOf_dvd_natCard (NZ t) hmem
        rw [hyord, hNZ] at hdvd
        norm_num at hdvd
      apply orderOf_eq_prime _ hne
      rw [← map_pow, ← hyord, pow_orderOf_eq_one, map_one]
    have h := hrig y hyodd
    rw [← hφchar, h, card_sylow_five_fixed_eq_zero L hL60 hLidx hκ]
    norm_num
  have hχ₂3 : ∀ y : C t, orderOf (y : G) = 3 →
      (basis.representation χ₂).character (t * y) = 1 := by
    intro y hy
    have hyodd : Odd (orderOf y) := by rw [← Subgroup.orderOf_coe, hy]; decide
    obtain ⟨-, h2, -⟩ := hsec y hyodd
    rw [h2, hφ3 y hy]
    norm_num
  have hWC : W ≤ C t := hWD.trans hDC
  have hWord : ∀ x ∈ W, x ≠ 1 → orderOf x = 3 := fun x hx hx1 =>
    orderOf_eq_prime_of_mem_of_card_eq hW3 hx hx1
  have hb : ∀ v ∈ V, v ≠ 1 → (basis.representation χ₂).character (v * w) = 1 ∧
      (basis.representation χ₂).character (v * w ^ 2) = 1 := by
    intro v hv hv1
    obtain ⟨g, hgM, hg⟩ := hfus v hv hv1
    have hgH := hMH hgM
    have key : ∀ x ∈ W, x ≠ 1 → (basis.representation χ₂).character (v * x) = 1 := by
      intro x hx hx1
      have hgx : g * x * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgH x).mp hx
      have hgx1 : g * x * g⁻¹ ≠ 1 := by
        intro h
        apply hx1
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this
      have hconj : (basis.representation χ₂).character (v * x) =
          (basis.representation χ₂).character (g * (v * x) * g⁻¹) :=
        (Representation.char_conj (basis.representation χ₂).representation (v * x) g).symm
      have heq : g * (v * x) * g⁻¹ = t * (g * x * g⁻¹) := by
        rw [← hg]
        group
      rw [hconj, heq]
      exact hχ₂3 ⟨g * x * g⁻¹, hWC hgx⟩ (hWord _ hgx hgx1)
    have hw21 : w ^ 2 ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hw3] at this
      norm_num at this
    exact ⟨key w hwW hw1, key (w ^ 2) (W.pow_mem hwW 2) hw21⟩
  have ha : ∀ v ∈ V, v ≠ 1 → (basis.representation χ₂).character v = -5 := by
    intro v hv hv1
    have hv2 : v ^ 2 = 1 := by
      have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
      rw [hV.exponent_two] at h
      exact congrArg Subtype.val h
    rw [hinvol χ₂ v (orderOf_eq_prime hv2 hv1), htval₂]
  obtain ⟨-, -, x, hx, -, hxmod, -⟩ := cyclic_nine_four_group_rational_character_mod_thirty_six
    V hV.card_four c hcM hc9 hφ w rfl (basis.representation χ₂) hrat₂ (-5) 1 (by
      intro v hv hv1
      rw [ha v hv hv1]
      norm_num) (by
      intro v hv hv1
      rw [(hb v hv hv1).1, (hb v hv hv1).2]
      norm_num)
  rw [hf₂] at hxmod
  have hx15 : 21 ≤ x ∨ x ≤ -15 := by
    unfold Int.ModEq at hxmod
    omega
  have hcol := norm_sq_character_le_card_centralizer basis χ₂ w
  have hCw := hbound w hwW hw1
  rw [hx, Complex.norm_intCast, sq_abs] at hcol
  have hCw' : (Nat.card (Subgroup.centralizer ({w} : Set G)) : ℝ) ≤ 180 := by exact_mod_cast hCw
  have hx225 : (225 : ℝ) ≤ (x : ℝ) ^ 2 := by
    rcases hx15 with h | h
    · have h' : (21 : ℝ) ≤ x := by exact_mod_cast h
      nlinarith
    · have h' : (x : ℝ) ≤ -15 := by exact_mod_cast h
      nlinarith
  linarith


end CFSG.Semidihedral.Principal
