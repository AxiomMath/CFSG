module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ExactGL2OrderAlternativesSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.ExactGL2CharacterColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.OddKernelGL2ScaledOrders
public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ThreeProfile

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters

theorem central_ne_one_eq_neg_one (g : G23) (hg : g ∈ Subgroup.center G23) (h1 : g ≠ 1) :
    g = -1 := by
  rw [CFSG.Semidihedral.GL2ThreeStructure.centerH] at hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, CFSG.Semidihedral.GL2ThreeStructure.z_order] at h1 ⊢
  push_cast at h1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at h1
    exact absurd rfl h1
  · rw [h, zpow_one, GL2_three_neg_one_eq_Z]

theorem involution_class_sum_square {G : Type} [Group G] [Fintype G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {t : G} (ht : orderOf t = 2)
    {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G) :
    (∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), χ (u * v)) * χ 1 =
      (((Subgroup.centralizer ({t} : Set G)).index : ℂ) * χ t) ^ 2 := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  have hIconj : ∀ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ∀ g : G,
      g * u * g⁻¹ ∈ Finset.univ.filter (fun g : G => orderOf g = 2) := by
    intro u hu g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  have : ρ.IsIrreducible := hirr
  have h := GL2ScaledOrders.class_sum_square ρ (Finset.univ.filter fun g : G => orderOf g = 2)
    hIconj
  have hsum : ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ρ.character u =
      ((Finset.univ.filter fun g : G => orderOf g = 2).card : ℂ) * ρ.character t := by
    rw [Finset.sum_congr rfl fun u hu => ?_, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hinv t u ht (Finset.mem_filter.mp hu).2)
    exact Representation.char_conj _ t g
  have hIcard : ((Finset.univ.filter fun g : G => orderOf g = 2).card : ℂ) =
      (Subgroup.centralizer ({t} : Set G)).index := by
    exact_mod_cast GL2ScaledOrders.card_involutions_eq_index hinv ht
  rw [hsum, hIcard] at h
  exact h

theorem exact_GL2_centralizer_order_alternatives_core {G : Type} [Group G] [Fintype G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G)
    (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (a p b : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (ha : orderOf a = 8)
    (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (φ : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ)
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (hφ : let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)
      let ω : ℂ := ξ + ξ ^ 3
      let rep : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
        ![1, -1, a ^ 2, p, -1 * p, b, a, a⁻¹]
      let table : Fin 8 → Fin 8 → ℂ := ![![1, 1, 1, 1, 1, 1, 1, 1],
        ![1, 1, 1, 1, 1, -1, -1, -1], ![2, 2, 2, -1, -1, 0, 0, 0], ![3, 3, -1, 0, 0, -1, 1, 1],
        ![3, 3, -1, 0, 0, 1, -1, -1], ![4, -4, 0, 1, -1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, ω, -ω],
        ![2, -2, 0, -1, 1, 0, -ω, ω]]
      ∀ i j, φ i (rep j) = table i j) :
    let C := Subgroup.centralizer ({t} : Set G)
    let Φ : Fin 5 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ :=
      ![φ 0 + φ 2 - φ 4, φ 2 - φ 6, φ 6 - φ 7, φ 1 + φ 4 - φ 5, φ 1 + φ 2 - φ 3]
    let β : Fin 5 → G → ℂ := fun i => inducedFunction C (fun c => Φ i (π c))
    let identities : CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G →
        CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G → Prop :=
      fun χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ =>
        [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup ∧
        (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧ (χ₄ : G → ℂ) ≠ 1 ∧
        (χ₅ : G → ℂ) ≠ 1 ∧ (χ₆ : G → ℂ) ≠ 1 ∧ (χ₇ : G → ℂ) ≠ 1 ∧
        β 0 = 1 + ((χ₁ : G → ℂ) - χ₂) ∧ β 1 = (χ₁ : G → ℂ) - χ₃ ∧
        β 2 = (χ₃ : G → ℂ) - χ₄ ∧ β 3 = (χ₂ : G → ℂ) - χ₅ + χ₆ ∧
        β 4 = (χ₁ : G → ℂ) - χ₅ + χ₇ ∧
        ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
          ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
          ψ ≠ (χ₇ : G → ℂ) → ∀ g : G, Even (orderOf g) → ψ g = 0
    commutator G = ⊤ ∧
    Xor
      (Nat.card G = 7920 ∧
        ∃ χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G, identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ∧
          ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1, (χ₅ : G → ℂ) 1,
            (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![10, 11, 10, 10, 55, 44, 45] ∧
          (∃ ψ₁ ∈ CFSG.BlocksIrr G, ∃ ψ₂ ∈ CFSG.BlocksIrr G, ψ₁ ≠ ψ₂ ∧ ψ₁ 1 = 16 ∧ ψ₂ 1 = 16 ∧
            ∀ ψ ∈ CFSG.BlocksIrr G, ψ = 1 ∨ ψ = (χ₁ : G → ℂ) ∨ ψ = (χ₂ : G → ℂ) ∨
              ψ = (χ₃ : G → ℂ) ∨ ψ = (χ₄ : G → ℂ) ∨ ψ = (χ₅ : G → ℂ) ∨ ψ = (χ₆ : G → ℂ) ∨
              ψ = (χ₇ : G → ℂ) ∨ ψ = ψ₁ ∨ ψ = ψ₂) ∧
          (irreducibles_finite G).toFinset.val.map (fun ψ => ψ 1) =
            ({1, 10, 10, 10, 11, 16, 16, 44, 45, 55} : Multiset ℂ) ∧
          Nat.card (ConjClasses G) = 10)
      (Nat.card G = 5616 ∧
        ∃ χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G, identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ∧
          ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1, (χ₅ : G → ℂ) 1,
            (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![26, 27, 26, 26, 39, 12, 13] ∧
          (irreducibles_finite G).toFinset.val.map (fun ψ => ψ 1) =
            ({1, 12, 13, 16, 16, 16, 16, 26, 26, 26, 27, 39} : Multiset ℂ) ∧
          Nat.card (ConjClasses G) = 12) := by
  intro C Φ β identities
  have htC : GL2OddKernel.tC t ∈ Subgroup.center C :=
    Subgroup.mem_center_iff.mpr fun x => (GL2OddKernel.tC_comm t x).eq
  have hπt : π (GL2OddKernel.tC t) = -1 := by
    apply central_ne_one_eq_neg_one
    · rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨c, rfl⟩ := π.surjective h
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp htC c)]
    · intro h1
      have h2 : GL2OddKernel.tC t = 1 := π.injective (h1.trans (map_one π).symm)
      have h3 : t = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at ht
      norm_num at ht
  have hπt' : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1 := hπt
  have hφ' : ∀ i j, φ i (GL2OddKernel.rep a p b j) =
      (tableA i j : ℂ) + (tableB i j : ℂ) * omega8 := by
    intro i j
    have h : φ i (GL2OddKernel.rep a p b j) = GL2OddKernel.charTable
        (Complex.exp (2 * Real.pi * Complex.I / 8) +
          Complex.exp (2 * Real.pi * Complex.I / 8) ^ 3) i j := hφ i j
    rw [h, GL2OddKernel.charTable_eq, GL2OddKernel.exp_eq_xi]
  have hker : π.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr π.injective
  have hN : Odd (Nat.card π.toMonoidHom.ker) := by
    rw [hker, Subgroup.card_bot]
    exact odd_one
  have hπtM : π.toMonoidHom (GL2OddKernel.tC t) = -1 := hπt
  obtain ⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hnd, h1, h2, h3, h4, h5, h6, h7, hε, hε₁,
      hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4, hβodd, hrest⟩ :=
    odd_kernel_GL2_centralizer_produces_actual_characters t ht π.toMonoidHom π.surjective hN
      hπt' a p b ha hp hb hbz φ hφirr hφ
  have hvanish : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
      ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
      ψ ≠ (χ₇ : G → ℂ) → ∀ g : G, Even (orderOf g) → ψ g = 0 :=
    fun ψ hψ e0 e1 e2 e3 e4 e5 e6 e7 =>
      (hrest ψ hψ e0 e1 e2 e3 e4 e5 e6 e7).2 hker hinv
  obtain ⟨hvt, -, -⟩ := (exact_GL2_centralizer_produces_two_character_columns t ht π hπt' a p b
    ha hp hb hbz φ hφirr hφ).2 χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ ⟨hnd, h1, h2, h3, h4, h5, h6, h7,
      hε, hε₁, hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4⟩
  have v1 : (χ₁ : G → ℂ) t = 2 * ε := by simpa using congrFun hvt 0
  have v2 : (χ₂ : G → ℂ) t = 3 * ε := by simpa using congrFun hvt 1
  have v5 : (χ₅ : G → ℂ) t = ε₁ := by simpa using congrFun hvt 4
  have v6 : (χ₆ : G → ℂ) t = 4 * ε₂ := by simpa using congrFun hvt 5
  obtain ⟨d1, hd1pos, hd1⟩ := blocksIrr_degree_eq_natCast χ₁
  obtain ⟨d2, hd2pos, hd2⟩ := blocksIrr_degree_eq_natCast χ₂
  obtain ⟨d3, hd3pos, hd3⟩ := blocksIrr_degree_eq_natCast χ₃
  obtain ⟨d4, hd4pos, hd4⟩ := blocksIrr_degree_eq_natCast χ₄
  obtain ⟨d5, hd5pos, hd5⟩ := blocksIrr_degree_eq_natCast χ₅
  obtain ⟨d6, hd6pos, hd6⟩ := blocksIrr_degree_eq_natCast χ₆
  obtain ⟨d7, hd7pos, hd7⟩ := blocksIrr_degree_eq_natCast χ₇
  have hβ1z : ∀ i : Fin 5,
      inducedFunction C (fun x => GL2OddKernel.bigPhi φ i (π x)) 1 = 0 :=
    fun i => hβodd i 1 (by rw [orderOf_one]; exact odd_one)
  have e0 : (1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂)) 1 = 0 := by rw [← hβ0]; exact hβ1z 0
  have e1 : ((ε : ℂ) • ((χ₁ : G → ℂ) - χ₃)) 1 = 0 := by rw [← hβ1]; exact hβ1z 1
  have e2 : ((ε : ℂ) • ((χ₃ : G → ℂ) - χ₄)) 1 = 0 := by rw [← hβ2]; exact hβ1z 2
  have e3 : ((ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ)) 1 =
      0 := by rw [← hβ3]; exact hβ1z 3
  have e4 : ((ε : ℂ) • (χ₁ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₃ : ℂ) • (χ₇ : G → ℂ)) 1 =
      0 := by rw [← hβ4]; exact hβ1z 4
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul] at e0 e1
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e2 e3 e4
  rw [hd1, hd2] at e0
  rw [hd1, hd3] at e1
  rw [hd3, hd4] at e2
  rw [hd2, hd5, hd6] at e3
  rw [hd1, hd5, hd7] at e4
  have z0 : 1 + ε * ((d1 : ℤ) - d2) = 0 := by exact_mod_cast e0
  have z1 : ε * ((d1 : ℤ) - d3) = 0 := by exact_mod_cast e1
  have z2 : ε * ((d3 : ℤ) - d4) = 0 := by exact_mod_cast e2
  have z3 : ε * (d2 : ℤ) + ε₁ * d5 + ε₂ * d6 = 0 := by exact_mod_cast e3
  have z4 : ε * (d1 : ℤ) + ε₁ * d5 + ε₃ * d7 = 0 := by exact_mod_cast e4
  have hdeg2 : (d2 : ℤ) = d1 + ε := by rcases hε with rfl | rfl <;> omega
  have hdeg3 : d3 = d1 := by rcases hε with rfl | rfl <;> omega
  have hdeg4 : d4 = d1 := by rcases hε with rfl | rfl <;> omega
  have hJconj : ∀ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2), ∀ g : C,
      g * u * g⁻¹ ∈ Finset.univ.filter (fun x : C => orderOf x = 2) := by
    intro u hu g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  have hφconj : ∀ j, ∀ x g : G23, φ j (x * g * x⁻¹) = φ j g := fun j =>
    GL2OddKernel.blocksIrr_conj (hφirr j)
  obtain ⟨β₀, hβ₀, hβ₀z⟩ := GL2ScaledOrders.exists_noncentral_involution π.toMonoidHom
    π.surjective hN
  have hr1 : Nat.card π.toMonoidHom.ker / Nat.card (π.toMonoidHom.ker ⊓
      Subgroup.centralizer ({β₀} : Set C) : Subgroup C) = 1 := by
    rw [hker, bot_inf_eq, Subgroup.card_bot]
  have hT : ∀ j, (∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
      ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2), φ j (π (u * v))) * φ j 1 =
      (φ j (-1) + 12 * φ j (π β₀)) ^ 2 := by
    intro j
    obtain ⟨W, _, _, _, ρ, hirr, hρ⟩ := hφirr j
    have : Representation.IsIrreducible (ρ.comp π.toMonoidHom) :=
      CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective _ π.surjective _ hirr
    have h := GL2ScaledOrders.class_sum_square (ρ.comp π.toMonoidHom)
      (Finset.univ.filter fun x : C => orderOf x = 2) hJconj
    have hsum := GL2ScaledOrders.involution_sum ht π.toMonoidHom π.surjective hN hπtM β₀ hβ₀
      hβ₀z (φ j) (hφconj j)
    rw [hr1, Nat.cast_one, mul_one] at hsum
    have h' : (∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2), φ j (π (u * v))) *
          φ j (π 1) =
        (∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2), φ j (π u)) ^ 2 := by
      rw [← hρ]
      exact h
    rw [map_one] at h'
    rw [h']
    exact congrArg (· ^ 2) hsum
  have hβb : ∀ j, φ j (π β₀) = φ j b := by
    intro j
    have hπβ2 : orderOf (π β₀) = 2 := by rw [MulEquiv.orderOf_eq]; exact hβ₀
    have hcl : classOf (π β₀) = 5 := classOf_of_orderOf_two hπβ2
      (fun h => hβ₀z (h ▸ GL2ScaledOrders.neg_one_mem_center))
    have hclb : classOf b = 5 := classOf_of_orderOf_two hb
      (fun h => hbz (h ▸ GL2ScaledOrders.neg_one_mem_center))
    obtain ⟨x, hx⟩ := isConj_iff.mp ((isConj_iff_classOf b (π β₀)).mpr (by rw [hcl, hclb]))
    rw [← hx, hφconj]
  have t00 : φ 0 1 = 1 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 0 0
  have t01 : φ 0 (-1) = 1 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 0 1
  have t05 : φ 0 b = 1 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 0 5
  have t10 : φ 1 1 = 1 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 1 0
  have t11 : φ 1 (-1) = 1 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 1 1
  have t15 : φ 1 b = -1 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 1 5
  have t20 : φ 2 1 = 2 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 2 0
  have t21 : φ 2 (-1) = 2 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 2 1
  have t25 : φ 2 b = 0 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 2 5
  have t40 : φ 4 1 = 3 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 4 0
  have t41 : φ 4 (-1) = 3 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 4 1
  have t45 : φ 4 b = 1 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 4 5
  have t50 : φ 5 1 = 4 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 5 0
  have t51 : φ 5 (-1) = -4 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 5 1
  have t55 : φ 5 b = 0 := by simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 5 5
  have hR0 : ∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
      ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        GL2OddKernel.bigPhi φ 0 (π (u * v)) = 96 := by
    have h0 := hT 0
    have h2 := hT 2
    have h4 := hT 4
    rw [t00, t01, hβb, t05] at h0
    rw [t20, t21, hβb, t25] at h2
    rw [t40, t41, hβb, t45] at h4
    simp only [GL2OddKernel.bigPhi, Matrix.cons_val_zero, Pi.add_apply, Pi.sub_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linear_combination h0 + (1 / 2 : ℂ) * h2 - (1 / 3 : ℂ) * h4
  have hR3 : ∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
      ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        GL2OddKernel.bigPhi φ 3 (π (u * v)) = 192 := by
    have h1 := hT 1
    have h4 := hT 4
    have h5 := hT 5
    rw [t10, t11, hβb, t15] at h1
    rw [t40, t41, hβb, t45] at h4
    rw [t50, t51, hβb, t55] at h5
    simp only [GL2OddKernel.bigPhi, Matrix.cons_val, Pi.add_apply, Pi.sub_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linear_combination h1 + (1 / 3 : ℂ) * h4 - (1 / 4 : ℂ) * h5
  have hpc : ∀ i : Fin 5, ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
        inducedFunction C (fun x => GL2OddKernel.bigPhi φ i (π x)) (u * v) =
      (C.index : ℂ) * ∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
          GL2OddKernel.bigPhi φ i (π (u * v)) := fun i =>
    GL2ScaledOrders.pair_count_induced t _ fun x hx =>
      GL2Columns.bigPhi_comp_eq_zero_of_not_mem ht π.toMonoidHom hN hπtM ha hp hb hbz hφirr hφ'
        i x hx
  have hβ0' : inducedFunction C (fun x => GL2OddKernel.bigPhi φ 0 (π x)) =
      1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂) := hβ0
  have hβ3' : inducedFunction C (fun x => GL2OddKernel.bigPhi φ 3 (π x)) =
      (ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ) := hβ3
  have hP0 := hpc 0
  have hP3 := hpc 3
  rw [hR0, hβ0'] at hP0
  rw [hR3, hβ3'] at hP3
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hP0 hP3
  have hsign : ∀ e : ℤ, (e = 1 ∨ e = -1) → ((e : ℂ)) ^ 2 = 1 := by
    rintro e (rfl | rfl) <;> norm_num
  have hidx0 : (C.index : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Subgroup.index_ne_zero_of_finite)
  have hS0 := involution_class_sum_square hinv ht (principal_mem_blocksIrr G)
  have hS1 := involution_class_sum_square hinv ht χ₁.2
  have hS2 := involution_class_sum_square hinv ht χ₂.2
  have hS5 := involution_class_sum_square hinv ht χ₅.2
  have hS6 := involution_class_sum_square hinv ht χ₆.2
  simp only [Pi.one_apply, mul_one] at hS0 hP0
  rw [v1, hd1] at hS1
  rw [v2, hd2] at hS2
  rw [v5, hd5] at hS5
  rw [v6, hd6] at hS6
  have hd2' : (d2 : ℂ) = d1 + ε := by exact_mod_cast hdeg2
  have E1 := GL2ScaledOrders.first_order_equation (R0 := 96) (hsign ε hε) hidx0
    hS0 hS1 (by rw [← hd2']; exact hS2) (by linear_combination hP0)
  have E2 := GL2ScaledOrders.second_order_equation (R3 := 192) (hsign ε hε)
    (hsign ε₁ hε₁) (hsign ε₂ hε₂) hidx0 hS2 hS5 hS6 (by linear_combination hP3)
  have E1z : (C.index : ℤ) * (((d1 : ℤ) - 2 * ε) * ((d1 : ℤ) - 2 * ε)) =
      96 * 1 * ((d1 : ℤ) * ((d1 : ℤ) + ε)) := by
    rw [mul_one]
    exact_mod_cast E1
  have E2z : (C.index : ℤ) * (9 * ε * (d5 : ℤ) * d6 + ε₁ * ((d1 : ℤ) + ε) * d6 +
      16 * ε₂ * ((d1 : ℤ) + ε) * d5) = 192 * 1 * (((d1 : ℤ) + ε) * d5 * d6) := by
    rw [mul_one, ← hdeg2]
    exact_mod_cast E2
  have D1 : ε * ((d1 : ℤ) + ε) + ε₁ * d5 + ε₂ * d6 = 0 := by rw [← hdeg2]; exact z3
  have hidx : Odd C.index := GL2ScaledOrders.centralizer_index_odd hinv ht
  have hidxz : (C.index : ℤ) % 2 = 1 := by
    have := Nat.odd_iff.mp hidx
    omega
  have hcardG : Nat.card G = C.index * 48 := by
    rw [← C.index_mul_card, Nat.card_congr π.toEquiv, card_G23]
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := G)
  have hvanS : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
      ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
      ψ ≠ (χ₇ : G → ℂ) → ∀ s ∈ (S : Subgroup G), s ≠ 1 → ψ s = 0 := by
    intro ψ hψ e0 e1 e2 e3 e4 e5 e6 e7 s hs hs1
    apply hvanish ψ hψ e0 e1 e2 e3 e4 e5 e6 e7 s
    obtain ⟨k, hk⟩ := (S.isPGroup' ⟨s, hs⟩)
    have hord : orderOf s ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk s hs]
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    rcases m with _ | m
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact absurd hm hs1
    · rw [hm, pow_succ]
      exact even_two.mul_left _
  rcases GL2ScaledOrders.degree_solutions (by exact_mod_cast hd1pos)
      (by rw [← hdeg2]; exact_mod_cast hd2pos) (by exact_mod_cast hd5pos)
      (by exact_mod_cast hd6pos) (by exact_mod_cast hd7pos) hε hε₁ hε₂ hε₃ hidxz
      (by norm_num : (1 : ℤ) % 2 = 1) (by norm_num : (0 : ℤ) < 1) D1 z4 E1z E2z with
    ⟨rfl, h1d, rfl, h5d, rfl, h6d, rfl, h7d, hidxv⟩ |
      ⟨rfl, h1d, rfl, h5d, rfl, h6d, rfl, h7d, hidxv⟩
  all_goals
    have hid0 : β 0 = 1 + ((χ₁ : G → ℂ) - χ₂) := by
      rw [show β 0 = 1 + ((1 : ℤ) : ℂ) • ((χ₁ : G → ℂ) - χ₂) from hβ0]
      simp
    have hid1 : β 1 = (χ₁ : G → ℂ) - χ₃ := by
      rw [show β 1 = ((1 : ℤ) : ℂ) • ((χ₁ : G → ℂ) - χ₃) from hβ1]
      simp
    have hid2 : β 2 = (χ₃ : G → ℂ) - χ₄ := by
      rw [show β 2 = ((1 : ℤ) : ℂ) • ((χ₃ : G → ℂ) - χ₄) from hβ2]
      simp
    have hid3 : β 3 = (χ₂ : G → ℂ) - χ₅ + χ₆ := by
      rw [show β 3 = ((1 : ℤ) : ℂ) • (χ₂ : G → ℂ) + ((-1 : ℤ) : ℂ) • (χ₅ : G → ℂ) +
        ((1 : ℤ) : ℂ) • (χ₆ : G → ℂ) from hβ3]
      push_cast
      rw [one_smul, one_smul, neg_one_smul]
      abel
    have hid4 : β 4 = (χ₁ : G → ℂ) - χ₅ + χ₇ := by
      rw [show β 4 = ((1 : ℤ) : ℂ) • (χ₁ : G → ℂ) + ((-1 : ℤ) : ℂ) • (χ₅ : G → ℂ) +
        ((1 : ℤ) : ℂ) • (χ₇ : G → ℂ) from hβ4]
      push_cast
      rw [one_smul, one_smul, neg_one_smul]
      abel
    have hids : identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ :=
      ⟨hnd, h1, h2, h3, h4, h5, h6, h7, hid0, hid1, hid2, hid3, hid4, hvanish⟩
  ·
    have e1 : d1 = 10 := by omega
    have e2 : d2 = 11 := by omega
    have e3 : d3 = 10 := by omega
    have e4 : d4 = 10 := by omega
    have e5 : d5 = 55 := by omega
    have e6 : d6 = 44 := by omega
    have e7 : d7 = 45 := by omega
    have hidxn : C.index = 165 := by omega
    have hG : Nat.card G = 7920 := by rw [hcardG, hidxn]
    have hdeg : ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1,
        (χ₅ : G → ℂ) 1, (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![10, 11, 10, 10, 55, 44, 45] := by
      rw [hd1, hd2, hd3, hd4, hd5, hd6, hd7, e1, e2, e3, e4, e5, e6, e7]
      norm_num
    obtain ⟨hperf, hcls, hmset, hψ⟩ := seven_character_sylow_support_degree_profile_7920 hG S
      χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ hnd h1 h2 h3 h4 h5 h6 h7 hdeg hvanS
    refine ⟨hperf, Or.inl ⟨⟨hG, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, hids, hdeg, hψ, hmset, hcls⟩,
      fun hB => ?_⟩⟩
    rw [hB.1] at hG
    norm_num at hG
  ·
    have e1 : d1 = 26 := by omega
    have e2 : d2 = 27 := by omega
    have e3 : d3 = 26 := by omega
    have e4 : d4 = 26 := by omega
    have e5 : d5 = 39 := by omega
    have e6 : d6 = 12 := by omega
    have e7 : d7 = 13 := by omega
    have hidxn : C.index = 117 := by omega
    have hG : Nat.card G = 5616 := by rw [hcardG, hidxn]
    have hdeg : ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1,
        (χ₅ : G → ℂ) 1, (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![26, 27, 26, 26, 39, 12, 13] := by
      rw [hd1, hd2, hd3, hd4, hd5, hd6, hd7, e1, e2, e3, e4, e5, e6, e7]
      norm_num
    obtain ⟨hperf, hcls, hmset, -, -⟩ := seven_character_sylow_support_degree_profile hG S
      χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ hnd h1 h2 h3 h4 h5 h6 h7 hdeg hvanS
    refine ⟨hperf, Or.inr ⟨⟨hG, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, hids, hdeg, hmset, hcls⟩,
      fun hA => ?_⟩⟩
    rw [hA.1] at hG
    norm_num at hG

end CFSG.Semidihedral.GL2Recognition
