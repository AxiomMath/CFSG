module

public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ColumnsSupport
public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers GL2ThreeCharacters

theorem card_centralizer_eq_of_le {G : Type*} [Group G] (C : Subgroup G) (s : C)
    (hle : Subgroup.centralizer ({(s : G)} : Set G) ≤ C) :
    Nat.card (Subgroup.centralizer ({(s : G)} : Set G)) =
      Nat.card (Subgroup.centralizer ({s} : Set C)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨g, hle g.2⟩, ?_⟩
      invFun := fun x => ⟨x.1, ?_⟩
      left_inv := fun g => rfl
      right_inv := fun x => rfl }
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem card_centralizer_mulEquiv {C H : Type*} [Group C] [Group H] (π : C ≃* H) (s : C) :
    Nat.card (Subgroup.centralizer ({s} : Set C)) =
      Nat.card (Subgroup.centralizer ({π s} : Set H)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨π x, ?_⟩
      invFun := fun y => ⟨π.symm y, ?_⟩
      left_inv := fun x => Subtype.ext (π.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (π.apply_symm_apply y) }
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp x.2]
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply π.injective
    rw [map_mul, map_mul, π.apply_symm_apply, Subgroup.mem_centralizer_singleton_iff.mp y.2]

theorem exact_GL2_centralizer_produces_two_character_columns {G : Type} [Group G] [Fintype G]
    (t : G) (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hπt : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1)
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
    let q : G := ((π.symm p : C) : G)
    let identities : CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G →
        CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G →
        ℤ → ℤ → ℤ → ℤ → Prop := fun χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ =>
      [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup ∧
      (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧ (χ₄ : G → ℂ) ≠ 1 ∧
      (χ₅ : G → ℂ) ≠ 1 ∧ (χ₆ : G → ℂ) ≠ 1 ∧ (χ₇ : G → ℂ) ≠ 1 ∧
      (ε = 1 ∨ ε = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
      β 0 = 1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂) ∧
      β 1 = (ε : ℂ) • ((χ₁ : G → ℂ) - χ₃) ∧
      β 2 = (ε : ℂ) • ((χ₃ : G → ℂ) - χ₄) ∧
      β 3 = (ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ) ∧
      β 4 = (ε : ℂ) • (χ₁ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₃ : ℂ) • (χ₇ : G → ℂ)
    (∃ (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (ε ε₁ ε₂ ε₃ : ℤ),
      identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃) ∧
    ∀ (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (ε ε₁ ε₂ ε₃ : ℤ),
      identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ →
      ![(χ₁ : G → ℂ) t, (χ₂ : G → ℂ) t, (χ₃ : G → ℂ) t, (χ₄ : G → ℂ) t, (χ₅ : G → ℂ) t,
          (χ₆ : G → ℂ) t, (χ₇ : G → ℂ) t] =
        ![2 * (ε : ℂ), 3 * ε, -2 * ε, -2 * ε, (ε₁ : ℂ), 4 * ε₂, -3 * ε₃] ∧
      ![(χ₁ : G → ℂ) (t * q), (χ₂ : G → ℂ) (t * q), (χ₃ : G → ℂ) (t * q),
          (χ₄ : G → ℂ) (t * q), (χ₅ : G → ℂ) (t * q), (χ₆ : G → ℂ) (t * q),
          (χ₇ : G → ℂ) (t * q)] =
        ![-(ε : ℂ), 0, ε, ε, (ε₁ : ℂ), ε₂, 0] ∧
      ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
        ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
        ψ ≠ (χ₇ : G → ℂ) → ψ t = 0 ∧ ψ (t * q) = 0 := by
  intro C Φ β q identities
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
  have hπt' : π.toMonoidHom (GL2OddKernel.tC t) = -1 := hπt
  refine ⟨?_, ?_⟩
  · obtain ⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hnd, h1, h2, h3, h4, h5, h6, h7, hε, hε₁,
      hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4, -, -⟩ :=
      odd_kernel_GL2_centralizer_produces_actual_characters t ht π.toMonoidHom
        π.surjective hN hπt a p b ha hp hb hbz φ hφirr hφ
    exact ⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hnd, h1, h2, h3, h4, h5, h6, h7, hε,
      hε₁, hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4⟩
  intro χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ hsol
  obtain ⟨hnd, h1, h2, h3, h4, h5, h6, h7, hε, hε₁, hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4⟩ := hsol
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  let c : Fin 8 → G → ℂ := ![1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇]
  have hcirr : ∀ k, c k ∈ CFSG.BlocksIrr G := by
    intro k
    fin_cases k
    exacts [principal_mem_blocksIrr G, χ₁.2, χ₂.2, χ₃.2, χ₄.2, χ₅.2, χ₆.2, χ₇.2]
  have hcinj : Function.Injective c :=
    GL2Columns.injective_of_nodup hnd h1 h2 h3 h4 h5 h6 h7
  choose l hl using fun k => GL2Columns.exists_label_of_mem_blocksIrr basis (hcirr k)
  have hlinj : Function.Injective l := fun i j h => hcinj (by rw [← hl i, ← hl j, h])
  have hsymm1 : π.symm (-1) = GL2OddKernel.tC t := by
    rw [MulEquiv.symm_apply_eq]
    exact hπt.symm
  have hq3 : orderOf (π.symm p) = 3 := by rw [MulEquiv.orderOf_eq, hp]
  have hcoord : ∀ i ∈ (Finset.univ : Finset basis.index), ∃ x y : ℤ,
      (basis.representation i).character t = x + 2 * y ∧
        (basis.representation i).character (t * q) = x - y := by
    intro i _
    let dataH : FiniteComplexRepresentation.{0, 0} G23 :=
      { vector := (basis.representation i).vector
        representation := (basis.representation i).representation.comp
          ((Subgroup.centralizer ({t} : Set G)).subtype.comp π.symm.toMonoidHom) }
    obtain ⟨x, y, hx, hy⟩ := GL2Columns.character_coords ha hp hb hbz dataH
    refine ⟨x, y, ?_, ?_⟩
    · have e : dataH.character (-1) = (basis.representation i).character t := by
        show (basis.representation i).representation.character
          ((π.symm (-1) : Subgroup.centralizer ({t} : Set G)) : G) = _
        rw [hsymm1]
        rfl
      rw [← e, hx]
    · have e : dataH.character (-1 * p) = (basis.representation i).character (t * q) := by
        show (basis.representation i).representation.character
          ((π.symm (-1 * p) : Subgroup.centralizer ({t} : Set G)) : G) = _
        rw [map_mul, hsymm1]
        rfl
      rw [← e, hy]
  have hreal : ∀ i : basis.index, (basis.representation i).character (t * q)⁻¹ =
      (basis.representation i).character (t * q) := by
    intro i
    obtain ⟨x, y, -, hy⟩ := hcoord i (Finset.mem_univ _)
    rw [← finite_character_conjugate_inverse, hy]
    simp
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by rw [← pow_two, ht2])
  have htt : ∑ i, (basis.representation i).character t ^ 2 = 48 := by
    rw [CFSG.Wreathed.complete_involution_column_sum basis t ht2,
      Nat.card_congr π.toEquiv, card_G23]
    norm_num
  have hcentq : Subgroup.centralizer ({t * q} : Set G) ≤ C := by
    intro g hg
    have hcomm : Commute g (t * q) := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hq3' : (π.symm p : Subgroup.centralizer ({t} : Set G)) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (π.symm p)
      rwa [hq3] at h
    have htq3 : (t * q) ^ 3 = t := by
      have hcq : Commute t q := (Subgroup.mem_centralizer_singleton_iff.mp (π.symm p).2).symm
      rw [hcq.mul_pow, show q ^ 3 = 1 from congrArg Subtype.val hq3', mul_one,
        pow_succ, ht2, one_mul]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (hcomm.pow_right 3).eq
    rwa [htq3] at h
  have hcardq : Nat.card (Subgroup.centralizer ({t * q} : Set G)) = 6 := by
    have e := card_centralizer_eq_of_le C (GL2OddKernel.tC t * π.symm p) hcentq
    have hπt'' : π (GL2OddKernel.tC t) = -1 := hπt
    rw [card_centralizer_mulEquiv π, map_mul, hπt'', MulEquiv.apply_symm_apply,
      GL2Columns.card_centralizer_neg_one_mul ha hp hb hbz] at e
    exact e
  have hqq : ∑ i, (basis.representation i).character (t * q) ^ 2 = 6 := by
    have h := CFSG.Wreathed.complete_character_column_sum basis (t * q) (t * q)
    rw [CFSG.Wreathed.conjugatorCount_self, hcardq] at h
    simp only [hreal, ← pow_two] at h
    rw [h]
    norm_num
  have htq : ∑ i, (basis.representation i).character t *
      (basis.representation i).character (t * q) = 0 := by
    have h := CFSG.Wreathed.complete_character_column_sum basis t (t * q)
    rw [htinv] at h
    rw [h]
    unfold CFSG.Wreathed.conjugatorCount
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [ite_eq_right]
    intro hg
    have hsq : (t * q) ^ 2 = 1 := by rw [← hg, conj_pow, ht2, mul_one, mul_inv_cancel]
    have hcq : Commute t q := (Subgroup.mem_centralizer_singleton_iff.mp (π.symm p).2).symm
    rw [hcq.mul_pow, ht2, one_mul] at hsq
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [Subgroup.orderOf_coe, hq3] at hdvd
    norm_num at hdvd
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩, hrest⟩ :=
    GL2Columns.columns_of_identities ht π.toMonoidHom hN hπt' ha hp hb hbz hφirr hφ'
      (π.symm p) (π.apply_symm_apply p) basis Finset.univ hcoord htt hqq htq c rfl l hl hlinj
      (fun _ => Finset.mem_univ _) hε hε₁ hε₂ hε₃ hβ0 hβ1 hβ2 hβ3 hβ4
  refine ⟨?_, ?_, fun ψ hψ hψ0 hψ1 hψ2 hψ3 hψ4 hψ5 hψ6 hψ7 => ?_⟩
  · ext k
    fin_cases k
    exacts [a1, a2, a3, a4, a5, a6, a7]
  · ext k
    fin_cases k
    exacts [b1, b2, b3, b4, b5, b6, b7]
  · obtain ⟨i, hi⟩ := GL2Columns.exists_label_of_mem_blocksIrr basis hψ
    have hni : ∀ k, l k ≠ i := by
      intro k hk
      have e : ψ = c k := by rw [← hi, ← hk, hl k]
      fin_cases k
      exacts [hψ0 e, hψ1 e, hψ2 e, hψ3 e, hψ4 e, hψ5 e, hψ6 e, hψ7 e]
    obtain ⟨e1, e2⟩ := hrest i (Finset.mem_univ _) hni
    rw [hi] at e1 e2
    exact ⟨e1, e2⟩

end CFSG.Semidihedral.Principal
