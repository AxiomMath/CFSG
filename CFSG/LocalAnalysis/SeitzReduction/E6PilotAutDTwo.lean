module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutD

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed

section Roots

set_option maxRecDepth 100000 in
theorem permLattice_a5Root : ∀ i j : Fin 6,
    permLattice (τ := Tag.E6) TwistTag.E6.perm (a5Root i j) = a5Root (Fin.rev j) (Fin.rev i) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem permLattice_highRoot_E6 :
    permLattice (τ := Tag.E6) TwistTag.E6.perm (highRoot .E6) = highRoot .E6 ∧
      permLattice (τ := Tag.E6) TwistTag.E6.perm (-highRoot .E6) = -highRoot .E6 := by
  decide +kernel

end Roots

section Graph

variable {K : Type} [Field K]


theorem exactQ_one_conj_pinnedX (h2 : (2 : K) = 0) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) (c : K) :
    exactQ .E6 K 1 * pinnedX .E6 K α c * (exactQ .E6 K 1)⁻¹ =
      pinnedX .E6 K (permLattice (τ := Tag.E6) TwistTag.E6.perm α) c := by
  have hQ : exactQ .E6 K 1 = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) := by
    simp only [exactQ, pow_one]
    rfl
  rw [hQ]
  exact E6GraphRadical.diagramMap_conj_pinnedX_of_two h2 hα c

theorem exactQ_one_conj_of_mem_highRootSL2 [CharP K 2] {x : ModGL .E6 K}
    (hx : x ∈ EPilot.highRootSL2 .E6 K) :
    exactQ .E6 K 1 * x * (exactQ .E6 K 1)⁻¹ = x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hgen : ∀ {γ : Fin Tag.E6.rank → ℤ}, IsRoot .E6 γ →
      permLattice (τ := Tag.E6) TwistTag.E6.perm γ = γ →
        rootSubgroup .E6 K γ ≤ centralizer ({exactQ .E6 K 1} : Set (ModGL .E6 K)) := by
    intro γ hγ hργ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have e := exactQ_one_conj_pinnedX h2 hγ c
    rw [hργ] at e
    exact mul_inv_eq_iff_eq_mul.1 e
  have hle : EPilot.highRootSL2 .E6 K ≤
      centralizer ({exactQ .E6 K 1} : Set (ModGL .E6 K)) :=
    sup_le (hgen (isRoot_highRoot .E6) permLattice_highRoot_E6.1)
      (hgen (IsRoot.neg (isRoot_highRoot .E6)) permLattice_highRoot_E6.2)
  rw [Subgroup.mem_centralizer_iff.1 (hle hx) _ (Set.mem_singleton _), mul_inv_cancel_right]

end Graph

section Outer

variable {K : Type} [Field K]

theorem transvection_one_mul_self [CharP K 2] {i j : Fin 6} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : K) *
        Matrix.SpecialLinearGroup.transvection hij 1 = 1 := by
  refine Subtype.ext ?_
  have e := Matrix.transvection_mul_transvection_same i j hij (1 : K) 1
  rw [one_add_one_eq_two, CharTwo.two_eq_zero, Matrix.transvection_zero] at e
  exact e


theorem false_of_conj_a5Root_rev [Finite K] [CharP K 2] {d : ModGL .E6 K}
    (hd : d ∈ rootSpan .E6 K a5LeviRoots)
    (h : ∀ i : Fin 6, i = 1 ∨ i = 2 →
      d * pinnedX .E6 K (a5Root (Fin.rev 0) (Fin.rev i)) 1 * d⁻¹ =
        pinnedX .E6 K (a5Root i 0) 1) :
    False := by
  have hdC : d ∈ adjointGroup .E6 K := rootSpan_le_adjointGroup_E6 _ hd
  have hdD : (⟨d, hdC⟩ : adjointGroup .E6 K) ∈ a5Levi K := mem_a5Levi_iff.2 hd
  rw [← range_slToAdjointE6] at hdD
  obtain ⟨B, hB⟩ := hdD
  have hBd : ((slToAdjointE6 K B : adjointGroup .E6 K) : ModGL .E6 K) = d :=
    congrArg Subtype.val hB
  have hcol : ∀ i : Fin 6, i = 1 ∨ i = 2 → ∀ k : Fin 6, k ≠ i →
      (B : Matrix (Fin 6) (Fin 6) K) k (Fin.rev 0) = 0 := by
    intro i hi k hk
    have hi0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    have hr : Fin.rev (0 : Fin 6) ≠ Fin.rev i := fun e => hi0 (Fin.rev_inj.1 e).symm
    set T' := Matrix.SpecialLinearGroup.transvection hr (1 : K) with hT'
    set T := Matrix.SpecialLinearGroup.transvection hi0 (1 : K) with hT
    have e := h i hi
    rw [← coe_slToAdjointE6_transvection hr, ← coe_slToAdjointE6_transvection hi0, ← hT,
      ← hT', ← hBd] at e
    have e2 : slToAdjointE6 K (B * T' * B⁻¹ * T⁻¹) = 1 := by
      refine Subtype.ext ?_
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [e, mul_inv_cancel]
    have hz : B * T' * B⁻¹ * T⁻¹ ∈ center (Matrix.SpecialLinearGroup (Fin 6) K) := by
      rw [← ker_slToAdjointE6]
      exact e2
    set z := B * T' * B⁻¹ * T⁻¹ with hzdef
    have hBT : B * T' * B⁻¹ = z * T := by
      rw [hzdef]
      group
    have hzT : T * z = z * T := Subgroup.mem_center_iff.1 hz T
    have hzz : z * z = 1 := by
      calc z * z = z * z * (T * T) := by rw [transvection_one_mul_self hi0, mul_one]
        _ = (z * T) * (z * T) := by
          rw [mul_assoc z T, ← mul_assoc T z T, hzT]
          group
        _ = (B * T' * B⁻¹) * (B * T' * B⁻¹) := by rw [hBT]
        _ = B * (T' * T') * B⁻¹ := by group
        _ = 1 := by rw [transvection_one_mul_self hr, mul_one, mul_inv_cancel]
    obtain ⟨r, -, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    have hr1 : r = 1 := by
      have e3 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 6) K =>
        (A : Matrix (Fin 6) (Fin 6) K) 0 0) hzz
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] at e3
      rw [← hrz] at e3
      simp only [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
        at e3
      exact charTwo_eq_one_of_mul_self_eq_one e3
    have hz1 : z = 1 := by
      refine Subtype.ext ?_
      rw [← hrz, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
    have hBT' : B * T' = T * B := by
      have e4 : B * T' * B⁻¹ = T := by rw [hBT, hz1, one_mul]
      rw [← e4]
      group
    have em := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 6) K =>
      (A : Matrix (Fin 6) (Fin 6) K) k (Fin.rev i)) hBT'
    have hTc : (T : Matrix (Fin 6) (Fin 6) K) = Matrix.transvection i 0 1 := by
      rw [hT]
      rfl
    have hT'c : (T' : Matrix (Fin 6) (Fin 6) K) = Matrix.transvection (Fin.rev 0) (Fin.rev i) 1 := by
      rw [hT']
      rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, hTc, hT'c] at em
    rw [Matrix.mul_transvection_apply_same (Fin.rev 0) (Fin.rev i) k (1 : K)
        (B : Matrix (Fin 6) (Fin 6) K),
      Matrix.transvection_mul_apply_of_ne i 0 k (Fin.rev i) hk (1 : K)
        (B : Matrix (Fin 6) (Fin 6) K), one_mul] at em
    linear_combination em
  have hzero : ∀ k : Fin 6, (B : Matrix (Fin 6) (Fin 6) K) k (Fin.rev 0) = 0 := by
    intro k
    by_cases hk : k = 1
    · subst hk
      exact hcol 2 (Or.inr rfl) 1 (by decide)
    · exact hcol 1 (Or.inl rfl) k hk
  have hdet := Matrix.det_eq_zero_of_column_eq_zero (Fin.rev 0) hzero
  rw [B.2] at hdet
  exact one_ne_zero hdet

end Outer

section Two

variable {K : Type} [Field K]


theorem eq_one_of_fix_a5Levi_of_card_eq_two [Finite K] [CharP K 2] (hK2 : Nat.card K = 2)
    {X Y : Subgroup (adjointGroup .E6 K)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hXc : centralizer (X : Set (adjointGroup .E6 K)) ≤ Y ⊔ a5Levi K)
    (hY : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut (adjointGroup .E6 K)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ a5Levi K, β d = d) (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hunit : ∀ u : Kˣ, u = 1 := by
    have hc : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hc).1
    exact fun u => Subsingleton.elim u 1
  have hK01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (congrArg Units.val (hunit (Units.mk0 c hc)))
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex β
  have ha : a = 1 := funext fun i => hunit (a i)
  have hσ : σ = RingEquiv.refl K := RingEquiv.ext fun c => by
    rcases hK01 c with rfl | rfl
    · rw [map_zero, RingEquiv.refl_apply]
    · rw [map_one, RingEquiv.refl_apply]
  subst ha hσ
  have hβg : ∀ x : adjointGroup .E6 K, (β x : ModGL .E6 K) =
      (g : ModGL .E6 K) * (exactQ .E6 K ε * (x : ModGL .E6 K) * (exactQ .E6 K ε)⁻¹) *
        (g : ModGL .E6 K)⁻¹ := by
    intro x
    have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL .E6 K) = x :=
      Units.ext (entrywise_id _)
    rw [hga x, e1, rootDiagUnit_one]
    group
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with hε | hε
  ·
    have hβc : β = MulAut.conj g := MulEquiv.ext fun x => Subtype.ext (by
      rw [hβg x, hε, exactQ_zero, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, one_mul, inv_one, mul_one])
    subst hβc
    have hgD : g ∈ centralizer (a5Levi K : Set (adjointGroup .E6 K)) :=
      mem_centralizer_iff.2 fun y hy => by
        have := hβD y hy
        rw [MulAut.conj_apply] at this
        calc y * g = g * y * g⁻¹ * g := by rw [this]
          _ = g * y := by group
    have hgX : g ∈ centralizer (X : Set (adjointGroup .E6 K)) :=
      mem_centralizer_iff.2 fun x hx => by
        have := hβX x hx
        rw [MulAut.conj_apply] at this
        calc x * g = g * x * g⁻¹ * g := by rw [this]
          _ = g * x := by group
    have hgn : g ^ 2 ^ n = 1 := by
      have hc : MulAut.conj (g ^ 2 ^ n) = 1 := by rw [map_pow, hβn]
      have hz : g ^ 2 ^ n ∈ center (adjointGroup .E6 K) := by
        rw [mem_center_iff]
        intro y
        have := congrArg (fun γ : MulAut _ => γ y) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc y * g ^ 2 ^ n = g ^ 2 ^ n * y * (g ^ 2 ^ n)⁻¹ * g ^ 2 ^ n := by rw [this]
          _ = g ^ 2 ^ n * y := by group
      rw [center_adjointGroup_eq_bot] at hz
      exact hz
    rw [F4Pilot.eq_one_of_mem_sup_of_mem_centralizer hY center_a5Levi_eq_bot hYodd (hXc hgX) hgD
      hgn, map_one]
  ·
    exfalso
    have hQ1 : exactQ .E6 K ε = exactQ .E6 K 1 := by rw [hε]
    have hgX : g ∈ centralizer (X : Set (adjointGroup .E6 K)) :=
      mem_centralizer_iff.2 fun x hx => by
        have e := congrArg Subtype.val (hβX x hx)
        rw [hβg x, hQ1, exactQ_one_conj_of_mem_highRootSL2 (mem_subgroupOf.1 (hXJ hx))] at e
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul]
        calc (x : ModGL .E6 K) * g = g * x * (g : ModGL .E6 K)⁻¹ * g := by rw [e]
          _ = g * x := by group
    have hYN : Y ≤ normalizer (a5Levi K : Set (adjointGroup .E6 K)) :=
      hY.trans (Subgroup.centralizer_le_normalizer _)
    have hg' : g ∈ ((Y ⊔ a5Levi K : Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) :=
      hXc hgX
    rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at hg'
    obtain ⟨y, hy, d, hd, rfl⟩ := Set.mem_mul.1 hg'
    refine false_of_conj_a5Root_rev (d := (d : ModGL .E6 K)) (mem_a5Levi_iff.1 hd) fun i hi => ?_
    have hi0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    have hr : Fin.rev (0 : Fin 6) ≠ Fin.rev i := fun e => hi0 (Fin.rev_inj.1 e).symm
    set x' : adjointGroup .E6 K :=
      ⟨pinnedX .E6 K (a5Root (Fin.rev 0) (Fin.rev i)) 1, pinnedX_mem_adjointGroup _ _⟩ with hx'
    have hx'D : x' ∈ a5Levi K := pinnedX_a5Root_mem_a5Levi hr 1
    have hzD : d * x' * d⁻¹ ∈ a5Levi K := mul_mem (mul_mem hd hx'D) (inv_mem hd)
    have hyz : d * x' * d⁻¹ * y = y * (d * x' * d⁻¹) := mem_centralizer_iff.1 (hY hy) _ hzD
    have e := congrArg Subtype.val (hβD _ (pinnedX_a5Root_mem_a5Levi hi0 (1 : K)))
    rw [hβg, hQ1, exactQ_one_conj_pinnedX h2 (isRoot_a5Root hi0), permLattice_a5Root] at e
    have e' : ((y * d * x' * (y * d)⁻¹ : adjointGroup .E6 K) : ModGL .E6 K) =
        pinnedX .E6 K (a5Root i 0) 1 := by
      refine Eq.trans ?_ e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx']
    have e'' : y * d * x' * (y * d)⁻¹ = d * x' * d⁻¹ := by
      calc y * d * x' * (y * d)⁻¹ = (y * (d * x' * d⁻¹)) * y⁻¹ := by group
        _ = (d * x' * d⁻¹ * y) * y⁻¹ := by rw [hyz]
        _ = d * x' * d⁻¹ := by group
    rw [e''] at e'
    simpa [hx'] using e'

theorem eq_one_of_fix_a5Levi_of_le_highRootSL2 {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {X Y : Subgroup (adjointGroup .E6 K)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hXc : centralizer (X : Set (adjointGroup .E6 K)) ≤ Y ⊔ a5Levi K)
    (hY : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut (adjointGroup .E6 K)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ a5Levi K, β d = d) (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
  · exact eq_one_of_fix_a5Levi_of_card_eq_two (by rw [hK, pow_one]) hXJ hXc hY hYodd β hβX hβD
      n hβn
  · exact eq_one_of_fix_a5Levi hf2 hK hXc hY hYodd β hβX hβD n hβn

end Two

end CFSG.SeitzReduction.E6Pilot
