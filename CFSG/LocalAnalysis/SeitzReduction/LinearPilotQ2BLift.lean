module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2BLift
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwo
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Model

variable {n : ℕ} {K : Type*} [Field K]

private theorem center_projectiveSL_eq_bot' (hn : 3 ≤ n) :
    Subgroup.center (LinearFlag.projectiveSL n K) = ⊥ := by
  have hsimple : IsSimpleGroup (LinearFlag.projectiveSL n K) := by
    have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) (by omega)
      (Or.inl hn)).2.1
    exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.isSimpleGroup
  have hperf : Group.IsPerfect (LinearFlag.projectiveSL n K) := by
    have := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := n) (by omega) (Or.inl hn)
    exact Group.IsPerfect.ofSurjective
      (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).toMonoidHom)
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (LinearFlag.projectiveSL n K)) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (LinearFlag.projectiveSL n K)).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

private theorem eq_of_conj_eq_projectiveSL (hn : 3 ≤ n) {w u : LinearFlag.projectiveSL n K}
    (h : MulAut.conj w = MulAut.conj u) : w = u := by
  have hc : u⁻¹ * w ∈ Subgroup.center (LinearFlag.projectiveSL n K) := by
    rw [Subgroup.mem_center_iff]
    intro v
    have hv := congrArg (fun α : MulAut (LinearFlag.projectiveSL n K) => α v) h
    simp only [MulAut.conj_apply] at hv
    calc v * (u⁻¹ * w) = u⁻¹ * (u * v * u⁻¹) * w := by group
      _ = u⁻¹ * (w * v * w⁻¹) * w := by rw [hv]
      _ = u⁻¹ * w * v := by group
  rw [center_projectiveSL_eq_bot' hn, Subgroup.mem_bot] at hc
  calc w = u * (u⁻¹ * w) := by group
    _ = u := by rw [hc, mul_one]

private theorem eq_of_agrees_one_of_submatrix_eq {r : ℕ} {e : Fin r → Fin n}
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e)
    {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (hN : ∀ i j, (i ∉ J ∨ j ∉ J) → N i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (h : M.submatrix e e = N.submatrix e e) : M = N := by
  ext i j
  by_cases hij : i ∈ J ∧ j ∈ J
  · obtain ⟨k, rfl⟩ := (hJ i).1 hij.1
    obtain ⟨l, rfl⟩ := (hJ j).1 hij.2
    have := congrFun (congrFun h k) l
    simpa only [submatrix_apply] using this
  · rw [hM i j (not_and_or.1 hij), hN i j (not_and_or.1 hij)]

omit [Field K] in
private theorem eq_zero_or_eq_one_of_card_two [Field K] (hK : Nat.card K = 2) (c : K) :
    c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  rcases eq_or_ne c 0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (mul_left_cancel₀ h0 (h.trans (mul_one c).symm))

variable [Finite K] [CharP K 2]

theorem mem_of_mem_centralizer_torusQ1_two (hK : Nat.card K = 2) (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) {w : LinearFlag.projectiveSL n K}
    (hwX : w ∈ Subgroup.centralizer (X₀ : Set (LinearFlag.projectiveSL n K)))
    (hwD : w ∈ Subgroup.centralizer
      (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ) : Set (LinearFlag.projectiveSL n K))) :
    w ∈ X₀ := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  have hβD : ∀ d ∈ blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ), MulAut.conj w d = d := by
    intro d hd
    rw [MulAut.conj_apply, ← Subgroup.mem_centralizer_iff.1 hwD d hd, mul_inv_cancel_right]
  obtain ⟨A, hA, hA1⟩ := exists_conjAut_eq_of_fix_blockSL (K := K) (by omega)
    (by rw [hcard]; omega) hβD
  have hA' : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := fun i j h =>
    hA1 i j (by simpa only [Finset.mem_compl] using h)
  obtain ⟨x, hxX, y, hy, rfl, -, hxm, hyy⟩ := exists_lift_torusQ1 hX₀ hX₀c
  have hfix : conjAut n K A (LinearFlag.proj n K y) = LinearFlag.proj n K y := by
    rw [← hA, MulAut.conj_apply, ← Subgroup.mem_centralizer_iff.1 hwX _ hxX, mul_inv_cancel_right]
  have hAy := mul_eq_mul_of_conjAut_fix hfix hxm
  have he := pair_injective (n := n) hab
  have hJ := mem_pair_iff_mem_range (a := a) (b := b)
  have hrowsA : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ k ∉ ({a, b} : Finset (Fin n)),
      (A : Matrix (Fin n) (Fin n) K) i k = 0 := fun i hi k hk =>
    (blockDiag_of_agrees_one hA') i k (by tauto)
  have hrowsy : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ k ∉ ({a, b} : Finset (Fin n)),
      (y : Matrix (Fin n) (Fin n) K) i k = 0 := fun i hi k hk =>
    row_eq_zero_of_agrees_one hy hi k hk
  have hblock : (A : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] *
      (y : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] =
        (y : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] *
          (A : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] := by
    rw [← submatrix_mul_of_rows he hJ hrowsA, ← submatrix_mul_of_rows he hJ hrowsy, hAy]
  set y₀ := (y : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] with hy₀
  have hydet : (y : Matrix (Fin n) (Fin n) K).det = 1 := y.2
  have hyy' : (y : Matrix (Fin n) (Fin n) K) * y ≠ 1 := fun h =>
    hyy (Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, h,
      Matrix.SpecialLinearGroup.coe_one]))
  have hx0 : ¬ (y₀ 0 1 = 0 ∧ y₀ 1 0 = 0 ∧ y₀ 0 0 = y₀ 1 1) :=
    not_scalar_submatrix_pair hab hy hydet hyy'
  have hdet0 : y₀.det = 1 := by rw [hy₀, det_submatrix_of_agrees_one he hJ hy, hydet]
  have hsq0 : ((y : Matrix (Fin n) (Fin n) K) * y).submatrix ![a, b] ![a, b] = y₀ * y₀ :=
    submatrix_mul_of_rows he hJ hrowsy _
  have hy0ne1 : y₀ * y₀ ≠ 1 := fun h =>
    hyy' (eq_one_of_agrees_one_of_submatrix_eq_one he hJ (agrees_one_mul hy hy) (hsq0.trans h))
  have hunit : IsUnit y₀ := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet0]; exact isUnit_one)
  have hy0ne : y₀ * y₀ ≠ y₀ := fun h => by
    have h1 : y₀ = 1 := hunit.mul_left_cancel (h.trans (Matrix.mul_one y₀).symm)
    apply hx0
    rw [h1]
    simp
  have hy0ne0 : y₀ * y₀ ≠ 0 := fun h => by
    have h1 := congrArg Matrix.det h
    rw [det_mul, hdet0, mul_one, det_zero] at h1
    exact one_ne_zero h1
  obtain ⟨s₂, r₂, hsr₂⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hx0
    (show y₀ * y₀ * y₀ = y₀ * (y₀ * y₀) from Matrix.mul_assoc _ _ _)
  have hy2 : y₀ * y₀ = 1 + y₀ := by
    rcases eq_zero_or_eq_one_of_card_two hK s₂ with rfl | rfl <;>
      rcases eq_zero_or_eq_one_of_card_two hK r₂ with rfl | rfl
    · exact (hy0ne0 (by rw [hsr₂, zero_smul, zero_smul, add_zero])).elim
    · exact (hy0ne (by rw [hsr₂, zero_smul, one_smul, zero_add])).elim
    · exact (hy0ne1 (by rw [hsr₂, one_smul, zero_smul, add_zero])).elim
    · rw [hsr₂, one_smul, one_smul]
  obtain ⟨s, r, hsr⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hx0 hblock
  have hconj : ∀ S : SpecialLinearGroup (Fin n) K, (A : Matrix (Fin n) (Fin n) K) = S →
      w = LinearFlag.proj n K S := by
    intro S hS
    have hAS : A = Matrix.SpecialLinearGroup.toGL S :=
      Units.ext (by rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; exact hS)
    apply eq_of_conj_eq_projectiveSL (by omega : 3 ≤ n)
    rw [hA, hAS, conjAut_toGL]
  rcases eq_zero_or_eq_one_of_card_two hK s with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_card_two hK r with rfl | rfl
  ·
    exfalso
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    rw [← det_submatrix_of_agrees_one he hJ hA', hsr, zero_smul, zero_smul, add_zero, det_zero]
  ·
    rw [zero_smul, one_smul, zero_add] at hsr
    rw [hconj y (eq_of_agrees_one_of_submatrix_eq hJ hA' hy hsr)]
    exact hxX
  ·
    rw [one_smul, zero_smul, add_zero] at hsr
    have hA1' : (A : Matrix (Fin n) (Fin n) K) = ((1 : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact eq_one_of_agrees_one_of_submatrix_eq_one he hJ hA' hsr
    rw [hconj 1 hA1', map_one]
    exact X₀.one_mem
  ·
    rw [one_smul, one_smul, ← hy2] at hsr
    have hyy2 : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
        ((y * y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
          (1 : Matrix (Fin n) (Fin n) K) i j := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact agrees_one_mul hy hy
    rw [hconj (y * y) (eq_of_agrees_one_of_submatrix_eq hJ hA' hyy2
      (by rw [Matrix.SpecialLinearGroup.coe_mul, hsq0]; exact hsr)), map_mul]
    exact X₀.mul_mem hxX hxX

end Model

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem inf_centralizer_eq_torusQ1_two {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) = X := by
  have hmemX : ∀ x ∈ X₀, ((e.symm x : L) : G) ∈ X := fun x hx => hX ▸ ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have hmemD : ∀ d ∈ blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ), ((e.symm d : L) : G) ∈ D :=
    fun d hd => hDe ▸ ⟨e.symm d, ⟨d, hd, rfl⟩, rfl⟩
  have hcomm : ∀ {c : G} (hcL : c ∈ L) (u : LinearFlag.projectiveSL n K),
      ((e.symm u : L) : G) * c = c * ((e.symm u : L) : G) → u * e ⟨c, hcL⟩ = e ⟨c, hcL⟩ * u := by
    intro c hcL u h
    have h' : e.symm u * ⟨c, hcL⟩ = ⟨c, hcL⟩ * e.symm u := Subtype.ext h
    have h'' := congrArg e h'
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h''
  apply le_antisymm
  · rintro c ⟨⟨hcL, hcX⟩, hcD⟩
    have hwX : e ⟨c, hcL⟩ ∈ centralizer (X₀ : Set (LinearFlag.projectiveSL n K)) :=
      mem_centralizer_iff.2 fun x hx => hcomm hcL x (mem_centralizer_iff.1 hcX _ (hmemX x hx))
    have hwD : e ⟨c, hcL⟩ ∈ centralizer
        (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ) : Set (LinearFlag.projectiveSL n K)) :=
      mem_centralizer_iff.2 fun d hd => hcomm hcL d (mem_centralizer_iff.1 hcD _ (hmemD d hd))
    have hmem := mem_of_mem_centralizer_torusQ1_two hK hn hab hX₀ hX₀c hwX hwD
    have hc : ((e.symm (e ⟨c, hcL⟩) : L) : G) = c := by rw [MulEquiv.symm_apply_apply]
    rw [← hc]
    exact hmemX _ hmem
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic X₀ := isCyclic_of_prime_card (p := 3) (by rw [hX₀c, hK])
    have hXc : X ≤ centralizer (X : Set G) :=
      hX ▸ F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_map_symm e hcyc)
    have hDX : D ≤ centralizer (X : Set G) := by
      rw [hDe, hX]
      exact map_symm_le_centralizer_map_symm e (blockSL_compl_le_centralizer hX₀)
    exact le_inf (le_inf (hX ▸ map_subtype_le _) hXc) (le_centralizer_iff.1 hDX)

theorem hasBLift_neighbour_linear_two (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    ∃ htX : t ∈ centralizer (X : Set G),
      (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf c) → c ∈ X) ∧
      (∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        CFSG.IsComponent E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
          centralizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
          (oddCoreLift E).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = E ∧
          (oddCore (centralizer (X : Set G))).subgroupOf (oddCoreLift E) ≤
            center (oddCoreLift E) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have hKt := inf_centralizer_eq_zpowers hset e hK1 (by omega) htC ht
  have hOut := SeitzQ2.isPGroup_outer_of_mulEquiv_PSL_two (by omega : 3 ≤ n) hK e
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have htL : t ∉ L := not_mem_of_mem_centralizer hset.center_eq_bot htC ht1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  obtain ⟨-, htX, -, -, hD, -⟩ := neighbour_data_torusQ1 e hn hab htC hX₀ hX₀c hX hDe
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_blockSL (L := L) e
    (I := ({a, b} : Finset (Fin n))ᶜ) (by omega) (by omega) (Or.inl (by omega))
  have hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X :=
    (inf_centralizer_eq_torusQ1_two hK e hn hab hX₀ hX₀c hX hDe).le
  exact ⟨htX, SeitzQ2.forall_odd_mem_of_two hOut htC ht htL hCN hKt hXD,
    fun E hE htE hEt =>
      SeitzQ2.hasBLift_of_isPGroup_outer hOut htC ht htL hCN hKt htX hD hDq hXD hE htE hEt,
    fun E hE htE htE' =>
      SeitzQ2.isComponent_oddCoreLift_of_isPGroup_outer hOut htC ht htL hCN hKt htX hD hDq hXD hE
        htE htE'⟩

end Setting

end CFSG.SeitzReduction.LinearPilot
