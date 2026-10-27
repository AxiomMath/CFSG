module

public import CFSG.ClassicalInvolution.SmallCases.LocalDatumRank
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart
public import CFSG.ClassicalInvolution.Models.Transfer.Unitary

public section

namespace CFSG.ClassicalInvolution

open Matrix CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section Elements

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] def negN (σ : K ≃+* K) : normOne σ :=
  ⟨-1, by rw [mem_normOne]; simp⟩

omit [Finite K] in
theorem negN_mul_self (σ : K ≃+* K) : negN σ * negN σ = 1 :=
  Subtype.ext (Units.ext (by simp [negN]))

omit [Finite K] in
theorem negN_ne_one (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) : negN σ ≠ 1 := by
  intro h
  have := congrArg (fun u : normOne σ => ((u : Kˣ) : K)) h
  simp only [negN, Subgroup.coe_one, Units.val_neg, Units.val_one] at this
  exact neg_one_ne_one_of_two_ne_zero h2 this

omit [Finite K] in
theorem diagU3_mul (σ : K ≃+* K) (a b a' b' : normOne σ) :
    diagU3 σ a b * diagU3 σ a' b' = diagU3 σ (a * a') (b * b') := by
  apply Units.ext
  simp only [diagU3, Units.val_mul, coe_diagGL, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

omit [Finite K] in
theorem diagU3_one (σ : K ≃+* K) : diagU3 σ 1 1 = 1 := by
  apply Units.ext
  simp only [diagU3, coe_diagGL, Units.val_one]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagConj3U_one (hK : Nat.card K = (p ^ f) ^ 2) (x : Su K p f 3) :
    diagConj3U hK 1 1 x = x := by
  apply Subtype.ext
  simp [diagConj3U, diagU3_one]

theorem diagConj3U_mul (hK : Nat.card K = (p ^ f) ^ 2)
    (a b a' b' : normOne (unitaryInvolution K p f)) (x : Su K p f 3) :
    diagConj3U hK a b (diagConj3U hK a' b' x) = diagConj3U hK (a * a') (b * b') x := by
  apply Subtype.ext
  show diagU3 _ a b * (diagU3 _ a' b' * (x : GL (Fin 3) K) * (diagU3 _ a' b')⁻¹) *
      (diagU3 _ a b)⁻¹ = diagU3 _ (a * a') (b * b') * (x : GL (Fin 3) K) *
        (diagU3 _ (a * a') (b * b'))⁻¹
  rw [← diagU3_mul]
  group

variable (K p f) in
@[expose] noncomputable def uA : Su K p f 3 :=
  embSUid (unitaryInvolution K p f) 2 (negOneSU K p f)

variable (K p f) in
@[expose] noncomputable def uB : Su K p f 3 :=
  embSUid (unitaryInvolution K p f) 0 (negOneSU K p f)

theorem suMat_uA : suMat (uA K p f) = Matrix.diagonal ![-1, -1, 1] := by
  rw [uA, suMat, coe_embSUid]
  change embPair 2 (suMat (negOneSU K p f)) = _
  rw [suMat_negOneSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair]

theorem suMat_uB : suMat (uB K p f) = Matrix.diagonal ![1, -1, -1] := by
  rw [uB, suMat, coe_embSUid]
  change embPair 0 (suMat (negOneSU K p f)) = _
  rw [suMat_negOneSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair]

theorem uA_mul_self : uA K p f * uA K p f = 1 := by
  rw [uA, ← map_mul, negOneSU_mul_self, map_one]

theorem uB_mul_self : uB K p f * uB K p f = 1 := by
  rw [uB, ← map_mul, negOneSU_mul_self, map_one]

theorem uA_inv : (uA K p f)⁻¹ = uA K p f := inv_eq_of_mul_eq_one_right uA_mul_self

theorem uB_inv : (uB K p f)⁻¹ = uB K p f := inv_eq_of_mul_eq_one_right uB_mul_self

theorem uA_mul_uB : uA K p f * uB K p f = uB K p f * uA K p f := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_uA, suMat_uB, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem uA_ne_one (h2 : (2 : K) ≠ 0) : uA K p f ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg suMat h) 0) 0
  rw [suMat_uA, suMat_one] at this
  simp at this
  exact neg_one_ne_one_of_two_ne_zero h2 this

theorem uA_conj (hK : Nat.card K = (p ^ f) ^ 2) (x : Su K p f 3) :
    uA K p f * x * (uA K p f)⁻¹ =
      diagConj3U hK (negN (unitaryInvolution K p f)) (negN (unitaryInvolution K p f)) x := by
  apply Subtype.ext
  show (uA K p f : GL (Fin 3) K) * x * (uA K p f : GL (Fin 3) K)⁻¹ = _
  have h : (uA K p f : GL (Fin 3) K) = diagU3 (unitaryInvolution K p f) (negN _) (negN _) := by
    apply Units.ext
    exact (suMat_uA (K := K) (p := p) (f := f)).trans (by
      simp only [diagU3, coe_diagGL]
      congr 1
      funext i
      fin_cases i <;> simp [negN])
  rw [h]
  rfl

theorem uB_conj (hK : Nat.card K = (p ^ f) ^ 2) (x : Su K p f 3) :
    uB K p f * x * (uB K p f)⁻¹ =
      diagConj3U hK (negN (unitaryInvolution K p f)) 1 x := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, uB_inv, suMat_uB]
  show _ = (((diagU3 (unitaryInvolution K p f) (negN _) 1 : GL (Fin 3) K) * (x : GL (Fin 3) K) *
    (diagU3 (unitaryInvolution K p f) (negN _) 1 : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)
  simp only [Units.val_mul, diagU3, coe_diagGL, coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, negN, suMat]

omit [Finite K] in
theorem mul_self_eq_one_of_sign {σ : K ≃+* K} {a : normOne σ} (ha : a = 1 ∨ a = negN σ) :
    a * a = 1 := by
  rcases ha with rfl | rfl
  · simp
  · exact negN_mul_self σ

theorem rotSU_not_mem_range_torusTwo :
    rotSU (unitaryInvolution K p f) ∉ (torusTwo (unitaryInvolution K p f)).range := by
  rintro ⟨u, hu⟩
  have h := congrFun (congrFun (congrArg (fun g : Su K p f 2 =>
    ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hu) 0) 1
  simp [coe_torusTwo, rotSU, rotMat] at h

end Elements

section Center

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem isPerfect_su_three (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    Group.IsPerfect (Su K p f 3) := by
  have h : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (n := 3) (by norm_num)
      (pair_ne_three_two_of_five_le hq)
  exact Group.IsPerfect.ofSurjective
    (f := (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)).symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem mem_center_of_forall_commutator_mem_center_su (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : 5 ≤ p ^ f) {x : Su K p f 3}
    (h : ∀ y : Su K p f 3, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (Su K p f 3)) :
    x ∈ Subgroup.center (Su K p f 3) := by
  have := isPerfect_su_three hK hq
  have h1 : (QuotientGroup.mk x : Su K p f 3 ⧸ Subgroup.center (Su K p f 3)) ∈
      Subgroup.center (Su K p f 3 ⧸ Subgroup.center (Su K p f 3)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hz := Subgroup.mem_center_iff.mp (h y) (y * x)⁻¹
    have e : (y * x)⁻¹ * (x * y) = (y * x)⁻¹ * (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    rw [e, hz, mul_assoc, inv_mul_cancel, mul_one]
    exact h y
  rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot,
    QuotientGroup.eq_one_iff] at h1
  exact h1

theorem eq_one_of_mem_range_of_centralizesU {G : Type} [Group G] (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : 5 ≤ p ^ f) {θ : Su K p f 3 →* G} (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {m : G}
    (hm : m ∈ θ.range) (hc : ∀ x, m * θ x = θ x * m) {k : ℕ} (hk : orderOf m = 2 ^ k) :
    m = 1 := by
  obtain ⟨x, rfl⟩ := hm
  have hx : x ∈ Subgroup.center (Su K p f 3) := by
    refine mem_center_of_forall_commutator_mem_center_su hK hq fun y => hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h := hc y
    calc θ x * θ y * (θ x)⁻¹ * (θ y)⁻¹ = (θ x * θ y) * (θ x)⁻¹ * (θ y)⁻¹ := rfl
      _ = (θ y * θ x) * (θ x)⁻¹ * (θ y)⁻¹ := by rw [h]
      _ = 1 := by group
  obtain ⟨c, hcs⟩ := exists_scalar_of_mem_center_su hK hq (le_refl 3) hx
  have hdet : c ^ 3 = 1 := by
    have := det_suMat x
    rw [hcs, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    exact this
  have hx3 : x ^ 3 = 1 := by
    apply suMat_injective
    rw [pow_succ, pow_succ, pow_one, suMat_mul, suMat_mul, hcs, ← map_mul, ← map_mul, suMat_one]
    rw [show c * c * c = c ^ 3 by ring, hdet, map_one]
  have h3 : (θ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hdvd : 2 ^ k ∣ 3 := hk ▸ orderOf_dvd_of_pow_eq_one h3
  have hk0 : 2 ^ k = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) hdvd
  rw [hk0, orderOf_eq_one_iff] at hk
  exact hk

end Center

section Action

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {G : Type} [Group G]

@[expose] def SignActU (hK : Nat.card K = (p ^ f) ^ 2) (θ : Su K p f 3 →* G) (e : G) : Prop :=
  ∃ a b : normOne (unitaryInvolution K p f),
    (a = 1 ∨ a = negN (unitaryInvolution K p f)) ∧ (b = 1 ∨ b = negN (unitaryInvolution K p f)) ∧
      ∀ x : Su K p f 3, e * θ x * e⁻¹ = θ (diagConj3U hK a b x)

namespace SignActU

variable {hK : Nat.card K = (p ^ f) ^ 2} {θ : Su K p f 3 →* G}

theorem one : SignActU hK θ (1 : G) :=
  ⟨1, 1, Or.inl rfl, Or.inl rfl, fun x => by simp [diagConj3U_one]⟩

theorem of_commute {t : G} (h : ∀ x, t * θ x = θ x * t) : SignActU hK θ t :=
  ⟨1, 1, Or.inl rfl, Or.inl rfl, fun x => by
    rw [diagConj3U_one, h x]
    group⟩

theorem mul {e e' : G} (h : SignActU hK θ e) (h' : SignActU hK θ e') :
    SignActU hK θ (e * e') := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨a', b', ha', hb', h'⟩ := h'
  refine ⟨a * a', b * b', ?_, ?_, fun x => ?_⟩
  · rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;> simp [negN_mul_self]
  · rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp [negN_mul_self]
  · calc e * e' * θ x * (e * e')⁻¹ = e * (e' * θ x * e'⁻¹) * e⁻¹ := by group
      _ = e * θ (diagConj3U hK a' b' x) * e⁻¹ := by rw [h' x]
      _ = θ (diagConj3U hK a b (diagConj3U hK a' b' x)) := h _
      _ = θ (diagConj3U hK (a * a') (b * b') x) := by rw [diagConj3U_mul]

theorem inv {e : G} (h : SignActU hK θ e) : SignActU hK θ e⁻¹ := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  refine ⟨a, b, ha, hb, fun x => ?_⟩
  have h1 := h (diagConj3U hK a b x)
  rw [diagConj3U_mul, mul_self_eq_one_of_sign ha, mul_self_eq_one_of_sign hb, diagConj3U_one] at h1
  calc e⁻¹ * θ x * e⁻¹⁻¹ = e⁻¹ * θ x * e := by rw [inv_inv]
    _ = e⁻¹ * (e * θ (diagConj3U hK a b x) * e⁻¹) * e := by rw [h1]
    _ = θ (diagConj3U hK a b x) := by group

end SignActU

end Action

section FrameGroup

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {G : Type} [Group G]

variable (K p f) in
@[expose] noncomputable def frameGroupU (θ : Su K p f 3 →* G) (t : G) : Subgroup G :=
  Subgroup.closure {θ (uA K p f), θ (uB K p f), t}

section Basic

variable (hK : Nat.card K = (p ^ f) ^ 2) {θ : Su K p f 3 →* G} {t : G}

theorem z₁_mem_frameGroupU : θ (uA K p f) ∈ frameGroupU K p f θ t :=
  Subgroup.subset_closure (by simp)

theorem z₂_mem_frameGroupU : θ (uB K p f) ∈ frameGroupU K p f θ t :=
  Subgroup.subset_closure (by simp)

theorem t_mem_frameGroupU : t ∈ frameGroupU K p f θ t :=
  Subgroup.subset_closure (by simp)

include hK in
theorem signActU_z₁ : SignActU hK θ (θ (uA K p f)) :=
  ⟨negN _, negN _, Or.inr rfl, Or.inr rfl, fun x => by
    rw [← map_inv, ← map_mul, ← map_mul, uA_conj hK]⟩

include hK in
theorem signActU_z₂ : SignActU hK θ (θ (uB K p f)) :=
  ⟨negN _, 1, Or.inr rfl, Or.inl rfl, fun x => by
    rw [← map_inv, ← map_mul, ← map_mul, uB_conj hK]⟩

include hK in
theorem signActU_of_mem_frameGroupU (ht : ∀ x, t * θ x = θ x * t) {e : G}
    (he : e ∈ frameGroupU K p f θ t) : SignActU hK θ e := by
  induction he using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl | rfl
    · exact signActU_z₁ hK
    · exact signActU_z₂ hK
    · exact SignActU.of_commute ht
  | one => exact SignActU.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem frameGroupU_comm (ht : ∀ x, t * θ x = θ x * t) {x y : G}
    (hx : x ∈ frameGroupU K p f θ t) (hy : y ∈ frameGroupU K p f θ t) : x * y = y * x := by
  have hcomm : ({θ (uA K p f), θ (uB K p f), t} : Set G).Pairwise Commute := by
    have h12 : θ (uA K p f) * θ (uB K p f) = θ (uB K p f) * θ (uA K p f) := by
      rw [← map_mul, ← map_mul, uA_mul_uB]
    have h13 : θ (uA K p f) * t = t * θ (uA K p f) := (ht _).symm
    have h23 : θ (uB K p f) * t = t * θ (uB K p f) := (ht _).symm
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd rfl ‹_›
    · exact h12
    · exact h13
    · exact h12.symm
    · exact absurd rfl ‹_›
    · exact h23
    · exact h13.symm
    · exact h23.symm
    · exact absurd rfl ‹_›
  have := Subgroup.isMulCommutative_closure hcomm
  exact setLike_mul_comm (s := Subgroup.closure ({θ (uA K p f), θ (uB K p f), t} : Set G)) hx hy

theorem frameGroupU_sq (ht : ∀ x, t * θ x = θ x * t) (ht2 : t * t = 1) {x : G}
    (hx : x ∈ frameGroupU K p f θ t) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl | rfl
    · rw [← map_mul, uA_mul_self, map_one]
    · rw [← map_mul, uB_mul_self, map_one]
    · exact ht2
  | one => simp
  | mul x y hx hy hx1 hy1 =>
    have hc := frameGroupU_comm ht hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx1, hy1, one_mul]
  | inv x _ hx => rw [← _root_.mul_inv_rev, hx, inv_one]

end Basic

section Charts

variable (hK : Nat.card K = (p ^ f) ^ 2) (θ : Su K p f 3 →* G) {t : G}

structure IsChartEquiv (ψ : SL(2, fixedSubfield K p f) ≃* Su K p f 2) : Prop where
  neg : ψ (-1) = negOneSU K p f
  swap : ∃ g : GL (Fin 2) (fixedSubfield K p f), ∀ s : SL(2, fixedSubfield K p f),
    Matrix.diagonal ![(1 : K), -1] * suMat (ψ s) * Matrix.diagonal ![(1 : K), -1] =
      suMat (ψ (slConjugation 2 (fixedSubfield K p f) g s))

theorem isChartEquiv_psiEquiv {ζ μ : K} (hζ0 : ζ ≠ 0)
    (hζ : unitaryInvolution K p f ζ = -ζ) (h2 : (2 : K) ≠ 0)
    (hμ : unitaryInvolution K p f μ * μ = -1) : IsChartEquiv (psiEquiv hζ0 hζ h2 hμ) :=
  ⟨psiEquiv_neg_one hζ0 hζ h2 hμ, gSwapGL hζ0 h2 hζ, fun s => suMat_psiEquiv_conj hζ0 hζ h2 hμ s⟩

variable (ψ : SL(2, fixedSubfield K p f) ≃* Su K p f 2)

@[expose] noncomputable def uChart₁ : SL(2, fixedSubfield K p f) →* G :=
  (θ.comp (embSUid (unitaryInvolution K p f) 2)).comp ψ.toMonoidHom

@[expose] noncomputable def uChart₂ : SL(2, fixedSubfield K p f) →* G :=
  (θ.comp (embSUid (unitaryInvolution K p f) 0)).comp ψ.toMonoidHom

theorem range_uChart₁ : (uChart₁ θ ψ).range = (B12 K p f).map θ := by
  have h1 : ψ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr ψ.surjective
  rw [uChart₁, MonoidHom.range_comp, h1, ← MonoidHom.range_eq_map, MonoidHom.range_comp]
  rfl

theorem range_uChart₂ : (uChart₂ θ ψ).range = (B23 K p f).map θ := by
  have h1 : ψ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr ψ.surjective
  rw [uChart₂, MonoidHom.range_comp, h1, ← MonoidHom.range_eq_map, MonoidHom.range_comp]
  rfl

theorem suMat_diagConj2U_eq_swap {a b : normOne (unitaryInvolution K p f)}
    (ha : a = 1 ∨ a = negN (unitaryInvolution K p f))
    (hb : b = 1 ∨ b = negN (unitaryInvolution K p f)) (hab : a ≠ b) (A : Su K p f 2) :
    suMat (diagConj2U hK a b A) =
      Matrix.diagonal ![(1 : K), -1] * suMat A * Matrix.diagonal ![(1 : K), -1] := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · show (((diagU2 (unitaryInvolution K p f) 1 (negN _) : GL (Fin 2) K) * (A : GL (Fin 2) K) *
      (diagU2 (unitaryInvolution K p f) 1 (negN _) : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = _
    simp only [Units.val_mul, diagU2, coe_diagGL, coe_diagGL_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, negN, suMat]
  · show (((diagU2 (unitaryInvolution K p f) (negN _) 1 : GL (Fin 2) K) * (A : GL (Fin 2) K) *
      (diagU2 (unitaryInvolution K p f) (negN _) 1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = _
    simp only [Units.val_mul, diagU2, coe_diagGL, coe_diagGL_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, negN, suMat]
  · exact absurd rfl hab

variable {hK θ ψ}

theorem diagConj2U_psi_swap (hψ : IsChartEquiv ψ) {a b : normOne (unitaryInvolution K p f)}
    (ha : a = 1 ∨ a = negN (unitaryInvolution K p f))
    (hb : b = 1 ∨ b = negN (unitaryInvolution K p f)) (hab : a ≠ b) :
    ∃ g : GL (Fin 2) (fixedSubfield K p f), ∀ s : SL(2, fixedSubfield K p f),
      diagConj2U hK a b (ψ s) = ψ (slConjugation 2 (fixedSubfield K p f) g s) := by
  obtain ⟨g, hg⟩ := hψ.swap
  exact ⟨g, fun s => suMat_injective (by rw [suMat_diagConj2U_eq_swap hK ha hb hab, hg s])⟩

theorem act_uChart₁ (hψ : IsChartEquiv ψ) {e : G} {a b : normOne (unitaryInvolution K p f)}
    (ha : a = 1 ∨ a = negN (unitaryInvolution K p f))
    (hb : b = 1 ∨ b = negN (unitaryInvolution K p f))
    (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3U hK a b x)) :
    ∃ g : GL (Fin 2) (fixedSubfield K p f), ∀ s : SL(2, fixedSubfield K p f),
      e * uChart₁ θ ψ s * e⁻¹ = uChart₁ θ ψ (slConjugation 2 (fixedSubfield K p f) g s) := by
  by_cases hab : a = b
  · refine ⟨1, fun s => ?_⟩
    have h1 := h (embSUid (unitaryInvolution K p f) 2 (ψ s))
    rw [diagConj3U_embSUid_two, hab, diagConj2U_self] at h1
    rw [map_one, MulAut.one_apply]
    exact h1
  · obtain ⟨g, hg⟩ := diagConj2U_psi_swap (hK := hK) hψ ha hb hab
    refine ⟨g, fun s => ?_⟩
    have h1 := h (embSUid (unitaryInvolution K p f) 2 (ψ s))
    rw [diagConj3U_embSUid_two, hg s] at h1
    exact h1

theorem act_uChart₂ (hψ : IsChartEquiv ψ) {e : G} {a b : normOne (unitaryInvolution K p f)}
    (hb : b = 1 ∨ b = negN (unitaryInvolution K p f))
    (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3U hK a b x)) :
    ∃ g : GL (Fin 2) (fixedSubfield K p f), ∀ s : SL(2, fixedSubfield K p f),
      e * uChart₂ θ ψ s * e⁻¹ = uChart₂ θ ψ (slConjugation 2 (fixedSubfield K p f) g s) := by
  by_cases hb1 : b = 1
  · refine ⟨1, fun s => ?_⟩
    have h1 := h (embSUid (unitaryInvolution K p f) 0 (ψ s))
    rw [diagConj3U_embSUid_zero, hb1, diagConj2U_self] at h1
    rw [map_one, MulAut.one_apply]
    exact h1
  · obtain ⟨g, hg⟩ := diagConj2U_psi_swap (hK := hK) hψ hb (Or.inl rfl) hb1
    refine ⟨g, fun s => ?_⟩
    have h1 := h (embSUid (unitaryInvolution K p f) 0 (ψ s))
    rw [diagConj3U_embSUid_zero, hg s] at h1
    exact h1

theorem centralizes_B12_iff (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {e : G}
    {a b : normOne (unitaryInvolution K p f)}
    (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3U hK a b x)) :
    (∀ k ∈ (B12 K p f).map θ, k * e = e * k) ↔ a = b := by
  have hinj := comp_embSUid_injective hK hker 2
  constructor
  · intro hc
    by_contra hab
    have hk : θ (embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f))) ∈
        (B12 K p f).map θ := ⟨_, ⟨rotSU _, rfl⟩, rfl⟩
    have h1 := hc _ hk
    have h2 : e * θ (embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f))) *
        e⁻¹ = θ (embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f))) := by
      rw [← h1]
      group
    rw [h, diagConj3U_embSUid_two] at h2
    have h3 : diagConj2U hK a b (rotSU (unitaryInvolution K p f)) =
        rotSU (unitaryInvolution K p f) := hinj h2
    exact rotSU_not_mem_range_torusTwo (mem_range_torusTwo_of_diagConj2U_eq hK hab h3)
  · rintro rfl k hk
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
    have h1 := h (embSUid (unitaryInvolution K p f) 2 A)
    rw [diagConj3U_embSUid_two, diagConj2U_self] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem centralizes_B23_iff (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {e : G}
    {a b : normOne (unitaryInvolution K p f)}
    (h : ∀ x, e * θ x * e⁻¹ = θ (diagConj3U hK a b x)) :
    (∀ k ∈ (B23 K p f).map θ, k * e = e * k) ↔ b = 1 := by
  have hinj := comp_embSUid_injective hK hker 0
  constructor
  · intro hc
    by_contra hb
    have hk : θ (embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f))) ∈
        (B23 K p f).map θ := ⟨_, ⟨rotSU _, rfl⟩, rfl⟩
    have h1 := hc _ hk
    have h2 : e * θ (embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f))) *
        e⁻¹ = θ (embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f))) := by
      rw [← h1]
      group
    rw [h, diagConj3U_embSUid_zero] at h2
    have h3 : diagConj2U hK b 1 (rotSU (unitaryInvolution K p f)) =
        rotSU (unitaryInvolution K p f) := hinj h2
    exact rotSU_not_mem_range_torusTwo (mem_range_torusTwo_of_diagConj2U_eq hK hb h3)
  · rintro rfl k hk
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
    have h1 := h (embSUid (unitaryInvolution K p f) 0 A)
    rw [diagConj3U_embSUid_zero, diagConj2U_self] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

omit [Finite K] in
theorem mul_negN_eq_iff {σ : K ≃+* K} {a c : normOne σ} (h : negN σ ≠ 1)
    (ha : a = 1 ∨ a = negN σ) (hc : c = 1 ∨ c = negN σ) : a * negN σ = c ↔ ¬ a = c := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [h, h.symm, negN_mul_self]

omit [Finite K] in
theorem mul_negN_eq_one_iff {σ : K ≃+* K} {c : normOne σ} (h : negN σ ≠ 1)
    (hc : c = 1 ∨ c = negN σ) : c * negN σ = 1 ↔ ¬ c = 1 := by
  rcases hc with rfl | rfl <;> simp [h, negN_mul_self]

theorem index_two_B12 (hK : Nat.card K = (p ^ f) ^ 2) (hker : θ.ker ≤ Subgroup.center (Su K p f 3))
    (ht : ∀ x, t * θ x = θ x * t) (h2 : (2 : K) ≠ 0) :
    (axisSub (frameGroupU K p f θ t) ((B12 K p f).map θ)).relIndex
      (frameGroupU K p f θ t) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨θ (uB K p f), z₂_mem_frameGroupU, fun b hb => ?_⟩
  obtain ⟨a, c, ha, hc, hab⟩ := signActU_of_mem_frameGroupU hK ht hb
  have hbz : b * θ (uB K p f) ∈ frameGroupU K p f θ t :=
    (frameGroupU K p f θ t).mul_mem hb z₂_mem_frameGroupU
  have hbz_act : ∀ x, (b * θ (uB K p f)) * θ x * (b * θ (uB K p f))⁻¹ =
      θ (diagConj3U hK (a * negN (unitaryInvolution K p f)) (c * 1) x) := fun x => by
    calc (b * θ (uB K p f)) * θ x * (b * θ (uB K p f))⁻¹
        = b * (θ (uB K p f) * θ x * (θ (uB K p f))⁻¹) * b⁻¹ := by group
      _ = θ (diagConj3U hK (a * negN (unitaryInvolution K p f)) (c * 1) x) := by
        rw [← map_inv, ← map_mul, ← map_mul, uB_conj hK, hab, diagConj3U_mul]
  rw [xor_iff_iff_not, mem_axisSub_iff, mem_axisSub_iff]
  simp only [hb, hbz, true_and]
  rw [centralizes_B12_iff hker hbz_act, centralizes_B12_iff hker hab, mul_one,
    mul_negN_eq_iff (negN_ne_one _ h2) ha hc]

theorem index_two_B23 (hK : Nat.card K = (p ^ f) ^ 2) (hker : θ.ker ≤ Subgroup.center (Su K p f 3))
    (ht : ∀ x, t * θ x = θ x * t) (h2 : (2 : K) ≠ 0) :
    (axisSub (frameGroupU K p f θ t) ((B23 K p f).map θ)).relIndex
      (frameGroupU K p f θ t) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨θ (uA K p f), z₁_mem_frameGroupU, fun b hb => ?_⟩
  obtain ⟨a, c, ha, hc, hab⟩ := signActU_of_mem_frameGroupU hK ht hb
  have hbz : b * θ (uA K p f) ∈ frameGroupU K p f θ t :=
    (frameGroupU K p f θ t).mul_mem hb z₁_mem_frameGroupU
  have hbz_act : ∀ x, (b * θ (uA K p f)) * θ x * (b * θ (uA K p f))⁻¹ =
      θ (diagConj3U hK (a * negN (unitaryInvolution K p f))
        (c * negN (unitaryInvolution K p f)) x) := fun x => by
    calc (b * θ (uA K p f)) * θ x * (b * θ (uA K p f))⁻¹
        = b * (θ (uA K p f) * θ x * (θ (uA K p f))⁻¹) * b⁻¹ := by group
      _ = θ (diagConj3U hK (a * negN (unitaryInvolution K p f))
          (c * negN (unitaryInvolution K p f)) x) := by
        rw [← map_inv, ← map_mul, ← map_mul, uA_conj hK, hab, diagConj3U_mul]
  rw [xor_iff_iff_not, mem_axisSub_iff, mem_axisSub_iff]
  simp only [hb, hbz, true_and]
  rw [centralizes_B23_iff hker hbz_act, centralizes_B23_iff hker hab,
    mul_negN_eq_one_iff (negN_ne_one _ h2) hc]

theorem diagData_uChart₁ (hK : Nat.card K = (p ^ f) ^ 2) (hψ : IsChartEquiv ψ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) (ht : ∀ x, t * θ x = θ x * t)
    (ht2 : t * t = 1) (h2 : (2 : K) ≠ 0) :
    DiagData (uChart₁ θ ψ) (frameGroupU K p f θ t) where
  inj := (comp_embSUid_injective hK hker 2).comp ψ.injective
  comm := fun x hx y hy => frameGroupU_comm ht hx hy
  sq := fun x hx => frameGroupU_sq ht ht2 hx
  neg_mem := by
    show θ (embSUid (unitaryInvolution K p f) 2 (ψ (-1))) ∈ _
    rw [hψ.neg]
    exact z₁_mem_frameGroupU
  diag := fun e he => by
    obtain ⟨a, b, ha, hb, h⟩ := signActU_of_mem_frameGroupU hK ht he
    exact act_uChart₁ hψ ha hb h
  index_two := by
    rw [range_uChart₁]
    exact index_two_B12 hK hker ht h2

theorem diagData_uChart₂ (hK : Nat.card K = (p ^ f) ^ 2) (hψ : IsChartEquiv ψ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) (ht : ∀ x, t * θ x = θ x * t)
    (ht2 : t * t = 1) (h2 : (2 : K) ≠ 0) :
    DiagData (uChart₂ θ ψ) (frameGroupU K p f θ t) where
  inj := (comp_embSUid_injective hK hker 0).comp ψ.injective
  comm := fun x hx y hy => frameGroupU_comm ht hx hy
  sq := fun x hx => frameGroupU_sq ht ht2 hx
  neg_mem := by
    show θ (embSUid (unitaryInvolution K p f) 0 (ψ (-1))) ∈ _
    rw [hψ.neg]
    exact z₂_mem_frameGroupU
  diag := fun e he => by
    obtain ⟨a, b, ha, hb, h⟩ := signActU_of_mem_frameGroupU hK ht he
    exact act_uChart₂ hψ hb h
  index_two := by
    rw [range_uChart₂]
    exact index_two_B23 hK hker ht h2

theorem inSigma_frameGroupU_left (hK : Nat.card K = (p ^ f) ^ 2) (hψ : IsChartEquiv ψ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) (ht : ∀ x, t * θ x = θ x * t)
    (ht2 : t * t = 1) (h2 : (2 : K) ≠ 0) :
    InSigma (fixedSubfield K p f) (frameGroupU K p f θ t) ((B12 K p f).map θ) :=
  ⟨uChart₁ θ ψ, range_uChart₁ θ ψ, diagData_uChart₁ hK hψ hker ht ht2 h2⟩

theorem inSigma_frameGroupU_right (hK : Nat.card K = (p ^ f) ^ 2) (hψ : IsChartEquiv ψ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) (ht : ∀ x, t * θ x = θ x * t)
    (ht2 : t * t = 1) (h2 : (2 : K) ≠ 0) :
    InSigma (fixedSubfield K p f) (frameGroupU K p f θ t) ((B23 K p f).map θ) :=
  ⟨uChart₂ θ ψ, range_uChart₂ θ ψ, diagData_uChart₂ hK hψ hker ht ht2 h2⟩

theorem frameGroupU_diagAction (hK : Nat.card K = (p ^ f) ^ 2)
    (ht : ∀ x, t * θ x = θ x * t) : DiagActionU hK θ (frameGroupU K p f θ t) := fun e he => by
  obtain ⟨a, b, -, -, h⟩ := signActU_of_mem_frameGroupU hK ht he
  exact ⟨a, b, h⟩

end Charts

section Order

variable {hK : Nat.card K = (p ^ f) ^ 2} {θ : Su K p f 3 →* G} {t : G}

theorem eight_le_card_frameGroupU [Finite G] (hK : Nat.card K = (p ^ f) ^ 2)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) (ht : ∀ x, t * θ x = θ x * t)
    (ht2 : t * t = 1) (h2 : (2 : K) ≠ 0) (hz : θ (uA K p f) ≠ 1) (ht1 : t ≠ 1)
    (hnot : t ∉ θ.range) : 8 ≤ Nat.card (frameGroupU K p f θ t) := by
  classical
  have := Fintype.ofFinite G
  set A := frameGroupU K p f θ t with hA
  set C := axisSub A ((B12 K p f).map θ) with hC
  have hCA : C ≤ A := inf_le_left
  have hidx : C.relIndex A = 2 := index_two_B12 hK hker ht h2
  have h1 := (C.subgroupOf A).card_mul_index
  have h3 : Nat.card (C.subgroupOf A) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  rw [h3] at h1
  have hidx' : (C.subgroupOf A).index = 2 := hidx
  rw [hidx'] at h1
  have hz1 : θ (uA K p f) ∈ C := by
    refine mem_axisSub_iff.mpr ⟨z₁_mem_frameGroupU, ?_⟩
    exact (centralizes_B12_iff hker (a := negN (unitaryInvolution K p f))
      (b := negN (unitaryInvolution K p f)) (hK := hK) (fun x => by
        rw [← map_inv, ← map_mul, ← map_mul, uA_conj hK])).mpr rfl
  have ht1' : t ∈ C := by
    refine mem_axisSub_iff.mpr ⟨t_mem_frameGroupU, ?_⟩
    exact (centralizes_B12_iff hker (a := 1) (b := 1) (hK := hK) (fun x => by
      rw [diagConj3U_one, ht x]; group)).mpr rfl
  have hzt : θ (uA K p f) ≠ t := fun h => hnot (h ▸ ⟨uA K p f, rfl⟩)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hS : ({1, θ (uA K p f), t, θ (uA K p f) * t} : Finset G) ⊆ (C : Set G).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Set.mem_toFinset]
    rcases hx with rfl | rfl | rfl | rfl
    · exact C.one_mem
    · exact hz1
    · exact ht1'
    · exact C.mul_mem hz1 ht1'
  have hcard : ({1, θ (uA K p f), t, θ (uA K p f) * t} : Finset G).card = 4 := by
    have n1 : (1 : G) ∉ ({θ (uA K p f), t, θ (uA K p f) * t} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hz.symm, ht1.symm, fun h => hzt ?_⟩
      rw [← hti]
      exact eq_inv_of_mul_eq_one_left h.symm
    have n2 : θ (uA K p f) ∉ ({t, θ (uA K p f) * t} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hzt, fun h => ht1 ?_⟩
      exact mul_left_cancel (a := θ (uA K p f)) (b := t) (c := 1) (by rw [mul_one]; exact h.symm)
    have n3 : t ∉ ({θ (uA K p f) * t} : Finset G) := by
      simp only [Finset.mem_singleton]
      exact fun h => hz (mul_right_cancel (a := θ (uA K p f)) (b := t) (c := 1)
        (by rw [one_mul]; exact h.symm))
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_singleton]
  have h4 : 4 ≤ Nat.card C := by
    have := Finset.card_le_card hS
    rw [hcard] at this
    simpa [Nat.card_eq_fintype_card, Set.toFinset_card] using this
  omega

end Order

section Blocks

variable {θ : Su K p f 3 →* G}

theorem not_commutes_B12_B23 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) :
    ¬ Commutes ((B12 K p f).map θ) ((B23 K p f).map θ) := by
  intro hc
  set a : Su K p f 3 := embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f))
    with ha
  set b : Su K p f 3 := embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f))
    with hb
  have h := hc (θ a) ⟨a, ⟨_, rfl⟩, rfl⟩ (θ b) ⟨b, ⟨_, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul] at h
  obtain ⟨z, hz⟩ : ∃ z : Su K p f 3, z = (b * a)⁻¹ * (a * b) := ⟨_, rfl⟩
  have hk : z ∈ θ.ker := by
    rw [hz, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hcs⟩ := exists_scalar_of_mem_center_su hK hq (le_refl 3) (hker hk)
  have h' : a * b = b * a * z := by rw [hz]; group
  have hm := congrArg suMat h'
  rw [suMat_mul, suMat_mul, suMat_mul, hcs, ha, hb] at hm
  have h02 := congrFun (congrFun hm 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, suMat, coe_embSUid, embPair, rotSU, rotMat,
    Matrix.scalar_apply, Matrix.diagonal_apply] at h02

theorem map_B12_ne_map_B23 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) : (B12 K p f).map θ ≠ (B23 K p f).map θ := by
  intro h
  set a : Su K p f 3 := embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f))
    with ha
  have hx : θ a ∈ (B23 K p f).map θ := h ▸ ⟨a, ⟨_, rfl⟩, rfl⟩
  obtain ⟨b, ⟨A, rfl⟩, hb⟩ := hx
  obtain ⟨z, hz⟩ : ∃ z : Su K p f 3,
      z = (embSUid (unitaryInvolution K p f) 0 A)⁻¹ * a := ⟨_, rfl⟩
  have hk : z ∈ θ.ker := by
    rw [hz, MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel]
  obtain ⟨c, hcs⟩ := exists_scalar_of_mem_center_su hK hq (le_refl 3) (hker hk)
  have h' : a = embSUid (unitaryInvolution K p f) 0 A * z := by rw [hz]; group
  have hm := congrArg suMat h'
  rw [suMat_mul, hcs, ha] at hm
  have h01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, suMat, coe_embSUid, embPair, rotSU, rotMat,
    Matrix.scalar_apply, Matrix.diagonal_apply] at h01

end Blocks

section LocalDatum

structure LocalDatumU (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    {G : Type} [Group G] (L₁ L₂ : Subgroup G) (t : G) : Prop where
  chart : ∃ θ : Su K p f 3 →* G, θ.ker ≤ Subgroup.center (Su K p f 3) ∧
    (B12 K p f).map θ = L₁ ∧ (B23 K p f).map θ = L₂ ∧ ∀ x, t * θ x = θ x * t
  two_element : ∃ k : ℕ, orderOf t = 2 ^ (k + 1)

theorem LocalDatumU.exists_frameGroup [Finite G] {L₁ L₂ : Subgroup G} {t : G}
    (hLD : LocalDatumU K p f L₁ L₂ t) (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) :
    ∃ A : Subgroup G, 8 ≤ Nat.card A ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      (∀ x ∈ A, x * x = 1) ∧ InSigma (fixedSubfield K p f) A L₁ ∧
        InSigma (fixedSubfield K p f) A L₂ ∧ ¬ Commutes L₁ L₂ ∧
          UnitaryA2Pair K p f A L₁ L₂ ∧ IsLine A L₁ L₂ ∧ IsLine A L₂ L₁ := by
  obtain ⟨θ, hker, hL₁, hL₂, ht⟩ := hLD.chart
  obtain ⟨k, hk⟩ := hLD.two_element
  set t' : G := t ^ (2 ^ k) with ht'
  have hord : orderOf t' = 2 := by
    rw [ht', orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (Nat.le_succ k)),
      hk, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have ht'2 : t' * t' = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  have ht'1 : t' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    omega
  have htc : ∀ x, t' * θ x = θ x * t' := fun x => ((Commute.pow_left (ht x) (2 ^ k)) : _)
  have hnot : t' ∉ θ.range := fun hm =>
    ht'1 (eq_one_of_mem_range_of_centralizesU hK hq hker hm htc (k := 1) (by simpa using hord))
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨μ, hμ⟩ := exists_norm_eq_neg_one hK
  have hψ := isChartEquiv_psiEquiv hζ0 hζ h2 hμ
  have hz : θ (uA K p f) ≠ 1 := fun h => negOneSU_ne_one h2
    ((comp_embSUid_injective hK hker 2) (show θ (embSUid (unitaryInvolution K p f) 2
      (negOneSU K p f)) = θ (embSUid (unitaryInvolution K p f) 2 1) by
        rw [map_one, map_one]; exact h))
  have hS₁ : InSigma (fixedSubfield K p f) (frameGroupU K p f θ t') L₁ := by
    rw [← hL₁]
    exact inSigma_frameGroupU_left hK hψ hker htc ht'2 h2
  have hS₂ : InSigma (fixedSubfield K p f) (frameGroupU K p f θ t') L₂ := by
    rw [← hL₂]
    exact inSigma_frameGroupU_right hK hψ hker htc ht'2 h2
  have hLin : UnitaryA2Pair K p f (frameGroupU K p f θ t') L₁ L₂ :=
    unitaryA2Pair_of_diagAction hK hker hL₁ hL₂ (frameGroupU_diagAction hK htc) hS₁ hS₂
  have hodd := odd_natCard_fixedSubfield hK hp
  have h5 : 5 ≤ Nat.card (fixedSubfield K p f) := by
    rw [card_fixedSubfield hK]
    exact hq
  have hline := hLin.isLine hK hS₁ hS₂ hodd h5
  have hLnc : ¬ Commutes L₁ L₂ := by
    rw [← hL₁, ← hL₂]
    exact not_commutes_B12_B23 hK hq hker
  exact ⟨frameGroupU K p f θ t', eight_le_card_frameGroupU hK hker htc ht'2 h2 hz ht'1 hnot,
    fun x hx y hy => frameGroupU_comm htc hx hy, fun x hx => frameGroupU_sq htc ht'2 hx, hS₁, hS₂,
    hLnc, hLin, hline.1, hline.2⟩

theorem LocalDatumU.exists_rankFrame [Finite G] {L₁ L₂ : Subgroup G} {t : G}
    (hLD : LocalDatumU K p f L₁ L₂ t) (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (h₁ : L₁ ∈ Ω) (h₂ : L₂ ∈ Ω) :
    ∃ A : Subgroup G, RankFrame (fixedSubfield K p f) Ω A (sigmaSet (fixedSubfield K p f) Ω A) ∧
      L₁ ∈ sigmaSet (fixedSubfield K p f) Ω A ∧ L₂ ∈ sigmaSet (fixedSubfield K p f) Ω A ∧
        L₁ ≠ L₂ ∧ ¬ Commutes L₁ L₂ ∧ UnitaryA2Pair K p f A L₁ L₂ ∧ IsLine A L₁ L₂ ∧
          IsLine A L₂ L₁ := by
  obtain ⟨A, hcard, -, hsq, hS₁, hS₂, hnc, hLin, hl₁, hl₂⟩ := hLD.exists_frameGroup hK hp hq
  obtain ⟨θ, hker, hL₁, hL₂, -⟩ := hLD.chart
  have hne : L₁ ≠ L₂ := by
    rw [← hL₁, ← hL₂]
    exact map_B12_ne_map_B23 hK hq hker
  have hodd := odd_natCard_fixedSubfield hK hp
  have h5 : 5 ≤ Nat.card (fixedSubfield K p f) := by
    rw [card_fixedSubfield hK]
    exact hq
  exact ⟨A, ⟨hodd, h5, hΩ, hsq, rfl, ⟨L₁, ⟨h₁, hS₁⟩, L₂, ⟨h₂, hS₂⟩, hne⟩, hcard⟩, ⟨h₁, hS₁⟩,
    ⟨h₂, hS₂⟩, hne, hnc, hLin, hl₁, hl₂⟩

end LocalDatum

end FrameGroup

end CFSG.ClassicalInvolution
