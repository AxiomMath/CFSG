module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Dich
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Inner

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne Subgroup Matrix

open GenLocU4Basic

namespace GenLocU4Inner

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem conj_eq_of_smul {u v : GL (Fin 4) K} {l : K} (hl : l ≠ 0)
    (h : (u : Matrix (Fin 4) (Fin 4) K) = l • (v : Matrix (Fin 4) (Fin 4) K)) (g : GL (Fin 4) K) :
    u * g * u⁻¹ = v * g * v⁻¹ := by
  have hu : u = Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) * v := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, h]
    rfl
  rw [hu]
  have hc : ∀ x : GL (Fin 4) K, Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) * x =
      x * Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) :=
    fun x => Matrix.GeneralLinearGroup.scalar_commute _ x
  calc Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) * v * g *
        (Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) * v)⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) * (v * g * v⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl))⁻¹ := by group
    _ = (v * g * v⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) *
          (Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl))⁻¹ := by rw [hc]
    _ = v * g * v⁻¹ := by group

omit [Finite K] in
theorem mem_primeFormUnitary_of_isUnitaryU {p f : ℕ} (h : UnitaryFieldData p f K) {x : GL (Fin 4) K}
    (hx : IsUnitaryU (p ^ f) (x : Matrix (Fin 4) (Fin 4) K)) : x ∈ primeFormUnitary h (idGram K 4) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  exact hx

omit [Finite K] in
theorem isUnitaryU_smul {q : ℕ} {M : Matrix (Fin 4) (Fin 4) K} (hM : IsUnitaryU q M) {c : K}
    (hc : c ^ (q + 1) = 1) : IsUnitaryU q (c • M) := by
  unfold IsUnitaryU at hM ⊢
  rw [map_smul_pow, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM,
    ← pow_succ, hc, one_smul]

theorem rho_sq_scalar {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {A : Type}
    [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (ρ : A → GL (Fin 4) K)
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    (hsq : ∀ a, α a * α a = 1) (a : A) :
    ∃ c : K, (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K) =
      c • (1 : Matrix (Fin 4) (Fin 4) K) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hρ' : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      ((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = ρ a * (g : GL (Fin 4) K) * (ρ a)⁻¹ :=
    fun a g => Units.ext (by rw [hρ a g, Units.val_mul, Units.val_mul])
  obtain ⟨c, -, hc⟩ := proportional_of_conj_eq h hp2 (u := ρ a * ρ a) (v := 1) (fun g hg => by
    have h1 := congrArg (fun φ : MulAut ↥(StatedSU 4 (p ^ f) K) =>
      ((φ ⟨g, hg⟩ : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K)) (hsq a)
    simp only [MulAut.mul_apply, hρ', MulAut.one_apply] at h1
    calc ρ a * ρ a * g * (ρ a * ρ a)⁻¹ = ρ a * (ρ a * g * (ρ a)⁻¹) * (ρ a)⁻¹ := by group
      _ = g := h1
      _ = 1 * g * 1⁻¹ := by group)
  exact ⟨c, by rw [← Units.val_mul]; rw [Units.val_mul, Units.val_one] at hc; exact hc⟩

end GenLocU4Inner

namespace GenLocU4Basic

variable {K : Type} [Field K] [Finite K]

open GenLocU4Inner

theorem gammaAct_su4_of_commuting_squares {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    (hab : ∀ a b, ρ a * ρ b = ρ b * ρ a)
    (hsq : ∀ a, ∃ μ : K, μ ^ (p ^ f + 1) = 1 ∧
      (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K) = (μ * μ) • (1 : Matrix (Fin 4) (Fin 4) K)) :
    gammaAct α = ⊤ := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  choose μ hμN hμ using hsq
  have hμ0 : ∀ a, μ a ≠ 0 := fun a h0 => by
    have := hμN a
    rw [h0, zero_pow (Nat.succ_ne_zero _)] at this
    exact zero_ne_one this
  choose ρ' hρ'v using fun a => GenLocL4Inner.exists_unit_smul (ρ a) (inv_ne_zero (hμ0 a))
  have hρv : ∀ a, (ρ a : Matrix (Fin 4) (Fin 4) K) = μ a • (ρ' a : Matrix (Fin 4) (Fin 4) K) :=
    fun a => by rw [hρ'v a, smul_smul, mul_inv_cancel₀ (hμ0 a), one_smul]
  have hsq' : ∀ a, ρ' a * ρ' a = 1 := fun a => by
    apply Units.ext
    rw [Units.val_mul, hρ'v a, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hμ a, smul_smul,
      show (μ a)⁻¹ * (μ a)⁻¹ * (μ a * μ a) = 1 by have := hμ0 a; field_simp, one_smul]
    rfl
  have hcomm' : ∀ a b, ρ' a * ρ' b = ρ' b * ρ' a := fun a b => by
    apply Units.ext
    have h1 := congrArg Units.val (hab a b)
    rw [Units.val_mul, Units.val_mul] at h1
    rw [Units.val_mul, Units.val_mul, hρ'v a, hρ'v b, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, smul_smul, mul_comm (μ a)⁻¹, h1]
  have hU' : ∀ a, IsUnitaryU (p ^ f) (ρ' a : Matrix (Fin 4) (Fin 4) K) := fun a => by
    rw [hρ'v a]
    refine isUnitaryU_smul (hU a) ?_
    rw [inv_pow, hμN a, inv_one]
  have hmemU : ∀ a, ρ' a ∈ primeFormUnitary h (idGram K 4) := fun a =>
    mem_primeFormUnitary_of_isUnitaryU h (hU' a)
  have hconj : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      ((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = ρ' a * g * (ρ' a)⁻¹ := fun a g => by
    have h1 : ((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = ρ a * g * (ρ a)⁻¹ :=
      Units.ext (by rw [hρ a g, Units.val_mul, Units.val_mul])
    rw [h1]
    exact conj_eq_of_smul (hμ0 a) (hρv a) g
  let U := primeFormUnitary h (idGram K 4)
  let ρU : A → ↥U := fun a => ⟨ρ' a, hmemU a⟩
  have hρU : ∀ a, α a = GenLocDiagU.conjSUHom h 4 (ρU a) := fun a =>
    MulEquiv.ext fun g => Subtype.ext (by rw [GenLocDiagU.coe_conjSUHom]; exact hconj a g)
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Subgroup ↥U, S₀ = Subgroup.closure (Set.range ρU) := ⟨_, rfl⟩
  have hρUmem : ∀ a, ρU a ∈ S₀ := fun a => hS₀ ▸ Subgroup.subset_closure ⟨a, rfl⟩
  have hcommU : ∀ a b, ρU a * ρU b = ρU b * ρU a := fun a b => Subtype.ext (hcomm' a b)
  have hsqU : ∀ a, ρU a * ρU a = 1 := fun a => Subtype.ext (hsq' a)
  have hcomm₀ : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y = y * x := by
    have h1 : S₀ ≤ Subgroup.centralizer (Set.range ρU : Set ↥U) := by
      rw [hS₀, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, rfl⟩
      exact hcommU b a
    have h2 : S₀ ≤ Subgroup.centralizer (S₀ : Set ↥U) := by
      conv_lhs => rw [hS₀]
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (h1 hy) (ρU a) ⟨a, rfl⟩).symm
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm
  have hsq₀ : ∀ x ∈ S₀, x * x = 1 := by
    intro x hx
    rw [hS₀] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        exact hsqU a
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
        have hxS : x ∈ S₀ := hS₀ ▸ hx
        have hyS : y ∈ S₀ := hS₀ ▸ hy
        calc x * y * (x * y) = x * (y * x) * y := by rw [mul_assoc, mul_assoc, ← mul_assoc y]
          _ = x * (x * y) * y := by rw [hcomm₀ y hyS x hxS]
          _ = (x * x) * (y * y) := by simp only [mul_assoc]
          _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x hx ihx => rw [← _root_.mul_inv_rev, ihx, inv_one]
  have hpq : 2 ∣ p ^ f + 1 := even_iff_two_dvd.1 ((h.prime.odd_of_ne_two hp2).pow).add_one
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_two hpq S₀ hcomm₀
    (fun x hx => by rw [pow_two]; exact hsq₀ x hx)
  let c : ↥U →* ↥U := (MulAut.conj P⁻¹).toMonoidHom
  have hc : ∀ x, c x = P⁻¹ * x * P := fun x => by simp [c]
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Subgroup ↥U, S₁ = S₀.map c := ⟨_, rfl⟩
  have hS₁mem : ∀ s ∈ S₁, ∃ x ∈ S₀, c x = s := fun s hs => by
    rw [hS₁] at hs
    exact hs
  have hA₁ : CFSG.IsElementaryAbelian 2 ↥S₁ := by
    refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
    · obtain ⟨x, hx, rfl⟩ := hS₁mem u hu
      obtain ⟨y, hy, rfl⟩ := hS₁mem v hv
      rw [← map_mul, ← map_mul, hcomm₀ x hx y hy]
    · obtain ⟨x, hx, rfl⟩ := hS₁mem u hu
      rw [← map_mul, hsq₀ x hx, map_one]
  let ρ₁ : ↥S₁ →* GL (Fin 4) K := U.subtype.comp S₁.subtype
  let α₁ : ↥S₁ →* MulAut ↥(StatedSU 4 (p ^ f) K) := (GenLocDiagU.conjSUHom h 4).comp S₁.subtype
  have htop : gammaAct α₁ = ⊤ := by
    refine gammaAct_su_of_diag hp hp2 hK hA₁ α₁ ρ₁ (fun s => ?_) (fun s => ?_) (fun s g => ?_)
    · obtain ⟨x, hx, hxs⟩ := hS₁mem s s.2
      have e : ((s : ↥U) : GL (Fin 4) K) = ((P⁻¹ * x * P : ↥U) : GL (Fin 4) K) := by
        rw [← hxs, hc]
      show (((s : ↥U) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag
      rw [e]
      exact hP x hx
    · obtain ⟨x, hx, hxs⟩ := hS₁mem s s.2
      have h1 : (s : ↥U) * s = 1 := by rw [← hxs, ← map_mul, hsq₀ x hx, map_one]
      exact congrArg Subtype.val h1
    · exact GenLocDiagU.coe_conjSUHom h (s : ↥U) g
  let β : MulAut ↥(StatedSU 4 (p ^ f) K) := GenLocDiagU.conjSUHom h 4 P⁻¹
  refine GenLocL4Inner.gammaAct_eq_top_of_range_conj hA hA₁ α α₁ β ?_ htop
  have hcx : ∀ x ∈ S₀, GenLocDiagU.conjSUHom h 4 x ∈ α.range := fun x hx => by
    have : S₀ ≤ α.range.comap (GenLocDiagU.conjSUHom h 4) := by
      rw [hS₀, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨a, hρU a⟩
    exact this hx
  refine le_antisymm ?_ ?_
  · rintro _ ⟨s, rfl⟩
    obtain ⟨x, hx, hxs⟩ := hS₁mem s s.2
    refine ⟨_, hcx x hx, ?_⟩
    change β * GenLocDiagU.conjSUHom h 4 x * β⁻¹ = GenLocDiagU.conjSUHom h 4 (s : ↥U)
    rw [← hxs, hc]
    simp only [β, map_mul, map_inv, inv_inv]
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have hmem : c (ρU a) ∈ S₁ := by
      rw [hS₁]
      exact Subgroup.mem_map_of_mem _ (hρUmem a)
    refine ⟨⟨c (ρU a), hmem⟩, ?_⟩
    change GenLocDiagU.conjSUHom h 4 (c (ρU a)) = β * α a * β⁻¹
    rw [hc, hρU a]
    simp only [β, map_mul, map_inv, inv_inv]

end GenLocU4Basic

namespace GenLocU4Inner

variable {K : Type} [Field K] [Finite K]

@[expose] def Su4ExtStmt (K : Type) [Field K] [Finite K] (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)), IsRank23 A →
      ∀ ρ : A → GL (Fin 4) K, (∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K)) →
      (∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
        (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((ρ a)⁻¹ : GL (Fin 4) K)) →
      (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∀ (a₀ : A) (c : K), (∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ c) →
      (ρ a₀ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) =
        c • (1 : Matrix (Fin 4) (Fin 4) K) → gammaAct α = ⊤

@[expose] def Su4QuatStmt (K : Type) [Field K] [Finite K] (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)), IsRank23 A →
      (∀ c : A, IsInnerDiagU4 (α c)) →
      ∀ ρ : A → GL (Fin 4) K, (∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K)) →
      (∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
        (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((ρ a)⁻¹ : GL (Fin 4) K)) →
      ∀ (a b : A), (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
        -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K)) → gammaAct α = ⊤

theorem gammaAct_su4_inner_of_classes {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) (hExt : Su4ExtStmt K p f)
    (hQuat : Su4QuatStmt K p f) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A)
    (hinner : ∀ c : A, IsInnerDiagU4 (α c)) : gammaAct α = ⊤ := by
  choose ρ hU hρ using hinner
  have hEA := hA.1
  have hsq_aut : ∀ a, α a * α a = 1 := fun a => by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEA a, map_one]
  have hcomm_aut : ∀ a b : A, α a * α b = α b * α a := fun a b => by
    rw [← map_mul, ← map_mul, mul_comm' a b]
  by_cases hanti : ∃ a b : A, (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))
  · obtain ⟨a, b, hab⟩ := hanti
    exact hQuat hp hp2 hK hq α hA (fun c => ⟨ρ c, hU c, hρ c⟩) ρ hU hρ a b hab
  · push Not at hanti
    have hab : ∀ a b, ρ a * ρ b = ρ b * ρ a := fun a b =>
      (comm_or_anticomm_U4_of_card hp hp2 hK α ρ hρ hsq_aut a b (hcomm_aut a b)).resolve_right (hanti a b)
    by_cases hall : ∀ a, ∃ μ : K, μ ^ (p ^ f + 1) = 1 ∧
        (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K) = (μ * μ) • (1 : Matrix (Fin 4) (Fin 4) K)
    · exact gammaAct_su4_of_commuting_squares hp hp2 hK hEA α ρ hU hρ hab hall
    · push Not at hall
      obtain ⟨a₀, ha₀⟩ := hall
      obtain ⟨c, hc⟩ := rho_sq_scalar hp hp2 hK α ρ hρ hsq_aut a₀
      exact hExt hp hp2 hK hq α hA ρ hU hρ hab a₀ c
        (fun μ hμ hμc => ha₀ μ hμ (by rw [hc, ← hμc])) hc

end GenLocU4Inner

end CFSG.GH74.Generic.BProg.B2
