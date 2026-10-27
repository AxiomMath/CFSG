module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3Good
public import CFSG.GH74.Generic.BProg.B2.GenLocU3

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.LieType.Steinberg
  CFSG.GH74.Generic.BProg.B2.GenLocU3NF CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

namespace GenLocU3Small

open GenLocU3Good

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

@[expose] def SqU (h : UnitaryFieldData p f F) (z : F) : Prop :=
  ∃ n : F, h.bar n * n = 1 ∧ n * n = z

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem SqU.mul {h : UnitaryFieldData p f F} {z z' : F} (hz : SqU h z) (hz' : SqU h z') :
    SqU h (z * z') := by
  obtain ⟨n, hn, rfl⟩ := hz
  obtain ⟨n', hn', rfl⟩ := hz'
  refine ⟨n * n', ?_, by ring⟩
  rw [map_mul]
  calc h.bar n * h.bar n' * (n * n') = (h.bar n * n) * (h.bar n' * n') := by ring
    _ = 1 := by rw [hn, hn', one_mul]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem SqU.inv {h : UnitaryFieldData p f F} {z : F} (hz : SqU h z) : SqU h z⁻¹ := by
  obtain ⟨n, hn, rfl⟩ := hz
  refine ⟨n⁻¹, ?_, by rw [mul_inv]⟩
  rw [map_inv₀, ← mul_inv, hn, inv_one]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem sqU_self {h : UnitaryFieldData p f F} {e : F} (he : h.bar e * e = 1) : SqU h (e * e) :=
  ⟨e, he, rfl⟩

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem two_nonsq {h : UnitaryFieldData p f F} {d0 d1 d2 : F} (h0 : h.bar d0 * d0 = 1)
    (h1 : h.bar d1 * d1 = 1) (h2 : h.bar d2 * d2 = 1)
    (hn : ¬ (SqU h (d0 * d1) ∧ SqU h (d0 * d2) ∧ SqU h (d1 * d2))) :
    (¬ SqU h (d0 * d1) ∧ ¬ SqU h (d1 * d2)) ∨ (¬ SqU h (d0 * d1) ∧ ¬ SqU h (d0 * d2)) ∨
      (¬ SqU h (d0 * d2) ∧ ¬ SqU h (d1 * d2)) := by
  have hP : SqU h (d0 * d1 * (d0 * d2) * (d1 * d2)) := by
    have : d0 * d1 * (d0 * d2) * (d1 * d2) = (d0 * d1 * d2) * (d0 * d1 * d2) := by ring
    rw [this]
    refine sqU_self ?_
    rw [map_mul, map_mul]
    calc h.bar d0 * h.bar d1 * h.bar d2 * (d0 * d1 * d2) =
        (h.bar d0 * d0) * (h.bar d1 * d1) * (h.bar d2 * d2) := by ring
      _ = 1 := by rw [h0, h1, h2]; ring
  have hd0 : d0 ≠ 0 := fun e => by rw [e] at h0; simp at h0
  have hd1 : d1 ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have hd2 : d2 ≠ 0 := fun e => by rw [e] at h2; simp at h2
  have c12 : SqU h (d0 * d1) → SqU h (d0 * d2) → SqU h (d1 * d2) := by
    intro a b
    have := hP.mul (a.mul b).inv
    have e : d0 * d1 * (d0 * d2) * (d1 * d2) * (d0 * d1 * (d0 * d2))⁻¹ = d1 * d2 := by
      field_simp
    rwa [e] at this
  have c13 : SqU h (d0 * d1) → SqU h (d1 * d2) → SqU h (d0 * d2) := by
    intro a b
    have := hP.mul (a.mul b).inv
    have e : d0 * d1 * (d0 * d2) * (d1 * d2) * (d0 * d1 * (d1 * d2))⁻¹ = d0 * d2 := by
      field_simp
    rwa [e] at this
  have c23 : SqU h (d0 * d2) → SqU h (d1 * d2) → SqU h (d0 * d1) := by
    intro a b
    have := hP.mul (a.mul b).inv
    have e : d0 * d1 * (d0 * d2) * (d1 * d2) * (d0 * d2 * (d1 * d2))⁻¹ = d0 * d1 := by
      field_simp
    rwa [e] at this
  by_cases a : SqU h (d0 * d1)
  · by_cases b : SqU h (d0 * d2)
    · exact absurd ⟨a, b, c12 a b⟩ hn
    · by_cases c : SqU h (d1 * d2)
      · exact absurd (c13 a c) b
      · exact Or.inr (Or.inr ⟨b, c⟩)
  · by_cases b : SqU h (d0 * d2)
    · by_cases c : SqU h (d1 * d2)
      · exact absurd (c23 b c) a
      · exact Or.inl ⟨a, c⟩
    · exact Or.inr (Or.inl ⟨a, b⟩)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem not_sqU_neg_sq (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) (hq : p ^ f = 5 ∨ p ^ f = 9)
    {e : F} (he : h.bar e * e = 1) : ¬ SqU h (-(e * e)) := by
  rintro ⟨n, hn, hnn⟩
  have he0 : e ≠ 0 := fun e0 => by rw [e0] at he; simp at he
  have hbe : h.bar e = e⁻¹ := eq_inv_of_mul_eq_one_left he
  have hm : h.bar (n * e⁻¹) * (n * e⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hbe, inv_inv]
    calc h.bar n * e * (n * e⁻¹) = (h.bar n * n) * (e * e⁻¹) := by ring
      _ = 1 := by rw [hn, mul_inv_cancel₀ he0]; ring
  have hmm : (n * e⁻¹) * (n * e⁻¹) = -1 := by
    have : (n * e⁻¹) * (n * e⁻¹) = (n * n) * (e⁻¹ * e⁻¹) := by ring
    rw [this, hnn]
    field_simp
  have hpow : (n * e⁻¹) ^ (p ^ f + 1) = 1 := by
    rw [pow_succ, ← h.bar_apply]
    exact hm
  rcases hq with hq | hq <;> rw [hq] at hpow
  · have e6 : (n * e⁻¹) ^ (5 + 1) = ((n * e⁻¹) * (n * e⁻¹)) ^ 3 := by ring
    rw [e6, hmm] at hpow
    exact h2 (by linear_combination (-1 : F) * hpow)
  · have e10 : (n * e⁻¹) ^ (9 + 1) = ((n * e⁻¹) * (n * e⁻¹)) ^ 5 := by ring
    rw [e10, hmm] at hpow
    exact h2 (by linear_combination (-1 : F) * hpow)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem odd_index {d : Fin 3 → F} {c : F} (hsq : ∀ u, d u * d u = c) (hne : ¬ (d 0 = d 1 ∧ d 1 = d 2)) :
    (d 1 = d 2 ∧ d 0 = -d 1) ∨ (d 0 = d 2 ∧ d 1 = -d 0) ∨ (d 0 = d 1 ∧ d 2 = -d 0) := by
  have s01 := mul_self_eq_mul_self_iff.1 ((hsq 0).trans (hsq 1).symm)
  have s12 := mul_self_eq_mul_self_iff.1 ((hsq 1).trans (hsq 2).symm)
  have s02 := mul_self_eq_mul_self_iff.1 ((hsq 0).trans (hsq 2).symm)
  by_cases a : d 0 = d 1
  · have hb : d 1 ≠ d 2 := fun hb => hne ⟨a, hb⟩
    have h02 : d 0 = -d 2 := s02.resolve_left (fun e => hb (a ▸ e))
    exact Or.inr (Or.inr ⟨a, by linear_combination h02⟩)
  · have h01 : d 0 = -d 1 := s01.resolve_left a
    by_cases b : d 1 = d 2
    · exact Or.inl ⟨b, h01⟩
    · have h12 : d 1 = -d 2 := s12.resolve_left b
      exact Or.inr (Or.inl ⟨by linear_combination h01 - h12, by linear_combination h01⟩)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem eq_one_of_scalar_lift {h : UnitaryFieldData p f F} {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {x : MulAut J} {Δ : GL (Fin 3) F}
    (hl : IsLift θ Δ 1 x) (hD : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hs : (Δ : Matrix (Fin 3) (Fin 3) F) 0 0 = (Δ : Matrix (Fin 3) (Fin 3) F) 1 1 ∧
      (Δ : Matrix (Fin 3) (Fin 3) F) 1 1 = (Δ : Matrix (Fin 3) (Fin 3) F) 2 2) : x = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨g, rfl⟩ := hθ.surj y
  obtain ⟨g', hg'1, hg'2⟩ := hl g
  have hcomm : Δ * (g : GL (Fin 3) F) = (g : GL (Fin 3) F) * Δ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have hdiag : (Δ : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal (fun _ => (Δ : Matrix (Fin 3) (Fin 3) F) 0 0) := by
      rw [← hD.diagonal_diag]
      congr 1
      ext u
      fin_cases u
      · rfl
      · exact hs.1.symm
      · exact (hs.1.trans hs.2).symm
    rw [hdiag]
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have : g' = g := by
    apply Subtype.ext
    rw [hg'1, glAut_one_apply, hcomm]
    group
  rw [← hg'2, this]
  rfl

theorem gammaAct_eq_top_five_nine_std (h : UnitaryFieldData p f F)
    (hp2 : p ≠ 2) (hq : p ^ f = 5 ∨ p ^ f = 9) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {A : Type} [Group A] [Finite A]
    (hA : IsRank23 A) (α : A →* MulAut J) (hα : ∀ a, DiagLift h θ (α a)) : gammaAct α = ⊤ := by
  have h2 : (2 : F) ≠ 0 := GenLocU3Desc.two_ne_zero' h hp2
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  have hPerf : Group.IsPerfect ↥(unitarySU p f F 3) :=
    (CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (le_refl 3)).1
  have hsq : ∀ a : A, a * a = 1 := fun a => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  have h5 : 5 ≤ p ^ f := by omega
  by_cases hk : ∀ a ∈ A0 h θ α hsq, α a = 1
  · exact gammaAct_eq_top_of_le_ker α
      ((GenLocBasic.adm_iff_index hA.1 _).2 (A0_index_le_two h α hsq hα)) (fun a ha => hk a ha)
  · push Not at hk
    obtain ⟨a, ha, hne⟩ := hk
    obtain ⟨Δ, hl, hD⟩ := ha
    obtain ⟨c, hc⟩ := sq_scalar_of_isLift h h2 hPerf hker (by rw [← map_mul, hsq a, map_one]) hl
    set d : Fin 3 → F := fun u => (Δ : Matrix (Fin 3) (Fin 3) F) u u with hd
    have hd2 : ∀ u, d u * d u = c := fun u => diag_sq_eq hD.2 hc u
    have hn : ∀ u, h.bar (d u) * d u = 1 := fun u => hD.entry_norm u
    have hne' : ¬ (d 0 = d 1 ∧ d 1 = d 2) := fun hs =>
      hne (eq_one_of_scalar_lift hθ hl hD.2 hs)
    have key : ∀ σ : Equiv.Perm (Fin 3),
        (∀ i : Fin 2, ¬ SqU h (d (σ (idx3 i 0)) * d (σ (idx3 i 1)))) → gammaAct α = ⊤ :=
      fun σ hB => gammaAct_eq_top_of_nonInner h hp2 h5 hθ h2 hPerf hker hA α hα σ
        (fun i => ⟨a, Δ, 1, hl, Or.inl rfl, hD, hB i⟩)
    have hns : ∀ {e : F}, h.bar e * e = 1 → ¬ SqU h (-(e * e)) := fun he =>
      not_sqU_neg_sq h h2 hq he
    rcases odd_index hd2 hne' with ⟨h12, h0⟩ | ⟨h02, h1⟩ | ⟨h01, h2'⟩
    · refine key (Equiv.swap 0 1) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · show ¬ SqU h (d 1 * d 0)
        rw [h0, show d 1 * -d 1 = -(d 1 * d 1) by ring]
        exact hns (hn 1)
      · show ¬ SqU h (d 0 * d 2)
        rw [h0, ← h12, show -d 1 * d 1 = -(d 1 * d 1) by ring]
        exact hns (hn 1)
    · refine key 1 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · show ¬ SqU h (d 0 * d 1)
        rw [h1, show d 0 * -d 0 = -(d 0 * d 0) by ring]
        exact hns (hn 0)
      · show ¬ SqU h (d 1 * d 2)
        rw [h1, ← h02, show -d 0 * d 0 = -(d 0 * d 0) by ring]
        exact hns (hn 0)
    · refine key (Equiv.swap 1 2) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · show ¬ SqU h (d 0 * d 2)
        rw [h2', show d 0 * -d 0 = -(d 0 * d 0) by ring]
        exact hns (hn 0)
      · show ¬ SqU h (d 2 * d 1)
        rw [h2', ← h01, show -d 0 * d 0 = -(d 0 * d 0) by ring]
        exact hns (hn 0)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem isCover_comp_conj (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1) :
    IsCover h (θ.comp (KFU.conjSU h ⟨C, mem_pfu_of_unitary h hCu⟩).toMonoidHom) := by
  have hC := mem_pfu_of_unitary h hCu
  refine ⟨hθ.surj.comp (KFU.conjSU h ⟨C, hC⟩).surjective, ?_⟩
  ext g
  have hmem : g ∈ (θ.comp (KFU.conjSU h ⟨C, hC⟩).toMonoidHom).ker ↔
      KFU.conjSU h ⟨C, hC⟩ g ∈ θ.ker := Iff.rfl
  rw [hmem, hθ.ker, mem_unitaryScalars, mem_unitaryScalars]
  have hcomm : ∀ c : Fˣ, C * GeneralLinearGroup.scalar (Fin 3) c =
      GeneralLinearGroup.scalar (Fin 3) c * C := fun c => (commute_scalar c C).eq
  constructor
  · rintro ⟨c, h1, h2, h3⟩
    refine ⟨c, h1, h2, ?_⟩
    have h4 : C * (g : GL (Fin 3) F) * C⁻¹ = GeneralLinearGroup.scalar (Fin 3) c := h3
    calc (g : GL (Fin 3) F) = C⁻¹ * (C * (g : GL (Fin 3) F) * C⁻¹) * C := by group
      _ = GeneralLinearGroup.scalar (Fin 3) c := by
        rw [h4, mul_assoc, ← hcomm c]; group
  · rintro ⟨c, h1, h2, h3⟩
    refine ⟨c, h1, h2, ?_⟩
    change C * (g : GL (Fin 3) F) * C⁻¹ = GeneralLinearGroup.scalar (Fin 3) c
    rw [h3, hcomm c]; group

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem diagLift_of_frameForm (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    {x : MulAut J} (hx : FrameForm h θ C x) :
    DiagLift h (θ.comp (KFU.conjSU h ⟨C, mem_pfu_of_unitary h hCu⟩).toMonoidHom) x := by
  have hC := mem_pfu_of_unitary h hCu
  obtain ⟨A', Δ, ψ, hl, hψ, hA'u, hΔd, hAC⟩ := hx
  have hΔeq : Δ = C⁻¹ * (A' * glAut ψ C) := by rw [hAC]; group
  have hΔu : ((Δ : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (Δ : Matrix (Fin 3) (Fin 3) F) = 1 := by
    refine (mem_unitaryIsom3 (h := h)).1 ?_
    rw [hΔeq]
    exact mul_mem (inv_mem ((mem_unitaryIsom3 (h := h)).2 hCu))
      (mul_mem ((mem_unitaryIsom3 (h := h)).2 hA'u)
        (glAut_mem_unitaryIsom3 ψ ((mem_unitaryIsom3 (h := h)).2 hCu)))
  refine ⟨Δ, ψ, ?_, hψ, hΔu, hΔd⟩
  intro g
  obtain ⟨g1, hg1, hg2⟩ := hl (KFU.conjSU h ⟨C, hC⟩ g)
  refine ⟨(KFU.conjSU h ⟨C, hC⟩).symm g1, ?_, ?_⟩
  · change C⁻¹ * (g1 : GL (Fin 3) F) * C = Δ * glAut ψ (g : GL (Fin 3) F) * Δ⁻¹
    rw [hg1, hΔeq]
    change C⁻¹ * (A' * glAut ψ (C * (g : GL (Fin 3) F) * C⁻¹) * A'⁻¹) * C = _
    simp only [map_mul, map_inv]
    group
  · change θ (KFU.conjSU h ⟨C, hC⟩ ((KFU.conjSU h ⟨C, hC⟩).symm g1)) =
      x (θ (KFU.conjSU h ⟨C, hC⟩ g))
    rw [MulEquiv.apply_symm_apply, hg2]

theorem gammaAct_eq_top_of_std {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 ≤ p ^ f) (hJ : LieModel J .PSU 3 p f) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut J) (hA : IsRank23 A)
    (std : ∀ (F : Type) [Field F] [Finite F] [CharP F p] [Fact p.Prime] (h : UnitaryFieldData p f F)
      (θ : ↥(unitarySU p f F 3) →* J), IsCover h θ → (∀ a, DiagLift h θ (α a)) → gammaAct α = ⊤) :
    gammaAct α = ⊤ := by
  classical
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := GenLocU3.stated_PSU hJ
  have hf : 1 ≤ f := hadm.2.1
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := hud.charP
  have : Finite F := hud.finite
  let ψ : J ≃* unitaryPSU hud 3 := e₀.trans (unitaryPSUEquiv hud (by norm_num)).symm
  let θ : ↥(unitarySU p f F 3) →* J := ψ.symm.toMonoidHom.comp (unitaryProj hud 3)
  have hθs : Function.Surjective θ := ψ.symm.surjective.comp (unitaryProj_surjective hud 3)
  have hθ1 : ∀ g : ↥(unitarySU p f F 3), θ g = 1 ↔ g ∈ unitaryScalars hud 3 := by
    intro g
    change ψ.symm (unitaryProj hud 3 g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]
  have hθ : IsCover hud θ := ⟨hθs, by ext g; exact hθ1 g⟩
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center hud 3
  obtain ⟨hPerf, hcen⟩ := CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' hud hp2 (le_refl 3)
  have hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g => hz g
    rw [← map_center_eq_center_of_perfect hθs hker, hcen] at hzc
    obtain ⟨w, hw, rfl⟩ := hzc
    have : w ∈ θ.ker := by rw [hθ.ker]; exact hw
    exact this
  have hinj : Function.Injective (MulAut.conj : J →* MulAut J) :=
    GenLocBasic.conj_injective_of_center_trivial hZ
  have hD : CFSG.IsElementaryAbelian 2 ↥α.range :=
    GenLocBasic.isEA_of_surjective hA.1 α.rangeRestrict α.rangeRestrict_surjective
  have hframe : ∃ C : GL (Fin 3) F,
      ((C : Matrix (Fin 3) (Fin 3) F).map hud.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1 ∧
        ∀ a, FrameForm hud θ C (α a) := by
    by_cases hout : ∃ a : A, ∀ y : J, MulAut.conj y ≠ α a
    · obtain ⟨a0, ha0⟩ := hout
      obtain ⟨C, hCu, hC⟩ := exists_frame hud hp2 h3 hθ hinj hD (u := α a0) ⟨a0, rfl⟩ ha0
      exact ⟨C, hCu, fun a => hC (α a) ⟨a, rfl⟩⟩
    · push Not at hout
      obtain ⟨C, hCu, hC⟩ := exists_frame_inner hud hp2 hθ hinj hD (fun x hx => by
        obtain ⟨a, rfl⟩ := hx
        exact hout a)
      exact ⟨C, hCu, fun a => hC (α a) ⟨a, rfl⟩⟩
  obtain ⟨C, hCu, hC⟩ := hframe
  exact std F hud _ (isCover_comp_conj hud hθ hCu) fun a => diagLift_of_frameForm hud hCu (hC a)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem ne_two_of_pow {p f : ℕ} (hf : 1 ≤ f) (hq : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) : p ≠ 2 := by
  intro hp2
  have h2f : 2 ∣ p ^ f := by
    rw [hp2]
    exact dvd_pow_self 2 (by omega)
  rcases hq with h | h | h <;> rw [h] at h2f <;> omega

theorem genProp_psu3_five_nine {J : Type} [Group J] {p f : ℕ}
    (hq : p ^ f = 5 ∨ p ^ f = 9) (hJ : LieModel J .PSU 3 p f) : GenProp J := by
  intro A _ _ α hA
  obtain ⟨hadm, -⟩ := GenLocU3.stated_PSU hJ
  have hq' : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 := by
    rcases hq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hp2 : p ≠ 2 := ne_two_of_pow hadm.2.1 hq'
  have h3 : 3 ≤ p ^ f := by
    rcases hq with h | h <;> rw [h] <;> norm_num
  exact gammaAct_eq_top_of_std hadm.1 hp2 h3 hJ α hA fun F _ _ _ _ h θ hθ hα =>
    gammaAct_eq_top_five_nine_std h hp2 hq hθ hA α hα

@[expose] def Exc7 (h : UnitaryFieldData p f F) {J : Type} [Group J] (θ : ↥(unitarySU p f F 3) →* J)
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1) : Prop :=
  (∃ a ∈ A0 h θ α hsq, α a ≠ 1) ∧
    ∃ a ∉ A0 h θ α hsq, ∃ (Δ : GL (Fin 3) F) (ψ : F ≃+* F), IsLift θ Δ ψ (α a) ∧
      (∀ c, ψ c = h.bar c) ∧ DU h Δ ∧
      SqU h ((Δ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ : Matrix (Fin 3) (Fin 3) F) 1 1) ∧
      SqU h ((Δ : Matrix (Fin 3) (Fin 3) F) 0 0 * (Δ : Matrix (Fin 3) (Fin 3) F) 2 2) ∧
      SqU h ((Δ : Matrix (Fin 3) (Fin 3) F) 1 1 * (Δ : Matrix (Fin 3) (Fin 3) F) 2 2)

theorem gammaAct_eq_top_seven_std (h : UnitaryFieldData p f F)
    (hp2 : p ≠ 2) (hq : p ^ f = 7) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) {A : Type} [Group A] [Finite A] (hA : IsRank23 A) (α : A →* MulAut J)
    (hα : ∀ a, DiagLift h θ (α a))
    (hexc : ∀ hsq : (∀ a : A, a * a = 1), Exc7 h θ α hsq → gammaAct α = ⊤) : gammaAct α = ⊤ := by
  have h2 : (2 : F) ≠ 0 := GenLocU3Desc.two_ne_zero' h hp2
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  have hPerf : Group.IsPerfect ↥(unitarySU p f F 3) :=
    (CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (le_refl 3)).1
  have hsq : ∀ a : A, a * a = 1 := fun a => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  have h5 : 5 ≤ p ^ f := by rw [hq]; norm_num
  have hq2 : p ^ f ≠ 2 := by rw [hq]; norm_num
  by_cases hall : ∀ a, a ∈ A0 h θ α hsq
  · exact gammaAct_eq_top_of_A0_top h hq2 hθ h2 hPerf hker hA α hα hsq hall
  push Not at hall
  obtain ⟨a2, ha2⟩ := hall
  obtain ⟨Δ, ψ, hl, hψ, hΔu, hΔd⟩ := hα a2
  have hψ' : ∀ c, ψ c = h.bar c := by
    rcases hψ with rfl | hb
    · exact absurd ⟨Δ, hl, hΔu, hΔd⟩ ha2
    · exact hb
  have hD : DU h Δ := ⟨hΔu, hΔd⟩
  set d : Fin 3 → F := fun u => (Δ : Matrix (Fin 3) (Fin 3) F) u u with hd
  have hn : ∀ u, h.bar (d u) * d u = 1 := fun u => hD.entry_norm u
  have key : ∀ σ : Equiv.Perm (Fin 3),
      (∀ i : Fin 2, ¬ SqU h (d (σ (idx3 i 0)) * d (σ (idx3 i 1)))) → gammaAct α = ⊤ :=
    fun σ hB => gammaAct_eq_top_of_nonInner h hp2 h5 hθ h2 hPerf hker hA α hα σ
      (fun i => ⟨a2, Δ, ψ, hl, Or.inr hψ', hD, hB i⟩)
  by_cases hsqall : SqU h (d 0 * d 1) ∧ SqU h (d 0 * d 2) ∧ SqU h (d 1 * d 2)
  · by_cases hk : ∀ a ∈ A0 h θ α hsq, α a = 1
    · exact gammaAct_eq_top_of_le_ker α
        ((GenLocBasic.adm_iff_index hA.1 _).2 (A0_index_le_two h α hsq hα)) (fun a ha => hk a ha)
    · push Not at hk
      exact hexc hsq ⟨hk, a2, ha2, Δ, ψ, hl, hψ', hD, hsqall⟩
  · rcases two_nonsq (hn 0) (hn 1) (hn 2) hsqall with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · refine key 1 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · exact a
      · exact b
    · refine key (Equiv.swap 0 1) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · show ¬ SqU h (d 1 * d 0)
        rwa [mul_comm]
      · exact b
    · refine key (Equiv.swap 1 2) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · exact a
      · show ¬ SqU h (d 2 * d 1)
        rwa [mul_comm]

@[expose] def Exc7Hyp (J : Type) [Group J] (p f : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F p] [Fact p.Prime] (h : UnitaryFieldData p f F)
    (θ : ↥(unitarySU p f F 3) →* J), IsCover h θ → ∀ (A : Type) [Group A] [Finite A], IsRank23 A →
      ∀ (α : A →* MulAut J), (∀ a, DiagLift h θ (α a)) → ∀ hsq : (∀ a : A, a * a = 1),
        Exc7 h θ α hsq → gammaAct α = ⊤

theorem genProp_psu3_seven_of_exc {J : Type} [Group J] {p f : ℕ}
    (hq : p ^ f = 7) (hJ : LieModel J .PSU 3 p f) (hexc : Exc7Hyp J p f) : GenProp J := by
  intro A _ _ α hA
  obtain ⟨hadm, -⟩ := GenLocU3.stated_PSU hJ
  have hp2 : p ≠ 2 := ne_two_of_pow hadm.2.1 (Or.inr (Or.inl hq))
  have h3 : 3 ≤ p ^ f := by rw [hq]; norm_num
  exact gammaAct_eq_top_of_std hadm.1 hp2 h3 hJ α hA fun F _ _ _ _ h θ hθ hα =>
    gammaAct_eq_top_seven_std h hp2 hq hθ hA α hα fun hsq he => hexc F h θ hθ A hA α hα hsq he

end GenLocU3Small

end CFSG.GH74.Generic.BProg.B2
