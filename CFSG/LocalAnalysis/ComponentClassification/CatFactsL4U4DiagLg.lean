module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLf

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

variable {F : Type} [Field F] [Fintype F]

theorem two_ne_zero_of_card_odd (hq : Odd (Fintype.card F)) : (2 : F) ≠ 0 := by
  intro h0
  have hc : ringChar F = 2 := by
    have := (ringChar.spec F 2).1 (by exact_mod_cast h0)
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 this
  have := FiniteField.even_card_iff_char_two.1 hc
  rw [Nat.odd_iff] at hq
  omega

omit [Fintype F] in
theorem mem_scalars_of_toGL_mem_center {Y : SpecialLinearGroup (Fin 4) F}
    (h : SpecialLinearGroup.toGL Y ∈ Subgroup.center (GL (Fin 4) F)) : Y ∈ scalars 4 F := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨c, hc⟩ := h
  have hY : (Y : Matrix (Fin 4) (Fin 4) F) = Matrix.scalar (Fin 4) (c : F) := by
    have := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar] at this
    exact this.symm
  refine mem_scalars.2 ⟨c, Units.ext ?_, hY⟩
  have hdet : (Y : Matrix (Fin 4) (Fin 4) F).det = 1 := Y.2
  rw [hY, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  rw [Units.val_pow_eq_pow_val, hdet, Units.val_one]

omit [Fintype F] in
theorem toGL_mem_center_of_mem_scalars {Y : SpecialLinearGroup (Fin 4) F}
    (h : Y ∈ scalars 4 F) : SpecialLinearGroup.toGL Y ∈ Subgroup.center (GL (Fin 4) F) := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, Units.ext (by rw [GeneralLinearGroup.coe_scalar, ← hc]; rfl)⟩

theorem exists_nonsquare_of_conjAut (hq : Odd (Fintype.card F)) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsq : s ∣ Fintype.card F ^ 2 + 1) (A : GL (Fin 4) F)
    (hA1 : conjAut 4 F A ≠ 1) (hA2 : conjAut 4 F A ^ 2 = 1) {y : projectiveSL 4 F}
    (hy : orderOf y = s) (hAy : conjAut 4 F A y = y) :
    ∃ l : Fˣ, A ^ 2 = GeneralLinearGroup.scalar (Fin 4) l ∧ ¬ IsSquare (l : F) := by
  obtain ⟨Y, rfl⟩ := proj_surjective 4 F y
  have hker : ∀ B : GL (Fin 4) F, B ∈ Subgroup.center (GL (Fin 4) F) → conjAut 4 F B = 1 := by
    intro B hB
    rw [GeneralLinearGroup.center_eq_range_scalar] at hB
    obtain ⟨c, rfl⟩ := hB
    exact (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).2 ⟨c, rfl⟩
  refine not_isSquare_of_comm_odd_order (n := 4) (e := 1) (by norm_num) hq hs hs2
    (by simpa using hsq) (by norm_num) A ?_ ?_ (SpecialLinearGroup.toGL Y) ?_ ?_ ?_
  · intro h
    exact hA1 (hker A (ProjGenLinGroup.mk_eq_one.1 h))
  · rw [← map_pow, ProjGenLinGroup.mk_eq_one]
    rw [← map_pow] at hA2
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).1 hA2
    rw [← hc, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  · intro h
    have h1 := mem_scalars_of_toGL_mem_center (ProjGenLinGroup.mk_eq_one.1 h)
    rw [← proj_eq_one_iff] at h1
    rw [h1, orderOf_one] at hy
    exact hs.one_lt.ne' hy.symm
  · rw [← map_pow, ← map_pow, ProjGenLinGroup.mk_eq_one]
    apply toGL_mem_center_of_mem_scalars
    rw [← proj_eq_one_iff, map_pow, ← hy, pow_orderOf_eq_one]
  · have h1 := mem_center_of_conjAut_fix A hAy
    rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

omit [Fintype F] in
theorem exists_conj_eq_kG {l : Fˣ} (hns : ¬ IsSquare (l : F)) {A : GL (Fin 4) F}
    (hA : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) l) :
    ∃ P : GL (Fin 4) F, P⁻¹ * A * P = kG (Units.ne_zero l) := by
  have hX : (A : Matrix (Fin 4) (Fin 4) F) * A = (l : F) • 1 := by
    have := congrArg Units.val hA
    rw [Units.val_pow_eq_pow_val, sq, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
    rw [this, Matrix.smul_one_eq_diagonal]
  obtain ⟨P, hP, hAP⟩ := exists_mul_eq_mul_kZero hns hX
  set P' : GL (Fin 4) F := GeneralLinearGroup.mkOfDetNeZero P hP.ne_zero with hP'
  refine ⟨P', Units.ext ?_⟩
  have hc : (P' : Matrix (Fin 4) (Fin 4) F) = P := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hinv : ((P'⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * P' = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hc] at hinv
  rw [Units.val_mul, Units.val_mul, hc, coe_kG, Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, hinv,
    Matrix.one_mul]

@[expose] noncomputable def actP {H : Type} [Group H] {L : Subgroup H} [L.Normal]
    (e : ↥L ≃* projectiveSL 4 F) : H →* MulAut (projectiveSL 4 F) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

omit [Fintype F] in
theorem actP_apply {H : Type} [Group H] {L : Subgroup H} [L.Normal]
    (e : ↥L ≃* projectiveSL 4 F) (h : H) (x : ↥L) :
    actP e h (e x) = e (MulAut.conjNormal h x) := by
  change e (MulAut.conjNormal h (e.symm (e x))) = _
  rw [MulEquiv.symm_apply_apply]

omit [Fintype F] in
theorem eq_one_of_actP_eq_one {H : Type} [Group H] {L : Subgroup H} [L.Normal]
    (hC : Subgroup.centralizer (L : Set H) = ⊥) (e : ↥L ≃* projectiveSL 4 F) {h : H}
    (hh : actP e h = 1) : h = 1 := by
  have hmem : h ∈ Subgroup.centralizer (L : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut (projectiveSL 4 F) => φ (e ⟨x, hx⟩)) hh
    simp only [actP_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    rw [MulAut.conjNormal_apply] at h2
    calc x * h = h * x * h⁻¹ * h := by rw [h2]
      _ = h * x := by group
  rw [hC, Subgroup.mem_bot] at hmem
  exact hmem

omit [Fintype F] in
theorem actP_trans {H : Type} [Group H] {L : Subgroup H} [L.Normal]
    (e : ↥L ≃* projectiveSL 4 F) (c : MulAut (projectiveSL 4 F)) (h : H) :
    actP (e.trans c) h = c * actP e h * c⁻¹ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (e.trans c).surjective x
  rw [actP_apply, MulAut.mul_apply, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulAut.inv_apply, MulEquiv.symm_apply_apply, actP_apply]

open Subgroup in
theorem diag_L4 {H : Type} [Group H] {L : Subgroup H} [L.Normal]
    (hC : centralizer (L : Set H) = ⊥) (hF : Fintype.card F % 4 = 1)
    (e : ↥L ≃* projectiveSL 4 F) {α β ξ : H} (hαα : α * α = 1) (hα1 : α ≠ 1)
    (hαc : α = ⁅β, ξ⁆) {J₁ : Subgroup H} (hJL : J₁ ≤ L) (hJα : J₁ ≤ centralizer {α})
    (hJp : ⁅J₁, J₁⁆ = J₁)
    (hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J₁) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ Nat.card F ^ 2 + 1) {y : H} (hyJ : y ∈ J₁)
    (hy : orderOf y = s) :
    2 * Nat.card J₁ ≤ Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ∧
      (β ∈ centralizer (J₁ : Set H) → ξ ∈ centralizer (J₁ : Set H) → False) := by
  classical
  have hcF : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hq : Odd (Fintype.card F) := by rw [Nat.odd_iff]; omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_odd hq
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hneg : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.2 (by omega)
  obtain ⟨A, hA⟩ : actP e α ∈ (conjAut 4 F).range := by
    rw [hαc, map_commutatorElement]
    exact commutator_mem_range_conjAut _ _
  have hA1 : conjAut 4 F A ≠ 1 := fun h => hα1 (eq_one_of_actP_eq_one hC e (hA ▸ h))
  have hA2 : conjAut 4 F A ^ 2 = 1 := by rw [hA, ← map_pow, sq, hαα, map_one]
  have hyL : y ∈ L := hJL hyJ
  have hyα : α * y * α⁻¹ = y := by
    have := mem_centralizer_singleton_iff.mp (hJα hyJ)
    rw [← this]; group
  have hAy : conjAut 4 F A (e ⟨y, hyL⟩) = e ⟨y, hyL⟩ := by
    rw [hA, actP_apply]
    congr 1
    exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hyα)
  have hys : orderOf (e ⟨y, hyL⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
  obtain ⟨l, hl2, hns⟩ := exists_nonsquare_of_conjAut hq hs hs2 (by rw [← hcF]; exact hsq) A
    hA1 hA2 hys hAy
  obtain ⟨P, hP⟩ := exists_conj_eq_kG hns hl2
  set hl := Units.ne_zero l
  set e' : ↥L ≃* projectiveSL 4 F := e.trans (conjAut 4 F P⁻¹) with he'
  have hα' : actP e' α = conjAut 4 F (kG hl) := by
    rw [he', actP_trans, ← hA, ← map_inv, ← map_mul, ← map_mul, inv_inv, hP]
  set X : Subgroup ↥L := J₁.subgroupOf L with hX
  have hXp : ⁅X, X⁆ = X := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hX, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJL, hJp]
  set J' : Subgroup (projectiveSL 4 F) := X.map e'.toMonoidHom with hJ'
  have hJ'p : ⁅J', J'⁆ = J' := by rw [hJ', ← Subgroup.map_commutator, hXp]
  have hfix : ∀ g : H, (∀ j ∈ J₁, g * j * g⁻¹ = j) → ∀ x ∈ J', actP e' g x = x := by
    rintro g hg _ ⟨z, hz, rfl⟩
    change actP e' g (e' z) = e' z
    rw [actP_apply]
    congr 1
    exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hg _ (mem_subgroupOf.1 hz))
  have hJ'k : ∀ x ∈ J', conjAut 4 F (kG hl) x = x := by
    rw [← hα']
    refine hfix α fun j hj => ?_
    have := mem_centralizer_singleton_iff.mp (hJα hj)
    rw [← this]; group
  have hcJ : Nat.card J' = Nat.card J₁ := by
    rw [hJ', Subgroup.card_map_of_injective e'.injective, hX,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv]
  have hJK : J' = JK F hl := eq_JK h2 hl (by simpa using hns) hJ'k hJ'p (by rw [hcJ]; exact hcard)
  refine ⟨?_, fun hβ hξ => ?_⟩
  · rw [← hcJ, hJK]
    exact two_mul_card_JK_le h2 hl (by simpa using hns)
  · have hmem : ∀ g ∈ centralizer (J₁ : Set H), actP e' g ∈ CA F hl := by
      intro g hg x hx
      rw [← hJK] at hx
      refine hfix g (fun j hj => ?_) x hx
      have := mem_centralizer_iff.mp hg j hj
      rw [← this]; group
    apply conjAut_kG_not_mem_commutator h4 hneg hl (by simpa using hns)
    rw [← hα', hαc, map_commutatorElement]
    exact commutator_mem_commutator (hmem β hβ) (hmem ξ hξ)

end DiagL

end CFSG.ComponentClassification.CatFactsL4U4
