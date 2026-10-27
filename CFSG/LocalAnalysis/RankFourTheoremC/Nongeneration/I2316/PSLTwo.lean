module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

open Matrix Matrix.SpecialLinearGroup MulAction
open scoped MatrixGroups LinearAlgebra.Projectivization

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

variable {F : Type*} [Field F]

@[expose] noncomputable def coordPt0 : ℙ F (Fin 2 → F) :=
  Projectivization.mk F (Pi.single 0 1) (Pi.single_ne_zero_iff.2 one_ne_zero)

@[expose] noncomputable def coordPt1 : ℙ F (Fin 2 → F) :=
  Projectivization.mk F (Pi.single 1 1) (Pi.single_ne_zero_iff.2 one_ne_zero)

theorem coordPt0_ne_coordPt1 : (coordPt0 : ℙ F (Fin 2 → F)) ≠ coordPt1 := by
  intro h
  rw [coordPt0, coordPt1, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp at h0 h1

theorem submodule_coordPt0 :
    (coordPt0 : ℙ F (Fin 2 → F)).submodule = Submodule.span F {(Pi.single 0 1 : Fin 2 → F)} := by
  rw [coordPt0, Projectivization.submodule_mk]

theorem submodule_coordPt1 :
    (coordPt1 : ℙ F (Fin 2 → F)).submodule = Submodule.span F {(Pi.single 1 1 : Fin 2 → F)} := by
  rw [coordPt1, Projectivization.submodule_mk]

theorem lineStab_sup_lineStab_eq_top {P Q : ℙ F (Fin 2 → F)} (hPQ : P ≠ Q) :
    lineStab P.submodule ⊔ lineStab Q.submodule = (⊤ : Subgroup SL(2, F)) := by
  obtain ⟨g, hg0, hg1⟩ := (is_two_pretransitive_iff (G := SL(2, F))
    (α := ℙ F (Fin 2 → F))).1 inferInstance (coordPt0_ne_coordPt1 (F := F)) hPQ
  have hP : lineStab P.submodule = (lineStab (coordPt0 : ℙ F (Fin 2 → F)).submodule).map
      (MulAut.conj g).toMonoidHom := by
    rw [← hg0, PSL.smul_submodule, lineStab_smul, Subgroup.pointwise_smul_def]
    rfl
  have hQ : lineStab Q.submodule = (lineStab (coordPt1 : ℙ F (Fin 2 → F)).submodule).map
      (MulAut.conj g).toMonoidHom := by
    rw [← hg1, PSL.smul_submodule, lineStab_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hP, hQ, ← Subgroup.map_sup, submodule_coordPt0, submodule_coordPt1,
    SL2Gen.SL_card_two_lineStab_sup_eq_top]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

theorem iwasawaT_sup_iwasawaT_eq_top {P Q : ℙ F (Fin 2 → F)} (hPQ : P ≠ Q) :
    PSL.iwasawaT P ⊔ PSL.iwasawaT Q = (⊤ : Subgroup PSL(2, F)) := by
  unfold PSL.iwasawaT
  rw [← Subgroup.map_sup, lineStab_sup_lineStab_eq_top hPQ]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem pow_eq_self_of_sq_eq_one {r : F} (hr : r ^ 2 = 1) {p : ℕ} (hp : p ≠ 2) [Fact p.Prime] :
    r ^ p = r := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, hr, one_pow, one_mul]

section Unipotent

variable {p : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_mem_iwasawaT_of_pow_eq_one (hp2 : p ≠ 2) {u : PSL(2, F)} (hu1 : u ≠ 1)
    (hup : u ^ p = 1) : ∃ P : ℙ F (Fin 2 → F), u ∈ PSL.iwasawaT P := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective u
  have hcen : A ^ p ∈ Subgroup.center SL(2, F) := by
    rw [← QuotientGroup.mk_pow] at hup
    exact (QuotientGroup.eq_one_iff _).1 hup
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  rw [Fintype.card_fin] at hr2
  have hrp : r ^ p = r := pow_eq_self_of_sq_eq_one hr2 hp2
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr2
  set M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hM
  set N : Matrix (Fin 2) (Fin 2) F := M - Matrix.scalar (Fin 2) r with hN
  have hMp : M ^ p = Matrix.scalar (Fin 2) r := by
    rw [hM, ← Matrix.SpecialLinearGroup.coe_pow]
    exact hrA.symm
  have hNp : N ^ p = 0 := by
    rw [hN, sub_pow_char_of_commute (p := p)
      ((Matrix.scalar_commute r (fun r' => Commute.all r r') M).symm), hMp, ← map_pow, hrp]
    simp
  have hdetN : N.det = 0 := by
    have h1 : N.det ^ p = 0 := by rw [← Matrix.det_pow, hNp, Matrix.det_zero]
    exact (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 h1
  have hdetM : M.det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have hMN : M = N + Matrix.scalar (Fin 2) r := by rw [hN]; abel
  have e00 : M 0 0 = N 0 0 + r := by rw [hMN]; simp
  have e11 : M 1 1 = N 1 1 + r := by rw [hMN]; simp
  have e01 : M 0 1 = N 0 1 := by rw [hMN]; simp
  have e10 : M 1 0 = N 1 0 := by rw [hMN]; simp
  have hdetN' := hdetN
  rw [Matrix.det_fin_two] at hdetN'
  have htr : N 0 0 + N 1 1 = 0 := by
    have h1 := hdetM
    rw [Matrix.det_fin_two, e00, e11, e01, e10] at h1
    have h2 : r * (N 0 0 + N 1 1) = 0 := by linear_combination h1 - hdetN' - hr2
    exact (mul_eq_zero.1 h2).resolve_left hr0
  have hN2 : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-1) * hdetN' + (N 0 0) * htr
    · linear_combination (N 0 1) * htr
    · linear_combination (N 1 0) * htr
    · linear_combination (-1) * hdetN' + (N 1 1) * htr
  have hN0 : N ≠ 0 := by
    intro h0
    apply hu1
    have hMr : M = Matrix.scalar (Fin 2) r := by rw [hMN, h0, zero_add]
    have hAc : A ∈ Subgroup.center SL(2, F) :=
      Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨r, by rwa [Fintype.card_fin], hMr.symm⟩
    exact (QuotientGroup.eq_one_iff A).2 hAc
  set f : (Fin 2 → F) →ₗ[F] (Fin 2 → F) := Matrix.toLin' N with hf
  have hf2 : f ∘ₗ f = 0 := by
    rw [hf, ← Matrix.toLin'_mul, hN2, map_zero]
  have hf0 : f ≠ 0 := fun h => hN0 ((map_eq_zero_iff _ (Matrix.toLin').injective).1 h)
  have hrk : LinearMap.range f ≤ LinearMap.ker f := LinearMap.range_le_ker_iff.2 hf2
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  have hmono := Submodule.finrank_mono hrk
  have hdim : Module.finrank F (Fin 2 → F) = 2 := by simp
  have hbot : LinearMap.range f ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  obtain ⟨v, hvr, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hspan : Submodule.span F {v} = LinearMap.range f := by
    apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v _).2 hvr)
    rw [finrank_span_singleton hv0]
    have h1 : 1 ≤ Module.finrank F (LinearMap.range f) := by
      have := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem v _).2 hvr)
      rwa [finrank_span_singleton hv0] at this
    omega
  refine ⟨Projectivization.mk F v hv0, ?_⟩
  have hB : A * A ^ p ∈ lineStab (Projectivization.mk F v hv0).submodule := by
    rw [Projectivization.submodule_mk, mem_lineStab_iff]
    intro w
    have h1 : (A * A ^ p) • w = r • (M *ᵥ w) := by
      rw [mul_smul, Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def,
        ← hrA]
      simp [Matrix.mulVec_smul, hM]
    have h2 : r • (N *ᵥ w) = (A * A ^ p) • w - w := by
      rw [h1, hN, Matrix.sub_mulVec, smul_sub]
      simp [smul_smul, ← sq, hr2]
    rw [← h2, hspan]
    exact Submodule.smul_mem _ _ ⟨w, rfl⟩
  refine ⟨A * A ^ p, hB, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
  have : (QuotientGroup.mk (A ^ p) : PSL(2, F)) = 1 := (QuotientGroup.eq_one_iff _).2 hcen
  rw [this, mul_one]

end Unipotent

section Transvections

@[expose] noncomputable def tUpper (F : Type*) [Field F] : SL(2, F) :=
  SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1

@[expose] noncomputable def tLower (F : Type*) [Field F] : SL(2, F) :=
  SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1

@[expose] noncomputable def sUpper (F : Type*) [Field F] : PSL(2, F) := QuotientGroup.mk (tUpper F)

@[expose] noncomputable def sLower (F : Type*) [Field F] : PSL(2, F) := QuotientGroup.mk (tLower F)

theorem tUpper_smul (v : Fin 2 → F) : tUpper F • v = ![v 0 + v 1, v 1] := by
  ext i
  fin_cases i <;> simp [tUpper, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    Pi.single_apply]

theorem tLower_smul (v : Fin 2 → F) : tLower F • v = ![v 0, v 0 + v 1] := by
  ext i
  fin_cases i <;> simp [tLower, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    Pi.single_apply, add_comm]

theorem not_fixed_sUpper_and_sLower (P : ℙ F (Fin 2 → F)) :
    ¬ (sUpper F • P = P ∧ sLower F • P = P) := by
  induction P using Projectivization.ind with | _ v hv => ?_
  rintro ⟨h1, h2⟩
  rw [sUpper, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff] at h1
  rw [sLower, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff] at h2
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  rw [tUpper_smul] at hc
  rw [tLower_smul] at hd
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  have d0 := congrFun hd 0
  have d1 := congrFun hd 1
  simp [Units.smul_def, smul_eq_mul] at c0 c1 d0 d1
  have hv1 : v 1 = 0 := by
    by_contra h1
    have hc1 : (c : F) = 1 := by
      have : ((c : F) - 1) * v 1 = 0 := by linear_combination c1
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h1)
    rw [hc1] at c0
    exact h1 (by linear_combination (-1 : F) * c0)
  have hv0 : v 0 = 0 := by
    by_contra h0
    have hd1 : (d : F) = 1 := by
      have : ((d : F) - 1) * v 0 = 0 := by linear_combination d0
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
    rw [hd1] at d1
    exact h0 (by linear_combination (-1 : F) * d1)
  exact hv (by ext i; fin_cases i <;> simp [hv0, hv1])

end Transvections

section KeyLemma

theorem iwasawaT_comm {P : ℙ F (Fin 2 → F)} {a b : PSL(2, F)} (ha : a ∈ PSL.iwasawaT P)
    (hb : b ∈ PSL.iwasawaT P) : a * b = b * a := by
  have h := (PSL2.Iwasawa (F := F)).is_comm P
  exact congrArg Subtype.val (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem iwasawaT_smul_le {Y : Subgroup PSL(2, F)} {P : ℙ F (Fin 2 → F)} {s : PSL(2, F)}
    (hs : s ∈ Y) (hT : PSL.iwasawaT P ≤ Y) : PSL.iwasawaT (s • P) ≤ Y := by
  intro x hx
  have h := (PSL2.Iwasawa (F := F)).is_conj s P
  change x ∈ (PSL2.Iwasawa (F := F)).T (s • P) at hx
  rw [h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  have hx' := hT hx
  have : x = s * ((MulAut.conj s)⁻¹ • x) * s⁻¹ := by
    simp [MulAut.smul_def, MulAut.conj_inv_apply, mul_assoc]
  rw [this]
  exact Y.mul_mem (Y.mul_mem hs hx') (Y.inv_mem hs)

variable {p : ℕ} [Fact p.Prime] [CharP F p]

theorem eq_top_of_centralizer_le (hp2 : p ≠ 2) {u : PSL(2, F)} (hu1 : u ≠ 1) (hup : u ^ p = 1)
    {Y : Subgroup PSL(2, F)} (hY : Subgroup.centralizer ({u} : Set PSL(2, F)) ≤ Y)
    (hs₁ : sUpper F ∈ Y) (hs₂ : sLower F ∈ Y) : Y = ⊤ := by
  obtain ⟨P, hP⟩ := exists_mem_iwasawaT_of_pow_eq_one hp2 hu1 hup
  have hTP : PSL.iwasawaT P ≤ Y := by
    intro t ht
    apply hY
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact iwasawaT_comm hP ht
  have key : ∃ s ∈ Y, s • P ≠ P := by
    by_cases h : sUpper F • P = P
    · exact ⟨sLower F, hs₂, fun h2 => not_fixed_sUpper_and_sLower P ⟨h, h2⟩⟩
    · exact ⟨sUpper F, hs₁, h⟩
  obtain ⟨s, hsY, hsP⟩ := key
  have hT2 := iwasawaT_smul_le hsY hTP
  rw [eq_top_iff, ← iwasawaT_sup_iwasawaT_eq_top (Ne.symm hsP)]
  exact sup_le hTP hT2

end KeyLemma

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
