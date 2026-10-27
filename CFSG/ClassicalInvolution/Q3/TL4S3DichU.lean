module

public import CFSG.ClassicalInvolution.Q3.TL4S3DichB
public import CFSG.ClassicalInvolution.Q3.Q3AM289Dich
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1M

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.S3Dich

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem exists_sl2_embedding_su3 :
    ∃ ι : SL(2, ZMod 3) →* SU3, Function.Injective ι ∧ ι.range = rootSU2₃ := by
  obtain ⟨e2⟩ := Q3P21.exists_su2_equiv_sl2 (K := F9) (p := 3) (f := 1) card_F9 (by norm_num)
    (by norm_num)
  refine ⟨(blockEmb F9 3 1 3 2 0 (by norm_num)).comp e2.symm.toMonoidHom,
    (blockEmb_injective (by norm_num)).comp e2.symm.injective, ?_⟩
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective e2.symm.toMonoidHom e2.symm.surjective,
    ← MonoidHom.range_eq_map]
  rfl

theorem mem_of_pow_four_su3 {L₁ : Subgroup SU3} (hL₁ : IsSylow2In L₁ rootSU2₃) {x : SU3}
    (hx : x ∈ rootSU2₃) (hx4 : x ^ 4 = 1) : x ∈ L₁ := by
  obtain ⟨ι, hι, hιR⟩ := exists_sl2_embedding_su3
  rw [← hιR] at hL₁ hx
  obtain ⟨y, rfl⟩ := hx
  exact mem_of_pow_four ι hι hL₁ (hι (by rw [map_pow, hx4, map_one]))

theorem weylElt_mul_self : weylElt F9 3 1 * weylElt F9 3 1 = negOneSU F9 3 1 := by
  apply suMat_injective
  rw [suMat_mul, suMat_negOneSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suMat, weylElt, Matrix.mul_apply, Fin.sum_univ_two]

theorem isBlockScalar_of_commute_sylow {L₁ : Subgroup SU3} (hL₁ : IsSylow2In L₁ rootSU2₃)
    {M : Matrix (Fin 3) (Fin 3) F9}
    (hM : ∀ x ∈ L₁, M * (((x : SU3) : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) =
      (((x : SU3) : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) * M) :
    IsBlockScalar M := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := normOne (unitaryInvolution F9 3 1))
  rw [card_normOne card_F9] at hu
  have hu4 : u ^ 4 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu] at h
  have hu2 : ((u : F9ˣ) : F9) ≠ ((u : F9ˣ) : F9)⁻¹ := by
    intro h
    have hsq : ((u : F9ˣ) : F9) * ((u : F9ˣ) : F9) = 1 := by
      calc ((u : F9ˣ) : F9) * ((u : F9ˣ) : F9) = ((u : F9ˣ) : F9) * ((u : F9ˣ) : F9)⁻¹ := by
            rw [← h]
        _ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
    have h1 : u ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_one, Units.val_one, pow_two]
      exact hsq
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at h3
    exact absurd h3 (by norm_num)
  have hmem : ∀ A : Su F9 3 1 2, A ^ 4 = 1 → blockEmb F9 3 1 3 2 0 (by norm_num) A ∈ L₁ :=
    fun A hA => mem_of_pow_four_su3 hL₁ ⟨A, rfl⟩ (by rw [← map_pow, hA, map_one])
  have hz := hM _ (hmem (negOneSU F9 3 1) (by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq, negOneSU_mul_self, one_mul]))
  have hd := hM _ (hmem (torusTwo (unitaryInvolution F9 3 1) u) (by
    rw [← map_pow, hu4, map_one]))
  have hj := hM _ (hmem (weylElt F9 3 1) (by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq, weylElt_mul_self, negOneSU_mul_self]))
  rw [coe_blockEmb3] at hz hd hj
  refine isBlockScalar_of_commute_unitary two_ne_zero_F9 hu2 M ?_ ?_ ?_
  · convert hz using 2 <;> simp [negOneSU]
  · convert hd using 2 <;> simp [coe_torusTwo]
  · convert hj using 2 <;> simp [weylElt]

theorem isBlockScalar_of_commutes_sylow {L₁ : Subgroup SU3} (hL₁ : IsSylow2In L₁ rootSU2₃)
    {g : SU3} (hg : ∀ r ∈ L₁, g * r = r * g) : IsBlockScalar (suMat g) :=
  isBlockScalar_of_commute_sylow hL₁ fun x hx => congrArg suMat (hg x hx)

theorem invDich_rootSU2 {L₁ : Subgroup SU3} (hL₁ : IsSylow2In L₁ rootSU2₃) : InvDich SU3 L₁ := by
  intro ρ hρ2 hρR
  have hC : ∀ g : SU3, (∀ r ∈ L₁, g * r = r * g) → g * g = 1 → g = 1 ∨ g = rootInvSU₃ := by
    intro g hg hg2
    have hsq : suMat g * suMat g = 1 := by rw [← suMat_mul, hg2, suMat_one]
    rcases isBlockScalar_sq_eq_one (isBlockScalar_of_commutes_sylow hL₁ hg) (det_suMat g) hsq
      with h | h
    · exact Or.inl (suMat_injective (by rw [h, suMat_one]))
    · exact Or.inr (suMat_injective (by rw [h, suMat_rootInvSU₃]))
  have hγC : ∀ g : SU3, (∀ r ∈ L₁, g * r = r * g) → suGam g = g⁻¹ := by
    intro g hg
    apply suToSL_injective
    rw [suToSL_suGam, map_inv]
    refine gam'_eq_inv_of_isBlockScalar ?_
    rw [← map_inv, coe_suToSL]
    refine isBlockScalar_of_commutes_sylow hL₁ fun r hr => ?_
    have := hg r hr
    calc g⁻¹ * r = g⁻¹ * (r * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * r) * g⁻¹ := by rw [this]
      _ = r * g⁻¹ := by group
  rcases eq_one_or_conj_of_invol center_su3_eq_bot outOne_su3 (R := L₁) (t := rootInvSU₃)
      rootInvSU₃_mul_self rootInvSU₃_ne_one hC suGam
      (fun r hr => suGam_apply_of_mem (hL₁.1 hr)) suGam_sq hγC ρ hρ2 hρR with h | h
  · exact ⟨1, L₁.one_mem, mul_one 1, by rw [h, map_one]⟩
  · refine ⟨rootInvSU₃, mem_of_pow_four_su3 hL₁ (rootInvSU_mem_rootSU2 _) ?_,
      rootInvSU₃_mul_self, h⟩
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq, rootInvSU₃_mul_self, one_mul]

theorem invDich_su3 {g₀ : SU3} {L₀ : Subgroup SU3} (hL₀ : IsSylow2In L₀ (conjSub g₀ rootSU2₃)) :
    InvDich SU3 L₀ := by
  have h := (invDich_rootSU2 (isSylow2In_conj g₀ hL₀)).map (MulAut.conj g₀)
  have hL : (conjSub g₀⁻¹ L₀).map (MulAut.conj g₀).toMonoidHom = L₀ := by
    change conjSub g₀ (conjSub g₀⁻¹ L₀) = L₀
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  rwa [hL] at h

theorem invDich_psu3 {R : Subgroup (CompData.model .PSU 3).G}
    (hR : R ∈ (CompData.model .PSU 3).fund) {L₀ : Subgroup (CompData.model .PSU 3).G}
    (hL₀ : IsSylow2In L₀ R) : InvDich (CompData.model .PSU 3).G L₀ := by
  obtain ⟨e', he'⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num)
    statedLieAdmissible_psu3
  obtain ⟨g₀, hg₀⟩ := (mem_longRootSetU_iff (by norm_num)).mp ((he' R).mp hR)
  have hg₀' : R.map e'.toMonoidHom = conjSub g₀ rootSU2₃ := hg₀
  have h1 := isSylow2In_map e' hL₀
  rw [hg₀'] at h1
  have h2 := (invDich_su3 h1).map e'.symm
  have hL : (L₀.map e'.toMonoidHom).map e'.symm.toMonoidHom = L₀ := by
    rw [Subgroup.map_map]
    ext x
    simp
  rwa [hL] at h2

end CFSG.ClassicalInvolution.Q3.TL4.S3Dich
