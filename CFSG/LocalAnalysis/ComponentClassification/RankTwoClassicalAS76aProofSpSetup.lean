module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpBlocks
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviGen

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt_positiveLong)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Transvection

variable {K : Type} [Field K] {n : ℕ}

theorem exists_form_eq_one {u : Fin n ⊕ Fin n → K} (hu : u ≠ 0) :
    ∃ w : Fin n ⊕ Fin n → K, form u w = 1 := by
  obtain ⟨b, hb⟩ : ∃ b, u b ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  have hs : u b * sgn K b ≠ 0 := mul_ne_zero hb (sgn_ne_zero b)
  refine ⟨(u b * sgn K b)⁻¹ • Pi.single (par b) 1, ?_⟩
  rw [form_smul_right, form_single_right, par_par, inv_mul_cancel₀ hs]

theorem form_single_left' (b : Fin n ⊕ Fin n) (v : Fin n ⊕ Fin n → K) :
    form (Pi.single b 1) v = sgn K b * v (par b) := by
  rw [form_apply, Finset.sum_eq_single b]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

theorem exists_transvection_form (M : StatedSp n K) (hr : (mat n K M - 1).rank = 1) :
    ∃ (u : Fin n ⊕ Fin n → K) (c : K), u ≠ 0 ∧ c ≠ 0 ∧
      ∀ v, (mat n K M - 1) *ᵥ v = (c * form u v) • u := by
  set N := mat n K M - 1 with hN
  obtain ⟨v₀, hv₀⟩ : ∃ v, N *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    have hN0 : N = 0 := by
      ext r t
      have := congrFun (h (Pi.single t 1)) r
      rwa [mulVec_single_one_apply] at this
    rw [hN0, rank_zero] at hr
    exact zero_ne_one hr
  set u := N *ᵥ v₀ with hu
  have hline : ∀ v, ∃ a : K, N *ᵥ v = a • u := by
    have hle : (K ∙ u) ≤ LinearMap.range N.mulVecLin := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨v₀, rfl⟩
    have heq : (K ∙ u) = LinearMap.range N.mulVecLin := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [finrank_span_singleton hv₀]
      exact hr.symm
    intro v
    have hv : N *ᵥ v ∈ (K ∙ u) := by
      rw [heq]
      exact ⟨v, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨a, ha.symm⟩
  choose φ hφ using hline
  have hrel : ∀ v w, φ v * form u w = φ w * form u v := by
    intro v w
    have h1 := form_mulVec M v w
    have hM : mat n K M = N + 1 := by rw [hN, sub_add_cancel]
    rw [hM, add_mulVec, add_mulVec, one_mulVec, one_mulVec, hφ, hφ, form_add_left,
      form_add_right, form_add_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, form_self, form_antisymm u v] at h1
    linear_combination h1
  obtain ⟨w₀, hw₀⟩ := exists_form_eq_one hv₀
  refine ⟨u, φ w₀, hv₀, fun hc => ?_, fun v => ?_⟩
  · have h1 := hrel v₀ w₀
    rw [hw₀, mul_one, hc, zero_mul] at h1
    have h2 := hφ v₀
    rw [h1, zero_smul] at h2
    exact hv₀ h2
  · rw [hφ v]
    congr 1
    have := hrel v w₀
    rw [hw₀, mul_one] at this
    exact this

end Transvection

section Setup

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}
variable {G : Type} [Group G] {A : Subgroup G}

omit [CharP K 2] in
theorem conj_proj_sp (g h : StatedSp (m + 1) K) :
    MulAut.conj (proj (m + 1) K g) (proj (m + 1) K h) = proj (m + 1) K (g * h * g⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

omit [CharP K 2] in
theorem longBlock_zero_mem_range_spL (hm : 1 ≤ m) (X : SL(2, K)) :
    longBlock K (m + 1) ⟨0, by omega⟩ X ∈ (spL K m).range := by
  rw [range_spL]
  refine suppGroup_mono (coords_subset_compl ?_) (isSupp_longBlock _ X)
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem exists_spLeviTheta (hm : 1 ≤ m) (e : rankTwoQuot A ≃* StatedProj (StatedSp (m + 1) K))
    {p : G} (hp : IsInvolutionOfRank e p 1) :
    ∃ θ : ↥A →* StatedProj (StatedSp (m + 1) K), θ.ker = center ↥A ∧ Function.Surjective θ ∧
      ∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL (Fin (m + 1) ⊕ Fin (m + 1)) K,
        Represents e p M ∧ orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K) - 1 =
            a • ((M : Matrix _ _ K) - 1)},
        y ∈ liftSub θ (spBarL K m) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1 := by
  obtain ⟨-, M, hpM, hM2, hr⟩ := hp
  have hMH : M ∈ StatedSp (m + 1) K := hpM.2.1
  set M' : StatedSp (m + 1) K := ⟨M, hMH⟩ with hM'
  have hr' : (mat (m + 1) K M' - 1).rank = 1 := hr
  obtain ⟨u, c, hu, hc, huc⟩ := exists_transvection_form M' hr'
  obtain ⟨w₀, hw₀⟩ := exists_form_eq_one hu
  obtain ⟨g, hge, -⟩ := exists_sp_apply_eq u w₀ hw₀
  set e₀ : Fin (m + 1) ⊕ Fin (m + 1) → K := Pi.single (Sum.inl 0) 1 with he₀
  have hgi : mat (m + 1) K g⁻¹ *ᵥ u = e₀ := ((mulVec_eq_iff g e₀ u).1 hge).symm
  have hconj : mat (m + 1) K g⁻¹ * (mat (m + 1) K M' - 1) * mat (m + 1) K g =
      single (Sum.inl 0) (Sum.inr 0) c := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, huc,
      mulVec_smul, hgi, ← hge, form_mulVec, he₀, form_single_left', single_mulVec]
    ext r
    by_cases hr : r = Sum.inl 0
    · subst hr
      simp
    · simp [hr]
  refine ⟨(MulAut.conj (proj (m + 1) K g⁻¹)).toMonoidHom.comp (quotModelHom e), ?_, ?_, ?_⟩
  · rw [← ker_quotModelHom (e := e)]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · exact (MulAut.conj _).surjective.comp quotModelHom_surjective
  · rintro y ⟨hyj, M₁, N, hpM₁, hM₁2, hyN, a, ha⟩
    refine ⟨?_, hyj⟩
    obtain rfl := hpM.eq_of_orderOf_eq_two hpM₁ hM2 hM₁2
    have hNH : N ∈ StatedSp (m + 1) K := hyN.2.1
    obtain ⟨hyA, hyθ⟩ := (represents_iff_quotModelHom hNH).mp hyN
    refine mem_liftSub.mpr ⟨hyA, ?_⟩
    rw [MonoidHom.comp_apply, hyθ, MulEquiv.coe_toMonoidHom]
    change MulAut.conj (proj (m + 1) K g⁻¹) (proj (m + 1) K ⟨N, hNH⟩) ∈ _
    rw [conj_proj_sp, inv_inv]
    have hmat : mat (m + 1) K (g⁻¹ * ⟨N, hNH⟩ * g) =
        mat (m + 1) K (longBlock K (m + 1) 0 (sl2Upper (a * c))) := by
      rw [longBlock_sl2Upper, mat_elt_positiveLong, transvection, map_mul, map_mul]
      have hNe : mat (m + 1) K ⟨N, hNH⟩ = 1 + a • (mat (m + 1) K M' - 1) := by
        change N.val = 1 + a • (M.val - 1)
        rw [← ha, add_sub_cancel]
      rw [hNe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← map_mul, inv_mul_cancel, map_one,
        Matrix.mul_smul, Matrix.smul_mul, hconj, smul_single, smul_eq_mul]
    obtain ⟨S, hS⟩ := longBlock_zero_mem_range_spL hm (sl2Upper (a * c))
    refine ⟨S, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [hS]
    congr 1
    exact (mat_injective hmat).symm

end Setup

end CFSG.ComponentClassification.RankTwoClassical
