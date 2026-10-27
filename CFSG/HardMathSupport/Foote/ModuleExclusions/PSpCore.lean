module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSpAlg
public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSLCore

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Matrix CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

section Dim

variable {n : ℕ} {K : Type} [Field K]

theorem exists_pair_indep (E : Submodule K (Fin n ⊕ Fin n → K)) (hE : 2 ≤ Module.finrank K E) :
    ∃ v v' : Fin n ⊕ Fin n → K, v ∈ E ∧ v' ∈ E ∧ v ≠ 0 ∧ LinearIndependent K ![v, v'] := by
  have hpos : 0 < Module.finrank K E := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K) (M := E)
    (by omega) hx
  refine ⟨(x : Fin n ⊕ Fin n → K), (y : Fin n ⊕ Fin n → K), x.2, y.2,
    fun h0 => hx (Subtype.ext h0), ?_⟩
  rw [LinearIndependent.pair_iff] at hy ⊢
  intro s t hst
  exact hy s t (Subtype.ext (by simpa using hst))

theorem exists_orth_pair (E : Submodule K (Fin n ⊕ Fin n → K)) (hE : 3 ≤ Module.finrank K E)
    (h2 : (2 : K) ≠ 0) :
    ∃ v v' : Fin n ⊕ Fin n → K, v ∈ E ∧ v' ∈ E ∧ LinearIndependent K ![v, v'] ∧
      sLam v ⬝ᵥ v' = 0 := by
  have hpos : 0 < Module.finrank K E := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  let φ : E →ₗ[K] K := (dotProductBilin K K (sLam (x : Fin n ⊕ Fin n → K))).comp E.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : Module.finrank K (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have h4 : 1 < Module.finrank K (LinearMap.ker φ) := by omega
  have hxk : x ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    show sLam (x : Fin n ⊕ Fin n → K) ⬝ᵥ (x : Fin n ⊕ Fin n → K) = 0
    exact sLam_dot_self h2 _
  have hx' : (⟨x, hxk⟩ : LinearMap.ker φ) ≠ 0 := fun h0 => hx (congrArg Subtype.val h0)
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K)
    (M := LinearMap.ker φ) h4 hx'
  refine ⟨(x : Fin n ⊕ Fin n → K), ((y : E) : Fin n ⊕ Fin n → K), x.2, (y : E).2, ?_, ?_⟩
  · have hy' := LinearIndependent.pair_iff.mp hy
    rw [LinearIndependent.pair_iff]
    intro s t hst
    exact hy' s t (Subtype.ext (Subtype.ext (by simpa using hst)))
  · have := y.2
    rw [LinearMap.mem_ker] at this
    exact this

theorem exists_eig_pm {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hM : M * M = (1 : K) • 1)
    (hnon : ∀ a : K, M ≠ a • 1) :
    (∃ a, a ∈ eig M 1 ∧ a ≠ 0) ∧ (∃ b, b ∈ eig M (-1) ∧ b ≠ 0) := by
  have hMMx : ∀ x : Fin n ⊕ Fin n → K, M *ᵥ (M *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hM, Matrix.smul_mulVec, one_smul, Matrix.one_mulVec]
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_not_scalar M hnon
  have hv' := LinearIndependent.pair_iff.mp hv
  refine ⟨⟨v + M *ᵥ v, ?_, ?_⟩, ⟨v - M *ᵥ v, ?_, ?_⟩⟩
  · rw [mem_eig, Matrix.mulVec_add, hMMx, one_smul, add_comm]
  · intro h0
    have := hv' 1 1 (by rw [one_smul, one_smul]; exact h0)
    exact one_ne_zero this.1
  · rw [mem_eig, Matrix.mulVec_sub, hMMx]
    module
  · intro h0
    have := hv' 1 (-1) (by rw [one_smul, neg_smul, one_smul, ← sub_eq_add_neg]; exact h0)
    exact one_ne_zero this.1

end Dim

section Group

variable {n : ℕ} {K : Type} [Field K] [CharP K 5]

abbrev gm (h : ↥(StatedSp n K)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  ((h : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)

theorem two_ne_zero_five : (2 : K) ≠ 0 := by
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  intro h2
  have : (1 : K) = 0 := by linear_combination 3 * h2 - h5
  exact one_ne_zero this

theorem key_c55 (hn : 1 ≤ n) (h : ↥(StatedSp n K)) {c ε ε' : K} (hM : gm h * gm h = c • 1)
    (hεε' : ε * ε' = -1) {u v v' : Fin n ⊕ Fin n → K} (hu : u ≠ 0)
    (hMu : gm h *ᵥ u = ε • u) (hv : gm h *ᵥ v = ε' • v) (hv' : gm h *ᵥ v' = ε' • v')
    (hLI : LinearIndependent K ![v, v']) (hvv' : sLam v ⬝ᵥ v' = 0) :
    ∃ Φ : C55 →* StatedProj (StatedSp n K), Function.Injective Φ ∧
      ∀ w : C55, (QuotientGroup.mk h : StatedProj (StatedSp n K)) * Φ w *
        (QuotientGroup.mk h : StatedProj (StatedSp n K))⁻¹ = (Φ w)⁻¹ := by
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsymp := symp_of_mem_statedSp h.2
  have h2 : (2 : K) ≠ 0 := two_ne_zero_five
  have hLI' := LinearIndependent.pair_iff.mp hLI
  have hv0 : v ≠ 0 := by
    intro h0
    have := hLI' 1 0 (by simp [h0])
    exact one_ne_zero this.1
  have hv'0 : v' ≠ 0 := by
    intro h0
    have := hLI' 0 1 (by simp [h0])
    exact one_ne_zero this.2
  have hne : ε * ε' ≠ 1 := by
    rw [hεε']
    intro h1
    apply h2
    linear_combination -h1
  have hne' : ε' * ε ≠ 1 := by rwa [mul_comm]
  have o_uv : sLam u ⬝ᵥ v = 0 := sLam_eigen_zero hsymp hMu hv hne
  have o_uv' : sLam u ⬝ᵥ v' = 0 := sLam_eigen_zero hsymp hMu hv' hne
  have o_vu : sLam v ⬝ᵥ u = 0 := sLam_eigen_zero hsymp hv hMu hne'
  have o_v'u : sLam v' ⬝ᵥ u = 0 := sLam_eigen_zero hsymp hv' hMu hne'
  have o_v'v : sLam v' ⬝ᵥ v = 0 := by rw [sLam_dot_swap, hvv', neg_zero]
  have hAA := sS_mul_sS h2 u v v o_vu o_uv (sLam_dot_self h2 v)
  have hAB := sS_mul_sS h2 u v v' o_vu o_uv' hvv'
  have hBA := sS_mul_sS h2 u v' v o_v'u o_uv o_v'v
  have hBB := sS_mul_sS h2 u v' v' o_v'u o_uv' (sLam_dot_self h2 v')
  have hMA := anticomm_sS hsymp hM hu hv0 hMu hv hεε'
  have hMB := anticomm_sS hsymp hM hu hv'0 hMu hv' hεε'
  have hH : ∀ a b : ZMod 5, Tu hAA hAB hBA hBB (zi K a) (zi K b) ∈ StatedSp n K := fun a b => by
    apply mem_statedSp_of_symp
    have e : ((Tu hAA hAB hBA hBB (zi K a) (zi K b) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        1 + (1 : K) • sS u (zi K a • v + zi K b • v') := by
      show Tm (sS u v) (sS u v') (zi K a) (zi K b) = _
      simp only [Tm, sS_add_right, sS_smul_right, one_smul, add_assoc]
    rw [e]
    refine sS_symp h2 u _ ?_ 1
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, o_uv, o_uv']
    simp
  have hind : ∀ a b : ZMod 5, zi K a • sS u v + zi K b • sS u v' = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h0 : sS u (zi K a • v + zi K b • v') = 0 := by
      rw [sS_add_right, sS_smul_right, sS_smul_right]
      exact hab
    have h1 := eq_zero_of_sS h2 hu h0
    obtain ⟨ha, hb⟩ := hLI' _ _ h1
    exact ⟨(zi K).injective (by rw [ha, map_zero]), (zi K).injective (by rw [hb, map_zero])⟩
  exact inverted_c55_proj (StatedSp n K) (h : GL (Fin n ⊕ Fin n) K) h.2 hAA hAB hBA hBB hMA hMB
    hH hind

theorem psp_neg_inverts (hn : 2 ≤ n) (h : ↥(StatedSp n K)) (hM : gm h * gm h = (-1 : K) • 1) :
    ∃ Φ : C55 →* StatedProj (StatedSp n K), Function.Injective Φ ∧
      ∀ w : C55, (QuotientGroup.mk h : StatedProj (StatedSp n K)) * Φ w *
        (QuotientGroup.mk h : StatedProj (StatedSp n K))⁻¹ = (Φ w)⁻¹ := by
  have hsymp := symp_of_mem_statedSp h.2
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have h2 : (2 : K) ≠ 0 := two_ne_zero_five
  have h22 : (2 : K) * 2 = -1 := by linear_combination h5
  have hM' : gm h * gm h = ((2 : K) * 2) • 1 := by rw [h22]; exact hM
  have hdim := finrank_eig_add (n := n) h2 h2 hM'
  have hiso : ∀ x ∈ eig (gm h) (-2), ∀ y ∈ eig (gm h) (-2), sLam x ⬝ᵥ y = 0 := by
    intro x hx y hy
    refine sLam_eigen_zero hsymp (mem_eig.mp hx) (mem_eig.mp hy) ?_
    intro h1
    apply h2
    linear_combination h5 - h1
  have hle := finrank_le_of_isotropic _ hiso
  have hge : 2 ≤ Module.finrank K (eig (gm h) 2) := by
    omega
  obtain ⟨v, v', hv, hv', hv0, hLI⟩ := exists_pair_indep _ hge
  have hωvv' : sLam v ⬝ᵥ v' = 0 := by
    refine sLam_eigen_zero hsymp (mem_eig.mp hv) (mem_eig.mp hv') ?_
    rw [h22]
    intro h1
    apply h2
    linear_combination -h1
  exact key_c55 (by omega) h hM h22 hv0 (mem_eig.mp hv) (mem_eig.mp hv) (mem_eig.mp hv') hLI hωvv'

theorem psp_pos_big (hn : 1 ≤ n) (h : ↥(StatedSp n K)) (hM : gm h * gm h = (1 : K) • 1)
    {ε' : K} (hε' : ε' * ε' = 1) (hd : 3 ≤ Module.finrank K (eig (gm h) ε'))
    {u : Fin n ⊕ Fin n → K} (hu : u ∈ eig (gm h) (-ε')) (hu0 : u ≠ 0) :
    ∃ Φ : C55 →* StatedProj (StatedSp n K), Function.Injective Φ ∧
      ∀ w : C55, (QuotientGroup.mk h : StatedProj (StatedSp n K)) * Φ w *
        (QuotientGroup.mk h : StatedProj (StatedSp n K))⁻¹ = (Φ w)⁻¹ := by
  obtain ⟨v, v', hv, hv', hLI, hω⟩ := exists_orth_pair _ hd two_ne_zero_five
  exact key_c55 hn h hM (by linear_combination -hε') hu0 (mem_eig.mp hu) (mem_eig.mp hv)
    (mem_eig.mp hv') hLI hω

theorem psp_pos_zeta (hn : 1 ≤ n) (hK : 5 < Nat.card K) (h : ↥(StatedSp n K))
    (hM : gm h * gm h = (1 : K) • 1) (hnon : ∀ a : K, gm h ≠ a • 1) :
    ∃ Φ : C55 →* StatedProj (StatedSp n K), Function.Injective Φ ∧
      ∀ w : C55, (QuotientGroup.mk h : StatedProj (StatedSp n K)) * Φ w *
        (QuotientGroup.mk h : StatedProj (StatedSp n K))⁻¹ = (Φ w)⁻¹ := by
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hsymp := symp_of_mem_statedSp h.2
  have h2 : (2 : K) ≠ 0 := two_ne_zero_five
  obtain ⟨ζ, hζ⟩ := exists_not_mem_primeField hK
  obtain ⟨⟨a, ha, ha0⟩, ⟨b, hb, hb0⟩⟩ := exists_eig_pm hM hnon
  have hMa := mem_eig.mp ha
  have hMb := mem_eig.mp hb
  have hne : (1 : K) * (-1) ≠ 1 := by
    intro h1
    apply h2
    linear_combination -h1
  have hne' : (-1 : K) * 1 ≠ 1 := by
    intro h1
    apply h2
    linear_combination -h1
  have o_ab : sLam a ⬝ᵥ b = 0 := sLam_eigen_zero hsymp hMa hMb hne
  have o_ba : sLam b ⬝ᵥ a = 0 := sLam_eigen_zero hsymp hMb hMa hne'
  have hXX := sS_mul_sS h2 a b b o_ba o_ab (sLam_dot_self h2 b)
  have hX0 : sS a b ≠ 0 := fun h0 => hb0 (eq_zero_of_sS h2 ha0 h0)
  have hMX := anticomm_sS hsymp hM ha0 hb0 hMa hMb (by norm_num)
  refine inverted_c55_proj_single (StatedSp n K) (h : GL (Fin n ⊕ Fin n) K) h.2 hXX hX0 hMX hζ
    (fun g a' b' hg => ?_)
  apply mem_statedSp_of_symp
  have e : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      1 + (zi K a' + zi K b' * ζ) • sS a b := by
    rw [hg, add_smul, mul_smul, add_assoc]
  rw [e]
  exact sS_symp h2 a b o_ab _

theorem psp_inverts (hn : 2 ≤ n) (hK : 3 ≤ n ∨ 5 < Nat.card K)
    (z : StatedProj (StatedSp n K)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∃ Φ : C55 →* StatedProj (StatedSp n K), Function.Injective Φ ∧
      ∀ w : C55, z * Φ w * z⁻¹ = (Φ w)⁻¹ := by
  classical
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc, hM⟩ := scalar_sq_of_mk_sq h hz2
  have hnon := not_scalar_of_mk_ne_one h hz1
  have hsymp := symp_of_mem_statedSp h.2
  have hcc : c * c = 1 := by
    have h1 : (gm h * gm h)ᵀ * sJ n K * (gm h * gm h) = sJ n K := by
      rw [Matrix.transpose_mul]
      calc (gm h)ᵀ * (gm h)ᵀ * sJ n K * (gm h * gm h)
          = (gm h)ᵀ * ((gm h)ᵀ * sJ n K * gm h) * gm h := by simp only [Matrix.mul_assoc]
        _ = sJ n K := by rw [hsymp, hsymp]
    rw [hM] at h1
    have h3 : (c * c) • sJ n K = sJ n K := by
      simpa [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] using h1
    have h4 := congrFun (congrFun h3 (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
    simpa [sJ] using h4
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · rw [h1] at hM
    by_cases hn3 : 3 ≤ n
    · have h5 : (1 : K) ≠ 0 := one_ne_zero
      have hM' : gm h * gm h = ((1 : K) * 1) • 1 := by rw [mul_one]; exact hM
      have hdim := finrank_eig_add (n := n) two_ne_zero_five h5 hM'
      obtain ⟨⟨a, ha, ha0⟩, ⟨b, hb, hb0⟩⟩ := exists_eig_pm hM hnon
      by_cases hd : 3 ≤ Module.finrank K (eig (gm h) 1)
      · exact psp_pos_big (by omega) h hM (ε' := 1) (by norm_num) hd (u := b) (by simpa using hb)
          hb0
      · have hd' : 3 ≤ Module.finrank K (eig (gm h) (-1)) := by omega
        exact psp_pos_big (by omega) h hM (ε' := -1) (by norm_num) hd' (u := a)
          (by simpa using ha) ha0
    · exact psp_pos_zeta (by omega) (hK.resolve_left hn3) h hM hnon
  · rw [h1] at hM
    exact psp_neg_inverts hn h hM

end Group

end CFSG.HardMathSupport.Foote.ModuleExclusions
