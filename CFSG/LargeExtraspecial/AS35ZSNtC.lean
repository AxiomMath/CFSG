module

public import CFSG.LargeExtraspecial.AS35ZSNtB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

noncomputable abbrev de (n : ℕ) : Fin n → K :=
  fun i => if (i : ℕ) < 2 then ω else if (i : ℕ) < 4 then ω * ω else 1

theorem frob_de (i : Fin n) : frob (de n i) * de n i = 1 := by
  simp only [de]
  split_ifs
  · exact frob_mul_self omega_ne_zero
  · exact frob_mul_self (mul_ne_zero omega_ne_zero omega_ne_zero)
  · rw [map_one, one_mul]

theorem prod_de (hn : 4 ≤ n) : ∏ i, de n i = 1 := by
  have e : ∏ i : Fin n, de n i =
      ∏ i ∈ Finset.range n, (if i < 2 then ω else if i < 4 then ω * ω else (1 : K)) :=
    Fin.prod_univ_eq_prod_range (fun i => if i < 2 then ω else if i < 4 then ω * ω else 1) n
  have h2 : ∏ i ∈ Finset.Ico 4 n,
      (if i < 2 then ω else if i < 4 then ω * ω else (1 : K)) = 1 :=
    Finset.prod_eq_one fun i hi => by
      rw [Finset.mem_Ico] at hi
      simp [show ¬ i < 2 by omega, show ¬ i < 4 by omega]
  rw [e, ← Finset.prod_range_mul_prod_Ico _ hn, h2, mul_one]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num
  have := omega_cube
  linear_combination (ω * ω * ω + 1) * this

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

theorem diagSU_cube {d : Fin n → K} (hd : ∀ i, frob (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    (h3 : ∀ i, d i * d i * d i = 1) : diagSU d hd hdet ^ 3 = 1 := by
  refine ext_smul _ fun v => ?_
  rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, diagSU_smul, diagSU_smul, diagSU_smul,
    one_smul]
  funext i
  linear_combination v i * h3 i

theorem diagSU_smul_pp {d : Fin n → K} (hd : ∀ i, frob (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    {i j : Fin n} (hdij : d i = d j) (c : K) :
    diagSU d hd hdet • pp i j c = d i • pp i j c := by
  rw [diagSU_smul]
  funext k
  simp only [pp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with h1 h2 <;> subst_vars <;> simp_all

namespace ZSHyp

variable (h : ZSHyp n q ρ)
include h

omit [FiniteDimensional (ZMod 2) V] in
theorem rs_diag_ne_one {d : Fin n → K} (hd : ∀ i, frob (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    {i j : Fin n} (hij : d i ≠ d j) : rs ρ (diagSU d hd hdet) ≠ 1 := by
  intro h1
  have hc := h.ker_rs h1
  rw [center_SUid h.three_le] at hc
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hc
  have ei := congrFun (hc (Pi.single i 1)) i
  have ej := congrFun (hc (Pi.single j 1)) j
  rw [diagSU_smul] at ei ej
  simp only [Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul] at ei ej
  exact hij (ei.trans ej.symm)

theorem false_even (H₀ : ∀ x : IsoVec n, ∀ a ∈ lineA ρ x.1, oLine ρ x.1 a = a) {k : ℕ}
    (hk : n = k + k) : False := by
  have hn4 := h.four_le
  have h3 : diagSU (de n) frob_de (prod_de hn4) ^ 3 = 1 := diagSU_cube _ _ fun i => by
    simp only [de]
    split_ifs
    · exact omega_cube
    · linear_combination (ω * ω * ω + 1) * omega_cube
    · ring
  obtain ⟨-, hdim, -⟩ := h.Ysum_props 0 k (by omega)
  have htop : Ysum ρ 0 k = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hdim, h.finrank_eq]; omega)
  have hfix := h.Ysum_apply_eq_self H₀ h3 0
    (fun l hb => ⟨de n ⟨0 + 2 * l, by omega⟩, ?_, fun c => ?_⟩) k
  · apply h.rs_diag_ne_one frob_de (prod_de hn4) (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩)
      (by
        simp only [de]
        norm_num
        intro he
        have e2 : ω * ω = ω + 1 := by rw [← frob_omega, frob_apply, _root_.sq]
        exact one_ne_zero (by linear_combination -e2 - he : (1 : K) = 0))
    exact LinearEquiv.ext fun v => hfix v (by rw [htop]; exact Submodule.mem_top)
  · intro h0
    have := frob_de (n := n) ⟨0 + 2 * l, by omega⟩
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  · refine diagSU_smul_pp _ _ ?_ c
    simp only [de]
    split_ifs <;> first | rfl | (exfalso; omega)

omit h [FiniteDimensional (ZMod 2) V] in
theorem mem_of_mem_sup_of_orth {Y B : Submodule (ZMod 2) V}
    (hY : Y ⊓ LinearMap.BilinForm.orthogonal (polarBilin q) Y = ⊥)
    (hBY : B ≤ LinearMap.BilinForm.orthogonal (polarBilin q) Y) {v : V} (hv : v ∈ Y ⊔ B)
    (hvY : v ∈ LinearMap.BilinForm.orthogonal (polarBilin q) Y) : v ∈ B := by
  obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have hyo : y ∈ LinearMap.BilinForm.orthogonal (polarBilin q) Y := by
    have := (LinearMap.BilinForm.orthogonal (polarBilin q) Y).sub_mem hvY (hBY hb)
    rwa [add_sub_cancel_right] at this
  have : y ∈ Y ⊓ LinearMap.BilinForm.orthogonal (polarBilin q) Y := Submodule.mem_inf.2 ⟨hy, hyo⟩
  rw [hY, Submodule.mem_bot] at this
  rw [this, zero_add]
  exact hb

theorem false_odd (H₀ : ∀ x : IsoVec n, ∀ a ∈ lineA ρ x.1, oLine ρ x.1 a = a) {k : ℕ}
    (hk : n = 2 * k + 1) : False := by
  have hn4 := h.four_le
  have hn3 : 3 ≤ n := by omega
  have hk2 : 2 ≤ k := by omega
  set s := s₀ hn3 with hs
  have h3 : s ^ 3 = 1 := s₀_cube hn3
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨hZnd, hZdim, -⟩ := h.Ysum_props 3 (k - 1) (by omega)
  set Z := Ysum ρ 3 (k - 1) with hZ
  set B := blk ρ ⟨0, by omega⟩ ⟨1, by omega⟩ with hB
  have hsupp : ∀ {x : Fin n → K}, (∀ i : Fin n, 3 ≤ (i : ℕ) → x i = 0) → x ≠ 0 →
      herm frob x x = 0 → lineA ρ x ≤ LinearMap.BilinForm.orthogonal (polarBilin q) Z :=
    fun hx hx0 hxx => h.lineA_le_orth_Ysum 3 hx0 hxx hx (k - 1)
  have hpp : ∀ c : K, ∀ i : Fin n, 3 ≤ (i : ℕ) →
      pp (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ c i = 0 := fun c i hi => by
    simp [pp, Fin.ext_iff, show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega]
  have hBZ : B ≤ LinearMap.BilinForm.orthogonal (polarBilin q) Z :=
    sup_le (hsupp (hpp 1) (pp_ne_zero h01 1) (pp_iso h01 one_ne_zero))
      (hsupp (hpp ω) (pp_ne_zero h01 ω) (pp_iso h01 omega_ne_zero))
  obtain ⟨-, hYdim⟩ := AS35ZM.nondeg_sup q hZnd (h.nondeg_blk h01) hBZ
  have hsZ := h.Ysum_apply_eq_self H₀ h3 3 (fun l hb => ⟨1, one_ne_zero, fun c => ?_⟩) (k - 1)
  · have hsd : ∀ i : Fin n, (i : ℕ) < 3 → sd n i = ω := fun i hi => by simp [sd, hi]
    have hsB : ∀ v ∈ B, rs ρ s v = v := fun v hv =>
      h.blk_apply_eq_self H₀ h01 h3 omega_ne_zero
        (fun c => by
          rw [hs, s₀, diagSU_smul_pp _ _ (by rw [hsd _ (by simp), hsd _ (by simp)]) c,
            hsd _ (by simp)]) hv
    have hsix : ∀ m : Fin 6, ∀ v ∈ lineA ρ (six hn3 m), rs ρ s v = v := fun m v hv => by
      refine h.apply_eq_self_of_cube H₀ h3 (six_ne_zero hn3 m) (six_isotropic hn3 m)
        omega_ne_zero ?_ hv
      rw [hs, s₀, six, pv, ← pp, diagSU_smul_pp _ _ ?_ _, hsd _ (by simp)]
      rw [hsd _ (by simp), hsd _ (by split_ifs <;> simp)]
    have hsix_supp : ∀ m : Fin 6, ∀ i : Fin n, 3 ≤ (i : ℕ) → six hn3 m i = 0 := by
      intro m i hi
      simp only [six, pv, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> simp_all
    obtain ⟨m, hm⟩ : ∃ m : Fin 6, ¬ lineA ρ (six hn3 m) ≤ Z ⊔ B := by
      by_contra hall
      push Not at hall
      refine false_of_six_disjoint (U := B) (by rw [h.finrank_blk h01])
        (fun m => lineA ρ (six hn3 m)) (fun m => ?_)
        (fun m => h.finrank_lineA (six_ne_zero hn3 m) (six_isotropic hn3 m))
        (fun m l hml => h.inf_lineA_eq_bot (six_ne_zero hn3 m) (six_isotropic hn3 m)
          (six_ne_zero hn3 l) (six_isotropic hn3 l) (herm_six_ne_zero hn3 hml))
      intro v hv
      exact mem_of_mem_sup_of_orth hZnd hBZ (hall m hv)
        (hsupp (hsix_supp m) (six_ne_zero hn3 m) (six_isotropic hn3 m) hv)
    have hle : Z ⊔ B ⊔ lineA ρ (six hn3 m) ≤ fixSpace (rs ρ s) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> intro v hv <;> rw [mem_fixSpace]
      · exact hsZ v hv
      · exact hsB v hv
      · exact hsix m v hv
    have hlt : Z ⊔ B < Z ⊔ B ⊔ lineA ρ (six hn3 m) :=
      lt_of_le_of_ne le_sup_left fun he => hm (he ▸ le_sup_right)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_mono hle
    rw [hYdim, hZdim, h.finrank_blk h01] at h1
    have hone := eq_one_of_cube_of_finrank (cube_apply_rs (ρ := ρ) h3)
      (by rw [h.finrank_eq]; omega)
    rw [hs, s₀] at hone
    exact h.rs_diag_ne_one frob_sd (prod_sd hn3) (i := ⟨0, by omega⟩) (j := ⟨3, by omega⟩)
      (by simp only [sd]; norm_num; exact omega_ne_one) hone
  · rw [hs, s₀, diagSU_smul_pp _ _ (by simp only [sd]; split_ifs <;> first | rfl | omega) c]
    simp only [sd]
    split_ifs
    · omega
    · rw [one_smul]

theorem exists_oLine_ne : ∃ x : IsoVec n, ∃ a ∈ lineA ρ x.1, oLine ρ x.1 a ≠ a := by
  by_contra hcon
  push Not at hcon
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact h.false_even hcon hk
  · exact h.false_odd hcon hk

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
