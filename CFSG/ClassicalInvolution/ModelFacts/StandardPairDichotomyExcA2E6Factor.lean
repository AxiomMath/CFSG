module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Levi

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Rank1

variable {F : Type} [Field F]

theorem rootSL2_HSL_mem_levi_E6 (s : Fˣ) :
    rootSL2 .E6 F thetaE6 (HSL s) ∈ parabolicLevi .E6 F JE6 :=
  torusGroup_le_parabolicLevi JE6
    ((exceptional_Lang_root_rank_one_torus_transport .E6 F isRoot_thetaE6).2.1 s)

variable (F) in
@[expose] def h1E6 : Subgroup (ModGL .E6 F) where
  carrier := {x | ∃ n ∈ parabolicLevi .E6 F JE6, ∃ A : SL2 F, x = n * rootSL2 .E6 F thetaE6 A}
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, A₁, rfl⟩ ⟨n₂, hn₂, A₂, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E6 (inv_mem hn₂) A₁
    rw [inv_inv] at hA'
    refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, A' * A₂, ?_⟩
    calc n₁ * rootSL2 .E6 F thetaE6 A₁ * (n₂ * rootSL2 .E6 F thetaE6 A₂) =
        n₁ * n₂ * (n₂⁻¹ * rootSL2 .E6 F thetaE6 A₁ * n₂) * rootSL2 .E6 F thetaE6 A₂ := by group
      _ = _ := by rw [hA', map_mul]; group
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, hn, A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E6 hn A⁻¹
    refine ⟨n⁻¹, inv_mem hn, A', ?_⟩
    rw [← hA', map_inv]
    group

theorem rootSL2_mem_h1E6 (A : SL2 F) : rootSL2 .E6 F thetaE6 A ∈ h1E6 F :=
  ⟨1, one_mem _, A, by simp⟩

theorem levi_le_h1E6 {n : ModGL .E6 F} (hn : n ∈ parabolicLevi .E6 F JE6) : n ∈ h1E6 F :=
  ⟨n, hn, 1, by simp⟩

theorem toralRootGroup_le_h1E6 (hF : ringChar F ≠ 2) :
    toralRootGroup .E6 F (thetaDiag thetaE6 (-1 : Fˣ)) ≤ h1E6 F := by
  refine sup_le (fun t ht => levi_le_h1E6 (torusGroup_le_parabolicLevi JE6 ht)) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaE6 σ) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_thetaDiag]
    exact hσ1
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E6 F isRoot_thetaE6).1
  rcases eq_or_iform_eq_zero_of_even_E6 hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .E6 F thetaE6 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    obtain ⟨A, rfl⟩ := this
    exact rootSL2_mem_h1E6 A
  · intro x hx
    have : x ∈ rootRankOneGroup .E6 F thetaE6 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    obtain ⟨A, rfl⟩ := this
    exact rootSL2_mem_h1E6 A
  · intro x hx
    exact levi_le_h1E6 (rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_E6 hσr h0) hx)

end Rank1

section Factor

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_factor_levi_E6 {n : ModGL .E6 k} (hn : n ∈ parabolicLevi .E6 k JE6) :
    ∃ (s : kˣ) (y : ModGL .E6 k), y ∈ parabolicLevi .E6 k JE6 ∧
      (∀ A : SL2 k, y * rootSL2 .E6 k thetaE6 A = rootSL2 .E6 k thetaE6 A * y) ∧
      n = rootSL2 .E6 k thetaE6 (HSL s) * y := by
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaE6 hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (l : k) (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact l.ne_zero (by simpa using hz.symm)
  set s : kˣ := Units.mk0 z hz0 with hs
  have hs2 : (s : k) ^ 2 = l := hz
  have hs2' : ((s⁻¹ : kˣ) : k) ^ 2 = ((l⁻¹ : kˣ) : k) := by
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_pow, hs2]
  set ρ := rootSL2 .E6 k thetaE6 with hρ
  have hHu : ∀ w : k, ρ (HSL s) * ρ (uSL w) * (ρ (HSL s))⁻¹ = ρ (uSL ((l : k) * w)) := fun w => by
    rw [hρ, rootSL2_HSL_conj_uSL, hs2]
  have hHv : ∀ w : k, ρ (HSL s) * ρ (vSL w) * (ρ (HSL s))⁻¹ =
      ρ (vSL (((l⁻¹ : kˣ) : k) * w)) := fun w => by
    rw [hρ, rootSL2_HSL_conj_vSL, hs2']
  have hyu : ∀ w : k, (ρ (HSL s))⁻¹ * n * ρ (uSL w) = ρ (uSL w) * ((ρ (HSL s))⁻¹ * n) :=
    fun w => by
      calc (ρ (HSL s))⁻¹ * n * ρ (uSL w) = (ρ (HSL s))⁻¹ * (n * ρ (uSL w) * n⁻¹) * n := by group
        _ = (ρ (HSL s))⁻¹ * ρ (uSL ((l : k) * w)) * n := by rw [hu]
        _ = (ρ (HSL s))⁻¹ * (ρ (HSL s) * ρ (uSL w) * (ρ (HSL s))⁻¹) * n := by rw [hHu]
        _ = _ := by group
  have hyv : ∀ w : k, (ρ (HSL s))⁻¹ * n * ρ (vSL w) = ρ (vSL w) * ((ρ (HSL s))⁻¹ * n) :=
    fun w => by
      calc (ρ (HSL s))⁻¹ * n * ρ (vSL w) = (ρ (HSL s))⁻¹ * (n * ρ (vSL w) * n⁻¹) * n := by group
        _ = (ρ (HSL s))⁻¹ * ρ (vSL (((l⁻¹ : kˣ) : k) * w)) * n := by rw [hv]
        _ = (ρ (HSL s))⁻¹ * (ρ (HSL s) * ρ (vSL w) * (ρ (HSL s))⁻¹) * n := by rw [hHv]
        _ = _ := by group
  refine ⟨s, (ρ (HSL s))⁻¹ * n, mul_mem (inv_mem (rootSL2_HSL_mem_levi_E6 s)) hn,
    commute_rootSL2_of_commute_uv hyu hyv, by group⟩

theorem exists_factor_h1E6 {c : ModGL .E6 k} (hc : c ∈ h1E6 k) :
    ∃ (B : SL2 k) (y : ModGL .E6 k), y ∈ parabolicLevi .E6 k JE6 ∧
      (∀ A : SL2 k, y * rootSL2 .E6 k thetaE6 A = rootSL2 .E6 k thetaE6 A * y) ∧
      c = rootSL2 .E6 k thetaE6 B * y := by
  obtain ⟨n, hn, A, rfl⟩ := hc
  obtain ⟨s, y, hyL, hyc, rfl⟩ := exists_factor_levi_E6 hn
  refine ⟨HSL s * A, y, hyL, hyc, ?_⟩
  calc rootSL2 .E6 k thetaE6 (HSL s) * y * rootSL2 .E6 k thetaE6 A =
      rootSL2 .E6 k thetaE6 (HSL s) * (y * rootSL2 .E6 k thetaE6 A) := by group
    _ = rootSL2 .E6 k thetaE6 (HSL s) * (rootSL2 .E6 k thetaE6 A * y) := by rw [hyc A]
    _ = _ := by rw [map_mul]; group

end Factor

section Normal

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_conj_signDiag_deltaE6 {p : ℕ} [Fact p.Prime] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (hp2 : p ≠ 2)
    {c g : ModGL .E6 k} (hgG : g ∈ adjointGroup .E6 k) (hc2 : c * c = 1) (hcH : c ∈ h1E6 k)
    (hgc : g * signDiagE6 k thetaE6 * g⁻¹ = c)
    (hnc : ¬ ∀ A : SL2 k, c * rootSL2 .E6 k thetaE6 A = rootSL2 .E6 k thetaE6 A * c) :
    ∃ v ∈ h1E6 k, v * c * v⁻¹ = signDiagE6 k deltaE6 := by
  have hk : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hinj : Function.Injective (rootSL2 .E6 k thetaE6) :=
    ((exceptional_Lang_root_rank_one_data .E6 k thetaE6).2.2.2.2.2.2.2.1 hk).1
  obtain ⟨B, y, hyL, hyB, hcdef⟩ := exists_factor_h1E6 hcH
  set ρ := rootSL2 .E6 k thetaE6 with hρ
  have hsq : ρ (B * B) * (y * y) = 1 := by
    have e : (ρ B * y) * (ρ B * y) = ρ (B * B) * (y * y) := by
      rw [map_mul]
      calc (ρ B * y) * (ρ B * y) = ρ B * (y * ρ B) * y := by group
        _ = ρ B * (ρ B * y) * y := by rw [hyB B]
        _ = _ := by group
    rw [← e, ← hcdef]
    exact hc2
  have hcen : ∀ A : SL2 k, (B * B) * A = A * (B * B) := by
    intro A
    apply hinj
    rw [map_mul ρ (B * B) A, map_mul ρ A (B * B)]
    have hyy : ρ (B * B) = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have hyyA : y * y * ρ A = ρ A * (y * y) := by
      rw [mul_assoc, hyB A, ← mul_assoc, hyB A, mul_assoc]
    rw [hyy]
    calc (y * y)⁻¹ * ρ A = (y * y)⁻¹ * (ρ A * (y * y)) * (y * y)⁻¹ := by group
      _ = (y * y)⁻¹ * (y * y * ρ A) * (y * y)⁻¹ := by rw [hyyA]
      _ = ρ A * (y * y)⁻¹ := by group
  have hBB : B * B = HSL (-1) := by
    rcases eq_one_or_HSL_neg_one_of_forall_commute hcen with h1 | h1
    · exfalso
      apply hnc
      have hBcent : ∀ A : SL2 k, B * A = A * B := by
        rcases sl2_sq_eq_one_A2 h2 h1 with rfl | rfl
        · intro A; simp
        · intro A
          rw [HSL_neg_one_eq_neg_one_A2]
          simp
      intro A
      rw [hcdef]
      calc ρ B * y * ρ A = ρ B * (y * ρ A) := by group
        _ = ρ B * (ρ A * y) := by rw [hyB A]
        _ = ρ (B * A) * y := by rw [map_mul]; group
        _ = ρ (A * B) * y := by rw [hBcent A]
        _ = ρ A * (ρ B * y) := by rw [map_mul]; group
    · exact h1
  obtain ⟨s, t, hst⟩ := sl2_exists_conj_diag h2 hBB
  have ht2 : (t : k) ^ 2 = -1 := by
    have h1 : HSL t * HSL t = HSL (-1) := by
      calc HSL t * HSL t = (s * B * s⁻¹) * (s * B * s⁻¹) := by rw [hst]
        _ = s * (B * B) * s⁻¹ := by group
        _ = s * HSL (-1) * s⁻¹ := by rw [hBB]
        _ = HSL (-1) := by rw [HSL_neg_one_eq_neg_one_A2]; simp
    rw [HSL_mul_HSL_A2] at h1
    have h3 := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k) 0 0) h1
    simpa [coe_HSL, sq] using h3
  have hys : y * (ρ s)⁻¹ = (ρ s)⁻¹ * y := by
    have := hyB s
    calc y * (ρ s)⁻¹ = (ρ s)⁻¹ * (ρ s * y) * (ρ s)⁻¹ := by group
      _ = (ρ s)⁻¹ * (y * ρ s) * (ρ s)⁻¹ := by rw [this]
      _ = _ := by group
  have hc' : ρ s * c * (ρ s)⁻¹ = ρ (HSL t) * y := by
    rw [hcdef]
    calc ρ s * (ρ B * y) * (ρ s)⁻¹ = ρ s * ρ B * (y * (ρ s)⁻¹) := by group
      _ = ρ s * ρ B * ((ρ s)⁻¹ * y) := by rw [hys]
      _ = ρ (s * B * s⁻¹) * y := by rw [map_mul, map_mul, map_inv]; group
      _ = _ := by rw [hst]
  have hc'L : ρ (HSL t) * y ∈ parabolicLevi .E6 k JE6 :=
    mul_mem (rootSL2_HSL_mem_levi_E6 t) hyL
  have hc'2 : (ρ (HSL t) * y) ^ 2 = 1 := by
    rw [sq, ← hc']
    calc ρ s * c * (ρ s)⁻¹ * (ρ s * c * (ρ s)⁻¹) = ρ s * (c * c) * (ρ s)⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hgy : (ρ s * g) * signDiagE6 k thetaE6 * (ρ s * g)⁻¹ = ρ (HSL t) * y := by
    rw [← hc', ← hgc]
    group
  obtain ⟨v', hv', a, ha, hva⟩ := exists_levi_conj_eq_rootDiagUnit hp2 k halg hc'L hc'2
  have hvg : v' * (ρ s * g) ∈ adjointGroup .E6 k :=
    mul_mem (parabolicSubgroup_le_adjointGroup _ _ _
      (parabolicLevi_le_parabolicSubgroup JE6 hv')) (mul_mem (rootSL2_mem_adjointGroup _ s) hgG)
  have hga : (v' * (ρ s * g)) * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) *
      (v' * (ρ s * g))⁻¹ = rootDiagUnit .E6 a := by
    rw [← hva, ← hgy]
    unfold signDiagE6
    group
  obtain ⟨δ, hδ, rfl⟩ := exists_root_of_conj_thetaDiag_E6 hk ha hvg hga
  have hyu : y * ρ (uSL 1) * y⁻¹ = ρ (uSL 1) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hyB _
  have hc'u : (ρ (HSL t) * y) * ρ (uSL 1) * (ρ (HSL t) * y)⁻¹ = ρ (uSL (-1)) := by
    calc (ρ (HSL t) * y) * ρ (uSL 1) * (ρ (HSL t) * y)⁻¹ =
        ρ (HSL t) * (y * ρ (uSL 1) * y⁻¹) * (ρ (HSL t))⁻¹ := by group
      _ = ρ (HSL t) * ρ (uSL 1) * (ρ (HSL t))⁻¹ := by rw [hyu]
      _ = ρ (uSL ((t : k) ^ 2 * 1)) := by rw [hρ, rootSL2_HSL_conj_uSL]
      _ = ρ (uSL (-1)) := by rw [ht2]; norm_num
  obtain ⟨l', hu', -⟩ := exists_levi_conj_rootSL2_thetaE6 hv'
  have hdu : rootDiagUnit .E6 (thetaDiag δ (-1 : kˣ)) * ρ (uSL (l' : k)) *
      (rootDiagUnit .E6 (thetaDiag δ (-1 : kˣ)))⁻¹ = ρ (uSL (-(l' : k))) := by
    have h1 : ρ (uSL (l' : k)) = v' * ρ (uSL 1) * v'⁻¹ := by
      have := hu' 1
      rw [mul_one] at this
      exact this.symm
    rw [← hva, h1]
    calc v' * (ρ (HSL t) * y) * v'⁻¹ * (v' * ρ (uSL 1) * v'⁻¹) *
          (v' * (ρ (HSL t) * y) * v'⁻¹)⁻¹ =
        v' * ((ρ (HSL t) * y) * ρ (uSL 1) * (ρ (HSL t) * y)⁻¹) * v'⁻¹ := by group
      _ = v' * ρ (uSL (-1)) * v'⁻¹ := by rw [hc'u]
      _ = ρ (uSL ((l' : k) * (-1))) := hu' (-1)
      _ = _ := by rw [mul_neg, mul_one]
  have hχ : (((rootChar (thetaDiag δ (-1 : kˣ)) thetaE6 : kˣ)) : k) = -1 := by
    have h1 := (rootDiagUnit_conj_rootSL2 (thetaDiag δ (-1 : kˣ)) isRoot_thetaE6 (l' : k)).1
    rw [hdu] at h1
    have h3 := uSL_injective_of_field (hinj h1)
    have hl0 : (l' : k) ≠ 0 := l'.ne_zero
    refine mul_right_cancel₀ hl0 ?_
    rw [← h3]
    ring
  have hodd : ¬ Even (iform thetaE6 δ) := by
    intro he
    have h1 : rootChar (thetaDiag δ (-1 : kˣ)) thetaE6 = 1 := by
      rw [rootChar_thetaDiag, iform_comm]
      exact he.neg_one_zpow
    rw [h1, Units.val_one] at hχ
    exact Ring.neg_one_ne_one_of_char_ne_two hk hχ.symm
  have hb := abs_iform_le_two_E6 isRoot_thetaE6 hδ
  rw [abs_le] at hb
  have hm' : iform thetaE6 δ = 1 ∨ iform thetaE6 δ = -1 := by
    rw [Int.not_even_iff_odd] at hodd
    obtain ⟨r, hr⟩ := hodd
    omega
  have hδ' : ∃ δ' : Fin (Tag.rank .E6) → ℤ, IsPartnerE6 δ' ∧
      thetaDiag δ' (-1 : kˣ) = thetaDiag δ (-1 : kˣ) := by
    rcases hm' with h1 | h1
    · refine ⟨-δ, ⟨IsRoot.neg hδ, ?_⟩, thetaDiag_neg_E6 δ⟩
      rw [show (-δ : Fin (Tag.rank .E6) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_right]
      omega
    · exact ⟨δ, ⟨hδ, h1⟩, rfl⟩
  obtain ⟨δ', hδ'p, hδ'd⟩ := hδ'
  obtain ⟨n, hn, hnd⟩ := exists_levi_conj_partnerE6 (F := k) hδ'p
  have hnd' : n * signDiagE6 k deltaE6 * n⁻¹ =
      rootDiagUnit .E6 (thetaDiag δ (-1 : kˣ)) := by
    rw [hnd]
    unfold signDiagE6
    rw [hδ'd]
  refine ⟨n⁻¹ * v' * ρ s, mul_mem (mul_mem (levi_le_h1E6 (inv_mem hn)) (levi_le_h1E6 hv'))
    (rootSL2_mem_h1E6 s), ?_⟩
  calc n⁻¹ * v' * ρ s * c * (n⁻¹ * v' * ρ s)⁻¹ =
      n⁻¹ * (v' * (ρ s * c * (ρ s)⁻¹) * v'⁻¹) * n := by group
    _ = n⁻¹ * (v' * (ρ (HSL t) * y) * v'⁻¹) * n := by rw [hc']
    _ = n⁻¹ * (n * signDiagE6 k deltaE6 * n⁻¹) * n := by rw [hva, hnd']
    _ = signDiagE6 k deltaE6 := by group

end Normal

end CFSG.ClassicalInvolution.ModelFacts.Levi
