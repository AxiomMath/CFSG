module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Levi
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Class
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Rank1

variable {F : Type} [Field F]

theorem rootSL2_HSL_mem_levi_F4 (s : Fˣ) :
    rootSL2 .F4 F thetaF4 (HSL s) ∈ parabolicLevi .F4 F JF4 :=
  torusGroup_le_parabolicLevi JF4
    ((exceptional_Lang_root_rank_one_torus_transport .F4 F isRoot_thetaF4).2.1 s)

variable (F) in
@[expose] def h1F4 : Subgroup (ModGL .F4 F) where
  carrier := {x | ∃ n ∈ parabolicLevi .F4 F JF4, ∃ A : SL2 F, x = n * rootSL2 .F4 F thetaF4 A}
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, A₁, rfl⟩ ⟨n₂, hn₂, A₂, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_F4 (inv_mem hn₂) A₁
    rw [inv_inv] at hA'
    refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, A' * A₂, ?_⟩
    calc n₁ * rootSL2 .F4 F thetaF4 A₁ * (n₂ * rootSL2 .F4 F thetaF4 A₂) =
        n₁ * n₂ * (n₂⁻¹ * rootSL2 .F4 F thetaF4 A₁ * n₂) * rootSL2 .F4 F thetaF4 A₂ := by group
      _ = _ := by rw [hA', map_mul]; group
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, hn, A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_F4 hn A⁻¹
    refine ⟨n⁻¹, inv_mem hn, A', ?_⟩
    rw [← hA', map_inv]
    group

theorem rootSL2_mem_h1F4 (A : SL2 F) : rootSL2 .F4 F thetaF4 A ∈ h1F4 F :=
  ⟨1, one_mem _, A, by simp⟩

theorem levi_le_h1F4 {n : ModGL .F4 F} (hn : n ∈ parabolicLevi .F4 F JF4) : n ∈ h1F4 F :=
  ⟨n, hn, 1, by simp⟩

theorem toralRootGroup_le_h1F4 (hF : ringChar F ≠ 2) :
    toralRootGroup .F4 F (corootDiagF4 thetaF4 (-1 : Fˣ)) ≤ h1F4 F := by
  refine sup_le (fun t ht => levi_le_h1F4 (torusGroup_le_parabolicLevi JF4 ht)) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaF4 σ / 2) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_corootDiagF4 isRoot_thetaF4 iform_thetaF4_self]
    exact hσ1
  have hL := (exceptional_Lang_root_rank_one_torus_transport .F4 F isRoot_thetaF4).1
  rcases eq_or_iform_eq_zero_of_even_F4 hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .F4 F thetaF4 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    obtain ⟨A, rfl⟩ := this
    exact rootSL2_mem_h1F4 A
  · intro x hx
    have : x ∈ rootRankOneGroup .F4 F thetaF4 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    obtain ⟨A, rfl⟩ := this
    exact rootSL2_mem_h1F4 A
  · intro x hx
    exact levi_le_h1F4 (rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_F4 hσr h0) hx)

end Rank1

section Factor

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_factor_levi_F4 {n : ModGL .F4 k} (hn : n ∈ parabolicLevi .F4 k JF4) :
    ∃ (s : kˣ) (y : ModGL .F4 k), y ∈ parabolicLevi .F4 k JF4 ∧
      (∀ A : SL2 k, y * rootSL2 .F4 k thetaF4 A = rootSL2 .F4 k thetaF4 A * y) ∧
      n = rootSL2 .F4 k thetaF4 (HSL s) * y := by
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaF4 hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (l : k) (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact l.ne_zero (by simpa using hz.symm)
  set s : kˣ := Units.mk0 z hz0 with hs
  have hs2 : (s : k) ^ 2 = l := hz
  have hs2' : ((s⁻¹ : kˣ) : k) ^ 2 = ((l⁻¹ : kˣ) : k) := by
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_pow, hs2]
  set ρ := rootSL2 .F4 k thetaF4 with hρ
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
  refine ⟨s, (ρ (HSL s))⁻¹ * n, mul_mem (inv_mem (rootSL2_HSL_mem_levi_F4 s)) hn,
    commute_rootSL2_of_commute_uv hyu hyv, by group⟩

theorem exists_factor_h1F4 {c : ModGL .F4 k} (hc : c ∈ h1F4 k) :
    ∃ (B : SL2 k) (y : ModGL .F4 k), y ∈ parabolicLevi .F4 k JF4 ∧
      (∀ A : SL2 k, y * rootSL2 .F4 k thetaF4 A = rootSL2 .F4 k thetaF4 A * y) ∧
      c = rootSL2 .F4 k thetaF4 B * y := by
  obtain ⟨n, hn, A, rfl⟩ := hc
  obtain ⟨s, y, hyL, hyc, rfl⟩ := exists_factor_levi_F4 hn
  refine ⟨HSL s * A, y, hyL, hyc, ?_⟩
  calc rootSL2 .F4 k thetaF4 (HSL s) * y * rootSL2 .F4 k thetaF4 A =
      rootSL2 .F4 k thetaF4 (HSL s) * (y * rootSL2 .F4 k thetaF4 A) := by group
    _ = rootSL2 .F4 k thetaF4 (HSL s) * (rootSL2 .F4 k thetaF4 A * y) := by rw [hyc A]
    _ = _ := by rw [map_mul]; group

end Factor

section Normal

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_conj_signDiag_deltaF4 {p : ℕ} [Fact p.Prime] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (hp2 : p ≠ 2)
    {c g : ModGL .F4 k} (hgG : g ∈ adjointGroup .F4 k) (hc2 : c * c = 1) (hcH : c ∈ h1F4 k)
    (hgc : g * signDiagF4 k thetaF4 * g⁻¹ = c)
    (hnc : ¬ ∀ A : SL2 k, c * rootSL2 .F4 k thetaF4 A = rootSL2 .F4 k thetaF4 A * c) :
    ∃ v ∈ h1F4 k, v * c * v⁻¹ = signDiagF4 k deltaF4 := by
  have hk : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hinj : Function.Injective (rootSL2 .F4 k thetaF4) :=
    ((exceptional_Lang_root_rank_one_data .F4 k thetaF4).2.2.2.2.2.2.2.1 hk).1
  obtain ⟨B, y, hyL, hyB, hcdef⟩ := exists_factor_h1F4 hcH
  set ρ := rootSL2 .F4 k thetaF4 with hρ
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
  have hc'L : ρ (HSL t) * y ∈ parabolicLevi .F4 k JF4 :=
    mul_mem (rootSL2_HSL_mem_levi_F4 t) hyL
  have hc'2 : (ρ (HSL t) * y) ^ 2 = 1 := by
    rw [sq, ← hc']
    calc ρ s * c * (ρ s)⁻¹ * (ρ s * c * (ρ s)⁻¹) = ρ s * (c * c) * (ρ s)⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hgy : (ρ s * g) * signDiagF4 k thetaF4 * (ρ s * g)⁻¹ = ρ (HSL t) * y := by
    rw [← hc', ← hgc]
    group
  obtain ⟨v', hv', a, ha, hva⟩ := exists_levi_conj_eq_rootDiagUnit hp2 k halg hc'L hc'2
  have hvg : v' * (ρ s * g) ∈ adjointGroup .F4 k :=
    mul_mem (parabolicSubgroup_le_adjointGroup _ _ _
      (parabolicLevi_le_parabolicSubgroup JF4 hv')) (mul_mem (rootSL2_mem_adjointGroup _ s) hgG)
  have hga : (v' * (ρ s * g)) * rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ)) *
      (v' * (ρ s * g))⁻¹ = rootDiagUnit .F4 a := by
    rw [← hva, ← hgy]
    unfold signDiagF4
    group
  obtain ⟨δ, hδ, hδl, rfl⟩ := exists_root_of_conj_corootDiagF4 hk ha hvg hga
  have hyu : y * ρ (uSL 1) * y⁻¹ = ρ (uSL 1) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hyB _
  have hc'u : (ρ (HSL t) * y) * ρ (uSL 1) * (ρ (HSL t) * y)⁻¹ = ρ (uSL (-1)) := by
    calc (ρ (HSL t) * y) * ρ (uSL 1) * (ρ (HSL t) * y)⁻¹ =
        ρ (HSL t) * (y * ρ (uSL 1) * y⁻¹) * (ρ (HSL t))⁻¹ := by group
      _ = ρ (HSL t) * ρ (uSL 1) * (ρ (HSL t))⁻¹ := by rw [hyu]
      _ = ρ (uSL ((t : k) ^ 2 * 1)) := by rw [hρ, rootSL2_HSL_conj_uSL]
      _ = ρ (uSL (-1)) := by rw [ht2]; norm_num
  obtain ⟨l', hu', -⟩ := exists_levi_conj_rootSL2_thetaF4 hv'
  have hdu : rootDiagUnit .F4 (corootDiagF4 δ (-1 : kˣ)) * ρ (uSL (l' : k)) *
      (rootDiagUnit .F4 (corootDiagF4 δ (-1 : kˣ)))⁻¹ = ρ (uSL (-(l' : k))) := by
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
  have hχ : (((rootChar (corootDiagF4 δ (-1 : kˣ)) thetaF4 : kˣ)) : k) = -1 := by
    have h1 := (rootDiagUnit_conj_rootSL2 (corootDiagF4 δ (-1 : kˣ)) isRoot_thetaF4 (l' : k)).1
    rw [hdu] at h1
    have h3 := uSL_injective_of_field (hinj h1)
    have hl0 : (l' : k) ≠ 0 := l'.ne_zero
    refine mul_right_cancel₀ hl0 ?_
    rw [← h3]
    ring
  have hodd : ¬ Even (iform δ thetaF4 / 2) := by
    intro he
    have h1 : rootChar (corootDiagF4 δ (-1 : kˣ)) thetaF4 = 1 := by
      rw [rootChar_corootDiagF4 hδ hδl]
      exact he.neg_one_zpow
    rw [h1, Units.val_one] at hχ
    exact Ring.neg_one_ne_one_of_char_ne_two hk hχ.symm
  obtain ⟨m, hm⟩ := even_iform_of_long_F4 isRoot_thetaF4 iform_thetaF4_self δ
  have hb := abs_iform_le_four_F4 isRoot_thetaF4 hδ
  rw [abs_le] at hb
  have hmod : iform δ thetaF4 / 2 = m := by
    rw [iform_comm, hm]
    omega
  rw [hmod, Int.not_even_iff_odd] at hodd
  have hm' : m = 1 ∨ m = -1 := by
    obtain ⟨r, hr⟩ := hodd
    omega
  have hneg : iform (-δ) (-δ) = 4 := by
    rw [show (-δ : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_left,
      iform_smul_right, hδl]
    norm_num
  have hδ' : ∃ δ' : Fin (Tag.rank .F4) → ℤ, IsPartnerF4 δ' ∧
      corootDiagF4 δ' (-1 : kˣ) = corootDiagF4 δ (-1 : kˣ) := by
    rcases hm' with h1 | h1
    · refine ⟨-δ, ⟨IsRoot.neg hδ, hneg, ?_⟩,
        corootDiagF4_neg δ (even_iform_of_long_F4 hδ hδl)⟩
      rw [show (-δ : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_right]
      omega
    · exact ⟨δ, ⟨hδ, hδl, by omega⟩, rfl⟩
  obtain ⟨δ', hδ'p, hδ'd⟩ := hδ'
  obtain ⟨n, hn, hnd⟩ := exists_levi_conj_partnerF4 (F := k) hδ'p
  have hnd' : n * signDiagF4 k deltaF4 * n⁻¹ =
      rootDiagUnit .F4 (corootDiagF4 δ (-1 : kˣ)) := by
    rw [hnd]
    unfold signDiagF4
    rw [hδ'd]
  refine ⟨n⁻¹ * v' * ρ s, mul_mem (mul_mem (levi_le_h1F4 (inv_mem hn)) (levi_le_h1F4 hv'))
    (rootSL2_mem_h1F4 s), ?_⟩
  calc n⁻¹ * v' * ρ s * c * (n⁻¹ * v' * ρ s)⁻¹ =
      n⁻¹ * (v' * (ρ s * c * (ρ s)⁻¹) * v'⁻¹) * n := by group
    _ = n⁻¹ * (v' * (ρ (HSL t) * y) * v'⁻¹) * n := by rw [hc']
    _ = n⁻¹ * (n * signDiagF4 k deltaF4 * n⁻¹) * n := by rw [hva, hnd']
    _ = signDiagF4 k deltaF4 := by group

end Normal

end CFSG.ClassicalInvolution.ModelFacts.Levi
