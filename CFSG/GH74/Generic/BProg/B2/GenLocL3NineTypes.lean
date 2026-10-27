module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix GenLocL3Good GenLocL3Pair GenLocL3Seven
open scoped MatrixGroups Classical

namespace GenLocL3Nine

variable {K : Type} [Field K]

@[expose] def diagSub (K : Type) [Field K] : Subgroup (MulAut (LinearFlag.projectiveSL 3 K)) where
  carrier := {y | ∃ x : GL (Fin 3) K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧
    y = LinearFlag.conjAut 3 K x}
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    exact ⟨x * x', by rw [Units.val_mul]; exact GenLocL3NFFrame.isDiag_mul' hx hx', by rw [map_mul]⟩
  one_mem' := ⟨1, by rw [Units.val_one]; exact Matrix.isDiag_one, by rw [map_one]⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, GenLocL3NFFrame.isDiag_inv_gl hx, by rw [map_inv]⟩

theorem sigma_sq_one_of_involution [Finite K] {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy2 : y * y = 1) {A : GL (Fin 3) K} {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1)
    (h : y = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε) :
    σ * σ = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [h, pow_zero, mul_one, LinearFlag.conjAut_mul_fieldAut_mul] at hy2
    exact (LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hy2).1
  · rw [h, pow_one, ← sq, LinearFlag.sq_conjAut_fieldAut_dualAut] at hy2
    exact (LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hy2).1

theorem involution_unique [Finite K] (hK : Nat.card K = 9) {σ τ : K ≃+* K} (hσ : σ ≠ 1)
    (hσσ : σ * σ = 1) (hτ : τ ≠ 1) (hττ : τ * τ = 1) : σ = τ := by
  have hK' : Nat.card K = 3 ^ 2 := by simpa using hK
  obtain ⟨-, h1⟩ := LinearFlag.even_and_eq_pow_of_involution_prime Nat.prime_three (by norm_num) hK' hσ hσσ
  obtain ⟨-, h2⟩ := LinearFlag.even_and_eq_pow_of_involution_prime Nat.prime_three (by norm_num) hK' hτ hττ
  exact RingEquiv.ext fun x => (h1 x).trans (h2 x).symm


theorem prod_eps1 (A B : GL (Fin 3) K) (σ : K ≃+* K) :
    (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K) *
        (LinearFlag.conjAut 3 K B * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K) =
      LinearFlag.conjAut 3 K (A * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose B)) * LinearFlag.fieldAut 3 K (σ * σ) := by
  have hδδ : LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have s1 := LinearFlag.fieldAut_mul_conjAut (n := 3) (K := K) σ (GeneralLinearGroup.inverseTranspose B)
  have s2 := LinearFlag.dualAut_mul_conjAut (n := 3) (K := K) B
  have s3 := LinearFlag.dualAut_mul_fieldAut (n := 3) (K := K) σ
  calc (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K) *
        (LinearFlag.conjAut 3 K B * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K)
      = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ *
          (LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K B) * LinearFlag.fieldAut 3 K σ *
          LinearFlag.dualAut 3 K := by simp only [mul_assoc]
    _ = LinearFlag.conjAut 3 K A * (LinearFlag.fieldAut 3 K σ *
          LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose B)) *
          (LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K σ) * LinearFlag.dualAut 3 K := by
        rw [s2]; simp only [mul_assoc]
    _ = LinearFlag.conjAut 3 K A * (LinearFlag.conjAut 3 K
          (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose B)) *
          LinearFlag.fieldAut 3 K σ) * (LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K) *
          LinearFlag.dualAut 3 K := by rw [s1, s3]
    _ = LinearFlag.conjAut 3 K A * LinearFlag.conjAut 3 K
          (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose B)) *
          (LinearFlag.fieldAut 3 K σ * LinearFlag.fieldAut 3 K σ) *
          (LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K) := by simp only [mul_assoc]
    _ = _ := by rw [hδδ, mul_one, ← map_mul, ← map_mul]

theorem mul_mem_diagSub_of_sameType [Finite K] (hK : Nat.card K = 9)
    {y y' : MulAut (LinearFlag.projectiveSL 3 K)} (hy : y * y = 1) (hy' : y' * y' = 1)
    {u u' : Fin 3 → Kˣ} {σ σ' : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1)
    (h : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε)
    (h' : y' = LinearFlag.conjAut 3 K (diag3 u') * LinearFlag.fieldAut 3 K σ' * LinearFlag.dualAut 3 K ^ ε)
    (hσ : σ = 1 ↔ σ' = 1) : y * y' ∈ diagSub K := by
  have hσσ : σ * σ = 1 := sigma_sq_one_of_involution hy hε h
  have hσσ' : σ' * σ' = 1 := sigma_sq_one_of_involution hy' hε h'
  have heq : σ = σ' := by
    by_cases h1 : σ = 1
    · rw [h1, (hσ.1 h1)]
    · exact involution_unique hK h1 hσσ (fun h2 => h1 (hσ.2 h2)) hσσ'
  subst heq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [h, h', pow_zero, mul_one, mul_one, LinearFlag.conjAut_mul_fieldAut_mul, hσσ, map_one, mul_one]
    refine ⟨_, ?_, rfl⟩
    rw [Units.val_mul]
    exact GenLocL3NFFrame.isDiag_mul' (isDiag_diag3 u)
      (GenLocL3NFFrame.isDiag_map_gl σ (isDiag_diag3 u'))
  · rw [h, h', pow_one, prod_eps1, hσσ, map_one, mul_one]
    refine ⟨_, ?_, rfl⟩
    rw [Units.val_mul]
    exact GenLocL3NFFrame.isDiag_mul' (isDiag_diag3 u)
      (GenLocL3NFFrame.isDiag_map_gl σ (GenLocL3NFFrame.isDiag_inverseTranspose (isDiag_diag3 u')))


section Types

theorem exists_type {y : MulAut (LinearFlag.projectiveSL 3 K)} (hy : y ∈ frameStab 3 K) :
    ∃ (t : Bool × Bool) (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε ∧
      t = (decide (σ = 1), decide (ε = 0)) := by
  classical
  obtain ⟨u, σ, ε, hε, h⟩ := exists_data hy
  exact ⟨_, u, σ, ε, hε, h, rfl⟩

@[expose] noncomputable def typ (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K)
    (y : D) : Bool × Bool :=
  Classical.choose (exists_type (hfs y.2))

theorem typ_spec (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (y : D) :
    ∃ (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      (y : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 u) *
        LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε ∧
      typ D hfs y = (decide (σ = 1), decide (ε = 0)) := by
  classical
  obtain ⟨u, σ, ε, hε, h, ht⟩ := Classical.choose_spec (exists_type (hfs y.2))
  exact ⟨u, σ, ε, hε, h, ht⟩

theorem mul_mem_diagSub_of_typ_eq [Finite K] (hK : Nat.card K = 9)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K)
    (hD : CFSG.IsElementaryAbelian 2 ↥D) {y y' : D} (h : typ D hfs y = typ D hfs y') :
    ((y * y' : D) : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K := by
  classical
  have hsq : ∀ z : D, ((z : MulAut (LinearFlag.projectiveSL 3 K))) *
      ((z : MulAut (LinearFlag.projectiveSL 3 K))) = 1 := fun z =>
    congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD z)
  obtain ⟨u, σ, ε, hε, hy, ht⟩ := typ_spec D hfs y
  obtain ⟨u', σ', ε', hε', hy', ht'⟩ := typ_spec D hfs y'
  rw [ht, ht'] at h
  simp only [Prod.mk.injEq, decide_eq_decide] at h
  have hεε : ε = ε' := by omega
  subst hεε
  exact mul_mem_diagSub_of_sameType hK (hsq y) (hsq y') hε hy hy' h.1

end Types

section Counting

variable [Finite K] (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) [Fintype ↥D]

@[expose] noncomputable def T1D : Finset ↥D :=
  (Finset.univ : Finset ↥D).filter fun z => (z : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K

omit [Finite K] in
theorem mem_T1D {z : D} : z ∈ T1D D ↔ (z : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K := by
  simp [T1D]

theorem T1D_data (hD : CFSG.IsElementaryAbelian 2 ↥D) {z : D} (hz : z ∈ T1D D) :
    ∃ (m : Fin 3) (u : Fin 3 → Kˣ), (z : MulAut (LinearFlag.projectiveSL 3 K)) =
      LinearFlag.conjAut 3 K (diag3 u) ∧ u (crd m 0) = u (crd m 1) ∧
      ∀ i i', ((u i : Kˣ) : K) * u i = (u i' : K) * u i' := by
  obtain ⟨x, hx, hzx⟩ := (mem_T1D D).1 hz
  obtain ⟨u, rfl⟩ := exists_diag3 hx
  have h1 : LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.conjAut 3 K (diag3 u) = 1 := by
    rw [← hzx]
    exact congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD z)
  have hsq := sq_equal_of_conjAut_sq u h1
  obtain ⟨m, hm⟩ := exists_block_eq hsq
  exact ⟨m, u, hzx, hm, hsq⟩

@[expose] noncomputable def blockFun (hD : CFSG.IsElementaryAbelian 2 ↥D) (z : ↥D) : Fin 3 :=
  if h : z ∈ T1D D then Classical.choose (T1D_data D hD h) else 0

theorem blockFun_spec (hD : CFSG.IsElementaryAbelian 2 ↥D) {z : D} (hz : z ∈ T1D D) :
    ∃ u : Fin 3 → Kˣ, (z : MulAut (LinearFlag.projectiveSL 3 K)) =
      LinearFlag.conjAut 3 K (diag3 u) ∧ u (crd (blockFun D hD z) 0) = u (crd (blockFun D hD z) 1) ∧
      ∀ i i', ((u i : Kˣ) : K) * u i = (u i' : K) * u i' := by
  simp only [blockFun, hz, ↓reduceDIte]
  exact Classical.choose_spec (T1D_data D hD hz)

theorem blockFun_injOn (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    Set.InjOn (blockFun D hD) ↑((T1D D).erase 1) := by
  intro z hz z' hz' hzz'
  have hz1 : z ≠ 1 := (Finset.mem_erase.1 hz).1
  have hz1' : z' ≠ 1 := (Finset.mem_erase.1 hz').1
  obtain ⟨u, hu, hm, hs⟩ := blockFun_spec D hD (Finset.mem_erase.1 hz).2
  obtain ⟨u', hu', hm', hs'⟩ := blockFun_spec D hD (Finset.mem_erase.1 hz').2
  rw [← hzz'] at hm'
  have hne : ∀ (y : D) (w : Fin 3 → Kˣ), y ≠ 1 → (y : MulAut (LinearFlag.projectiveSL 3 K)) =
      LinearFlag.conjAut 3 K (diag3 w) → LinearFlag.conjAut 3 K (diag3 w) ≠ 1 := by
    intro y w hy1 hyw h1
    apply hy1
    apply Subtype.ext
    rw [hyw, h1]; rfl
  have e := eq_of_trivial_block (blockFun D hD z) hs hs' hm hm' (hne z u hz1 hu) (hne z' u' hz1' hu')
  apply Subtype.ext
  rw [hu, hu', e]

theorem card_T1D_le (hD : CFSG.IsElementaryAbelian 2 ↥D) : (T1D D).card ≤ 4 := by
  have := Finset.card_le_card_of_injOn (blockFun D hD) (s := (T1D D).erase 1)
    (t := (Finset.univ : Finset (Fin 3))) (fun _ _ => Finset.mem_univ _) (blockFun_injOn D hD)
  rw [Finset.card_erase_of_mem (by rw [mem_T1D]; exact one_mem _)] at this
  simp at this
  have h0 : 0 < (T1D D).card := Finset.card_pos.2 ⟨1, (mem_T1D D).2 (one_mem _)⟩
  omega

theorem exists_T1_block (hD : CFSG.IsElementaryAbelian 2 ↥D) (hcard : (T1D D).card = 4) (m : Fin 3) :
    ∃ z ∈ (T1D D).erase 1, blockFun D hD z = m := by
  have himg : ((T1D D).erase 1).image (blockFun D hD) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (blockFun_injOn D hD),
      Finset.card_erase_of_mem (by rw [mem_T1D]; exact one_mem _), hcard]
    simp
  have : m ∈ ((T1D D).erase 1).image (blockFun D hD) := by rw [himg]; exact Finset.mem_univ m
  obtain ⟨z, hz, hzm⟩ := Finset.mem_image.1 this
  exact ⟨z, hz, hzm⟩

theorem card_le_mul_T1D (hK : Nat.card K = 9) (hfs : D ≤ frameStab 3 K)
    (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    (Finset.univ : Finset ↥D).card ≤ (T1D D).card * ((Finset.univ : Finset ↥D).image (typ D hfs)).card := by
  refine Finset.card_le_mul_card_image _ _ fun t ht => ?_
  obtain ⟨y0, -, hy0⟩ := Finset.mem_image.1 ht
  refine Finset.card_le_card_of_injOn (fun y => y0 * y) (fun y hy => ?_) (fun y _ y' _ h => mul_left_cancel h)
  rw [Finset.mem_coe, Finset.mem_filter] at hy
  rw [Finset.mem_coe, mem_T1D]
  exact mul_mem_diagSub_of_typ_eq hK D hfs hD (hy0.trans hy.2.symm)

end Counting


end GenLocL3Nine

end CFSG.GH74.Generic.BProg.B2
