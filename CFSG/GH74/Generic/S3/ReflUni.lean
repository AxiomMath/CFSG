module

public import CFSG.GH74.Generic.S3.Rank5
public import CFSG.GH74.GLS.LU.Ident

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg Subgroup
open scoped MatrixGroups

section Uni
variable {K : Type} [Field K] (σ : K ≃+* K)

theorem diagGL_mem_SUid (a b : Kˣ) (hab : (a : K) * b = 1) (ha : σ a * a = 1) (hb : σ b * b = 1) :
    (diagGL ![a, b] : GL (Fin 2) K) ∈ SUid σ 2 := by
  refine ⟨?_, ?_⟩
  · rw [coe_diagGL, Matrix.det_diagonal]
    simpa [Fin.prod_univ_two] using hab
  · rw [coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb]


@[expose] noncomputable def sU (ι : Kˣ) (hι : (ι : K) ^ 2 = -1) (hσ : σ ι * ι = 1) : SUid σ 2 :=
  ⟨diagGL ![ι, -ι], diagGL_mem_SUid σ ι (-ι) (by
      simp only [Units.val_neg]; linear_combination (-1 : K) * hι)
    hσ (by simp only [Units.val_neg, map_neg]; linear_combination hσ)⟩

@[expose] noncomputable def cU : SUid σ 2 :=
  ⟨diagGL ![-1, -1], diagGL_mem_SUid σ (-1) (-1) (by simp) (by simp) (by simp)⟩

theorem cU_mul_self : cU σ * cU σ = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, cU, coe_diagGL, Subgroup.coe_one, Units.val_one,
    Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blkU_sq : embSUid σ 2 (cU σ) * embSUid σ 2 (cU σ) = 1 := by
  rw [← map_mul, cU_mul_self, map_one]

theorem blkU_conj (ι : Kˣ) (hι : (ι : K) ^ 2 = -1) (hσ : σ ι * ι = 1) (A : SUid σ 2) :
    embSUid σ 2 (cU σ) * embSUid σ 0 A * (embSUid σ 2 (cU σ))⁻¹ =
      embSUid σ 0 (sU σ ι hι hσ * A * (sU σ ι hι hσ)⁻¹) := by
  rw [inv_eq_of_mul_eq_one_right (blkU_sq σ)]
  apply Subtype.ext
  apply Units.ext
  have hι0 : (ι : K) ≠ 0 := ι.ne_zero
  have hinv : ((ι⁻¹ : Kˣ) : K) = -(ι : K) := by
    have : (ι : K) * (-(ι : K)) = 1 := by linear_combination (-1 : K) * hι
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right this
  have hinv2 : (((-ι)⁻¹ : Kˣ) : K) = (ι : K) := by
    rw [Units.val_inv_eq_inv_val, Units.val_neg, inv_neg]
    have h1 : ((ι : K))⁻¹ = -(ι : K) := by rw [← Units.val_inv_eq_inv_val]; exact hinv
    rw [h1, neg_neg]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, Subgroup.coe_inv, sU, cU, coe_diagGL,
    coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp


theorem cU_central (B : SUid σ 2) : cU σ * B = B * cU σ := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, cU, coe_diagGL]
  have : (Matrix.diagonal fun i => (((![-1, -1] : Fin 2 → Kˣ) i : Kˣ) : K)) =
      (-1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [this]
  simp

theorem cU_ne_one (h2 : (2 : K) ≠ 0) : cU σ ≠ 1 := by
  intro h
  have := congrArg (fun B : SUid σ 2 => ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [cU, coe_diagGL] at this
  exact h2 (by linear_combination (-1 : K) * this)

theorem sU_mul_self (ι : Kˣ) (hι : (ι : K) ^ 2 = -1) (hσ : σ ι * ι = 1) :
    sU σ ι hι hσ * sU σ ι hι hσ = cU σ := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, sU, cU, coe_diagGL, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination hι

end Uni

theorem img_eq_of_central {G : Type} [Group G] {F₂ F : Type} [Field F₂] [Field F]
    (σ : F₂ ≃+* F₂) (hchar : ringChar F ≠ 2) {Y' : Subgroup G} (e : SL(2, F) ≃* Y') {w : G}
    (hw : GLS.LU.IsCentralInvolutionIn w Y') (ι'' : SUid σ 2 →* G) (hr : ι''.range = Y')
    (hinj : Function.Injective ι'') (a : SUid σ 2) (hac : ∀ B, a * B = B * a) (ha1 : a ≠ 1) :
    ι'' a = w := by
  have hw1 : w ≠ 1 := by
    intro h
    have := hw.2.1
    rw [h, orderOf_one] at this
    omega
  have hmem : ι'' a ∈ Y' := hr ▸ ⟨a, rfl⟩
  have hcent : ∀ b ∈ Y', ι'' a * b = b * ι'' a := by
    intro b hb
    rw [← hr] at hb
    obtain ⟨B, rfl⟩ := hb
    rw [← map_mul, ← map_mul, hac B]
  rcases (sl2_img_eq_z hchar e hw.1 hw.2.2 hw1).1 (ι'' a) hmem hcent with h | h
  · exact absurd (hinj (h.trans (map_one ι'').symm)) ha1
  · exact h

open CFSG.ClassicalInvolution.Phan CFSG.GH74.L5U5 in
theorem exists_refl_conj_uni {G : Type} [Group G] {F₂ F : Type} [Field F₂] [Finite F₂] [Field F]
    [Finite F] {z u : G} {Y : Fin 3 → Subgroup G} (p f : ℕ) [Fact p.Prime] [CharP F₂ p]
    (h : GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F z u Y)
    (hp2 : p ≠ 2) (hF₂ : Nat.card F₂ = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 3) :
    ∃ j ∈ Y 2, j * j = z ∧ ∀ g ∈ Y 2, u * g * u⁻¹ = j * g * j⁻¹ := by
  have hq2 : p ^ f ≠ 2 := by omega
  have hoddq : Odd (p ^ f) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hodd2 : Odd (Nat.card F₂) := by rw [hF₂]; exact hoddq.pow
  have h2 : (2 : F₂) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd2
  have hoddF : Odd (Nat.card F) := by rw [hF]; exact hoddq
  have hchar : ringChar F ≠ 2 := by
    intro hc
    have h2F : (2 : F) ≠ 0 :=
      CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hoddF
    apply h2F
    have := ringChar.of_eq hc
    simpa using CharP.cast_eq_zero F 2
  have h4 : 4 ∣ Nat.card F₂ - 1 := by
    rw [hF₂]
    have : (p ^ f) ^ 2 % 4 = 1 := by rw [Nat.pow_mod, hq4]
    omega
  obtain ⟨ι, hιord⟩ := exists_units_orderOf (F := F₂) (d := 4) h4
  have hι4 : ι ^ 4 = 1 := hιord ▸ pow_orderOf_eq_one ι
  have hι2' : ι ^ 2 ≠ 1 := by
    intro h'
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hιord] at this
    omega
  have hι : (ι : F₂) ^ 2 = -1 := by
    have h1 : ((ι : F₂) ^ 2) * ((ι : F₂) ^ 2) = 1 := by
      rw [← pow_add]
      have := congrArg Units.val hι4
      simpa using this
    rcases mul_self_eq_one_iff.1 h1 with h' | h'
    · exfalso
      apply hι2'
      apply Units.ext
      simpa using h'
    · exact h'
  have hιq : (ι : F₂) ^ (p ^ f) = -(ι : F₂) := by
    obtain ⟨t, ht⟩ : ∃ t, p ^ f = 2 * (2 * t + 1) + 1 := ⟨(p ^ f) / 4, by omega⟩
    rw [ht, pow_succ, pow_mul, hι]
    have : Odd (2 * t + 1) := odd_two_mul_add_one t
    rw [this.neg_one_pow]
    ring
  have hσ : unitaryInvolution F₂ p f ι * ι = 1 := by
    rw [unitaryInvolution_apply, hιq]
    linear_combination (-1 : F₂) * hι
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs hF₂ hF hp2 hq
  obtain ⟨hiso, hz0, hz2, hu1, -⟩ := h
  set N : Subgroup G := ⨆ i, Y i with hN
  have hYN : ∀ i, Y i ≤ N := fun i => le_iSup Y i
  have hgen : ⨆ i, (Y i).subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hYN _)]
    exact hN.symm
  have hstd : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair F₂ p f W ((Y i).subgroupOf N) ((Y j).subgroupOf N) :=
    fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf N, unitaryBlockStandardPair_subgroupOf hF₂ hq2 hW N (hYN i) (hYN j)⟩
  have hW : WeakPhanA F₂ p f 3 (fun i => (Y i).subgroupOf N)
      (fun i j => (Y i).subgroupOf N ⊔ (Y j).subgroupOf N) := by
    refine ⟨?_, fun _ _ _ => rfl, ?_, ?_, hgen⟩
    · intro i
      by_cases h : (i : ℕ) + 1 < 3
      · obtain ⟨W, hW⟩ := hstd i ⟨i + 1, h⟩ rfl
        exact (nonempty_mulEquiv_of_standardPair hF₂ hW).1
      · have hi : 0 < (i : ℕ) := by have := i.2; omega
        obtain ⟨W, hW⟩ := hstd ⟨(i : ℕ) - 1, by omega⟩ i (by simp only; omega)
        exact (nonempty_mulEquiv_of_standardPair hF₂ hW).2
    · intro i j hij x hx y hy
      exact Subtype.ext (hcomm i j hij x hx y hy)
    · intro i j hj
      obtain ⟨W, hW⟩ := hstd i j hj
      rwa [unitaryBlockStandardPair_eq_sup hF₂ hq2 hW] at hW
  obtain ⟨Fam, hFι, hFinj, -⟩ := coherent_family hF₂ (by norm_num : 2 ≤ 3) hW
  have hrange : ∀ i, (N.subtype.comp (Fam.ι i)).range = Y i := by
    intro i
    rw [MonoidHom.range_comp, hFι i, Subgroup.subgroupOf_map_subtype, inf_of_le_left (hYN i)]
  have hinj : ∀ i, Function.Injective (N.subtype.comp (Fam.ι i)) := fun i =>
    N.subtype_injective.comp (hFinj i)
  obtain ⟨e1⟩ := hiso 1
  obtain ⟨e2⟩ := hiso 2
  have hu : u = N.subtype (Fam.ι 1 (cU (unitaryInvolution F₂ p f))) :=
    (img_eq_of_central (unitaryInvolution F₂ p f) hchar e1 hu1 (N.subtype.comp (Fam.ι 1))
      (hrange 1) (hinj 1) _ (cU_central _) (cU_ne_one _ h2)).symm
  have hjj : N.subtype (Fam.ι 2 (sU (unitaryInvolution F₂ p f) ι hι hσ)) *
      N.subtype (Fam.ι 2 (sU (unitaryInvolution F₂ p f) ι hι hσ)) = z := by
    rw [← map_mul, ← map_mul, sU_mul_self]
    exact img_eq_of_central (unitaryInvolution F₂ p f) hchar e2 hz2 (N.subtype.comp (Fam.ι 2))
      (hrange 2) (hinj 2) _ (cU_central _) (cU_ne_one _ h2)
  have hθ1 := Fam.left 1 (by norm_num)
  have hθ2 := Fam.right 1 (by norm_num)
  have hθ1' : ∀ c, Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 2 c) = Fam.ι 1 c := fun c =>
    DFunLike.congr_fun hθ1 c
  have hθ2' : ∀ A, Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 0 A) = Fam.ι 2 A := fun A =>
    DFunLike.congr_fun hθ2 A
  refine ⟨N.subtype (Fam.ι 2 (sU (unitaryInvolution F₂ p f) ι hι hσ)), ?_, hjj, ?_⟩
  · rw [← hrange 2]
    exact ⟨_, rfl⟩
  · intro g hg
    rw [← hrange 2] at hg
    obtain ⟨A, rfl⟩ := hg
    change u * N.subtype (Fam.ι 2 A) * u⁻¹ = _ * N.subtype (Fam.ι 2 A) * _⁻¹
    calc u * N.subtype (Fam.ι 2 A) * u⁻¹
        = N.subtype (Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 2 (cU (unitaryInvolution F₂ p f)) *
            embSUid (unitaryInvolution F₂ p f) 0 A *
            (embSUid (unitaryInvolution F₂ p f) 2 (cU (unitaryInvolution F₂ p f)))⁻¹)) := by
          rw [hu, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hθ1', hθ2']
      _ = N.subtype (Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 0
            (sU (unitaryInvolution F₂ p f) ι hι hσ * A *
              (sU (unitaryInvolution F₂ p f) ι hι hσ)⁻¹))) := by
          rw [blkU_conj _ ι hι hσ A]
      _ = N.subtype (Fam.ι 2 (sU (unitaryInvolution F₂ p f) ι hι hσ * A *
            (sU (unitaryInvolution F₂ p f) ι hι hσ)⁻¹)) := by rw [hθ2']
      _ = _ := by rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

end CFSG.GH74.Generic.S3
