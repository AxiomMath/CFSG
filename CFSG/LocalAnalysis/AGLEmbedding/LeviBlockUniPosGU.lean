module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.AutBound

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ}

theorem bar_det_mul_det_of_mem_hypUnitary {p : ℕ} (h : UnitaryFieldData p f K)
    {B : GL (HypIndex s ε) K} (hB : B ∈ hypUnitary h s ε) :
    h.bar (B : Matrix (HypIndex s ε) (HypIndex s ε) K).det *
      (B : Matrix (HypIndex s ε) (HypIndex s ε) K).det = 1 := by
  have h1 := congrArg Matrix.det (mem_hypUnitary.mp hB)
  rw [det_mul, det_mul, det_transpose,
    show ((B : Matrix (HypIndex s ε) (HypIndex s ε) K).map h.bar).det =
      h.bar (B : Matrix (HypIndex s ε) (HypIndex s ε) K).det from (RingHom.map_det h.bar _).symm]
    at h1
  refine mul_right_cancel₀ (det_hypGram_ne_zero (r := s) (ε := ε) (K := K)) ?_
  linear_combination h1

@[expose] noncomputable def guChar (h : UnitaryFieldData 2 f K) (s ε : ℕ) :
    hypUnitary h s ε →* Kˣ :=
  (powMonoidHom (2 ^ (f - 1))).comp
    (Matrix.GeneralLinearGroup.det.comp (hypUnitary h s ε).subtype)

theorem coe_guChar (h : UnitaryFieldData 2 f K) (B : hypUnitary h s ε) :
    ((guChar h s ε B : Kˣ) : K) =
      ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K).det ^ 2 ^ (f - 1) := by
  simp [guChar, Matrix.GeneralLinearGroup.val_det_apply]

theorem guChar_div_bar_mul_det (h : UnitaryFieldData 2 f K) (B : hypUnitary h s ε) :
    ((guChar h s ε B : Kˣ) : K) / h.bar (guChar h s ε B : Kˣ) *
      ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K).det = 1 := by
  set u := ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K).det with hu
  have hbu : h.bar u * u = 1 := bar_det_mul_det_of_mem_hypUnitary h B.2
  have hbar : h.bar u = u⁻¹ := eq_inv_of_mul_eq_one_left hbu
  rw [coe_guChar, ← hu, map_pow, hbar, inv_pow, div_inv_eq_mul, ← pow_add, ← two_mul,
    ← pow_succ', Nat.sub_add_cancel h.one_le, ← h.bar_apply, hbu]

@[expose] noncomputable def guDiag (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (x : Kˣ) :
    HypIndex (t + s) ε → K :=
  torusEntries h (Pi.mulSingle (⟨0, by omega⟩ : Fin (t + s)) x) 1

theorem guDiag_mul (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (x y : Kˣ) :
    guDiag (s := s) (ε := ε) h ht (x * y) = guDiag h ht x * guDiag h ht y := by
  funext a
  rcases a with i | k | i <;>
    simp [guDiag, torusEntries, Pi.mulSingle_apply] <;> split_ifs <;> simp [mul_comm]

theorem guDiag_resIdx (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (x : Kˣ) (y : HypIndex s ε) :
    guDiag h ht x (resIdx t y) = 1 := by
  have hne : ∀ i : Fin s, (Fin.natAdd t i : Fin (t + s)) ≠ ⟨0, by omega⟩ := fun i he => by
    have := congrArg Fin.val he
    simp only [Fin.natAdd, Fin.val_mk] at this
    omega
  rcases y with i | k | i
  · simp [guDiag, torusEntries, resIdx, Pi.mulSingle_eq_of_ne (hne i)]
  · simp [guDiag, torusEntries, resIdx]
  · simp [guDiag, torusEntries, resIdx, Pi.mulSingle_eq_of_ne (hne i)]

theorem guDiag_isometry (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (x : Kˣ) :
    ((diagonal (guDiag (s := s) (ε := ε) h ht x)).map h.bar)ᵀ * hypGram (t + s) ε K *
      diagonal (guDiag h ht x) = hypGram (t + s) ε K :=
  diagonal_torusEntries_isometry h _ fun k => by simp [UnitaryFieldData.norm]

theorem det_diagonal_guDiag (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (x : Kˣ) :
    (diagonal (guDiag (s := s) (ε := ε) h ht x)).det = (x : K) / h.bar x := by
  rw [guDiag, det_diagonal_torusEntries, torusRatio,
    Finset.prod_eq_single (⟨0, by omega⟩ : Fin (t + s)) (fun j _ hj => by
      simp [Pi.mulSingle_eq_of_ne hj]) (by simp)]
  simp

theorem diagonal_mul_extendMat_comm {ι κ : Type*} [DecidableEq κ] [Fintype κ] {φ : ι → κ}
    (hφ : Function.Injective φ) {d : κ → K} (hd : ∀ x, d (φ x) = 1) (B : Matrix ι ι K) :
    diagonal d * extendMat hφ B = extendMat hφ B * diagonal d := by
  ext u w
  rw [diagonal_mul, mul_diagonal]
  by_cases huw : u ∈ Set.range φ ∧ w ∈ Set.range φ
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := huw
    rw [hd, hd, one_mul, mul_one]
  · rw [extendMat_apply_of_not_mem hφ B (not_and_or.mp huw)]
    rcases eq_or_ne u w with rfl | hne
    · exact mul_comm _ _
    · rw [one_apply_ne hne, mul_zero, zero_mul]

@[expose] noncomputable def guMat (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t)
    (B : hypUnitary h s ε) : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K :=
  diagonal (guDiag h ht (guChar h s ε B)) *
    extendMat (resIdx_injective t)
      ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K)

theorem guMat_gram (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (ht : 1 ≤ t)
    (B : hypUnitary h s ε) :
    ((guMat h ht B).map h.bar)ᵀ * hypGram (t + s) ε K * guMat h ht B = hypGram (t + s) ε K := by
  rw [guMat, conjTranspose_mul_mul, guDiag_isometry, extendMat_resIdx_gram h hε t B.2]

theorem det_guMat (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (B : hypUnitary h s ε) :
    (guMat (ε := ε) h ht B).det = 1 := by
  rw [guMat, det_mul, det_diagonal_guDiag, det_extendMat, guChar_div_bar_mul_det]

theorem guMat_mul (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (B B' : hypUnitary h s ε) :
    guMat (ε := ε) h ht (B * B') = guMat h ht B * guMat h ht B' := by
  have hc := diagonal_mul_extendMat_comm (resIdx_injective (s := s) (ε := ε) t)
    (guDiag_resIdx h ht (guChar h s ε B'))
    ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K)
  have hd : ∀ d₁ d₂ : HypIndex (t + s) ε → K, diagonal (d₁ * d₂) = diagonal d₁ * diagonal d₂ :=
    fun d₁ d₂ => (diagonal_mul_diagonal d₁ d₂).symm
  rw [guMat, guMat, guMat, map_mul, guDiag_mul, hd, Subgroup.coe_mul, Units.val_mul,
    extendMat_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (guDiag h ht (guChar h s ε B'))),
    hc]
  simp only [Matrix.mul_assoc]

@[expose] noncomputable def guEmbed (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (ht : 1 ≤ t) :
    hypUnitary h s ε →* hypSU h (t + s) ε :=
  MonoidHom.mk' (fun B => mkHypSU h (guMat h ht B) (guMat_gram h hε ht B) (det_guMat h ht B))
    fun B B' => Subtype.ext (Units.ext (guMat_mul h ht B B'))

theorem coe_guEmbed (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (ht : 1 ≤ t)
    (B : hypUnitary h s ε) :
    (((guEmbed h hε ht B : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = guMat h ht B :=
  rfl

theorem guMat_apply_eq_zero (h : UnitaryFieldData 2 f K) (ht : 1 ≤ t) (B : hypUnitary h s ε)
    {c : ℕ} (hct : c ≤ t) {u w : HypIndex (t + s) ε} (hw : fullPos w < c)
    (hu : c ≤ fullPos u) : guMat h ht B u w = 0 := by
  rw [guMat, diagonal_mul, extendMat_resIdx_apply_eq_zero t _ hct hw hu, mul_zero]

theorem guEmbed_mem_flagStabilizer (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (ht : 1 ≤ t)
    {I : Set ℕ} (hI : ∀ c ∈ I, c ≤ t) (B : hypUnitary h s ε) :
    guEmbed h hε ht B ∈ flagStabilizer h (t + s) ε I := by
  refine mem_flagStabilizer.mpr fun c hc => smul_hypFlag_eq_of_apply_eq_zero h hε
    ((hI c hc).trans (Nat.le_add_right t s))
    (fun u w hw hu => guMat_apply_eq_zero h ht B (hI c hc) hw hu) fun u w hw hu => ?_
  have : ((guEmbed h hε ht B : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K)⁻¹ =
      ((guEmbed h hε ht B⁻¹ : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) := by
    rw [map_inv, Subgroup.coe_inv]
  rw [this, coe_guEmbed]
  exact guMat_apply_eq_zero h ht _ (hI c hc) hw hu

theorem eq_one_of_guEmbed_mem_hypScalars (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (ht : 1 ≤ t)
    {B : hypUnitary h s ε} (hB : guEmbed h hε ht B ∈ hypScalars h (t + s) ε)
    (htn : 2 ≤ t ∨ Nat.Coprime (2 * (t + s) + ε) (2 ^ f + 1)) : B = 1 := by
  obtain ⟨c, hcN, hcn, hc⟩ := mem_normOneScalars.mp hB
  have hM : guMat h ht B = Matrix.scalar _ (c : K) := congrArg Units.val hc
  have hc1 : c = 1 := by
    rcases htn with ht2 | hcop
    · have e := congrFun (congrFun hM (.inl ⟨1, by omega⟩)) (.inl ⟨1, by omega⟩)
      have hnr : (Sum.inl ⟨1, by omega⟩ : HypIndex (t + s) ε) ∉
          Set.range (resIdx (s := s) (ε := ε) t) := fun hm => by
        rw [mem_range_resIdx] at hm
        simp only [fullPos_inl] at hm
        omega
      rw [guMat, diagonal_mul, extendMat_apply_of_not_mem _ _ (Or.inl hnr), one_apply_eq,
        mul_one, scalar_apply, diagonal_apply_eq] at e
      have h1 : (Pi.mulSingle (⟨0, by omega⟩ : Fin (t + s)) (guChar h s ε B) : Fin (t + s) → Kˣ)
          ⟨1, by omega⟩ = 1 := Pi.mulSingle_eq_of_ne (fun he => by simp at he) _
      simp only [guDiag, torusEntries, h1, Units.val_one] at e
      exact Units.ext e.symm
    · have hq : c ^ (2 ^ f + 1) = 1 := by
        refine Units.ext ?_
        rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← h.bar_apply, mul_comm]
        exact hcN
      have := (pow_gcd_eq_one (a := c)).mpr ⟨hcn, hq⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  subst hc1
  refine Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  have e := congrFun (congrFun hM (resIdx t x)) (resIdx t y)
  rw [guMat, diagonal_mul, guDiag_resIdx, one_mul, extendMat_apply_map, Units.val_one] at e
  rw [e, scalar_apply, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [ite_eq_right ((resIdx_injective t).ne hxy)]
    simp [one_apply_ne hxy]

theorem card_hypUnitary_dvd_card_of_flag {Y : Type} [Group Y] {L P : Subgroup Y}
    (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (ρ : hypSU h (t + s) ε →* ↥L)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε) (g : hypSU h (t + s) ε)
    (hJ : ∀ y, y ∈ (P.subgroupOf L).comap ρ ↔
      ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag h (t + s) ε i) = g • hypFlag h (t + s) ε i)
    (htn : 2 ≤ t ∨ Nat.Coprime (2 * (t + s) + ε) (2 ^ f + 1)) :
    Nat.card (hypUnitary h s ε) ∣ Nat.card P := by
  have ht : 1 ≤ t := (hI.le t hI.mem).1
  obtain ⟨φ, hinj, hrange⟩ := exists_injective_of_hypFlag ρ hZ g hJ (guEmbed (s := s) h hε ht)
    (guEmbed_mem_flagStabilizer h hε ht fun c hc => (hI.le c hc).2)
    fun B hB => eq_one_of_guEmbed_mem_hypScalars h hε ht hB htn
  calc Nat.card (hypUnitary h s ε) = Nat.card φ.range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ ∣ Nat.card P := Subgroup.card_dvd_of_le hrange

theorem three_pow_seven_dvd_card_hypUnitary_one_one (h : UnitaryFieldData 2 3 K) :
    3 ^ 7 ∣ Nat.card (hypUnitary h 1 1) := by
  rw [CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.card_hypUnitary h (by norm_num)]
  have hS := (card_hypSU h (r := 1) (ε := 1) (by norm_num)).1
  have hI : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at hS
  have hS' : Nat.card (hypSU h 1 1) = 16547328 := by
    have : (Nat.card (hypSU h 1 1) : ℤ) = 16547328 := by rw [hS]; norm_num
    exact_mod_cast this
  rw [hS']
  norm_num

theorem three_pow_five_dvd_card_hypUnitary_two_zero (h : UnitaryFieldData 2 1 K) :
    3 ^ 5 ∣ Nat.card (hypUnitary h 2 0) := by
  rw [CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.card_hypUnitary h (by norm_num)]
  have hS := (card_hypSU h (r := 2) (ε := 0) (by norm_num)).1
  have hI : Finset.Icc 2 (2 * 2 + 0) = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by norm_num)] at hS
  have hS' : Nat.card (hypSU h 2 0) = 25920 := by
    have : (Nat.card (hypSU h 2 0) : ℤ) = 25920 := by rw [hS]; norm_num
    exact_mod_cast this
  rw [hS']
  norm_num

end CFSG.AGLEmbedding.LeviBlock
