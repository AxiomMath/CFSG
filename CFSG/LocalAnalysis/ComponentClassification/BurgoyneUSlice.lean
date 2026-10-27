module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd compInd_mul_apply mul_compInd_apply
  compInd_apply commute_compInd_iff signMat signMat_mul_self signMat_eq det_signMat
  commute_signMat_iff commutator_eq_self_of_isQuasisimple mul_conj_mul_inv exists_not_mem_pair
  compInd_commute_diagonal)
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def uPairSign {a b : Fin n} (hab : a ≠ b) : StatedSU n (p ^ f) K :=
  uSUmk h (signMat K {a, b}) (by rw [det_signMat, Finset.card_pair hab]; norm_num)
    (by rw [map_signMat, signMat, diagonal_transpose, ← signMat, signMat_mul_self])

theorem coe_uPairSign {a b : Fin n} (hab : a ≠ b) :
    (((uPairSign h hab : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      signMat K {a, b} := rfl

theorem uPairSign_mem {a b : Fin n} (hab : a ≠ b) : uPairSign h hab ∈ uBlock p f K {a, b} := by
  rw [mem_uBlock_iff]
  intro x y hxy
  rw [coe_uPairSign, signMat, diagonal_apply]
  by_cases hxy' : x = y
  · subst hxy'
    have hx : x ∉ ({a, b} : Finset (Fin n)) := by tauto
    simp [hx]
  · simp [hxy']

theorem commute_signMat_of_compInd (h2 : (2 : K) ≠ 0) {I : Finset (Fin n)}
    {M : Matrix (Fin n) (Fin n) K} (hM : compInd K I * M = M * compInd K I) :
    M * signMat K I = signMat K I * M :=
  ((commute_signMat_iff h2 I M).2 hM).symm

include h in
theorem nonempty_uBlock_pair_equiv [Finite K] [Fact p.Prime] [CharP K p] {a b : Fin n}
    (hab : a ≠ b) :
    Nonempty (uBlock p f K {a, b} ≃*
      SL(2, CFSG.LieType.Steinberg.fixedSubfield K p f)) := by
  have hK := h.card_eq_sq
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  have key : ∀ m, m = 2 → Nonempty (StatedSU m (p ^ f) K ≃*
      SL(2, CFSG.LieType.Steinberg.fixedSubfield K p f)) := by
    rintro m rfl
    exact ⟨((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
      (CFSG.LieType.Universal.Unitary.equivStatedSU hK 2)).symm⟩
  obtain ⟨e⟩ := key _ (Finset.card_pair hab)
  exact ⟨(uBlockEquiv h {a, b}).symm.trans e⟩

theorem commute_uPairSign (h2 : (2 : K) ≠ 0) {a b : Fin n} (hab : a ≠ b)
    {g : StatedSU n (p ^ f) K} (hg : g ∈ uBlock p f K {a, b}) :
    g * uPairSign h hab = uPairSign h hab * g := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_uPairSign]
  exact commute_signMat_of_compInd h2 (commute_compInd_of_mem_uBlock hg)

theorem uPairSign_eq_neg_one (h2 : (2 : K) ≠ 0) {a b : Fin n} (hab : a ≠ b) {F : Type}
    [Field F] (e : uBlock p f K {a, b} ≃* SL(2, F)) :
    ((e ⟨uPairSign h hab, uPairSign_mem h hab⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  set u : uBlock p f K {a, b} := ⟨uPairSign h hab, uPairSign_mem h hab⟩ with hu
  have hcen : e u ∈ center SL(2, F) := by
    rw [← Subgroup.map_center_eq e]
    refine ⟨u, mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (commute_uPairSign h h2 hab g.2)
  obtain ⟨r, hr, hre⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  rw [Fintype.card_fin] at hr
  have hfac : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exfalso
    have hu1 : u = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [← hre, sub_eq_zero.1 h1, map_one]
      simp
    have e1 := congrArg (fun x : uBlock p f K {a, b} =>
      (((x : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a) hu1
    simp only [hu, coe_uPairSign, signMat, diagonal_apply_eq, OneMemClass.coe_one,
      Units.val_one, one_apply_eq] at e1
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, ↓reduceIte] at e1
    exact h2 (by linear_combination -e1)
  · rw [← hre, eq_neg_of_add_eq_zero_left h1]
    ext i j
    by_cases hij : i = j <;> simp [hij, one_apply]

theorem commute_of_centralize (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) (hn : 1 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K)))) {a b : Fin n} (hab : a ≠ b) {A : uU h n}
    (hA : ∀ x ∈ slice (uBlock p f K {a, b}), uConjAut h hn A * x = x * uConjAut h hn A)
    {g : StatedSU n (p ^ f) K} (hg : g ∈ uBlock p f K {a, b}) :
    ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hQ := isQuasisimple_uBlock h hp2 (J := {a, b}) (by rw [Finset.card_pair hab])
    (Or.inr hq5)
  have hfix : ∀ g' ∈ uBlock p f K {a, b}, (uConjAut h hn A * uFieldAut h hn 1)
      (projH _ g') = projH _ g' := by
    intro g' hg'
    rw [map_one, mul_one]
    apply hinj
    have e := hA _ ⟨g', hg', rfl⟩
    change uConjAut h hn A * MulAut.conj (projH _ g') = MulAut.conj (projH _ g') *
      uConjAut h hn A at e
    rw [← mul_conj_mul_inv, e, mul_inv_cancel_right]
  have e := uSemilinear_eq_of_fix h hn (commutator_eq_self_of_isQuasisimple hQ) hfix hg
  rw [map_one_ringEquiv] at e
  calc ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [show ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one], Matrix.mul_one]
    _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← Matrix.mul_assoc, e]

theorem uConjAut_mul_conjProjH_mul_inv (hn : 1 ≤ n) (D : uU h n) (g : StatedSU n (p ^ f) K) :
    uConjAut h hn D * conjProjH (StatedSU n (p ^ f) K) g * (uConjAut h hn D)⁻¹ =
      conjProjH (StatedSU n (p ^ f) K) ⟨_, uConjSU_mem h D g⟩ := by
  change uConjAut h hn D * MulAut.conj (projH _ g) * (uConjAut h hn D)⁻¹ =
    MulAut.conj (projH _ _)
  rw [mul_conj_mul_inv, uConjAut_proj]

theorem conj_mem_slice (hn : 1 ≤ n) {a b : Fin n} {D : uU h n}
    (hD : compInd K {a, b} * ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {a, b})
    {x : MulAut (StatedProj (StatedSU n (p ^ f) K))} (hx : x ∈ slice (uBlock p f K {a, b})) :
    uConjAut h hn D * x * (uConjAut h hn D)⁻¹ ∈ slice (uBlock p f K {a, b}) := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [uConjAut_mul_conjProjH_mul_inv]
  refine ⟨_, conj_mem_uBlock (D := ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (Di := (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hD hg rfl, rfl⟩

theorem uConjAut_mem_normalizer_slice (hn : 1 ≤ n) {a b : Fin n} {D : uU h n}
    (hD : compInd K {a, b} * ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {a, b}) :
    uConjAut h hn D ∈ normalizer
      (slice (uBlock p f K {a, b}) : Set (MulAut (StatedProj (StatedSU n (p ^ f) K)))) := by
  have hDi : compInd K {a, b} * (((D⁻¹ : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((D⁻¹ : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {a, b} := by
    set M := ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
    set Mi := (((D⁻¹ : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMi
    have h1 : M * Mi = 1 := by
      rw [hM, hMi, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1' : Mi * M = 1 := by
      rw [hM, hMi, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc compInd K {a, b} * Mi = (Mi * M) * compInd K {a, b} * Mi := by
          rw [h1', Matrix.one_mul]
      _ = Mi * (M * compInd K {a, b}) * Mi := by simp only [Matrix.mul_assoc]
      _ = Mi * (compInd K {a, b} * M) * Mi := by rw [hD]
      _ = Mi * compInd K {a, b} := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_slice h hn hD
  · intro hx
    have := conj_mem_slice h hn hDi hx
    rw [map_inv, inv_inv] at this
    have e : (uConjAut h hn D)⁻¹ * (uConjAut h hn D * x * (uConjAut h hn D)⁻¹) *
        uConjAut h hn D = x := by group
    rwa [e] at this

theorem split_propAConclusionIn (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J)
    {Y : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (uConjAut h (by omega) (uSign h J))) :
    PropAConclusionIn B (uConjAut h (by omega) (uSign h J)) Y := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  have hcard : p ^ f = 3 ∨ 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    have : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hab : a ≠ b := fun e => hb (e ▸ ha)
  have hcore := fun {y} (hy : y ∈ oddCoreIn B (uConjAut h (by omega) (uSign h J))) =>
    split_oddCoreIn h hp2 hn hinj hB ha hb hy
  rcases hcard with h3 | h5
  ·
    exfalso
    apply hY
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨α, β, hα, hβ, rfl⟩ := hcore (hYO hy)
    have hodd := odd_orderOf_of_mem_oddCoreIn (hYO hy)
    have h4 : ∀ γ : Kˣ, h.norm (γ : K) = 1 → (γ : K) ^ 4 = 1 := by
      intro γ hγ
      rw [UnitaryFieldData.norm, h.bar_apply, h3] at hγ
      linear_combination hγ
    have hD4 : uDiagJ h J α β hα hβ ^ 4 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_uDiagJ, diagonal_pow,
        OneMemClass.coe_one, Units.val_one, ← diagonal_one]
      congr 1
      ext i
      simp only [Pi.pow_apply]
      split_ifs
      · exact h4 α hα
      · exact h4 β hβ
    have hy4 : (uConjAut h (by omega) (uDiagJ h J α β hα hβ)) ^ 4 = 1 := by
      rw [← map_pow, hD4, map_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hy4
    have h1 : orderOf (uConjAut h (by omega) (uDiagJ h J α β hα hβ)) = 1 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have h3' : orderOf (uConjAut h (by omega) (uDiagJ h J α β hα hβ)) ≠ 3 := fun e3 => by
        rw [e3] at hdvd
        norm_num at hdvd
      obtain ⟨k, hk⟩ := hodd
      omega
    exact mem_bot.2 (orderOf_eq_one_iff.1 h1)
  ·
    set F := CFSG.LieType.Steinberg.fixedSubfield K p f with hF
    have hFc : Nat.card F = p ^ f := CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq
    have h2F : (2 : F) ≠ 0 := fun e => h2 (by
      have h1 : ((1 + 1 : F) : K) = 1 + 1 := by rw [Subfield.coe_add, Subfield.coe_one]
      rw [← one_add_one_eq_two] at e ⊢
      rw [← h1, e, Subfield.coe_zero])
    have hF2 : ringChar F ≠ 2 := fun e => h2F (by
      have := ringChar.spec F 2
      exact_mod_cast (this.2 (by rw [e])))
    obtain ⟨e⟩ := nonempty_uBlock_pair_equiv h hab
    obtain ⟨k, hk⟩ := exists_not_mem_pair hn a b
    have hLZ : ∀ g ∈ uBlock p f K {a, b},
        g ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) → g = 1 :=
      fun g hg hz => eq_one_of_mem_uBlock_scalars hk hg hz
    have hdiagR : ∀ {D : uU h n}, (∀ x y, x ≠ y →
        ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0) →
        (∀ x ∈ slice (uBlock p f K {a, b}), uConjAut h (by omega) D * x =
          x * uConjAut h (by omega) D) →
        ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a =
          ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b b := by
      intro D hoff hcen
      have e1 := commute_of_centralize h hp2 h5 (by omega) hinj hab hcen
        (uRot_mem_uBlock h hab (by simp) (by simp))
      rw [coe_uRot] at e1
      exact diag_eq_of_commute_rot hab e1 (hoff a b hab)
    refine slice_propAConclusionIn hinj hB hLZ hF2 (by rw [hFc]; omega) (uPairSign_mem h hab) e
      (uPairSign_eq_neg_one h h2 hab e) (fun g hg => commute_uPairSign h h2 hab hg) ?_ ?_ hY hYO
      ?_ ?_ ?_ ?_
    ·
      intro g' hg' g hg
      have e1 := congrArg (fun x : StatedSU n (p ^ f) K =>
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg'
      simp only [Subgroup.coe_mul, Units.val_mul, coe_uPairSign] at e1
      have hc := (commute_signMat_iff h2 {a, b} _).1 e1.symm
      refine conj_mem_uBlock (D := ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (Di := (((g'⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ?_ ?_ hc hg ?_
      · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one]
      · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one]
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    ·
      apply orderOf_eq_prime
      · rw [← map_pow, pow_two, uSign_mul_self, map_one]
      · intro h1
        obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn (uSign h J)).1 h1
        have e1 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
        simp only [coe_uSign, GeneralLinearGroup.coe_scalar] at e1
        have ea := congrFun (congrFun e1 a) a
        have eb := congrFun (congrFun e1 b) b
        simp only [signMat, diagonal_apply_eq, ha, hb, ↓reduceIte, Matrix.scalar_apply] at ea eb
        exact h2 (by linear_combination eb - ea)
    ·
      exact uConjAut_mem_normalizer_slice h (by omega) (by
        rw [coe_uSign, signMat]
        exact compInd_commute_diagonal _ _)
    ·
      by_contra hall
      push Not at hall
      have e1 := hdiagR (D := uSign h J) (fun x y hxy => by
        rw [coe_uSign, signMat, diagonal_apply_ne _ hxy]) hall
      rw [coe_uSign, signMat, diagonal_apply_eq, diagonal_apply_eq] at e1
      simp only [ha, hb, ↓reduceIte] at e1
      exact h2 (by linear_combination -e1)
    ·
      intro y hy
      obtain ⟨α, β, hα, hβ, rfl⟩ := hcore hy
      exact uConjAut_mem_normalizer_slice h (by omega) (by
        rw [coe_uDiagJ]
        exact compInd_commute_diagonal _ _)
    ·
      intro y hy hcen
      obtain ⟨α, β, hα, hβ, rfl⟩ := hcore hy
      have e1 := hdiagR (D := uDiagJ h J α β hα hβ) (fun x y hxy => by
        rw [coe_uDiagJ, diagonal_apply_ne _ hxy]) hcen
      rw [coe_uDiagJ, diagonal_apply_eq, diagonal_apply_eq] at e1
      simp only [ha, hb, ↓reduceIte] at e1
      refine (uConjAut_eq_one_iff h hn _).2 ⟨α, ?_⟩
      apply Units.ext
      rw [coe_uDiagJ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      congr 1
      ext i
      split_ifs
      · rfl
      · exact (Units.ext_iff.1 (Units.ext e1)).symm

end CFSG.ComponentClassification.Burgoyne.U
