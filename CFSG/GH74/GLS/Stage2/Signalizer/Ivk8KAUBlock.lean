module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSplit

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.PSL (compInd compInd_mul_apply mul_compInd_apply
  compInd_apply commute_compInd_iff compInd_compl signMat signMat_mul_self signMat_eq
  commute_signMat_iff)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

section Small

include h in
theorem kaUS_uBlock_eq_bot {I : Finset (Fin n)} (hI : I.card ≤ 1) : uBlock p f K I = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' := mem_uBlock_iff.1 hg
  set M : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hoff : ∀ i j : Fin n, i ≠ j → M i j = 0 := by
    intro i j hij
    have hnot : i ∉ I ∨ j ∉ I := by
      by_contra hcon
      push Not at hcon
      exact hij (Finset.card_le_one.1 hI i hcon.1 j hcon.2)
    rw [hg' i j hnot]
    simp [hij]
  have hdiag : M = diagonal fun k => M k k := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      exact hoff i j hij
  have hdet : M.det = 1 := ((mem_unitarySU_iff h).1 g.2).1
  have hprod : ∏ k, M k k = 1 := by
    rw [← det_diagonal, ← hdiag]
    exact hdet
  have hone : ∀ k, k ∉ I → M k k = 1 := fun k hk => by
    rw [hg' k k (Or.inl hk)]
    simp
  have hall : ∀ k, M k k = 1 := by
    intro k
    by_cases hk : k ∈ I
    · rw [← hprod]
      symm
      refine Finset.prod_eq_single k (fun j _ hjk => hone j fun hj => hjk ?_) fun hk' =>
        absurd (Finset.mem_univ k) hk'
      exact Finset.card_le_one.1 hI j hj k hk
    · exact hone k hk
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Subgroup.coe_one, Units.val_one, one_apply_eq]
    exact hall i
  · rw [Subgroup.coe_one, Units.val_one, one_apply_ne hij]
    exact hoff i j hij

end Small

section Swap

theorem kaUS_conj_mem_uBlock_swap {I I' : Finset (Fin n)} {D Di : Matrix (Fin n) (Fin n) K}
    (hDD : D * Di = 1) (hDiD : Di * D = 1) (hD : compInd K I * D = D * compInd K I')
    {g g' : StatedSU n (p ^ f) K} (hg : g ∈ uBlock p f K I')
    (hg' : ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      D * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Di) : g' ∈ uBlock p f K I := by
  obtain ⟨hg1, hg2⟩ := hg
  have hDiP : Di * compInd K I = compInd K I' * Di := by
    calc Di * compInd K I = Di * compInd K I * (D * Di) := by rw [hDD, Matrix.mul_one]
      _ = Di * (compInd K I * D) * Di := by simp only [Matrix.mul_assoc]
      _ = Di * (D * compInd K I') * Di := by rw [hD]
      _ = (Di * D) * compInd K I' * Di := by simp only [Matrix.mul_assoc]
      _ = compInd K I' * Di := by rw [hDiD, Matrix.one_mul]
  have hPD : D * compInd K I' * Di = compInd K I := by
    rw [← hD, Matrix.mul_assoc, hDD, Matrix.mul_one]
  change compInd K I * ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = compInd K I ∧
    ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K I = compInd K I
  rw [hg']
  refine ⟨?_, ?_⟩
  · calc compInd K I * (D * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Di) =
        (compInd K I * D) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Di := by
          simp only [Matrix.mul_assoc]
      _ = D * (compInd K I' * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * Di := by
          rw [hD]
          simp only [Matrix.mul_assoc]
      _ = D * compInd K I' * Di := by rw [hg1, Matrix.mul_assoc]
      _ = compInd K I := hPD
  · calc (D * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Di) * compInd K I =
        D * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Di * compInd K I)) := by
          simp only [Matrix.mul_assoc]
      _ = D * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K I') * Di := by
          rw [hDiP]
          simp only [Matrix.mul_assoc]
      _ = D * compInd K I' * Di := by rw [hg2]
      _ = compInd K I := hPD

end Swap

section Sign

theorem kaUS_eq_zero_of_eq_neg (h2 : (2 : K) ≠ 0) {x : K} (hx : x = -x) : x = 0 := by
  have : (2 : K) * x = 0 := by linear_combination hx
  exact (mul_eq_zero.1 this).resolve_left h2

theorem kaUS_coe_uSign_inv (J : Finset (Fin n)) :
    ((((uSign h J : uU h n) : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      signMat K J := by
  have hSS : signMat K J * signMat K J = 1 := signMat_mul_self J
  rw [← Matrix.mul_one ((((uSign h J : uU h n) : GL (Fin n) K)⁻¹ : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K), ← hSS, ← Matrix.mul_assoc, ← coe_uSign h J, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem kaUS_sign_cases (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) (J : Finset (Fin n))
    (g : StatedSU n (p ^ f) K)
    (hg : projH (StatedSU n (p ^ f) K) (uLift h (uSign h J) 1 g) =
      projH (StatedSU n (p ^ f) K) g) :
    compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J ∨
      compInd K Jᶜ * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J := by
  have hz := projH_eq_projH_iff.1 hg
  rw [mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  set M : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  set S : Matrix (Fin n) (Fin n) K := signMat K J with hS
  have hSS : S * S = 1 := signMat_mul_self J
  have hgu : (g : GL (Fin n) K) =
      ((uLift h (uSign h J) 1 g : StatedSU n (p ^ f) K) : GL (Fin n) K) *
        GeneralLinearGroup.scalar (Fin n) c := by
    have h1 : ((uLift h (uSign h J) 1 g : StatedSU n (p ^ f) K) : GL (Fin n) K)⁻¹ *
        (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := hc.symm
    rw [← h1]
    group
  have h2' := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hgu
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h2'
  rw [coe_uLift, coe_uSign, kaUS_coe_uSign_inv h, map_one_ringEquiv] at h2'
  have hMc : M = (c : K) • (S * M * S) := by
    calc M = S * M * S * Matrix.scalar (Fin n) (c : K) := h2'
      _ = (c : K) • (S * M * S) := by
          rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hSMS : S * M * S = (c : K) • M := by
    calc S * M * S = S * ((c : K) • (S * M * S)) * S := by rw [← hMc]
      _ = (c : K) • ((S * S) * M * (S * S)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = (c : K) • M := by rw [hSS, Matrix.one_mul, Matrix.mul_one]
  have hcc : (c : K) * (c : K) = 1 := by
    have e1 : M = ((c : K) * (c : K)) • M := by
      calc M = (c : K) • (S * M * S) := hMc
        _ = (c : K) • ((c : K) • M) := by rw [hSMS]
        _ = ((c : K) * (c : K)) • M := by rw [smul_smul]
    have hMi : M * (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 := by
      rw [hM, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one]
    have e2 : (1 : Matrix (Fin n) (Fin n) K) = ((c : K) * (c : K)) • 1 := by
      calc (1 : Matrix (Fin n) (Fin n) K) =
          M * (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
            hMi.symm
        _ = (((c : K) * (c : K)) • M) *
            (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [← e1]
        _ = ((c : K) * (c : K)) • (M *
            (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            rw [Matrix.smul_mul]
        _ = ((c : K) * (c : K)) • 1 := by rw [hMi]
    have := congrFun (congrFun e2 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this.symm
  rcases mul_self_eq_one_iff.1 hcc with hc1 | hc1
  · left
    have e : S * M = M * S := by
      calc S * M = S * M * (S * S) := by rw [hSS, Matrix.mul_one]
        _ = (S * M * S) * S := by simp only [Matrix.mul_assoc]
        _ = M * S := by rw [hSMS, hc1, one_smul]
    exact (commute_signMat_iff h2 J M).1 e
  · right
    have hent : ∀ i j, ((if i ∈ J then (-1 : K) else 1) * M i j) *
        (if j ∈ J then (-1 : K) else 1) = (c : K) * M i j := by
      intro i j
      have := congrFun (congrFun hSMS i) j
      simpa [hS, signMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply] using this
    have hM0 : ∀ i j, (i ∈ J ↔ j ∈ J) → M i j = 0 := by
      intro i j hij
      have e := hent i j
      rw [hc1] at e
      by_cases hi : i ∈ J
      · have hj := hij.1 hi
        simp only [hi, hj, ↓reduceIte] at e
        exact kaUS_eq_zero_of_eq_neg h2 (by linear_combination e)
      · have hj : j ∉ J := fun hj => hi (hij.2 hj)
        simp only [hi, hj, ↓reduceIte] at e
        exact kaUS_eq_zero_of_eq_neg h2 (by linear_combination e)
    ext i j
    rw [compInd_mul_apply, mul_compInd_apply]
    by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
    · have e0 := hM0 i j (iff_of_true hi hj)
      simp [hi, hj, e0]
    · simp [hi, hj]
    · simp [hi, hj]
    · have e0 := hM0 i j (iff_of_false hi hj)
      simp [hi, hj, e0]

end Sign

section Normalizer

theorem kaUS_mul_inv_coe (x : StatedSU n (p ^ f) K) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]

theorem kaUS_inv_mul_coe (x : StatedSU n (p ^ f) K) :
    (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]

theorem kaUS_coe_conj (x g : StatedSU n (p ^ f) K) :
    (((x * g * x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]

theorem kaUS_uLift_eq_of_mem (h2 : (2 : K) ≠ 0) (J : Finset (Fin n)) {I : Finset (Fin n)}
    (hI : I = J ∨ I = Jᶜ) {g : StatedSU n (p ^ f) K} (hg : g ∈ uBlock p f K I) :
    uLift h (uSign h J) 1 g = g :=
  (uLift_sign_eq_iff h h2 J g).2 (commute_compInd_of_or' hI (commute_compInd_of_mem_uBlock hg))

theorem kaUS_conj_mem_of_fix (h2 : (2 : K) ≠ 0) (J : Finset (Fin n)) {I : Finset (Fin n)}
    (hI : I = J ∨ I = Jᶜ) {x g : StatedSU n (p ^ f) K} (hx : uLift h (uSign h J) 1 x = x)
    (hg : g ∈ uBlock p f K I) : x * g * x⁻¹ ∈ uBlock p f K I :=
  conj_mem_uBlock (kaUS_mul_inv_coe x) (kaUS_inv_mul_coe x)
    (commute_compInd_of_or hI ((uLift_sign_eq_iff h h2 J x).1 hx)) hg (kaUS_coe_conj x g)

theorem kaUS_normalizes (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) (J : Finset (Fin n))
    {x : StatedSU n (p ^ f) K}
    (hx : projH (StatedSU n (p ^ f) K) (uLift h (uSign h J) 1 x) =
      projH (StatedSU n (p ^ f) K) x) {g : StatedSU n (p ^ f) K}
    (hg : g ∈ uBlock p f K J ⊔ uBlock p f K Jᶜ) :
    x * g * x⁻¹ ∈ uBlock p f K J ⊔ uBlock p f K Jᶜ := by
  have hcases : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → ∀ {g : StatedSU n (p ^ f) K},
      g ∈ uBlock p f K I → x * g * x⁻¹ ∈ uBlock p f K J ⊔ uBlock p f K Jᶜ := by
    intro I hI g hg
    rcases kaUS_sign_cases h h2 hn J x hx with hc | hc
    · have hxI := conj_mem_uBlock (kaUS_mul_inv_coe x) (kaUS_inv_mul_coe x)
        (commute_compInd_of_or hI hc) hg (kaUS_coe_conj x g)
      rcases hI with hI | hI
      · rw [hI] at hxI
        exact Subgroup.mem_sup_left hxI
      · rw [hI] at hxI
        exact Subgroup.mem_sup_right hxI
    · rcases hI with hI | hI
      · rw [hI] at hg
        exact Subgroup.mem_sup_right (kaUS_conj_mem_uBlock_swap (I := Jᶜ) (I' := J)
          (kaUS_mul_inv_coe x) (kaUS_inv_mul_coe x) hc hg (kaUS_coe_conj x g))
      · rw [hI] at hg
        have hc' : compInd K J * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K Jᶜ := by
          rw [compInd_compl] at hc ⊢
          rw [Matrix.sub_mul, Matrix.one_mul] at hc
          rw [Matrix.mul_sub, Matrix.mul_one, ← hc]
          abel
        exact Subgroup.mem_sup_left (kaUS_conj_mem_uBlock_swap (I := J) (I' := Jᶜ)
          (kaUS_mul_inv_coe x) (kaUS_inv_mul_coe x) hc' hg (kaUS_coe_conj x g))
  have hle : uBlock p f K J ⊔ uBlock p f K Jᶜ ≤
      (uBlock p f K J ⊔ uBlock p f K Jᶜ).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun g hg => by simpa [MulAut.conj_apply] using hcases (Or.inl rfl) hg)
      (fun g hg => by simpa [MulAut.conj_apply] using hcases (Or.inr rfl) hg)
  simpa [MulAut.conj_apply] using hle hg

end Normalizer

section Transvection

theorem kaUS_mem_uBlock_of_transvection {I : Finset (Fin n)} {v : Fin n → K}
    (hvI : ∀ x, x ∉ I → v x = 0) {g : StatedSU n (p ^ f) K} {c η : K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + c • (η • vecMulVec v (fun k => h.bar (v k)))) : g ∈ uBlock p f K I := by
  rw [mem_uBlock_iff]
  intro x z hxz
  rw [hg, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, vecMulVec_apply]
  rcases hxz with hx | hz
  · rw [hvI x hx]
    simp [one_apply]
  · rw [hvI z hz]
    simp [one_apply]

include h in
theorem kaUS_exists_isotropic {I : Finset (Fin n)} (hI : 2 ≤ I.card) :
    ∃ (v : Fin n → K) (η : K) (i : Fin n), (∀ x, x ∉ I → v x = 0) ∧
      (fun k => h.bar (v k)) ⬝ᵥ v = 0 ∧ h.bar η = -η ∧
      (η • vecMulVec v (fun k => h.bar (v k))) i i ≠ 0 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hI
  obtain ⟨μ, hμ⟩ := exists_norm_neg_one h
  obtain ⟨η, hη0, hη⟩ := exists_skew h
  set v : Fin n → K := Pi.single i 1 + Pi.single j μ with hv
  have hvI : ∀ x, x ∉ I → v x = 0 := by
    intro x hx
    have hxi : x ≠ i := fun e => hx (e ▸ hi)
    have hxj : x ≠ j := fun e => hx (e ▸ hj)
    simp [hv, hxi, hxj]
  have hiso : (fun k => h.bar (v k)) ⬝ᵥ v = 0 := by
    rw [dotProduct, Finset.sum_eq_add i j hij (fun c _ hc => by
      simp [hv, hc.1, hc.2]) (by simp) (by simp)]
    simp only [hv, Pi.add_apply, Pi.single_apply, Ne.symm hij, hij, ↓reduceIte, add_zero,
      zero_add, map_one, mul_one]
    rw [mul_comm, ← UnitaryFieldData.norm, hμ]
    ring
  refine ⟨v, η, i, hvI, hiso, hη, ?_⟩
  simp only [Matrix.smul_apply, vecMulVec_apply, hv, Pi.add_apply, Pi.single_apply, hij,
    ↓reduceIte, add_zero, map_one, mul_one, smul_eq_mul]
  exact hη0

end Transvection

section Torus

@[expose] def kaUNormOne : Subgroup Kˣ where
  carrier := {u | h.norm (u : K) = 1}
  mul_mem' := fun {a b} ha hb => by
    have ha' : h.norm (a : K) = 1 := ha
    have hb' : h.norm (b : K) = 1 := hb
    show h.norm ((a * b : Kˣ) : K) = 1
    rw [Units.val_mul, norm_mul_eq h, ha', hb', one_mul]
  one_mem' := by
    show h.norm ((1 : Kˣ) : K) = 1
    simp [UnitaryFieldData.norm]
  inv_mem' := fun {a} ha => by
    have ha' : h.norm (a : K) = 1 := ha
    show h.norm ((a⁻¹ : Kˣ) : K) = 1
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, ha', inv_one]

theorem mem_kaUNormOne {u : Kˣ} : u ∈ kaUNormOne h ↔ h.norm (u : K) = 1 := Iff.rfl

@[expose] def kaUTor (J : Finset (Fin n)) : ↥(kaUNormOne h) →* uU h n :=
  MonoidHom.mk' (fun u => uDiagJ h J (u : Kˣ) 1 ((mem_kaUNormOne h).1 u.2)
    (by simp [UnitaryFieldData.norm])) (by
    intro u v
    apply Subtype.ext
    apply Units.ext
    change (diagonal fun i => if i ∈ J then (((u * v : ↥(kaUNormOne h)) : Kˣ) : K) else
        ((1 : Kˣ) : K)) = (diagonal fun i => if i ∈ J then ((u : Kˣ) : K) else ((1 : Kˣ) : K)) *
        (diagonal fun i => if i ∈ J then ((v : Kˣ) : K) else ((1 : Kˣ) : K))
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp)

theorem coe_kaUTor (J : Finset (Fin n)) (u : ↥(kaUNormOne h)) :
    (((kaUTor h J u : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => if i ∈ J then ((u : Kˣ) : K) else ((1 : Kˣ) : K) := rfl

theorem kaUS_conj_diag_eq (hn : 3 ≤ n) (J : Finset (Fin n)) (a d : Kˣ) (ha : h.norm (a : K) = 1)
    (hd : h.norm (d : K) = 1) :
    ∃ u : ↥(kaUNormOne h), uConjAut h (by omega) (uDiagJ h J a d ha hd) =
      uConjAut h (by omega) (kaUTor h J u) := by
  have hu : a * d⁻¹ ∈ kaUNormOne h := by
    rw [mem_kaUNormOne, Units.val_mul, norm_mul_eq h, Units.val_inv_eq_inv_val, norm_inv_eq h, ha,
      hd, inv_one, mul_one]
  refine ⟨⟨a * d⁻¹, hu⟩, ?_⟩
  have hdecomp : uDiagJ h J a d ha hd = kaUTor h J ⟨a * d⁻¹, hu⟩ * uDiagJ h J d d hd hd := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_uDiagJ, Subgroup.coe_mul, Units.val_mul, coe_kaUTor, coe_uDiagJ,
      diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  have hscal : uConjAut h (by omega) (uDiagJ h J d d hd hd) = 1 := by
    rw [uConjAut_eq_one_iff h hn]
    refine ⟨d, Units.ext ?_⟩
    rw [coe_uDiagJ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    ext i
    simp
  rw [hdecomp, map_mul, hscal, mul_one]

end Torus

section Big

theorem kaUS_exists_big (hn : 3 ≤ n) (J : Finset (Fin n)) :
    ∃ I : Finset (Fin n), (I = J ∨ I = Jᶜ) ∧ 2 ≤ I.card := by
  have hsum : J.card + Jᶜ.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ J
    rw [Fintype.card_fin] at this
    omega
  by_cases hJ : 2 ≤ J.card
  · exact ⟨J, Or.inl rfl, hJ⟩
  · exact ⟨Jᶜ, Or.inr rfl, by omega⟩

include h in
theorem kaUS_block_quasisimple (hp2 : p ≠ 2) (J : Finset (Fin n))
    (h5 : J.card = 2 ∨ J.card + 2 = n → 5 ≤ p ^ f) {I : Finset (Fin n)} (hI : I = J ∨ I = Jᶜ)
    (h2I : 2 ≤ I.card) : IsQuasisimple (uBlock p f K I) := by
  refine isQuasisimple_uBlock h hp2 h2I ?_
  by_cases h3 : 3 ≤ I.card
  · exact Or.inl h3
  · right
    apply h5
    have hc : I.card = 2 := by omega
    rcases hI with hI | hI
    · left
      rw [← hI]
      exact hc
    · right
      rw [hI, Finset.card_compl, Fintype.card_fin] at hc
      have := Finset.card_le_univ J
      rw [Fintype.card_fin] at this
      omega

include h in
theorem kaUS_eq_uDiagJ (hn : 3 ≤ n) {J : Finset (Fin n)} (hJ : J.Nonempty)
    (hJc : J ≠ Finset.univ) (E : uU h n)
    (hcomm : ∀ I : Finset (Fin n), (I = J ∨ I = Jᶜ) → 2 ≤ I.card → ∀ g ∈ uBlock p f K I,
      ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ (a d : Kˣ) (ha : h.norm (a : K) = 1) (hd : h.norm (d : K) = 1),
      E = uDiagJ h J a d ha hd := by
  set Em : Matrix (Fin n) (Fin n) K := ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hEm
  obtain ⟨a, ha⟩ := hJ
  obtain ⟨b, hb⟩ : ∃ b, b ∉ J := by
    by_contra hcon
    push Not at hcon
    exact hJc (Finset.eq_univ_iff_forall.2 hcon)
  have hstruct : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → 2 ≤ I.card →
      (∀ i ∈ I, ∀ y, y ≠ i → Em i y = 0 ∧ Em y i = 0) ∧ ∀ i ∈ I, ∀ j ∈ I, Em i i = Em j j :=
    fun {I} hI h2I => eq_of_commute_uBlock h h2I (hcomm I hI h2I)
  have hoffI : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → 2 ≤ I.card → ∀ x z, x ≠ z →
      (x ∈ I ∨ z ∈ I) → Em x z = 0 := by
    intro I hI h2I x z hxz hxzI
    rcases hxzI with hx | hz
    · exact ((hstruct hI h2I).1 x hx z (Ne.symm hxz)).1
    · exact ((hstruct hI h2I).1 z hz x hxz).2
  obtain ⟨I0, hI0, h2I0⟩ := kaUS_exists_big hn J
  have hoff : ∀ x z, x ≠ z → Em x z = 0 := by
    intro x z hxz
    by_cases hx : x ∈ J <;> by_cases hz : z ∈ J
    · exact hoffI (Or.inl rfl) (Finset.one_lt_card.2 ⟨x, hx, z, hz, hxz⟩) x z hxz (Or.inl hx)
    · refine hoffI hI0 h2I0 x z hxz ?_
      rcases hI0 with hI | hI
      · left
        rw [hI]
        exact hx
      · right
        rw [hI]
        exact Finset.mem_compl.2 hz
    · refine hoffI hI0 h2I0 x z hxz ?_
      rcases hI0 with hI | hI
      · right
        rw [hI]
        exact hz
      · left
        rw [hI]
        exact Finset.mem_compl.2 hx
    · exact hoffI (Or.inr rfl) (Finset.one_lt_card.2 ⟨x, Finset.mem_compl.2 hx, z,
        Finset.mem_compl.2 hz, hxz⟩) x z hxz (Or.inl (Finset.mem_compl.2 hx))
  have hdiagJ : ∀ x ∈ J, Em x x = Em a a := by
    intro x hx
    by_cases hxa : x = a
    · rw [hxa]
    · exact (hstruct (Or.inl rfl) (Finset.one_lt_card.2 ⟨x, hx, a, ha, hxa⟩)).2 x hx a ha
  have hdiagJc : ∀ x, x ∉ J → Em x x = Em b b := by
    intro x hx
    by_cases hxb : x = b
    · rw [hxb]
    · exact (hstruct (Or.inr rfl) (Finset.one_lt_card.2 ⟨x, Finset.mem_compl.2 hx, b,
        Finset.mem_compl.2 hb, hxb⟩)).2 x (Finset.mem_compl.2 hx) b (Finset.mem_compl.2 hb)
  have hdiag : Em = diagonal fun k => if k ∈ J then Em a a else Em b b := by
    ext x z
    by_cases hxz : x = z
    · subst hxz
      rw [diagonal_apply_eq]
      split_ifs with hx
      · exact hdiagJ x hx
      · exact hdiagJc x hx
    · rw [diagonal_apply_ne _ hxz]
      exact hoff x z hxz
  have hU : (Em.map h.bar)ᵀ * Em = 1 := (mem_uU h).1 E.2
  have hnorm : ∀ k, h.norm (if k ∈ J then Em a a else Em b b) = 1 := by
    intro k
    have e := congrFun (congrFun hU k) k
    rw [hdiag, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      diagonal_apply_eq, one_apply_eq] at e
    rw [UnitaryFieldData.norm, mul_comm]
    exact e
  have hna : h.norm (Em a a) = 1 := by simpa [ha] using hnorm a
  have hnb : h.norm (Em b b) = 1 := by simpa [hb] using hnorm b
  have h0 : ∀ c : K, h.norm c = 1 → c ≠ 0 := fun c hc h0 => by
    rw [h0, UnitaryFieldData.norm, zero_mul] at hc
    exact zero_ne_one hc
  refine ⟨Units.mk0 (Em a a) (h0 _ hna), Units.mk0 (Em b b) (h0 _ hnb), hna, hnb, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hdiag

end Big

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
