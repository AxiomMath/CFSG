module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Open.LocalVocabulary

public noncomputable section

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

section Mat

variable {F : Type} [Field F]

@[expose] def heisMat (x : Heis F) : Matrix (Fin 3) (Fin 3) F := !![1, x.a, x.c; 0, 1, x.b; 0, 0, 1]

theorem heisMat_mul (x y : Heis F) : heisMat (x * y) = heisMat x * heisMat y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_heisMat (x : Heis F) : (heisMat x).det = 1 := by
  simp [heisMat, Matrix.det_fin_three]

@[expose] def heisSL : Heis F →* SpecialLinearGroup (Fin 3) F where
  toFun x := ⟨heisMat x, det_heisMat x⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisMat]
  map_mul' x y := Subtype.ext (heisMat_mul x y)

theorem coe_heisSL (x : Heis F) :
    ((heisSL x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = heisMat x := rfl

theorem heisSL_injective : Function.Injective (heisSL (F := F)) := by
  intro x y h
  have h' := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_heisSL] at h'
  have h1 := congrFun (congrFun h' 0) 1
  have h2 := congrFun (congrFun h' 1) 2
  have h3 := congrFun (congrFun h' 0) 2
  simp [heisMat] at h1 h2 h3
  ext <;> assumption

theorem heisSL_mem_unitriangular (x : Heis F) : heisSL x ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [coe_heisSL, heisMat] at hij ⊢
  · fin_cases i <;> simp [coe_heisSL, heisMat]

theorem exists_heisSL_of_mem_unitriangular {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ unitriangular 3 F) : ∃ x, heisSL x = A := by
  refine ⟨⟨(A : Matrix (Fin 3) (Fin 3) F) 0 1, (A : Matrix (Fin 3) (Fin 3) F) 1 2,
    (A : Matrix (Fin 3) (Fin 3) F) 0 2⟩, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_heisSL, heisMat, hA.2 0, hA.2 1, hA.2 2, hA.1 1 0 (by decide), hA.1 2 0 (by decide),
      hA.1 2 1 (by decide)]

@[expose] def heisEquivU : Heis F ≃* unitriangular 3 F :=
  MulEquiv.ofBijective (heisSL.codRestrict (unitriangular 3 F) heisSL_mem_unitriangular)
    ⟨fun x y h => heisSL_injective (congrArg Subtype.val h), fun A => by
      obtain ⟨x, hx⟩ := exists_heisSL_of_mem_unitriangular A.2
      exact ⟨x, Subtype.ext hx⟩⟩

@[expose] def heisEquivBar : Heis F ≃* projUnitriangular 3 F :=
  heisEquivU.trans (unitriangularEquivProj 3)

@[expose] def theta : Heis F →* projectiveSL 3 F := (proj 3 F).comp heisSL

theorem heisEquivBar_apply (x : Heis F) :
    ((heisEquivBar x : projUnitriangular 3 F) : projectiveSL 3 F) = theta x := rfl

theorem exists_theta_of_mem_bar {u : projectiveSL 3 F} (hu : u ∈ projUnitriangular 3 F) :
    ∃ y : Heis F, theta y = u := by
  obtain ⟨y, hy⟩ := heisEquivBar.surjective ⟨u, hu⟩
  exact ⟨y, congrArg Subtype.val hy⟩

theorem lower_entries_zero (g : SpecialLinearGroup (Fin 3) F) (c : F)
    (h : (g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 0, 1⟩ : Heis F) =
      heisMat (⟨0, 0, c⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F)) :
    (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have e : ∀ i j : Fin 3, ((g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 0, 1⟩ : Heis F)) i j =
      (heisMat (⟨0, 0, c⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F)) i j := fun i j => by rw [h]
  have e01 := e 0 1
  have e02 := e 0 2
  have e12 := e 1 2
  have e22 := e 2 2
  simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three] at e01 e02 e12 e22
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  refine ⟨e12, e22, ?_⟩
  rcases e01 with hc | h21
  · exfalso
    have h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by
      rw [hc] at e02
      linear_combination e02
    rw [e12, e22, h00] at hdet
    simp at hdet
  · exact h21

theorem mem_upperTriangular_of_lower_entries {g : SpecialLinearGroup (Fin 3) F}
    (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) : g ∈ upperTriangular 3 F := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact absurd hij (by decide) | exact h10 | exact h20 | exact h21

end Mat

section Normalizer

variable {F : Type} [Field F] [Finite F]

theorem p_dvd_card {p : ℕ} [CharP F p] : p ∣ Nat.card F := by
  have := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F p
  rw [← Nat.card_eq_fintype_card] at hk
  rw [hk]
  exact dvd_pow_self p k.ne_zero

theorem scalars_coprime {p : ℕ} (hp : p.Prime) [CharP F p] :
    Nat.Coprime (Nat.card (scalars 3 F)) p := by
  refine Nat.Coprime.coprime_dvd_left (card_scalars_dvd (by norm_num : 1 ≤ 3)) ?_
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdvd
  have h1 : 1 ≤ Nat.card F := Finite.card_pos
  have := Nat.dvd_sub (p_dvd_card (F := F) (p := p)) hdvd
  rw [Nat.sub_sub_self h1] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

end Normalizer

end CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3
