module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CMatEq

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.A6C

variable {n : ℕ} {Γ : Type} [Group Γ]

@[expose] def A6CElt (m : A6CModel n Γ) (x : Mat) : Γ := m.ofMat (A6CToMat n x)

@[expose] def A6CSimArr (n : ℕ) (x : Mat) : Prop := A6CWf n x ∧ A6CSimMat (A6CToMat n x)

theorem A6CSimArr.of_simOK {g : Mat} (h : simOK n g = true) : A6CSimArr n g :=
  (a6c_simOK_iff n g).mp h

theorem A6CSimArr.idN (n : ℕ) : A6CSimArr n (idN n) :=
  ⟨a6c_wf_idN n, by rw [a6c_toMat_idN]; exact A6CSimMat.one⟩

theorem A6CSimArr.mulN {x y : Mat} (hx : A6CSimArr n x) (hy : A6CSimArr n y) :
    A6CSimArr n (mulN n x y) :=
  ⟨a6c_wf_mulN n x y, by rw [a6c_toMat_mulN]; exact hx.2.mul hy.2⟩

theorem A6CSimArr.negM {x : Mat} (hx : A6CSimArr n x) : A6CSimArr n (negM x) :=
  ⟨a6c_wf_negM n hx.1, by rw [a6c_toMat_negM]; exact hx.2.neg⟩

theorem A6CSimArr.trN {x : Mat} (hx : A6CSimArr n x) : A6CSimArr n (trN n x) :=
  ⟨a6c_wf_trN n hx.1, by rw [a6c_toMat_trN]; exact hx.2.transpose⟩

theorem A6CSimArr.conjN {g x : Mat} (hg : A6CSimArr n g) (hx : A6CSimArr n x) :
    A6CSimArr n (conjN n g x) := by
  unfold Certificates.A6C.conjN
  exact A6CSimArr.mulN (A6CSimArr.mulN hg hx) (A6CSimArr.trN hg)

theorem a6cElt_mulN (m : A6CModel n Γ) {x y : Mat} (hx : A6CSimArr n x) (hy : A6CSimArr n y) :
    A6CElt m (mulN n x y) = A6CElt m x * A6CElt m y := by
  unfold A6CElt
  rw [a6c_toMat_mulN, m.ofMat_mul _ _ hx.2 hy.2]

theorem a6cElt_idN (m : A6CModel n Γ) : A6CElt m (idN n) = 1 := by
  unfold A6CElt
  rw [a6c_toMat_idN, m.ofMat_one]

theorem a6cElt_powM (m : A6CModel n Γ) {x : Mat} (hx : A6CSimArr n x) (k : ℕ) :
    A6CElt m (powM n x k) = A6CElt m x ^ k := by
  unfold A6CElt
  rw [a6c_toMat_powM, m.ofMat_pow hx.2 k]

theorem a6cElt_conjN (m : A6CModel n Γ) {g x : Mat} (hg : A6CSimArr n g) (hx : A6CSimArr n x) :
    A6CElt m (conjN n g x) = A6CElt m g * A6CElt m x * (A6CElt m g)⁻¹ := by
  unfold A6CElt
  rw [a6c_toMat_conjN, m.ofMat_conj hg.2 hx.2]

theorem a6cElt_eq_iff (m : A6CModel n Γ) {x y : Mat} (hx : A6CSimArr n x) (hy : A6CSimArr n y) :
    eqP x y = true ↔ A6CElt m x = A6CElt m y := by
  rw [a6c_eqP_iff n hx.1 hy.1]
  unfold A6CElt
  exact (m.ofMat_eq _ _ hx.2 hy.2).symm

theorem a6cElt_commP (m : A6CModel n Γ) {x y : Mat} (hx : A6CSimArr n x) (hy : A6CSimArr n y) :
    commP n x y = true ↔ A6CElt m x * A6CElt m y = A6CElt m y * A6CElt m x := by
  rw [a6c_commP_iff n x y]
  unfold A6CElt
  rw [← m.ofMat_mul _ _ hx.2 hy.2, ← m.ofMat_mul _ _ hy.2 hx.2]
  exact (m.ofMat_eq _ _ (hx.2.mul hy.2) (hy.2.mul hx.2)).symm

theorem a6cElt_relP (m : A6CModel n Γ) {a x : Mat} (ha : A6CSimArr n a) (hx : A6CSimArr n x) :
    relP n a x = true ↔ A6CElt m a * A6CElt m a = 1 ∧
      (A6CElt m a * A6CElt m x) ^ 4 = 1 ∧ (A6CElt m x * A6CElt m a * A6CElt m x) ^ 5 = 1 := by
  rw [a6c_relP_iff n a x]
  have e1 : (A6CToMat n a * A6CToMat n a = 1 ∨ A6CToMat n a * A6CToMat n a = -1) ↔
      A6CElt m a * A6CElt m a = 1 := by
    rw [show A6CElt m a * A6CElt m a = m.ofMat (A6CToMat n a * A6CToMat n a) by
      unfold A6CElt; rw [m.ofMat_mul _ _ ha.2 ha.2]]
    simpa [m.ofMat_one] using (m.ofMat_eq _ _ (ha.2.mul ha.2) A6CSimMat.one).symm
  have e2 : ((A6CToMat n a * A6CToMat n x) ^ 4 = 1 ∨
      (A6CToMat n a * A6CToMat n x) ^ 4 = -1) ↔
      (A6CElt m a * A6CElt m x) ^ 4 = 1 := by
    rw [show (A6CElt m a * A6CElt m x) ^ 4 =
        m.ofMat ((A6CToMat n a * A6CToMat n x) ^ 4) by
      unfold A6CElt; rw [← m.ofMat_mul _ _ ha.2 hx.2, m.ofMat_pow (ha.2.mul hx.2) 4]]
    simpa [m.ofMat_one] using (m.ofMat_eq _ _ ((ha.2.mul hx.2).pow 4) A6CSimMat.one).symm
  have e3 : ((A6CToMat n x * A6CToMat n a * A6CToMat n x) ^ 5 = 1 ∨
      (A6CToMat n x * A6CToMat n a * A6CToMat n x) ^ 5 = -1) ↔
      (A6CElt m x * A6CElt m a * A6CElt m x) ^ 5 = 1 := by
    rw [show (A6CElt m x * A6CElt m a * A6CElt m x) ^ 5 =
        m.ofMat ((A6CToMat n x * A6CToMat n a * A6CToMat n x) ^ 5) by
      unfold A6CElt
      rw [← m.ofMat_mul _ _ hx.2 ha.2, ← m.ofMat_mul _ _ (hx.2.mul ha.2) hx.2,
        m.ofMat_pow ((hx.2.mul ha.2).mul hx.2) 5]]
    simpa [m.ofMat_one] using
      (m.ofMat_eq _ _ (((hx.2.mul ha.2).mul hx.2).pow 5) A6CSimMat.one).symm
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨e1.mp h1, e2.mp h2, e3.mp h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨e1.mpr h1, e2.mpr h2, e3.mpr h3⟩⟩

end CFSG.OddStandard.SmallF3.Omega
