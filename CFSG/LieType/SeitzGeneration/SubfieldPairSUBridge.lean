module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxUnitary
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.BorelTits CFSG.RankThree.Classical

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem bar_eq_unitaryInvolution (h : UnitaryFieldData ℓ f K) (c : K) :
    h.bar c = unitaryInvolution K ℓ f c := by
  rw [h.bar_apply, unitaryInvolution_apply]

theorem bar_funext (h : UnitaryFieldData ℓ f K) : ⇑h.bar = ⇑(unitaryInvolution K ℓ f) :=
  funext (bar_eq_unitaryInvolution h)

theorem gramSU_one_eq (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      SUid (unitaryInvolution K ℓ f) n := by
  ext g
  rw [mem_gramSU, mem_SUid, Units.val_one, Matrix.mul_one, and_comm, conjTr, bar_funext h]

section Subfield

variable (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K} [Finite k] [CharP k ℓ]
  (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c)

omit [Finite k] [CharP k ℓ] in
include hbar in
theorem stable_of_bar : ∀ x ∈ k, unitaryInvolution K ℓ f x ∈ k := by
  intro x hx
  rw [← bar_eq_unitaryInvolution h, ← hbar ⟨x, hx⟩]
  exact (h₀.bar ⟨x, hx⟩).2

include hbar in
theorem bar_coe : ∀ x : k, ((unitaryInvolution k ℓ e x : k) : K) =
    unitaryInvolution K ℓ f (x : K) := by
  intro x
  rw [← bar_eq_unitaryInvolution h₀, ← bar_eq_unitaryInvolution h, hbar]

variable (n : ℕ)

@[expose] noncomputable def eSU : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃*
    SUid (unitaryInvolution K ℓ f) n :=
  MulEquiv.subgroupCongr (gramSU_one_eq h n)

theorem map_suSub_eq :
    (suSub h h₀ hbar n).map (eSU h n).toMonoidHom =
      ratSU (unitaryInvolution K ℓ f) k (stable_of_bar h h₀ hbar) n := by
  ext g
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩ i j
    exact (((y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j).2
  · intro hg
    obtain ⟨x, hx⟩ := exists_subSU_eq (unitaryInvolution k ℓ e) (bar_coe h h₀ hbar)
      (stable_of_bar h h₀ hbar) hg
    refine ⟨subfieldSU h h₀ hbar n ((eSU h₀ n).symm x), ⟨_, rfl⟩, ?_⟩
    rw [← hx]
    rfl

omit [Finite k] [CharP k ℓ] in
theorem conjTr_mul_self_of_mem (A : primeFormUnitary h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) :
    conjTr (unitaryInvolution K ℓ f) ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have h1 := mem_primeFormUnitary.1 A.2
  have e1 : ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := Units.val_one
  rw [conjTr, ← bar_funext h]
  simpa only [e1, Matrix.mul_one] using h1

omit [Finite k] [CharP k ℓ] in
theorem eSU_conj (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    (eSU h n).toMonoidHom.comp (primeFormConjSU h _ A).toMonoidHom =
      (suConj (unitaryInvolution_involutive h.card_eq_sq) (A : GL (Fin n) K)
        (conjTr_mul_self_of_mem h n A)).comp (eSU h n).toMonoidHom :=
  MonoidHom.ext fun _ => rfl

theorem map_conj_suSub_eq (A : primeFormUnitary h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) :
    ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom).map (eSU h n).toMonoidHom =
      (ratSU (unitaryInvolution K ℓ f) k (stable_of_bar h h₀ hbar) n).map
        (suConj (unitaryInvolution_involutive h.card_eq_sq) (A : GL (Fin n) K)
          (conjTr_mul_self_of_mem h n A)) := by
  rw [Subgroup.map_map, eSU_conj, ← Subgroup.map_map, map_suSub_eq]

end Subfield

end CFSG.LieType.SeitzGeneration.SUPair
