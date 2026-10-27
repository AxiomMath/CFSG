module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.EightQuaternionCandidatesData
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Semidihedral.GL2Recognition

open Matrix
open scoped Pointwise

@[expose] def Q₀ : Subgroup (GL (Fin 2) (ZMod 3)) := Subgroup.closure {I₀, J₀}

@[expose] def IsCandidateSigma (α : MulAut Q₀) (σ : Equiv.Perm (Fin 11)) : Prop :=
  σ 9 = 10 ∧ σ 10 = 0 ∧ σ 0 = 9 ∧
    ∀ q : Q₀, σ (planePoint (((q : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ
        vecE)) =
      planePoint (((α q : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ vecE)

@[expose] def candidateGroup (σ : Equiv.Perm (Fin 11)) : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure {genH₁, genH₂, genH₃, genH₄, σ}

theorem I₀_mem_Q₀ : I₀ ∈ Q₀ := Subgroup.subset_closure (by simp)

theorem J₀_mem_Q₀ : J₀ ∈ Q₀ := Subgroup.subset_closure (by simp)

theorem qElem_mem (i : Fin 8) : qElem i ∈ Q₀ := by
  have hI := I₀_mem_Q₀
  have hJ := J₀_mem_Q₀
  fin_cases i
  · exact Q₀.one_mem
  · exact hI
  · exact hJ
  · exact Q₀.mul_mem hI hI
  · exact Q₀.mul_mem hI hJ
  · exact Q₀.mul_mem hJ hI
  · exact Q₀.mul_mem (Q₀.mul_mem hI hI) hI
  · exact Q₀.mul_mem (Q₀.mul_mem hJ hJ) hJ

theorem mem_Q₀_iff (g : GL (Fin 2) (ZMod 3)) : g ∈ Q₀ ↔ ∃ i, qElem i = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    | one => exact ⟨0, rfl⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨i, rfl⟩ := ihg
      obtain ⟨j, rfl⟩ := ihh
      exact ⟨qMul i j, (qElem_mul i j).symm⟩
    | inv g _ ih =>
      obtain ⟨i, rfl⟩ := ih
      exact ⟨qInv i, (qElem_inv i).symm⟩
  · rintro ⟨i, rfl⟩
    exact qElem_mem i

@[expose] def qSub (i : Fin 8) : Q₀ := ⟨qElem i, qElem_mem i⟩

theorem qSub_surjective : Function.Surjective qSub := fun q => by
  obtain ⟨i, hi⟩ := (mem_Q₀_iff q).1 q.2
  exact ⟨i, Subtype.ext hi⟩

theorem qSub_injective : Function.Injective qSub := fun _ _ h =>
  qElem_injective (congrArg Subtype.val h)

theorem qSub_mul (i j : Fin 8) : qSub i * qSub j = qSub (qMul i j) :=
  Subtype.ext (qElem_mul i j)

theorem card_Q₀ : Nat.card Q₀ = 8 := by
  rw [← Nat.card_eq_of_bijective qSub ⟨qSub_injective, qSub_surjective⟩, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem exists_autArray (α : MulAut Q₀) :
    ∃ a b : Fin 8, ∀ i, α (qSub i) = qSub (autArray a b i) := by
  obtain ⟨a, ha⟩ := qSub_surjective (α (qSub 1))
  obtain ⟨b, hb⟩ := qSub_surjective (α (qSub 2))
  refine ⟨a, b, fun i => ?_⟩
  fin_cases i
  · show α (qSub 0) = qSub 0
    rw [show qSub 0 = 1 from rfl, map_one]
  · exact ha.symm
  · exact hb.symm
  · show α (qSub 1 * qSub 1) = qSub (qMul a a)
    rw [map_mul, ← ha, qSub_mul]
  · show α (qSub 1 * qSub 2) = qSub (qMul a b)
    rw [map_mul, ← ha, ← hb, qSub_mul]
  · show α (qSub 2 * qSub 1) = qSub (qMul b a)
    rw [map_mul, ← ha, ← hb, qSub_mul]
  · show α (qSub 1 * qSub 1 * qSub 1) = qSub (qMul (qMul a a) a)
    rw [map_mul, map_mul, ← ha, qSub_mul, qSub_mul]
  · show α (qSub 2 * qSub 2 * qSub 2) = qSub (qMul (qMul b b) b)
    rw [map_mul, map_mul, ← hb, qSub_mul, qSub_mul]

theorem exists_cand_of_orderOf_eq_three (α : MulAut Q₀) (hα : orderOf α = 3) :
    ∃ k : Fin 8, ∀ i, α (qSub i) = qSub (autArray (candA k) (candB k) i) := by
  obtain ⟨a, b, hab⟩ := exists_autArray α
  have hinj : ∀ i j, autArray a b i = autArray a b j → i = j := fun i j h =>
    qSub_injective (α.injective (by rw [hab, hab, h]))
  have hmul : ∀ i j, autArray a b (qMul i j) = qMul (autArray a b i) (autArray a b j) :=
    fun i j => qSub_injective (by rw [← hab, ← qSub_mul, map_mul, hab, hab, qSub_mul])
  have hpow : α ^ 3 = 1 := by
    have h := pow_orderOf_eq_one α
    rwa [hα] at h
  have hcube : ∀ i, autArray a b (autArray a b (autArray a b i)) = i := fun i =>
    qSub_injective (by
      rw [← hab, ← hab, ← hab]
      have h := congrArg (fun β : MulAut Q₀ => β (qSub i)) hpow
      simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h)
  have hne : ∃ i, autArray a b i ≠ i := by
    by_contra! h
    have h1 : α = 1 := MulEquiv.ext fun q => by
      obtain ⟨i, rfl⟩ := qSub_surjective q
      rw [hab, h, MulAut.one_apply]
    rw [h1, orderOf_one] at hα
    omega
  obtain ⟨k, rfl, rfl⟩ := autArray_classification a b hinj hmul hcube hne
  exact ⟨k, hab⟩

theorem sigma_ptTable_of_isCandidateSigma {α : MulAut Q₀} {f : Fin 8 → Fin 8}
    (hf : ∀ i, α (qSub i) = qSub (f i)) {σ : Equiv.Perm (Fin 11)} (hσ : IsCandidateSigma α σ)
    (j : Fin 8) : σ (ptTable j) = ptTable (f j) := by
  have h := hσ.2.2.2 (qSub j)
  rw [hf j] at h
  change σ (planePoint ((qElem j : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ vecE)) =
    planePoint ((qElem (f j) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ vecE) at h
  rwa [planePoint_qElem_vecE, planePoint_qElem_vecE] at h

theorem eq_of_ptTable_spec (f : Fin 8 → Fin 8) {σ τ : Equiv.Perm (Fin 11)}
    (hσ : σ 9 = 10 ∧ σ 10 = 0 ∧ σ 0 = 9 ∧ ∀ j, σ (ptTable j) = ptTable (f j))
    (hτ : τ 9 = 10 ∧ τ 10 = 0 ∧ τ 0 = 9 ∧ ∀ j, τ (ptTable j) = ptTable (f j)) : σ = τ := by
  ext x
  rcases point_cases x with rfl | rfl | rfl | ⟨j, rfl⟩
  · rw [hσ.1, hτ.1]
  · rw [hσ.2.1, hτ.2.1]
  · rw [hσ.2.2.1, hτ.2.2.1]
  · rw [hσ.2.2.2, hτ.2.2.2]

theorem isCandidateSigma_sigmaCand {α : MulAut Q₀} {k : Fin 8}
    (hk : ∀ i, α (qSub i) = qSub (autArray (candA k) (candB k) i)) :
    IsCandidateSigma α (sigmaCand k) := by
  obtain ⟨h9, h10, h0⟩ := sigmaCand_triple k
  refine ⟨h9, h10, h0, fun q => ?_⟩
  obtain ⟨j, rfl⟩ := qSub_surjective q
  rw [hk j]
  change sigmaCand k (planePoint ((qElem j : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ vecE)) =
    planePoint ((qElem (autArray (candA k) (candB k) j) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ
      vecE)
  rw [planePoint_qElem_vecE, planePoint_qElem_vecE]
  exact sigmaCand_ptTable k j

theorem conj_nativeM11_le {c : Equiv.Perm (Fin 11)} {K : Subgroup (Equiv.Perm (Fin 11))}
    (ha : c * m11GenA * c⁻¹ ∈ K) (hb : c * m11GenB * c⁻¹ ∈ K) :
    MulAut.conj c • CFSG.Blueprint.NativeSporadic.M11 ≤ K := by
  have hM : CFSG.Blueprint.NativeSporadic.M11 = Subgroup.closure {m11GenA, m11GenB} := rfl
  rw [hM, Subgroup.smul_closure, Subgroup.closure_le, Set.smul_set_insert,
    Set.smul_set_singleton, Set.insert_subset_iff, Set.singleton_subset_iff, MulAut.smul_def,
    MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply]
  exact ⟨ha, hb⟩

theorem alternative_sigmaCand (k : Fin 8) :
    (∃ g ∈ candidateGroup (sigmaCand k), g ≠ 1 ∧
        4 ≤ (Finset.univ.filter fun x => g x = x).card) ∨
      ∃ c : Equiv.Perm (Fin 11),
        MulAut.conj c • CFSG.Blueprint.NativeSporadic.M11 ≤ candidateGroup (sigmaCand k) := by
  have hgens : ∀ g ∈ candGens k, g ∈ candidateGroup (sigmaCand k) := fun g hg =>
    Subgroup.subset_closure (by simpa [candGens] using hg)
  by_cases h37 : k = 3 ∨ k = 7
  · exact Or.inl ⟨_, signedWord_mem _ _ hgens _, fixedWord_cand k h37⟩
  · push Not at h37
    refine Or.inr ⟨conjCand k, conj_nativeM11_le ?_ ?_⟩
    · rw [conjCand_m11GenA k h37.1 h37.2]
      exact signedWord_mem _ _ hgens _
    · rw [conjCand_m11GenB k h37.1 h37.2]
      exact signedWord_mem _ _ hgens _

theorem eight_quaternion_candidates_force_M11 (α : MulAut Q₀) (hα : orderOf α = 3) :
    (∃! σ : Equiv.Perm (Fin 11), IsCandidateSigma α σ) ∧
      ∀ σ : Equiv.Perm (Fin 11), IsCandidateSigma α σ →
        (∃ g ∈ candidateGroup σ, g ≠ 1 ∧ 4 ≤ (Finset.univ.filter fun x => g x = x).card) ∨
          ∃ c : Equiv.Perm (Fin 11),
            MulAut.conj c • CFSG.Blueprint.NativeSporadic.M11 ≤ candidateGroup σ := by
  obtain ⟨k, hk⟩ := exists_cand_of_orderOf_eq_three α hα
  have hspec : ∀ σ, IsCandidateSigma α σ → σ = sigmaCand k := fun σ hσ =>
    eq_of_ptTable_spec (autArray (candA k) (candB k))
      ⟨hσ.1, hσ.2.1, hσ.2.2.1, sigma_ptTable_of_isCandidateSigma hk hσ⟩
      ⟨(sigmaCand_triple k).1, (sigmaCand_triple k).2.1, (sigmaCand_triple k).2.2,
        sigmaCand_ptTable k⟩
  refine ⟨⟨sigmaCand k, isCandidateSigma_sigmaCand hk, hspec⟩, fun σ hσ => ?_⟩
  rw [hspec σ hσ]
  exact alternative_sigmaCand k

end CFSG.Semidihedral.GL2Recognition
