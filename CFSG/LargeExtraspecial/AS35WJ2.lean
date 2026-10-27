module

public import CFSG.LargeExtraspecial.AS35WCheck
public import CFSG.LargeExtraspecial.AS35WList
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2
public import Certificates.Certificate21295

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier
  CFSG.ClassicalInvolution.J2Data CFSG.ClassicalInvolution.J2Proof CFSG.ClassicalInvolution
  CFSG.Blueprint

namespace AS35W

theorem j2U_facts :
    uChain.originalSubgroup ≤ cent2AChain.originalSubgroup ∧
      cent2AChain.originalSubgroup ≤
        normalizer (uChain.originalSubgroup : Set (Equiv.Perm (Fin 315))) ∧
      IsPGroup 2 uChain.originalSubgroup := by
  obtain ⟨hin, hnorm, -⟩ := cent2A_structure_check
  have hUgen : ∀ i < 4, Rep 315 uStrong[i]! (permOfArr 315 uStrong[i]!) := fun i hi =>
    rep_permOfArr_of_chainOK uChain_ok (by rw [uStrong_size]; exact hi)
  have hKgen : ∀ i < 2, Rep 315 cent2AStrong[i]! (permOfArr 315 cent2AStrong[i]!) := fun i hi =>
    rep_permOfArr_of_chainOK cent2A_ok (by
      have : cent2AStrong.size = 5 := rfl
      omega)
  have hKinv : ∀ i < 2, Rep 315 (invCand 315 cent2AStrong[i]!)
      (permOfArr 315 cent2AStrong[i]!)⁻¹ :=
    fun i hi => rep_inv_of_chainOK cent2A_ok (by
      have : cent2AStrong.size = 5 := rfl
      omega)
  have hmemU : ∀ {t : Array ℕ} {g : Equiv.Perm (Fin 315)}, Rep 315 t g →
      (siftA 315 uLevels uBase 0 t = true ↔ g ∈ uChain.originalSubgroup) := fun {t g} h =>
    ofArrays_mem_iff (by norm_num) uChain_ok h
  have hmemK : ∀ {t : Array ℕ} {g : Equiv.Perm (Fin 315)}, Rep 315 t g →
      (siftA 315 cent2ALevels cent2ABase 0 t = true ↔ g ∈ cent2AChain.originalSubgroup) :=
    fun {t g} h => ofArrays_mem_iff (by norm_num) cent2A_ok h
  have hUc : uChain.originalSubgroup =
      Subgroup.closure {g | ∃ i < 4, permOfArr 315 uStrong[i]! = g} := ofArrays_originalSubgroup
  refine ⟨?_, ?_, ?_⟩
  · rw [hUc, Subgroup.closure_le]
    rintro g ⟨i, hi, rfl⟩
    exact (hmemK (hUgen i hi)).1 (hin i hi)
  · rw [cent2AChain, ofArrays_originalSubgroup, hUc]
    refine closure_le_normalizer_closure _ _ ?_
    rintro _ ⟨k, hk, rfl⟩ _ ⟨i, hi, rfl⟩
    have := (hmemU (rep_conjA (hKgen k hk) (hKinv k hk) (hUgen i hi))).1 (hnorm k hk i hi)
    rwa [hUc] at this
  · exact IsPGroup.of_card (n := 5) (by rw [card_uChain]; norm_num)

@[expose] noncomputable def j2C : Equiv.Perm (Fin 315) :=
  (j2Word.map fun b => if b then permB else permA).prod

theorem rep_word {n : ℕ} {a₀ a₁ : Array Nat} {g₀ g₁ : Equiv.Perm (Fin n)} (h₀ : Rep n a₀ g₀)
    (h₁ : Rep n a₁ g₁) (l : List Bool) :
    Rep n ((l.map fun b => if b then a₁ else a₀).foldr (compA n) (idA n))
      (l.map fun b => if b then g₁ else g₀).prod := by
  induction l with
  | nil => exact rep_idA
  | cons b l ih =>
    rw [List.map_cons, List.foldr_cons, List.map_cons, List.prod_cons]
    cases b
    · exact rep_compA h₀ ih
    · exact rep_compA h₁ ih

theorem rep_j2C : Rep 315 j2CArr j2C :=
  rep_word rep_permA rep_permB j2Word

theorem j2C_mem : j2C ∈ P := by
  refine P.list_prod_mem fun g hg => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
  cases b
  · exact permA_mem
  · exact permB_mem

@[expose] noncomputable def j2X : Equiv.Perm (Fin 315) := permOfArr 315 uStrong[0]!

theorem rep_j2X : Rep 315 uStrong[0]! j2X :=
  rep_permOfArr_of_chainOK uChain_ok (by rw [uStrong_size]; norm_num)

theorem j2X_mem_U : j2X ∈ uChain.originalSubgroup := by
  rw [uChain, ofArrays_originalSubgroup]
  exact Subgroup.subset_closure ⟨0, by norm_num, rfl⟩

theorem j2_conj :
    j2C * permTwoA * j2C⁻¹ = j2X ∧ j2X ≠ permTwoA := by
  have h := Certificates.certificate21295
  simp only [j2ConjCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : j2C * permTwoA = j2X * j2C :=
    eq_of_eqA (rep_compA rep_j2C rep_permTwoA) (rep_compA rep_j2X rep_j2C) h1
  refine ⟨by rw [e1]; group, fun e => ?_⟩
  have := (eqA_iff rep_j2X rep_permTwoA).2 e
  rw [this] at h2
  exact Bool.noConfusion h2

theorem j2W2Input :
    J2W2Input := by
  intro X _ _ hX z hz
  exfalso
  obtain ⟨e⟩ := hX
  have e' : X ≃* P := e.trans nativeEquivP
  have hz' := hz.map e'
  obtain ⟨hcov, -, h2B, -, h2A⟩ := inner_classes
  have hw2 : orderOf ((e' z : P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hz'.orderOf_eq
  obtain ⟨r, hr, c, hcP, hrc⟩ := hcov _ (e' z).2 hw2
  have hdP : r ∈ P := by
    have : r = c⁻¹ * (e' z : Equiv.Perm (Fin 315)) * c := by rw [hrc]; group
    rw [this]
    exact P.mul_mem (P.mul_mem (P.inv_mem hcP) (e' z).2) hcP
  have hic : IsConj (⟨r, hdP⟩ : P) (e' z) := isConj_iff.2 ⟨(⟨c, hcP⟩ : P), Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hrc.symm)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  ·
    have hcard : Nat.card (centralizer ({e' z} : Set P)) = 240 := by
      rw [← card_centralizer_of_isConj hic, card_centralizer_subtype hdP,
        show (P ⊓ centralizer ({permA} : Set (Equiv.Perm (Fin 315)))) =
          Sporadic.Schreier.centralizerIn P permA from rfl, h2B, cent2B_facts.2.1]
    have := hz'.pow_dvd (k := 7) (by rw [card_P]; norm_num)
    rw [hcard] at this
    revert this
    decide
  ·
    obtain ⟨hUK, hKN, hU2⟩ := j2U_facts
    obtain ⟨hconj, hne⟩ := j2_conj
    have hz'' : W2Data P ⟨permTwoA, hdP⟩ := by
      obtain ⟨g, hg⟩ := isConj_iff.1 hic.symm
      have := hz'.map (MulAut.conj g)
      rwa [MulAut.conj_apply, hg] at this
    have hU : ∀ u ∈ uChain.originalSubgroup, u ∈ P := fun u hu =>
      (cent2A_facts.1 (hUK hu)).1
    refine hz''.false_of_conj_mem (P := uChain.originalSubgroup.comap P.subtype)
      (x := ⟨j2X, hU _ j2X_mem_U⟩) ?_ ?_ ?_ j2X_mem_U ?_ ?_
    · intro u hu
      rw [mem_centralizer_singleton_iff]
      have h1 := (cent2A_facts.1 (hUK hu)).2
      exact Subtype.ext (mem_centralizer_singleton_iff.mp h1)
    · intro g hg u hu
      have hg' : (g : Equiv.Perm (Fin 315)) ∈ cent2AChain.originalSubgroup := by
        rw [← h2A]
        exact ⟨g.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg))⟩
      exact (Subgroup.mem_normalizer_iff.mp (hKN hg') _).1 hu
    · exact hU2.comap_of_injective P.subtype P.subtype_injective
    · intro h
      exact hne (congrArg Subtype.val h)
    · exact isConj_iff.2 ⟨⟨j2C, j2C_mem⟩, Subtype.ext (by simpa using hconj)⟩

end AS35W

end CFSG.LargeExtraspecial
