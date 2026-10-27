module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Assembly
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Shapes
public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo
public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.ComponentClassification.Asc75L47

open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isElemAbelian_of_card_eq_two {T : Subgroup X} (hT : Nat.card T = 2) :
    IsElemAbelian 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic T := isCyclic_of_prime_card hT
  refine ⟨inferInstance, fun t ht => ?_⟩
  have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
  rw [hT] at h1
  exact congrArg Subtype.val h1

omit [Finite X] in
theorem le_omegaOne_of_isDihedral {P : Subgroup X} (hP : IsDihedralTwoGroup P) :
    P ≤ omegaOne P := by
  obtain ⟨n, -, ⟨e⟩⟩ := hP
  have hsr : ∀ (q : P) (i : ZMod (2 ^ (n - 1))), e q = DihedralGroup.sr i →
      (q : X) ∈ omegaOne P := by
    intro q i hi
    refine mem_omegaOne q.2 ?_
    have h1 : q ^ 2 = 1 :=
      e.injective (by rw [map_pow, hi, map_one, pow_two, DihedralGroup.sr_mul_self])
    simpa using congrArg Subtype.val h1
  intro p hp
  rcases hpe : e ⟨p, hp⟩ with i | i
  · have hprod : (⟨p, hp⟩ : P) = e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.sr i) := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, DihedralGroup.sr_mul_sr, sub_zero, hpe]
    have h1 : p = (e.symm (DihedralGroup.sr 0) : X) * e.symm (DihedralGroup.sr i) :=
      congrArg Subtype.val hprod
    rw [h1]
    exact mul_mem (hsr _ 0 (e.apply_symm_apply _)) (hsr _ i (e.apply_symm_apply _))
  · exact hsr _ i hpe

theorem mem_dihedralSubgroup_of_sq_eq_one {n : ℕ} (hn : 4 ≤ n) {y : SemidihedralGroup n}
    (hy : y ^ 2 = 1) : y ∈ CFSG.Semidihedral.dihedralSubgroup n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  rcases (CFSG.Semidihedral.involution_iff n (by omega) y).mp (orderOf_eq_prime hy hy1) with
    rfl | ⟨j, rfl⟩
  · rw [CFSG.Semidihedral.z, CFSG.Semidihedral.half, show n - 2 = n - 3 + 1 by omega, pow_succ',
      pow_mul]
    exact pow_mem (CFSG.Semidihedral.r_sq_mem_dihedralSubgroup n) _
  · rw [pow_mul]
    exact mul_mem (pow_mem (CFSG.Semidihedral.r_sq_mem_dihedralSubgroup n) _)
      (CFSG.Semidihedral.s_mem_dihedralSubgroup n)

omit [Finite X] in
theorem not_isSemidihedral_of_le_omegaOne {S : Subgroup X} (hS : S ≤ omegaOne S) :
    ¬ IsSemidihedralTwoGroup S := by
  rintro ⟨n, hn, ⟨e⟩⟩
  set D : Subgroup S := (CFSG.Semidihedral.dihedralSubgroup n).comap e.toMonoidHom with hD
  have hle : omegaOne S ≤ D.map S.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxS, hx2⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    have h2 : (⟨x, hxS⟩ : S) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    have h3 : e ⟨x, hxS⟩ ^ 2 = 1 := by rw [← map_pow, h2, map_one]
    exact mem_dihedralSubgroup_of_sq_eq_one hn h3
  have htop : CFSG.Semidihedral.dihedralSubgroup n = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨u, hu, hux⟩ := hle (hS (e.symm y).2)
    have hu' : u = e.symm y := Subtype.ext (by simpa using hux)
    have h1 : e u ∈ CFSG.Semidihedral.dihedralSubgroup n := hu
    rwa [hu', e.apply_symm_apply] at h1
  have hidx := CFSG.Semidihedral.dihedralSubgroup_index n (by omega)
  rw [htop, Subgroup.index_top] at hidx
  omega

variable {Q T P S : Subgroup X}

theorem exists_hyp45 (h : Hyp3 Q T P S) (hW : relativeWeakClosure Q T S ≠ T) :
    ∃ g ∈ Q, Hyp45 Q T S P ((Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X)) g ∧
      (Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X) ⊓ S = T ⊔ rightConjugate T g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := (Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X) with hHdef
  have h43 := h.hyp43
  have hsf := h.sylowFrame
  have hF := hsf.toFrame
  have hTS := hsf.le
  have hS2 := hsf.sylow.isPGroup
  have hSGT := hsf.sylow.le
  have hsize : T.relIndex (S ⊓ H) ≤ Nat.card T := by
    rw [h.inf_H]
    exact h.index_le
  obtain ⟨g, hg, hgN, hne⟩ := exists_conj_le_normalizer hF hS2 hSGT hTS hW
  have hNH : S ⊓ Subgroup.normalizer (T : Set X) ≤ H :=
    (inf_le_inf_right _ hSGT).trans (h43.normalizer_le hF h.ne_bot)
  have hgSH : rightConjugate T g ≤ S ⊓ H := le_inf (hgN.trans inf_le_left) (hgN.trans hNH)
  obtain ⟨-, hinf, -, -⟩ := lemma_4_4_two hF h43 hS2 hTS hg hgSH hne
  have hcardM : Nat.card (T ⊔ rightConjugate T g : Subgroup X) = Nat.card T * Nat.card T := by
    rw [card_sup_of_le_normalizer (hgN.trans inf_le_right) hinf, rightConjugate_card]
  have hMle : T ⊔ rightConjugate T g ≤ H ⊓ S :=
    le_inf (sup_le h43.le_H (hgSH.trans inf_le_right)) (sup_le hTS (hgSH.trans inf_le_left))
  have hcardHS : Nat.card (H ⊓ S : Subgroup X) ≤ Nat.card T * Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card T (S ⊓ H)
    rw [inf_eq_left.mpr (le_inf hTS h43.le_H)] at h1
    rw [inf_comm, ← h1]
    exact Nat.mul_le_mul_right _ hsize
  have hHS : H ⊓ S = T ⊔ rightConjugate T g :=
    (Subgroup.eq_of_le_of_card_ge hMle (hcardHS.trans hcardM.ge)).symm
  refine ⟨g, hg, ⟨hsf, h43, hg, hne, ?_⟩, hHS⟩
  exact le_antisymm (by rw [← hHS]; exact relative_weak_closure_le _ _ _)
    (sup_le (subgroup_le_relative_weak_closure _ _ _ (hHS ▸ le_sup_left))
      (rightConjugate_le_relativeWeakClosure hg (hHS ▸ le_sup_right)))

theorem weakClosure_eq_of_not_isElemAbelian (h : Hyp3 Q T P S)
    (hW : relativeWeakClosure Q T S ≠ T) (hel : ¬ IsElemAbelian 2 T) :
    ∃ g ∈ Q, Hyp45 Q T S P ((Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X)) g ∧
      (Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X) ⊓ S = T ⊔ rightConjugate T g ∧
      relativeWeakClosure Q T S = T ⊔ rightConjugate T g := by
  obtain ⟨g, hg, h45, hHS⟩ := exists_hyp45 h hW
  refine ⟨g, hg, h45, hHS, ?_⟩
  by_contra hWM
  obtain ⟨y, hy, hyN, hyM⟩ := h45.exists_conj_not_le hHS hWM
  by_cases hm : 1 < CFSG.Open.pRank 2 T
  · exact hel (Elem47.elem ⟨h45, hHS, hm, hy, hyN, hyM⟩)
  · exact hel (isElemAbelian_of_card_eq_two (card_eq_two_of_pRank_le_one h45 hm hy hyN hyM))

theorem lemma47_cyclic (h : Hyp3 Q T P S) (hW : relativeWeakClosure Q T S ≠ T)
    (hcyc : IsCyclic T) :
    (IsCyclic (S ⊓ Q : Subgroup X) ∨ IsQuaternionTwoGroup (S ⊓ Q) ∨
        IsDihedralTwoGroup (S ⊓ Q)) ∧
      ((Nat.card T = 2 ∧ (IsDihedralTwoGroup S ∨ IsSemidihedralTwoGroup S)) ∨
        (2 < Nat.card T ∧ relativeWeakClosure Q T S = S ⊓ Subgroup.normalizer (T : Set X) ∧
          IsWreathedTwoGroup S)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, h45, hHS⟩ := exists_hyp45 h hW
  have hsf := h.sylowFrame
  have hF := hsf.toFrame
  have hT := h.ne_bot
  have hTS := hsf.le
  have hS2 := hsf.sylow.isPGroup
  have hSGT := hsf.sylow.le
  obtain ⟨-, -, hcomm, -⟩ := h45.facts
  have hm : ¬ 1 < CFSG.Open.pRank 2 T := fun hm =>
    AschbacherStrongEmbedding.Lemma34.not_isCyclic_of_two_le_pRank hm hcyc
  by_cases hT2 : Nat.card T = 2
  ·
    obtain ⟨t₀, ht₀, ht₀2, -⟩ := exists_center_involution hsf.isPGroup hT
    have ht₀1 : t₀ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht₀2
      omega
    have hsqT : ∀ t ∈ T, t ^ 2 = 1 := (isElemAbelian_of_card_eq_two hT2).2
    have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _)
    have hsqM : ∀ w ∈ T ⊔ rightConjugate T g, w ^ 2 = 1 := by
      intro w hw
      have hwmem : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
        exact hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hwmem
      have hab : a * b = b * a :=
        (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
      have hb2 : b ^ 2 = 1 := by
        have hb' : g * b * g⁻¹ ∈ T := (mem_rightConjugate_iff T g b).mp hb
        rw [show b ^ 2 = g⁻¹ * (g * b * g⁻¹) ^ 2 * g by simp only [pow_two]; group,
          hsqT _ hb']
        group
      calc (a * b) ^ 2 = a * (b * a) * b := by simp only [pow_two, mul_assoc]
        _ = a * (a * b) * b := by rw [hab]
        _ = a ^ 2 * b ^ 2 := by simp only [pow_two, mul_assoc]
        _ = 1 := by rw [hsqT a ha, hb2, one_mul]
    have hC := lemma_4_5_one h45 ht₀ ht₀1
    have hcardC : Nat.card (Subgroup.centralizer ({⟨t₀, hTS ht₀⟩} : Set S)) = 4 := by
      rw [card_centralizer_subtype, ← hC, hHS, h45.card_W, hT2]
    have hexpC : ∀ x ∈ Subgroup.centralizer ({⟨t₀, hTS ht₀⟩} : Set S), x ^ 2 = 1 := by
      intro x hx
      have hxC : (x : X) ∈ S ⊓ Subgroup.centralizer {t₀} := by
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        exact congrArg Subtype.val hx
      rw [← hC, hHS] at hxC
      exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsqM _ hxC)
    have hSQ : IsCyclic (S ⊓ Q : Subgroup X) ∨ IsQuaternionTwoGroup (S ⊓ Q) ∨
        IsDihedralTwoGroup (S ⊓ Q) := by
      apply shape_of_index_two hS2 inf_le_left _ (hTS ht₀) _ ht₀2
      · have heq : (S ⊓ Q) ⊓ Subgroup.centralizer {t₀} = (T ⊔ rightConjugate T g) ⊓ Q := by
          rw [← hHS, hC, inf_right_comm]
        rw [heq, h45.card_W_inf_G, hT2]
      · have h1 := hF.card_eq_mul hSGT hTS
        have h2 := Subgroup.relIndex_mul_card (S ⊓ Q) S
        rw [inf_eq_left.mpr inf_le_left, h1, hT2] at h2
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
      · intro hmem
        have hmem' : t₀ ∈ T ⊓ Q := ⟨ht₀, hmem.2⟩
        rw [hF.inf_eq_bot, Subgroup.mem_bot] at hmem'
        exact ht₀1 hmem'
    refine ⟨hSQ, Or.inl ⟨hT2, ?_⟩⟩
    rcases AschbacherToolkit.suzuki_two_group (P := S) hS2 hcardC hexpC with hD | hSD
    · exact Or.inl hD
    · exact Or.inr hSD
  ·
    have hWM : relativeWeakClosure Q T S = T ⊔ rightConjugate T g := by
      by_contra hWM
      obtain ⟨y, hy, hyN, hyM⟩ := h45.exists_conj_not_le hHS hWM
      exact hT2 (card_eq_two_of_pRank_le_one h45 hm hy hyN hyM)
    have hT4 : 2 < Nat.card T := by
      have h1 : Nat.card T ≠ 1 := fun h1 => hT (Subgroup.card_eq_one.mp h1)
      have h0 : 0 < Nat.card T := Nat.card_pos
      omega
    obtain ⟨hwr, hshape⟩ := h45.wreathed_case hHS hWM hcyc hT4 h.oddCore_eq_bot
    refine ⟨hshape, Or.inr ⟨hT4, ?_, hwr⟩⟩
    rw [hWM, ← hHS, h45.inf_eq_normalizer]

theorem lemma47_cyclic_of_isDihedral (h : Hyp3 Q T P S) (hW : relativeWeakClosure Q T S ≠ T)
    (hcyc : IsCyclic T) (hD : IsDihedralTwoGroup (S ⊓ Q)) :
    IsDihedralTwoGroup S ∨ IsWreathedTwoGroup S := by
  rcases (lemma47_cyclic h hW hcyc).2 with ⟨hT2, hS | hS⟩ | ⟨-, -, hS⟩
  · exact Or.inl hS
  · refine absurd hS (not_isSemidihedral_of_le_omegaOne ?_)
    have hsf := h.sylowFrame
    have hT2' : T ≤ omegaOne T := le_omegaOne (isElemAbelian_of_card_eq_two hT2).2
    calc S = (S ⊓ Q) ⊔ T := hsf.toFrame.eq_sup_inf hsf.sylow.le hsf.le
      _ ≤ omegaOne S := sup_le ((le_omegaOne_of_isDihedral hD).trans (omegaOne_mono inf_le_left))
          (hT2'.trans (omegaOne_mono hsf.le))
  · exact Or.inr hS

end CFSG.ComponentClassification.Asc75L47
