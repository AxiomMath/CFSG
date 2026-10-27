module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Frame

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3
  (Theorem3Statement Frame SylowFrame exists_isSylowOf_le)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sup_isElemAbelian {A B : Subgroup G} (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hAs : ∀ a ∈ A, a * a = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBs : ∀ b ∈ B, b * b = 1) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (∀ x ∈ A ⊔ B, ∀ x' ∈ A ⊔ B, x * x' = x' * x) ∧ (∀ x ∈ A ⊔ B, x * x = 1) := by
  have hmem : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := fun x hx =>
    (mem_sup_iff_of_commute hAB).1 hx
  refine ⟨fun x hx x' hx' => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hmem x' hx'
    have e1 : a * b * (a' * b') = a * a' * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [(hAB a' ha' b hb).symm]
        _ = a * a' * (b * b') := by group
    have e2 : a' * b' * (a * b) = a' * a * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [(hAB a ha b' hb').symm]
        _ = a' * a * (b' * b) := by group
    rw [e1, e2, hAc a ha a' ha', hBc b hb b' hb']
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    have e1 : a * b * (a * b) = a * a * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [(hAB a ha b hb).symm]
        _ = a * a * (b * b) := by group
    rw [e1, hAs a ha, hBs b hb, mul_one]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem inf_conj_le_of_sylowFrame {g : G} (hg : g ∉ M) {T S : Subgroup G} (hS : SylowFrame J T S)
    (hQV : S ⊓ Subgroup.normalizer (T : Set G) ⊓ J ≤ blockU J)
    (hTB : T ≤ rightConjugate J g) :
    rightConjugate J g ⊓ (S ⊓ Subgroup.normalizer (T : Set G)) ≤ T := by
  rintro x ⟨hxB, hxW⟩
  obtain ⟨t, ht, q, hq, rfl⟩ := X_decomp hS hxW
  have hqB : q ∈ rightConjugate J g := by
    have := (rightConjugate J g).mul_mem ((rightConjugate J g).inv_mem (hTB ht)) hxB
    have e : t⁻¹ * (t * q) = q := by group
    rwa [e] at this
  have hqJ : q ∈ J := (Subgroup.mem_inf.1 hq).2
  have hq2 : ∃ n : ℕ, q ^ 2 ^ n = 1 :=
    ⟨1, by rw [pow_one, pow_two]; exact c.block.blockU_sq_eq_one q (hQV hq)⟩
  have hq1 : q = 1 := c.eq_one_of_mem_inf hg hqJ hqB hq2
  rw [hq1, mul_one]
  exact ht

theorem le_normalizer_blockU_sup {J' : Subgroup G} (hne : J' ≠ J)
    (hJ' : ∀ m ∈ M, rightConjugate J m = J ∨ rightConjugate J m = J') :
    M ≤ Subgroup.normalizer ((blockU J ⊔ blockU J' : Subgroup G) : Set G) := by
  obtain ⟨m₃, hm₃, hne₃⟩ := c.exists_conj_ne
  have hJ'eq : rightConjugate J m₃ = J' := (hJ' m₃ hm₃).resolve_left hne₃
  intro m hm
  rw [← rightConjugate_eq_self_iff]
  have h1 := hJ' m hm
  have h2 : rightConjugate J' m = J ∨ rightConjugate J' m = J' := by
    have := hJ' (m₃ * m) (M.mul_mem hm₃ hm)
    rw [← rightConjugate_mul, hJ'eq] at this
    exact this
  have hinj : rightConjugate J m ≠ rightConjugate J' m := fun h =>
    hne (rightConjugate_inj'.1 h).symm
  have hsup : rightConjugate (blockU J ⊔ blockU J') m =
      blockU (rightConjugate J m) ⊔ blockU (rightConjugate J' m) := by
    rw [blockU_rightConjugate, blockU_rightConjugate]
    exact Subgroup.map_sup _ _ _
  rw [hsup]
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hinj
    · rw [h1, h2]
  · rcases h2 with h2 | h2
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) hinj

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
