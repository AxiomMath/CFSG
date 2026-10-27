module

public import Certificates.Certificate778702

public section

namespace CFSG.CGT.Stroth77

open Equiv Equiv.Perm

theorem Eg_eq_Qns : Eg = Qns :=
  Certificates.certificate778702.2.2.2.1

theorem card_Eg : Nat.card Eg = 16 := by rw [Eg_eq_Qns, card_Qns]

theorem card_Tg : Nat.card Tg = 256 :=
  Certificates.certificate778702.2.2.2.2.1

theorem card_Ag : Nat.card Ag = 32 :=
  Certificates.certificate778702.2.2.2.2.2.1

theorem mem_Ag {g : Mns} : g ∈ Ag ↔ g ∈ bfsList gensA 60 :=
  Certificates.certificate778702.2.2.2.2.2.2.2.1 g

theorem mem_Lg {g : Mns} : g ∈ Lg ↔ g ∈ bfsList gensL 40 :=
  Certificates.certificate778702.2.2.2.2.2.2.2.2.1 g

theorem gensA_sub : ∀ g ∈ gensA, g ∈ gensT := by
  simp [gensA, gensT]

theorem Ag_le_Tg : Ag ≤ Tg := by
  rw [Ag, Subgroup.closure_le]
  intro g hg
  exact Subgroup.subset_closure (gensA_sub g hg)

theorem Tg_isSylow : ∃ S : Sylow 2 Mns, (S : Subgroup Mns) = Tg := by
  refine ⟨Sylow.ofCard Tg ?_, rfl⟩
  rw [card_Tg, card_Mns]
  rw [show (11520 : ℕ) = 2 ^ 8 * 45 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem Ag_commutative : IsMulCommutative Ag :=
  Certificates.certificate778702.2.2.2.2.2.2.2.2.2.1

theorem Ag_sup_Lg : Ag ⊔ Lg = NAg :=
  Certificates.certificate778702.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Lg_le_normalizer : Lg ≤ NAg := by
  rw [← Ag_sup_Lg]
  exact le_sup_right

theorem mem_normalizer_iff_normB {g : Mns} : g ∈ NAg ↔ normB g = true := by
  constructor
  · intro hg
    simp only [normB, List.all_eq_true, decide_eq_true_eq]
    intro a ha
    exact mem_Ag.1 ((Subgroup.mem_set_normalizer_iff.1 hg a).1
      (Subgroup.subset_closure ha))
  · intro h
    simp only [normB, List.all_eq_true, decide_eq_true_eq] at h
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hle : Ag ≤ Ag.comap (MulAut.conj g).toMonoidHom := by
      rw [Ag, Subgroup.closure_le]
      intro a ha
      exact mem_Ag.2 (h a ha)
    exact hle hn

theorem strothT_mem_sup_mul {A B : Subgroup Mns} (hBA : B ≤ Subgroup.normalizer (A : Set Mns))
    {x : Mns} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup Mns :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * (b * a' * b⁻¹), A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) a').mp
          ha'), b * b', B.mul_mem hb hb', by group⟩
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer _).inv_mem (hBA hb)) a⁻¹).mp (A.inv_mem ha), b⁻¹, B.inv_mem hb,
          by group⟩ }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem normB_decomp : ∀ g : Mns, normB g = true → ∃ l ∈ bfsList gensL 40,
    g * l⁻¹ ∈ bfsList gensA 60 := by
  intro g hg
  rw [← mem_normalizer_iff_normB, ← Ag_sup_Lg] at hg
  obtain ⟨a, ha, l, hl, rfl⟩ := strothT_mem_sup_mul Lg_le_normalizer hg
  refine ⟨l, mem_Lg.1 hl, ?_⟩
  rw [mul_inv_cancel_right]
  exact mem_Ag.1 ha

end CFSG.CGT.Stroth77
