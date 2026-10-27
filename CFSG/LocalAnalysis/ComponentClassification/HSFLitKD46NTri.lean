module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NCompat

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

include S in
theorem card_T_64 : Nat.card A.T = 64 := by rw [card_T_eq S, card_TE S]

theorem x_y_ne : S.x * S.y ≠ S.y * S.x := by
  intro h
  have h1 : S.y * S.x * S.y⁻¹ = S.x := by rw [← h]; group
  rw [S.y_inv] at h1
  apply x_sq_ne_one S
  calc S.x ^ 2 = S.x * S.x := pow_two _
    _ = S.x⁻¹ * S.x := by rw [h1]
    _ = 1 := inv_mul_cancel _

include S in
theorem not_conjTo_of_comm {B' : Subgroup X} (hB' : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a)
    (hcard : Nat.card B' = 64) {q : X} (hq : q ∈ B') : ¬ ConjTo t q := by
  rintro ⟨g, hg⟩
  set A' := B'.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have htA : t ∈ A' := ⟨q, hq, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; rw [← hg]; group⟩
  have hA'C : A' ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨q', hq', hq'e⟩ := htA
    rw [mem_centralizer_singleton_iff, ← hq'e]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hB' a ha q' hq']
  have hcard' : Nat.card A' = 64 := by
    rw [hA', card_map_of_injective (MulAut.conj _).injective, hcard]
  have hp : IsPGroup 2 A' := IsPGroup.of_card (n := 6) (by rw [hcard']; norm_num)
  obtain ⟨h, -, hT⟩ := exists_conj_le_T (A := A) hp hA'C
  have hc : Nat.card (A'.map (MulAut.conj h).toMonoidHom) = 64 := by
    have h1 : Nat.card (A'.map (MulAut.conj h).toMonoidHom) = Nat.card A' :=
      card_map_of_injective (MulAut.conj h).injective
    rw [h1, hcard']
  have heq : A'.map (MulAut.conj h).toMonoidHom = A.T :=
    eq_of_le_of_card_ge hT (by rw [hc, card_T_64 S])
  have hcomm : ∀ a ∈ A.T, ∀ b ∈ A.T, a * b = b * a := by
    rw [← heq]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hB' a ha b hb]
  exact x_y_ne S (hcomm _ (x_mem_T S) _ (y_mem_T S))

end CFSG.ComponentClassification.HSFLit.KD46
