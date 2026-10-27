module

public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Semidihedral.Local

open QuaternionGroup

theorem kleinFour_automorphism_action {V : Type*} [Group V] [IsKleinFour V] :
    (∃ e : MulAut V ≃* Equiv.Perm {x : V // x ≠ 1}, ∀ φ x, (e φ x : V) = φ x) ∧
      Nat.card (MulAut V) = 6 ∧
      (∀ N : Subgroup (MulAut V), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (∀ H K : Subgroup (MulAut V), K ≤ H → Nat.card K = 2 → Nat.card H = 2 ∨ H = ⊤) := by
  obtain ⟨ψ⟩ := nonempty_mulAut_equiv_perm_three (V := V)
  have hcard : Nat.card (MulAut V) = 6 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have : Finite (MulAut V) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨⟨MulEquiv.ofBijective _ nontrivialPerm_bijective, fun φ x => rfl⟩, hcard,
    fun N hN h2 => normal_isPGroup_two_eq_bot ψ N hN h2, fun H K hKH hK => ?_⟩
  exact card_eq_or_eq_top_of_le (by norm_num) (by rw [hcard]) hKH hK

theorem quaternionEight_automorphism_action {Q : Type*} [Group Q]
    (hQ : Nonempty (Q ≃* QuaternionGroup 2)) :
    Nat.card {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} = 3 ∧
      Nat.card (MulAut Q) = 24 ∧
      (∃ ρ : MulAut Q →* Equiv.Perm {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4},
        (∀ φ H, (ρ φ H : Subgroup Q) = (H : Subgroup Q).map φ.toMonoidHom) ∧
        Function.Surjective ρ ∧ ρ.ker = (MulAut.conj : Q →* MulAut Q).range) ∧
      Nat.card (MulAut.conj : Q →* MulAut Q).range = 4 ∧
      (MulAut.conj : Q →* MulAut Q).range.Normal ∧
      IsPGroup 2 (MulAut.conj : Q →* MulAut Q).range ∧
      (∀ N : Subgroup (MulAut Q), N.Normal → IsPGroup 2 N →
        N ≤ (MulAut.conj : Q →* MulAut Q).range) ∧
      (∀ H K : Subgroup (MulAut Q), K ≤ H → Nat.card K = 8 → Nat.card H = 8 ∨ H = ⊤) := by
  obtain ⟨e⟩ := hQ
  have := finite_of_equiv e
  have hX := card_cyclicFour_of_equiv e
  have hAut := card_mulAut_of_equiv e
  have hInn := card_inner_of_equiv e
  have : Finite (MulAut Q) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have : Finite {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hker : (cyclicFourAction Q).ker = (MulAut.conj : Q →* MulAut Q).range := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (inner_le_ker_cyclicFourAction e)
    rw [hInn]
    exact card_ker_cyclicFourAction_le e
  have hsurj : Function.Surjective (cyclicFourAction Q) := by
    rw [← MonoidHom.range_eq_top, ← Subgroup.card_eq_iff_eq_top]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (cyclicFourAction Q).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hker, hInn, hAut] at h1
    rw [Nat.card_perm, hX]
    have h6 : Nat.card (cyclicFourAction Q).range = 6 := by omega
    rw [h6]
    rfl
  obtain ⟨ψ⟩ : Nonempty (Equiv.Perm {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} ≃*
      Equiv.Perm (Fin 3)) := ⟨(Finite.equivFinOfCardEq hX).permCongrHom⟩
  refine ⟨hX, hAut, ⟨cyclicFourAction Q, fun φ H => rfl, hsurj, hker⟩, hInn, ?_, ?_, ?_, ?_⟩
  · rw [← hker]
    exact MonoidHom.normal_ker _
  · exact IsPGroup.of_card (n := 2) (by rw [hInn]; rfl)
  · intro N hN h2
    rw [← hker, ← Subgroup.map_eq_bot_iff]
    exact normal_isPGroup_two_eq_bot ψ _ (hN.map _ hsurj) (h2.map _)
  · intro H K hKH hK
    exact card_eq_or_eq_top_of_le (by norm_num) (by rw [hAut]) hKH hK

theorem four_and_quaternion_eight_automorphism_actions {V : Type*} [Group V] [IsKleinFour V]
    {Q : Type*} [Group Q] (hQ : Nonempty (Q ≃* QuaternionGroup 2)) :
    ((∃ e : MulAut V ≃* Equiv.Perm {x : V // x ≠ 1}, ∀ φ x, (e φ x : V) = φ x) ∧
      Nat.card (MulAut V) = 6 ∧
      (∀ N : Subgroup (MulAut V), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (∀ H K : Subgroup (MulAut V), K ≤ H → Nat.card K = 2 → Nat.card H = 2 ∨ H = ⊤)) ∧
    (Nat.card {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} = 3 ∧
      Nat.card (MulAut Q) = 24 ∧
      (∃ ρ : MulAut Q →* Equiv.Perm {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4},
        (∀ φ H, (ρ φ H : Subgroup Q) = (H : Subgroup Q).map φ.toMonoidHom) ∧
        Function.Surjective ρ ∧ ρ.ker = (MulAut.conj : Q →* MulAut Q).range) ∧
      Nat.card (MulAut.conj : Q →* MulAut Q).range = 4 ∧
      (MulAut.conj : Q →* MulAut Q).range.Normal ∧
      IsPGroup 2 (MulAut.conj : Q →* MulAut Q).range ∧
      (∀ N : Subgroup (MulAut Q), N.Normal → IsPGroup 2 N →
        N ≤ (MulAut.conj : Q →* MulAut Q).range) ∧
      (∀ H K : Subgroup (MulAut Q), K ≤ H → Nat.card K = 8 → Nat.card H = 8 ∨ H = ⊤)) :=
  ⟨kleinFour_automorphism_action, quaternionEight_automorphism_action hQ⟩

end CFSG.Semidihedral.Local
