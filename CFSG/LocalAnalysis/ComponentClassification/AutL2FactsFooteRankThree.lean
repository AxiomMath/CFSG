module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupA7
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup Equiv

@[expose] def a7AutEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective a7Conj
    ⟨CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by norm_num),
      fun f => exists_a7Conj_eq f⟩

theorem perm7_card_le_eight_of_sq (E : Subgroup (Perm (Fin 7))) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := isPGroup_two_of_forall_sq E hE
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2
  have hcard : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hdvd : 2 ^ k ∣ 5040 := by
    rw [← hk, ← hcard]
    exact E.card_subgroup_dvd_card
  have hk4 : k ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  by_contra hlt
  have hk4' : k = 4 := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hidx : ¬ 2 ∣ E.index := by
    have h1 := E.card_mul_index
    rw [hk, hk4', hcard] at h1
    omega
  set P := hE2.toSylow hidx
  obtain ⟨H, hH2, x, hx, y, hy, hxy⟩ := exists_noncomm_two_subgroup_a7
  set H' := H.map (alternatingGroup (Fin 7)).subtype
  have hH'2 : IsPGroup 2 H' := hH2.map _
  obtain ⟨Q, hQ⟩ := hH'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) Q P
  have hmem : ∀ z ∈ H, g * (z : Perm (Fin 7)) * g⁻¹ ∈ E := by
    intro z hz
    have h1 : g * (z : Perm (Fin 7)) * g⁻¹ ∈ (P : Subgroup (Perm (Fin 7))) := by
      rw [← hg, mem_smul_sylow_iff_conj, show g⁻¹ * (g * (z : Perm (Fin 7)) * g⁻¹) * g =
        (z : Perm (Fin 7)) by group]
      exact hQ ⟨z, hz, rfl⟩
    exact h1
  have hc := commute_of_forall_sq E hE (hmem x hx) (hmem y hy)
  apply hxy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  calc (x : Perm (Fin 7)) * y
      = g⁻¹ * (g * (x : Perm (Fin 7)) * g⁻¹ * (g * (y : Perm (Fin 7)) * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * (y : Perm (Fin 7)) * g⁻¹ * (g * (x : Perm (Fin 7)) * g⁻¹)) * g := by rw [hc]
    _ = (y : Perm (Fin 7)) * x := by group

theorem footeAutRankThree :
    ∀ (S : Type) [Group S] [Finite S],
      (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
      ∀ E : Subgroup (MulAut S), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 8 := by
  intro S _ _ hS E hE
  rcases hS with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · set Ψ : MulAut S ≃* Perm (Fin 7) := (MulAut.congr e).trans a7AutEquiv.symm
    rw [← Subgroup.card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective]
    apply perm7_card_le_eight_of_sq
    rintro _ ⟨x, hx, rfl⟩
    change Ψ x * Ψ x = 1
    rw [← map_mul, hE x hx, map_one]
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
    rw [← Subgroup.card_map_of_injective (f := (autEquiv e).toMonoidHom) (autEquiv e).injective]
    apply pGammaL2_card_le_eight_of_sq (isOddPrimePower_of hp hp2 hf hF)
    rintro _ ⟨x, hx, rfl⟩
    change autEquiv e x * autEquiv e x = 1
    rw [← map_mul, hE x hx, map_one]

end CFSG.ComponentClassification.AutL2Facts
