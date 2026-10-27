module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YHCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YERest

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T CFSG.StandardType
  CFSG.StandardType.Triality

section Emb

variable {H : Type} [Group H] [Finite H] {K : Subgroup H}

@[expose] def FixEmb (K : Subgroup H) (c : H) (J : Type) [Group J] : Prop :=
  ∃ j : J →* H, Function.Injective j ∧ (∀ x, j x ∈ K) ∧ ∀ x, c * j x = j x * c

theorem fixEmb_transport {J : Type} [Group J] {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (Φ : ↥K ≃* Om8 K₀) {c : H} (hcN : c ∈ Subgroup.normalizer (K : Set H)) (j : J →* Om8 K₀)
    (hj : Function.Injective j) (hfix : ∀ x, (MulAut.congr Φ (conjAut K c hcN)) (j x) = j x) :
    FixEmb K c J := by
  refine ⟨K.subtype.comp (Φ.symm.toMonoidHom.comp j),
    K.subtype_injective.comp (Φ.symm.injective.comp hj), fun x => (Φ.symm (j x)).2, fun x => ?_⟩
  have h1 : Φ (conjAut K c hcN (Φ.symm (j x))) = j x := hfix x
  have h2 : conjAut K c hcN (Φ.symm (j x)) = Φ.symm (j x) :=
    Φ.injective (h1.trans (Φ.apply_symm_apply _).symm)
  have h3 := congrArg Subtype.val h2
  change c * (Φ.symm (j x) : H) * c⁻¹ = (Φ.symm (j x) : H) at h3
  change c * (Φ.symm (j x) : H) = (Φ.symm (j x) : H) * c
  calc c * (Φ.symm (j x) : H) = c * (Φ.symm (j x) : H) * c⁻¹ * c := by group
    _ = (Φ.symm (j x) : H) * c := by rw [h3]

theorem FixEmb.rank4 {c : H} {J : Type} [Group J] (h : FixEmb K c J)
    (hJ : ∃ E : Subgroup J, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) :
    ∃ E : Subgroup H, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ ∀ y ∈ E, c * y = y * c := by
  obtain ⟨j, hj, hjK, hjc⟩ := h
  obtain ⟨E, hE, hEc⟩ := hJ
  refine ⟨E.map j, ?_, CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map j hE, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hjK x
  · rw [Subgroup.card_map_of_injective hj, hEc]
  · rintro _ ⟨x, -, rfl⟩
    exact hjc x

theorem FixEmb.rankW {c : H} {J : Type} [Group J] (h : FixEmb K c J) {m : ℕ}
    (hJ : ∃ E W : Subgroup J, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ m ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (W : Set J)) :
    ∃ E W : Subgroup H, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ m ∧ (∀ y ∈ E, c * y = y * c) ∧
      IsPGroup 2 W ∧ W ≠ ⊥ ∧ E ≤ Subgroup.normalizer (W : Set H) ∧
      c ∈ Subgroup.normalizer (W : Set H) ∧ W ≤ K := by
  obtain ⟨j, hj, hjK, hjc⟩ := h
  obtain ⟨E, W, hE, hEc, hW2, hWne, hEW⟩ := hJ
  refine ⟨E.map j, W.map j, ?_, CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map j hE, ?_, ?_,
    hW2.map j, fun h => hWne ((Subgroup.map_eq_bot_iff_of_injective W hj).1 h), ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hjK x
  · rw [Subgroup.card_map_of_injective hj, hEc]
  · rintro _ ⟨x, -, rfl⟩
    exact hjc x
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.le_normalizer_map j (Subgroup.mem_map_of_mem _ (hEW hy))
  · refine mem_normalizer_of_centralizes ?_
    rintro _ ⟨x, -, rfl⟩
    exact hjc x
  · rintro _ ⟨x, -, rfl⟩
    exact hjK x

end Emb

end CFSG.LocalAnalysis.GLTheoremA.D4Y
