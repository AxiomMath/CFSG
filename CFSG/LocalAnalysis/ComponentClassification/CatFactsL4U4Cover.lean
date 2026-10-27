module

public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix CFSG.Assembly.LowTwoRank

theorem eq_one_or_eq_neg_one_of_pow_four {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F % 4 = 3) {r : F} (hr : r ^ 4 = 1) : r = 1 ∨ r = -1 := by
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at hr
  have hq := FiniteField.pow_card_sub_one_eq_one r hr0
  obtain ⟨t, ht⟩ : ∃ t, Fintype.card F - 1 = 4 * t + 2 := ⟨(Fintype.card F - 1) / 4, by omega⟩
  rw [ht, pow_add, pow_mul, hr, one_pow, one_mul] at hq
  exact mul_self_eq_one_iff.1 (by rw [← pow_two]; exact hq)

theorem card_center_SL_four_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F % 4 = 3) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 4) F)) ≤ 2 := by
  classical
  let f : Subgroup.center (SpecialLinearGroup (Fin 4) F) → ({1, -1} : Finset F) := fun A =>
    ⟨(A : SpecialLinearGroup (Fin 4) F) 0 0, by
      obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 A.2
      rw [← hA, Fintype.card_fin] at *
      rcases eq_one_or_eq_neg_one_of_pow_four hF hr with h | h <;> simp [h]⟩
  have hf : Function.Injective f := by
    intro A B hAB
    obtain ⟨r, -, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 A.2
    obtain ⟨s, -, hB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 B.2
    have h1 : (A : SpecialLinearGroup (Fin 4) F) 0 0 = (B : SpecialLinearGroup (Fin 4) F) 0 0 :=
      congrArg Subtype.val hAB
    rw [← hA, ← hB] at h1
    simp only [scalar_apply, diagonal_apply_eq] at h1
    apply Subtype.ext
    apply Subtype.ext
    rw [← hA, ← hB, h1]
  have := Nat.card_le_card_of_injective f hf
  refine this.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (Finset.card_insert_le _ _).trans (by simp)

theorem exists_equiv_statedSL_four {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ2 : IsPGroup 2 (Subgroup.center Y)) (hZ : Subgroup.center Y ≠ ⊥) {F : Type} [Field F]
    [Fintype F] [DecidableEq F] (hF : Fintype.card F % 4 = 3)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL 4 F)) :
    ∃ ψ : Y ≃* StatedSL 4 F, ∀ y : Y,
      e (QuotientGroup.mk y) = QuotientGroup.mk (ψ y) := by
  have hk : ringChar F ≠ 2 := by
    intro h
    have := FiniteField.even_card_iff_char_two.1 h
    omega
  set ι := specialLinearGroupEquivStatedSL 4 F with hι
  set β : SpecialLinearGroup (Fin 4) F →* StatedProj (StatedSL 4 F) :=
    (QuotientGroup.mk' _).comp ι.toMonoidHom with hβ
  set η : Y →* StatedProj (StatedSL 4 F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hη
  have hβs : Function.Surjective β :=
    (QuotientGroup.mk'_surjective _).comp ι.surjective
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SpecialLinearGroup (Fin 4) F),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
        ∃ σ : SpecialLinearGroup (Fin 4) F →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker h2
    obtain ⟨σ, hσ, -, -⟩ := LieType.Steinberg.sl_central_two_extension_splitting 3 hk hπ hker h2
    exact ⟨σ, hσ⟩
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβs hηs
    (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hβker : β.ker = Subgroup.center (SpecialLinearGroup (Fin 4) F) := by
    ext A
    rw [MonoidHom.mem_ker, hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← map_center_eq_statedScalars 4 F]
    constructor
    · rintro ⟨B, hB, hBA⟩
      rwa [ι.injective hBA] at hB
    · intro hA
      exact ⟨A, hA, rfl⟩
  have hαβ : α.ker ≤ β.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    rw [← hα, hA, map_one]
  have hne : α.ker ≠ β.ker := by
    intro h
    apply hZ
    rw [← hηker, hker, ← h, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hcard := card_center_SL_four_le hF
  rw [← hβker] at hcard
  have hdvd : Nat.card α.ker ∣ Nat.card β.ker := Subgroup.card_dvd_of_le hαβ
  have hpos : 0 < Nat.card α.ker := Nat.card_pos
  have h1 : Nat.card α.ker = 1 := by
    by_contra h1
    have h2 : 2 ≤ Nat.card α.ker := by omega
    have hle : Nat.card β.ker ≤ Nat.card α.ker := by
      have := Nat.le_of_dvd (Nat.card_pos) hdvd
      omega
    exact hne (Subgroup.eq_of_le_of_card_ge hαβ hle)
  have hbot : α.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).1 hbot
  refine ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm.trans ι, fun y => ?_⟩
  set A := (MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm y with hA
  have hy : α A = y := MulEquiv.ofBijective_apply_symm_apply α ⟨hinj, hαs⟩
  have h3 : η (α A) = β A := hα A
  rw [hy] at h3
  exact h3

end CFSG.ComponentClassification.CatFactsL4U4
