module

public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsFin

public section

namespace CFSG.AGLEmbedding

open Subgroup

variable {A V : Type*} [CommGroup A] [Finite A] [CommGroup V] [Finite V]
  [MulDistribMulAction A V]

omit [Finite A] [Finite V] in
theorem fixedPiece_map_ne_bot {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v) {F : Subgroup A}
    (hF : (fixedPiece F : Subgroup V) ≠ ⊥) :
    (fixedPiece (F.map α.toMonoidHom) : Subgroup V) ≠ ⊥ := by
  intro hbot
  obtain ⟨w, hw, hw1⟩ := (bot_or_exists_ne_one _).resolve_left hF
  have hmem := map_fixedPiece_le hαβ F ⟨w, hw, rfl⟩
  rw [hbot, mem_bot] at hmem
  exact hw1 (β.injective (hmem.trans (map_one _).symm))

omit [MulDistribMulAction A V] in
theorem coprime_card_of_exponent {s p : ℕ} [Fact s.Prime] [Fact p.Prime] (hsp : s ≠ p)
    (hA : ∀ a : A, a ^ p = 1) (hV : ∀ v : V, v ^ s = 1) :
    Nat.Coprime (Nat.card A) (Nat.card V) := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
  have hVp : IsPGroup s V := fun v => ⟨1, by rw [pow_one]; exact hV v⟩
  obtain ⟨m, hm⟩ := hAp.exists_card_eq
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  rw [hm, hn]
  exact Nat.coprime_pow_primes m n hp hs hsp.symm

omit [Finite A] [Finite V] in
theorem index_map_eq {α : MulAut A} {F : Subgroup A} (hF : F.index = 5) :
    (F.map α.toMonoidHom).index = 5 := by
  rw [MulEquiv.toMonoidHom_eq_coe, index_map_equiv]
  exact hF

omit [Finite V] in
theorem eq_one_of_smul_eq_of_mem_fixedPiece (c : Fin 3 → A) (hAc : closure (Set.range c) = ⊤)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) {i : Fin 3} {w : V}
    (hw : w ∈ (fixedPiece (coordPlane c i) : Subgroup V)) (hfix : c i • w = w) : w = 1 := by
  have hstab : (⊤ : Subgroup A) ≤ MulAction.stabilizer A w := by
    rw [← coordPlane_sup_zpowers c hAc i]
    exact sup_le (fun b hb => fixedPiece_le_fixedBy _ hw b hb) (zpowers_le.mpr hfix)
  have htop : Nat.Coprime (Nat.card (⊤ : Subgroup A)) (Nat.card V) := by
    rwa [card_top]
  have hmem : w ∈ actCommutator (⊤ : Subgroup V) (⊤ : Subgroup A) ⊓
      fixedBy (⊤ : Subgroup A) :=
    ⟨actCommutator_mono le_top le_rfl hw, fun a _ => hstab (mem_top a)⟩
  rwa [actCommutator_top_inf_fixedBy htop, mem_bot] at hmem

theorem exists_orthogonal_of_injective {Z : Type*} [CommGroup Z] {s : ℕ} [Fact s.Prime]
    (hs5 : s ≠ 5) (hA : ∀ a : A, a ^ 5 = 1) (hV : ∀ v : V, v ^ s = 1) (B : V →* V →* Z)
    (hB : ∀ (a : A) (v w : V), B (a • v) (a • w) = B v w) (halt : ∀ v, B v v = 1)
    {F : Fin 4 → Subgroup A} (hinj : Function.Injective F) (hF : ∀ j, (F j).index = 5)
    (hne : ∀ j, (fixedPiece (F j) : Subgroup V) ≠ ⊥) :
    ∃ v : Fin 4 → V, (∀ j k, B (v j) (v k) = 1) ∧ s ^ 4 ≤ Nat.card (closure (Set.range v)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcop := coprime_card_of_exponent hs5 hA hV
  have hVp : IsPGroup s V := fun v => ⟨1, by rw [pow_one]; exact hV v⟩
  choose w hw hw1 using fun j =>
    (bot_or_exists_ne_one (fixedPiece (F j) : Subgroup V)).resolve_left (hne j)
  refine ⟨w, fun j k => ?_, ?_⟩
  · by_cases hjk : j = k
    · rw [hjk]
      exact halt _
    · exact pairing_fixedPiece_eq_one Fact.out hcop B hB (hF j) (hF k) (hinj.ne hjk) (hw j) (hw k)
  · simpa using pow_card_le_card_closure_of_fixedPiece Fact.out hVp hcop hinj hF hw hw1

section Monomial

variable {s : ℕ} [Fact s.Prime] (c : Fin 3 → A) {ασ ατ : MulAut A} {βσ βτ : MulAut V}

omit [Finite V] in
theorem exists_injective_of_support_two (hA : ∀ a : A, a ^ 5 = 1)
    (hAc : closure (Set.range c) = ⊤) (hAcard : Nat.card A = 5 ^ 3)
    (hσ : ∀ a v, βσ (a • v) = ασ a • βσ v) (hσc : ∀ i, ασ (c i) = c (i + 1))
    (hτ : ∀ a v, βτ (a • v) = ατ a • βτ v)
    (hτc : ατ (c 0) = c 0 ^ 2 ∧ ατ (c 1) = c 1 ∧ ατ (c 2) = c 2 ^ 2) {F : Subgroup A}
    (hF : F.index = 5) (hne : (fixedPiece F : Subgroup V) ≠ ⊥) {i : Fin 3} (hi : c i ∉ F)
    (hi' : ¬ (c (i + 1) ∈ F ∧ c (i + 2) ∈ F)) :
    ∃ F' : Fin 4 → Subgroup A, Function.Injective F' ∧ (∀ j, (F' j).index = 5) ∧
      ∀ j, (fixedPiece (F' j) : Subgroup V) ≠ ⊥ := by
  obtain ⟨k, h1, h20⟩ := exists_pow_not_mem_of_cycle c hσc hi hi'
  have hF₁ := index_map_eq (α := ασ ^ k) hF
  have hne₁ := fixedPiece_map_ne_bot (pow_apply_smul hσ k) hne
  exact ⟨fun j => (F.map (ασ ^ k).toMonoidHom).map (ατ ^ (j : ℕ)).toMonoidHom,
    injective_map_pow_of_diag c hτc hA hAc hAcard hF₁ h1 h20, fun j => index_map_eq hF₁,
    fun j => fixedPiece_map_ne_bot (pow_apply_smul hτ j) hne₁⟩

theorem exists_injective_or_forall_coordPlane (hs5 : s ≠ 5) (hA : ∀ a : A, a ^ 5 = 1)
    (hAc : closure (Set.range c) = ⊤) (hAcard : Nat.card A = 5 ^ 3) (hV : ∀ v : V, v ^ s = 1)
    (hσ : ∀ a v, βσ (a • v) = ασ a • βσ v) (hσc : ∀ i, ασ (c i) = c (i + 1))
    (hτ : ∀ a v, βτ (a • v) = ατ a • βτ v)
    (hτc : ατ (c 0) = c 0 ^ 2 ∧ ατ (c 1) = c 1 ∧ ατ (c 2) = c 2 ^ 2)
    (hnt : ∃ (a : A) (v : V), a • v ≠ v) :
    (∃ F' : Fin 4 → Subgroup A, Function.Injective F' ∧ (∀ j, (F' j).index = 5) ∧
      ∀ j, (fixedPiece (F' j) : Subgroup V) ≠ ⊥) ∨
      ∀ j, (fixedPiece (coordPlane c j) : Subgroup V) ≠ ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5V : ¬ 5 ∣ Nat.card V := fun h => by
    have hcop := coprime_card_of_exponent hs5 hA hV
    rw [hAcard] at hcop
    have hc5 : Nat.Coprime 5 (Nat.card V) :=
      Nat.Coprime.coprime_dvd_left (dvd_pow_self 5 (by norm_num)) hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hc5 h) (by norm_num)
  obtain ⟨F, hF, hne⟩ := exists_fixedPiece_ne_bot hA h5V hnt
  rcases eq_coordPlane_or_exists_not_mem c hA hAc hAcard hF with ⟨i, rfl⟩ | ⟨i, hi, hi'⟩
  · refine Or.inr fun j => ?_
    obtain ⟨k, hk⟩ := exists_map_pow_coordPlane_of_cycle c hσc i j
    rw [← hk]
    exact fixedPiece_map_ne_bot (pow_apply_smul hσ k) hne
  · exact Or.inl (exists_injective_of_support_two c hA hAc hAcard hσ hσc hτ hτc hF hne hi hi')

end Monomial

end CFSG.AGLEmbedding
