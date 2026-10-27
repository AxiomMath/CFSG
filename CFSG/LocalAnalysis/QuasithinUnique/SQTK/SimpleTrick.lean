module

public import CFSG.Sporadic.Bridge.Common
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Interface
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Sporadic.Bridge CFSG.Open TauCeti

section Trick

variable {P N : Type*} [Group P] [Group N]

theorem injective_of_isSimpleGroup_of_ne_one [IsSimpleGroup P] (φ : P →* N) (h : φ ≠ 1) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
  · exact hk
  · exact absurd (MonoidHom.ext fun x => MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top x)) h

theorem injective_of_isSimpleGroup_of_surjective [IsSimpleGroup P] [Nontrivial N] (φ : P →* N)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  refine injective_of_isSimpleGroup_of_ne_one φ fun h => ?_
  obtain ⟨y, hy⟩ := exists_ne (1 : N)
  obtain ⟨x, rfl⟩ := hφ y
  exact hy (by rw [h]; rfl)

@[expose] noncomputable def mulEquivOfSurjective [IsSimpleGroup P] [Nontrivial N] (φ : P →* N)
    (hφ : Function.Surjective φ) : P ≃* N :=
  MulEquiv.ofBijective φ ⟨injective_of_isSimpleGroup_of_surjective φ hφ, hφ⟩

end Trick

theorem nontrivial_of_two_le_natCard {J : Type*} {k : ℕ} (hk : 2 ≤ k) (h : k ≤ Nat.card J) :
    Nontrivial J :=
  have := Nat.finite_of_card_ne_zero (show Nat.card J ≠ 0 by omega)
  Finite.one_lt_card_iff_nontrivial.1 (by omega)

section Presentation

theorem nonempty_mulEquiv_of_relators (P : GroupPresentation) [IsSimpleGroup P.Group] {N : Type*}
    [Group N] [Nontrivial N] (img : ℕ → N) (hrel : ∀ v ∈ P.relatorLetters, wordProd img v = 1)
    (hgen : Subgroup.closure (img '' Set.Iio P.generatorCount) = ⊤) :
    Nonempty (P.Group ≃* N) := by
  have hsurj : Function.Surjective (presHom P img hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨presGen P i, presHom_presGen P img hrel hi⟩
  exact ⟨mulEquivOfSurjective _ hsurj⟩

theorem nonempty_mulEquiv_of_relators_two (P : GroupPresentation) [IsSimpleGroup P.Group]
    (hP : P.generatorCount = 2) {N : Type*} [Group N] [Nontrivial N] {x y : N}
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (fun i => if i = 0 then x else y) v = 1)
    (hgen : Subgroup.closure ({x, y} : Set N) = ⊤) : Nonempty (P.Group ≃* N) := by
  refine nonempty_mulEquiv_of_relators P (fun i => if i = 0 then x else y) hrel ?_
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, Set.mem_Iio.2 (by omega), by simp⟩
  · exact Subgroup.subset_closure ⟨1, Set.mem_Iio.2 (by omega), by simp⟩

end Presentation

section Witness

theorem exists_isElemAbelian_card_three_pow_three {T : Type*} [Group T] {E : Subgroup T}
    (hE : IsElemAbelian 3 E) {k : ℕ} (hk : 3 ≤ k) (hc : Nat.card E = 3 ^ k) :
    ∃ E' : Subgroup T, IsElemAbelian 3 E' ∧ Nat.card E' = 3 ^ 3 := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 3)
    (by rw [hc]; exact pow_dvd_pow 3 hk)
  have hcomm := hE.1
  refine ⟨K.map E.subtype, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hbz⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : T) * b = b * a
    rw [← hax, ← hbz]
    exact congrArg (fun w : E => (w : T)) (mul_comm' x z)
  · obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact hE.2 x x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]

theorem tcExcludedSporadic_of_equiv (s : TauCeti.SporadicName) {T : Type} [Group T]
    (e : IsSimpleGroup s.Group → Nonempty (s.Group ≃* T))
    (hw : ∃ E : Subgroup T, IsElemAbelian 3 E ∧ ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k) :
    TCExcludedSporadic s := by
  intro G _ _ _ _ ⟨eG⟩
  have hs : IsSimpleGroup s.Group := eG.symm.isSimpleGroup
  obtain ⟨eT⟩ := e hs
  obtain ⟨E, hE, k, hk, hc⟩ := hw
  obtain ⟨E₃, hE₃, hc₃⟩ := exists_isElemAbelian_card_three_pow_three hE hk hc
  let φ : T ≃* G := eT.symm.trans eG.symm
  exact ⟨3, Nat.prime_three, by norm_num, E₃.map φ.toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map hE₃ _, by
      rw [Subgroup.card_map_of_injective φ.injective, hc₃]⟩

end Witness

end CFSG.QuasithinUnique.SQTK
