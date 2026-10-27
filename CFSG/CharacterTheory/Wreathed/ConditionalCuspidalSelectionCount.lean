module

public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesCount

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2

section Cyclic

variable (Γ : Type) [CommGroup Γ] [Finite Γ] [IsCyclic Γ]

theorem card_two_pow_hom_units :
    Nat.card {α : Γ →* ℂˣ // ∃ k : ℕ, orderOf α = 2 ^ k} =
      2 ^ (Nat.card Γ).factorization 2 := by
  have := finite_hom_units_of_isCyclic Γ
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Γ ℂ
  have : IsCyclic (Γ →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  rw [card_two_pow_orderOf_of_isCyclic, card_hom_units_of_isCyclic]

theorem card_two_pow_hom_units_ne_one :
    Nat.card {α : Γ →* ℂˣ // (∃ k : ℕ, orderOf α = 2 ^ k) ∧ α ≠ 1} =
      2 ^ (Nat.card Γ).factorization 2 - 1 := by
  have := finite_hom_units_of_isCyclic Γ
  let : Fintype (Γ →* ℂˣ) := Fintype.ofFinite _
  rw [← card_two_pow_hom_units Γ]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsplit : (Finset.univ.filter fun α : Γ →* ℂˣ => ∃ k : ℕ, orderOf α = 2 ^ k) =
      insert 1 (Finset.univ.filter fun α : Γ →* ℂˣ => (∃ k : ℕ, orderOf α = 2 ^ k) ∧ α ≠ 1) := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases h1 : α = 1
      · exact Or.inl h1
      · exact Or.inr ⟨h, h1⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact ⟨0, by rw [orderOf_one, pow_zero]⟩
      · exact h
  rw [hsplit, Finset.card_insert_of_notMem (by simp)]
  simp

end Cyclic

section Parameters

theorem card_nonsplitParameter_filter (F : Type) [Field F] [Fintype F] (E : Type) [Field E]
    [Algebra F E] (basis : Module.Basis (Fin 2) F E) (b : Fˣ) {m : ℕ} (hm : 0 < m)
    (h2 : (2 : F) ≠ 0) (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)
    (Q : (normOne F E →* ℂˣ) → Prop) :
    Nat.card {P : NonsplitParameter F E b m h2 z hz // Q P.1.1} =
      Nat.card {α : normOne F E →* ℂˣ // Q α} * m := by
  have := finite_of_basis F E basis
  have := finite_hom_units_of_isCyclic (normOne F E)
  let e : {P : NonsplitParameter F E b m h2 z hz // Q P.1.1} ≃
      (α : {α : normOne F E →* ℂˣ // Q α}) × {w : ℂˣ // w ^ m = α.1 (cMinus F E b m h2 z hz)} :=
    { toFun := fun P => ⟨⟨P.1.1.1, P.2⟩, ⟨P.1.1.2, P.1.2⟩⟩
      invFun := fun x => ⟨⟨(x.1.1, x.2.1), x.2.2⟩, x.1.2⟩
      left_inv := fun P => rfl
      right_inv := fun x => rfl }
  have hfin : ∀ α : {α : normOne F E →* ℂˣ // Q α},
      Finite {w : ℂˣ // w ^ m = α.1 (cMinus F E b m h2 z hz)} := fun α =>
    Nat.finite_of_card_ne_zero (by rw [card_pow_eq m hm]; exact hm.ne')
  let : Fintype {α : normOne F E →* ℂˣ // Q α} := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [card_pow_eq m hm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem card_two_pow_nonsplitParameter (F : Type) [Field F] [Fintype F] (E : Type) [Field E]
    [Algebra F E] (basis : Module.Basis (Fin 2) F E) (b : Fˣ) {m : ℕ} (hm : 0 < m)
    (h2 : (2 : F) ≠ 0) (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    Nat.card {P : NonsplitParameter F E b m h2 z hz //
      P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k} =
      m * (2 ^ (Nat.card F + 1).factorization 2 - 1) := by
  have := finite_of_basis F E basis
  rw [card_nonsplitParameter_filter F E basis b hm h2 z hz
    (fun α => α ≠ 1 ∧ ∃ k : ℕ, orderOf α = 2 ^ k)]
  rw [show Nat.card {α : normOne F E →* ℂˣ // α ≠ 1 ∧ ∃ k : ℕ, orderOf α = 2 ^ k} =
      Nat.card {α : normOne F E →* ℂˣ // (∃ k : ℕ, orderOf α = 2 ^ k) ∧ α ≠ 1} from
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => And.comm),
    card_two_pow_hom_units_ne_one, card_normOne F E basis, mul_comm]

theorem orderOf_comp_dvd {X Y : Type*} [Group X] [Group Y] (lam : Y →* ℂˣ) (φ : X →* Y) :
    orderOf (lam.comp φ) ∣ orderOf lam := by
  apply orderOf_dvd_of_pow_eq_one
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
    MonoidHom.one_apply, MonoidHom.one_apply]

theorem exists_two_pow_of_dvd {M : Type*} [Monoid M] {x : M} {N : ℕ} (h : orderOf x ∣ 2 ^ N) :
    ∃ k : ℕ, orderOf x = 2 ^ k := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨k, hk⟩

theorem nonsplitCharacter_two_pow_iff (F : Type) [Field F] [Fintype F] (E : Type) [Field E]
    [Algebra F E] (basis : Module.Basis (Fin 2) F E) (b : Fˣ) {m : ℕ} (hm : 0 < m)
    (heven : Even m) (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) {n : ℕ} (hmn : m = 2 ^ n)
    (P : NonsplitParameter F E b m h2 z hz) :
    (∃ k : ℕ, orderOf (nonsplitCharacter F b m hm heven E basis h2 z hz P) = 2 ^ k) ↔
      ∃ k : ℕ, orderOf P.1.1 = 2 ^ k := by
  set lam := nonsplitCharacter F b m hm heven E basis h2 z hz P with hlam
  obtain ⟨hs1, hs2⟩ := nonsplitCharacter_spec F b m hm heven E basis h2 z hz P
  constructor
  · rintro ⟨k, hk⟩
    have hP : P.1.1 = lam.comp (nonsplitDiagT F b m hm heven E basis) :=
      MonoidHom.ext fun t => (hs1 t).symm
    rw [hP]
    exact exists_two_pow_of_dvd ((orderOf_comp_dvd lam _).trans hk.dvd)
  · rintro ⟨k, hk⟩
    have hα : P.1.1 ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    have hz2 : P.1.2 ^ (2 ^ (n + k)) = 1 := by
      rw [pow_add, pow_mul, ← hmn, P.2, ← MonoidHom.pow_apply, hα, MonoidHom.one_apply]
    apply exists_two_pow_of_dvd (N := n + k)
    apply orderOf_dvd_of_pow_eq_one
    refine MonoidHom.ext fun g => ?_
    obtain ⟨t, j, hg⟩ := nonsplitTorus_normalForm z hz (g : CentralExtension F b m hm heven) g.2
    have hge : g = ⟨nonsplitDiag F b m hm heven E basis t, nonsplitDiag_mem t⟩ *
        ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ ^ (j : ℕ) :=
      Subtype.ext (by rw [hg]; rfl)
    have htk : P.1.1 t ^ (2 ^ (n + k)) = 1 := by
      rw [pow_add, mul_comm, pow_mul, ← MonoidHom.pow_apply, hα, MonoidHom.one_apply, one_pow]
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hge, map_mul, map_pow, hs1, hs2, mul_pow,
      htk, one_mul, ← pow_mul, mul_comm, pow_mul, hz2, one_pow]

end Parameters

section Family

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}
  {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) (h2 : (2 : F) ≠ 0)
  (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)
  (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)

theorem nonsplitCharacter_comp_minusWeylConj (P : NonsplitParameter F E b m h2 z hz) :
    (nonsplitCharacter F b m hm heven E basis h2 z hz P).comp (minusWeylConj h2 y hy) =
      nonsplitCharacter F b m hm heven E basis h2 z hz
        (nonsplitWeylParameter F b m heven E basis h2 z hz P) := by
  rw [minusWeylConj_eq h2 z hz y hy, nonsplitCharacter_comp_weylConj]

include hb in
theorem nonsplitWeylParameter_two_pow {P : NonsplitParameter F E b m h2 z hz}
    (hP : P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) :
    ((nonsplitWeylParameter F b m heven E basis h2 z hz P).1.1 ≠ 1 ∧
      ∃ k : ℕ, orderOf (nonsplitWeylParameter F b m heven E basis h2 z hz P).1.1 = 2 ^ k) ∧
      nonsplitWeylParameter F b m heven E basis h2 z hz P ≠ P := by
  obtain ⟨hP1, k, hk⟩ := hP
  have hfst : (nonsplitWeylParameter F b m heven E basis h2 z hz P).1.1 = P.1.1⁻¹ := rfl
  refine ⟨⟨?_, k, ?_⟩, ?_⟩
  · rw [hfst]
    intro h
    apply hP1
    refine MonoidHom.ext fun c => ?_
    have h' := DFunLike.congr_fun h c
    rw [MonoidHom.inv_apply, MonoidHom.one_apply, inv_eq_one] at h'
    rw [h', MonoidHom.one_apply]
  · rw [hfst]
    exact (orderOf_inv P.1.1).trans hk
  · intro h
    exact hP1 ((nonsplitWeylParameter_eq_self_iff F b m heven E basis h2 z hz hb P).mp h)

include hpodd hb hψ y hy in
theorem cuspidalCharacter_nonsplit_eq_iff {P P' : NonsplitParameter F E b m h2 z hz}
    (hP : P.1.1 ≠ 1) :
    cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z hz P) =
        cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z hz P') ↔
      P' = P ∨ P' = nonsplitWeylParameter F b m heven E basis h2 z hz P := by
  have hinj : Function.Injective (nonsplitCharacter F b m hm heven E basis h2 z hz) :=
    (nonsplitCharacterEquiv F b m hm heven E basis h2 z hz).injective
  have hfix : (nonsplitCharacter F b m hm heven E basis h2 z hz P).comp (minusWeylConj h2 y hy) ≠
      nonsplitCharacter F b m hm heven E basis h2 z hz P := fun h =>
    hP ((minusWeyl_fixed_iff hb y hy h2 z hz P).mp h)
  rw [cuspidalCharacter_eq_iff hpodd hb y hy h2 hψ hfix,
    nonsplitCharacter_comp_minusWeylConj h2 z hz y hy, hinj.eq_iff, hinj.eq_iff]

include hpodd hψ y hy in
theorem ncard_twoPrimaryCuspidal :
    Set.ncard ((fun P : NonsplitParameter F E b m h2 z hz =>
      cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z hz P)) ''
        {P | P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k}) =
      m * (2 ^ (Nat.card F + 1).factorization 2 - 1) / 2 := by
  set S : Set (NonsplitParameter F E b m h2 z hz) :=
    {P | P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k} with hSdef
  have hcardS := card_two_pow_nonsplitParameter F E basis b hm h2 z hz
  have hfinP : Finite (NonsplitParameter F E b m h2 z hz) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_nonsplitParameter F b m hm E basis h2 z hz]
      exact Nat.mul_ne_zero (by omega) hm.ne')
  have h2S := two_mul_ncard_image_of_pairs
    (fun P : NonsplitParameter F E b m h2 z hz =>
      cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z hz P))
    (nonsplitWeylParameter F b m heven E basis h2 z hz) S
    (fun P hP => nonsplitWeylParameter_two_pow hb h2 z hz hP)
    (fun P hP P' _ => cuspidalCharacter_nonsplit_eq_iff hpodd hb h2 z hz y hy hψ hP.1)
  rw [show Set.ncard S = m * (2 ^ (Nat.card F + 1).factorization 2 - 1) by
    rw [← hcardS, ← Nat.card_coe_set_eq]; rfl] at h2S
  omega

end Family

end CFSG.Wreathed
