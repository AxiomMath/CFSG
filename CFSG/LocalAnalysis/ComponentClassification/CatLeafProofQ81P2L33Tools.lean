module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Rows
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81P2

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup

theorem not_isPGroup_of_closure_odd {G : Type*} [Group G] [Finite G] {F : Subgroup G}
    {T : Set G} (hTF : T ⊆ F) (hT : ∀ t ∈ T, Odd (orderOf t))
    (h2 : 2 ∣ Nat.card (closure T)) : ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hP
  set T' : Set ↥F := F.subtype ⁻¹' T with hT'
  have hle : closure T' ≤ pPrimeCore 2 ↥F := by
    rw [closure_le]
    intro t ht
    obtain ⟨k, hk⟩ := hP (QuotientGroup.mk t)
    have h1 : orderOf (QuotientGroup.mk t : ↥F ⧸ pPrimeCore 2 ↥F) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have h2' : orderOf (QuotientGroup.mk t : ↥F ⧸ pPrimeCore 2 ↥F) ∣ orderOf t :=
      orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥F)) t
    have hto : Odd (orderOf t) := by
      rw [← Subgroup.orderOf_coe]
      exact hT _ ht
    have h3 : orderOf (QuotientGroup.mk t : ↥F ⧸ pPrimeCore 2 ↥F) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k
        (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hto h2'))) h1
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  have himg : F.subtype '' T' = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hTF hx⟩, hx, rfl⟩
  have hmap : (closure T').map F.subtype = closure T := by
    rw [MonoidHom.map_closure, himg]
  have h2'' : 2 ∣ Nat.card (closure T') := by
    rwa [← hmap, card_map_of_injective F.subtype_injective] at h2
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl (h2''.trans (card_dvd_of_le hle))
    pPrimeCore_coprime_card

theorem not_isPGroup_of_perfect {G : Type*} [Group G] [Finite G] {F X : Subgroup G}
    (hXF : X ≤ F) (hX : ⁅X, X⁆ = X) (heven : 2 ∣ Nat.card X) :
    ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hP
  set X' := X.subgroupOf F with hX'
  have hmap : X'.map F.subtype = X := map_subgroupOf_eq_of_le hXF
  have hX'p : ⁅X', X'⁆ = X' := by
    apply map_injective F.subtype_injective
    rw [Subgroup.map_commutator, hmap, hX]
  set Q := ↥F ⧸ pPrimeCore 2 ↥F
  set Y := X'.map (QuotientGroup.mk' (pPrimeCore 2 ↥F)) with hY
  have hYp : ⁅Y, Y⁆ = Y := by rw [hY, ← Subgroup.map_commutator, hX'p]
  have : Group.IsNilpotent Q := hP.isNilpotent
  have hle : ∀ n, Y ≤ derivedSeries Q n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hYp]
      exact commutator_mono ih ih
  obtain ⟨n, hn⟩ := (Group.isSolvable_def Q).mp inferInstance
  have hYbot : Y = ⊥ := le_bot_iff.mp (hn ▸ hle n)
  have hX'O : X' ≤ pPrimeCore 2 ↥F := by
    intro x hx
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥F) x ∈ Y := mem_map_of_mem _ hx
    rw [hYbot, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hcard : Nat.card X' = Nat.card X := by
    rw [← hmap, card_map_of_injective F.subtype_injective]
  have h2 : 2 ∣ Nat.card X' := hcard ▸ heven
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl (h2.trans (card_dvd_of_le hX'O))
    pPrimeCore_coprime_card

theorem isPGroup_of_pPrimeCore_eq_bot {H : Type*} [Group H] (hO : pPrimeCore 2 H = ⊥)
    (hP : IsPGroup 2 (H ⧸ pPrimeCore 2 H)) : IsPGroup 2 H := by
  intro h
  obtain ⟨k, hk⟩ := hP (QuotientGroup.mk h)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hO, mem_bot] at hk
  exact hk

theorem isPGroup_quotient_iff_hasNormalPComplement {H : Type*} [Group H] [Finite H] :
    IsPGroup 2 (H ⧸ pPrimeCore 2 H) ↔ HasNormalPComplement 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · exact fun h => ⟨pPrimeCore 2 H, inferInstance, pPrimeCore_coprime_card, h⟩
  · rintro ⟨N, hN, hcop, hq⟩ x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hNO : N ≤ pPrimeCore 2 H := le_sSup ⟨hN, hcop⟩
    obtain ⟨k, hk⟩ := hq (QuotientGroup.mk x)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk ⊢
    exact hNO hk

theorem mem_fixedPoints_congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (a : MulAut Y)
    (y : Y) : e y ∈ fixedPoints (MulAut.congr e a) ↔ y ∈ fixedPoints a := by
  rw [mem_fixedPoints, mem_fixedPoints]
  change e (a (e.symm (e y))) = e y ↔ a y = y
  rw [MulEquiv.symm_apply_apply]
  exact e.injective.eq_iff

theorem isPGroup_fixedPoints_congr {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    (e : Y ≃* Y') (a : MulAut Y)
    (h : IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a))) :
    IsPGroup 2 (↥(fixedPoints (MulAut.congr e a)) ⧸
      pPrimeCore 2 ↥(fixedPoints (MulAut.congr e a))) := by
  have hmem : ∀ y : ↥(fixedPoints a), (e.toMonoidHom.comp (fixedPoints a).subtype) y ∈
      fixedPoints (MulAut.congr e a) := fun y =>
    (mem_fixedPoints_congr e a y).mpr y.2
  refine Q81.isPGroup_quotient_of_surjective
    ((e.toMonoidHom.comp (fixedPoints a).subtype).codRestrict _ hmem) ?_ h
  rintro ⟨y', hy'⟩
  have hy : e.symm y' ∈ fixedPoints a := by
    rw [← mem_fixedPoints_congr e a, MulEquiv.apply_symm_apply]
    exact hy'
  exact ⟨⟨e.symm y', hy⟩, Subtype.ext (MulEquiv.apply_symm_apply e y')⟩

theorem orderOf_congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (a : MulAut Y) :
    orderOf (MulAut.congr e a) = orderOf a :=
  MulEquiv.orderOf_eq _ a

theorem isTwoNilpExc_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsTwoNilpExc Y') : IsTwoNilpExc Y := by
  rcases h with ⟨p, f, h⟩ | ⟨p, f, hp, a, ha, K, _, _, hf, hK, ⟨e'⟩⟩ | h | h | h
  · exact Or.inl ⟨p, f, GSThmB.OddQuot.lieModel_of_equiv e.symm h⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, a, ha, K, inferInstance, inferInstance, hf, hK,
      ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl (GSThmB.OddQuot.lieModel_of_equiv e.symm h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (GSThmB.OddQuot.lieModel_of_equiv e.symm h))))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩)))

end CFSG.ComponentClassification.HarrisLit.L33
