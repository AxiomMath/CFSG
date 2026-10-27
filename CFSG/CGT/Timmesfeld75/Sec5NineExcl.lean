module

public import CFSG.CGT.Timmesfeld75.Sec5NineGen
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.CGT.Timmesfeld75.Sec5NineMathieu
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.CGT.Timmesfeld75.Reduction
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Ident59 (K : Type) [Group K] : Prop :=
  (∃ m r : ℕ, 2 ≤ m ∧ 1 ≤ r ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL m 2 r) ∨
    Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* alternatingGroup (Fin 7))

@[expose] def A9Input : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Z : Subgroup Y) [Z.Normal], Z ≤ Subgroup.center Y →
    Nonempty (Y ⧸ Z ≃* alternatingGroup (Fin 9)) →
      ∀ (N : Type) [Group N] [Finite N], (∀ a b : N, a * b = b * a) → (∀ a : N, a * a = 1) →
        ∀ ρ : Y →* MulAut N, ρ.ker ≤ Z → 2 ^ 6 < Nat.card N

section Exclusion

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem card_quotient_dvd_card_range {M : Type*} [Group M] (ρ : Y →* M) {Z : Subgroup Y}
    [Z.Normal] (hρ : ρ.ker ≤ Z) : Nat.card (Y ⧸ Z) ∣ Nat.card ρ.range := by
  have hsurj : Function.Surjective (QuotientGroup.map ρ.ker Z (MonoidHom.id Y) hρ) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk y, rfl⟩
  have h := Subgroup.card_dvd_of_surjective hsurj
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at h

theorem card_eq_of_psu3_model {K : Type} [Group K] {s : ℕ} (hs : 1 ≤ s)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 2 s) :
    Nat.card K = Nat.card (PSU3 2 s) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hs hF (by norm_num),
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3 hs]
  have hq : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hq2 : 1 ≤ (2 ^ s) ^ 2 := Nat.one_le_pow _ _ hq
  have hprod : (∏ i ∈ Finset.Icc 2 3, ((((2 ^ s : ℕ) : ℤ)) ^ i - (-1) ^ i).toNat) =
      ((2 ^ s) ^ 2 - 1) * ((2 ^ s) ^ 3 + 1) := by
    have : Finset.Icc 2 3 = {2, 3} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
    have h2 : ((((2 ^ s : ℕ) : ℤ)) ^ 2 - (-1) ^ 2).toNat = (2 ^ s) ^ 2 - 1 := by
      have : ((((2 ^ s : ℕ) : ℤ)) ^ 2 - (-1) ^ 2) = (((2 ^ s) ^ 2 - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hq2]
        ring
      rw [this, Int.toNat_natCast]
    have h3 : ((((2 ^ s : ℕ) : ℤ)) ^ 3 - (-1) ^ 3).toNat = (2 ^ s) ^ 3 + 1 := by
      have : ((((2 ^ s : ℕ) : ℤ)) ^ 3 - (-1) ^ 3) = (((2 ^ s) ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    rw [h2, h3]
  rw [hprod]

theorem exists_card_eq_sz_of_model {K : Type} [Group K] {s : ℕ}
    (h : CFSG.Blueprint.LieModel K .twistedB2 0 2 s) :
    ∃ a : ℕ, 1 ≤ a ∧ s = 2 * a + 1 ∧ Nat.card K = Nat.card (Sz a) := by
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, a, ha, F, _, _, hs, hF, ⟨e⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · refine ⟨a, ha, hs, ?_⟩
    subst hs
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF,
      CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
    ring

theorem card_nativeM23
    : Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem isPrimitivePrimeDivisor_eleven : CFSG.Timmesfeld.IsPrimitivePrimeDivisor 11 10 := by
  refine ⟨by norm_num, by norm_num, fun j hj0 hj => ?_⟩
  interval_cases j <;> norm_num

theorem isPrimitivePrimeDivisor_twentythree : CFSG.Timmesfeld.IsPrimitivePrimeDivisor 23 11 := by
  refine ⟨by norm_num, by norm_num, fun j hj0 hj => ?_⟩
  interval_cases j <;> norm_num

theorem ident59_of_listGroup
    (h9 : A9Input) (hl : ListGroup (Y ⧸ Subgroup.center Y))
    {Ē : Subgroup (Y ⧸ Subgroup.center Y)} (hStd : StdPair (Y ⧸ Subgroup.center Y) Ē)
    {N : Type} [Group N] [Finite N] (hNc : ∀ a b : N, a * b = b * a) (hN2 : ∀ a : N, a * a = 1)
    (ρ : Y →* MulAut N) (hρ : ρ.ker ≤ Subgroup.center Y)
    (hNE : Nat.card N ≤ Nat.card Ē ^ 2) : Ident59 (Y ⧸ Subgroup.center Y) := by
  have hNp : IsPGroup 2 N := fun x => ⟨1, by simpa [pow_one, sq] using hN2 x⟩
  obtain ⟨d, hd⟩ := hNp.exists_card_eq
  have hdvd := card_quotient_dvd_card_range ρ hρ
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hinj : Function.Injective (ρ.range.subtype : ↥ρ.range →* MulAut N) :=
    Subtype.val_injective
  have hM : ∀ r k : ℕ, CFSG.Timmesfeld.IsPrimitivePrimeDivisor r k → 8 < k →
      r ∣ Nat.card (Y ⧸ Subgroup.center Y) → ¬ Nat.card Ē = 16 := by
    intro r k hr hk hrK hE
    rw [hE, hd] at hNE
    have hd8 : d ≤ 8 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 9 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    have h10 := faithful_le_of_primitive ρ.range.subtype hinj (by omega) hd hr (hrK.trans hdvd)
    omega
  rcases hl with ⟨m, s, hm, hs, hmodel⟩ | ⟨s, hs, hmodel⟩ | ⟨s, hodd, h3, hmodel⟩ |
      ⟨k, hk6, hk9, ⟨e⟩⟩ | hM22 | hM23 | hM24
  · exact Or.inl ⟨m, s, hm, hs, hmodel⟩
  ·
    exfalso
    obtain ⟨hE, -⟩ := hStd.of_psu3 hs hmodel
    have hcard := card_eq_of_psu3_model (by omega) hmodel
    have h6 := lemma27_psu3 hs (hcard.symm ▸ hdvd) ρ.range.subtype hinj hd
    rw [hE, ← pow_mul, hd] at hNE
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hNE
    omega
  ·
    exfalso
    obtain ⟨hE, -⟩ := hStd.of_sz hodd h3 hmodel
    obtain ⟨a, ha, hsa, hcard⟩ := exists_card_eq_sz_of_model hmodel
    have h4 := lemma27_sz ha (hcard.symm ▸ hdvd) ρ.range.subtype hinj hd
    rw [hE, ← pow_mul, hd] at hNE
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hNE
    omega
  ·
    have hk : k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inr (Or.inr ⟨e⟩)
    · refine Or.inl ⟨4, 1, by norm_num, le_rfl, ?_⟩
      have hL := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
        (Y ⧸ Subgroup.center Y)).2 ⟨e⟩
      rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    · exfalso
      have hE := hStd.card_alternating (by norm_num) (by norm_num) ⟨e⟩
      simp only [show ¬ (9 : ℕ) ≤ 7 by norm_num, ite_false] at hE
      have h8 := h9 Y (Subgroup.center Y) le_rfl ⟨e⟩ N hNc hN2 ρ hρ
      rw [hE] at hNE
      omega
  ·
    obtain ⟨e⟩ := hM22
    exact absurd (hStd.card_sporadic (Or.inl ⟨e⟩)) fun hE =>
      hM 11 10 isPrimitivePrimeDivisor_eleven (by norm_num) (by
        rw [Nat.card_congr e.toEquiv]
        exact eleven_dvd_card_nativeM22) hE
  ·
    obtain ⟨e⟩ := hM23
    exact absurd (hStd.card_sporadic (Or.inr (Or.inl ⟨e⟩))) fun hE =>
      hM 11 10 isPrimitivePrimeDivisor_eleven (by norm_num) (by
        have hK : Nat.card (Y ⧸ Subgroup.center Y) = 10200960 := by
          rw [Nat.card_congr e.toEquiv]
          exact card_nativeM23
        rw [hK]
        norm_num) hE
  ·
    obtain ⟨e⟩ := hM24
    exact absurd (hStd.card_sporadic (Or.inr (Or.inr ⟨e⟩))) fun hE =>
      hM 23 11 isPrimitivePrimeDivisor_twentythree (by norm_num) (by
        rw [Nat.card_congr e.toEquiv]
        exact twentythree_dvd_card_nativeM24) hE

end Exclusion

section Abstract

structure Ident59Out (Y : Type) [Group Y] (E : Subgroup Y) : Prop where
  wc : IsWC E
  cl : Subgroup.normalClosure (E : Set Y) = ⊤
  four_le : 4 ≤ Nat.card E
  inf_center : E ⊓ Subgroup.center Y = ⊥
  perfect : commutator Y = ⊤
  simple : IsSimpleGroup (Y ⧸ Subgroup.center Y)
  ident : Ident59 (Y ⧸ Subgroup.center Y)
  stdPair : StdPair (Y ⧸ Subgroup.center Y) (E.map (QuotientGroup.mk' (Subgroup.center Y)))

variable {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y}

theorem ident59_abstract
    {n : ℕ} (hInd : SimpleCaseUpTo n) (h215 : Lemma215Stmt)
    (hList : ListWCIdentification) (h9 : A9Input)
    (hE : IsWC E) (hcl : Subgroup.normalClosure (E : Set Y) = ⊤)
    (hnc : ∃ a b : Y, a * b ≠ b * a) (h4 : 4 ≤ Nat.card E)
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P ≤ Subgroup.center Y)
    (hn : Nat.card (Y ⧸ Subgroup.center Y) < n)
    {N : Type} [Group N] [Finite N] (hNc : ∀ a b : N, a * b = b * a) (hN2 : ∀ a : N, a * a = 1)
    (ρ : Y →* MulAut N) (hρ : ρ.ker ≤ Subgroup.center Y)
    (hNE : Nat.card N ≤ Nat.card E ^ 2) : Ident59Out Y E := by
  classical
  have hEZ := inf_center_eq_bot_of_not_comm hE hcl hnc
  have hmksurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center Y)) :=
    QuotientGroup.mk'_surjective _
  set Ē : Subgroup (Y ⧸ Subgroup.center Y) := E.map (QuotientGroup.mk' (Subgroup.center Y))
    with hĒ
  have hĒwc : IsWC Ē := hE.map_quotient_central_of_inf_eq_bot (Subgroup.center Y) le_rfl hEZ
  have hĒcl : Subgroup.normalClosure (Ē : Set (Y ⧸ Subgroup.center Y)) = ⊤ := by
    rw [hĒ, Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ hmksurj, hcl,
      Subgroup.map_top_of_surjective _ hmksurj]
  have hĒcard : Nat.card Ē = Nat.card E :=
    card_map_eq_of_inf_ker_eq_bot (QuotientGroup.mk' (Subgroup.center Y))
      (by rwa [QuotientGroup.ker_mk'])
  have hĒ4 : 4 ≤ Nat.card Ē := hĒcard ▸ h4
  have hrad : ∀ R : Subgroup (Y ⧸ Subgroup.center Y), R.Normal → Group.IsSolvable R → R = ⊥ := by
    refine solvable_normal_bot_of_pSubgroups_central fun p hp P hPn hPp => ?_
    by_cases hp2 : p = 2
    · subst hp2
      exact hO2 P hPn hPp
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨m, hm⟩ := hPp.exists_card_eq
      have hodd : Odd (Nat.card P) := by
        rw [hm]
        exact (hp.odd_of_ne_two hp2).pow
      have hNn : ∀ k ∈ Subgroup.normalClosure (E : Set Y), ∀ n ∈ P, k * n * k⁻¹ ∈ P :=
        fun k _ n hn => hPn.conj_mem n hn k
      intro n hn
      refine Subgroup.mem_center_iff.2 fun k => ?_
      have hkK : k ∈ Subgroup.normalClosure (E : Set Y) := by rw [hcl]; trivial
      exact (oddCore_le_center hE h4 P (by rw [hcl]; exact le_top) hNn hodd n hn k hkK).symm
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := h215 _ Ē hĒwc hĒ4 hĒcl hrad
  have hKnc : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (show Ē ≠ ⊥ from fun h => by rw [h] at hĒ4; simp at hĒ4)
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hnorm : (Subgroup.zpowers t).Normal := ⟨fun n hn g => by
      rwa [show g * n * g⁻¹ = n by rw [hcomm g n, mul_inv_cancel_right]]⟩
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers t) with h | h
    · exact ht1' (by simpa [h] using (Subgroup.mem_zpowers t))
    · have hord : orderOf t = 2 := by
        refine orderOf_eq_prime (by simpa [sq] using elemAbelian_mul_self hĒwc.1 ht) ht1'
      have h1 : Nat.card (Subgroup.zpowers t) = Nat.card (Y ⧸ Subgroup.center Y) := by
        rw [h, Subgroup.card_top]
      have h2 := Subgroup.card_le_card_group Ē
      rw [← h1, Nat.card_zpowers, hord] at h2
      omega
  have : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hsimple
  obtain ⟨hlist, htrK⟩ := hInd (Y ⧸ Subgroup.center Y) hn hKnc Ē hĒwc hĒ4
  have hStd : StdPair (Y ⧸ Subgroup.center Y) Ē := hList _ hlist Ē hĒwc hĒ4
  refine ⟨hE, hcl, h4, hEZ, ?_, hsimple, ident59_of_listGroup h9 hlist hStd hNc hN2 ρ hρ
    (hĒcard ▸ hNE), hStd⟩
  refine commutator_eq_top_of_wc hE hEZ hcl h4 ?_
  intro a ha ha1 b hb hb1
  have hma : QuotientGroup.mk' (Subgroup.center Y) a ∈ Ē := Subgroup.mem_map_of_mem _ ha
  have hmb : QuotientGroup.mk' (Subgroup.center Y) b ∈ Ē := Subgroup.mem_map_of_mem _ hb
  have hne1 : ∀ x ∈ E, x ≠ 1 → QuotientGroup.mk' (Subgroup.center Y) x ≠ 1 := by
    intro x hx hx1 h
    have hxZ : x ∈ E ⊓ Subgroup.center Y := ⟨hx, (QuotientGroup.eq_one_iff x).1 h⟩
    rw [hEZ, Subgroup.mem_bot] at hxZ
    exact hx1 hxZ
  obtain ⟨g', -, hg'⟩ := htrK _ hma (hne1 a ha ha1) _ hmb (hne1 b hb hb1)
  obtain ⟨g, rfl⟩ := hmksurj g'
  have hq : QuotientGroup.mk' (Subgroup.center Y) (g * a * g⁻¹) =
      QuotientGroup.mk' (Subgroup.center Y) b := by
    rw [map_mul, map_mul, map_inv]
    exact hg'
  refine ⟨g, b⁻¹ * (g * a * g⁻¹), QuotientGroup.eq.1 hq.symm, by group⟩

end Abstract

end CFSG.CGT.Timmesfeld75
