module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Balance
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly CFSG.Open

variable {X : Type} [Group X] [Finite X]

@[expose] def signalizerJoin (A : Subgroup X) : Subgroup X :=
  ⨆ (a : A) (_ : a ≠ 1), oddCentralizer (a : X)

omit [Finite X] in
theorem oddCentralizer_le_signalizerJoin {A : Subgroup X} {a : X} (haA : a ∈ A) (ha1 : a ≠ 1) :
    oddCentralizer a ≤ signalizerJoin A :=
  le_iSup₂_of_le (f := fun (b : A) (_ : b ≠ 1) => oddCentralizer (b : X)) ⟨a, haA⟩
    (fun h => ha1 (congrArg Subtype.val h)) le_rfl

omit [Finite X] in
theorem signalizerJoin_mono {A B : Subgroup X} (h : A ≤ B) : signalizerJoin A ≤ signalizerJoin B :=
  iSup₂_le fun a ha => oddCentralizer_le_signalizerJoin (h a.2) fun h1 => ha (Subtype.ext h1)

@[expose] def oddCoreOf (C : Subgroup X) : Subgroup X :=
  (CFSG.pPrimeCore 2 C).map C.subtype

omit [Finite X] in
theorem oddCoreOf_congr {C D : Subgroup X} (h : C = D) : oddCoreOf C = oddCoreOf D := by
  subst h
  rfl

omit [Finite X] in
theorem centralizer_zpowers (a : X) :
    centralizer ((zpowers a : Subgroup X) : Set X) = centralizer {a} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite X] in
theorem oddCoreOf_centralizer_zpowers (a : X) :
    oddCoreOf (centralizer ((zpowers a : Subgroup X) : Set X)) = oddCentralizer a :=
  oddCoreOf_congr (centralizer_zpowers a)

theorem exists_eq_zpowers_of_card_eq_two {S : Subgroup X} (hS : Nat.card S = 2) :
    ∃ a ∈ S, a ≠ 1 ∧ S = zpowers a := by
  rcases S.bot_or_exists_ne_one with h | ⟨a, haS, ha1⟩
  · rw [h, Subgroup.card_bot] at hS
    exact absurd hS (by norm_num)
  refine ⟨a, haS, ha1, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haS) ?_).symm⟩
  rw [hS, Nat.card_zpowers]
  have hdvd : orderOf a ∣ 2 := hS ▸ Subgroup.orderOf_dvd_natCard S haS
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha1
  · exact h.ge

omit [Finite X] in
theorem zpowers_mem_signalizerFunctorEk {A : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1) {a : X}
    (haA : a ∈ A) (ha1 : a ≠ 1) : zpowers a ∈ signalizerFunctorEk 2 1 A :=
  ⟨Subgroup.zpowers_le.mpr haA, by rw [Nat.card_zpowers, orderOf_eq_prime (hA2 a haA) ha1, pow_one]⟩

theorem iSup_signalizerFunctorEk_eq {A : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1) :
    (⨆ (S : Subgroup X) (_ : S ∈ signalizerFunctorEk 2 1 A),
      oddCoreOf (centralizer (S : Set X))) = signalizerJoin A := by
  refine le_antisymm (iSup₂_le fun S hS => ?_) (iSup₂_le fun a ha => ?_)
  · obtain ⟨a, haS, ha1, rfl⟩ := exists_eq_zpowers_of_card_eq_two (by rw [hS.2, pow_one])
    rw [oddCoreOf_centralizer_zpowers]
    exact oddCentralizer_le_signalizerJoin (hS.1 haS) ha1
  · have ha1 : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
    rw [← oddCoreOf_centralizer_zpowers]
    exact le_iSup₂_of_le (f := fun (S : Subgroup X) (_ : S ∈ signalizerFunctorEk 2 1 A) =>
      oddCoreOf (centralizer (S : Set X))) _ (zpowers_mem_signalizerFunctorEk hA2 a.2 ha1) le_rfl

theorem signalizerMcBrideHypothesisB_oddCoreOf (C : Subgroup X) :
    signalizerMcBrideHypothesisB 2 (oddCoreOf C) := by
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreOf C)) := by
    rw [oddCoreOf, Subgroup.card_map_of_injective C.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  refine ⟨Nat.prime_two, hcop, fun K L hK _ _ _ hnc => ?_⟩
  exfalso
  have : Group.IsSolvable K := CFSG.SignalizerFunctorTheorem.isSolvable_of_coprime_two K
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hK) hcop)
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)

theorem signalizerJoin_spec {A : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : 8 ≤ Nat.card A)
    (hall : ∀ b ∈ A, b ≠ 1 → IsTwoANine (EscapingQuotient b)) :
    (Odd (Nat.card (signalizerJoin A)) ∧ A ≤ normalizer (signalizerJoin A : Set X)) ∧
    (∀ a ∈ A, a ≠ 1 → signalizerJoin A ⊓ centralizer {a} = oddCentralizer a) ∧
    (∀ Y : Subgroup X, A ≤ normalizer (Y : Set X) →
      (∀ a ∈ A, a ≠ 1 → Y ⊓ centralizer {a} ≤ oddCentralizer a) → Y ≤ signalizerJoin A) := by
  have hcomm : ∀ {x y : X}, x ∈ A → y ∈ A → Commute x y := fun hx hy =>
    commute_of_sq_eq_one_of_mem hA2 hx hy
  have hEA : IsElemAbelian 2 A :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x.2 y.2).eq⟩⟩, hA2⟩
  have hgen : ∀ S ∈ signalizerFunctorEk 2 1 A, ∃ a ∈ A, a ≠ 1 ∧ S = zpowers a := fun S hS => by
    obtain ⟨a, haS, ha1, rfl⟩ := exists_eq_zpowers_of_card_eq_two (by rw [hS.2, pow_one])
    exact ⟨a, hS.1 haS, ha1, rfl⟩
  have key := CFSG.SignalizerFunctorTheorem.signalizer_functor_theorem_two X 1 le_rfl A hEA
    (by rw [show (2 : ℕ) ^ (1 + 2) = 8 by norm_num]; exact hA)
    (fun S => oddCoreOf (centralizer (S : Set X)))
    (fun S _ => Subgroup.map_subtype_le _)
    (fun S _ => by
      rw [oddCoreOf, Subgroup.card_map_of_injective (centralizer (S : Set X)).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card)
    (fun S hS => by
      obtain ⟨a, haA, -, rfl⟩ := hgen S hS
      rw [oddCoreOf_centralizer_zpowers]
      exact (le_centralizer_of_sq_eq_one hA2 haA).trans
        (centralizer_le_normalizer_oddCentralizer a))
    (fun S hS S' hS' => by
      obtain ⟨a, haA, ha1, rfl⟩ := hgen S hS
      obtain ⟨b, hbA, hb1, rfl⟩ := hgen S' hS'
      rw [oddCoreOf_centralizer_zpowers, oddCoreOf_centralizer_zpowers, centralizer_zpowers]
      exact oddCentralizer_inf_centralizer_le (orderOf_eq_prime (hA2 a haA) ha1) (hcomm haA hbA)
        (hall b hbA hb1))
    (fun S _ => signalizerMcBrideHypothesisB_oddCoreOf _)
  obtain ⟨⟨hcop, hnorm⟩, hinf, hmax, -⟩ := key
  rw [iSup_signalizerFunctorEk_eq hA2] at hcop hnorm hinf hmax
  refine ⟨⟨Nat.coprime_two_left.mp hcop, hnorm⟩, fun a haA ha1 => ?_, fun Y hAY hY => ?_⟩
  · have h := hinf _ (zpowers_mem_signalizerFunctorEk hA2 haA ha1)
    rwa [oddCoreOf_centralizer_zpowers, centralizer_zpowers] at h
  · refine hmax Y hAY fun S hS => ?_
    obtain ⟨a, haA, ha1, rfl⟩ := hgen S hS
    rw [oddCoreOf_centralizer_zpowers, centralizer_zpowers]
    exact hY a haA ha1

section Spec

variable {A : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : 8 ≤ Nat.card A)
  (hall : ∀ b ∈ A, b ≠ 1 → IsTwoANine (EscapingQuotient b))
include hA2 hA hall

theorem odd_card_signalizerJoin : Odd (Nat.card (signalizerJoin A)) :=
  (signalizerJoin_spec hA2 hA hall).1.1

theorem le_normalizer_signalizerJoin : A ≤ normalizer (signalizerJoin A : Set X) :=
  (signalizerJoin_spec hA2 hA hall).1.2

theorem signalizerJoin_inf_centralizer {a : X} (haA : a ∈ A) (ha1 : a ≠ 1) :
    signalizerJoin A ⊓ centralizer {a} = oddCentralizer a :=
  (signalizerJoin_spec hA2 hA hall).2.1 a haA ha1

theorem le_signalizerJoin {Y : Subgroup X} (hAY : A ≤ normalizer (Y : Set X))
    (hY : ∀ a ∈ A, a ≠ 1 → Y ⊓ centralizer {a} ≤ oddCentralizer a) : Y ≤ signalizerJoin A :=
  (signalizerJoin_spec hA2 hA hall).2.2 Y hAY hY

theorem signalizerJoin_eq_of_le {V : Subgroup X} (hVA : V ≤ A) (hV : Nat.card V = 4) :
    signalizerJoin A = signalizerJoin V := by
  refine le_antisymm ?_ (signalizerJoin_mono hVA)
  have hodd := odd_card_signalizerJoin hA2 hA hall
  calc signalizerJoin A = ⨆ (v : V) (_ : v ≠ 1), signalizerJoin A ⊓ centralizer {(v : X)} :=
        CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
          Nat.prime_two V (signalizerJoin A) (fun v => Subtype.ext (hA2 _ (hVA v.2)))
          (by rw [hV]; norm_num) (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
          (hVA.trans (le_normalizer_signalizerJoin hA2 hA hall))
    _ ≤ signalizerJoin V := iSup₂_le fun v hv => by
        have hv1 : (v : X) ≠ 1 := fun h => hv (Subtype.ext h)
        rw [signalizerJoin_inf_centralizer hA2 hA hall (hVA v.2) hv1]
        exact oddCentralizer_le_signalizerJoin v.2 hv1

end Spec

theorem signalizerJoin_eq_of_le_of_le {A A' V : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA : 8 ≤ Nat.card A) (hall : ∀ b ∈ A, b ≠ 1 → IsTwoANine (EscapingQuotient b))
    (hA'2 : ∀ x ∈ A', x ^ 2 = 1) (hA' : 8 ≤ Nat.card A')
    (hall' : ∀ b ∈ A', b ≠ 1 → IsTwoANine (EscapingQuotient b)) (hVA : V ≤ A) (hVA' : V ≤ A')
    (hV : Nat.card V = 4) : signalizerJoin A = signalizerJoin A' :=
  (signalizerJoin_eq_of_le hA2 hA hall hVA hV).trans
    (signalizerJoin_eq_of_le hA'2 hA' hall' hVA' hV).symm

theorem le_signalizerJoin_of_odd {A Y : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA : Nat.card A = 16) (hall : ∀ b ∈ A, b ≠ 1 → IsTwoANine (EscapingQuotient b))
    (hY : Odd (Nat.card Y)) (hAY : A ≤ normalizer (Y : Set X)) : Y ≤ signalizerJoin A :=
  le_signalizerJoin hA2 (by rw [hA]; norm_num) hall hAY fun a haA ha1 =>
    inf_centralizer_le_oddCentralizer hA2 hA haA (hall a haA ha1) hY hAY

omit [Finite X] in
theorem map_conj_signalizerJoin (A : Subgroup X) (g : X) :
    (signalizerJoin A).map (MulAut.conj g).toMonoidHom =
      signalizerJoin (A.map (MulAut.conj g).toMonoidHom) := by
  rw [signalizerJoin, Subgroup.map_iSup]
  refine le_antisymm (iSup_le fun a => ?_) (iSup₂_le fun b hb => ?_)
  · rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    have ha1 : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
    rw [map_conj_oddCentralizer]
    exact oddCentralizer_le_signalizerJoin ⟨a, a.2, rfl⟩ (by simpa using ha1)
  · obtain ⟨a, haA, hab⟩ := b.2
    have hb' : (b : X) = g * a * g⁻¹ := hab.symm
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hb (Subtype.ext (by rw [hb', mul_one, mul_inv_cancel, OneMemClass.coe_one]))
    rw [hb', ← map_conj_oddCentralizer]
    refine le_iSup_of_le ⟨a, haA⟩ (Subgroup.map_mono ?_)
    exact le_iSup_of_le (fun h => ha1 (congrArg Subtype.val h)) le_rfl

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
