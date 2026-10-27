module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def E8TwistedResidual :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card K) → ∀ p : ℕ, p.Prime → 5 ≤ p →
      p ∣ Nat.card K + 1 → ∀ g0 ∈ adjointGroup Tag.E8 L, Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.E8) L e8Neg →
          RootSL2Generated (langModel Tag.E8 K L g0) ∧
            RootComponentsQuasisimple (langModel Tag.E8 K L g0) p

theorem factorization_card_adjointGroup_E8_le_of_dvd_add_one
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization p ≤
      8 * (Nat.card K + 1).factorization p + 1 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := fun h => by
    have h1 : p ∣ Nat.card K + 1 - Nat.card K := Nat.dvd_sub hpq h
    rw [show Nat.card K + 1 - Nat.card K = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK1 : ¬ p ∣ Nat.card K - 1 := fun h => by
    have h1 : p ∣ Nat.card K + 1 - (Nat.card K - 1) := Nat.dvd_sub hpq h
    rw [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
    have : Fact p.Prime := ⟨hp⟩
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    rw [Nat.cast_add, Nat.cast_one] at h0
    have h1 := orderOf_neg_one (R := ZMod p)
    simp only [ZMod.ringChar_zmod_n, hp2, ite_false] at h1
    rw [eq_neg_of_add_eq_zero_left h0]
    exact h1
  have hsq : (Nat.card K ^ 2 - 1).factorization p = (Nat.card K + 1).factorization p := by
    have h1 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      have : 1 ≤ Nat.card K := by omega
      zify [this, Nat.one_le_pow 2 _ (by omega : 0 < Nat.card K)]
      ring
    rw [h1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpK1, zero_add]
  have hlte : ∀ k : ℕ, k ≠ 0 → p ^ (Nat.card K ^ (2 * k) - 1).factorization p =
      p ^ (Nat.card K + 1).factorization p * p ^ k.factorization p := fun k hk => by
    rw [ordProj_pow_sub_one_of_dvd hp hp2 hpK hq2 hord hk, hsq]
  have h := ordProj_card_adjointGroup_E (τ := Tag.E8) (K := K) (by simp) hp (by omega) hpK
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [hlte 1 one_ne_zero, hlte 4 (by norm_num), hlte 6 (by norm_num), hlte 7 (by norm_num),
    hlte 9 (by norm_num), hlte 10 (by norm_num), hlte 12 (by norm_num), hlte 15 (by norm_num)] at h
  have hnd : ∀ k ∈ ([1, 4, 6, 9, 10, 12, 15] : List ℕ), ¬ p ∣ k := by
    intro k hk hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hle : p ≤ k := Nat.le_of_dvd (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num) hdvd
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals interval_cases p <;> first | omega | (norm_num at hp)
  rw [ordProj_eq_one_of_not_dvd' (hnd 1 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 4 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 6 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 9 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 10 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 12 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 15 (by simp))] at h
  have h7 : (7 : ℕ).factorization p ≤ 1 := by
    rcases eq_or_ne p 7 with rfl | hne
    · rw [Nat.Prime.factorization_self (by norm_num)]
    · rw [Nat.factorization_eq_zero_of_not_dvd fun hd =>
        hne ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd)]
      norm_num
  have h' : (Nat.card (adjointGroup Tag.E8 K)).factorization p =
      8 * (Nat.card K + 1).factorization p + (7 : ℕ).factorization p := by
    refine Nat.pow_right_injective hp.two_le ?_
    change p ^ _ = p ^ _
    rw [h]
    ring
  omega

section Twisted


theorem mulAut_conj_injective_langModel (τ : Tag) (K : Type) [Field K] [Finite K] (L : Type)
    [Field L] [Algebra K L] (g0 : ModGL τ L) :
    Function.Injective (MulAut.conj : langModel τ K L g0 →* MulAut (langModel τ K L g0)) := by
  have hZ : Subgroup.center (langModel τ K L g0) = ⊥ := by
    have h1 := Subgroup.map_center_eq (langModelEquiv τ K L g0)
    rw [center_adjointGroup_eq_bot, Subgroup.map_bot] at h1
    exact h1.symm
  intro g g' hgg
  have hc : g'⁻¹ * g ∈ Subgroup.center (langModel τ K L g0) :=
    Subgroup.mem_center_iff.2 fun x => by
      have e1 := congrArg (fun φ : MulAut (langModel τ K L g0) => φ x) hgg
      simp only [MulAut.conj_apply] at e1
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [e1]
        _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem localDeltaIn_eq_bot_langModel_E8 (hTw : E8TwistedResidual) (K : Type) [Field K]
    [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {g0 : ModGL Tag.E8 L} (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem Tag.E8) L e8Neg)
    {H : Subgroup (MulAut (langModel Tag.E8 K L g0))}
    (hH : innerAut (langModel Tag.E8 K L g0) ≤ H) (E₀ : Subgroup (langModel Tag.E8 K L g0))
    (hpow : ∀ x ∈ E₀, x ^ p = 1) (hcard : p < Nat.card E₀)
    (htor : ∀ x ∈ E₀, (x : ModGL Tag.E8 L) ∈ torusGroup Tag.E8 L) :
    localDeltaIn p H (E₀.map (MulAut.conj : langModel Tag.E8 K L g0 →*
      MulAut (langModel Tag.E8 K L g0))) = ⊥ := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have := finite_langModel Tag.E8 K L g0
  obtain ⟨hgen, hqs⟩ := hTw K L Fr hFr p hp hp5 hpq g0 hg0C hg0
  obtain ⟨ζ, hζ, hζq⟩ := exists_orderOf_eq_of_dvd_add_one K (L := L) hpq
  have hζ2 : ζ ^ 2 ≠ 1 := fun h2 => by
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζ] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  exact localDeltaIn_eq_bot_of_rootSL2 (langModel_le_adjointGroup Tag.E8 K L hg0C)
    (mulAut_conj_injective_langModel Tag.E8 K L g0) hp hζ hζ2
    (fun v k => coroot_mem_langModel_E8 K L hFr hg0C hg0 hζq v k) hgen hqs hH E₀ hpow hcard htor

theorem isInnerLocallyBalanced_adjointE8_of_dvd_add_one_of_twisted (hTw : E8TwistedResidual)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K + 1) : IsInnerLocallyBalanced p (adjointGroup Tag.E8 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E8 K e8Neg
  set L := AlgebraicClosure K
  set M := langModel Tag.E8 K L g0 with hM
  have := finite_langModel Tag.E8 K L g0
  set e := langModelEquiv Tag.E8 K L g0
  have hinj := mulAut_conj_injective_langModel Tag.E8 K L g0
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH _
  set D₀ := D.comap (MulAut.conj : M →* MulAut M) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hpow₀ : ∀ y ∈ D₀, y ^ p = 1 := fun y hy => hinj (by
    rw [map_pow, show (MulAut.conj y) ^ p = 1 from hD.2 _ hy, map_one])
  have hD₀card : Nat.card D₀ = p ^ 3 := by
    rw [← hcard]
    conv_rhs => rw [← hDD]
    rw [Subgroup.card_map_of_injective hinj]
  have hD₀p : IsPGroup p D₀ := IsPGroup.of_card hD₀card
  obtain ⟨H₀, hH₀T, hH₀M, hH₀card⟩ := exists_twistedTorus_le_langModel_E8 K L hFr hg0C hg0
    (Nat.ordProj_dvd (Nat.card K + 1) p)
  rw [← pow_mul] at hH₀card
  have hfac : (Nat.card (⊤ : Subgroup M)).factorization p ≤
      (Nat.card (H₀.subgroupOf M)).factorization p + 1 := by
    rw [Subgroup.card_top, ← Nat.card_congr e.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀M).toEquiv, hH₀card,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    have := factorization_card_adjointGroup_E8_le_of_dvd_add_one K hp hp7 hpq
    omega
  obtain ⟨g, -, E, hED, hEcard, hEH⟩ := exists_large_conj_le_of_sylow (p := p) (Y := ⊤)
    (H := H₀.subgroupOf M) (A := D₀) le_top le_top hD₀p hfac
  set Ed := E.map (MulAut.conj : M →* MulAut M) with hEd
  have hEdD : Ed ≤ D := by
    rw [← hDD]
    exact Subgroup.map_mono hED
  refine le_bot_iff.1 ((localDeltaIn_antitone H hEdD).trans (le_of_eq ?_))
  refine localDeltaIn_eq_bot_of_map_conj (c := MulAut.conj g) (hH ⟨g, rfl⟩) ?_
  have hmap : Ed.map (MulAut.conj (MulAut.conj g)).toMonoidHom =
      (E.map (MulAut.conj g).toMonoidHom).map MulAut.conj := by
    rw [hEd, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap]
  refine localDeltaIn_eq_bot_langModel_E8 hTw K L hFr hp (by omega) hpq hg0C hg0 hH _ ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hpow₀ y (hED hy), mul_one, mul_inv_cancel]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [hD₀card] at hEcard
    by_contra hle
    push Not at hle
    have h1 : p ^ 3 ≤ p * p := hEcard.trans (Nat.mul_le_mul_left p hle)
    have h2 : p * p < p ^ 3 := by
      have := hp.two_le
      nlinarith
    omega
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := hEH y hy
    rw [Subgroup.mem_subgroupOf] at h1
    exact (hH₀T h1).1

end Twisted

section Family


theorem crossCharInnerAt_E8_dvd_add_one_of_twisted (hTw : E8TwistedResidual) :
    CrossCharInnerAt .E8 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧ p ∣ q.card + 1) ∧ 7 ≤ p := by
  rintro ⟨d, hv⟩ _ p hp _ _ ⟨⟨q, hd, hpq⟩, hp7⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at hpq
  exact (isInnerLocallyBalanced_adjointE8_of_dvd_add_one_of_twisted hTw K hp hp7 hpq).of_mulEquiv e

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
