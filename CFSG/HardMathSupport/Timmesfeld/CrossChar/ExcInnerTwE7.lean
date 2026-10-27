module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def E7TwistedResidual :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card K) → 5 ∣ Nat.card K + 1 →
      ∀ g0 ∈ adjointGroup Tag.E7 L, Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.E7) L e7Neg →
          RootSL2Generated (e7Model K L g0) ∧ RootComponentsQuasisimple (e7Model K L g0) 5

theorem exists_orderOf_eq_of_dvd_add_one (K : Type) [Field K] [Finite K] {L : Type} [Field L]
    [Algebra K L] [IsAlgClosed L] {N : ℕ} (hN : N ∣ Nat.card K + 1) :
    ∃ ζ : Lˣ, orderOf ζ = N ∧ ζ ^ (Nat.card K + 1) = 1 := by
  classical
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have : NeZero ((N : ℕ) : L) := ⟨by
    obtain ⟨m, hm⟩ := hN
    intro hN0
    have h1 : ((Nat.card K + 1 : ℕ) : L) = 0 := by rw [hm, Nat.cast_mul, hN0, zero_mul]
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1⟩
  have hNpos : N ≠ 0 := fun h0 => by
    rw [h0] at hN
    exact absurd (Nat.eq_zero_of_zero_dvd hN) (by omega)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  set ζu : Lˣ := (hζ.isUnit hNpos).unit with hζu
  have hζu' : IsPrimitiveRoot ζu N :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  refine ⟨ζu, hζu'.eq_orderOf.symm, ?_⟩
  obtain ⟨m, hm⟩ := hN
  rw [hm, pow_mul, hζu'.pow_eq_one, one_pow]

section Twisted


theorem isInnerLocallyBalanced_adjointE7_five_of_twisted (h : E7TwistedResidual) (K : Type)
    [Field K] [Finite K] (h5 : 5 ∣ Nat.card K + 1)
    (hord : (Nat.card (adjointGroup Tag.E7 K)).factorization 5 =
      7 * (Nat.card K + 1).factorization 5 + 1) :
    IsInnerLocallyBalanced 5 (adjointGroup Tag.E7 K) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E7 K e7Neg
  set L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set n := canonicalRep (coxeterSystem Tag.E7) L e7Neg with hn
  set M := e7Model K L g0 with hM
  have := finite_e7Model K L g0
  set e := e7ModelEquiv K L g0
  obtain ⟨hgen, hqs⟩ := h K L Fr hFr h5 g0 hg0C hg0
  have hMtw := e7Model_le_twModel K L hFr hg0C hg0
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH _
  have hZ : Subgroup.center M = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [center_adjointGroup_eq_bot, Subgroup.map_bot] at h1
    exact h1.symm
  have hinj : Function.Injective (MulAut.conj : M →* MulAut M) := by
    intro g g' hgg
    have hc : g'⁻¹ * g ∈ Subgroup.center M :=
      Subgroup.mem_center_iff.2 fun x => by
        have e1 := congrArg (fun φ : MulAut M => φ x) hgg
        simp only [MulAut.conj_apply] at e1
        calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
          _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [e1]
          _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  set D₀ := D.comap (MulAut.conj : M →* MulAut M) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hpow₀ : ∀ y ∈ D₀, y ^ 5 = 1 := fun y hy => hinj (by
    rw [map_pow, show (MulAut.conj y) ^ 5 = 1 from hD.2 _ hy, map_one])
  have hD₀card : Nat.card D₀ = 5 ^ 3 := by
    rw [← hcard]
    conv_rhs => rw [← hDD]
    rw [Subgroup.card_map_of_injective hinj]
  have hD₀p : IsPGroup 5 D₀ := IsPGroup.of_card hD₀card
  set a := (Nat.card K + 1).factorization 5 with ha
  obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_add_one K (L := L)
    (Nat.ordProj_dvd (Nat.card K + 1) 5)
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card (L := L)
    rootDiagUnit_mem_torusGroup_E7 e7Neg_smul hFr hζq
  rw [hζord, ← pow_mul] at hH₀card
  have : Finite H₀ := Nat.finite_of_card_ne_zero (by rw [hH₀card]; positivity)
  have hH₀M : H₀ ≤ M := le_e7Model_of_le_twModel K L hFr hg0C hg0
    (hH₀T.trans (twistedTorus_le_twModel n Fr)) Nat.prime_five (by norm_num)
    (IsPGroup.of_card hH₀card)
  have hfac : (Nat.card (⊤ : Subgroup M)).factorization 5 ≤
      (Nat.card (H₀.subgroupOf M)).factorization 5 + 1 := by
    rw [Subgroup.card_top, ← Nat.card_congr e.toEquiv, hord,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀M).toEquiv, hH₀card,
      Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
      show Tag.E7.rank = 7 from rfl]
    omega
  obtain ⟨g, -, E, hED, hEcard, hEH⟩ := exists_large_conj_le_of_sylow (p := 5) (Y := ⊤)
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
  obtain ⟨ζ₅, hζ₅, hζ₅q⟩ := exists_orderOf_eq_of_dvd_add_one K (L := L) h5
  have hζ₅2 : ζ₅ ^ 2 ≠ 1 := fun h2 => by
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζ₅] at h3
    norm_num at h3
  refine localDeltaIn_eq_bot_of_rootSL2 (A := M) (e7Model_le_adjointGroup K L hg0C) hinj
    Nat.prime_five hζ₅ hζ₅2 (fun w k => ?_) hgen hqs hH _ ?_ ?_ ?_
  ·
    set x := canonicalRep (coxeterSystem Tag.E7) L w * torusElt Tag.E7 L k ζ₅ *
      (canonicalRep (coxeterSystem Tag.E7) L w)⁻¹ with hx
    have hxT : x ∈ twistedTorus n Fr :=
      coroot_mem_twistedTorus rootDiagUnit_mem_torusGroup_E7 e7Neg_smul hFr hζ₅q w k
    have hxord : orderOf x = 5 := orderOf_canonicalRep_conj_torusElt Nat.prime_five w k hζ₅ hζ₅2
    have : Finite (Subgroup.zpowers x) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hxord]; norm_num)
    have hZx : Subgroup.zpowers x ≤ M := le_e7Model_of_le_twModel K L hFr hg0C hg0
      ((Subgroup.zpowers_le).2 (twistedTorus_le_twModel n Fr hxT)) Nat.prime_five (by norm_num)
      (IsPGroup.of_card (by rw [Nat.card_zpowers, hxord, pow_one]))
    exact hZx (Subgroup.mem_zpowers x)
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hpow₀ y (hED hy), mul_one, mul_inv_cancel]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [hD₀card] at hEcard
    by_contra hle
    push Not at hle
    have : 5 ^ 3 ≤ 5 * 5 := hEcard.trans (Nat.mul_le_mul_left 5 hle)
    norm_num at this
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := hEH y hy
    rw [Subgroup.mem_subgroupOf] at h1
    exact (hH₀T h1).1

end Twisted

section Family


theorem crossCharInnerAt_E7_five_of_twisted (hTw : E7TwistedResidual)
    (hord : ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
      (Nat.card (adjointGroup Tag.E7 K)).factorization 5 =
        7 * (Nat.card K + 1).factorization 5 + 1) :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card + 1) ∧ p = 5 := by
  rintro ⟨d, hv⟩ _ p _ _ _ ⟨⟨q, hd, h5⟩, rfl⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at h5
  exact (isInnerLocallyBalanced_adjointE7_five_of_twisted hTw K h5 (hord K h5)).of_mulEquiv e

theorem crossCharInnerAt_E7_five_sq_of_twisted (hTw : E7TwistedResidual)
    (hord : ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
      (Nat.card (adjointGroup Tag.E7 K)).factorization 5 =
        7 * (Nat.card K + 1).factorization 5 + 1) :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5 :=
  crossCharInnerAt_E7_five_of_add_one (crossCharInnerAt_E7_five_of_twisted hTw hord)

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
