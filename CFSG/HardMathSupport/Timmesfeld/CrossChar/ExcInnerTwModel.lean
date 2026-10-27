module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.RankThree.PartOne.K133H.F4Torus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.Timmesfeld.ExceptionalOrders CFSG.Open

theorem factorization_ordF4_of_dvd_add_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hd : p ∣ q + 1) : (ordF4 q).factorization p = 4 * (q + 1).factorization p := by
  have hp2 : p ≠ 2 := by omega
  have hpq : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hd h
    rw [show q + 1 - q = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpq1 : ¬ p ∣ q - 1 := by
    intro h
    have h1 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hd h
    rw [show q + 1 - (q - 1) = 2 by omega] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hQ : 2 ≤ q ^ 2 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rcases q with _ | q
    · omega
    · simp only [Nat.add_sub_cancel]
      ring_nf
      omega
  have hdQ : p ∣ q ^ 2 - 1 := hsq ▸ dvd_mul_of_dvd_right hd _
  have hsq0 : (q ^ 2 - 1).factorization p = (q + 1).factorization p := by
    rw [hsq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpq1, zero_add]
  have hnd : ∀ k : ℕ, k = 3 ∨ k = 4 ∨ k = 6 → ¬ p ∣ k := by
    intro k hk h
    have hle : p ≤ k := Nat.le_of_dvd (by omega) h
    have hk6 : p ≤ 6 := by omega
    interval_cases p <;> rcases hk with rfl | rfl | rfl <;> first | omega | (norm_num at hp)
  have hpow : ∀ k : ℕ, k = 3 ∨ k = 4 ∨ k = 6 →
      ((q ^ 2) ^ k - 1).factorization p = (q + 1).factorization p := fun k hk => by
    rw [CFSG.RankThree.PartOne.K133H.factorization_pow_sub_one hp hp2 hQ hdQ (by omega)
      (hnd k hk), hsq0]
  have h12 : q ^ 12 - 1 = (q ^ 2) ^ 6 - 1 := by rw [← pow_mul]
  have h8 : q ^ 8 - 1 = (q ^ 2) ^ 4 - 1 := by rw [← pow_mul]
  have h6 : q ^ 6 - 1 = (q ^ 2) ^ 3 - 1 := by rw [← pow_mul]
  have hne : ∀ k, k ≠ 0 → q ^ k - 1 ≠ 0 := fun k hk =>
    Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by omega : 1 < q) (Nat.le_self_pow hk q))
  have hq24 : q ^ 24 ≠ 0 := by positivity
  have e12 := hne 12 (by norm_num)
  have e8 := hne 8 (by norm_num)
  have e6 := hne 6 (by norm_num)
  have e2 := hne 2 (by norm_num)
  unfold ordF4
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hq24 e12) e8) e6) e2,
    Nat.factorization_mul (mul_ne_zero (mul_ne_zero hq24 e12) e8) e6,
    Nat.factorization_mul (mul_ne_zero hq24 e12) e8, Nat.factorization_mul hq24 e12]
  simp only [Finsupp.add_apply]
  rw [h12, h8, h6, hpow 6 (by omega), hpow 4 (by omega), hpow 3 (by omega), hsq0,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hpq (hp.dvd_of_dvd_pow h))]
  ring

section Model

variable (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]


noncomputable def twModelEquivF4 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) L f4Neg) :
    adjointGroup Tag.F4 K ≃* twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr :=
  ((adjointGroup Tag.F4 K).equivMapOfInjective _ (baseChangeGL_injective _)).trans
    ((MulEquiv.subgroupCongr ((map_conj_twModel hg0C hg0).trans
      (G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl) K L Fr hFr).1)).symm.trans
      ((MulAut.conj g0).subgroupMap _).symm)

theorem finite_twModelF4 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) L f4Neg) :
    Finite (twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr) := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  exact Finite.of_equiv _ (twModelEquivF4 K L hFr hg0C hg0).toEquiv

theorem card_twModelF4 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) L f4Neg) :
    Nat.card (twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr) =
      ordF4 (Nat.card K) := by
  rw [← Nat.card_congr (twModelEquivF4 K L hFr hg0C hg0).toEquiv, card_adjointGroup_F4]

theorem exists_conj_into_twistedTorus_F4 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) L f4Neg)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    {A : Subgroup (ModGL Tag.F4 L)}
    (hA : A ≤ twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr)
    (hpow : ∀ x ∈ A, x ^ p = 1) :
    ∃ g ∈ twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr,
      A.map (MulAut.conj g).toMonoidHom ≤
        twistedTorus (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set n := canonicalRep (coxeterSystem Tag.F4) L f4Neg with hn
  set M := twModel n Fr with hM
  have := finite_twModelF4 K L hFr hg0C hg0
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have : NeZero (((Nat.card K + 1 : ℕ)) : L) := ⟨by
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one]
    exact one_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card K + 1)
  set ζu : Lˣ := (hζ.isUnit (by omega)).unit with hζu
  have hζu' : IsPrimitiveRoot ζu (Nat.card K + 1) :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  have hord : orderOf ζu = Nat.card K + 1 := hζu'.eq_orderOf.symm
  have hζpow : ζu ^ (Nat.card K + 1) = 1 := hζu'.pow_eq_one
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card (L := L)
    (rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec) f4Neg_smul hFr
    hζpow
  have hH₀M : H₀ ≤ M := hH₀T.trans (twistedTorus_le_twModel n Fr)
  have hfac : (Nat.card (⊤ : Subgroup M)).factorization p =
      (Nat.card (H₀.subgroupOf M)).factorization p := by
    rw [Subgroup.card_top, card_twModelF4 K L hFr hg0C hg0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀M).toEquiv, hH₀card, hord,
      factorization_ordF4_of_dvd_add_one hp hp5 hq2 hpq, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul]
    rfl
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (p := p) (Y := ⊤)
    (H := H₀.subgroupOf M)
    (A := A.subgroupOf M) le_top le_top (fun x hx => by
      apply Subtype.ext
      simpa using hpow x.1 (Subgroup.mem_subgroupOf.1 hx)) hfac
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hg ⟨⟨x, hA hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  exact hH₀T (Subgroup.mem_subgroupOf.1 h1)

end Model

end CFSG.HardMathSupport.Timmesfeld.CrossChar
