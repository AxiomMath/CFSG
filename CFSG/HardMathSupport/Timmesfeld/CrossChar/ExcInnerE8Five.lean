module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator Polynomial
open scoped Matrix

theorem orderOf_natCast_zmod_five_of_dvd_sq_add_one {n : ℕ} (h5 : 5 ∣ n ^ 2 + 1) :
    orderOf ((n : ℕ) : ZMod 5) = 4 := by
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h0
  have hx2 : ((n : ℕ) : ZMod 5) ^ 2 = -1 := eq_neg_of_add_eq_zero_left h0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ¬ ((n : ℕ) : ZMod 5) ^ 2 ^ 1 = 1 := by
    rw [pow_one, hx2]
    decide
  have h2 : ((n : ℕ) : ZMod 5) ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx2]
    decide
  exact orderOf_eq_prime_pow h1 h2

theorem not_five_dvd_of_dvd_sq_add_one {n : ℕ} (h5 : 5 ∣ n ^ 2 + 1) : ¬ 5 ∣ n := by
  intro h
  have h1 : 5 ∣ n ^ 2 := dvd_pow h (by norm_num)
  have h2 : 5 ∣ n ^ 2 + 1 - n ^ 2 := Nat.dvd_sub h5 h1
  rw [show n ^ 2 + 1 - n ^ 2 = 1 by omega] at h2
  norm_num at h2

theorem five_dvd_sq_sub_one_or_sq_add_one {n : ℕ} (hn : ¬ 5 ∣ n) :
    5 ∣ n ^ 2 - 1 ∨ 5 ∣ n ^ 2 + 1 := by
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => hn (h0 ▸ dvd_zero 5))
  have h0 : ((n : ℕ) : ZMod 5) ≠ 0 := fun h => hn ((ZMod.natCast_eq_zero_iff n 5).1 h)
  have key : ∀ x : ZMod 5, x ≠ 0 → x ^ 2 - 1 = 0 ∨ x ^ 2 + 1 = 0 := by decide
  rcases key _ h0 with h | h
  · left
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hn1, Nat.cast_pow, Nat.cast_one]
    exact h
  · right
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    exact h

theorem factorization_pow_four_sub_one_of_dvd_sq_add_one {q : ℕ} (hq : 2 ≤ q)
    (h5 : 5 ∣ q ^ 2 + 1) : (q ^ 4 - 1).factorization 5 = (q ^ 2 + 1).factorization 5 := by
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
    have : q ^ 4 = (q ^ 2) ^ 2 := by ring
    rw [this]
    zify [hq1, Nat.one_le_pow 2 (q ^ 2) (by omega)]
    ring
  have hne : ¬ 5 ∣ q ^ 2 - 1 := by
    intro h1
    have h2 : 5 ∣ (q ^ 2 + 1) - (q ^ 2 - 1) := Nat.dvd_sub h5 h1
    rw [show q ^ 2 + 1 - (q ^ 2 - 1) = 2 by omega] at h2
    norm_num at h2
  have hpos : q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  rw [h4, Nat.factorization_mul (by omega) hpos, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hne, add_zero]

noncomputable abbrev e8PhiFourWeyl :
    WeylGroup Tag.E8 :=
  (coxeterSystem Tag.E8).wordProd e8FourWord

section Four


theorem factorization_five_card_adjointGroup_E8_of_dvd_sq_add_one (K : Type) [Field K]
    [Finite K] (h5 : 5 ∣ Nat.card K ^ 2 + 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
      4 * (Nat.card K ^ 4 - 1).factorization 5 + 1 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpq := not_five_dvd_of_dvd_sq_add_one h5
  have he := orderOf_natCast_zmod_five_of_dvd_sq_add_one h5
  have h := ordProj_card_adjointGroup_E (τ := Tag.E8) (K := K) (by simp) Nat.prime_five
    (by norm_num) hpq
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  have hlte : ∀ k : ℕ, k ≠ 0 → 5 ^ (Nat.card K ^ (4 * k) - 1).factorization 5 =
      5 ^ (Nat.card K ^ 4 - 1).factorization 5 * 5 ^ k.factorization 5 := fun k hk =>
    ordProj_pow_sub_one_of_dvd Nat.prime_five (by norm_num) hpq hq2 he hk
  have hnd : ∀ d : ℕ, ¬ 4 ∣ d → 5 ^ (Nat.card K ^ d - 1).factorization 5 = 1 := fun d hd =>
    ordProj_eq_one_of_not_dvd' fun h1 => hd ((dvd_pow_sub_one_iff_orderOf (by omega) he).1 h1)
  have h5f : 5 ^ (5 : ℕ).factorization 5 = 5 := by
    rw [Nat.Prime.factorization_self Nat.prime_five, pow_one]
  have h8 : 5 ^ (Nat.card K ^ 8 - 1).factorization 5 =
      5 ^ (Nat.card K ^ 4 - 1).factorization 5 * 5 ^ (2 : ℕ).factorization 5 := by
    have := hlte 2 (by norm_num)
    rwa [show 4 * 2 = 8 by norm_num] at this
  have h12 : 5 ^ (Nat.card K ^ 12 - 1).factorization 5 =
      5 ^ (Nat.card K ^ 4 - 1).factorization 5 * 5 ^ (3 : ℕ).factorization 5 := by
    have := hlte 3 (by norm_num)
    rwa [show 4 * 3 = 12 by norm_num] at this
  have h20 : 5 ^ (Nat.card K ^ 20 - 1).factorization 5 =
      5 ^ (Nat.card K ^ 4 - 1).factorization 5 * 5 ^ (5 : ℕ).factorization 5 := by
    have := hlte 5 (by norm_num)
    rwa [show 4 * 5 = 20 by norm_num] at this
  have h24 : 5 ^ (Nat.card K ^ 24 - 1).factorization 5 =
      5 ^ (Nat.card K ^ 4 - 1).factorization 5 * 5 ^ (6 : ℕ).factorization 5 := by
    have := hlte 6 (by norm_num)
    rwa [show 4 * 6 = 24 by norm_num] at this
  rw [hnd 2 (by norm_num), h8, h12, hnd 14 (by norm_num), hnd 18 (by norm_num), h20, h24,
    hnd 30 (by norm_num), ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 2),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 3),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6), h5f] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_card_adjointE8_le_of_dvd_sq_add_one (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K ^ 2 + 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization 5 ≤
      (((wordMat Tag.E8 e8FourWord).charpoly.eval (Nat.card K : ℤ)).natAbs).factorization 5 +
        1 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have he := orderOf_natCast_zmod_five_of_dvd_sq_add_one h5
  have h2 := ordProj_charpoly_eval_of_blocks Nat.prime_five le_rfl hq2 he (by norm_num) _
    e8Four_charpoly (by decide)
  have h3 : [4, 4, 4, 4].count 4 = 4 := by decide
  rw [h3, ← pow_mul] at h2
  rw [factorization_five_card_adjointGroup_E8_of_dvd_sq_add_one K h5,
    Nat.pow_right_injective (by norm_num : 2 ≤ 5) h2, mul_comm]

theorem isInnerLocallyBalanced_adjointE8_five_of_dvd_sq_add_one
    (hres : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1)
    (K : Type) [Field K] [Finite K] (h5 : 5 ∣ Nat.card K ^ 2 + 1) :
    IsInnerLocallyBalanced 5 (adjointGroup Tag.E8 K) :=
  isInnerLocallyBalanced_adjoint_of_langTorus 1 (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (wordProd_smul_eq_wordMat_mulVec Tag.E8 e8FourWord) (n := 4) (by norm_num) e8Four_pow
    Nat.prime_five (by norm_num) hres K h5
    (charpoly_eval_ne_zero_of_blocks Finite.one_lt_card _ e8Four_charpoly)
    (factorization_card_adjointE8_le_of_dvd_sq_add_one K h5)

end Four


section Neg


theorem langTorusPlaneBalance_E8_neg_of_twisted (hTw : E8TwistedResidual) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : LangTorusPlaneBalance Tag.E8 e8Neg p fun q => p ∣ q + 1 := by
  intro K _ _ hQ Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  set L := AlgebraicClosure K
  set M := langModel Tag.E8 K L g0 with hM
  let e : adjointGroup Tag.E8 K ≃* M :=
    ((adjointGroup Tag.E8 K).equivMapOfInjective _ (baseChangeGL_injective _)).trans
      ((MulAut.conj g0⁻¹).subgroupMap _)
  set ψ : MulAut (adjointGroup Tag.E8 K) →* MulAut M := (MulAut.congr e).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr e).injective
  have hconj : ∀ x : adjointGroup Tag.E8 K, ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext z
    simp [hψ, MulAut.congr_apply, MulAut.conj_apply]
  have he_val : ∀ x : adjointGroup Tag.E8 K, ((e x : M) : ModGL Tag.E8 L) =
      g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) * g0⁻¹⁻¹ := fun x => by
    change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K)) = _
    rw [MulAut.conj_apply]
  set E₀ : Subgroup M := D₀.map e.toMonoidHom with hE₀
  have hE₀pow : ∀ y ∈ E₀, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change e x ^ p = 1
    rw [← map_pow, hpow x hx, map_one]
  have hE₀card : p < Nat.card E₀ := by
    rw [hE₀, Subgroup.card_map_of_injective e.injective]
    exact hcard
  have hE₀tor : ∀ y ∈ E₀, (y : ModGL Tag.E8 L) ∈ torusGroup Tag.E8 L := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hte⟩ := htor x hx
    change ((e x : M) : ModGL Tag.E8 L) ∈ torusGroup Tag.E8 L
    rw [he_val, inv_inv, ← hte]
    change g0⁻¹ * (g0 * t * g0⁻¹) * g0 ∈ torusGroup Tag.E8 L
    rw [show g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t by group]
    exact (mem_twistedTorusOf.1 ht).1
  have hH' : innerAut M ≤ H.map ψ := by
    rintro _ ⟨m, rfl⟩
    refine ⟨MulAut.conj (e.symm m), hH ⟨e.symm m, rfl⟩, ?_⟩
    rw [hconj, MulEquiv.apply_symm_apply]
  have h0 := localDeltaIn_eq_bot_langModel_E8 hTw K L hFr hp hp5 hQ hg0C hg0 hH' E₀ hE₀pow
    hE₀card hE₀tor
  have hDmap : (D₀.map (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K))).map
      ψ = E₀.map (MulAut.conj : M →* MulAut M) := by
    rw [Subgroup.map_map, hE₀, Subgroup.map_map]
    congr 1
    ext x : 1
    exact hconj x
  have hle := map_localDeltaIn_le p ψ hψinj H
    (D₀.map (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)))
  rw [hDmap, h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψinj] at hle
  exact hle

end Neg

@[expose] def E8FiveToralPlane :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 5 ∣ Nat.card K →
    ∀ A : Subgroup (adjointGroup Tag.E8 K), (∀ x ∈ A, x ^ 5 = 1) → Nat.card A = 5 ^ 2 →
      ∃ w : WeylGroup Tag.E8, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ Nat.card K) ∧
        ∃ g0 ∈ adjointGroup Tag.E8 (AlgebraicClosure K),
          Units.map (entrywiseHom Fr) g0 =
            g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w ∧
          ∃ c : adjointGroup Tag.E8 K, ∀ x ∈ A,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom

theorem exists_subgroup_card_sq_le {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {D : Subgroup G} (hcard : Nat.card D = p ^ 3) :
    ∃ A ≤ D, Nat.card A = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) p
    (show p ^ 2 ∣ Nat.card D by rw [hcard]; exact pow_dvd_pow p (by norm_num))
  refine ⟨A₀.map D.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective D.subtype_injective, hA₀]

section Toral


theorem isInnerLocallyBalanced_adjointE8_five_of_toral (htor : E8FiveToralPlane) {Q : ℕ → Prop}
    (hT1 : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 5 Q) (K : Type) [Field K]
    [Finite K] (h5 : ¬ 5 ∣ Nat.card K) (hQ : Q (Nat.card K)) :
    IsInnerLocallyBalanced 5 (adjointGroup Tag.E8 K) := by
  intro D hD hcard hDin H hH _
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E8) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K))
    with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = 5 ^ 3 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ 5 = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ 5 = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  obtain ⟨A, hAD₀, hAcard⟩ := exists_subgroup_card_sq_le Nat.prime_five hD₀card
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ :=
    htor K h5 A (fun x hx => hpow₀ x (hAD₀ hx)) hAcard
  refine localDeltaIn_eq_bot_of_conj_sub hH (E := A) ?_ c ?_
  · rw [← hDD]
    exact Subgroup.map_mono hAD₀
  · refine hT1 w K hQ Fr hFr g0 hg0C hg0 _ ?_ ?_ ?_ H hH
    · rintro _ ⟨x, hx, rfl⟩
      change (c * x * c⁻¹) ^ 5 = 1
      rw [conj_pow, hpow₀ x (hAD₀ hx), mul_one, mul_inv_cancel]
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hAcard]
      norm_num
    · rintro _ ⟨x, hx, rfl⟩
      exact hc x hx

end Toral

section Family


theorem crossCharInnerAt_E8_five_of_parts (htor : E8FiveToralPlane)
    (hSplit : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q - 1)
    (hNeg : ∀ w : WeylGroup Tag.E8, w ≠ e8Neg →
      LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q + 1)
    (hTw : E8TwistedResidual)
    (hFour : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1) :
    CrossCharInnerAt .E8 fun _ p => p = 5 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.E8 q := hk
  subst hq
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have h5 : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  rcases five_dvd_sq_sub_one_or_sq_add_one h5 with h | h
  · rcases five_dvd_sq_sub_one_iff_or.1 h with h1 | h1
    · exact isInnerLocallyBalanced_adjointE8_five_of_toral htor hSplit K h5 h1
    · refine isInnerLocallyBalanced_adjointE8_five_of_toral htor (Q := fun q => 5 ∣ q + 1)
        (fun w => ?_) K h5 h1
      by_cases hw : w = e8Neg
      · have hb := langTorusPlaneBalance_E8_neg_of_twisted hTw Nat.prime_five le_rfl
        rw [← hw] at hb
        exact hb
      · exact hNeg w hw
  · exact isInnerLocallyBalanced_adjointE8_five_of_dvd_sq_add_one hFour K h

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
