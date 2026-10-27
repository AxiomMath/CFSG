module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreAlmost
public import CFSG.RankThree.PartTwo.KFacts.K71L28Cent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open scoped MatrixGroups
open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (rank_two_has_coordinate_embedding
  embedded_rank_two_signalizer_le_of_line_centralizers coordinatePairLineHom)
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem k1Core_not_three_dvd {n : ℕ} (hn : Nat.Coprime n 6) : ¬ 3 ∣ n :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Nat.Coprime.coprime_dvd_right (by norm_num) hn).symm

theorem k1Core_psl28_field_eq_bot {σ : GaloisField 2 3 ≃+* GaloisField 2 3} (hσ : orderOf σ = 3)
    {N : Subgroup (MulAut PSL(2, GaloisField 2 3))}
    (hNc : ∀ ν ∈ N, ν * psl2FieldAut _ σ = psl2FieldAut _ σ * ν)
    (hN : Nat.Coprime (Nat.card N) 6) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN3 := k1Core_not_three_dvd hN
  set φ := CFSG.RankThree.PartTwo.KFacts.sl2EquivPSL28.symm with hφ
  rw [eq_bot_iff]
  intro ν hν
  rw [Subgroup.mem_bot]
  obtain ⟨y, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_of_pow_eq_one_psl28 hN3
    (CFSG.RankThree.PartTwo.KFacts.pow_card_eq_one_of_mem hν)
  have hyσ : psl2FieldAut _ σ y = y := by
    have h1 := hNc _ hν
    have h2 : MulAut.conj y = MulAut.conj (psl2FieldAut _ σ y) := by
      rw [← CFSG.RankThree.PartTwo.KFacts.mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    have h3 : MulAut.conj (psl2FieldAut _ σ y * y⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h2, mul_inv_cancel]
    exact mul_inv_eq_one.mp (CFSG.RankThree.PartTwo.KFacts.eq_one_of_conj_eq_one_psl28 h3)
  have hy6 : y ^ 6 = 1 := by
    have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom (φ y) = φ y := by
      rw [← CFSG.RankThree.PartTwo.KFacts.psl2MulEquivSL2_psl2FieldAut, hyσ]
    have hmap' : (φ y).1.map σ.toRingHom = (φ y).1 := congrArg Subtype.val hmap
    have htr : σ (φ y).1.trace = (φ y).1.trace := by
      conv_rhs => rw [← hmap']
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]
      rfl
    have h6 := CFSG.RankThree.PartTwo.KFacts.mat2_pow_six_eq_one_of_trace (φ y).2
      (CFSG.RankThree.PartTwo.KFacts.eq_zero_or_eq_one_of_fixed hσ htr)
    have h1 : φ y ^ 6 = 1 := Subtype.ext h6
    rw [← map_pow] at h1
    exact (map_eq_one_iff φ φ.injective).1 h1
  have hyn : y ^ Nat.card N = 1 := by
    have h1 := CFSG.RankThree.PartTwo.KFacts.pow_card_eq_one_of_mem hν
    rw [← map_pow] at h1
    exact CFSG.RankThree.PartTwo.KFacts.eq_one_of_conj_eq_one_psl28 h1
  have h1 : y ^ Nat.gcd (Nat.card N) 6 = 1 := pow_gcd_eq_one.mpr ⟨hyn, hy6⟩
  rw [hN.gcd_eq_one, pow_one] at h1
  rw [h1, map_one]

theorem k1Core_psl28_eq_bot {ε : MulAut PSL(2, GaloisField 2 3)} (hε3 : ε ^ 3 = 1)
    (hε1 : ε ≠ 1) {N : Subgroup (MulAut PSL(2, GaloisField 2 3))}
    (hNc : ∀ ν ∈ N, ν * ε = ε * ν) (hN : Nat.Coprime (Nat.card N) 6) : N = ⊥ := by
  have hN3 := k1Core_not_three_dvd hN
  by_cases hD : ε ∈ (pglAction (GaloisField 2 3)).range
  · obtain ⟨g, rfl⟩ := hD
    obtain ⟨s, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.toPGL_surjective_psl28 g
    rw [pglAction_toPGL] at hε3 hε1 hNc
    have hs3 : s ^ 3 = 1 := by
      rw [← map_pow] at hε3
      exact CFSG.RankThree.PartTwo.KFacts.eq_one_of_conj_eq_one_psl28 hε3
    have hs1 : s ≠ 1 := fun h => hε1 (by rw [h, map_one])
    exact CFSG.RankThree.PartTwo.KFacts.psl28_eq_bot_of_commute_conj hs3 hs1 hNc hN3
  · have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hε1
    obtain ⟨σ, hσ, g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent
      Nat.prime_three ε hεo hD
    set φ := pglAction (GaloisField 2 3) g with hφ
    let ψ : MulAut PSL(2, GaloisField 2 3) →* MulAut PSL(2, GaloisField 2 3) :=
      (MulAut.conj φ⁻¹).toMonoidHom
    have hψa : ∀ ν, ψ ν = φ⁻¹ * ν * φ := fun ν => by
      simp only [ψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hψinj : Function.Injective ψ := (MulAut.conj φ⁻¹).injective
    have h0 : N.map ψ = ⊥ := by
      refine k1Core_psl28_field_eq_bot hσ ?_ ?_
      · rintro _ ⟨ν, hν, rfl⟩
        have h1 := hNc ν hν
        rw [hg] at h1
        rw [hψa]
        calc φ⁻¹ * ν * φ * psl2FieldAut _ σ =
              φ⁻¹ * (ν * (φ * psl2FieldAut _ σ * φ⁻¹)) * φ := by group
          _ = φ⁻¹ * ((φ * psl2FieldAut _ σ * φ⁻¹) * ν) * φ := by rw [h1]
          _ = psl2FieldAut _ σ * (φ⁻¹ * ν * φ) := by group
      · rwa [Subgroup.card_map_of_injective hψinj]
    exact (Subgroup.map_eq_bot_iff_of_injective N hψinj).mp h0

variable {X : Type} [Group X] [Finite X]

theorem k1Core_inf_centralizer_eq_bot_of_l28 {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) (e : K ≃* PSL(2, GaloisField 2 3)) {W : Subgroup X}
    (hW : Nat.Coprime (Nat.card W) 6) {a : X} (haA : a ∈ A) (ha1 : a ≠ 1) :
    W ⊓ Subgroup.centralizer ({a} : Set X) = ⊥ := by
  have := h.normal
  obtain ⟨ι, hι, -, -⟩ := k1Core_exists_action h.centralizer_eq_bot e
  have ha3 : a ^ 3 = 1 := h.elem.2 a haA
  have hN := k1Core_psl28_eq_bot (ε := ι a) (N := (W ⊓ Subgroup.centralizer ({a} : Set X)).map ι)
    (by rw [← map_pow, ha3, map_one]) (fun h1 => ha1 (hι (by rw [h1, map_one]))) ?_ ?_
  · exact (Subgroup.map_eq_bot_iff_of_injective _ hι).mp hN
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ι (Subgroup.mem_centralizer_singleton_iff.mp hw.2)
  · rw [Subgroup.card_map_of_injective hι]
    exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hW

theorem k1Core_eq_bot_of_l28 {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) (e : K ≃* PSL(2, GaloisField 2 3)) {W : Subgroup X}
    (hAW : A ≤ Subgroup.normalizer (W : Set X)) (hW : Nat.Coprime (Nat.card W) 6) : W = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hcop : Nat.Coprime 3 (Nat.card W) := (Nat.Coprime.coprime_dvd_right (by norm_num) hW).symm
  obtain ⟨emb, hinj, hrange⟩ := rank_two_has_coordinate_embedding 3 hp A
    (le_pRank_of_isElemAbelian hp h.elem h.card_A)
  refine le_bot_iff.mp
    (embedded_rank_two_signalizer_le_of_line_centralizers 3 hp emb W ⊥
      (fun x hx => hAW (hrange hx)) hcop ?_)
  intro v hv
  set a := emb (coordinatePairLineHom v (Multiplicative.ofAdd (1 : ZMod 3))) with ha
  have haR : a ∈ (emb.comp (coordinatePairLineHom v)).range := ⟨Multiplicative.ofAdd 1, rfl⟩
  have haA : a ∈ A := hrange ⟨_, rfl⟩
  have ha1 : a ≠ 1 := by
    intro h1
    have h2 := hinj (h1.trans (map_one emb).symm)
    have h3 : (Multiplicative.toAdd (coordinatePairLineHom v
        (Multiplicative.ofAdd (1 : ZMod 3)))) = 0 := by rw [h2]; rfl
    apply hv
    simpa [coordinatePairLineHom] using h3
  calc W ⊓ Subgroup.centralizer
        (((emb.comp (coordinatePairLineHom v)).range : Subgroup X) : Set X)
      ≤ W ⊓ Subgroup.centralizer ({a} : Set X) :=
        inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haR))
    _ = ⊥ := k1Core_inf_centralizer_eq_bot_of_l28 h e hW haA ha1

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
