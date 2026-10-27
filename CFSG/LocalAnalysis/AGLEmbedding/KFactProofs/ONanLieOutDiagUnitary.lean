module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagLevi
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSU
import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped commutatorElement

theorem NoAp.of_dvd {p : ℕ} {S : Type} [Group S] [Finite S] {r : ℕ}
    (hrA : ¬ r ∣ Nat.card (alternatingGroup (Fin p))) (hrS : r ∣ Nat.card S) : NoAp p S := by
  intro R _ _ ι hι f hf
  have h1 : Nat.card S ∣ Nat.card R := by
    have := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top] at this
    exact ⟨Nat.card f.ker, by rw [← this, mul_comm]⟩
  have h2 : Nat.card R ∣ Nat.card (alternatingGroup (Fin p)) := by
    have := Subgroup.card_dvd_of_le (le_top : ι.range ≤ ⊤)
    rw [Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm, Subgroup.card_top] at this
    exact this
  exact hrA (hrS.trans (h1.trans h2))

theorem exists_quasisimple_of_node_equiv {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J)
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (h : BorelQuotient D n H π M) {π' : K →* ↥L ⧸ Subgroup.center ↥L}
    (hker : π'.ker = π.ker) {i : Fin D.rank}
    (hiJ : (rankOne D.rootGroup i).map π' ≤ quotImage L J) {p : ℕ} (hp : p.Prime)
    {G : Type} [Group G] [Finite G] (e : ↥(rankOne D.rootGroup i) ≃* G)
    (hG : CFSG.Open.IsQuasisimple G) (hpG : p ∣ Nat.card G)
    (hc : ¬ p ∣ Nat.card (Subgroup.center G)) (hno : NoAp p (G ⧸ Subgroup.center G)) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin p), ¬ φ.ker ≤ Subgroup.center ↥X := by
  classical
  set R := rankOne D.rootGroup i with hR
  let ρ : G →* (↥L ⧸ Subgroup.center ↥L) := (π'.comp R.subtype).comp e.symm.toMonoidHom
  have hrange : ρ.range = R.map π' := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(e.symm g : K), (e.symm g).2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨e ⟨r, hr⟩, by simp [ρ]⟩
  have hker_ρ : ρ.ker ≤ Subgroup.center G := by
    intro g hg
    have hg1 : π' (e.symm g : K) = 1 := hg
    have hc' : (e.symm g : K) ∈ Subgroup.center K := h.ker_central _ (hker ▸ hg1)
    rw [Subgroup.mem_center_iff]
    intro t
    apply e.symm.injective
    apply Subtype.ext
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc' (e.symm t : K)
  have hpS : p ∣ Nat.card ρ.range := by
    have hker_dvd : Nat.card ρ.ker ∣ Nat.card (Subgroup.center G) :=
      Subgroup.card_dvd_of_le hker_ρ
    have hcard := Subgroup.card_ker_mul_card_range ρ
    have : p ∣ Nat.card ρ.ker * Nat.card ρ.range := hcard ▸ hpG
    rcases (Nat.Prime.dvd_mul hp).1 this with h1 | h1
    · exact absurd (h1.trans hker_dvd) hc
    · exact h1
  exact exists_quasisimple_of_cover hZ ρ (hrange ▸ hiJ) hker_ρ hG hpS hno


theorem five_dvd_sq_sub_one {q : ℕ} (h : 5 ∣ q + 1) : 5 ∣ q ^ 2 - 1 := by
  have := Nat.sq_sub_sq q 1
  rw [one_pow] at this
  rw [this]
  exact Dvd.dvd.mul_right h _

theorem isQuasisimple_sl2 {k : Type} [Field k] [CharP k 2] (h4 : 4 ≤ Nat.card k) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have := sl2_isSimpleGroup h4
  exact ⟨(sl2_isPerfect h4).commutator_eq_top,
    ((QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩

theorem exists_quasisimple_of_node_sl2 {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J)
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (h : BorelQuotient D n H π M) {π' : K →* ↥L ⧸ Subgroup.center ↥L}
    (hker : π'.ker = π.ker) {i : Fin D.rank}
    (hiJ : (rankOne D.rootGroup i).map π' ≤ quotImage L J)
    {k : Type} [Field k] [Finite k] [CharP k 2]
    (e : ↥(rankOne D.rootGroup i) ≃* Matrix.SpecialLinearGroup (Fin 2) k)
    (h8 : 8 ∣ Nat.card k) (hk5 : 5 ∣ Nat.card k ^ 2 - 1) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ 5 ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin 5), ¬ φ.ker ≤ Subgroup.center ↥X := by
  have h8' : 8 ≤ Nat.card k := Nat.le_of_dvd Nat.card_pos h8
  have h4 : 4 ≤ Nat.card k := by omega
  have hcq : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k))
    have h1 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) = 1 := by
      rw [sl2_center_eq_bot, Subgroup.card_bot]
    rw [h1, mul_one] at h
    exact h.symm
  refine exists_quasisimple_of_node_equiv hZ h hker hiJ (p := 5) (by norm_num) e
    (isQuasisimple_sl2 h4) ?_ ?_ ?_
  · rw [card_sl2]
    exact Dvd.dvd.mul_left hk5 _
  · rw [sl2_center_eq_bot, Subgroup.card_bot]
    norm_num
  · refine NoAp.of_dvd (r := 8) ?_ ?_
    · rw [nat_card_alt_five]
      norm_num
    · rw [hcq, card_sl2]
      exact Dvd.dvd.mul_right h8 _


section SU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem not_dvd_card_center_su_three (hq : 4 ≤ 2 ^ f) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    ¬ r ∣ Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) 3)) := by
  intro hd
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hd
  have h3 := su_three_center_pow_three hF hq z.2
  have h3' := orderOf_dvd_of_pow_eq_one h3
  rw [Subgroup.orderOf_coe, hz] at h3'
  exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3')

include hF in
theorem exists_quasisimple_of_node_su {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J)
    {nW : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 f) n}
    {H : Fin (rootDatum hF n).rank → Subgroup (SU (unitaryInvolution F 2 f) n)}
    {π : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (h : BorelQuotient (rootDatum hF n) nW H π M)
    {π' : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L}
    (hker : π'.ker = π.ker) {i : Fin (n / 2)}
    (hiJ : (rankOne (rootDatum hF n).rootGroup i).map π' ≤ quotImage L J)
    (h5 : 5 ∣ 2 ^ f + 1) (hf2 : 2 ≤ f) (hgood : i.val + 1 < n / 2 ∨ ¬Even n ∨ 3 ≤ f) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ 5 ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin 5), ¬ φ.ker ≤ Subgroup.center ↥X := by
  have hσ := unitaryInvolution_involutive hF
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hq2 : 5 ∣ (2 ^ f) ^ 2 - 1 := five_dvd_sq_sub_one h5
  by_cases hk : i.val + 1 < n / 2
  ·
    refine exists_quasisimple_of_node_sl2 hZ h hker hiJ (k := F)
      (rankOneShortEquiv (hσ := hσ) hk) ?_ ?_
    · rw [hF]
      calc 8 = 2 ^ 3 := by norm_num
        _ ∣ 2 ^ (f * 2) := pow_dvd_pow 2 (by omega)
        _ = (2 ^ f) ^ 2 := pow_mul 2 f 2
    · rw [hF]
      have := Nat.sq_sub_sq ((2 ^ f) ^ 2) 1
      rw [one_pow] at this
      rw [this]
      exact Dvd.dvd.mul_left hq2 _
  · by_cases he : Even n
    ·
      have hf3 : 3 ≤ f := by
        rcases hgood with h1 | h1 | h1
        · exact absurd h1 hk
        · exact absurd he h1
        · exact h1
      obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
      refine exists_quasisimple_of_node_sl2 hZ h hker hiJ (k := fixedSubfield F 2 f)
        ((rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm) ?_ ?_
      · rw [card_fixedSubfield hF]
        exact pow_dvd_pow 2 hf3
      · rw [card_fixedSubfield hF]
        exact hq2
    ·
      have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := fun h' => by
        have := (Prod.mk.inj h').2
        omega
      have hQ : CFSG.Open.IsQuasisimple (SU (unitaryInvolution F 2 f) 3) := by
        obtain ⟨hperf, hsimple, -⟩ := isQuasisimple_SU hF le_rfl hnq
        exact ⟨hperf.commutator_eq_top, hsimple⟩
      have hc2 := not_dvd_card_center_su_three (F := F) hF hq4 (r := 2) Nat.prime_two (by norm_num)
      have hc5 := not_dvd_card_center_su_three (F := F) hF hq4 (r := 5) (by norm_num) (by norm_num)
      refine exists_quasisimple_of_node_equiv hZ h hker hiJ (p := 5) (by norm_num)
        (rankOneLastOddEquiv hF he hk) hQ ?_ hc5 ?_
      · rw [card_SU_three hF]
        exact (Dvd.dvd.mul_left hq2 _).mul_right _
      · refine NoAp.of_dvd (r := 8) ?_ ?_
        · rw [nat_card_alt_five]
          norm_num
        · have h8 : 8 ∣ Nat.card (SU (unitaryInvolution F 2 f) 3) := by
            rw [card_SU_three hF]
            refine ((Dvd.dvd.mul_right ?_ _).mul_right _)
            calc 8 = 2 ^ 3 := by norm_num
              _ ∣ (2 ^ f) ^ 3 := pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 3
          have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
            (Subgroup.center (SU (unitaryInvolution F 2 f) 3))
          have hcop : Nat.Coprime 8
              (Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) 3))) := by
            have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hc2
            exact Nat.Coprime.pow_left 3 this
          rw [hcard] at h8
          exact hcop.dvd_of_dvd_mul_right h8

end SU


theorem exists_quasisimple_of_model_psu (hbad : DiagLeviBad) {Y : Type} [Group Y] [Finite Y]
    {L J : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcl : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hpar : IsParabolicTwo L J) (hne : J ≠ L)
    (hnB : ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y))
    {n f : ℕ} (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f)
    (hpg : 5 ∣ Nat.gcd n (2 ^ f + 1)) {x : Y} (hx : x ∈ Subgroup.normalizer (L : Set Y))
    (hxp : x ^ 5 = 1) (hxo : x ∉ L ⊔ Subgroup.centralizer (L : Set Y))
    (hN : ∀ T : Subgroup Y, IsSylowTwoOf T L →
      5 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y)))
    (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ 5 ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin 5), ¬ φ.ker ≤ Subgroup.center ↥X := by
  have hpar' := hpar
  obtain ⟨hJL, T, hT, hNT⟩ := hpar'
  have h5n : 5 ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
  have h5q : 5 ∣ 2 ^ f + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f < 2 := by omega
    interval_cases f <;> simp at h5q
  obtain ⟨⟨-, -, hn, -⟩, F, hFf, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  have hB := borelQuotient_su hcard (by omega) ζ hζ e
  obtain ⟨π', hπ', hker, hBJ, i₀, hi₀⟩ := exists_rankOne_le_of_borel hB (barSylow hT)
    (quotImage L J) (normalizer_barSylow_le_quotImage hT hNT)
    (quotImage_ne_normalizer hT hJL (hnB T hT) hNT)
  have hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J :=
    fun z hz => center_le_of_normalizer_le hT hNT hz
  by_cases hex : ∃ i : Fin (n / 2), (i.val + 1 < n / 2 ∨ ¬Even n ∨ 3 ≤ f) ∧
      (rankOne (rootDatum hcard n).rootGroup i).map π' ≤ quotImage L J
  · obtain ⟨i, hgood, hiJ⟩ := hex
    exact exists_quasisimple_of_node_su hcard hZ hB hker hiJ h5q hf2 hgood
  · have hshort : ∀ i : Fin (n / 2), i.val + 1 < n / 2 →
        ¬ (rankOne (rootDatum hcard n).rootGroup i).map π' ≤ quotImage L J :=
      fun i hi hiJ => hex ⟨i, Or.inl hi, hiJ⟩
    have hgood₀ : ¬ (i₀.val + 1 < n / 2 ∨ ¬Even n ∨ 3 ≤ f) := fun hg => hex ⟨i₀, hg, hi₀⟩
    have hk₀ : ¬ i₀.val + 1 < n / 2 := fun h' => hgood₀ (Or.inl h')
    have heven : Even n := by
      by_contra h'
      exact hgood₀ (Or.inr (Or.inl h'))
    have hf3 : f < 3 := by
      by_contra h'
      exact hgood₀ (Or.inr (Or.inr (by omega)))
    obtain rfl : f = 2 := by omega
    exact hbad Y L J hL hcl hpar hne hnB n F hcard heven h5n π' hπ'
      (fun z hz => hB.ker_central z (hker ▸ hz)) ⟨hBJ, hshort, i₀, hk₀, hi₀⟩ x hx hxp hxo hN
      hfix

end CFSG.AGLEmbedding.LieOut
