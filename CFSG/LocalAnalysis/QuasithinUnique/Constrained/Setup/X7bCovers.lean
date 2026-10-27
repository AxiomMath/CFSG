module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearCover CFSG.SectionRank.EvenCover

variable {Q : Type} [Group Q]

noncomputable def centralQuotientEquiv (hQ : CFSG.IsQuasisimple Q) {A : Subgroup Q} [A.Normal]
    (hA : A ≤ center Q) : Q ⧸ center Q ≃* (Q ⧸ A) ⧸ center (Q ⧸ A) := by
  obtain ⟨-, hcomap, -⟩ := quasisimple_central_quotient hQ hA
  have hsurj := QuotientGroup.mk'_surjective A
  let φ := (QuotientGroup.mk' (center (Q ⧸ A))).comp (QuotientGroup.mk' A)
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hsurj
  have hφker : φ.ker = center Q := by
    rw [← hcomap]
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact QuotientGroup.liftEquiv _ hφ hφker.symm

theorem statedClassicalModel_psp_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n p f : ℕ} (h : StatedClassicalModel Y .PSp n p f) : StatedClassicalModel X .PSp n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem statedClassicalModel_psl_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n p f : ℕ} (h : StatedClassicalModel Y .PSL n p f) : StatedClassicalModel X .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem odd_card_center_quotient_twoPart [Finite Q] {A : Subgroup Q} [A.Normal]
    (hA : A = twoPart (center Q) le_rfl) (hQ : CFSG.IsQuasisimple Q) :
    Odd (Nat.card (center (Q ⧸ A))) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (center (Q ⧸ A)) := by
    rw [Nat.not_odd_iff_even] at hne
    exact even_iff_two_dvd.1 hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center (Q ⧸ A)) 2 h2
  have hz2 : (z : Q ⧸ A) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  obtain ⟨-, -, hmap⟩ := quasisimple_central_quotient hQ (A := A) (hA ▸ twoPart_le_center)
  have hzc : (z : Q ⧸ A) ∈ (center Q).map (QuotientGroup.mk' A) := hmap ▸ z.2
  obtain ⟨y, hy, hyz⟩ := hzc
  have hy2 : y ^ 2 ∈ A := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have : (QuotientGroup.mk y : Q ⧸ A) = z := hyz
    rw [this]
    exact hz2
  have hy2' : y ^ 2 ∈ twoPart (center Q) le_rfl := hA ▸ hy2
  obtain ⟨-, n, hn⟩ := hy2'
  have hyA : y ∈ A := by
    rw [hA]
    refine ⟨hy, n + 1, ?_⟩
    rw [pow_succ', pow_mul]
    exact hn
  have hz1 : (z : Q ⧸ A) = 1 := by
    rw [← hyz]
    exact (QuotientGroup.eq_one_iff y).2 hyA
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem statedScalars_subgroupOf_eq_bot_of_card_two {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hunit : Subsingleton Kˣ := by
    have h1 : Fintype.card Kˣ = 1 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    exact Fintype.card_le_one_iff_subsingleton.mp h1.le
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  rw [Subsingleton.elim c 1, map_one] at hc
  rw [Subgroup.mem_bot]
  exact Subtype.ext hc.symm

theorem perfect_full_central_covers_trivial
    [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (h : (∃ f : ℕ, 2 ≤ f ∧ LieModel (Q ⧸ center Q) .PSp 2 2 f) ∨
      (∃ n : ℕ, 5 ≤ n ∧ LieModel (Q ⧸ center Q) .PSL n 2 1)) :
    center Q = ⊥ ∧ Function.Bijective (QuotientGroup.mk' (center Q)) := by
  have hperf : Group.IsPerfect Q := hQ.1
  set Z2 := twoPart (center Q) le_rfl with hZ2
  have hZ2n : Z2.Normal := normal_of_le_center twoPart_le_center
  obtain ⟨hQo, hcomap, -⟩ := quasisimple_central_quotient hQ (A := Z2) twoPart_le_center
  have hodd : Odd (Nat.card (center (Q ⧸ Z2))) := odd_card_center_quotient_twoPart hZ2 hQ
  have e := centralQuotientEquiv hQ (A := Z2) twoPart_le_center
  have hperfo : Group.IsPerfect (Q ⧸ Z2) := hQo.1
  have hcen : center (Q ⧸ Z2) = ⊥ := by
    rcases h with ⟨f, hf, hmodel⟩ | ⟨n, hn, hmodel⟩
    · have hm := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
        (by decide : StatedLieTag.PSp ∈ classicalTags) hmodel
      have hm' := statedClassicalModel_psp_of_mulEquiv e.symm hm
      exact (even_symplectic_odd_cover_catalog_step hQo hodd hm').1
    · have hm := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
        (by decide : StatedLieTag.PSL ∈ classicalTags) hmodel
      obtain ⟨-, K, hK, hfin, hcard, ⟨e'⟩⟩ := statedClassicalModel_psl_of_mulEquiv e.symm hm
      have hK2 : Nat.card K = 2 := by rw [hcard, pow_one]
      have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (le_refl 1) hcard
      obtain ⟨φ, -, -, hD⟩ := even_linear_perfect_odd_cover_map (K := K) (n := n) (by omega) hodd e'
      rw [← hD, statedScalars_subgroupOf_eq_bot_of_card_two hK2, Subgroup.map_bot]
  have hZQ : center Q = Z2 := by
    refine le_antisymm (fun z hz => ?_) twoPart_le_center
    have h1 : z ∈ (center (Q ⧸ Z2)).comap (QuotientGroup.mk' Z2) := hcomap ▸ hz
    rw [hcen, Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  have hker : (QuotientGroup.mk' (center Q)).ker = center Q := QuotientGroup.ker_mk' _
  have h2 : IsPGroup 2 (QuotientGroup.mk' (center Q)).ker := by
    rw [hker, hZQ]
    exact isPGroup_twoPart
  have hη := QuotientGroup.mk'_surjective (center Q)
  rcases h with ⟨f, hf, hmodel⟩ | ⟨n, hn, hmodel⟩
  · obtain ⟨hbot, hbij⟩ :=
      SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial
        (QuotientGroup.mk' (center Q)) hη (by rw [hker]) h2 hf hmodel
    exact ⟨by rwa [hker] at hbot, hbij⟩
  · obtain ⟨hbot, hbij⟩ := even_higher_linear_prime_field_central_two_cover_trivial
      (QuotientGroup.mk' (center Q)) hη (by rw [hker]) h2 hn hmodel
    exact ⟨by rwa [hker] at hbot, hbij⟩

end CFSG.QuasithinUnique.Setup.X7b
