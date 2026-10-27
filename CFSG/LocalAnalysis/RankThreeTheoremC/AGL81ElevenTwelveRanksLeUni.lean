module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksLeTorus
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCovers
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksLeLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def KFactTwelveRanksLeU : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ r, 3 ≤ r ∧ IsLieOver (Y ⧸ Subgroup.center Y) (.twistedA r) 2 1) →
      ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ⊓ Subgroup.center Y = ⊥

namespace TwelveRanksLe

theorem card_map_of_forall_eq_one {G H : Type*} [Group G] [Group H] {E : Subgroup G}
    (ψ : G →* H) (hψ : ∀ g ∈ E, ψ g = 1 → g = 1) : Nat.card (E.map ψ) = Nat.card E := by
  have hinj : Function.Injective (ψ.subgroupMap E) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    exact Subgroup.mem_bot.2 (Subtype.ext (hψ g g.2 (congrArg Subtype.val hg)))
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, ψ.subgroupMap_surjective E⟩)).symm

theorem exists_noncomm_of_isSimpleGroup_of_dvd {U : Type*} [Group U] [Finite U]
    [hs : IsSimpleGroup U] (h9 : 9 ∣ Nat.card U) : ∃ a b : U, a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : U, a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  haveI : IsMulCommutative U := ⟨⟨hcomm⟩⟩
  have hp : (Nat.card U).Prime := Group.is_simple_iff_prime_card.mp hs
  rcases (Nat.dvd_prime hp).1 h9 with h | h
  · omega
  · rw [← h] at hp
    exact absurd hp (by norm_num)


theorem exists_isElemAbelian_card_nine_of_statedSU_quotient {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hn : 4 ≤ n) (h3 : 3 ∣ 2 ^ f + 1)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU n (2 ^ f) K)) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ⊓ Subgroup.center Y = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  obtain ⟨E₀, hE₀, hE₀card, hE₀s⟩ := exists_isElemAbelian_card_nine_statedSU hK h3 hn
  have hsimple : IsSimpleGroup (StatedProj (StatedSU n (2 ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 f hK n hn3 hnq
  let π : StatedSU n (2 ^ f) K →* StatedProj (StatedSU n (2 ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))
  have hπE : ∀ g ∈ E₀, π g = 1 → g = 1 := fun g hg h =>
    hE₀s g hg (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff g).1 h))
  have h9 : 9 ∣ Nat.card (StatedProj (StatedSU n (2 ^ f) K)) := by
    have := Subgroup.card_subgroup_dvd_card (E₀.map π)
    rwa [card_map_of_forall_eq_one π hπE, hE₀card] at this
  obtain ⟨hUq, hUc⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (exists_noncomm_of_isSimpleGroup_of_dvd h9)
  have hQ : CFSG.IsQuasisimple (Y ⧸ Subgroup.center Y) :=
    CFSG.IsQuasisimple.of_mulEquiv e hUq
  have hY' : CFSG.IsQuasisimple (commutator Y) :=
    CFSG.LocalCores.quasisimple_central_extension_derived (Subgroup.center Y) le_rfl hQ
  obtain ⟨-, hperf', hsurj'⟩ :=
    CFSG.LocalCores.central_extension_derived (Subgroup.center Y) le_rfl hQ.1
  let φ : commutator Y →* StatedProj (StatedSU n (2 ^ f) K) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Y)).comp (commutator Y).subtype)
  have hφs : Function.Surjective φ := e.surjective.comp hsurj'
  have hφk : φ.ker ≤ Subgroup.center (commutator Y) := by
    intro x hx
    have h1 : e (QuotientGroup.mk' (Subgroup.center Y) (x : Y)) = 1 := hx
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 h1 g)
  have hcK : Subgroup.center (commutator Y) = φ.ker := by
    have h1 := CFSG.LocalCores.comap_center_eq_of_perfect hperf' φ hφs hφk
    rw [hUc, MonoidHom.comap_bot] at h1
    exact h1.symm
  let e₁ : commutator Y ⧸ Subgroup.center (commutator Y) ≃*
      StatedProj (StatedSU n (2 ^ f) K) :=
    (QuotientGroup.quotientMulEquivOfEq hcK).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  set Y' : Subgroup Y := commutator Y
  set A : Subgroup Y' := CFSG.LocalAnalysis.ComponentInitial.LinearCover.twoPart
    (Subgroup.center Y') le_rfl with hAdef
  have hAc : A ≤ Subgroup.center Y' :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.twoPart_le_center
  haveI hAn : A.Normal := Subgroup.normal_of_le_center hAc
  have hA2 : IsPGroup 2 A :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.isPGroup_twoPart
  obtain ⟨hqq, -, -⟩ := CFSG.LocalCores.quasisimple_central_quotient hY' A hAc
  have hodd : Odd (Nat.card (Subgroup.center (Y' ⧸ A))) :=
    CFSG.QuasithinUnique.Setup.X7b.odd_card_center_quotient_twoPart hAdef hY'
  let eQ : (Y' ⧸ A) ⧸ Subgroup.center (Y' ⧸ A) ≃* StatedProj (StatedSU n (2 ^ f) K) :=
    (CFSG.QuasithinUnique.Setup.X7b.centralQuotientEquiv hY' hAc).symm.trans e₁
  let eT : ↥(⊤ : Subgroup (Y' ⧸ A)) ≃* (Y' ⧸ A) := Subgroup.topEquiv
  have hQT : CFSG.IsQuasisimple ↥(⊤ : Subgroup (Y' ⧸ A)) :=
    CFSG.IsQuasisimple.of_mulEquiv eT hqq
  have hL : IsComponentOf (⊤ : Subgroup (Y' ⧸ A)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _, hQT.1.commutator_eq_top, hQT.2.1⟩
  have hcT : (Subgroup.center ↥(⊤ : Subgroup (Y' ⧸ A))).map eT.toMonoidHom =
      Subgroup.center (Y' ⧸ A) := Subgroup.map_center_eq eT
  have hcardT : Nat.card (Subgroup.center ↥(⊤ : Subgroup (Y' ⧸ A))) =
      Nat.card (Subgroup.center (Y' ⧸ A)) := by
    rw [← hcT]
    exact (Subgroup.card_map_of_injective eT.injective).symm
  let eQT : ↥(⊤ : Subgroup (Y' ⧸ A)) ⧸ Subgroup.center ↥(⊤ : Subgroup (Y' ⧸ A)) ≃*
      StatedProj (StatedSU n (2 ^ f) K) :=
    (QuotientGroup.congr _ _ eT hcT).trans eQ
  obtain ⟨ρ, -, -, hρ⟩ := CFSG.AGLEmbedding.kFactCoverUnitary (Y' ⧸ A) ⊤ hL (hcardT ▸ hodd) n
    (2 ^ f) K hK hn3 hnq eQT
  let ψ : StatedSU n (2 ^ f) K →* (Y' ⧸ A) := eT.toMonoidHom.comp ρ
  have hψE : ∀ g ∈ E₀, ψ g = 1 → g = 1 := fun g hg h => by
    have h1 : ρ g = 1 := by
      have h0 : eT (ρ g) = 1 := h
      exact eT.injective (h0.trans (map_one eT).symm)
    have h2 := hρ g
    rw [h1, QuotientGroup.mk_one, map_one] at h2
    exact hE₀s g hg (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff g).1 h2.symm))
  have hF : IsElemAbelian 3 (E₀.map ψ) := hE₀.map ψ
  have hFcard : Nat.card (E₀.map ψ) = 3 ^ 2 := by
    rw [card_map_of_forall_eq_one ψ hψE, hE₀card]
  have hFZ : E₀.map ψ ⊓ Subgroup.center (Y' ⧸ A) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨g, hg, rfl⟩, hz⟩
    have h1 : ρ g ∈ Subgroup.center ↥(⊤ : Subgroup (Y' ⧸ A)) := by
      have h0 : eT (ρ g) ∈ Subgroup.center (Y' ⧸ A) := hz
      rw [← hcT] at h0
      obtain ⟨w, hw, hwe⟩ := h0
      have hwρ : w = ρ g := eT.injective hwe
      exact hwρ ▸ hw
    have h2 : (QuotientGroup.mk (ρ g) : ↥(⊤ : Subgroup (Y' ⧸ A)) ⧸
        Subgroup.center ↥(⊤ : Subgroup (Y' ⧸ A))) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    have h3 := hρ g
    rw [h2, map_one] at h3
    have h4 := hE₀s g hg (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff g).1 h3.symm))
    rw [h4, map_one]
    exact Subgroup.one_mem _
  obtain ⟨E₁, hE₁, hE₁card, hE₁Z⟩ :=
    exists_isElemAbelian_card_nine_of_quotient_twoGroup A hA2 hF hFcard hFZ
  refine ⟨E₁.map Y'.subtype, hE₁.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Y'.subtype_injective, hE₁card]
  · rw [eq_bot_iff]
    rintro z ⟨⟨w, hw, rfl⟩, hz⟩
    have hwc : w ∈ Subgroup.center Y' :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hz g)
    have h1 : w ∈ E₁ ⊓ Subgroup.center Y' := ⟨hw, hwc⟩
    rw [hE₁Z, Subgroup.mem_bot] at h1
    rw [h1, map_one]
    exact Subgroup.one_mem _

end TwelveRanksLe

theorem kFactTwelveRanksLeU_holds :
    KFactTwelveRanksLeU := by
  intro Y _ _ ⟨r, hr, hLie⟩
  obtain ⟨⟨d, hv⟩, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := hLie
  simp only at hd
  subst hd
  have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hqp] at hc
  obtain ⟨⟨-, -, hn3, hnq⟩, K, hKf, hKfin, hcard, ⟨e'⟩⟩ := hc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * q.exponent)
    (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  exact TwelveRanksLe.exists_isElemAbelian_card_nine_of_statedSU_quotient hcard (by omega)
    (by rw [hqe]; norm_num) e'

end CFSG.LocalAnalysis.RankThreeTheoremC
