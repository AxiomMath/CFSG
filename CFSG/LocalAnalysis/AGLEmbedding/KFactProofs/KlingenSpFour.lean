module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourModel
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.AGLEmbedding.KlingenSpFour

open CFSG.Assembly.LowTwoRank CFSG.RankThreeCoreUniqueness.Helpers

variable {p : ℕ} [Fact p.Prime]

theorem card_center_dvd_griess {S Q : Type} [Group S] [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq hker.le)

theorem statedClassicalModel_of_spFourIndex {G : Type} [Group G] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsSpFourIndex p d) (e : G ≃* (TauCeti.CFSGIndex.lie d).Group) :
    StatedClassicalModel G .PSp 2 p 1 := by
  obtain ⟨q, hq⟩ := hd
  obtain ⟨d1, hv⟩ := d
  rcases hq with ⟨hqp, hqe, hd1⟩ | ⟨hp3, hqp, hqe, hd1⟩
  · simp only at hd1
    subst hd1
    have h1 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    rw [hqp, hqe] at h1
    exact h1
  · simp only at hd1
    subst hd1
    have h1 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hqp, hqe] at h1
    subst hp3
    exact CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two h1

theorem nonempty_mulEquiv_psp4 (hp2 : p ≠ 2) {G : Type} [Group G]
    (h : StatedClassicalModel G .PSp 2 p 1) : Nonempty (G ≃* PSp4 p) :=
  CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h
    ⟨⟨Fact.out, le_rfl, le_rfl, fun h => hp2 (by simpa using (Prod.mk.inj h).2)⟩, ZMod p,
      inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩

theorem card_griessHopf_psp4_dvd (hp2 : p ≠ 2) :
    Nat.card (CFSG.Open.griessHopfMultiplier (PSp4 p)) ∣ 2 := by
  have hp : p.Prime := Fact.out
  by_cases hp3 : p = 3
  · subst hp3
    have hmodel : CFSG.Models.LieModel (PSp4 3) .PSp 2 3 1 :=
      ⟨⟨Fact.out, le_rfl, le_rfl, by decide⟩, Or.inl
        ⟨⟨Fact.out, le_rfl, le_rfl, by decide⟩, ZMod 3, inferInstance, inferInstance, by simp,
          ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_four_three_row
      (X := PSp4 3) hmodel
    rw [Nat.card_congr eM.toEquiv]
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp 2 3 1 = (2, 1) := rfl
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 3 1 = (1, 1) := by decide
    have hc : ∀ n : ℕ, Nat.card (Multiplicative (ZMod n)) = n := fun n => by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    rw [hg, he]
    simp only [Nat.card_prod, hc]
    norm_num
  · have h5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h3 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
      omega
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier
      (K := ZMod p) (n := 2) le_rfl (by simpa using h5)
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact Nat.gcd_dvd_left _ _

theorem kFactKlingenSpFour :
    KFactKlingenSpFour := by
  intro p _ Y _ _ Rb Y₀ hred hcat K hK huniq hnc hcent d hd ⟨e⟩
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hred.ne_two
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSp 2 p 1 :=
    statedClassicalModel_of_spFourIndex d hd e
  obtain ⟨eK⟩ := nonempty_mulEquiv_psp4 hp2 hmodel
  have hperf : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hZp : IsPGroup p (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp hred.core_eq_bot hK
  have hdvd := (card_center_dvd_griess hperf eK).trans (card_griessHopf_psp4_dvd (p := p) hp2)
  have hZ : Subgroup.center K = ⊥ := by
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    rw [hn] at hdvd
    have hn0 : n = 0 := by
      by_contra hn0
      have h1 : p ∣ 2 := (dvd_pow_self p hn0).trans hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
  let ψ : K ≃* PSp4 p := (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center K))
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ],
      QuotientGroup.mk'_surjective _⟩).trans eK
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨Tstd, hKA, hrank⟩ := exists_klingenAlt p hp2
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSp4 p) (T₀.mapSurjective hψs) Tstd
  let Ψ : K ≃* PSp4 p := ψ.trans (MulAut.conj g)
  have hΨ : (T₀ : Subgroup K).map Ψ.toMonoidHom = Tstd := by
    have h1 := congrArg (fun P : Sylow p (PSp4 p) => (P : Subgroup (PSp4 p))) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    rw [← h1, Sylow.coe_mapSurjective, Subgroup.pointwise_smul_def]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ψ y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hKAK : KlingenAlt p K T₀ := klingenAlt_of_mulEquiv Ψ.symm (T := Tstd) (T' := T₀) (by
    rw [← hΨ, Subgroup.map_map]
    ext x
    simp) hKA
  have hrk : 3 ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ K) := by
    rw [← hT₀, PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
      K.subtype_injective, ← PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp
      Ψ.toMonoidHom Ψ.injective, hΨ]
    exact hrank
  have hnot : ¬ K ≤ Y₀ := not_le_of_weakCore_le hp Rb hred.weakCore_le hred.ne_top hrk
  exact klingenTransport Y p Rb Y₀ K T₀ hT₀ (weakCore_le_comap hred T₀ hT₀) hnot hKAK

end CFSG.AGLEmbedding.KlingenSpFour
