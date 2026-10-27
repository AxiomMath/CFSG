module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticLines
public import CFSG.Yardstones.Md8ed6d263d89.Definitions
import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcEndgame
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.PreuniquenessRankFour.Helpers Subgroup

theorem card_le_cube_of_autRankTwo {p : ℕ} (hp : p.Prime) {i : TauCeti.CFSGIndex}
    (hA : AutRankTwoAt p i) {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (e : Nonempty (K ≃* i.Group)) (hC : IsCyclic (centralizer (K : Set X))) {B : Subgroup X}
    (hB : IsElemAbelian p B) : Nat.card B ≤ p ^ 3 :=
  calc Nat.card B ≤ p * Nat.card (B.map (MulAut.conjNormal : X →* MulAut K)) :=
        card_le_mul_card_map_conjNormal hp hC hB
    _ ≤ p * p ^ 2 := Nat.mul_le_mul_left _ (hA K e _ (CFSG.Open.IsElemAbelian.map hB _))
    _ = p ^ 3 := by ring

section Point

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem false_of_autRankTwo [Fact p.Prime] (hp2 : p ≠ 2) (hS : D1Global G) (hD1 : D1For G)
    (hloc : D1Local p P M) (h : IsPPoint p P M x) {R : Sylow p (RedCent p x)}
    {K : Subgroup (RedCent p x)} {i : TauCeti.CFSGIndex} (hfacts : PPointFacts p M x R K i)
    (hReq : (R : Subgroup (RedCent p x)) = redQ p P x) (hrk : AutRankTwoAt p i)
    (hsig : SignalizerAutAt p i) : False := by
  have hp : p.Prime := Fact.out
  haveI := hfacts.red.normal
  have h32 : Lemma32At p P x := lemma32At_of_facts hp2 hloc h hsig hfacts hReq
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  have hOc : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hQ3 : ∀ B : Subgroup G, B ≤ (P : Subgroup G) ⊓ C → IsElemAbelian p B →
      Nat.card B ≤ p ^ 3 := by
    intro B hB hBel
    have hBC : B ≤ C := hB.trans inf_le_right
    set T : Subgroup C := B.subgroupOf C with hT
    have hrk3 : Open.pRank p (T.map (QuotientGroup.mk' O)) ≤ 3 := by
      apply csSup_le'
      rintro k ⟨E, hEle, hE, hk⟩
      have hle := card_le_cube_of_autRankTwo hp hrk hfacts.equiv hfacts.isCyclic hE
      rw [hk] at hle
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    rw [pRank_map_mk_eq_pRank_map_subtype hp O hOc T, hT, map_subgroupOf_eq_of_le hBC] at hrk3
    have hBp : IsPGroup p B := fun g => ⟨1, by simpa using Subtype.ext (hBel.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    have hkle : k ≤ Open.pRank p B := le_csSup (pRank_bddAbove p hp B) ⟨B, le_rfl, hBel, hk⟩
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (hkle.trans hrk3)
  have hA4 : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 4 := by
    have h4 : 4 ≤ Open.pRank p (P : Subgroup G) := by
      rw [pRank_sylow_eq_globalRank p hp P]
      exact betaFour_globalRank hloc.beta
    obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained p hp (P : Subgroup G)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p
      (n := 4) (by rw [hEc]; exact pow_dvd_pow p h4)
    refine ⟨K.map E.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨a, -, rfl⟩
      exact hEP a.2
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
      · obtain ⟨a', -, ha⟩ := a.2
        obtain ⟨b', -, hb⟩ := b.2
        apply Subtype.ext
        show (a : G) * (b : G) = (b : G) * (a : G)
        rw [← ha, ← hb]
        exact congrArg Subtype.val (hE.1.is_comm.comm a' b')
      · obtain ⟨a', -, rfl⟩ := hz
        exact congrArg Subtype.val (Subtype.ext (hE.2 a' a'.2) : a' ^ p = 1)
    · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  obtain ⟨y0, hy0Q, hy0c, hy0p, hy0x⟩ := h32.central
  exact PPointP.pGroupEndgame G p P P.isPGroup' x y0 h.elem.2.1 h.mem hy0Q hy0c hy0p hy0x hA4 hQ3
    fun D hDQ hD hDc =>
      h.not_exists_conj_lines_of_lemma32At hp2 hS hD1 hloc h32 hDQ hD hDc

theorem false_of_exotic (hp5 : 5 ≤ p) (hS : D1Global G) (hD1 : D1For G) (hloc : D1Local p P M)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} {i : TauCeti.CFSGIndex}
    (hdata : CFSG.Yardstones.Md8ed6d263d89.PPointData p P M x R K i) (hex : ExoticFive p i)
    (hrk : ExoticFive p i → AutRankTwoAt p i) (hsig : ExoticFive p i → SignalizerAutAt p i) :
    False := by
  haveI : Fact p.Prime := ⟨hloc.beta.1⟩
  obtain ⟨h, hfacts, hReq⟩ := hdata
  exact false_of_autRankTwo (by omega) hS hD1 hloc h hfacts hReq (hrk hex) (hsig hex)

end Point

theorem ysPPointTypeLinTwoOrUnitary_of_kfacts
    (hrk : ∀ (p : ℕ) (i : TauCeti.CFSGIndex), 5 ≤ p → ExoticFive p i → AutRankTwoAt p i)
    (hsig : ∀ (p : ℕ) (i : TauCeti.CFSGIndex), 5 ≤ p → ExoticFive p i → SignalizerAutAt p i) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointTypeLinTwoOrUnitary := by
  intro G _ _ _ hnonab hK hchar he hpre hD1 _ p P M x R K i hp5 hloc hdata
  have hS : D1Global G := ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
  rcases PPointType.cases_five hp5 hdata.2.1.type with ⟨d, n, hn, rfl, hd⟩ | ⟨d, rfl, hd, hn⟩ | hex
  · exact Or.inl ⟨d, n, hn, rfl, hd⟩
  · exact Or.inr ⟨d, rfl, hd, hn⟩
  · exact (false_of_exotic hp5 hS hD1 hloc hdata hex (hrk p i hp5) (hsig p i hp5)).elim

end CFSG.LocalAnalysis.RankFourTheoremC
