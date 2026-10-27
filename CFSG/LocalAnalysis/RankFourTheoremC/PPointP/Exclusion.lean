module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointProp31
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma33
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.BorelInvolution
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.PreuniquenessRankFour.Helpers CFSG.LocalAnalysis.RankFourTheoremC Subgroup

@[expose] def PGroupEndgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Subgroup G), IsPGroup p P →
    ∀ x y0 : G, orderOf x = p → x ∈ P → y0 ∈ P ⊓ centralizer ({x} : Set G) →
    (∀ q ∈ P ⊓ centralizer ({x} : Set G), q * y0 = y0 * q) → orderOf y0 = p →
    y0 ∉ zpowers x → (∃ A : Subgroup G, A ≤ P ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 4) →
    (∀ B : Subgroup G, B ≤ P ⊓ centralizer ({x} : Set G) → IsElemAbelian p B →
      Nat.card B ≤ p ^ 3) →
    (∀ D : Subgroup G, D ≤ P ⊓ centralizer ({x} : Set G) → IsElemAbelian p D →
      Nat.card D = p ^ 2 → ¬ ∃ S : Finset (Subgroup G), S.card = p ∧ ∀ L ∈ S,
        L ≤ D ∧ Nat.card L = p ∧ ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom) →
    False

section Groups

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G}
  {x : G}

theorem false_of_altSpor (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) (hKR : KFactExcludedRank)
    (hKI : KFactExcludedInner) (hEnd : PGroupEndgame) (hS : D1Global G) (hD1 : D1For G)
    (hFC : FullCoreLocality G) (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)}
    {K : Subgroup (RedCent p x)} (hRK : PPointReduced p M x R K) {i : TauCeti.CFSGIndex}
    (hi : ExcludedAltSpor p i) (e : Nonempty (K ≃* i.Group)) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  have hZ := hRK.center_eq_bot hp2 h243 (h.catalogSimpleSections hS hp)
  have hC := hRK.isCyclic_centralizer hzc hzp
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  have hOc : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hQ3 : ∀ B : Subgroup G, B ≤ (P : Subgroup G) ⊓ C → IsElemAbelian p B →
      Nat.card B ≤ p ^ 3 := by
    intro B hB hBel
    have hBC : B ≤ C := hB.trans inf_le_right
    set T : Subgroup C := B.subgroupOf C with hT
    have hrk : Open.pRank p (T.map (QuotientGroup.mk' O)) ≤ 3 := by
      apply csSup_le'
      rintro k ⟨E, hEle, hE, hk⟩
      have hle := card_le_cube_of_isElemAbelian hi hKR hKI hRK.normal e hZ hC hE
      rw [hk] at hle
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    rw [pRank_map_mk_eq_pRank_map_subtype hp O hOc T, hT, map_subgroupOf_eq_of_le hBC] at hrk
    have hBp : IsPGroup p B := fun g => ⟨1, by simpa using Subtype.ext (hBel.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    have hkle : k ≤ Open.pRank p B := le_csSup (pRank_bddAbove p hp B) ⟨B, le_rfl, hBel, hk⟩
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (hkle.trans hrk)
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
  obtain ⟨y0, hy0Q, hy0c, hy0p, hy0x⟩ :=
    h.exists_central_of_not_mem_zpowers hp2 h243 hS hFC hloc
  exact hEnd G p P P.isPGroup' x y0 h.elem.2.1 h.mem hy0Q hy0c hy0p hy0x hA4 hQ3
    fun D hDQ hD hDc => h.not_exists_conj_lines hp2 h243 h244 hsig hS hD1 hFC hloc hDQ hD hDc

end Groups

theorem pPointExclusionFive_of_kFacts (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) (hKR : KFactExcludedRank)
    (hKI : KFactExcludedInner) (hEnd : PGroupEndgame) : PPointExclusionFive := by
  intro G _ _ hS hD1 hFC p _ P M hloc hp5 x h R K hRK i e hex
  have hp2 : p ≠ 2 := by omega
  rcases altSpor_or_of_excluded hex with hAS | ⟨d, rfl, hd, hn⟩ | ⟨d, rfl, hd⟩
  · exact false_of_altSpor hp2 h243 h244 hsig hKR hKI hEnd hS hD1 hFC hloc h hRK hAS e
  · exact false_of_unitary_p hp2 h243 hS hD1 hloc h hRK hd hn e
  · exact absurd hd.1 (by omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
