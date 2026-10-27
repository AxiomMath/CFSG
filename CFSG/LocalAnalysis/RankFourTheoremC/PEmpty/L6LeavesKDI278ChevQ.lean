module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

theorem kdChevQ_sylow_le {p : ℕ} (hp : p.Prime) {Z : Type} [Group Z] [Finite Z] {K : Subgroup Z}
    (hKn : K.Normal) (hC : Subgroup.centralizer (K : Set Z) = ⊥) {Q : Sylow p Z}
    (hout : ¬ p ∣ Nat.card (Outer K)) : (Q : Subgroup Z) ≤ K := by
  have : K.Normal := hKn
  intro r hr
  obtain ⟨k, hk⟩ := Q.isPGroup' ⟨r, hr⟩
  have hrk : r ^ p ^ k = 1 := congrArg Subtype.val hk
  let ψ : Z →* Outer K := (QuotientGroup.mk' (inner K)).comp (MulAut.conjNormal (H := K))
  have hcop : (p ^ k).Coprime (Nat.card (Outer K)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hout)
  have hψ : ψ r = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp
      ⟨by rw [← map_pow, hrk, map_one], pow_card_eq_one'⟩
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  have hcent : (c : Z)⁻¹ * r ∈ Subgroup.centralizer (K : Set Z) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hc ⟨x, hx⟩)
    rw [MulAut.conjNormal_apply] at h1
    change (c : Z) * x * (c : Z)⁻¹ = r * x * r⁻¹ at h1
    calc x * ((c : Z)⁻¹ * r) = (c : Z)⁻¹ * ((c : Z) * x * (c : Z)⁻¹) * r := by group
      _ = (c : Z)⁻¹ * (r * x * r⁻¹) * r := by rw [h1]
      _ = (c : Z)⁻¹ * r * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hcent ▸ c.2

theorem kdChevQ_false_of_tits {p : ℕ} {Z : Type} [Group Z] [Finite Z] {K Q : Subgroup Z}
    (hQ : IsPGroup p Q) (hQK : Q ≤ K) (hsyl : SylowIsPlane p ↥K) {a b : Z} (ha : a ∈ Q)
    (hb : b ∈ Q) (hab : a * b ≠ b * a) : False := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  have hcomm : IsMulCommutative (S : Subgroup K) := (hsyl S).1.1
  have ha' : (⟨a, hQK ha⟩ : K) ∈ (S : Subgroup K) := hS (Subgroup.mem_comap.mpr ha)
  have hb' : (⟨b, hQK hb⟩ : K) ∈ (S : Subgroup K) := hS (Subgroup.mem_comap.mpr hb)
  apply hab
  have key := hcomm.is_comm.comm (⟨⟨a, hQK ha⟩, ha'⟩ : (S : Subgroup K)) ⟨⟨b, hQK hb⟩, hb'⟩
  have := congrArg (fun x : (S : Subgroup K) => ((x : K) : Z)) key
  simpa using this

theorem kdChevQ_false_of_suzuki {p : ℕ} (hp : p.Prime) {Z : Type} [Group Z] [Finite Z]
    {K : Subgroup Z} (hcyc : SylowIsCyclicSq p ↥K) (hpr : Open.pRank p K = 2) : False := by
  obtain ⟨E, hEK, hE, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp K
  rw [hpr] at hEc
  have hEp := CFSG.Open.IsElemAbelian.isPGroup hE
  obtain ⟨S, hS⟩ := (hEp.comap_subtype (K := K)).exists_le_sylow
  have hcardE : Nat.card (E.comap K.subtype : Subgroup K) = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hEqS : E.comap K.subtype = (S : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hS ((hcyc S).2.trans hcardE.symm).le
  haveI := (hcyc S).1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(S : Subgroup K))
  have hgE : ∀ x : (S : Subgroup K), ((x : K) : Z) ^ p = 1 := by
    intro x
    have hx : (x : K) ∈ E.comap K.subtype := by
      rw [hEqS]
      exact x.2
    exact hE.2 _ (Subgroup.mem_comap.mp hx)
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hgE g
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, (hcyc S).2] at hdvd
  have hle := Nat.le_of_dvd hp.pos hdvd
  have h2 := hp.two_le
  nlinarith

theorem kdChevQ_le_of_seitz {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {Z : Type} [Group Z] [Finite Z] {K : Subgroup Z}
    (hKn : K.Normal) (hC : Subgroup.centralizer (K : Set Z) = ⊥) {U : Subgroup Z}
    (hU : CFSG.Open.IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) {Y : Subgroup Z}
    (hY : ∀ S : Subgroup Z, S ≤ U → 1 ≤ Open.pRank p S → Subgroup.normalizer (S : Set Z) ≤ Y)
    (d : TauCeti.ValidLieTypeIndex) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) :
    K ≤ Y := by
  have : K.Normal := hKn
  have hφ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (K : Set Z) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hC] at hxc
    exact Subgroup.mem_bot.mp hxc
  let ψ : Z →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hψ : Function.Injective ψ := fun x y hxy => hφ ((MulAut.congr e).injective hxy)
  have hfix : ∀ (a : Z) (k : K), ψ a (e k) = e k ↔ a * (k : Z) * a⁻¹ = k := by
    intro a k
    have h1 : ψ a (e k) = e (MulAut.conjNormal (H := K) a k) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1, e.apply_eq_iff_eq, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  have hclos := hS d p hp hp2 hpd hex (U.map ψ)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hU ψ)
    (by rw [Subgroup.card_map_of_injective hψ, hUc])
  have hgen : Subgroup.closure {k : K | ∃ a ∈ U, a ≠ 1 ∧ a * (k : Z) * a⁻¹ = k} = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e k ∈ Subgroup.closure
        {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ U.map ψ, ε ≠ 1 ∧ ε k = k} := by
      rw [hclos]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure
        {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ U.map ψ, ε ≠ 1 ∧ ε k = k} ≤
        (Subgroup.closure {k : K | ∃ a ∈ U, a ≠ 1 ∧ a * (k : Z) * a⁻¹ = k}).map
          e.toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro t ⟨_, ⟨a, haU, rfl⟩, hε1, hεt⟩
      refine ⟨e.symm t, Subgroup.subset_closure ⟨a, haU, ?_, ?_⟩, by simp⟩
      · rintro rfl
        exact hε1 (map_one ψ)
      · refine (hfix a (e.symm t)).mp ?_
        simpa using hεt
    obtain ⟨y, hy, hyk⟩ := hle hk
    exact (e.injective hyk) ▸ hy
  have hsub : {k : K | ∃ a ∈ U, a ≠ 1 ∧ a * (k : Z) * a⁻¹ = k} ⊆ (Y.subgroupOf K : Set K) := by
    rintro k ⟨a, haU, ha1, hak⟩
    have hcent : (k : Z) ∈ Subgroup.centralizer ({a} : Set Z) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mul_inv_eq_iff_eq_mul.mp hak
    have hne : Subgroup.zpowers a ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
    have hE : CFSG.Open.IsElemAbelian p (Subgroup.zpowers a) :=
      CFSG.AGLEmbeddingD2.isElemAbelian_of_le hU (Subgroup.zpowers_le.mpr haU)
    have h1 : 1 ≤ Open.pRank p (Subgroup.zpowers a) :=
      CFSG.AGLEmbeddingD2.one_le_pRank_of_isElemAbelian hp hE hne
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact hY (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haU) h1
      (CFSG.AGLEmbeddingD2.centralizer_singleton_le_normalizer_zpowers a hcent)
  have htop : (⊤ : Subgroup K) ≤ Y.subgroupOf K := by
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hsub
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (htop (Subgroup.mem_top (⟨x, hx⟩ : K)))

theorem kdI278ChevQ_holds
    : KDI278ChevQ := by
  intro p hp h5 Z _ _ K hKn _ _ hr hC hKrank _ Q hQnc U _ hU hUc Y hY
  obtain ⟨r, hrp, idx, ⟨e⟩, hchar⟩ := hr
  have hpd : p ≠ idx.1.characteristic := by
    rw [hchar]
    exact fun h => hrp h.symm
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p idx.1 := by
    intro hex
    unfold CFSG.AGLEmbeddingD2.IsD2SeitzException at hex
    rcases hex with ⟨h3, -⟩ | ⟨hp5, hd⟩
    · omega
    · subst hp5
      obtain ⟨d, hv⟩ := idx
      rcases hd with hd | hd
      ·
        have hd' : d = TauCeti.LieTypeIndex.tits := hd
        subst hd'
        have hT : IsTitsType 5 ↥K := by
          unfold IsTitsType
          exact ⟨rfl, hv, ⟨e⟩⟩
        have hno := tits_noOuter ↥K hT
        have hsyl := tits_sylow ↥K hT
        have hQK : (Q : Subgroup Z) ≤ K := kdChevQ_sylow_le hp hKn hC hno
        obtain ⟨a, ha, b, hb, -, -, hab⟩ := hQnc
        exact kdChevQ_false_of_tits Q.isPGroup' hQK hsyl ha hb hab
      ·
        have hd' : d = TauCeti.LieTypeIndex.suzuki 2 := hd
        subst hd'
        have hSz : IsSz32Type 5 ↥K := by
          unfold IsSz32Type
          exact ⟨rfl, hv, ⟨e⟩⟩
        exact kdChevQ_false_of_suzuki hp (sz32_sylow ↥K hSz) hKrank
  exact kdChevQ_le_of_seitz hp (by omega) CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    hKn hC hU hUc hY idx e hpd hex

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
