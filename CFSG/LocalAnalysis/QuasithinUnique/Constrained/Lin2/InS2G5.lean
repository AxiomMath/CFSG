module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2G4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeFive
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLem125
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2G3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {g : G} (hg : g ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers g) := CFSG.Open.isElemAbelian_zpowers hg

omit [Finite G] in
theorem isElemAbelian_sup_of_commute_p {p : ℕ} {E Z : Subgroup G} (hE : IsElemAbelian p E)
    (hZ : IsElemAbelian p Z) (h : ∀ a ∈ E, ∀ b ∈ Z, a * b = b * a) : IsElemAbelian p (E ⊔ Z) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hE hZ h

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem false_of_M₀_eq_T
    (hT : M₀ = T) (h39 : Vol2Native.A39ForSQTKCat)
    (hlist : Vol2Native.Lemma2_3_9_7_listedW) (hodd : ListedLin2OddRank) : False := by
  have hB := O.base
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h36 := Vol2Native.a36CoreForSQTKCat_proved
  have hlocal : LocalSQTK G := hB.cs.setting.qtke.1
  have hpX : pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ≠ ⊥ :=
    O.pCore_ne_bot_of O.X_le_normalizer_R₁ O.R₁_le_X
  obtain ⟨K₂, ⟨hK₂, hLK⟩, -⟩ := Vol2Native.lemma_1_2_5 hlocal h37 h39 hpX (O.S₁_sylow_X hT)
    hB.R1_le_S₁ (hB.relIndex_R1_S₁ O.hT₁ O.hT₂ O.hD O.hC O.hDx).le O.local_S₀ le_sup_left
  have hL₂c : conjR L t ∈ cComp (conjR L t ⊔ AppE.R1 S L) := mem_cComp_iff.2 O.local_S₀.2.1
  have hperf₂ : ⁅conjR L t, conjR L t⁆ = conjR L t := perfect_of_mem_cComp hL₂c
  have hne₂ : conjR L t ≠ ⊥ := ne_bot_of_mem_cComp hL₂c
  have hKY : K₂ ≤ Subgroup.centralizer (pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) : Set G) :=
    Vol2Native.le_centralizer_of_mem_cComp hK₂ hLK hne₂ hperf₂ (X_le_normalizer_Y' _)
      (O.L₂_le_centralizer_Y hT)
  have hKX : K₂ ≤ conjR L t ⊔ s2S₁ M₀ S L := le_of_mem_cComp hK₂
  have hOK : pCoreOf 2 K₂ ≤ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₂)
  have hZK : pCoreOf 2 K₂ ≤ centerOf K₂ := fun y hy =>
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K₂ hy,
      Subgroup.mem_centralizer_iff.2 fun k hk =>
        (Subgroup.mem_centralizer_iff.1 (hKY hk) y (hOK hy)).symm⟩
  have hcardU : Nat.card ↥(blockU (conjR L t)) = 2 ^ (2 * n) := by
    have := lin2_card_U hB.hlin₂
    rwa [hB.blockZ₂_eq_bot O.hC, Subgroup.card_bot, mul_one] at this
  have hm : 1 < CFSG.Open.pRank 2 K₂ := by
    have hUel : IsElemAbelian 2 (blockU (conjR L t)) :=
      C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hB.hL₂)
    have := CFSG.SectionRank.le_pRank (p := 2) one_lt_two ((blockU_le _).trans hLK) hUel hcardU
    have h2 := hB.hn
    omega
  have hq : CFSG.IsQuasisimple ↥K₂ :=
    Vol2Native.lemma_1_2_1_five_core hlocal h36 CFSG.Quasithin.l2MultiplierFact hpX hK₂ hZK hm
  have hKc : IsComponentIn K₂ (conjR L t ⊔ s2S₁ M₀ S L) := by
    refine ⟨hKX, ?_, ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm hq
    · have := A3.subnormal_comap (conjR L t ⊔ s2S₁ M₀ S L).subtype (subnormal_of_mem_cComp hK₂)
      rw [show (conjR L t ⊔ s2S₁ M₀ S L).comap (conjR L t ⊔ s2S₁ M₀ S L).subtype = ⊤ from
        Subgroup.subgroupOf_self _] at this
      exact A3.subnormal_top_iff.mp this
  have hX0 : IsGamma0 M (conjR L t ⊔ s2S₁ M₀ S L) := O.isGamma0_X hT
  have hSXM := O.S₁_sylow_X_inf_M hT
  obtain ⟨T', z, hT', hST', hz, hz1, hz2⟩ := hX0.exists_central_involution hB.cs.setting hSXM
  have hKlW := hlist G T M hB.cs.setting (conjR L t ⊔ s2S₁ M₀ S L) (s2S₁ M₀ S L) T' z hX0 hSXM hT'
    hST' hz hz1 hz2 K₂ hKc
  obtain ⟨p, hp, hpd, hrank⟩ := hodd G M (s2S₁ M₀ S L) K₂ (conjR L t) z n
    (by have := hB.hn; omega) hB.hL₂ hB.hlin₂ (hB.blockZ₂_eq_bot O.hC) hLK hq hKlW
  have hK₂K : K₂ ≤ conjR L t ⊔ conjR (conjR L t) x₀ := by
    refine perfect_le_of_le_sup (perfect_of_mem_cComp hK₂) ?_ O.S₁_le_normalizer_K hB.S₁_isPGroup
    exact hKX.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hodd2 : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hB.hn; omega⟩
    have hx : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [hm, pow_succ]
    exact ⟨2 ^ m - 1, by omega⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hodd2.not_two_dvd_nat hpd
  have : Fact p.Prime := ⟨hp⟩
  have hdiv : p ∣ Nat.card ↥D₁ := by rw [O.hT₁.card]; exact hpd
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥D₁) p hdiv
  have hdp : (d : G) ^ p = 1 := by
    have := pow_orderOf_eq_one d
    rw [hd] at this
    exact congrArg Subtype.val this
  obtain ⟨E₂, hE₂K, hE₂, hE₂c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₂
  have hZd : Subgroup.zpowers (d : G) ≤ D₁ := Subgroup.zpowers_le.2 d.2
  have hcomm : ∀ a ∈ E₂, ∀ b ∈ Subgroup.zpowers (d : G), a * b = b * a := by
    intro a ha b hb
    have hbD : b ∈ D₁ := hZd hb
    have hbK := O.D₁_le_centralizer_K hbD
    exact (Subgroup.mem_centralizer_iff.1 hbK a (hK₂K (hE₂K ha)))
  have hAel : IsElemAbelian p (E₂ ⊔ Subgroup.zpowers (d : G)) :=
    isElemAbelian_sup_of_commute_p hE₂ (isElemAbelian_zpowers hdp) hcomm
  have hinf : E₂ ⊓ Subgroup.zpowers (d : G) = ⊥ := by
    rw [eq_bot_iff, ← O.D₁_inf_K]
    exact fun x hx => ⟨hZd hx.2, hK₂K (hE₂K hx.1)⟩
  have hAcard : Nat.card ↥(E₂ ⊔ Subgroup.zpowers (d : G)) = p ^ (CFSG.Open.pRank p K₂ + 1) := by
    have hN : Subgroup.zpowers (d : G) ≤ Subgroup.normalizer (E₂ : Set G) :=
      le_normalizer_of_commute fun a ha b hb => hcomm a ha b hb
    have h := card_sup_mul_card_inf hN
    rw [inf_comm, hinf, Subgroup.card_bot, mul_one, sup_comm, Nat.card_zpowers, Subgroup.orderOf_coe, hd, hE₂c] at h
    rw [h, pow_succ, mul_comm]
  have hD₁N : D₁ ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      (fun d hd => hB.D_le_normalizer_R (O.hD ▸ Subgroup.mem_sup_left hd)) ?_
    exact (O.hT₁.le_borel.trans inf_le_left).trans Subgroup.le_normalizer
  have hAN : E₂ ⊔ Subgroup.zpowers (d : G) ≤
      Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
    sup_le ((hE₂K.trans hKX).trans O.X_le_normalizer_R₁) (hZd.trans hD₁N)
  have hSQ : CFSG.SectionRank.IsSQTKCat ↥(Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) :=
    hB.cs.setting.qtke.1 _ (O.pCore_ne_bot_of le_rfl Subgroup.le_normalizer)
  have h1 := CFSG.SectionRank.le_pRank hp.one_lt hAN hAel hAcard
  have h2 := L238.rank_le_of_isSQTKCat hSQ hp hp2
  rw [pRank_top_subtype (p := p)] at h2
  omega

end S2Ok

end CFSG.QuasithinUnique.Lin2
