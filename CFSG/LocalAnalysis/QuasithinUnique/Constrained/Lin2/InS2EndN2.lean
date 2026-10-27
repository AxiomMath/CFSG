module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2EndN1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2EndNGrp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

namespace EndN

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x : G} {q : ℕ} {W D₁ D₂ : Subgroup G}

omit [Finite G] in
theorem isSubnormal_subgroupOf' {L X : Subgroup G} (h : IsSubnormal L X) :
    (L.subgroupOf X).IsSubnormal := by
  have h1 := A3.subnormal_comap X.subtype h
  have e2 : X.comap X.subtype = ⊤ := by ext x; simp
  rw [e2] at h1
  exact A3.subnormal_top_iff.1 h1

namespace Data

variable (E : Data T M H S L D n t M₀ x q W D₁ D₂)
include E

theorem conj_mem_normalizer_L₀ {y : G} (hy : y ∈ Subgroup.normalizer (thompsonJ S : Set G)) {d : G}
    (hd : d ∈ D) : y * d * y⁻¹ ∈ Subgroup.normalizer (conjJoin S L : Set G) := by
  have hA : IsMaxElemAbelian (thompsonJ S) (conjR (pCoreOf 2 H) y) :=
    C56.isMaxElemAbelian_conjSubgroup E.Q_isMax hy
  have h1 := E.D_fix hA hd
  rw [conjR_conjR] at h1
  have h2 : conjR (pCoreOf 2 H) (y * d * y⁻¹) = pCoreOf 2 H := by
    rw [conjR_mul, h1, conjR_conjR_inv]
  exact E.h246 G T M H S L E.cs E.B.cfg.double ⟨n, E.B.cfg.one_lt, E.B.hlin⟩
    (conjR_eq_self_iff.1 h2)

theorem isBlock₀ : IsBlock2 (Subgroup.normalizer (conjJoin S L : Set G)) L := by
  refine ⟨E.B.hL, E.B.L_le_L₀.trans Subgroup.le_normalizer, ?_⟩
  have hLL₀ : L ≤ conjJoin S L := E.B.L_le_L₀
  have hn1 : (L.subgroupOf (conjJoin S L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLL₀).2 E.B.L₀_le_normalizer_L
  have hn2 : ((conjJoin S L).subgroupOf
      (Subgroup.normalizer (conjJoin S L : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  exact isSubnormal_subgroupOf' (A3.subnormal_trans (A3.subnormal_of_normal hLL₀ hn1)
    (A3.subnormal_of_normal Subgroup.le_normalizer hn2))

theorem mem_cComp₀ : L ∈ cComp (Subgroup.normalizer (conjJoin S L : Set G)) :=
  L238.mem_cComp_of_isBlock2 E.isBlock₀ (L238.card_ne_three_of_isLin2Type E.B.cfg.one_lt E.B.hlin)

theorem pCore_normalizer_ne_bot :
    pCoreOf 2 (Subgroup.normalizer (conjJoin S L : Set G)) ≠ ⊥ := by
  intro hbot
  have hU2 : IsPGroup 2 (blockU L) := by
    rw [← E.B.pCore_L]
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  have h1 : blockU L ≤ pCoreOf 2 (conjJoin S L) := by
    refine le_pCoreOf_of_normalizes ((blockU_le L).trans E.B.L_le_L₀) ?_ hU2
    intro g hg
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (E.B.L₀_le_normalizer_L hg)
    rwa [E.B.pCore_L] at this
  have h2 : pCoreOf 2 (conjJoin S L) ≤ pCoreOf 2 (Subgroup.normalizer (conjJoin S L : Set G)) := by
    refine le_pCoreOf_of_normalizes
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (conjJoin S L)).trans
        Subgroup.le_normalizer) ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (conjJoin S L))
    intro g hg
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjJoin S L) hg
  have h3 : blockU L ≤ ⊥ := hbot ▸ h1.trans h2
  have h4 := one_lt_card_blockU E.B.hlin E.B.hn
  rw [le_bot_iff.1 h3, Subgroup.card_bot] at h4
  omega

theorem ncard_conj₀
    :
    Set.ncard (conjSubgroupsBy (Subgroup.normalizer (conjJoin S L : Set G)) L) = 2 := by
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h38 := Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact
    Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved
  have hnorm : ¬ (L.subgroupOf (Subgroup.normalizer (conjJoin S L : Set G))).Normal := by
    intro hn
    have hN : Subgroup.normalizer (conjJoin S L : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer E.isBlock₀.2.1).1 hn
    have htH : t ∈ Subgroup.normalizer (conjJoin S L : Set G) :=
      S_le_normalizer_conjJoin' S L E.B.ht
    exact E.B.hne (conjR_eq_of_mem_normalizer (hN htH))
  rcases Vol2Native.lemma_1_2_1_three E.cs.setting.qtke.1 h37 h38 E.pCore_normalizer_ne_bot
      E.mem_cComp₀ with hn | ⟨hc, -⟩
  · exact absurd hn hnorm
  · exact hc

theorem card_D : Nat.card D = Nat.card D₁ * Nat.card D₂ := by
  have hD₁L : D₁ ≤ L := E.hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := E.hT₂.le_borel.trans inf_le_left
  have hN : D₁ ≤ Subgroup.normalizer (D₂ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => (E.B.comm_elem b (hD₁L hb) a (hD₂L ha)).symm
  have h1 := card_sup_mul_card_inf hN
  have hbot : D₁ ⊓ D₂ = ⊥ := by
    rw [eq_bot_iff, ← E.B.L_inf_L₂]
    exact inf_le_inf hD₁L hD₂L
  rw [hbot, Subgroup.card_bot, mul_one, ← E.hD] at h1
  exact h1

theorem prime_dvd_of_dvd_card_D {p : ℕ} (hp : p.Prime) (hpD : p ∣ Nat.card D) :
    p ≠ 2 ∧ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hD₁L : D₁ ≤ L := E.hT₁.le_borel.trans inf_le_left
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact E.B.cfg.hall.2.1.not_two_dvd_nat hpD
  refine ⟨hp2, ?_⟩
  have hcard : Nat.card D₂ = Nat.card D₁ := by rw [E.hT₁.card, E.hT₂.card]
  have hpD₁ : p ∣ Nat.card D₁ := by
    rw [E.card_D, hcard] at hpD
    rcases hp.dvd_mul.1 hpD with h | h <;> exact h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpD₁
  exact prime_dvd_card_modPCore (hD₁L g.2) hp hp2 (by rw [Subgroup.orderOf_coe]; exact hg)

theorem le_conjJoin_of_le_normalizer
    {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (conjJoin S L : Set G)) (hXD : Nat.card X = Nat.card D) :
    X ≤ conjJoin S L := by
  have hLL₀ : L ≤ conjJoin S L := E.B.L_le_L₀
  have hconj : CFSG.Quasithin.conjClosure L (Subgroup.normalizer (conjJoin S L : Set G)) ≤
      conjJoin S L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨h, hh, z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hh z).1 (hLL₀ hz)
  have hgen : ∀ y ∈ X, ∀ p k : ℕ, p.Prime → orderOf y = p ^ k → y ∈ conjJoin S L := by
    intro y hy p k hp hk
    by_cases hk0 : k = 0
    · rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      rw [hk]
      exact (conjJoin S L).one_mem
    have hpD : p ∣ Nat.card D := by
      have h1 : orderOf y ∣ Nat.card X := by
        have := orderOf_dvd_natCard (⟨y, hy⟩ : X)
        rwa [Subgroup.orderOf_mk] at this
      rw [hk, hXD] at h1
      exact (dvd_pow_self p hk0).trans h1
    obtain ⟨hp2, hpL⟩ := E.prime_dvd_of_dvd_card_D hp hpD
    have hcl := Vol2Native.lemma122A_proved G E.cs.setting.simple E.cs.setting.nonabelian
      E.cs.setting.qtke (Subgroup.normalizer (conjJoin S L : Set G)) L E.pCore_normalizer_ne_bot
      E.mem_cComp₀ p hp hp2 E.ncard_conj₀ hpL
    have hmem : y ∈ Subgroup.closure
        {z : G | z ∈ Subgroup.normalizer (conjJoin S L : Set G) ∧ ∃ k : ℕ, orderOf z = p ^ k} :=
      Subgroup.subset_closure ⟨hX hy, k, hk⟩
    rw [hcl] at hmem
    exact hconj hmem
  intro g hg
  refine (Subgroup.closure_le _).2 ?_ (mem_closure_primePow X g hg)
  rintro y ⟨hy, p, k, hp, hk⟩
  exact hgen y hy p k hp hk

theorem conj_mem_L₀
    {y : G} (hy : y ∈ Subgroup.normalizer (thompsonJ S : Set G)) {d : G}
    (hd : d ∈ D) : y * d * y⁻¹ ∈ conjJoin S L := by
  have hX : conjR D y⁻¹ ≤ Subgroup.normalizer (conjJoin S L : Set G) := by
    intro z hz
    obtain ⟨d', hd', rfl⟩ := mem_conjR_iff'.1 hz
    simpa using E.conj_mem_normalizer_L₀ hy hd'
  exact E.le_conjJoin_of_le_normalizer hX (card_conjR D y⁻¹)
    (mem_conjR_iff'.2 ⟨d, hd, by simp⟩)

end Data

end EndN

end CFSG.QuasithinUnique.Lin2
