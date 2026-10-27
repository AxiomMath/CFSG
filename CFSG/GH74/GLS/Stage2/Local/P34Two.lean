module

public import CFSG.GH74.GLS.Stage2.Local.P34Pair
public import CFSG.GH74.GLS.Stage2.Local.P34Comp

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Rank

theorem pRank_top_coe {X : Type} [Group X] [Finite X] (K : Subgroup X) :
    Open.pRank 2 (⊤ : Subgroup ↥K) = Open.pRank 2 K :=
  (CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by norm_num) K).symm

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem three_le_open_pRank_S (hctx : Stage2Ctx G z k S) : 3 ≤ Open.pRank 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hctx.sylow_top
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hP, hdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hdvd
  let P : Sylow 2 G := hP.toSylow hdvd
  have hPS : (P : Subgroup G) = S := rfl
  have h1 := (CFSG.SectionRank.pRank_sylow P).2
  rw [hPS] at h1
  have h2 : CFSG.pRank 2 ↥S = Open.pRank 2 S := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_coe]
  have h3 := hctx.std.rank.1
  omega

theorem three_le_pRank_cenBar (hctx : Stage2Ctx G z k S) :
    3 ≤ Open.pRank 2 (⊤ : Subgroup (CentralizerBar z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := three_le_open_pRank_S hctx
  have h2 : Open.pRank 2 S ≤ Open.pRank 2 (Cen z) :=
    SectionRank.pRank_mono (by norm_num) hctx.S_le_Cen
  have hodd : ¬ 2 ∣ Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := fun hd => by
    have := odd_card_pPrimeCore (Cen z)
    exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hd)
  have h3 : Open.pRank 2 (⊤ : Subgroup (CentralizerBar z)) = Open.pRank 2 (⊤ : Subgroup ↥(Cen z)) :=
    SectionRank.pRank_quotient_eq (pPrimeCore 2 ↥(Cen z)) hodd
  rw [h3, pRank_top_coe]
  omega

theorem open_pRank_hbar_le (H : Subgroup G) : Open.pRank 2 (⊤ : Subgroup (HBar H)) ≤ CFSG.pRank 2 G := by
  rw [← SectionRank.pRank_eq_open_pRank_top]
  exact pRank_hbar_le H

end Rank

section Comps

variable {Y : Type} [Group Y] [Finite Y]

theorem rank_pair_le (hF : fittingSubgroup Y = ⊥) {A B : Subgroup Y} (hA : IsComponent A)
    (hB : IsComponent B) (hAB : A ≠ B) :
    Open.pRank 2 (⊤ : Subgroup ↥A) + Open.pRank 2 (⊤ : Subgroup ↥B) ≤ Open.pRank 2 (⊤ : Subgroup Y) ∧
      2 ≤ Open.pRank 2 (⊤ : Subgroup ↥A) ∧ 2 ≤ Open.pRank 2 (⊤ : Subgroup ↥B) := by
  obtain ⟨hsA, hnA⟩ := component_isSimple hF hA
  obtain ⟨hsB, hnB⟩ := component_isSimple hF hB
  obtain ⟨hA2, EA, hEA, hEAa, hEAc⟩ := exists_elemAbelian_of_simple hsA hnA
  obtain ⟨hB2, EB, hEB, hEBa, hEBc⟩ := exists_elemAbelian_of_simple hsB hnB
  obtain ⟨hcomm, hinf⟩ := components_commute_inf hF hA hB hAB
  exact ⟨rank_add_le hcomm hinf hEA hEB hEAa hEBa hEAc hEBc, hA2, hB2⟩

theorem rank_triple_le (hF : fittingSubgroup Y = ⊥) {A B D : Subgroup Y} (hA : IsComponent A)
    (hB : IsComponent B) (hD : IsComponent D) (hAB : A ≠ B) (hAD : A ≠ D) (hBD : B ≠ D) :
    6 ≤ Open.pRank 2 (⊤ : Subgroup Y) := by
  obtain ⟨hsA, hnA⟩ := component_isSimple hF hA
  obtain ⟨hsB, hnB⟩ := component_isSimple hF hB
  obtain ⟨hsD, hnD⟩ := component_isSimple hF hD
  obtain ⟨hA2, EA, hEA, hEAa, hEAc⟩ := exists_elemAbelian_of_simple hsA hnA
  obtain ⟨hB2, EB, hEB, hEBa, hEBc⟩ := exists_elemAbelian_of_simple hsB hnB
  obtain ⟨hD2, ED, hED, hEDa, hEDc⟩ := exists_elemAbelian_of_simple hsD hnD
  obtain ⟨hcBD, hinfBD⟩ := components_commute_inf hF hB hD hBD
  obtain ⟨F₁, hF₁le, hF₁ea, hF₁card⟩ := exists_elemAbelian_join hcBD hinfBD hEB hED hEBa hEDa
    hEBc hEDc
  obtain ⟨hcAB, -⟩ := components_commute_inf hF hA hB hAB
  obtain ⟨hcAD, -⟩ := components_commute_inf hF hA hD hAD
  have hcA : ∀ a ∈ A, ∀ y ∈ B ⊔ D, a * y = y * a := by
    intro a ha y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute' hcBD hy
    calc a * (u * v) = (a * u) * v := by group
      _ = (u * a) * v := by rw [hcAB a ha u hu]
      _ = u * (a * v) := by group
      _ = u * (v * a) := by rw [hcAD a ha v hv]
      _ = u * v * a := by group
  have hinfA : A ⊓ (B ⊔ D) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxz : (⟨x, hx.1⟩ : ↥A) ∈ center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcA g g.2 x hx.2)
    rw [center_component_eq_bot hF hA, Subgroup.mem_bot] at hxz
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hxz)
  obtain ⟨F₂, -, hF₂ea, hF₂card⟩ := exists_elemAbelian_join hcA hinfA hEA hF₁le hEAa hF₁ea hEAc
    hF₁card
  have := SectionRank.le_pRank (by norm_num) le_top hF₂ea hF₂card
  omega

end Comps

section QData

theorem hQ1_of_sub {X : Type} [Group X] {Qs : Subgroup X} {c : X} (hc : c ∈ Qs)
    (h : ∀ N : Subgroup X, N ≤ Qs → (∀ l ∈ Qs, ∀ n ∈ N, l * n * l⁻¹ ∈ N) → N ≠ ⊥ → c ∈ N) :
    ∀ N : Subgroup ↥Qs, N.Normal → N ≠ ⊥ → (⟨c, hc⟩ : ↥Qs) ∈ N := by
  intro N hN hN1
  have hle : N.map Qs.subtype ≤ Qs := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hnorm : ∀ l ∈ Qs, ∀ n ∈ N.map Qs.subtype, l * n * l⁻¹ ∈ N.map Qs.subtype := by
    rintro l hl _ ⟨n, hn, rfl⟩
    exact ⟨⟨l, hl⟩ * n * ⟨l, hl⟩⁻¹, hN.conj_mem n hn ⟨l, hl⟩, rfl⟩
  have hne : N.map Qs.subtype ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at hbot
    exact le_bot_iff.1 hbot
  obtain ⟨n, hn, hnc⟩ := Subgroup.mem_map.1 (h _ hle hnorm hne)
  have : n = ⟨c, hc⟩ := Subtype.ext hnc
  rwa [← this]

@[expose] def QData {G : Type} [Group G] [Finite G] (z : G) : Prop :=
  ∃ (Q : Subgroup (CentralizerBar z)) (c : ↥Q), ⁅Q, Q⁆ = Q ∧ orderOf c = 2 ∧
    (∀ N : Subgroup ↥Q, N.Normal → N ≠ ⊥ → c ∈ N) ∧ 3 ≤ Open.pRank 2 (⊤ : Subgroup ↥Q)

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem qData_of_pair {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (h : Stage1Pair G z S q L₁ L₂) :
    QData z := by
  obtain ⟨hsup, hcomm, hcard⟩ := h.prod
  have h4 : 4 ≤ q := by
    have := h.gt3
    omega
  have hq₁ : IsQuasisimple ↥L₁ := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4 h.sl₁
  have hq₂ : IsQuasisimple ↥L₂ := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4 h.sl₂
  obtain ⟨c, hc₁, hc₂, hc1⟩ := exists_inf_ne_one hcard
  have hcc : c * c = 1 := inf_sq hcard ⟨hc₁, hc₂⟩
  have hcQ : c ∈ L₁ ⊔ L₂ := Subgroup.mem_sup_left hc₁
  refine ⟨L₁ ⊔ L₂, ⟨c, hcQ⟩, pair_perfect hq₁ hq₂, ?_, ?_, ?_⟩
  · exact orderOf_eq_two_of_sq (Subtype.ext hcc) (fun h' => hc1 (congrArg Subtype.val h'))
  · exact hQ1_of_sub hcQ fun N hN hNn hN1 =>
      pair_normal_mem h.odd h4 h.odd h4 h.sl₁ h.sl₂ hcomm hcard hN hNn hN1 hc₁ hc₂ hc1
  · have hodd : ∀ n, n = q → Odd n := fun n hn => by rw [hn]; exact h.odd
    have := pair_rank_three hcomm hcard (hasSL2Model_mono h.sl₁ hodd) (hasSL2Model_mono h.sl₂ hodd)
    rwa [pRank_top_coe]

theorem qData_of_sporadic (hctx : Stage2Ctx G z k S) {n : ℕ} (hs : Stage1Sporadic G z S n) :
    QData z := by
  obtain ⟨hq, hcard, -⟩ := hs.cover
  have hperf : ⁅(⊤ : Subgroup (CentralizerBar z)), (⊤ : Subgroup (CentralizerBar z))⁆ =
      (⊤ : Subgroup (CentralizerBar z)) := by
    have := hq.1
    rwa [Group.isPerfect_def, _root_.commutator_def] at this
  obtain ⟨c, hcZ, hc1⟩ : ∃ c : CentralizerBar z, c ∈ Subgroup.center (CentralizerBar z) ∧ c ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : Subgroup.center (CentralizerBar z) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hno x hx)
    rw [hbot] at hcard
    simp at hcard
  have hcc : c * c = 1 := by
    have h : (⟨c, hcZ⟩ : ↥(Subgroup.center (CentralizerBar z))) ^
        Nat.card ↥(Subgroup.center (CentralizerBar z)) = 1 := pow_card_eq_one'
    rw [hcard] at h
    have := congrArg Subtype.val h
    simpa [pow_two] using this
  refine ⟨(⊤ : Subgroup (CentralizerBar z)), ⟨c, Subgroup.mem_top c⟩, hperf, ?_, ?_, ?_⟩
  · exact orderOf_eq_two_of_sq (Subtype.ext hcc) (fun h' => hc1 (congrArg Subtype.val h'))
  · refine hQ1_of_sub (Qs := (⊤ : Subgroup (CentralizerBar z))) (Subgroup.mem_top c) fun N _ hNn hN1 => ?_
    have hNnormal : N.Normal := ⟨fun n hn g => hNn g (Subgroup.mem_top g) n hn⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNnormal with htop | hcen
    · rw [htop]
      exact Subgroup.mem_top c
    · obtain ⟨n, hn, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
        by_contra hno
        push Not at hno
        apply hN1
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.2 (hno x hx)
      have hnc : n = c :=
        eq_of_card_le_two (D := Subgroup.center (CentralizerBar z)) hcard.le (hcen hn) hcZ hn1 hc1
      rwa [← hnc]
  · rw [pRank_top_coe]
    exact three_le_pRank_cenBar hctx

theorem qData_of_ctx (hctx : Stage2Ctx G z k S) (hk : k ≠ Kind.g2 ∧ k ≠ Kind.m12) : QData z := by
  cases hctx.data with
  | g2 _ => exact absurd rfl hk.1
  | m12 _ => exact absurd rfl hk.2
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact qData_of_pair h.pair
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact qData_of_pair h.pair
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact qData_of_sporadic hctx h
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact qData_of_sporadic hctx h

end QData

section Bar

variable {G : Type} [Group G]

theorem commutator_barIn (H : Subgroup G) {P : Subgroup G} (hPH : P ≤ H) (hP : ⁅P, P⁆ = P) :
    ⁅barIn H P, barIn H P⁆ = barIn H P := by
  have h1 : (P.subgroupOf H).map H.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPH
  have h2 : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, h1, hP]
  unfold barIn
  rw [← Subgroup.map_commutator, h2]

end Bar

end CFSG.GH74.GLS.Stage2.Local.P34
