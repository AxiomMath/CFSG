module

public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbBlock
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def StmtFaithfulExtraspecialRank : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {s p : ℕ}, s.Prime → s ≠ 2 → p.Prime → 5 ≤ p → s ≠ p →
    ∀ (Sg X : Subgroup Y), IsPGroup s Sg → X ≤ Subgroup.normalizer (Sg : Set Y) →
      Nat.card X = p ^ 3 → (∀ x ∈ X, x ^ p = 1) →
      ¬ ⁅X, X⁆ ≤ Subgroup.centralizer (Sg : Set Y) → 4 ≤ Open.pRank s Sg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.commutator_oddCore (hG1 : StmtFaithfulExtraspecialRank)
    (h : D1PhaseThree p P M H R) (hp5 : 5 ≤ p) {X : Subgroup G} (hXM : X ≤ M)
    (hXcard : Nat.card X = p ^ 3) (hXexp : ∀ x ∈ X, x ^ p = 1) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p) :
    barM M ⁅X, X⁆ ≤ Subgroup.centralizer
        ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) := by
  by_cases hns : barM M ⁅X, X⁆ ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M))
  · exact Or.inl hns
  right
  have hp := h.prime
  have := Fact.mk hs
  have hp2 : p ≠ 2 := by omega
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  have hXp : IsPGroup p X := IsPGroup.of_card hXcard
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hXb : Nat.card (barM M X) = p ^ 3 := by
    rw [card_barM_of_isPGroup hp hp2 hXM hXp, hXcard]
  have hXbexp : ∀ x ∈ barM M X, x ^ p = 1 := by
    rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
    have : (⟨x, hxM⟩ : M) ^ p = 1 :=
      Subtype.ext (by simpa using hXexp x (Subgroup.mem_subgroupOf.mp hxX))
    rw [← map_pow, this, map_one]
  have hcomm : ⁅barM M X, barM M X⁆ = barM M ⁅X, X⁆ := by
    rw [barM, barM, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXM,
      Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self X).trans hXM)]
  have hrank := hG1 hs hs2 hp hp5 hsp Sg (barM M X) CFSG.pCore_isPGroup (le_top.trans hSgN) hXb
    hXbexp (by rw [hcomm]; exact hns)
  have h1 := pRank_barM_le hs hs2 M ((Sg.comap mk).map M.subtype) (Subgroup.map_subtype_le _)
  rw [barM_preimage] at h1
  omega

theorem D1PhaseThree.commutator_le_centralizer_compFive (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (hα : KFactThreeOrFiveDvd)
    (hβ : KFactOutElemRank) (hp5 : 5 ≤ p) {X : Subgroup G} (hXK : X ≤ H ⊓ M)
    (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXnorm : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) → N ≠ ⊥ →
      ⁅X, X⁆ ≤ N)
    (hE : ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2)
    {L : Subgroup G} (hL2 : IsTwoPrimeComponent M L) (hLN : L ≤ GLBPrimeCore p H) :
    barM M ⁅X, X⁆ ≤ Subgroup.centralizer (barM M L : Set _) := by
  have hLK : L ≤ H ⊓ M := hLN.trans (le_inf (glbPrimeCore_le p H) h.primeCore_le)
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by omega
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Kb := barM M (H ⊓ M) with hKb
  have hLbC : IsComponentOf Lb ⊤ := hL2.component
  have hXM : X ≤ M := hXK.trans inf_le_right
  have hMtop : M ≠ ⊤ := fun hM => h.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h.glob.kProper M hMtop).quotient _
  have hLcat := hcat.isCatalogGroup_center_quotient hLbC
  have hpL : ¬ p ∣ Nat.card Lb := by
    have hcop : p.Coprime (Nat.card L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime p H)
    have hdvd : Nat.card Lb ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf M) mk
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
    intro hpd
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcop (hpd.trans hdvd)
  have hsimple : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLbC.2.2.2
  obtain ⟨q, hq, hq2, hqp, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q < p ∧
      q ∣ Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) := by
    rcases hα _ hsimple (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hLbC.2.2) hLcat with h3 | h5
    · exact ⟨3, Nat.prime_three, by decide, by omega, h3⟩
    · refine ⟨5, Nat.prime_five, by decide, ?_, h5⟩
      have hdvdL : Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) ∣ Nat.card Lb :=
        Subgroup.card_quotient_dvd_card _
      have hp5' : p ≠ 5 := fun he => hpL (he ▸ h5.trans hdvdL)
      omega
  obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
  have hLbK : Lb ≤ Kb := Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
    (hLK (Subgroup.mem_subgroupOf.mp hz)))
  have horbit : ∀ (m : ℕ) (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M), (∀ j, g j ∈ Kb) →
      Function.Injective (fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) → m ≤ 3 := by
    intro m g hg hinj
    have hm := le_pRank_of_injective_conj stmtComponentRank stmtBarPRankLift inf_le_right hq
      hq2 hLbC hLbK hyL hyq hlL hyl g hg hinj
    by_contra hm3
    exact h.false_of_four_le_pRank' hind hq hq2 hqp (by omega)
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    have hxM : x ∈ M := hXM hx
    have hxb : mk ⟨x, hxM⟩ ∈ Subgroup.normalizer (Lb : Set _) := by
      by_contra hxbN
      have hxp : IsPGroup p (Subgroup.zpowers (mk ⟨x, hxM⟩)) := by
        refine isPGroup_zpowers_of_pow_eq_one (k := 1) ?_
        have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hXexp x hx)
        rw [pow_one, ← map_pow, this, map_one]
      have hxbK : mk ⟨x, hxM⟩ ∈ Kb :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXK hx))
      have hinj := injective_conj_pow_of_not_mem_normalizer hxp hxbN
      have := horbit p (fun j => (mk ⟨x, hxM⟩) ^ (j : ℕ)) (fun j => Kb.pow_mem hxbK _) hinj
      omega
    have hLx := hL2.map_conj hxM
    have heq : barM M (L.map (MulAut.conj x).toMonoidHom) = barM M L := by
      rw [barM_map_conj hxM]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxb
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLx.eq_of_barM_eq hL2 heq)
  set C := X ⊓ blockCentralizer M L with hC
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      mem_normalizer_blockCentralizer (hXM hx) (hXL hx)⟩
  by_cases hC0 : C = ⊥
  swap
  · have h1 := hXnorm C inf_le_left hXC hC0
    exact (barM_mono (h1.trans inf_le_right)).trans (barM_blockCentralizer_le M L)
  exfalso
  obtain ⟨E, hEX, hEel, hEcard⟩ := hE
  have hEb : barM M E ⊓ Subgroup.centralizer (Lb : Set _) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨⟨x, hxM⟩, hxE, rfl⟩, hxC⟩
    have hxC' : x ∈ C := ⟨hEX (Subgroup.mem_subgroupOf.mp hxE), ⟨x, hxM⟩, hxC, rfl⟩
    rw [hC0, Subgroup.mem_bot] at hxC'
    have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext hxC'
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hle := hβ _ Lb (barM M E) hLbC hLcat p hpp hp5 hpL
    (barM_le_normalizer_barM (hEX.trans hXL)) (isElemAbelian_barM_of hEel) hEb
  rw [card_barM_of_elem hpp hp2 (hEX.trans hXM) hEel, hEcard] at hle
  have : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  omega

end CFSG.AGLEmbedding
