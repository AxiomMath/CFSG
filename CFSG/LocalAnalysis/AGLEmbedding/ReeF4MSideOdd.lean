module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorLineRankY
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section F4One

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barM_inf_preimage {M X : Subgroup G}
    {Fb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hFb : Fb ≤ barM M X) :
    barM M (X ⊓ (Fb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) = Fb := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    obtain ⟨-, ⟨m, hm, hmx⟩⟩ := Subgroup.mem_subgroupOf.mp hx
    have : m = ⟨x, hxM⟩ := Subtype.ext hmx
    rw [← this]
    exact hm
  · intro y hy
    obtain ⟨⟨x, hxM⟩, hx, rfl⟩ := hFb hy
    exact ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hx,
      ⟨x, hxM⟩, hy, rfl⟩, rfl⟩

theorem D1SurvivorData.preimage_le_or_le {p : ℕ} {P : Sylow p G} {M H R X : Subgroup G}
    (h : D1SurvivorData p P M H R X) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} [T.Normal]
    (hT : T ≤ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M)) :
    (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ GLBPrimeCore p H ∨
      X ≤ (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype :=
  h.normal_dichotomy _ (h.ph3.preimage_le_inf (h.ph3.le_barM_inf_of_le_centralizer
      (hT.trans (h.ph3.oddCore_le_centralizer h84 hD2))))
    (inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf T)))

theorem D1ReeF4Data.le_centralizer_pCore {P : Sylow 5 G} {M H R X : Subgroup G}
    (h : D1ReeF4Data P M H R X) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hs5 : s ≠ 5) :
    barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
  by_contra hns
  have := Fact.mk hs
  have h5 : Nat.Prime 5 := by norm_num
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  set Sh : Subgroup G := (Sg.comap mk).map M.subtype with hSh
  have hXM : X ≤ M := h.surv.le_R.trans h.surv.ph3.le_M
  have hXp : IsPGroup 5 X := fun x => ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩
  have hXb := isElemAbelian_barM (M := M) h.elem
  have hXbcard : Nat.card (barM M X) = 5 ^ 2 := by
    rw [card_barM_of_isPGroup h5 (by norm_num) hXM hXp, h.card_X]
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  set Γ : Set (↥M ⧸ CFSG.pCore 2 ↥M) :=
    {y | ∃ g ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∃ hg : g ∈ M, mk ⟨g, hg⟩ = y} with hΓ
  have h4 : 4 ≤ Open.pRank s Sg := by
    refine four_le_pRank_of_lineTransitive hs hs2 hs5 CFSG.pCore_isPGroup hXb hXbcard
      (le_top.trans hSgN) Γ (fun _ _ => hSgN (Subgroup.mem_top _)) ?_ ?_ hns
    · rintro _ ⟨g, hg, hgM, rfl⟩
      exact mem_normalizer_barM hgM (h.normalizer_le hg)
    · intro Fb Fb' hFb hFb' hFc hFc'
      set F := X ⊓ (Fb.comap mk).map M.subtype
      set F' := X ⊓ (Fb'.comap mk).map M.subtype
      have hbF : barM M F = Fb := barM_inf_preimage hFb
      have hbF' : barM M F' = Fb' := barM_inf_preimage hFb'
      have hFX : F ≤ X := inf_le_left
      have hF'X : F' ≤ X := inf_le_left
      have hcF : Nat.card F = 5 := by
        rw [← card_barM_of_isPGroup h5 (by norm_num) (hFX.trans hXM) (hXp.to_le hFX), hbF, hFc]
      have hcF' : Nat.card F' = 5 := by
        rw [← card_barM_of_isPGroup h5 (by norm_num) (hF'X.trans hXM) (hXp.to_le hF'X), hbF',
          hFc']
      obtain ⟨g, hg, hgF⟩ := h.transitive F F' hFX hF'X hcF hcF'
      refine ⟨mk ⟨g, hg.1.2⟩, ⟨g, hg, hg.1.2, rfl⟩, ?_⟩
      rw [← hbF, ← hbF', ← barM_map_conj hg.1.2, hgF]
  have h4' : 4 ≤ Open.pRank s Sh := by
    have h1 := pRank_barM_le hs hs2 M Sh (Subgroup.map_subtype_le _)
    rw [barM_preimage] at h1
    exact h4.trans h1
  have hShN : Sh ≤ GLBPrimeCore 5 H := by
    refine (h.surv.preimage_le_or_le h84 hD2 (pCore_le_pPrimeCore_two hs hs2)).resolve_right
      fun hXSh => ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := s) (G := ↥M ⧸ CFSG.pCore 2 ↥M))
    have hdvd := Subgroup.card_dvd_of_le (barM_le_of_le_preimage hXSh)
    rw [hXbcard, hk] at hdvd
    have h5dvd : 5 ∣ s ^ k := (dvd_pow_self 5 (by norm_num)).trans hdvd
    exact hs5 ((Nat.prime_dvd_prime_iff_eq h5 hs).mp (h5.dvd_of_dvd_pow h5dvd)).symm
  exact h.surv.ph3.false_of_preimage_le hs hs2
    (mem_glbBetaFour_of_le_pRank hs hs2 h.surv.ph3.maxTwoLocal_M.1 (Subgroup.map_subtype_le _) h4')
    CFSG.pCore_isPGroup ((by norm_num : 3 ≤ 4).trans h4') (glbPrimeCore_le 5 H)
    (le_normalizer_glbPrimeCore 5 H) h.surv.ph3.primeCore_le hShN

end F4One

end CFSG.AGLEmbedding
