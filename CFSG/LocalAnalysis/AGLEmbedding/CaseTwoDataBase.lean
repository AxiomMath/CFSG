module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Defs

variable {G : Type} [Group G] [Finite G]

structure D1CaseTwoDataBase (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfigU p P M H R Rbar
  cyclic : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
    IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
      Subgroup (H ⧸ primeComplementCore (G := H) p))
  rank : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3

theorem D1CaseTwoDataAt.toBase {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoDataAt p P M H R Rbar) :
    D1CaseTwoDataBase p P M H R Rbar :=
  ⟨hd.cfg, hd.cyclic, hd.rank⟩

end Defs

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataBase.inf_X0_facts (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoDataBase p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) :
    Group.IsSolvable ((d1X0 p M H).comap L.subtype) ∧
      ∀ k : L, (∀ y ∈ (d1X0 p M H).comap L.subtype, k * y * k⁻¹ ∈ (d1X0 p M H).comap L.subtype) →
        k ∈ (d1X0 p M H).comap L.subtype := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set X₀ := d1X0 p M H with hX₀
  have hiso := hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
      hd.cfg.catalog) hS hd.cyclic hd.rank hL hLX
  obtain ⟨hsimple, -, -, -⟩ :=
    hd.cfg.red.isSimpleGroup_of_isCyclic hd.cfg.catalog hL (hd.cyclic L hL)
  obtain ⟨hUP, -, hloc⟩ := hKL p L hiso
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨t, ht, htp, -⟩ :=
    exists_mem_sylow_inf_component hp hd.cfg.red.ne_two hd.cfg.red.core_eq_bot Rbar hL
  have hN : ∀ V : Subgroup (H ⧸ primeComplementCore (G := H) p),
      V ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L → V ≠ ⊥ →
        L ⊓ Subgroup.normalizer (V : Set (H ⧸ primeComplementCore (G := H) p)) ≤ X₀ :=
    fun V hV hV1 => (inf_le_inf_left L (normalizer_le_normalizer_of_isCyclic hp
      (hd.cyclic L hL) (Rbar.isPGroup'.to_le inf_le_left) (Subgroup.zpowers_le.mpr ht)
      (by rw [Nat.card_zpowers, htp]) hV hV1)).trans
      (hd.cfg.red.inf_normalizer_zpowers_le_of_aut (hAut _ _ _ _ hd.cfg.red hd.cfg.catalog)
          hd.cyclic hd.rank hL ht htp)
  have hΓX : (GLBCore p 1 (T : Subgroup L)).map L.subtype ≤ X₀ :=
    glbCore_map_le_of_normalizer_le hp hT hN
  have hne : GLBCore p 1 (T : Subgroup L) ≠ ⊤ := fun htop =>
    hLX fun x hx => hΓX ⟨⟨x, hx⟩, htop ▸ Subgroup.mem_top _, rfl⟩
  have hcomap : X₀.comap L.subtype = GLBCore p 1 (T : Subgroup L) := by
    rcases (hUP T hne).1 (X₀.comap L.subtype) (Subgroup.map_le_iff_le_comap.mp hΓX) with h | h
    · exact h
    · exact absurd (fun k hk => (Subgroup.mem_comap.mp (h.ge (Subgroup.mem_top ⟨k, hk⟩)) :))
        hLX
  refine ⟨hcomap ▸ (hloc T).2.2, fun k hk => ?_⟩
  rw [hcomap] at hk ⊢
  have hkN : k ∈ Subgroup.normalizer ((GLBCore p 1 (T : Subgroup L) : Subgroup L) : Set L) :=
    Subgroup.mem_normalizer_fintype hk
  rcases (hUP T hne).1 (Subgroup.normalizer ((GLBCore p 1 (T : Subgroup L) : Subgroup L) : Set L))
    Subgroup.le_normalizer with h | h
  · exact h ▸ hkN
  · exfalso
    have hΓn : (GLBCore p 1 (T : Subgroup L)).Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLBCore p 1 (T : Subgroup L)) with h1 | h1
    · have htX : (⟨t, ht.2⟩ : L) ∈ X₀.comap L.subtype := by
        show t ∈ X₀
        have htR : t ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := ht.1
        rw [hd.cfg.rbar] at htR
        obtain ⟨r, hrR, rfl⟩ := htR
        exact ⟨r, ⟨r.2, hd.cfg.ext.le_M hrR⟩, rfl⟩
      rw [hcomap, h1, Subgroup.mem_bot] at htX
      have : t = 1 := congrArg Subtype.val htX
      rw [this, orderOf_one] at htp
      exact hp.one_lt.ne htp
    · exact hne h1

end Data

end CFSG.AGLEmbedding
