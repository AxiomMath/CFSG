module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.KFactLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.ParabolicFacts

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin.B2F CFSG.Quasithin.E2

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem hcard_of_gn (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hLevi : P ≠ L → Group.IsSolvable ↥(pElementSubgroup 2 P) ∨
      Open.IsQuasisimple (↥(pElementSubgroup 2 P) ⧸ CFSG.pCore 2 ↥(pElementSubgroup 2 P))) :
    ∀ K M : Subgroup X,
      K.map (QuotientGroup.mk' (gnC T)) = pElementSubgroup 2 P ⊔ (gnImg T T ⊓
        (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T)))) →
      MinParabolic K (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
        Subgroup.normalizer (P : Set (X ⧸ gnC T)))) M → CharTwo K →
      ∀ (V : Subgroup X) (hV : IsElemAbelian 2 V),
        V = VZ (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
          Subgroup.normalizer (P : Set (X ⧸ gnC T)))) K →
        ∀ I, E23FamGen K (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
            Subgroup.normalizer (P : Set (X ⧸ gnC T)))) V hV I →
          (∀ L' ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L' (fixV (autI hV (twoResidual K))) n) →
            twoResidual K ≤ thompsonJ K → I.card < 2 := by
  intro K M hmap hmin hF V hV hVZ I hFam hnat hJ
  set N : Subgroup (X ⧸ gnC T) :=
    Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T))
    with hNdef
  set π := QuotientGroup.mk' (gnC T) with hπ
  set R : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ N with hRdef
  have hNL : N ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := inf_le_left
  have hRP : R ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)) := inf_le_right.trans inf_le_right
  have hTp : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map _
  have hR2 : IsPGroup 2 ↥R := hTp.to_le inf_le_left
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hL.2.1
  have hLN : gnImg T T ⊓ L ≤ N :=
    le_inf (inf_le_right.trans Subgroup.le_normalizer)
      ((le_of_isMinOverBorel hPb inf_le_right).trans Subgroup.le_normalizer)
  have hRL : R ⊓ L = gnImg T T ⊓ L :=
    le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (le_inf inf_le_left hLN) inf_le_right)
  have hne : K.map π ≠ (gnStab T N).map π := by
    rw [map_gnStab N, hmap]
    obtain ⟨M₀, hM₀⟩ := (hK _ L R P hL.2.2 hch (inf_le_right.trans hNL) hR2
      (by rw [hRL]; exact hSyl) (by rw [hRL]; exact hPb)).1
    rw [conjClosure_eq_self_of_le_normalizer hRP] at hM₀
    intro h
    exact hM₀.not_normal (by rw [h]; exact Subgroup.le_normalizer)
  by_cases hPL : P = L
  ·
    have hW : pElementSubgroup 2 P = L := by
      rw [hPL]
      exact pElementSubgroup_eq_of_isMinOverBorel_self hL.2.2 inf_le_right
        (hTp.to_le inf_le_left) (hPL ▸ hPb)
    have hq : Open.IsQuasisimple ↥(pElementSubgroup 2 P) := hW ▸ hL.2.2
    exact card_lt_two_of_sup_image hmin hF π hq hR2
      (hRP.trans (normalizer_le_normalizer_pElementSubgroup 2 P)) hmap hV hVZ hFam hnat hJ
  · exact card_lt_two_of_levi hmin hF π hR2 hRP hmap hne (hLevi hPL) hV hVZ hFam hnat hJ

end CFSG.AGLEmbeddingD2.Tits.GN516
