module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.OverS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin.B2F CFSG.Quasithin.E2

variable {X : Type} [Group X] {T : Subgroup X}

theorem inf_gnC_le_gnStab (T : Subgroup X) (N : Subgroup (X ⧸ gnC T)) :
    T ⊓ gnC T ≤ gnStab T N := by
  intro x hx
  refine mem_gnStab.2 ⟨hx.1, ?_⟩
  have h1 : QuotientGroup.mk' (gnC T) x = 1 := (QuotientGroup.eq_one_iff x).2 hx.2
  rw [h1]
  exact N.one_mem

variable [Finite X]

theorem parabolic_of_baum_le_gnStab' (hE : E23NonsolvGen) (hK : KFactChevMinParabolic)
    (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hB : baum T ≤ gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
      Subgroup.normalizer (P : Set (X ⧸ gnC T))))
    (hcard : ∀ K M : Subgroup X,
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
            twoResidual K ≤ thompsonJ K → I.card < 2)
    (hSym : AGL81I516SymOver) :
    pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  refine parabolic_of_concl_over hK hX hL hch hPb fun K M₁ hSK hmap' hmin hF => ?_
  rcases concl1Gen_over_weak_or_sym hE hP hX.sylow.2.1 hB (gnStab_le T _) hmin hF
      (hcard K M₁ hmap' hmin hF) with hc | ⟨hJ, hV, hsym⟩
  · exact Or.inl (concl_of_concl1Gen hF hmin.isSylow hc)
  ·
    right
    set N : Subgroup (X ⧸ gnC T) :=
      Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T))
      with hNdef
    have hRP : gnImg T T ⊓ N ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)) :=
      inf_le_right.trans inf_le_right
    have hRW : gnImg T T ⊓ N ≤ Subgroup.normalizer (pElementSubgroup 2 P : Set (X ⧸ gnC T)) :=
      hRP.trans (normalizer_le_normalizer_pElementSubgroup 2 P)
    have hSimg : gnImg T (gnStab T N) = gnImg T T ⊓ N := gnImg_gnStab T N
    have hSN : gnImg T T ⊓ N ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
      inf_le_right.trans inf_le_left
    refine hSym X T hX C₁ C₂ hP L hL hch P hPb (gnStab T N) hB (gnStab_le T N)
      (pCoreOf_le_gnStab hX N) (inf_gnC_le_gnStab T N) K M₁ hSK ?_ hmin hF hJ hV hsym
    show K.map (QuotientGroup.mk' (gnC T)) = _
    rw [hmap', hSimg, inf_eq_left.2 hSN, conjClosure_eq_self_of_le_normalizer hRP,
      conjClosure_eq_self_of_le_normalizer hRW]

end CFSG.AGLEmbeddingD2.Tits.GN516
