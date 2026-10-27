module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem conjClosure_eq_self_of_le_normalizer {Y : Type*} [Group Y] {P R : Subgroup Y}
    (h : R ≤ Subgroup.normalizer (P : Set Y)) : conjClosure P R = P := by
  apply le_antisymm
  · apply conjClosure_le
    intro r hr z hz
    exact (Subgroup.mem_normalizer_iff.mp (h hr) z).mp hz
  · exact le_conjClosure P R

theorem le_of_isMinOverBorel {Y : Type*} [Group Y] {L S₀ P : Subgroup Y}
    (hP : IsMinOverBorel L S₀ P) (hS₀L : S₀ ≤ L) : S₀ ≤ P :=
  fun _ hx => hP.2.1.le ⟨hS₀L hx, Subgroup.le_normalizer hx⟩

theorem not_le_normalizer_of_isMinOverBorel {Y : Type*} [Group Y] {L S₀ P : Subgroup Y}
    (hP : IsMinOverBorel L S₀ P) : ¬ L ≤ Subgroup.normalizer (S₀ : Set Y) := by
  intro hLN
  have hLP : L ⊓ Subgroup.normalizer (S₀ : Set Y) = L := inf_eq_left.2 hLN
  have h := hP.2.1
  rw [hLP] at h
  exact lt_irrefl L (h.trans_le hP.1)

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
theorem inf_normalizer_inf_eq {L P : Subgroup (X ⧸ gnC T)}
    (hP : IsMinOverBorel L (gnImg T T ⊓ L) P) :
    gnImg T T ⊓ (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
      Subgroup.normalizer (P : Set (X ⧸ gnC T))) ⊓ L = gnImg T T ⊓ L := by
  have hSP : gnImg T T ⊓ L ≤ P := le_of_isMinOverBorel hP inf_le_right
  apply le_antisymm
  · exact fun x hx => ⟨hx.1.1, hx.2⟩
  · intro x hx
    exact ⟨⟨hx.1, Subgroup.le_normalizer hx.2, Subgroup.le_normalizer (hSP hx)⟩, hx.2⟩

theorem isSylowTwoOf_pElementSubgroup (hX : GNSetting X T) {L P : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hP : IsMinOverBorel L (gnImg T T ⊓ L) P) :
    IsSylowTwoOf (gnImg T T ⊓ L) (pElementSubgroup 2 P) := by
  have hTp : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map _
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hL.2.1
  have hPS : gnImg T T ⊓ L ≤ P := le_of_isMinOverBorel hP inf_le_right
  have hS : gnImg T T ⊓ L ≤ pElementSubgroup 2 P := fun x hx => by
    apply Subgroup.subset_closure
    refine ⟨hPS hx, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hTp ⟨x, hx.1⟩
    exact ⟨k, (Subgroup.orderOf_coe ⟨x, hx.1⟩).trans hk⟩
  exact B6.isSylowTwoOf_mono hSyl hS ((pElementSubgroup_le P).trans hP.1)

theorem commutator_ne_bot_of_ne (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {L P : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) (hP : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hne : P ≠ L) :
    ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 P)), twoResidual (pElementSubgroup 2 P)⁆ ≠ ⊥ := by
  have hTp : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map _
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hL.2.1
  have hRN : gnImg T T ⊓ (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
      Subgroup.normalizer (P : Set (X ⧸ gnC T))) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
    fun x hx => hx.2.1
  have hRP : gnImg T T ⊓ (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
      Subgroup.normalizer (P : Set (X ⧸ gnC T))) ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)) :=
    fun x hx => hx.2.2
  have hR2 : IsPGroup 2 ↥(gnImg T T ⊓ (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
      Subgroup.normalizer (P : Set (X ⧸ gnC T)))) := hTp.to_le inf_le_left
  have hSylR : IsSylowTwoOf
      (gnImg T T ⊓ (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
        Subgroup.normalizer (P : Set (X ⧸ gnC T))) ⊓ L) L := by
    rw [inf_normalizer_inf_eq hP]
    exact hSyl
  have hPR : IsMinOverBorel L
      (gnImg T T ⊓ (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
        Subgroup.normalizer (P : Set (X ⧸ gnC T))) ⊓ L) P := by
    rw [inf_normalizer_inf_eq hP]
    exact hP
  have hcond := (hK (X ⧸ gnC T) L _ P hL.2.2 hch hRN hR2 hSylR hPR).2
  have h3a := conjClosure_eq_self_of_le_normalizer hRP
  have key := hcond (by rw [h3a]; exact hne)
  rw [h3a] at key
  exact key
