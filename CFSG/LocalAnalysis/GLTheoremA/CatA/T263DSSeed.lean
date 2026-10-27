module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem t263_catalogIs_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs X Q) : catalogIs Y Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem t263_isChevSimple_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsChevSimple 2 X) :
    IsChevSimple 2 Y :=
  h.elim (fun h' => Or.inl (t263_catalogIs_congr e h')) (fun h' => Or.inr (t263_catalogIs_congr e h'))

theorem t263_marking_n1_congr {L L' : Type} [Group L] [Group L'] (hL' : commutator L' = ⊤)
    (e : L ⧸ Subgroup.center L ≃* L' ⧸ Subgroup.center L')
    (h : GLAMarking L (fun lab _ _ _ _ _ => lab.n = 1)) :
    GLAMarking L' (fun lab _ _ _ _ _ => lab.n = 1) := by
  obtain ⟨-, lab, hΛ, hraw⟩ := h
  refine ⟨hL', lab, hΛ, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hn⟩
  exact ⟨hs, hna, e.symm.trans θ, hn⟩

@[expose] def T263DescSeed (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ → GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 →
    ∀ B₀ : Subgroup Ω, T263HasB0 p S B B₀ → T263Dich p S B →
    p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀ →
    ∀ T' : Subgroup Ω, T' ≠ ⊥ → IsPGroup 2 T' → T' ≤ S → B ≤ Subgroup.normalizer (T' : Set Ω) →
    B ⊓ Subgroup.centralizer (T' : Set Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    ∀ x : Ω, x ∈ B₀ → x ∉ Subgroup.centralizer (S : Set Ω) →
    (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥ →
    T263GConcl p S B ∨
      ∃ J W : Subgroup Ω, GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J ∧
        CFSG.Open.IsQuasisimple (PQuot p J) ∧ IsChevSimple 2 (PSimple p J) ∧
        (p = 3 → ¬ GLAMarking (PQuot 3 J) (fun lab _ _ _ _ _ => lab.n = 1)) ∧
        W ≤ J ∧ IsPGroup 2 W ∧ B ⊓ Subgroup.normalizer (J : Set Ω) ≤ Subgroup.normalizer (W : Set Ω) ∧
        ¬ W ≤ GLAPPrimeCoreOf p J

@[expose] def T263DiagStep : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω) (x : Ω) (J W : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → CFSG.Open.IsElemAbelian p B → x ∈ B →
    x ∉ Subgroup.centralizer (S : Set Ω) →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J → CFSG.Open.IsQuasisimple (PQuot p J) →
    W ≤ J → IsPGroup 2 W → B ⊓ Subgroup.normalizer (J : Set Ω) ≤ Subgroup.normalizer (W : Set Ω) →
    ¬ W ≤ GLAPPrimeCoreOf p J →
    ∃ D I : Subgroup Ω, D ≤ B ∧ GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω)) I ∧
      B ≤ Subgroup.normalizer (I : Set Ω) ∧ CFSG.Open.IsQuasisimple (PQuot p I) ∧
      Nonempty (PSimple p I ≃* PSimple p J) ∧ Nat.card (PQuot p I) < Nat.card ↥S ∧
      ∃ T'' : Subgroup Ω, T'' ≤ I ∧ IsPGroup 2 T'' ∧ B ≤ Subgroup.normalizer (T'' : Set Ω) ∧
        ¬ T'' ≤ GLAPPrimeCoreOf p I

theorem t263Desc_of_seed {Q : TauCeti.CFSGIndex → Prop} (hD : T263DiagStep) (hS : T263DescSeed Q) :
    T263Desc Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T' hT'ne hT'2 hT'S
    hBT' hker x hxB₀ hxC hxcomm
  rcases hS p hp hp2 Ω hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T' hT'ne hT'2 hT'S
      hBT' hker x hxB₀ hxC hxcomm with hconcl | ⟨J, W, hJ, hJq, hJc, hJF, hWJ, hW2, hWB, hWnc⟩
  · exact Or.inl hconcl
  · right
    obtain ⟨D, I, hDB, hI, hBI, hIq, ⟨e⟩, hIlt, T'', hT''I, hT''2, hBT'', hT''nc⟩ :=
      hD p hp hp2 Ω S B x J W hSn hSq hSp hB.1 (hB₀.1 hxB₀) hxC hJ hJq hWJ hW2 hWB hWnc
    have hIc : IsChevSimple 2 (PSimple p I) := t263_isChevSimple_congr e.symm hJc
    refine ⟨D, I, hDB, hI, hBI, hIq, hIc, hIlt, ⟨T'', hT''I, hT''2, hBT'', hT''nc⟩, ?_⟩
    intro hp3 hmk
    subst hp3
    exact hJF rfl (t263_marking_n1_congr hJq.1 e hmk)

end CFSG.LocalAnalysis.GLTheoremA.T263

end
