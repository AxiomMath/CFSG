module

public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_Gamma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        Subgroup.centralizer ({z} : Set G) ≤
            gamma2 (Subgroup.closure {u * e, u, z}) (Subgroup.centralizer ({z} : Set G)) ∧
          Subgroup.centralizer ({u} : Set G) ≤
            gamma2 (Subgroup.closure {u * e, u, z}) (Subgroup.centralizer ({u} : Set G))

@[expose] def C23_9_noZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f) → u * e ∉ zStarOf (rLayer Ω u)

@[expose] def C23_9_gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g → SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f) →
        (SectionOrthType p f Ω (rLayer Ω u) 5 true ∨
          SectionOrthType p f Ω (rLayer Ω u) 6 (!piSign p f)) →
            rLayer Ω e ⊔ rLayer Ω u = ⊤

variable {p f}

theorem gamma2_le_normalizer_alphaOf {G : Type} [Group G] {B α₀ : Subgroup G}
    (h : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀) (H : Subgroup G) :
    gamma2 B H ≤ Subgroup.normalizer (α₀ : Set G) := by
  refine iSup₂_le fun A hA => ?_
  have hA' : A ≤ B ∧ IsElemAbelian2 A 2 := hA
  calc H ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A : Set G) := inf_le_right
    _ ≤ Subgroup.normalizer (alphaOf A : Set G) := T7B.centralizer_le_normalizer_alphaOf A
    _ = Subgroup.normalizer (α₀ : Set G) := by rw [h A hA'.1 hA'.2]

theorem c23_9_of (h2 : C23_2 p f) (h4 : C23_4 p f) (h5 : C23_5 p f) (h7 : C23_7 p f)
    (hΓ : C23_Gamma p f) (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) : C23_9 p f := by
  intro G _ _ _ Ω K K' W z u e g h
  have hE : SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f) :=
    (h4 G Ω K K' W z u e g h).resolve_left (h7 G Ω K K' W z u e g h)
  obtain ⟨⟨hodd, halpha⟩, -, hY⟩ := h5 G Ω K K' W z u e g h
  have hset : Hyp23Setting p f Ω K K' z := h.std.setting
  have hY' : SectionOrthType p f Ω (rLayer Ω u) 5 true ∨
      SectionOrthType p f Ω (rLayer Ω u) 6 (!piSign p f) :=
    hY.resolve_left (hnoZ G Ω K K' W z u e g hset h.data hE)
  obtain ⟨hΓz, hΓu⟩ := hΓ G Ω K K' W z u e g hset h.data
  have hG := h2 G Ω K K' z h.std W h.hW h.hzW u h.hu h.huW h.hu1 h.huz h.hu2
  have hN : Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hG]
    exact sup_le (hΓu.trans (gamma2_le_normalizer_alphaOf halpha _))
      (hΓz.trans (gamma2_le_normalizer_alphaOf halpha _))
  have hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard h.std.1.hz)
  exact ⟨⟨hα, hgen G Ω K K' W z u e g hset h.data hE hY'⟩, hE, hY'⟩

end CFSG.ClassicalInvolution.Asc77
