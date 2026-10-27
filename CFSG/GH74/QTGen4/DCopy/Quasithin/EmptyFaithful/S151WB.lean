module

public import CFSG.Quasithin.EmptyFaithful.S151WB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151XD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise commutatorElement

@[expose] def Input15122ThreeEFlip4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeE T Mc Z₁ L → IsPSL 4 2 1 ↥L →
    ¬ SActsTrivially L (s1516 T Z₁) → Case15122Seven T M Mc Z₁ L

theorem input15122ThreeE_of'_F4 (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kN : L45NotA38Type) (hno3 : Input15122ThreeENoFlip)
    (hflip : Input15122ThreeEFlip4_F4) : Input15122ThreeE_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h3E
  have h3E' := h3E
  by_cases hfl : IsPSL 4 2 1 ↥L ∧ ¬ SActsTrivially L (s1516 T Z₁)
  · exact hflip G T Mc M Z₁ Z₂ V₁ V₂ L hc h3E' hfl.1 hfl.2
  obtain ⟨htype, hMLpar, hMLne, hCML⟩ := h3E
  have hcase : IsPSL 5 2 1 ↥L ∨ (IsPSL 4 2 1 ↥L ∧ SActsTrivially L (s1516 T Z₁)) := by
    rcases htype with h4 | h5
    · exact Or.inr ⟨h4, by_contra fun hn => hfl ⟨h4, hn⟩⟩
    · exact Or.inl h5
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have htypeq : IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    htype.imp (isPSL_quotient_pCore (by norm_num)) (isPSL_quotient_pCore (by norm_num))

  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L htypeq)

  have hselfN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L := by
    rcases htypeq with h4 | h5
    · exact FLc.normalizer_inf_le_of_isPSL (n := 4) (by norm_num) h4 hsyl
    · exact FLc.normalizer_inf_le_of_isPSL (n := 5) (by norm_num) h5 hsyl
  have hSM : S ≤ M := (s1516_le T Z₁).trans hMf.1.1.2
  have hMLne' : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
  have hBM : S ⊓ L ≤ M ⊓ L := le_inf (inf_le_left.trans hSM) inf_le_right
  have hloc := fun P => input15122ThreeELocalSafe_of hno3 L S P

  have hstar : ∀ P : Subgroup G, SMin L S P → P ≤ M ∨ P ≤ mZ1516 Mc Z₁ := by
    intro P hP
    obtain ⟨hchP, hno, -⟩ := hloc P hcase hS2 hSN hsyl hP
    have hchH : CharTwo (P ⊔ S) := zb_charTwo_sup hP.sP hS2 hchP
    have hmin : IsMinParabolicOf (P ⊔ S) (P ⊔ S) := hP.isMinParabolic hS2 hsyl hselfN
    exact bang_of_good h118 h126 hc hP.le hchH hmin hno
  have hQ : ∀ P : Subgroup G, SMin L S P → P ≤ (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) := by
    intro P hP
    rcases hstar P hP with h | h
    · exact le_sup_of_le_right (le_inf h hP.le)
    · exact le_sup_of_le_left (le_inf h hP.le)
  have hjoin : (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) = L :=
    le_antisymm (sup_le inf_le_right inf_le_right)
      (input15122L45Gen_holds G L S htypeq hS2 hSN hsyl _ hQ)

  obtain ⟨P, hP, hPnot⟩ : ∃ P : Subgroup G, SMin L S P ∧ ¬ P ≤ mZ1516 Mc Z₁ ⊓ L := by
    by_contra hall
    push Not at hall
    exact hMLne (le_antisymm inf_le_right
      (input15122L45Gen_holds G L S htypeq hS2 hSN hsyl _ hall))
  have hPnotZ : ¬ P ≤ mZ1516 Mc Z₁ := fun h => hPnot (le_inf h hP.le)
  have hPM : P ≤ M := (hstar P hP).resolve_right hPnotZ
  have hPML : P ≤ M ⊓ L := le_inf hPM hP.le
  obtain ⟨-, -, hoP⟩ := hloc P hcase hS2 hSN hsyl hP
  have hzl := input15122ThreeEZL2_of h37 h38 kN G T Mc M Z₁ Z₂ V₁ V₂ L hc h3E'
  have hCent : CentS15122 T M Z₁ L := centS15122_of hc hSN hzl hPML hPnotZ hoP
  exact ⟨htype, hjoin, hMLpar, hMLne, hCML, ⟨inf_le_right, S ⊓ L, hsyl, hselfN.trans hBM⟩, hMLne',
    hCent⟩

end CFSG.Quasithin
