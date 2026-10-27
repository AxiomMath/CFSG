
module

public import CFSG.Quasithin.Vol2.Ch1Comm

@[expose] public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

structure SQTKHypCat (G : Type) [Group G] : Prop where
  finite : Finite G
  sqt : CFSG.IsStronglyQuasithin G
  kgroup : CFSG.SectionRank.IsKGroupCat G
  o2 : CFSG.pCore 2 G = ⊥

abbrev A23ListCat (S : Type) [Group S] : Prop := CFSG.Milestones.SQTKSimpleList S

@[expose] def A36ConclusionCat {G : Type} [Group G] (L : Subgroup G) : Prop :=
  (CFSG.IsComponent L ∧ IsSimpleGroup ↥L ∧ A23ListCat ↥L) ∨
    (CFSG.IsComponent L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧ A36Case2List ↥L) ∨
    A36Case3 ↥L ∨ A36Case4 ↥L

@[expose] def A36StrongCat {G : Type} [Group G] (L : Subgroup G) : Prop :=
  A36ConclusionCat L ∧ A36Common ↥L ∧ ((A36Case3 ↥L ∨ A36Case4 ↥L) → A36Extra ↥L)

@[expose] def A36StatementCat (G : Type) [Group G] : Prop :=
  ∀ L ∈ cComp (⊤ : Subgroup G), A36StrongCat L

@[expose] def A36ForSQTKCat : Prop := ∀ (Q : Type) [Group Q], SQTKHypCat Q → A36StatementCat Q

@[expose] def A36CoreCat {G : Type} [Group G] (L : Subgroup G) : Prop :=
  (CFSG.IsComponent L ∨ A36Case3 ↥L ∨ A36Case4 ↥L) ∧ A36Common ↥L ∧
    ((A36Case3 ↥L ∨ A36Case4 ↥L) → A36Extra ↥L)

@[expose] def A36CoreStatementCat (G : Type) [Group G] : Prop :=
  ∀ L ∈ cComp (⊤ : Subgroup G), A36CoreCat L

@[expose] def A36CoreForSQTKCat : Prop :=
  ∀ (Q : Type) [Group Q], SQTKHypCat Q → A36CoreStatementCat Q

theorem A36StrongCat.core {G : Type} [Group G] {L : Subgroup G} (h : A36StrongCat L) :
    A36CoreCat L := by
  refine ⟨?_, h.2.1, h.2.2⟩
  rcases h.1 with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
  · exact Or.inl hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)

theorem A36ForSQTKCat.core (h : A36ForSQTKCat) : A36CoreForSQTKCat := fun Q _ hQ L hL =>
  (h Q hQ L hL).core

@[expose] def A37ForSQTKCat : Prop := ∀ (Q : Type) [Group Q], SQTKHypCat Q → A37Statement Q

@[expose] def A38ForSQTKCat : Prop := ∀ (Q : Type) [Group Q], SQTKHypCat Q → A38Part3 Q

@[expose] def A39ForSQTKCat : Prop := ∀ (Q : Type) [Group Q], SQTKHypCat Q → A39Statement Q

@[expose] def A312ForSQTKCat : Prop := ∀ (Q : Type) [Group Q], SQTKHypCat Q → A312Statement Q

theorem SQTKHypCat.quotient_pCore (X : Type) [Group X] [Finite X]
    (hX : CFSG.SectionRank.IsSQTKCat X) : SQTKHypCat (X ⧸ CFSG.pCore 2 X) where
  finite := inferInstance
  sqt := (CFSG.SectionRank.isStronglyQuasithin_quotient_two_group_iff (CFSG.pCore 2 X)
    CFSG.pCore_isPGroup).2 hX.1
  kgroup := hX.2.quotient _
  o2 := pCore_two_quotient_pCore_two X

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem sqtkHypCat_quotient_of_pCoreOf_ne_bot (hK : LocalSQTK G) {H : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) : SQTKHypCat (↥H ⧸ CFSG.pCore 2 ↥H) :=
  SQTKHypCat.quotient_pCore ↥H (hK H hH)

theorem lemma_1_2_1_one (hK : LocalSQTK G) (h39 : A39ForSQTKCat) {H : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) : cCompSpan H = perfectCore H :=
  cCompSpan_eq_perfectCore_of_subgroup H
    (h39 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH)).1

theorem commutator_le_pCoreOf_inf_of_le {H L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ cComp H)
    (h₂ : L₂ ∈ cComp H) (hc : ⁅L₁, L₂⁆ ≤ pCoreOf 2 H) :
    ⁅L₁, L₂⁆ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ∧ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn₁ := le_normalizer_of_mem_cComp h₁ h₂
  have hn₂ := le_normalizer_of_mem_cComp h₂ h₁
  have hc₁ : ⁅L₁, L₂⁆ ≤ L₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hn₁
  have hc₂ : ⁅L₁, L₂⁆ ≤ L₂ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hn₂
  have hLH₁ : L₁ ≤ H := le_of_mem_cComp h₁
  have hLH₂ : L₂ ≤ H := le_of_mem_cComp h₂
  have hpH : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnormO : ∀ {L : Subgroup G}, L ≤ H →
      L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro L hLH x hx
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, ?_⟩
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hx)
  have hle₁ : L₁ ⊓ pCoreOf 2 H ≤ pCoreOf 2 L₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (hnormO hLH₁)
      (hpH.to_le inf_le_right)
  have hle₂ : L₂ ⊓ pCoreOf 2 H ≤ pCoreOf 2 L₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (hnormO hLH₂)
      (hpH.to_le inf_le_right)
  refine ⟨le_inf (fun x hx => hle₁ ⟨hc₁ hx, hc hx⟩) (fun x hx => hle₂ ⟨hc₂ hx, hc hx⟩), ?_⟩
  exact inf_le_left.trans (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h₁))

theorem lemma_1_2_1_two (hK : LocalSQTK G) (h37 : A37ForSQTKCat) {H L₁ L₂ : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (h₁ : L₁ ∈ cComp H) (h₂ : L₂ ∈ cComp H) (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ∧ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ≤ pCoreOf 2 H :=
  commutator_le_pCoreOf_inf_of_le h₁ h₂
    (commutator_le_pCoreOf_of_ne
      (h37 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH)) h₁ h₂ hne)

theorem lemma_1_2_1_four (hK : LocalSQTK G) (h36 : A36ForSQTKCat) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) : A36ConclusionCat (modO2Image H L) :=
  (h36 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH) _ (modO2Image_mem_cComp hL)).1

theorem lemma_1_2_1_four_core (hK : LocalSQTK G) (h36 : A36CoreForSQTKCat) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) : A36CoreCat (modO2Image H L) :=
  h36 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH) _ (modO2Image_mem_cComp hL)

theorem lemma_1_2_1_four_strong (hK : LocalSQTK G) (h36 : A36ForSQTKCat) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) : A36StrongCat (modO2Image H L) :=
  h36 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH) _ (modO2Image_mem_cComp hL)

theorem lemma_1_2_4_exists (hK : LocalSQTK G) (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat)
    {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) : ∃ L ∈ cComp H, B ≤ L :=
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH
  exists_cComp_ge_of_subgroup hS hBH hB (h37 _ hQ) (h39 _ hQ)

theorem lemma_1_2_4_unique (hK : LocalSQTK G) (h37 : A37ForSQTKCat) {H S B L₁ L₂ : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hB : B ∈ lFamily S) (h₁ : L₁ ∈ cComp H) (h₂ : L₂ ∈ cComp H)
    (hB₁ : B ≤ L₁) (hB₂ : B ≤ L₂) : L₁ = L₂ :=
  CFSG.Quasithin.lemma_1_2_4_unique (h37 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH)) hB h₁ h₂
    hB₁ hB₂

theorem lemma_1_2_4_existsUnique (hK : LocalSQTK G) (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat)
    {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) : ∃! L, L ∈ cComp H ∧ B ≤ L := by
  obtain ⟨L, hL, hBL⟩ := lemma_1_2_4_exists hK h37 h39 hH hS hBH hB
  exact ⟨L, ⟨hL, hBL⟩, fun L' hL' => lemma_1_2_4_unique hK h37 hH hB hL'.1 hL hL'.2 hBL⟩

theorem normal_conjClosure_of_pCoreOf_ne_bot (hK : LocalSQTK G) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) {H T L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hT : IsSylowTwoOf T H)
    (hL : L ∈ cComp H) : H ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH
  normal_conjClosure_of_subgroup hT hL (h37 _ hQ) (h38 _ hQ)

end Ambient

end CFSG.QuasithinUnique.Vol2Native
