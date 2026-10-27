module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

section Contexts

variable {G : Type} [Group G] [Finite G]

structure L41Ph1 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ctx t L S x₁ x₂ lam rho where
  basic : L41Basic t S x₁ x₂ lam rho

structure L41Ph2 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph1 t L S x₁ x₂ lam rho where
  sylow : Lemma4_2Concl S

structure L41Ph3 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph2 t L S x₁ x₂ lam rho where
  fusion : L41Fusion t S x₁ x₂ lam

structure L41Ph4 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph3 t L S x₁ x₂ lam rho where
  normalizerFacts : L41Normalizer t S x₁ x₂ lam rho

structure L41Ph5 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph4 t L S x₁ x₂ lam rho where
  p2 : Lemma4_3Concl t

structure L41Ph6 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph5 t L S x₁ x₂ lam rho where
  e8 : L41E8Fact t S x₁ x₂

structure L41Ph7 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph6 t L S x₁ x₂ lam rho where
  nbar : L41NbarFacts t x₁ x₂ rho

structure L41Ph8 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph7 t L S x₁ x₂ lam rho where
  rfacts : L41RFacts t S x₁ x₂ lam rho

structure L41Ph9 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph8 t L S x₁ x₂ lam rho where
  hs29 : L41HS29Fact t x₁ x₂ lam rho

structure L41Ph10 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph9 t L S x₁ x₂ lam rho where
  rab : IsMulCommutative (l41R t x₁ x₂ rho)

structure L41Ph11 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph10 t L S x₁ x₂ lam rho where
  yfacts : L41YFacts t S x₁ x₂ lam rho

structure L41Ph12 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph11 t L S x₁ x₂ lam rho where
  uniqueY : L41UniqueYFact t S x₁ x₂ rho

structure L41Ph13 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph12 t L S x₁ x₂ lam rho where
  mbasic : L41MBasic t x₁ x₂ lam rho

structure L41Ph14 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph13 t L S x₁ x₂ lam rho where
  qfacts : L41QFacts t x₁ x₂ lam rho

structure L41Ph15 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph14 t L S x₁ x₂ lam rho where
  q1facts : L41Q1Facts t x₁ x₂ lam rho

structure L41Ph16 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph15 t L S x₁ x₂ lam rho where
  centQ1 : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
    l41Q1 t x₁ x₂ rho

structure L41Ph17 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41Ph16 t L S x₁ x₂ lam rho where
  q1elem : ∀ q ∈ l41Q1 t x₁ x₂ rho, q * q ∈ l41Y t x₁ x₂ rho

end Contexts

@[expose] def L41BasicStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ctx t L S x₁ x₂ lam rho →
      L41Basic t S x₁ x₂ lam rho

@[expose] def L41SylowStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph1 t L S x₁ x₂ lam rho →
      Lemma4_2Concl S

@[expose] def L41FusionStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph2 t L S x₁ x₂ lam rho →
      L41Fusion t S x₁ x₂ lam

@[expose] def L41NormalizerStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph3 t L S x₁ x₂ lam rho →
      L41Normalizer t S x₁ x₂ lam rho

@[expose] def L41P2Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph4 t L S x₁ x₂ lam rho →
      Lemma4_3Concl t

@[expose] def L41E8Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph5 t L S x₁ x₂ lam rho →
      L41E8Fact t S x₁ x₂

@[expose] def L41NbarStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph6 t L S x₁ x₂ lam rho →
      L41NbarFacts t x₁ x₂ rho

@[expose] def L41RStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph7 t L S x₁ x₂ lam rho →
      L41RFacts t S x₁ x₂ lam rho

@[expose] def L41HS29Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph8 t L S x₁ x₂ lam rho →
      L41HS29Fact t x₁ x₂ lam rho

@[expose] def L41RAbelianStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph9 t L S x₁ x₂ lam rho →
      IsMulCommutative (l41R t x₁ x₂ rho)

@[expose] def L41YStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph10 t L S x₁ x₂ lam rho →
      L41YFacts t S x₁ x₂ lam rho

@[expose] def L41UniqueYStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph11 t L S x₁ x₂ lam rho →
      L41UniqueYFact t S x₁ x₂ rho

@[expose] def L41MBasicStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph12 t L S x₁ x₂ lam rho →
      L41MBasic t x₁ x₂ lam rho

@[expose] def L41QStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph13 t L S x₁ x₂ lam rho →
      L41QFacts t x₁ x₂ lam rho

@[expose] def L41Q1Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph14 t L S x₁ x₂ lam rho →
      L41Q1Facts t x₁ x₂ lam rho

@[expose] def L41CentQ1Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph15 t L S x₁ x₂ lam rho →
      l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
        l41Q1 t x₁ x₂ rho

@[expose] def L41Q1ElemStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph16 t L S x₁ x₂ lam rho →
      ∀ q ∈ l41Q1 t x₁ x₂ rho, q * q ∈ l41Y t x₁ x₂ rho

@[expose] def L41FinalStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    L41Ph17 t L S x₁ x₂ lam rho →
      False

theorem lemma4_1_of_steps
    (s1 : L41BasicStmt) (s2 : L41SylowStmt) (s3 : L41FusionStmt) (s4 : L41NormalizerStmt)
    (s5 : L41P2Stmt) (s6 : L41E8Stmt) (s7 : L41NbarStmt) (s8 : L41RStmt) (s9 : L41HS29Stmt)
    (s10 : L41RAbelianStmt) (s11 : L41YStmt) (s12 : L41UniqueYStmt) (s13 : L41MBasicStmt)
    (s14 : L41QStmt) (s15 : L41Q1Stmt) (s16 : L41CentQ1Stmt) (s17 : L41Q1ElemStmt)
    (s18 : L41FinalStmt)
    : Lemma4_1Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho hI hG h0
  unfold Lemma4_1Concl
  intro hH
  have p0 : L41Ctx t L S x₁ x₂ lam rho := ⟨h0, hH, hG, hI⟩
  have p1 : L41Ph1 t L S x₁ x₂ lam rho := ⟨p0, s1 p0⟩
  have p2 : L41Ph2 t L S x₁ x₂ lam rho := ⟨p1, s2 p1⟩
  have p3 : L41Ph3 t L S x₁ x₂ lam rho := ⟨p2, s3 p2⟩
  have p4 : L41Ph4 t L S x₁ x₂ lam rho := ⟨p3, s4 p3⟩
  have p5 : L41Ph5 t L S x₁ x₂ lam rho := ⟨p4, s5 p4⟩
  have p6 : L41Ph6 t L S x₁ x₂ lam rho := ⟨p5, s6 p5⟩
  have p7 : L41Ph7 t L S x₁ x₂ lam rho := ⟨p6, s7 p6⟩
  have p8 : L41Ph8 t L S x₁ x₂ lam rho := ⟨p7, s8 p7⟩
  have p9 : L41Ph9 t L S x₁ x₂ lam rho := ⟨p8, s9 p8⟩
  have p10 : L41Ph10 t L S x₁ x₂ lam rho := ⟨p9, s10 p9⟩
  have p11 : L41Ph11 t L S x₁ x₂ lam rho := ⟨p10, s11 p10⟩
  have p12 : L41Ph12 t L S x₁ x₂ lam rho := ⟨p11, s12 p11⟩
  have p13 : L41Ph13 t L S x₁ x₂ lam rho := ⟨p12, s13 p12⟩
  have p14 : L41Ph14 t L S x₁ x₂ lam rho := ⟨p13, s14 p13⟩
  have p15 : L41Ph15 t L S x₁ x₂ lam rho := ⟨p14, s15 p14⟩
  have p16 : L41Ph16 t L S x₁ x₂ lam rho := ⟨p15, s16 p15⟩
  have p17 : L41Ph17 t L S x₁ x₂ lam rho := ⟨p16, s17 p16⟩
  exact s18 p17

end CFSG.OddStandard.SmallF3.HarrisU33
