module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_16FTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K

@[expose] def C19_16FNe9Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f ≠ 9 →
      (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K

@[expose] def C19_16F9Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f = 9 →
      (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K

variable {p f}

theorem c19_16FTmp_of_c19_16STmp (h : C19_16STmp p f) : C19_16FTmp p f :=
  fun G _ _ _ K z S W hd => (h G K z S W hd).trans le_sup_left

theorem c19_16FTmp_of_split (hne : C19_16FNe9Tmp p f) (h9 : C19_16F9Tmp p f) :
    C19_16FTmp p f := by
  intro G _ _ _ K z S W hd
  by_cases hq : p ^ f = 9
  · exact h9 G K z S W hd hq
  · exact hne G K z S W hd hq

end CFSG.ClassicalInvolution.Disconnected.AschTight
