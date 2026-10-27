module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Steps

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

section Contexts

variable {G : Type} [Group G] [Finite G]

structure L41GCtx (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends Ctx0 t L S x₁ x₂ lam rho where
  eq_PL : invCent t = twoCore t ⊔ L

structure L41GPh1 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GCtx t L S x₁ x₂ lam rho where
  basic : L41Basic t S x₁ x₂ lam rho

structure L41GPh2 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh1 t L S x₁ x₂ lam rho where
  sylow : Lemma4_2Concl S

structure L41GPh3 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh2 t L S x₁ x₂ lam rho where
  fusion : L41Fusion t S x₁ x₂ lam

structure L41GPh4 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh3 t L S x₁ x₂ lam rho where
  normalizerFacts : L41Normalizer t S x₁ x₂ lam rho

structure L41GPh5 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh4 t L S x₁ x₂ lam rho where
  p2 : Lemma4_3Concl t

structure L41GPh6 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh5 t L S x₁ x₂ lam rho where
  e8 : L41E8Fact t S x₁ x₂

structure L41GPh7 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh6 t L S x₁ x₂ lam rho where
  nbar : L41NbarFacts t x₁ x₂ rho

structure L41GPh8 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh7 t L S x₁ x₂ lam rho where
  rfacts : L41RFacts t S x₁ x₂ lam rho

structure L41GPh9 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh8 t L S x₁ x₂ lam rho where
  hs29 : L41HS29Fact t x₁ x₂ lam rho

structure L41GPh10 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh9 t L S x₁ x₂ lam rho where
  rab : IsMulCommutative (l41R t x₁ x₂ rho)

structure L41GPh11 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh10 t L S x₁ x₂ lam rho where
  yfacts : L41YFacts t S x₁ x₂ lam rho

structure L41GPh12 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh11 t L S x₁ x₂ lam rho where
  uniqueY : L41UniqueYFact t S x₁ x₂ rho

structure L41GPh13 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh12 t L S x₁ x₂ lam rho where
  mbasic : L41MBasic t x₁ x₂ lam rho

structure L41GPh14 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh13 t L S x₁ x₂ lam rho where
  qfacts : L41QFacts t x₁ x₂ lam rho

structure L41GPh15 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh14 t L S x₁ x₂ lam rho where
  q1facts : L41Q1Facts t x₁ x₂ lam rho

structure L41GPh16 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh15 t L S x₁ x₂ lam rho where
  centQ1 : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
    l41Q1 t x₁ x₂ rho

structure L41GPh17 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop
    extends L41GPh16 t L S x₁ x₂ lam rho where
  q1elem : ∀ q ∈ l41Q1 t x₁ x₂ rho, q * q ∈ l41Y t x₁ x₂ rho

end Contexts

section Facts

variable {G : Type} [Group G]

structure L41Normalizer0 (t : G) (S : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  normal_F2 : NormalIn (fourGrp x₁ x₂) (l41N t x₁ x₂)
  quot_N : Sec4SectionIso (l41N t x₁ x₂) (ctxW t x₁ x₂) (Equiv.Perm (Fin 4))
  orbit_t : conjIn (l41N t x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G)
  O2_eq : l41O2 t x₁ x₂ = l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  card_O2 : Nat.card (l41O2 t x₁ x₂) = 4 * Nat.card (ctxW t x₁ x₂)
  N_eq : l41N t x₁ x₂ = l41O2 t x₁ x₂ ⊔ closure {rho, lam}
  V_le : l41V S t x₁ x₂ ≤ l41N t x₁ x₂
  V_pGroup : IsPGroup 2 (l41V S t x₁ x₂)
  V_sylow : ¬ 2 ∣ (l41V S t x₁ x₂).relIndex (l41N t x₁ x₂)
  card_V : Nat.card (l41V S t x₁ x₂) = 8 * Nat.card (ctxW t x₁ x₂)
  cent_V_t : l41V S t x₁ x₂ ⊓ invCent t = S
  cent_V_A : l41V S t x₁ x₂ ⊓ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  quot_V : Sec4SectionIso (l41V S t x₁ x₂) (ctxW t x₁ x₂) (DihedralGroup 4)

end Facts

section Conversions

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem L41Ctx.toG (h : L41Ctx t L S x₁ x₂ lam rho) : L41GCtx t L S x₁ x₂ lam rho :=
  ⟨h.toCtx0, h.eq_PL⟩

theorem L41Ph1.toG (h : L41Ph1 t L S x₁ x₂ lam rho) : L41GPh1 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ctx.toG, h.basic⟩
theorem L41Ph2.toG (h : L41Ph2 t L S x₁ x₂ lam rho) : L41GPh2 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph1.toG, h.sylow⟩
theorem L41Ph3.toG (h : L41Ph3 t L S x₁ x₂ lam rho) : L41GPh3 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph2.toG, h.fusion⟩
theorem L41Ph4.toG (h : L41Ph4 t L S x₁ x₂ lam rho) : L41GPh4 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph3.toG, h.normalizerFacts⟩
theorem L41Ph5.toG (h : L41Ph5 t L S x₁ x₂ lam rho) : L41GPh5 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph4.toG, h.p2⟩
theorem L41Ph6.toG (h : L41Ph6 t L S x₁ x₂ lam rho) : L41GPh6 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph5.toG, h.e8⟩
theorem L41Ph7.toG (h : L41Ph7 t L S x₁ x₂ lam rho) : L41GPh7 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph6.toG, h.nbar⟩
theorem L41Ph8.toG (h : L41Ph8 t L S x₁ x₂ lam rho) : L41GPh8 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph7.toG, h.rfacts⟩
theorem L41Ph9.toG (h : L41Ph9 t L S x₁ x₂ lam rho) : L41GPh9 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph8.toG, h.hs29⟩
theorem L41Ph10.toG (h : L41Ph10 t L S x₁ x₂ lam rho) : L41GPh10 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph9.toG, h.rab⟩
theorem L41Ph11.toG (h : L41Ph11 t L S x₁ x₂ lam rho) : L41GPh11 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph10.toG, h.yfacts⟩
theorem L41Ph12.toG (h : L41Ph12 t L S x₁ x₂ lam rho) : L41GPh12 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph11.toG, h.uniqueY⟩
theorem L41Ph13.toG (h : L41Ph13 t L S x₁ x₂ lam rho) : L41GPh13 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph12.toG, h.mbasic⟩
theorem L41Ph14.toG (h : L41Ph14 t L S x₁ x₂ lam rho) : L41GPh14 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph13.toG, h.qfacts⟩
theorem L41Ph15.toG (h : L41Ph15 t L S x₁ x₂ lam rho) : L41GPh15 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph14.toG, h.q1facts⟩
theorem L41Ph16.toG (h : L41Ph16 t L S x₁ x₂ lam rho) : L41GPh16 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph15.toG, h.centQ1⟩
theorem L41Ph17.toG (h : L41Ph17 t L S x₁ x₂ lam rho) : L41GPh17 t L S x₁ x₂ lam rho :=
  ⟨h.toL41Ph16.toG, h.q1elem⟩

end Conversions

end CFSG.OddStandard.SmallF3.HarrisU33
