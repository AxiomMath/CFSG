module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourThree

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourFacts

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem elemModulo_of_le_yamadaB (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3)
    {P : Subgroup G} (hPB : P ≤ yamadaB d) (hP : IsPGroup 2 P)
    (hXP : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ P) : ElemModulo (yamadaU₁ d t) P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := yamadaB d)).exists_le_sylow
  set V := (Q : Subgroup (yamadaB d)).map (yamadaB d).subtype with hV
  have hPV : P ≤ V := fun x hx => ⟨⟨x, hPB hx⟩, hQ hx, rfl⟩
  have hVsyl : IsSylowOf 2 V (yamadaB d) := ⟨Q, rfl⟩
  obtain ⟨-, hE⟩ := h.yamada_5_10_4 d hK hK4 hcat hVsyl (hXP.trans hPV)
  intro x hx y hy
  exact hE x (hPV hx) y (hPV hy)

theorem doublingFacts_four (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    h.DoublingFacts d := by
  have hpkg : ∀ V : Subgroup G, IsSylowOf 2 V (yamadaB d) →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V → QFourSylowPackage d V :=
    fun _ hV hXV => h.qFourSylowPackage_of_cat d hK hK4 hcat hV hXV
  obtain ⟨hU₁X, hUU₁, hU₁D, -⟩ := h.yamadaU₁_spec_four d hK hK4 hpkg
  obtain ⟨hD₁, hinf, hcard⟩ := h.yamada_5_10_1_four d hK hK4 hcat
  have helem := h.yamada_5_10_2_four d hK hK4 hcat
  obtain ⟨hZ, hF₁⟩ := h.yamada_5_10_3_four d hK hK4 hcat
  have hU₁eq := yamadaU₁_eq_four d t hK4
  refine ⟨hU₁X.trans inf_le_left, hUU₁, hU₁D, hD₁, hinf, hcard,
    fun hx hy => congrArg Subtype.val (helem.1.1.1 ⟨_, hx⟩ ⟨_, hy⟩), hZ, hF₁,
    hU₁X.trans inf_le_right, ?_, Or.inr ⟨hK4, helem,
      h.yamadaD₁_inf_centralizer_J₁_le_yamadaB d hK hK4,
      fun P hPB hP hXP => h.elemModulo_of_le_yamadaB d hK hK4 hcat hPB hP hXP⟩⟩
  rw [d.S_inf_centralizer_J₁_four hK4]
  intro c hc
  have hcX : c ∈ yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) := by
    rw [← yamadaD₁_inf_centralizer_J₁_inf_D d hK4] at hc
    exact (Subgroup.mem_inf.1 hc).1
  refine mem_centralizer_iff.2 fun u hu => ?_
  rw [hU₁eq] at hu
  exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu).2 c hcX).symm

end QFourFacts

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
