module

public import CFSG.GH74.Generic.BProg.Neighbourhood
public import CFSG.GH74.Generic.S1.NbrCompQ3
public import CFSG.GH74.Generic.BProg.Helpers

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S1 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

@[expose] def DictS1High : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K → S1LargeModel K →
      ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu →
        S1SymFrame x u → ∀ c ∈ symJ (symX x u) 3, orderOf c = 2 →
          (∀ a ∈ symJ (symX x u) 3, a * c = c * a) →
            NbhdData G x c (symJ (symX x u) 0 ⊔ symJ (symX x u) 1)

@[expose] def DictS1Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K →
      ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu →
        ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 → S1SymFrameLin x u F →
          S1FrameOddFree x u → ∀ c ∈ symJ3 (symX x u) 3, orderOf c = 2 →
            (∀ a ∈ symJ3 (symX x u) 3, a * c = c * a) →
              NbhdData G x c (symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1)

@[expose] def DictS1Q3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K →
      ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu →
        ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 → S1SymFrameLin x u F →
          ∀ Fr : Q3FrameB G F, Fr.X = symX x u →
            NbhdData G x (Fr.X 2 * Fr.X 3) Fr.Ablk

theorem s1Setup_hyp2 {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hthin : ¬ GLS.HasTwoThinConfiguration G) : Hyp2 G :=
  ⟨hset.simple, hset.nonab, hset.rank, hset.gen4, hset.kgh, hset.sylow,
    ⟨x, hset.inv, K, hset.comp, hset.jmax.1.2.2⟩, hthin⟩

theorem b_S1_nbrCompHigh_of_program (hA : Stage2Allow) (hD : DictS1High) : B_S1_nbrCompHigh := by
  intro G _ _ x K hset hmax hthin hfront hbig u hu hf hsym c hcJ hc2 hcc hbar
  exact isSubnormal_of_barSub_of_comm hbar
    (comm_of_nbhdData hA (s1Setup_hyp2 hset hthin)
      (hD G x K hset hmax hthin hfront hbig u hu hf hsym c hcJ hc2 hcc))

theorem b_S1_nbrComp3_of_program (hA : Stage2Allow) (hD : DictS1Three) : B_S1_nbrComp3 := by
  intro G _ _ x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc hbar
  exact isSubnormal_of_barSub_of_comm hbar
    (comm_of_nbhdData hA (s1Setup_hyp2 hset hthin)
      (hD G x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc))

theorem b_S1_nbrQ3_of_program (hA : Stage2Allow) (hD : DictS1Q3) : B_S1_nbrQ3 := by
  intro G _ _ x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin Fr hFr _
  exact comm_of_nbhdData hA (s1Setup_hyp2 hset hthin) (hD G x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin Fr hFr)

theorem b_S1_nbrComp_of_program (hA : Stage2Allow) (hD1 : DictS1High) (hD3 : DictS1Three)
    (hDq : DictS1Q3) : B_S1_nbrComp :=
  ⟨b_S1_nbrCompHigh_of_program hA hD1, b_S1_nbrComp3_of_program hA hD3,
    b_S1_nbrQ3_of_program hA hDq⟩

end CFSG.GH74.Generic.BProg
