module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Roots

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Steinberg.Adjoint


local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

theorem frameClosing_holds : FrameClosing := by
  intro K _ S hS htop
  have hb : ∀ β ∈ longOrthRoots, ∀ c : K, 𝕩 β c ∈ S ∧ 𝕩 (-β) c ∈ S := fun β hβ c =>
    ⟨hS ⟨β, hβ, c, Or.inl rfl⟩, hS ⟨β, hβ, c, Or.inr rfl⟩⟩
  have nb1 : ∀ c : K, 𝕩 (-rootB1) c ∈ S := fun c => (hb _ (by decide) c).2
  have nb2 : ∀ c : K, 𝕩 (-rootB2) c ∈ S := fun c => (hb _ (by decide) c).2
  have nb3 : ∀ c : K, 𝕩 (-rootB3) c ∈ S := fun c => (hb _ (by decide) c).2
  have h1 : ∀ c : K, 𝕩 rootH1 c ∈ S := fun c => (htop c).1
  have h2 : ∀ c : K, 𝕩 rootH2 c ∈ S := fun c => (htop c).2
  have e0 : ∀ c : K, 𝕩 (Pi.single ⟨0, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 20) (b := 19) (g := 0) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb3 h1
  have e1 : ∀ c : K, 𝕩 (Pi.single ⟨1, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 18) (b := 19) (g := 1) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb2 h1
  have e3 : ∀ c : K, 𝕩 (Pi.single ⟨3, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 17) (b := 19) (g := 3) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb1 h1
  have f0 : ∀ c : K, 𝕩 rootF0 c ∈ S :=
    xPar_mem_of_repCheck (a := 20) (b := 22) (g := 5) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb3 h2
  have f1 : ∀ c : K, 𝕩 rootF1 c ∈ S :=
    xPar_mem_of_repCheck (a := 18) (b := 22) (g := 7) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb2 h2
  have m0 : ∀ c : K, 𝕩 (-Pi.single ⟨0, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 17) (b := 7) (g := 4) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb1 f1
  have m1 : ∀ c : K, 𝕩 (-Pi.single ⟨1, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 17) (b := 5) (g := 6) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb1 f0
  have m3 : ∀ c : K, 𝕩 (-Pi.single ⟨3, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 18) (b := 5) (g := 10) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) nb2 f0
  have e2 : ∀ c : K, 𝕩 (Pi.single ⟨2, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 4) (b := 5) (g := 2) (by decide) (by decide) (by decide)
      (Or.inr rfl) (by decide +kernel) m0 f0
  have mf1 : ∀ c : K, 𝕩 (-rootF1) c ∈ S :=
    xPar_mem_of_repCheck (a := 17) (b := 0) (g := 14) (by decide) (by decide) (by decide)
      (Or.inl rfl) (by decide +kernel) nb1 e0
  have m2 : ∀ c : K, 𝕩 (-Pi.single ⟨2, by decide⟩ 1) c ∈ S :=
    xPar_mem_of_repCheck (a := 1) (b := 14) (g := 8) (by decide) (by decide) (by decide)
      (Or.inl rfl) (by decide +kernel) e1 mf1
  refine CFSG.LieType.SeitzGeneration.ExcWideThree.eq_top_of_simple_mem fun i c => ?_
  fin_cases i
  exacts [⟨e0 c, m0 c⟩, ⟨e1 c, m1 c⟩, ⟨e2 c, m2 c⟩, ⟨e3 c, m3 c⟩]

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen
