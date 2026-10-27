module

public import CFSG.ClassicalInvolution.Phan.PhanG5Rank3
public import CFSG.ClassicalInvolution.Phan.Main

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G}

@[expose] def NullOnPhan (S : PhanFamilyD4 K p f G) (J : Set (Fin 4)) : Prop :=
  ∀ (x : G ⧸ torusSub S) (γ : List (Fin 4 × G ⧸ torusSub S)),
    (phanSystem S).IsGallery x γ → (∀ j ∈ galleryType γ, j ∈ J) → galleryEnd x γ = x →
      (phanSystem S).TwoHomotopic x γ []

theorem exists_chain_of_family (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hg : GoodFamily S) {e : Fin 3 → Fin 4} (he : Function.Injective e)
    (F : PhanFamily K p f G 3) (hι : ∀ j, F.ι j = S.ι (e j)) :
    ∃ ψ : Su K p f 4 →* G, PhanChain S e ψ := by
  obtain ⟨ψ, hψ, -⟩ := phanUniversal K p f hK hq (n := 3) le_rfl F
  have hcomp : ∀ j, ψ.comp (blockEmb2 K p f 3 j) = S.ι (e j) := fun j => (hψ j).trans (hι j)
  have happ : ∀ j A, ψ (blockEmb2 K p f 3 j A) = S.ι (e j) A := fun j A =>
    DFunLike.congr_fun (hcomp j) A
  refine ⟨ψ, he, fun j A => ?_, fun j r hr => ?_, fun j => ?_, fun j => ?_⟩
  · rw [happ]
    exact ⟨A, rfl⟩
  · obtain ⟨A, rfl⟩ := hr
    exact ⟨A, happ j A⟩
  · rw [hcomp]
    exact hg.inj (e j)
  · rw [hcomp]
    rfl

theorem exists_chain_012 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S) :
    ∃ ψ : Su K p f 4 →* G, PhanChain S ![0, 1, 2] ψ := by
  refine exists_chain_of_family hK hq hg (by decide)
    ⟨![S.ι 0, S.ι 1, S.ι 2], ![S.θ 0, S.θ 1, 1], ?_, ?_, ?_⟩ ?_
  · intro i hi
    fin_cases i
    · exact S.left 0
    · exact S.left 1
    · exact absurd hi (by decide)
  · intro i hi
    fin_cases i
    · exact S.right 0
    · exact S.right 1
    · exact absurd hi (by decide)
  · intro i j hij a b
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact S.comm 0 2 (by decide) (by decide) (by decide) a b
  · intro j
    fin_cases j <;> rfl

theorem exists_chain_013 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S) :
    ∃ ψ : Su K p f 4 →* G, PhanChain S ![0, 1, 3] ψ := by
  refine exists_chain_of_family hK hq hg (by decide)
    ⟨![S.ι 0, S.ι 1, S.ι 3], ![S.θ 0, S.θ 2, 1], ?_, ?_, ?_⟩ ?_
  · intro i hi
    fin_cases i
    · exact S.left 0
    · exact S.left 2
    · exact absurd hi (by decide)
  · intro i hi
    fin_cases i
    · exact S.right 0
    · exact S.right 2
    · exact absurd hi (by decide)
  · intro i j hij a b
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact S.comm 0 3 (by decide) (by decide) (by decide) a b
  · intro j
    fin_cases j <;> rfl

theorem nullOn_012 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S)
    (h2 : (2 : K) ≠ 0) : NullOnPhan S {0, 1, 2} := by
  obtain ⟨ψ, hch⟩ := exists_chain_012 hK hq hg
  intro x γ hγ hJ hend
  refine hch.twoHomotopic_nil hK (by omega) hg h2 x γ hγ (fun j hj => ?_) hend
  have := hJ j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

theorem nullOn_013 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S)
    (h2 : (2 : K) ≠ 0) : NullOnPhan S {0, 1, 3} := by
  obtain ⟨ψ, hch⟩ := exists_chain_013 hK hq hg
  intro x γ hγ hJ hend
  refine hch.twoHomotopic_nil hK (by omega) hg h2 x γ hγ (fun j hj => ?_) hend
  have := hJ j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

end CFSG.ClassicalInvolution.PhanG
