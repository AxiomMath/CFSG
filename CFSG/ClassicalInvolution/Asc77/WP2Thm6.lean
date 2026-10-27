module

public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

structure Std6 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G) : Prop where
  stand : AscStand p f Ω K
  edgeless : DEdgeless Ω
  hz : IsUniqueInvolution K z
  hR : R ∈ RSet Ω
  hRK : R ≤ K
  hRS : R ≤ (S : Subgroup G)
  cex : ¬ ConcOrTF4 G

@[expose] def C19_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → DEdgeless Ω → ∀ W ∈ WSet Ω, MuIsoZ2 Ω W ∨ MuIsoS3 Ω W

@[expose] def C19_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6 p f Ω K S R z →
      ∀ W ∈ WSet Ω, W ≤ (S : Subgroup G) → MuIsoZ2 Ω W → ConcOrTF4 G

@[expose] def gammaGen {G : Type} [Group G] (Ω : Set (Subgroup G)) (z : G) : Subgroup G :=
  ⨆ A ∈ {A : Subgroup G | (A ∈ USet Ω ∨ A ∈ RSet Ω) ∧ A ≤ Subgroup.centralizer ({z} : Set G)}, A

@[expose] def C19_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6 p f Ω K S R z →
      ∀ W ∈ WSet Ω, W ≤ (S : Subgroup G) →
        ∀ L ∈ Ω, ∀ t : G, IsUniqueInvolution L t → t ≠ z →
          ∀ V ∈ USet Ω, V ≤ (S : Subgroup G) → t ∈ V →
            (∃ (n : ℕ) (φ : ↥(gammaGen Ω z) →* DihedralGroup n), Function.Surjective φ ∧
                2 * n = Nat.card ↥R ∧
                ∀ x : ↥(gammaGen Ω z), φ x = 1 ↔ (x : G) ∈ centralizerModOdd (gammaGen Ω z) K) ∨
            (∃ (p' e : ℕ) (_ : Fact p'.Prime), p' ≠ 2 ∧ 0 < e ∧
              ∃ φ : ↥(gammaGen Ω z) →* Matrix.ProjGenLinGroup (Fin 2)
                  (GaloisField p' e),
                Function.Surjective φ ∧
                  ∀ x : ↥(gammaGen Ω z), φ x = 1 ↔ (x : G) ∈ centralizerModOdd (gammaGen Ω z) K)

@[expose] def C19_main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6 p f Ω K S R z →
      ∀ W ∈ WSet Ω, W ≤ (S : Subgroup G) → MuIsoS3 Ω W → ConcOrTF4 G

variable {p f}

@[expose] def W69 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → ∀ S : Sylow 2 G, ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G)

theorem exists_std6 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    (hs : AscStand p f Ω K) (he : DEdgeless Ω) (hc : ¬ ConcOrTF4 G) :
    ∃ (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6 p f Ω K S R z := by
  obtain ⟨z, hz⟩ := hs.hyp.classical K hs.mem
  have hU := ConnectedA2.isUniqueInvolution_of_isClassicalMember hs.odd hs.five hz
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  set R : Subgroup G := Subgroup.map K.subtype (P : Subgroup ↥K) with hR
  have hRp : IsPGroup 2 R := P.isPGroup'.map K.subtype
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  exact ⟨S, R, z, ⟨hs, he, hU, ⟨K, hs.mem, P, rfl⟩, Subgroup.map_subtype_le _, hRS, hc⟩⟩

theorem thm6A_of_steps (hW : W69 p f) (h2 : C19_2 p f) (h4 : C19_4 p f) (hmain : C19_main p f) :
    Thm6A p f := by
  intro G _ _ _ Ω K hs he
  by_cases hc : ConcOrTF4 G
  · exact hc
  obtain ⟨S, R, z, hstd⟩ := exists_std6 hs he hc
  obtain ⟨W, hWmem, hWS⟩ := hW G Ω K hs S
  rcases h2 G Ω K hs he W hWmem with hZ | hS3
  · exact h4 G Ω K S R z hstd W hWmem hWS hZ
  · exact hmain G Ω K S R z hstd W hWmem hWS hS3

end CFSG.ClassicalInvolution.Asc77
