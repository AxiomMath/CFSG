module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

structure Setup710 (B T I : Subgroup G) : Prop where
  bElem : IsElemAbelian 3 B
  card_b : Nat.card ↥B = 81
  tTwo : IsPGroup 2 ↥T
  bnT : B ≤ Subgroup.normalizer (T : Set G)
  tMax : ∀ T' : Subgroup G, IsPGroup 2 ↥T' → B ≤ Subgroup.normalizer (T' : Set G) → T ≤ T' →
    T' = T
  cB : ∀ b ∈ B, (∀ t ∈ T, b * t = t * b) → b = 1
  bnI : B ≤ Subgroup.normalizer (I : Set G)
  tnI : T ≤ Subgroup.normalizer (I : Set G)
  perf : ⁅I, I⁆ = I
  gen3 : Subgroup.closure {x : G | x ∈ I ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} = I
  lthree : IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I)
  ord3 : ∀ R : Subgroup G, R ≤ I → IsPGroup 3 ↥R → Nat.card ↥R ≤ 9
  card_bI : Nat.card ↥(B ⊓ I) = 9
  c18 : ∀ Q : Subgroup G, Q ≤ ⁅I, GLAPPrimeCoreOf 3 I⁆ → IsPGroup 2 ↥Q →
    ¬ 2 ∣ Q.relIndex ⁅I, GLAPPrimeCoreOf 3 I⁆ →
      I ⊓ Subgroup.centralizer (Q : Set G) ≤ GLAPPrimeCoreOf 3 I

@[expose] def yOf (B T I : Subgroup G) : Subgroup G := I ⊔ T ⊔ B

@[expose] def pOf (B T I : Subgroup G) : Subgroup G := GLAPPrimeCoreOf 3 (yOf B T I)

@[expose] def sOf (B T I : Subgroup G) : Subgroup G := T ⊓ pOf B T I

@[expose] def wOf (B T I : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (sOf B T I : Set G) ⊓ yOf B T I

@[expose] def zOf (B T I : Subgroup G) : Subgroup G :=
  GLAPPrimeCoreOf 2 (yOf B T I ⊓ Subgroup.centralizer (sOf B T I : Set G))

omit [Finite G] in
theorem zOf_le_wOf (B T I : Subgroup G) : zOf B T I ≤ wOf B T I := by
  refine (Subgroup.map_subtype_le _).trans (le_inf ?_ inf_le_left)
  exact inf_le_right.trans (Subgroup.centralizer_le_normalizer (sOf B T I : Set G))

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro g hg
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ y ∈ Subgroup.centralizer (S : Set G),
      g * y * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) s).1 hs
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 hy _ h1
    calc s * (g * y * g⁻¹) = g * ((g⁻¹ * s * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * s * g)) * g⁻¹ := by rw [h2]
      _ = g * y * g⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem wOf_le_normalizer_zOf (B T I : Subgroup G) :
    wOf B T I ≤ Subgroup.normalizer (zOf B T I : Set G) :=
  le_normalizer_glaPPrimeCoreOf_of_le' fun _ hg =>
    Sec7.inf_normalizer_le_normalizer_inf _ _
      ⟨Subgroup.le_normalizer hg.2, normalizer_le_normalizer_centralizer _ hg.1⟩

instance zOf_subgroupOf_normal (B T I : Subgroup G) : ((zOf B T I).subgroupOf (wOf B T I)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (zOf_le_wOf B T I)).2 (wOf_le_normalizer_zOf B T I)

abbrev XQ (B T I : Subgroup G) : Type := ↥(wOf B T I) ⧸ (zOf B T I).subgroupOf (wOf B T I)

noncomputable abbrev piQ (B T I : Subgroup G) : ↥(wOf B T I) →* XQ B T I :=
  QuotientGroup.mk' ((zOf B T I).subgroupOf (wOf B T I))

structure YFacts (B T I : Subgroup G) : Prop where
  sylow : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)
  cent : yOf B T I ⊓ Subgroup.centralizer (sOf B T I : Set G) ≤ pOf B T I

noncomputable abbrev bX (B T I : Subgroup G) : Subgroup (XQ B T I) :=
  (B.subgroupOf (wOf B T I)).map (piQ B T I)

noncomputable abbrev tX (B T I : Subgroup G) : Subgroup (XQ B T I) :=
  (T.subgroupOf (wOf B T I)).map (piQ B T I)

noncomputable abbrev preQ (B T I : Subgroup G) (N₁ : Subgroup (XQ B T I)) : Subgroup G :=
  (N₁.comap (piQ B T I)).map (wOf B T I).subtype

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
