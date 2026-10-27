module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.HyperplaneOrbitStructure
public import CFSG.LocalAnalysis.RankThreeUC.Section5.OddExponentCommutatorImage

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralMovedFixedSubgroup

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary

variable {G : Type} [Group G] [Finite G]

theorem fixed_eq_one {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e)
    (X : Subgroup (MulAut P)) (hXne : X ≠ ⊥)
    (hXT : X ≤ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal))
    (hcent : ∀ ψ ∈ X, ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal), Commute ψ φ)
    (hBX : Bstar P B ≤ Subgroup.normalizer (X : Set (MulAut P))) :
    ∀ q : P, (∀ ψ ∈ X, ψ q = q) → q = 1 := by
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have h51 := hc.oddPrimeClassTwoAction
  let F : Subgroup P :=
    { carrier := {q | ∀ ψ ∈ X, ψ q = q}
      mul_mem' := fun {a b} ha hb ψ hψ => by simp [map_mul, ha ψ hψ, hb ψ hψ]
      one_mem' := fun ψ _ => by simp
      inv_mem' := fun {a} ha ψ hψ => by simp [map_inv, ha ψ hψ] }
  have hF : ∀ q, q ∈ F ↔ ∀ ψ ∈ X, ψ q = q := fun q => Iff.rfl
  have inv : ∀ φ : MulAut P, (∀ ψ ∈ X, ∃ ψ' ∈ X, ψ * φ = φ * ψ') → ∀ q ∈ F, φ q ∈ F := by
    intro φ hφ q hq ψ hψ
    obtain ⟨ψ', hψ', h⟩ := hφ ψ hψ
    have := congrArg (fun f : MulAut P => f q) h
    simp only [MulAut.mul_apply] at this
    rw [this, hq ψ' hψ']
  set P₀ : Subgroup G := F.map P.subtype with hP₀
  have hP₀P : P₀ ≤ P := by
    rintro _ ⟨q, _, rfl⟩; exact q.2
  have hmem : ∀ x : G, x ∈ P₀ ↔ ∃ q : P, q ∈ F ∧ (q : G) = x := fun x => by
    simp [hP₀]
  have hconj : ∀ g : G, (∀ q ∈ F, conjOnP P hP g q ∈ F) → ∀ x ∈ P₀, g * x * g⁻¹ ∈ P₀ := by
    intro g hg x hx
    obtain ⟨q, hq, rfl⟩ := (hmem x).1 hx
    exact (hmem _).2 ⟨conjOnP P hP g q, hg q hq, conjOnP_apply P hP g q⟩
  have hnorm : ∀ K : Subgroup G, (∀ g ∈ K, ∀ q ∈ F, conjOnP P hP g q ∈ F) →
      K ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro K hK g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj g (hK g hg) h
    · intro h2
      have := hconj g⁻¹ (hK g⁻¹ (K.inv_mem hg)) _ h2
      rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  have hXs : twoCoreCommutator T B ≤ Subgroup.normalizer (P₀ : Set G) := by
    refine hnorm _ ?_
    intro g hg q hq
    have hgT : g ∈ T := OddExponentCommutatorImage.xs_le h51 he hg
    refine inv _ (fun ψ hψ => ⟨ψ, hψ, ?_⟩) q hq
    exact (hcent ψ hψ _ ⟨g, hgT, rfl⟩).eq
  have hBn : B ≤ Subgroup.normalizer (P₀ : Set G) := by
    refine hnorm _ ?_
    intro g hg q hq
    refine inv _ (fun ψ hψ => ?_) q hq
    have hβ : conjOnP P hP g ∈ Subgroup.normalizer (X : Set (MulAut P)) :=
      hBX ⟨⟨g, mem_normalizer hP g⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    refine ⟨(conjOnP P hP g)⁻¹ * ψ * conjOnP P hP g, ?_, by group⟩
    refine (Subgroup.mem_normalizer_iff.mp hβ _).mpr ?_
    rwa [show conjOnP P hP g * ((conjOnP P hP g)⁻¹ * ψ * conjOnP P hP g) * (conjOnP P hP g)⁻¹ = ψ
      by group]
  obtain ⟨_, _, _, _, _, _, hirr⟩ := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  intro q hq
  by_contra hq1
  have hne : P₀ ≠ ⊥ := by
    intro h
    have : (q : G) ∈ P₀ := (hmem _).2 ⟨q, hq, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hq1 (Subtype.ext this)
  have hPP : P₀ = P := hirr P₀ hP₀P hXs hBn hne
  apply hXne
  rw [eq_bot_iff]
  intro ψ hψ
  rw [Subgroup.mem_bot]
  ext x
  have : (x : G) ∈ P₀ := by rw [hPP]; exact x.2
  obtain ⟨y, hy, hyx⟩ := (hmem _).1 this
  have : y = x := Subtype.ext hyx
  subst this
  simpa using hy ψ hψ

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralMovedFixedSubgroup
