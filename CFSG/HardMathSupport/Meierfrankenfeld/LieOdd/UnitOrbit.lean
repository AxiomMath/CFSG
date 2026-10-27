module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitCount
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem exists_hom_of_index_eq_prime {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
    (D : AddSubgroup A) (hD : D.index = p) : ∃ l : A →+ ZMod p, ∀ x, l x = 0 ↔ x ∈ D := by
  have hQ : Nat.card (A ⧸ D) = p := hD
  have hcyc : IsAddCyclic (A ⧸ D) := isAddCyclic_of_prime_card hQ
  let e : ZMod (Nat.card (A ⧸ D)) ≃+ (A ⧸ D) := zmodAddCyclicAddEquiv hcyc
  refine ⟨((ZMod.ringEquivCongr hQ).toAddEquiv.toAddMonoidHom).comp
    (e.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' D)), fun x => ?_⟩
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    map_eq_zero_iff _ (EmbeddingLike.injective _), QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]

section Conj

variable {G : Type*} [Group G] [Finite G]

theorem card_image_conj_le_relIndex (T D₀ : Subgroup G) (s : Finset G) (hs : ∀ t ∈ s, t ∈ T)
    [DecidableEq (Subgroup G)] :
    (s.image fun t => conjSub t D₀).card ≤
      (T ⊓ Subgroup.normalizer (D₀ : Set G)).relIndex T := by
  classical
  let H' : Subgroup ↥T := (T ⊓ Subgroup.normalizer (D₀ : Set G)).subgroupOf T
  have hcongr : ∀ a b : ↥T, QuotientGroup.leftRel H' a b →
      conjSub (a : G) D₀ = conjSub (b : G) D₀ := by
    intro a b hab
    have hmem : (a : G)⁻¹ * b ∈ Subgroup.normalizer (D₀ : Set G) := by
      have := (QuotientGroup.leftRel_apply.1 hab)
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).2
    ext x
    rw [mem_conjSub, mem_conjSub]
    have hninv := Subgroup.mem_set_normalizer_iff.1
      ((Subgroup.normalizer (D₀ : Set G)).inv_mem hmem)
    have key := hninv ((a : G)⁻¹ * x * a)
    rw [inv_inv] at key
    have e : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * x * a) * ((a : G)⁻¹ * b) = (b : G)⁻¹ * x * b := by
      group
    rw [e] at key
    exact key
  let F : (↥T ⧸ H') → Subgroup G := Quotient.lift (fun t : ↥T => conjSub (t : G) D₀) hcongr
  have hsub : ((s.image fun t => conjSub t D₀ : Finset (Subgroup G)) : Set (Subgroup G)) ⊆
      Set.range F := by
    intro c hc
    obtain ⟨t, hts, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    exact ⟨QuotientGroup.mk ⟨t, hs t hts⟩, rfl⟩
  calc (s.image fun t => conjSub t D₀).card
      = Nat.card ((s.image fun t => conjSub t D₀ : Finset (Subgroup G)) : Set (Subgroup G)) := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ ≤ Nat.card (Set.range F) := Nat.card_mono (Set.finite_range F) hsub
    _ ≤ Nat.card (↥T ⧸ H') := Finite.card_range_le F
    _ = (T ⊓ Subgroup.normalizer (D₀ : Set G)).relIndex T := by
        rw [Subgroup.relIndex, Subgroup.index_eq_card]

end Conj

section Param

open scoped Classical

theorem mem_toSubgroup_symm {A : Type*} [AddGroup A] (C : Subgroup (Multiplicative A)) (z : A) :
    z ∈ AddSubgroup.toSubgroup.symm C ↔ Multiplicative.ofAdd z ∈ C := by
  have := Multiplicative.mem_toSubgroup (AddSubgroup.toSubgroup.symm C) (Multiplicative.ofAdd z)
  rw [OrderIso.apply_symm_apply, toAdd_ofAdd] at this
  exact this.symm

variable {F : Type} [Field F] [Fintype F] {ε : ℕ} {p : ℕ} [Fact p.Prime]
  {S : Type} [Group S] [Finite S]

theorem horb_of_param (ψ : Multiplicative (UP F ε) →* S) (t : (Fin ε → F) → Fˣ → S)
    (ht : ∀ d μ x, t d μ * ψ x * (t d μ)⁻¹ =
      ψ (Multiplicative.ofAdd (utau d (μ : F) (Multiplicative.toAdd x))))
    {D₀ : Subgroup S} (hrel : D₀.relIndex ψ.range = p)
    (hZ : ¬ ((ψ.comp (AddMonoidHom.inr (Fin ε → F) F).toMultiplicative).range ≤ D₀)) :
    Nat.card F ^ ε * (Nat.card F - 1) ≤ 2 * (p - 1) *
      (Subgroup.normalizer (ψ.range : Set S) ⊓ Subgroup.normalizer (D₀ : Set S)).relIndex
        (Subgroup.normalizer (ψ.range : Set S)) := by
  have hT : ∀ d μ, t d μ ∈ Subgroup.normalizer (ψ.range : Set S) := by
    intro d μ
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (ht d μ x).symm⟩
    · rintro ⟨x', hx'⟩
      obtain ⟨z, hz⟩ := utau_surjective d μ.ne_zero (Multiplicative.toAdd x')
      refine ⟨Multiplicative.ofAdd z, ?_⟩
      have h1 : t d μ * ψ (Multiplicative.ofAdd z) * (t d μ)⁻¹ = ψ x' := by
        rw [ht, toAdd_ofAdd, hz, ofAdd_toAdd]
      have h2 : t d μ * ψ (Multiplicative.ofAdd z) * (t d μ)⁻¹ = t d μ * y * (t d μ)⁻¹ := by
        rw [h1, hx']
      exact mul_left_cancel (mul_right_cancel h2)
  have hDidx : (D₀.comap ψ).index = p := by
    rw [Subgroup.index_comap]
    exact hrel
  have hDaidx : (AddSubgroup.toSubgroup.symm (D₀.comap ψ)).index = p := by
    rw [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply]
    exact hDidx
  obtain ⟨l, hl⟩ := exists_hom_of_index_eq_prime _ hDaidx
  have hlD : ∀ z : UP F ε, l z = 0 ↔ ψ (Multiplicative.ofAdd z) ∈ D₀ := fun z =>
    (hl z).trans (mem_toSubgroup_symm _ z)
  have hlz : ∃ a, l (0, a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hZ
    rintro _ ⟨y, rfl⟩
    exact (hlD (0, Multiplicative.toAdd y)).1 (hcon _)
  have hker : ∀ x : (Fin ε → F) × Fˣ, kerTau l x =
      AddSubgroup.toSubgroup.symm ((conjSub (t x.1 x.2)⁻¹ D₀).comap ψ) := by
    intro x
    ext z
    rw [kerTau, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hlD, mem_toSubgroup_symm,
      Subgroup.mem_comap, mem_conjSub, inv_inv, ht x.1 x.2 (Multiplicative.ofAdd z), toAdd_ofAdd]
  let s : Finset S := Finset.univ.image (fun x : (Fin ε → F) × Fˣ => (t x.1 x.2)⁻¹)
  have hs : ∀ y ∈ s, y ∈ Subgroup.normalizer (ψ.range : Set S) := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact (Subgroup.normalizer (ψ.range : Set S)).inv_mem (hT _ _)
  have h1 := card_image_conj_le_relIndex (Subgroup.normalizer (ψ.range : Set S)) D₀ s hs
  let G : Subgroup S → AddSubgroup (UP F ε) := fun C => AddSubgroup.toSubgroup.symm (C.comap ψ)
  have hcomp : (Finset.univ.image (kerTau l)) =
      (s.image fun y => conjSub y D₀).image G := by
    simp only [s, Finset.image_image]
    congr 1
    funext x
    exact hker x
  have h2 : (Finset.univ.image (kerTau l)).card ≤ (s.image fun y => conjSub y D₀).card := by
    rw [hcomp]
    exact Finset.card_image_le
  exact (card_params_le_mul_card_image l hlz).trans (Nat.mul_le_mul_left _ (h2.trans h1))

end Param

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
