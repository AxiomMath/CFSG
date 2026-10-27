module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

section Transport

variable {K L : Type} [Group K] [Finite K] [Group L] [Finite L]

theorem sylow_comm_of_mulEquiv {p : ℕ} [Fact p.Prime] (e : K ≃* L)
    (h : ∀ S : Sylow p L, IsMulCommutative (S : Subgroup L)) :
    ∀ S : Sylow p K, IsMulCommutative (S : Subgroup K) := by
  intro S
  have hcard : Nat.card (S.map e.toMonoidHom) = p ^ (Nat.card L).factorization p := by
    rw [Subgroup.card_map_of_injective e.injective, S.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  let P' : Sylow p L := Sylow.ofCard (S.map e.toMonoidHom) hcard
  have hP' : (P' : Subgroup L) = (S : Subgroup K).map e.toMonoidHom := Sylow.coe_ofCard _ _
  have := h P'
  rw [hP'] at this
  exact (isMulCommutative_map_iff_of_injective _ e.injective _).1 this

theorem CentralFusionAt.of_mulEquiv (e : K ≃* L) (h : CentralFusionAt L) :
    CentralFusionAt K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨by rw [Nat.card_congr (equivalence e).toEquiv]; exact h.1, ?_⟩
  intro T A hAT hAc hA
  have hconj : ∀ (g : L) (x : K), e ((MulAut.conj (e.symm g)) x) = (MulAut.conj g) (e x) := by
    intro g x
    simp [MulAut.conj_apply]
  set T' : Sylow 3 L := T.mapSurjective (f := e.toMonoidHom) e.surjective with hT'def
  have hT' : (T' : Subgroup L) = (T : Subgroup K).map e.toMonoidHom := rfl
  obtain ⟨g, hgN, hgA⟩ := h.2 T' (A.map e.toMonoidHom)
    (by rw [hT']; exact Subgroup.map_mono hAT)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ht
      rw [hT'] at ht
      obtain ⟨t, ht, rfl⟩ := ht
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hAc a ha t ht])
    (by rw [Subgroup.card_map_of_injective e.injective, hA])
  refine ⟨e.symm g, ?_, fun heq => hgA ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx := (Subgroup.mem_normalizer_iff.1 hgN) (e x)
    rw [hT'] at hx
    have h1 : e x ∈ (T : Subgroup K).map e.toMonoidHom ↔ x ∈ (T : Subgroup K) :=
      Subgroup.mem_map_iff_mem e.injective
    have h2 : g * e x * g⁻¹ = e (e.symm g * x * (e.symm g)⁻¹) := by simp
    have h3 : e (e.symm g * x * (e.symm g)⁻¹) ∈ (T : Subgroup K).map e.toMonoidHom ↔
        e.symm g * x * (e.symm g)⁻¹ ∈ (T : Subgroup K) :=
      Subgroup.mem_map_iff_mem e.injective
    rw [h1, h2, h3] at hx
    exact hx
  · ext y
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have : (MulAut.conj (e.symm g)).toMonoidHom a ∈ A := heq ▸ ⟨a, ha, rfl⟩
      refine ⟨_, this, ?_⟩
      exact hconj g a
    · rintro ⟨a, ha, rfl⟩
      have ha' : a ∈ A.map (MulAut.conj (e.symm g)).toMonoidHom := heq.symm ▸ ha
      obtain ⟨b, hb, rfl⟩ := ha'
      exact ⟨e b, ⟨b, hb, rfl⟩, (hconj g b).symm⟩

theorem OmegaDichAt.of_mulEquiv (e : K ≃* L) (h : OmegaDichAt L) : OmegaDichAt K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with h | h | h | h
  · exact Or.inl (sylow_comm_of_mulEquiv e h)
  · exact Or.inr (Or.inl (h.map e.symm.toMonoidHom e.symm.injective))
  · refine Or.inr (Or.inr (Or.inl ?_))
    have := pRank_map_mulEquiv (p := 3) e (⊤ : Subgroup K)
    rw [Subgroup.map_top_of_surjective _ e.surjective] at this
    omega
  · exact Or.inr (Or.inr (Or.inr (CentralFusionAt.of_mulEquiv e h)))

theorem HeisDichAt.of_mulEquiv (e : K ≃* L) (h : HeisDichAt L) : HeisDichAt K := by
  rcases h with h | h
  · exact Or.inl (SylowDichotomyAt.of_mulEquiv Nat.prime_three e h)
  · exact Or.inr (CentralFusionAt.of_mulEquiv e h)

theorem DichThreeAt.of_mulEquiv (e : K ≃* L) (h : DichThreeAt L) : DichThreeAt K :=
  ⟨OmegaDichAt.of_mulEquiv e h.1, HeisDichAt.of_mulEquiv e h.2⟩

end Transport

@[expose] def DichThreeAlt : Prop :=
  ∀ n : ℕ, 5 ≤ n → DichThreeAt (alternatingGroup (Fin n))

@[expose] def DichThreeLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f →
      CFSG.Blueprint.LieModel K t n ℓ f → 3 ∣ Nat.card K → DichThreeAt K

@[expose] def HeisDichThreeLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f →
      CFSG.Blueprint.LieModel K t n ℓ f → 3 ∣ Nat.card K → HeisDichAt K

@[expose] def DichThreeSpor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    CFSG.Blueprint.NativeSporadic.SporadicRep K → 3 ∣ Nat.card K → DichThreeAt K

section Dispatch


theorem dichThree_of_cases (hAlt : DichThreeAlt) (hLie : DichThreeLie)
    (hSpor : DichThreeSpor) : DichThree := by
  intro K _ _ hs hnab hcat h3
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact DichThreeAt.of_mulEquiv e (hAlt n hn5)
  · exact hLie K hs hnab t n ℓ f hadm hmodel h3
  · exact hSpor K hs hnab hspor h3

theorem heisDichThree_of_cases (hAlt : DichThreeAlt) (hLie : HeisDichThreeLie)
    (hSpor : DichThreeSpor) : HeisDichThree := by
  intro K _ _ hs hnab hcat h3
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact HeisDichAt.of_mulEquiv e (hAlt n hn5).2
  · exact hLie K hs hnab t n ℓ f hadm hmodel h3
  · exact (hSpor K hs hnab hspor h3).2

end Dispatch

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
