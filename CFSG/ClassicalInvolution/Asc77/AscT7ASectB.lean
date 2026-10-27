module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASectA
public import CFSG.ClassicalInvolution.Asc77.AscT7ATwin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic AscE184Sect

section Quot

variable {Y : Type} [Group Y] [Finite Y] {p f : ℕ} [Fact p.Prime] {Λ : Set (Subgroup Y)}
  {N : Subgroup Y} [N.Normal]

theorem map_ne_of_commutes_sylow (hp : p ≠ 2) (hΛ' : HypOmegaMod p f (quotFamily Λ N))
    (hN : Odd (Nat.card N)) {M₁ M₂ V₁ V₂ : Subgroup Y} (hM₁ : M₁ ∈ Λ)
    (hV₁ : IsSylow2In V₁ M₁) (hV₂ : IsSylow2In V₂ M₂) (hc : Commutes V₁ V₂) :
    M₁.map (QuotientGroup.mk' N) ≠ M₂.map (QuotientGroup.mk' N) := by
  intro heq
  set mk := QuotientGroup.mk' N with hmk
  have h1 : IsSylow2In (V₁.map mk) (M₁.map mk) := isSylow2In_map_mk hN hV₁
  have h2 : IsSylow2In (V₂.map mk) (M₁.map mk) := heq ▸ isSylow2In_map_mk hN hV₂
  have hc' : Commutes (V₁.map mk) (V₂.map mk) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have hP : IsPGroup 2 ↥(V₁.map mk ⊔ V₂.map mk) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes hc'.symm)
  have hsup : V₁.map mk ⊔ V₂.map mk ≤ M₁.map mk := sup_le h1.1 h2.1
  have hle : V₂.map mk ≤ V₁.map mk := by
    have := h1.eq_of_le hP hsup le_sup_left
    rw [← this]
    exact le_sup_right
  have heqV : V₁.map mk = V₂.map mk := h2.eq_of_le h1.2.1 h1.1 hle
  have hRset : V₁.map mk ∈ RSet (quotFamily Λ N) :=
    mem_RSet_of_isSylow2In (map_mem_quotFamily hM₁) h1
  obtain ⟨x, hx, y, hy, hxy⟩ := (hΛ'.isQuatSub_of_mem_RSet hp hRset).exists_not_commute
  exact hxy (hc' x hx y (heqV ▸ hy))

theorem twinTriple_quot (hp : p ≠ 2) (hΛ' : HypOmegaMod p f (quotFamily Λ N))
    (hN : Odd (Nat.card N)) {K K' J R R' T : Subgroup Y} (hK : K ∈ Λ) (hK' : K' ∈ twinSet Λ K)
    (hJ : J ∈ Λ) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K') (hT : IsSylow2In T J)
    (hRR' : Commutes R R') (hRT : Commutes R T) (hR'T : Commutes R' T)
    (hTK : T ≤ Subgroup.normalizer (K : Set Y)) (hTK' : T ≤ Subgroup.normalizer (K' : Set Y)) :
    TwinTriple (quotFamily Λ N) := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨hK'Λ, z, hzK, hzK'⟩ := hK'
  have hKK' : K'.map mk ≠ K.map mk :=
    map_ne_of_commutes_sylow hp hΛ' hN hK'Λ hR' hR hRR'.symm
  have hJK : J.map mk ≠ K.map mk := map_ne_of_commutes_sylow hp hΛ' hN hJ hT hR hRT.symm
  have hJK' : J.map mk ≠ K'.map mk := map_ne_of_commutes_sylow hp hΛ' hN hJ hT hR' hR'T.symm
  have hTset : T.map mk ∈ RSet (quotFamily Λ N) :=
    mem_RSet_of_isSylow2In (map_mem_quotFamily hJ) (isSylow2In_map_mk hN hT)
  refine ⟨K.map mk, map_mem_quotFamily hK, K'.map mk,
    ⟨map_mem_quotFamily hK'Λ, mk z, isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hzK,
      isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K') hzK'⟩, hKK',
    J.map mk, ⟨map_mem_quotFamily hJ, hJK, T.map mk, hTset, Subgroup.map_mono hT.1, ?_⟩,
    ⟨map_mem_quotFamily hJ, hJK', T.map mk, hTset, Subgroup.map_mono hT.1, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_map (hTK hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_map (hTK' hx)

end Quot

section Sub

variable {G : Type} [Group G] {Y : Subgroup G}

theorem commutes_subgroupOf {A B : Subgroup G} (h : Commutes A B) :
    Commutes (A.subgroupOf Y) (B.subgroupOf Y) := by
  intro x hx y hy
  exact Subtype.ext (h x hx y hy)

theorem le_normalizer_subgroupOf_of_le {K T : Subgroup G} (hKY : K ≤ Y)
    (h : T ≤ Subgroup.normalizer (K : Set G)) :
    T.subgroupOf Y ≤ Subgroup.normalizer ((K.subgroupOf Y : Subgroup Y) : Set Y) :=
  fun _ hx => (mem_normalizer_subgroupOf_iff hKY).mp (h hx)

end Sub

section Core

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem oddCoreOf_sectionHull_le (hΩ : HypOmegaMod p f Ω) (A : Subgroup G) :
    oddCoreOf (sectionHull Ω A) ≤ oddCoreOf (Subgroup.centralizer (A : Set G)) := by
  set Y := sectionHull Ω A with hY
  set C := Subgroup.centralizer (A : Set G) with hC
  have hYC : Y ≤ C := sectionHull_le_centralizer Ω A
  have hCN : ∀ g ∈ C, conjSub g Y = Y := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp (le_normalizer_sectionHull hΩ hg)
  have hPC : oddCoreOf Y ≤ C := (oddCoreOf_le_self Y).trans hYC
  have hinv : ∀ g ∈ C, conjSub g (oddCoreOf Y) = oddCoreOf Y := fun g hg => by
    rw [← oddCoreOf_conjSub, hCN g hg]
  have hnorm : ((oddCoreOf Y).subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 : (g : G) * x * (g : G)⁻¹ ∈ conjSub (g : G) (oddCoreOf Y) := conj_mem_conjSub hx
    rwa [hinv g g.2] at h1
  have hodd : Odd (Nat.card ↥((oddCoreOf Y).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv]
    have h1 : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥Y
    have h2 : Nat.card ↥(oddCoreOf Y) = Nat.card (classicalInvolutionOddCore ↥Y) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).symm.toEquiv
    rw [h2]
    exact h1
  have hle : (oddCoreOf Y).subgroupOf C ≤ classicalInvolutionOddCore ↥C :=
    le_sSup ⟨hnorm, hodd⟩
  intro x hx
  refine ⟨⟨x, hPC hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end Core

end CFSG.ClassicalInvolution.Asc77
