module

public import CFSG.ClassicalInvolution.Asc77.AscIHWitness

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Witness

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem pairNormalizers_le_sup (K J : Subgroup G) (zK zJ : G) :
    pairNormalizers K J zK zJ ≤ K ⊔ J :=
  sup_le_sup inf_le_left inf_le_left

theorem not_aEmpty_of_u2Witness' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hnc : ¬ ∃ g ∈ K ⊔ J, conjSub g K = J)
    (hW : U2Witness K J) : ¬ AEmpty Ω K := by
  intro hA
  have hne : J ≠ K := fun h => hnc ⟨1, Subgroup.one_mem _, by rw [conjSub_one, h]⟩
  have hstar : J ∈ omegaStarNbr Ω K := by
    obtain ⟨P, U, hUP, hcyc, hidx, hUN⟩ := hW.1
    refine ⟨hJ, hne, U.map J.subtype, ?_, Subgroup.map_subtype_le U, hUN⟩
    refine ⟨(P : Subgroup ↥J).map J.subtype, ⟨J, hJ, P, rfl⟩, Subgroup.map_mono hUP, ?_, ?_⟩
    · exact (MulEquiv.isCyclic (U.equivMapOfInjective J.subtype J.subtype_injective)).mp hcyc
    · rw [Subgroup.relIndex_map_map_of_injective _ _ J.subtype_injective]
      exact hidx
  have hnot : J ∉ omegaNbr Ω K := by
    rintro ⟨-, -, R₀, ⟨J'', hJ'', P'', rfl⟩, hR₀J, hR₀N⟩
    set R₀ : Subgroup G := (P'' : Subgroup ↥J'').map J''.subtype with hR₀
    have hcard : Nat.card J'' = Nat.card J := (natCard_member hΩ hJ'').trans
      (natCard_member hΩ hJ).symm
    have hP''card : Nat.card P'' = 2 ^ (Nat.card J).factorization 2 := by
      rw [Sylow.card_eq_multiplicity, hcard]
    have hR₀2 : IsPGroup 2 R₀ := P''.isPGroup'.map _
    have hQ₀2 : IsPGroup 2 (R₀.subgroupOf J) := hR₀2.comap_subtype
    have hQ₀card : Nat.card (R₀.subgroupOf J) = Nat.card P'' := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀J).toEquiv]
      exact (Nat.card_congr
        ((P'' : Subgroup ↥J'').equivMapOfInjective J''.subtype J''.subtype_injective).toEquiv).symm
    obtain ⟨Q, hQ₀⟩ := hQ₀2.exists_le_sylow
    have hQcard : Nat.card Q = 2 ^ (Nat.card J).factorization 2 := Sylow.card_eq_multiplicity Q
    have hQ₀eq : R₀.subgroupOf J = (Q : Subgroup ↥J) :=
      Subgroup.eq_of_le_of_card_ge hQ₀ (by rw [hQcard, hQ₀card, hP''card])
    refine hW.2 Q ?_
    rw [← hQ₀eq, Subgroup.map_subgroupOf_eq_of_le hR₀J]
    exact hR₀N
  obtain ⟨zK, hzK⟩ := hΩ.classical K hK
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJ
  obtain ⟨g, hgm, hg⟩ := hA J hstar hnot zK zJ
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzK)
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzJ)
  exact hnc ⟨g, pairNormalizers_le_sup K J zK zJ hgm, hg⟩

theorem not_aEmpty_of_centralizer_witness' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hnc : ¬ ∃ g ∈ K ⊔ J, conjSub g K = J) {z : G}
    (hz : IsUniqueInvolution K z) (P : Sylow 2 ↥J) (u : ↥J) (huP : u ∈ (P : Subgroup ↥J))
    (hidx : (Subgroup.zpowers u).relIndex (P : Subgroup ↥J) = 2) (hnoncen : ∃ w : ↥J, u * w ≠ w * u)
    (huz : (u : G) * z = z * (u : G))
    (hb : ∀ P' : Sylow 2 ↥J, ∃ x ∈ (P' : Subgroup ↥J), (x : G) * z ≠ z * (x : G)) :
    ¬ AEmpty Ω K := by
  have hKJ : K ≠ J := fun h => hnc ⟨1, Subgroup.one_mem _, by rw [conjSub_one, h]⟩
  have hu2 : IsPGroup 2 (Subgroup.zpowers (u : G)) := by
    have h1 : IsPGroup 2 ((P : Subgroup ↥J).map J.subtype) := P.isPGroup'.map _
    refine h1.to_le ?_
    rw [Subgroup.zpowers_le]
    exact ⟨u, huP, rfl⟩
  obtain ⟨w, hw⟩ := hnoncen
  have hun : (u : G) ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK J hJ hKJ z hz (u : G) u.2 (fun h => hw (Subtype.ext (h w w.2))) hu2 huz
  refine not_aEmpty_of_u2Witness' hp2 hq hΩ hK hJ hnc
    ⟨⟨P, Subgroup.zpowers u, ?_, ?_, hidx, ?_⟩, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact huP
  · infer_instance
  · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hun
  · intro P' hP'
    obtain ⟨x, hxP', hx⟩ := hb P'
    have h1 : (x : G) ∈ Subgroup.normalizer (K : Set G) := hP' ⟨x, hxP', rfl⟩
    have h2 := hz.conj_eq (conjSub_eq_of_mem_normalizer h1)
    apply hx
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2

end Witness

end CFSG.ClassicalInvolution.Asc77
