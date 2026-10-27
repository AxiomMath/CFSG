module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscE184SecE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic AscE184Sect CFSG.ClassicalInvolution.Disconnected

namespace T7P

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} {A : Subgroup G}

omit [Fact p.Prime] in
theorem dAdj_map {Y : Subgroup G} {K' J' : Subgroup Y}
    (h : dAdj (restrictFamily Ω Y) K' J') : dAdj Ω (K'.map Y.subtype) (J'.map Y.subtype) := by
  rcases h with h | h
  · exact Or.inl (omegaNbr_map h)
  · exact Or.inr (omegaNbr_map h)

variable [Finite G]

theorem dAdj_of_sectionFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {K J : Subgroup G} (hK : K ∈ sectionMembers Ω A)
    (hJ : J ∈ sectionMembers Ω A)
    (h : dAdj (sectionFamily Ω A) (secMember A K) (secMember A J)) : dAdj Ω K J := by
  rcases h with h1 | h1
  · exact Or.inl (mem_omegaNbr_of_sectionFamily hp hq hΩ hA hK hJ h1)
  · exact Or.inr (mem_omegaNbr_of_sectionFamily hp hq hΩ hA hJ hK h1)

@[expose] def sectionGoodD (Ω : Set (Subgroup G)) (A K : Subgroup G)
    (L : Subgroup ↥(sectionHull Ω A)) : Prop :=
  ∃ J ∈ sectionMembers Ω A, L = (secMember A J).subgroupOf (sectionHull Ω A) ∧
    J ∈ dComp Ω K

theorem sectionGoodD_step (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {K : Subgroup G} {L L' : Subgroup ↥(sectionHull Ω A)}
    (hL' : L' ∈ restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
    (hgood : sectionGoodD Ω A K L)
    (hadj : dAdj (restrictFamily (sectionFamily Ω A) (sectionHull Ω A)) L L') :
    sectionGoodD Ω A K L' := by
  obtain ⟨J, hJ, rfl, hJK⟩ := hgood
  obtain ⟨J', hJ', rfl⟩ := exists_of_mem_restrict_sectionFamily hL'
  have h1 := dAdj_map hadj
  rw [Subgroup.map_subgroupOf_eq_of_le (le_sectionHull hJ),
    Subgroup.map_subgroupOf_eq_of_le (le_sectionHull hJ')] at h1
  exact ⟨J', hJ', rfl, hJK.tail ⟨hJ'.1, dAdj_of_sectionFamily hp hq hΩ hA hJ hJ' h1⟩⟩

section Lift

variable {N : Subgroup G} [N.Normal]

omit [Fact p.Prime] [Finite G] in
theorem exists_good_lift_D (good : Subgroup G → Prop) {K : Subgroup G} (hK : K ∈ Ω) (hgK : good K)
    (hstep : ∀ L ∈ Ω, ∀ L' ∈ Ω, good L →
      dAdj (quotFamily Ω N) (L.map (QuotientGroup.mk' N)) (L'.map (QuotientGroup.mk' N)) →
      ∃ L'' ∈ Ω, L''.map (QuotientGroup.mk' N) = L'.map (QuotientGroup.mk' N) ∧ good L'')
    {Mb : Subgroup (G ⧸ N)}
    (hMb : Mb ∈ dComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ Ω, M.map (QuotientGroup.mk' N) = Mb ∧ good M := by
  induction hMb with
  | refl => exact ⟨K, hK, rfl, hgK⟩
  | tail _ hbc ih =>
    obtain ⟨M, hM, hMb, hgood⟩ := ih
    obtain ⟨L', hL', hL'eq⟩ := hbc.1
    have hL'eq' : L'.map (QuotientGroup.mk' N) = _ := hL'eq
    subst hMb hL'eq'
    obtain ⟨M'', hM'', hM''eq, hgood''⟩ := hstep M hM L' hL' hgood hbc.2
    exact ⟨M'', hM'', hM''eq, hgood''⟩

end Lift

theorem exists_conj_mem_dComp_of_dconn (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A) {B : Subgroup G}
    (hB : B ∈ sectionMembers Ω A)
    (hconn : ∀ L ∈ quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        (classicalInvolutionOddCore ↥(sectionHull Ω A)),
      ∀ M ∈ quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        (classicalInvolutionOddCore ↥(sectionHull Ω A)),
      M ∈ dComp (quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        (classicalInvolutionOddCore ↥(sectionHull Ω A))) L)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ sectionMembers Ω A) :
    ∃ n ∈ classicalInvolutionOddCore ↥(sectionHull Ω A), ∃ J ∈ sectionMembers Ω A,
      J ∈ dComp Ω B ∧ J₁ = conjSub (n : G) J := by
  set Y := sectionHull Ω A with hYdef
  set Λ : Set (Subgroup ↥Y) := restrictFamily (sectionFamily Ω A) Y with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f Λ := hypOmegaMod_sectionFamily hp hq hΩ hA
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq ↥Y Λ hΛ N₀ hN₀odd
  have hBΛ : (secMember A B).subgroupOf Y ∈ Λ := subgroupOf_secMember_mem hB
  have hJ₁Λ : (secMember A J₁).subgroupOf Y ∈ Λ := subgroupOf_secMember_mem hJ₁
  obtain ⟨M, hM', hMeq, hMgood⟩ := exists_good_lift_D (N := N₀) (sectionGoodD Ω A B) hBΛ
    ⟨B, hB, rfl, Relation.ReflTransGen.refl⟩
    (fun L hL L' hL' hgL hadj => by
      rcases hadj with hadj | hadj
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaNbr hp hq hΛ hΛ' hN₀odd hL hL' hadj
        have h1 := omegaNbr_conj hΛ.conjInvariant hn' (n⁻¹ : ↥Y)
        rw [conjSub_inv_conjSub] at h1
        have hnn : QuotientGroup.mk' N₀ n⁻¹ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (N₀.inv_mem hn)
        refine ⟨conjSub n⁻¹ L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact sectionGoodD_step hp hq hΩ hA (hΛ.conjInvariant _ L' hL') hgL (Or.inl h1)
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaNbr hp hq hΛ hΛ' hN₀odd hL' hL hadj
        have hnn : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
        refine ⟨conjSub n L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact sectionGoodD_step hp hq hΩ hA (hΛ.conjInvariant _ L' hL') hgL (Or.inr hn'))
    (hconn _ (map_mem_quotFamily hBΛ) _ (map_mem_quotFamily hJ₁Λ))
  obtain ⟨n, hn, hJ₁n⟩ := exists_conj_of_map_eq hp hq hΛ hN₀odd hM' hJ₁Λ hMeq
  obtain ⟨J, hJ, rfl, hJB⟩ := hMgood
  refine ⟨n, hn, J, hJ, hJB, ?_⟩
  have hnC : (n : G) ∈ Subgroup.centralizer (A : Set G) := sectionHull_le_centralizer Ω A n.2
  have h1 : (secMember A J₁).subgroupOf Y =
      (secMember A (conjSub (n : G) J)).subgroupOf Y := by
    rw [hJ₁n, ← conjSub_secMember hnC]
    exact conjSub_subgroupOf Y n (secMember A J)
  have h2 : secMember A J₁ = secMember A (conjSub (n : G) J) := by
    have hle1 : secMember A J₁ ≤ Y := le_sectionHull hJ₁
    have hle2 : secMember A (conjSub (n : G) J) ≤ Y :=
      le_sectionHull (conjSub_mem_sectionMembers hΩ hnC hJ)
    have := congrArg (Subgroup.map Y.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hle1, Subgroup.map_subgroupOf_eq_of_le hle2] at this
  exact eq_of_secMember_eq hp hΩ hA hJ₁ (conjSub_mem_sectionMembers hΩ hnC hJ) h2

end T7P

end CFSG.ClassicalInvolution.Asc77
