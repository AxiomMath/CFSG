module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmE

namespace CentEng

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem isSylow2In_map_cent (c : CentQuotGen Ω N) {J V : Subgroup G} (hJ : J ∈ Ω)
    (hV : IsSylow2In V J) :
    IsSylow2In (V.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N)) := by
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := J.map (QuotientGroup.mk' N))
    (IsPGroup.of_bot) bot_le
  have hcard : Nat.card V = Nat.card V₀ := by
    rw [natCard_eq_pow_of_isSylow2In hV, natCard_eq_pow_of_isSylow2In hV₀, c.natCard_map hJ]
  have hVN : V ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hV.1).trans (c.meet J hJ).le)
  have hmapcard : Nat.card ↥(V.map (QuotientGroup.mk' N)) = Nat.card V :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv).symm
  exact hV₀.of_natCard_le (hV.2.1.map _) (Subgroup.map_mono hV.1) (by rw [hmapcard, hcard])

theorem dstarAdj_of_map (c : CentQuotGen Ω N) {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω)
    (h : dstarAdj (quotFamily Ω N) (L.map (QuotientGroup.mk' N))
      (L'.map (QuotientGroup.mk' N))) : dstarAdj Ω L L' := by
  rcases h.2 with h1 | h1
  · exact ⟨hL', Or.inl (c.omegaStarNbr_of_map hL hL' h1)⟩
  · exact ⟨hL', Or.inr (c.omegaStarNbr_of_map hL' hL h1)⟩

theorem exists_lift_dstarComp (c : CentQuotGen Ω N) {K : Subgroup G} (hK : K ∈ Ω) {Mb : Subgroup (G ⧸ N)}
    (hMb : Mb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ dstarComp Ω K, M.map (QuotientGroup.mk' N) = Mb := by
  obtain ⟨M, -, hMeq, hgood⟩ := exists_good_lift (N := N) (fun L : Subgroup G => L ∈ dstarComp Ω K)
    hK Relation.ReflTransGen.refl
    (fun L hL L' hL' hgood hadj => ⟨L', hL', rfl, hgood.tail (dstarAdj_of_map c hL hL' hadj)⟩) hMb
  exact ⟨M, hgood, hMeq⟩

theorem exists_lift_kperp_cent (c : CentQuotGen Ω N) {L : Subgroup G} (hL : L ∈ Ω)
    {Jb : Subgroup (G ⧸ N)}
    (hJb : Jb ∈ KPerp (quotFamily Ω N) (L.map (QuotientGroup.mk' N))) :
    ∃ J ∈ KPerp Ω L, J.map (QuotientGroup.mk' N) = Jb := by
  rcases hJb with rfl | hJbn
  · exact ⟨L, Set.mem_insert _ _, rfl⟩
  · obtain ⟨J₀, hJ₀, rfl⟩ := hJbn.1
    exact ⟨J₀, Set.mem_insert_of_mem _ (c.omegaNbr_of_map hL hJ₀ hJbn), rfl⟩

theorem exists_lift_sylow_pair_cent (hN2 : IsPGroup 2 ↥N) (c : CentQuotGen Ω N) {L J : Subgroup G}
    (hL : L ∈ Ω) (hJ : J ∈ KPerp Ω L) {Rb₁ Rb₂ : Subgroup (G ⧸ N)}
    (hRb₁ : Rb₁ ∈ RSet (quotFamily Ω N)) (hRb₁L : Rb₁ ≤ L.map (QuotientGroup.mk' N))
    (hRb₂ : Rb₂ ∈ RSet (quotFamily Ω N)) (hRb₂J : Rb₂ ≤ J.map (QuotientGroup.mk' N))
    (hc : Commutes Rb₁ Rb₂ ∨ Rb₂ = Rb₁) :
    ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ L ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ J ∧
      R₁.map (QuotientGroup.mk' N) = Rb₁ ∧ R₂.map (QuotientGroup.mk' N) = Rb₂ ∧
      (Commutes R₁ R₂ ∨ R₂ = R₁) := by
  have hJΩ : J ∈ Ω := by
    rcases hJ with rfl | hJn
    · exact hL
    · exact hJn.1
  obtain ⟨R₁, hR₁, hR₁L, hR₁map⟩ := c.exists_lift_RSet hL hRb₁ hRb₁L
  rcases hc with hcomm | heq
  · obtain ⟨R₂, hR₂, hR₂J, hR₂map⟩ := c.exists_lift_RSet hJΩ hRb₂ hRb₂J
    refine ⟨R₁, R₂, hR₁, hR₁L, hR₂, hR₂J, hR₁map, hR₂map, ?_⟩
    by_cases hR₁₂ : R₂ = R₁
    · exact Or.inr hR₁₂
    refine Or.inl ?_
    have hR₁₂' : IsPGroup 2 ↥(R₁ ⊔ R₂) := by
      refine AscE186.isPGroup_of_map_isPGroup hN2 ?_
      rw [Subgroup.map_sup, hR₁map, hR₂map]
      have hb₁ : IsPGroup 2 ↥Rb₁ := by
        rw [← hR₁map]
        exact (AscE186.isPGroup_of_mem_RSet hR₁).map _
      have hb₂ : IsPGroup 2 ↥Rb₂ := by
        rw [← hR₂map]
        exact (AscE186.isPGroup_of_mem_RSet hR₂).map _
      exact hb₁.to_sup_of_normal_right' hb₂ fun x hx =>
        mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hx hcomm)
    obtain ⟨S, hS⟩ := hR₁₂'.exists_le_sylow
    exact Q3CP.l67Gen G Ω c.hyp S R₁ hR₁ R₂ hR₂ (le_sup_left.trans hS)
      (le_sup_right.trans hS) (Ne.symm hR₁₂)
  · have hJL : J = L := by
      by_contra hne
      have hJn : J ∈ omegaNbr Ω L := hJ.resolve_left hne
      have hLJ : L.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N) :=
        fun h => hne (c.eq_of_map L hL J hJΩ h).symm
      have h2 := Sec6Gen.card_le_two_of_le_inf c.hyp' (map_mem_quotFamily hL) (map_mem_quotFamily hJΩ) hLJ
        (AscE186.isPGroup_of_mem_RSet hRb₁) hRb₁L (heq ▸ hRb₂J)
      have h8 := Sec6Gen.eight_le_of_mem_RSet c.hyp' hRb₁
      omega
    subst hJL
    exact ⟨R₁, R₁, hR₁, hR₁L, hR₁, hR₁L, hR₁map, heq.symm ▸ hR₁map, Or.inr rfl⟩

end CentEng

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
