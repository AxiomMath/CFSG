module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuTab

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem c231_nonempty (hP : Q3CL.PartIHypG Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hW : W ∈ WSet Ω) : (muDelta Ω W).Nonempty := by
  obtain ⟨-, ρ, -⟩ := Q3T6.Mu.exists_rep hP hW hK
  exact ⟨muTabElt ρ, muTabElt_mem ρ⟩

theorem c231_sylow_frame (hP : Q3CL.PartIHypG Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (R R' : Subgroup G), W ≤ (S : Subgroup G) ∧ IsSylow2In R K ∧
      IsSylow2In R' K' ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hP.hyp hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ K) K :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hP.cls.isSubnormal_of_uniqueInvolution hK hz)
  have hR' : IsSylow2In (T ⊓ K') K' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hP.cls.isSubnormal_of_uniqueInvolution hK' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  exact ⟨S, T ⊓ K, T ⊓ K', hWT.trans hTS, hR, hR', inf_le_left.trans hTS,
    inf_le_left.trans hTS⟩

theorem c231_ncard_cent_le_two (hP : Q3CL.PartIHypG Ω) {K K' : Subgroup G}
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hperp : KPerp Ω K = {K, K'})
    (hW : W ∈ WSet Ω) {d : ↥(muGroup Ω W)} (hd : d ∈ muDelta Ω W) :
    (Star3T.cent (muDelta Ω W) d).ncard ≤ 2 := by
  obtain ⟨ρ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
  obtain ⟨g, hg⟩ := htrans ρ.K ρ.hK
  have hsub : omegaNbr Ω ρ.K ⊆ {conjSub g K'} := by
    intro J hJ
    have h1 : conjSub g⁻¹ J ∈ omegaNbr Ω K := by
      have := omegaNbr_conj hP.hyp.conjInvariant hJ g⁻¹
      rwa [← hg, conjSub_inv_conjSub] at this
    have h2 : conjSub g⁻¹ J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h1
    rw [hperp] at h2
    rcases h2 with h2 | h2
    · exact absurd h2 h1.2.1
    · have h3 : conjSub g⁻¹ J = K' := h2
      rw [Set.mem_singleton_iff, ← h3, conjSub_conjSub_inv]
  have hn : (omegaNbr Ω ρ.K).ncard ≤ 1 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_singleton _).le
  have := Q3T6.Mu.ncard_cent_le hP hW ρ hn
  omega

theorem c231_exists_cent_ne (hP : Q3CL.PartIHypG Ω) {K K' : Subgroup G} {z : G}
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hperp : KPerp Ω K = {K, K'}) (hW : W ∈ WSet Ω)
    {d : ↥(muGroup Ω W)} (hd : d ∈ muDelta Ω W) :
    ∃ x ∈ muDelta Ω W, x ≠ d ∧ x * d = d * x := by
  have hΩ : HypOmegaGen Ω := hP.hyp
  obtain ⟨ρ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
  obtain ⟨g, hg⟩ := htrans ρ.K ρ.hK
  obtain ⟨hK'Ω, z', hzK, hzK'⟩ := hK'
  have hzz : z' = z := (hz.eq hzK).symm
  rw [hzz] at hzK'
  have hz₁ : IsUniqueInvolution ρ.K (g * z * g⁻¹) := by
    rw [← hg]
    exact hz.conj g
  have hzW : g * z * g⁻¹ ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW ρ.hK ρ.hR ρ.hRK hz₁).2
  have hK₁' : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  obtain ⟨S, R₁, R₁', hWS, hR₁, hR₁', hR₁S, hR₁'S⟩ :=
    c231_sylow_frame hP ρ.hK hK₁' hz₁ (hzK'.conj g) hW hzW
  have hR₁'D : R₁' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK₁' hR₁') hR₁'S
  obtain ⟨ρ', hρ'K⟩ : ∃ ρ' : Rep Ω W, ρ'.K = conjSub g K' :=
    ⟨Q3CL.T8.mkRep hP hW hK₁' hR₁'D hR₁', rfl⟩
  have hnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hK'n : K' ∈ omegaNbr Ω K := by
      have h1 : K' ∈ KPerp Ω K := by
        rw [hperp]
        exact Or.inr rfl
      rcases h1 with h1 | h1
      · exact absurd h1 hne
      · exact h1
    have := omegaNbr_conj hΩ.conjInvariant hK'n g
    rw [hg] at this
    rw [hρ'K]
    exact this
  have hne' : ρ'.K ≠ ρ.K := hnbr.2.1
  refine ⟨muTabElt ρ', muTabElt_mem ρ', fun h => hne' ?_, ?_⟩
  · exact (Q3T6.Mu.muTabElt_eq_iff hP hW ρ' ρ).mp h
  · exact ((Q3T6.Mu.muTab_commute_iff hP hW ρ ρ' (Ne.symm hne')).mpr hnbr).symm

theorem c231_clique (hP : Q3CL.PartIHypG Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hperp : KPerp Ω K = {K, K'}) (hW : W ∈ WSet Ω) :
    (muDelta Ω W).Nonempty ∧
      ∀ d ∈ muDelta Ω W, (Star3T.cent (muDelta Ω W) d).ncard = 2 := by
  refine ⟨c231_nonempty hP hK hW, fun d hd => ?_⟩
  have hle := c231_ncard_cent_le_two hP htrans hperp hW hd
  obtain ⟨x, hx, hxd, hcomm⟩ := c231_exists_cent_ne hP htrans hz hK' hne hperp hW hd
  have hsub : ({d, x} : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) d := by
    rintro y (rfl | rfl)
    · exact Star3T.self_mem_cent hd
    · exact ⟨hx, hcomm⟩
  have hge : 2 ≤ (Star3T.cent (muDelta Ω W) d).ncard := by
    calc 2 = ({d, x} : Set ↥(muGroup Ω W)).ncard := (Set.ncard_pair hxd.symm).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end CFSG.ClassicalInvolution.Q3.Q3T7
