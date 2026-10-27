module

public import CFSG.ClassicalInvolution.Asc77.AscE184WY
public import CFSG.ClassicalInvolution.Asc77.AscE184Dich
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscIHThm4
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.le_H_of_mem_dstarComp_of {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {K H J : Subgroup G} (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) (hKH : K ≤ H)
    (hJ : J ∈ dstarComp Ω K) : J ≤ H := by
  obtain ⟨h, hhH, rfl⟩ := htrans J hJ
  intro x hx
  rw [mem_conjSub_iff] at hx
  have := H.mul_mem (H.mul_mem hhH (hKH hx)) (H.inv_mem hhH)
  simpa [mul_assoc] using this

theorem MinCex.le_H_of_mem_dstarComp (c : MinCex p f Ω K S R W H) {J : Subgroup G}
    (hJ : J ∈ dstarComp Ω K) : J ≤ H :=
  E187C.le_H_of_mem_dstarComp_of c.hyp.trans c.le_H hJ

theorem MinCex.layer_le_H (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    (h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    {K' R' : Subgroup G} (hK'tw : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {Y : Subgroup G} (hY : Y ≠ ⊤) (hKY : K ≤ Y)
    (hK'Y : K' ≤ Y) (hgen : Y ≤ ⨆ J ∈ {J | J ∈ Ω ∧ J ≤ Y}, J)
    (hS : IsSylow2In ((S : Subgroup G) ⊓ Y) Y) : Y ≤ H := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hRY : R ≤ Y := hRK.trans hKY
  have hR'Y : R' ≤ Y := hR'K'.trans hK'Y
  have hNH : oddCoreOf Y ≤ H :=
    c.oddCoreOf_le hA hM hK'tw hK'ne hR' hR'K' hR'S (sup_le hRY hR'Y)
  set Λ : Set (Subgroup ↥Y) := restrictFamily Ω Y with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f Λ := hΩ.restrict Y
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq ↥Y Λ hΛ N₀ hN₀odd
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  have hAΛ : ∀ J' ∈ Λ, AEmpty Λ J' := by
    intro J' hJ'
    have hJ : J'.map Y.subtype ∈ Ω := mem_restrictFamily_iff.mp hJ'
    have := AEmpty.restrict hp hΩ (Subgroup.map_subtype_le J') (hAΩ _ hJ)
    rwa [subgroupOf_map_subtype'] at this
  have hAΛ' := aEmpty_quotFamily hp hq hΛ hΛ' hN₀odd hAΛ
  have hltY := natCard_lt_of_ne_top hY
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hKΛ : K.subgroupOf Y ∈ Λ := subgroupOf_mem_restrictFamily hK hKY
  have hN₀H : ∀ n ∈ N₀, (n : G) ∈ H := fun n hn => hNH ⟨n, hn, rfl⟩
  rcases dichotomy_of_thm4 hp hq (thm4Below_of_citBelow c.stand.below) hlt hΛ' hOq hAΛ'
    (map_mem_quotFamily hKΛ) with hconn | horb
  ·
    have hmem : ∀ J' ∈ Λ, J'.map Y.subtype ≤ H := by
      intro J' hJ'
      obtain ⟨M, hM', hMeq, hMgood⟩ := exists_good_lift (N := N₀)
        (fun L : Subgroup ↥Y => L.map Y.subtype ∈ dstarComp Ω K) hKΛ
        (by rw [Subgroup.map_subgroupOf_eq_of_le hKY]; exact Relation.ReflTransGen.refl)
        (fun L hL L' hL' hgood hadj => by
          obtain ⟨-, hadj | hadj⟩ := hadj
          · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr hp hq hΛ hΛ' hN₀odd hL hL' hadj
            have h1 := omegaStarNbr_conj hΛ.conjInvariant hn' (n⁻¹ : ↥Y)
            rw [conjSub_inv_conjSub] at h1
            have hnn : QuotientGroup.mk' N₀ n⁻¹ = 1 :=
              (QuotientGroup.eq_one_iff _).mpr (N₀.inv_mem hn)
            refine ⟨conjSub n⁻¹ L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
            · rw [AscQuot.map_conjSub, hnn, conjSub_one]
            · exact hgood.tail (dstarAdj_map ⟨hΛ.conjInvariant _ L' hL', Or.inl h1⟩)
          · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr hp hq hΛ hΛ' hN₀odd hL' hL hadj
            have hnn : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
            refine ⟨conjSub n L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
            · rw [AscQuot.map_conjSub, hnn, conjSub_one]
            · exact hgood.tail (dstarAdj_map ⟨hΛ.conjInvariant _ L' hL', Or.inr hn'⟩))
        (hconn _ (map_mem_quotFamily hJ'))
      obtain ⟨n, hn, hJ'n⟩ := exists_conj_of_map_eq hp hq hΛ hN₀odd hM' hJ' hMeq
      have hMH : M.map Y.subtype ≤ H := by
        have := c.le_H_of_mem_dstarComp hMgood
        exact this
      rw [hJ'n]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : y ∈ conjSub n M := hy
      rw [mem_conjSub_iff] at hy'
      have hyM : (n⁻¹ * y * n) ∈ M := hy'
      have h1 : (n : G)⁻¹ * (y : G) * (n : G) ∈ H := hMH ⟨_, hyM, rfl⟩
      have h2 : (n : G) * ((n : G)⁻¹ * (y : G) * (n : G)) * (n : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (hN₀H n hn) h1) (H.inv_mem (hN₀H n hn))
      simpa [mul_assoc] using h2
    refine hgen.trans (iSup₂_le fun J hJ => ?_)
    have h1 := hmem (J.subgroupOf Y) (subgroupOf_mem_restrictFamily hJ.1 hJ.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ.2] at h1
  ·
    have hY1 : ∀ J ∈ dstarComp Λ (K.subgroupOf Y), ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = J := by
      intro J hJ
      have hJΛ : J ∈ Λ := by
        by_cases hJK : J = K.subgroupOf Y
        · rw [hJK]; exact hKΛ
        · exact mem_of_mem_dstarComp hJ hJK
      obtain ⟨yb, hyb⟩ := horb _ (map_mem_quotFamily hJΛ)
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N₀ yb
      have hKy : conjSub y (K.subgroupOf Y) ∈ Λ := hΛ.conjInvariant y _ hKΛ
      have himg : (conjSub y (K.subgroupOf Y)).map (QuotientGroup.mk' N₀) =
          J.map (QuotientGroup.mk' N₀) := by
        rw [AscQuot.map_conjSub]
        exact hyb
      obtain ⟨n, -, hn⟩ := exists_conj_of_map_eq hp hq hΛ hN₀odd hKy hJΛ himg
      exact ⟨n * y, by rw [conjSub_mul]; exact hn.symm⟩
    have h1 := c.trans_of_orbit hKY hY1
    obtain ⟨W₁, hW₁, hW₁S, hW₁n, -⟩ := c.exists_section_W hA hM hS
    have hRS' : R.subgroupOf Y ≤ (AscQuot.sylowOfIsSylow2In' hS : Subgroup ↥Y) :=
      Subgroup.subgroupOf_mono Y (le_inf hRS hRY)
    have hR'S' : R'.subgroupOf Y ≤ (AscQuot.sylowOfIsSylow2In' hS : Subgroup ↥Y) :=
      Subgroup.subgroupOf_mono Y (le_inf hR'S hR'Y)
    exact c.le_of_section hY hK'tw hK'ne hR' hR'K' hKY hK'Y (AscQuot.sylowOfIsSylow2In' hS)
      hRS' hR'S' hW₁ hW₁S hW₁n h1 (c.cent_section hKY)

end CFSG.ClassicalInvolution.Asc77
