module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_19 (hTIA : TIAbelianTwoGroupCommute) (h8 : Lemma2_4_8) (h14 : Lemma2_4_14)
    (h16 : Lemma2_4_16) (h17 : Lemma2_4_17) (h18 : Lemma2_4_18) : Lemma2_4_19 := by
  intro G _ _ T M H S L D n hcfg Z hZ
  obtain ⟨⟨hTS, -, hTnR⟩, -, ⟨-, -, h3⟩, -⟩ := h8 G T M H S L D n hcfg
  have hST : S ≤ T := hcfg.S_le_T
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  obtain ⟨x₀, hx₀T, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hZ1, -, hZ3⟩ := h16 G T M H S L D n hcfg Z hZ
  obtain ⟨hZel, hZcard, hZS⟩ := hZ1
  obtain ⟨hTIZ, -, -⟩ := h18 G T M H S L D n hcfg Z hZ
  obtain ⟨h17a, -⟩ := h17 G T M H S L D n hcfg Z hZ
  have hZR : Z ≤ centerOf (thompsonJ S) := lin2Z_le_centerOf h16 hcfg hZ
  have hZRle : Z ≤ thompsonJ S := hZR.trans inf_le_left
  have hRC : thompsonJ S ≤ Subgroup.centralizer (Z : Set G) := lin2Z_centralized h16 hcfg hZ
  have h4 : 4 ≤ 2 ^ n := hcfg.four_le_two_pow
  apply le_antisymm
  ·
    obtain ⟨hRsup, -, -, -⟩ := h3 x₀ hx₀T hx₀S
    have hU := (hZ3 x₀ hx₀T hx₀S).2
    have hUR : blockU L ≤ thompsonJ S := by rw [hRsup]; exact le_sup_left
    have hUxR : conjR (blockU L) x₀ ≤ thompsonJ S := by rw [hRsup]; exact le_sup_right
    calc thompsonJ S = blockU L ⊔ conjR (blockU L) x₀ := hRsup
      _ ≤ weakClosure Z T := by
        refine sup_le ?_ ?_
        · calc blockU L = weakClosure Z (blockU L) := hU
            _ ≤ weakClosure Z T := weakClosure_mono (hUR.trans hRT)
        · calc conjR (blockU L) x₀ = conjR (weakClosure Z (blockU L)) x₀ := by rw [← hU]
            _ = weakClosure Z (conjR (blockU L) x₀) := conjR_weakClosure _ _ _
            _ ≤ weakClosure Z T := weakClosure_mono (hUxR.trans hRT)
  ·
    refine iSup₂_le fun g hg => ?_
    by_contra hgR
    have hZgel : IsElemAbelian 2 (conjR Z g) := (isElemAbelian_conjR_iff Z g).2 hZel
    have hZgcard : Nat.card (conjR Z g) = 2 ^ n := by rw [card_conjR, hZcard]
    have hSZg : S ⊓ conjR Z g ≠ ⊥ := by
      intro hbot
      have := card_le_two_of_forall (A := conjR Z g) (N := S)
        (fun a ha haS b hb hbS => inv_mul_mem_of_relIndex_two hTS (hg ha) (hg hb) haS hbS)
        (by rw [inf_comm]; exact hbot)
      rw [hZgcard] at this
      omega
    have hNV : conjR Z g ⊓ Subgroup.normalizer (Z : Set G) ≠ ⊥ := by
      intro hbot
      apply hSZg
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ conjR Z g ⊓ Subgroup.normalizer (Z : Set G) := ⟨hy.2, hZS hy.1⟩
      rwa [hbot] at this
    have hcomm : ⁅conjR Z g, Z⁆ = ⊥ := by
      refine hTIA G (conjR Z g) Z hZgel hZel (by rw [hZgcard, hZcard])
        (fusionIsTI_conjR hTIZ g) hTIZ ?_ ?_ hNV
      · intro h hne
        have := fusionIsTI_iff_conjR.1 (fusionIsTI_conjR hTIZ g) (g⁻¹ * h)
          (by rwa [conjR_conjR, mul_inv_cancel_left])
        rw [conjR_conjR, mul_inv_cancel_left] at this
        rwa [inf_comm]
      · exact hcfg.sylowT.isPGroup.to_le (sup_le hg (hZRle.trans hRT))
    have hZgC : conjR Z g ≤ T ⊓ Subgroup.centralizer (Z : Set G) :=
      le_inf hg (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
    rcases h17a with hCT | ⟨-, t₀, ht₀T, ht₀S, ht₀2, hCT, -, hZC⟩
    · rw [hCT] at hZgC
      exact hgR hZgC
    · obtain ⟨t, htZg, htR⟩ := IsConcreteLE.not_le_iff_exists.1 hgR
      have ht₀n : t₀ ∈ Subgroup.normalizer (thompsonJ S : Set G) := hTnR ht₀T
      have htC : t ∈ T ⊓ Subgroup.centralizer (Z : Set G) := hZgC htZg
      have hsq : t₀ ^ 2 ∈ thompsonJ S := by rw [ht₀2]; exact one_mem _
      obtain ⟨r₀, hr₀, ht⟩ : ∃ r ∈ thompsonJ S, t = r * t₀ := by
        have h1 : t ∈ thompsonJ S ⊔ Subgroup.zpowers t₀ := by rw [← hCT]; exact htC
        exact (mem_sup_zpowers_of_sq_eq_one ht₀n ht₀2 h1).resolve_left htR
      obtain ⟨-, htrans, -⟩ := h14 G T M H S L D n hcfg t₀ ht₀T ht₀S hsq
      have htt₀ : t₀⁻¹ * t ∈ thompsonJ S := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem ht₀n : t₀⁻¹ ∈ _) r₀).1 hr₀
        have e : t₀⁻¹ * (r₀ * t₀) = t₀⁻¹ * r₀ * t₀⁻¹⁻¹ := by group
        rw [ht, e]; exact h1
      have ht2 : t ^ 2 = 1 := hZgel.2 t htZg
      obtain ⟨s, hs, hst⟩ := htrans t₀ t (by simp) htt₀ ht₀2 ht2
      have hCRt : ∀ y ∈ thompsonJ S, y * t = t * y → y ∈ Z := by
        intro y hy hyt
        have hy' : s * y * s⁻¹ ∈ thompsonJ S :=
          (thompsonJ S).mul_mem ((thompsonJ S).mul_mem hs hy) ((thompsonJ S).inv_mem hs)
        have ht₀eq : t₀ = s * t * s⁻¹ := by rw [← hst]; group
        have hcomm' : t₀ * (s * y * s⁻¹) = (s * y * s⁻¹) * t₀ := by
          rw [ht₀eq]
          calc s * t * s⁻¹ * (s * y * s⁻¹) = s * (t * y) * s⁻¹ := by group
            _ = s * (y * t) * s⁻¹ := by rw [hyt]
            _ = (s * y * s⁻¹) * (s * t * s⁻¹) := by group
        have hyZ' : s * y * s⁻¹ ∈ Z := by
          rw [hZC]
          exact ⟨hy', Subgroup.mem_centralizer_singleton_iff.2 hcomm'.symm⟩
        have hsc : s * (s * y * s⁻¹) = (s * y * s⁻¹) * s :=
          Subgroup.mem_centralizer_iff.1 (hZR hyZ').2 s hs
        have e : s * y * s⁻¹ = y := by
          have h1 : s * (s * y * s⁻¹) = s * y := by rw [hsc]; group
          exact mul_left_cancel h1
        rw [e] at hyZ'
        exact hyZ'
      have hKN : T ⊓ Subgroup.centralizer (Z : Set G) ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
        fun k hk => hTnR hk.1
      have hRZg : thompsonJ S ⊓ conjR Z g ≠ ⊥ := by
        intro hbot
        have := card_le_two_of_forall (A := conjR Z g) (N := thompsonJ S)
          (fun a ha haR b hb hbR =>
            inv_mul_mem_of_sq_eq_one (le_inf hRT hRC) hKN hCT (hZgC ha) (hZgC hb)
              (hZgel.2 a ha) (hZgel.2 b hb) haR hbR)
          (by rw [inf_comm]; exact hbot)
        rw [hZgcard] at this
        omega
      have hZZg : Z ⊓ conjR Z g ≠ ⊥ := by
        intro hbot
        apply hRZg
        rw [eq_bot_iff]
        intro y hy
        have hyZ : y ∈ Z := hCRt y hy.1 (IsElemAbelian.comm hZgel hy.2 htZg)
        have : y ∈ Z ⊓ conjR Z g := ⟨hyZ, hy.2⟩
        rwa [hbot] at this
      have heq : conjR Z g = Z := conjR_eq_of_inf_ne_bot hTIZ hZZg
      apply hgR
      rw [heq]
      exact hZRle

end CFSG.QuasithinUnique.Lin2
