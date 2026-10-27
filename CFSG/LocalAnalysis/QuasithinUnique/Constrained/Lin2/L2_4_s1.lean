module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_s1_end (h8 : Lemma2_4_8) (h12 : Lemma2_4_12) (h21 : Lemma2_4_21)
    (h22 : Lemma2_4_22) (h24 : Lemma2_4_24) (hfus : Lemma2_4_s1_fusion) : Lin2Statement fun _ _ _ _ _ _ _ _ _ _ _ => False := by
  intro G _ _ T M H S L D n hcfg
  obtain ⟨⟨-, -, hTnR⟩, -, -, -, ⟨B, hB⟩, -⟩ := h8 G T M H S L D n hcfg
  have hST : S ≤ T := hcfg.S_le_T
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  obtain ⟨-, hRlt⟩ := h22 G T M H S L D n hcfg
  obtain ⟨⟨-, hRF, hRFS, -, -⟩, -⟩ := h12 G T M H S L D n hcfg B hB
  obtain ⟨s, hsF, hs2, hs1⟩ : ∃ s ∈ S ⊓ Subgroup.normalizer (B : Set G), s ^ 2 = 1 ∧ s ≠ 1 := by
    have hFbot : S ⊓ Subgroup.normalizer (B : Set G) ≠ ⊥ := by
      intro h
      rw [h, sup_bot_eq] at hRFS
      exact (ne_of_lt hRlt) hRFS
    have hF2 : IsPGroup 2 (S ⊓ Subgroup.normalizer (B : Set G) : Subgroup G) :=
      hcfg.cs.sylow.isPGroup.to_le inf_le_left
    obtain ⟨f, hf, hf2, hf1⟩ := exists_involution_of_isPGroup hF2 hFbot
    exact ⟨f, hf, hf2, hf1⟩
  have hsS : s ∈ S := hsF.1
  have hsR : s ∉ thompsonJ S := fun hsR => hs1 (by
    have : s ∈ thompsonJ S ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) := ⟨hsR, hsF⟩
    rw [hRF] at this
    simpa using this)
  obtain ⟨⟨-, hRTB⟩, hc, x, hxN, hxS, hx2, -, hCT, hFcyc, hTBeq, -, -⟩ :=
    h24 G T M H S L D n hcfg B hB _ rfl
  obtain ⟨f₀, hf₀⟩ := hFcyc.exists_generator
  have hFeq : S ⊓ Subgroup.normalizer (B : Set G) = Subgroup.zpowers (f₀ : G) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hf₀ ⟨y, hy⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact Subgroup.zpowers_le.2 f₀.2
  have hZc : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) :=
    ((lin2Z_cases (rfl : lin2Z L (thompsonJ S) = lin2Z L (thompsonJ S))).resolve_right
      fun h => h.1 hc).2
  have hTcyc : T = (T ⊓ Subgroup.centralizer (lin2Z L (thompsonJ S) : Set G)) ⊔
      Subgroup.zpowers (f₀ : G) := by
    rw [← hCT, ← hFeq, sup_assoc, ← hTBeq]
    exact hRTB.symm
  have hTZ : T ≤ Subgroup.normalizer ((lin2Z L (thompsonJ S) : Subgroup G) : Set G) :=
    fun g hg => by
      rw [← conjR_eq_self_iff, hZc]
      exact centerOf_normalized (hTnR hg)
  have hTN : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (lin2Z L (thompsonJ S) : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [← conjR_eq_self_iff, conjR_inf, conjR_eq_of_mem hg, ← conjR_centralizer,
      conjR_eq_of_mem_normalizer (hTZ hg)]
  have hxT : x ∈ T := hxN.1
  have hxn : x ∈ Subgroup.normalizer (thompsonJ S : Set G) := hTnR hxT
  have hCS : ∀ k ∈ T ⊓ Subgroup.centralizer (lin2Z L (thompsonJ S) : Set G), k ∈ S →
      k ∈ thompsonJ S := by
    intro k hk hkS
    have hk' : k ∈ thompsonJ S ⊔ Subgroup.zpowers x := by rw [hCT]; exact hk
    rcases mem_sup_zpowers_of_sq_eq_one hxn hx2 hk' with h | ⟨r, hr, hkr⟩
    · exact h
    · exfalso
      apply hxS
      have : x = r⁻¹ * k := by rw [hkr]; group
      rw [this]
      exact S.mul_mem (S.inv_mem (hRS hr)) hkS
  obtain ⟨-, hfusR⟩ := h21 G T M H S L D n hcfg
  have : IsSimpleGroup G := hcfg.simple
  refine transfer_contradiction_cyclic hcfg.nonabelian hcfg.sylowT inf_le_left hTN hTcyc
    (hST hsS) ?_ hs2 ?_
  · intro hsC
    exact hsR (hCS s hsC hsS)
  · intro g hg
    have hgS := hfus G T M H S L D n hcfg s hsS hsR hs2 g hg.1
    have hgR : g⁻¹ * s * g ∈ thompsonJ S := hCS _ hg hgS
    have hi2 : (g⁻¹ * s * g) ^ 2 = 1 := by
      have : (g⁻¹ * s * g) ^ 2 = g⁻¹ * s ^ 2 * g := by simp only [pow_two]; group
      rw [this, hs2]; simp
    have e : (g⁻¹)⁻¹ * (g⁻¹ * s * g) * g⁻¹ = s := by group
    have := hfusR (g⁻¹ * s * g) hgR hi2 g⁻¹ (by rw [e]; exact hST hsS)
    rw [e] at this
    exact hsR this

end CFSG.QuasithinUnique.Lin2
