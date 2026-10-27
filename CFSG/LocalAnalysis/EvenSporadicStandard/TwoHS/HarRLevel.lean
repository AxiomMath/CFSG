module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarComm
public import CFSG.Sporadic.SmallOddCore.HS
public import Certificates.Certificate26132
public import Certificates.Certificate26133
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarEval

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

theorem hn3850 : (3850 : ℕ) < 2 ^ 32 := by norm_num

theorem hsSylowGenTbls_length : hsSylowGenTbls.length = 4 := by simp [hsSylowGenTbls]

theorem harSPairs_letters : ∀ p ∈ harSPairs, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ hsSylowGenTbls.length) ∧
    ∀ l ∈ p.2, 1 ≤ l ∧ l ≤ hsSylowGenTbls.length := by
  rw [hsSylowGenTbls_length]
  decide

theorem harFourOK_true : harFourOK 0 = true ∧ harFourOK 1 = true :=
  Certificates.certificate26133

@[expose] noncomputable def harD : Subgroup (Equiv.Perm (Fin 3850)) := genOf 3850 harSCgens

section SOK

theorem harSOK_true : harSOK = true := Certificates.certificate26132

private theorem harSOK_parts :
    (hsSylowGenTbls.all fun g => permOK 3850 g && invOK 3850 g (invT 3850 g)) = true ∧
    (harSPairs.all fun p => hsSift (wordTbl 3850 hsSylowGenTbls p.1) &&
      hsSift (wordTbl 3850 hsSylowGenTbls p.2)) = true ∧
    harSCgens.all (permOK 3850) = true ∧ enumOK 3850 200 64 harSCgens = true ∧
    normOK 3850 200 harSCgens hsSylowGenTbls = true ∧
    (hsSylowGenTbls.all fun g => hsSylowGenTbls.all fun h =>
      memT 3850 (mulClosureH 3850 harSCgens.toArray 200).1 (tComm 3850 g h)) = true := by
  have h := harSOK_true
  simp only [harSOK, Bool.and_eq_true, and_assoc] at h
  exact h

theorem hsSylowGens_perm :
    ∀ g ∈ hsSylowGenTbls, permOK 3850 g = true ∧ invOK 3850 g (invT 3850 g) = true := by
  obtain ⟨h, -⟩ := harSOK_parts
  intro g hg
  exact Bool.and_eq_true_iff.1 (List.all_eq_true.1 h g hg)

theorem harSCgens_perm : ∀ g ∈ harSCgens, permOK 3850 g = true := by
  obtain ⟨-, -, h, -⟩ := harSOK_parts
  exact List.all_eq_true.1 h

theorem harD_card : Nat.card harD = 64 := by
  obtain ⟨-, -, -, h, -⟩ := harSOK_parts
  exact (enumOK_spec hn3850 harSCgens_perm h).1

theorem hsS_normalizes_harD : ∀ x ∈ hsS, ∀ d ∈ harD, x * d * x⁻¹ ∈ harD := by
  obtain ⟨-, -, -, h4, h5, -⟩ := harSOK_parts
  have hn := normOK_spec hn3850 harSCgens_perm h4 hsSylowGens_perm h5
  intro x hx d hd
  have hx' : x ∈ normalizer (harD : Set (Equiv.Perm (Fin 3850))) := hn hx
  exact (mem_normalizer_iff.1 hx' d).1 hd

theorem commutator_hsS_le_harD : ⁅hsS, hsS⁆ ≤ harD := by
  obtain ⟨-, -, -, h4, -, h6⟩ := harSOK_parts
  refine commutator_le_of_gens (s := tp 3850 '' {x | x ∈ hsSylowGenTbls.toArray}) rfl
    hsS_normalizes_harD ?_
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
  have hg' : g ∈ hsSylowGenTbls := by simpa using hg
  have hh' : h ∈ hsSylowGenTbls := by simpa using hh
  have hm := List.all_eq_true.1 (List.all_eq_true.1 h6 g hg') h hh'
  exact mem_genOf_of_memT hn3850 harSCgens_perm h4
    (rep_tComm hn3850 (rep_tp (hsSylowGens_perm g hg').1) (rep_tp (hsSylowGens_perm h hh').1)) hm

theorem harD_le_commutator : harD ≤ ⁅hsS ⊓ hsP, hsS ⊓ hsP⁆ := by
  obtain ⟨-, h2, h3, -⟩ := harSOK_parts
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ harSCgens := by simpa using hg
  have hgp := harSCgens_perm g hg'
  simp only [harSCgens, List.mem_map] at hg'
  obtain ⟨p, hp, rfl⟩ := hg'
  obtain ⟨x, hxS, hxrep⟩ := rep_wordTbl hn3850 (fun g hg => (hsSylowGens_perm g hg).1) p.1
    (harSPairs_letters p hp).1
  obtain ⟨y, hyS, hyrep⟩ := rep_wordTbl hn3850 (fun g hg => (hsSylowGens_perm g hg).1) p.2
    (harSPairs_letters p hp).2
  have hs := Bool.and_eq_true_iff.1 (List.all_eq_true.1 h2 p hp)
  have hxP : x ∈ hsP := (hs_groupData.sift _ x hxrep).1 hs.1
  have hyP : y ∈ hsP := (hs_groupData.sift _ y hyrep).1 hs.2
  rw [rep_unique (rep_tp hgp) (rep_tComm hn3850 hxrep hyrep)]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_inf.2 ⟨hxS, hxP⟩)
    (Subgroup.mem_inf.2 ⟨hyS, hyP⟩)

theorem commutator_hsS_eq_harD : ⁅hsS, hsS⁆ = harD :=
  le_antisymm commutator_hsS_le_harD
    (harD_le_commutator.trans (Subgroup.commutator_mono inf_le_left inf_le_left))

end SOK

theorem conjOK_spec {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {sift : Table → Bool}
    (hsift : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → (sift T = true ↔ g ∈ P))
    {c r x : Table} {a : Equiv.Perm (Fin n)} (hr : Rep n r a) (h : conjOK n sift c r x = true) :
    ∃ g ∈ P, Rep n x (g * a * g⁻¹) := by
  simp only [conjOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hperm, hinv⟩, hsf⟩, he⟩ := h
  have hc := rep_tp hperm
  refine ⟨tp n c, (hsift _ _ hc).1 hsf, ?_⟩
  have h1 := rep_conjT hc (rep_invT hc hinv) hr
  exact fun i hi => ((tblEq_iff.1 he) i hi).symm.trans (h1 i hi)

theorem harBPairs_letters (c : ℕ) : ∀ i < 2, (∀ l ∈ ((harBPairs c).getD i ([], [])).1,
    1 ≤ l ∧ l ≤ 2) ∧ ∀ l ∈ ((harBPairs c).getD i ([], [])).2, 1 ≤ l ∧ l ≤ 2 := by
  by_cases hc : c = 0
  · simp only [harBPairs, hc, ite_true]
    decide
  · simp only [harBPairs, hc, ite_false]
    decide

section Four

theorem harFour_spec {c : ℕ} (h : harFourOK c = true) {ρ t₁ t₂ : Equiv.Perm (Fin 3850)}
    (hρ : Rep 3850 (harRho c) ρ) (ht₁ : Rep 3850 (hsCentTbl 5) t₁)
    (ht₂ : Rep 3850 (hsCentTbl 12) t₂) :
    (∃ x c₂ c₃ : Equiv.Perm (Fin 3850), c₂ ∈ hsP ∧ c₃ ∈ hsP ∧ c₂ * t₂ * c₂⁻¹ = x ∧
      x * ρ = ρ * x ∧ c₃ * ρ * c₃⁻¹ = x * ρ) ∧
    ∃ (B : Subgroup (Equiv.Perm (Fin 3850))) (z c₁ c₄ : Equiv.Perm (Fin 3850)),
      B ≤ hsP ∧ B ≤ centralizer ({ρ} : Set (Equiv.Perm (Fin 3850))) ∧ ⁅B, B⁆ = B ∧ z ∈ B ∧
      c₁ ∈ hsP ∧ c₄ ∈ hsP ∧ c₁ * t₁ * c₁⁻¹ = z ∧ c₄ * ρ * c₄⁻¹ = ρ * z := by
  simp only [harFourOK, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, h3, h4, h5, h6, -, h8, h9, h10, h11⟩ := h
  have hsift : ∀ (T : Table) (g : Equiv.Perm (Fin 3850)), Rep 3850 T g →
      (hsSift T = true ↔ g ∈ hsP) := fun T g hT => hs_groupData.sift T g hT
  obtain ⟨c₂, hc₂, hx⟩ := conjOK_spec hsift ht₂ h3
  obtain ⟨c₃, hc₃, hx₃⟩ := conjOK_spec hsift hρ h5
  refine ⟨⟨c₂ * t₂ * c₂⁻¹, c₂, c₃, hc₂, hc₃, rfl, (commTT_iff hx hρ).1 h4,
    rep_unique hx₃ (Rep.compT hx hρ)⟩, ?_⟩
  have hBparts : ∀ g ∈ ([harRT c 3, harRT c 4] : List Table),
      permOK 3850 g = true ∧ hsSift g = true ∧ commTT 3850 g (harRho c) = true := by
    intro g hg
    have h1 := List.all_eq_true.1 h6 g hg
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨hp, -⟩, hs⟩, hc⟩ := h1
    exact ⟨hp, hs, hc⟩
  obtain ⟨hzperm, hzsift, hzcomm⟩ := hBparts (harRT c 3) (by simp)
  obtain ⟨hyperm, hysift, hycomm⟩ := hBparts (harRT c 4) (by simp)
  have hBperm : ∀ g ∈ ([harRT c 3, harRT c 4] : List Table), permOK 3850 g = true :=
    fun g hg => (hBparts g hg).1
  have hzrep : Rep 3850 (harRT c 3) (tp 3850 (harRT c 3)) := rep_tp hzperm
  have hyrep : Rep 3850 (harRT c 4) (tp 3850 (harRT c 4)) := rep_tp hyperm
  have hzP : tp 3850 (harRT c 3) ∈ hsP := (hsift _ _ hzrep).1 hzsift
  have hyP : tp 3850 (harRT c 4) ∈ hsP := (hsift _ _ hyrep).1 hysift
  have hzρ := (commTT_iff hzrep hρ).1 hzcomm
  have hyρ := (commTT_iff hyrep hρ).1 hycomm
  have hl := harBPairs_letters c
  have hlen : ([harRT c 3, harRT c 4] : List Table).length = 2 := rfl
  obtain ⟨u₀, hu₀, hu₀rep⟩ := rep_wordTbl hn3850 hBperm ((harBPairs c).getD 0 ([], [])).1
    (by rw [hlen]; exact (hl 0 (by norm_num)).1)
  obtain ⟨v₀, hv₀, hv₀rep⟩ := rep_wordTbl hn3850 hBperm ((harBPairs c).getD 0 ([], [])).2
    (by rw [hlen]; exact (hl 0 (by norm_num)).2)
  obtain ⟨u₁, hu₁, hu₁rep⟩ := rep_wordTbl hn3850 hBperm ((harBPairs c).getD 1 ([], [])).1
    (by rw [hlen]; exact (hl 1 (by norm_num)).1)
  obtain ⟨v₁, hv₁, hv₁rep⟩ := rep_wordTbl hn3850 hBperm ((harBPairs c).getD 1 ([], [])).2
    (by rw [hlen]; exact (hl 1 (by norm_num)).2)
  have hzC : tp 3850 (harRT c 3) ∈ ⁅genOf 3850 [harRT c 3, harRT c 4],
      genOf 3850 [harRT c 3, harRT c 4]⁆ := by
    rw [← (tblEq_iff_eq (rep_tComm hn3850 hu₀rep hv₀rep) hzrep).1 h8]
    exact Subgroup.commutator_mem_commutator hu₀ hv₀
  have hyC : tp 3850 (harRT c 4) ∈ ⁅genOf 3850 [harRT c 3, harRT c 4],
      genOf 3850 [harRT c 3, harRT c 4]⁆ := by
    rw [← (tblEq_iff_eq (rep_tComm hn3850 hu₁rep hv₁rep) hyrep).1 h9]
    exact Subgroup.commutator_mem_commutator hu₁ hv₁
  have hgens : ∀ g ∈ tp 3850 '' {x | x ∈ ([harRT c 3, harRT c 4] : List Table).toArray},
      g = tp 3850 (harRT c 3) ∨ g = tp 3850 (harRT c 4) := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ ([harRT c 3, harRT c 4] : List Table) := by simpa using hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  obtain ⟨c₁, hc₁, hz₁⟩ := conjOK_spec hsift ht₁ h10
  obtain ⟨c₄, hc₄, hz₄⟩ := conjOK_spec hsift hρ h11
  refine ⟨genOf 3850 [harRT c 3, harRT c 4], tp 3850 (harRT c 3), c₁, c₄, ?_, ?_, ?_,
    tp_mem_genOf (by simp), hc₁, hc₄, (rep_unique hzrep hz₁).symm,
    rep_unique hz₄ (Rep.compT hρ hzrep)⟩
  · show Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro g hg
    rcases hgens g hg with h | h <;> rw [h]
    · exact hzP
    · exact hyP
  · show Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro g hg
    rcases hgens g hg with h | h <;> rw [h]
    · exact Subgroup.mem_centralizer_singleton_iff.2 hzρ
    · exact Subgroup.mem_centralizer_singleton_iff.2 hyρ
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · show Subgroup.closure _ ≤ _
      rw [Subgroup.closure_le]
      intro g hg
      rcases hgens g hg with h | h <;> rw [h]
      · exact hzC
      · exact hyC

end Four

end CFSG.EvenSporadicStandard.TwoHS
