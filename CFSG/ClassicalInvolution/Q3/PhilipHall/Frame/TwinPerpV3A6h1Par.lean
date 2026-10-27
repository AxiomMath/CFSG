module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1ParWr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1ParA8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open Certificates.AE6Par

theorem zBar_d0_mul_b0 :
    zBar d0 card_d0 * zBar b0 card_b0 = zBar {2, 3, 4, 5} (by decide) := by
  rw [zBar_eq_mk, zBar_eq_mk, zBar_eq_mk, ← map_mul, ofVec_mul_ofVec,
    show parInd d0 + parInd b0 = parInd {2, 3, 4, 5} from funext (by decide)]

theorem six_eq : six = [d0, d0ᶜ, b0, b0ᶜ, {2, 3, 4, 5}, ({2, 3, 4, 5} : Finset (Fin 8))ᶜ] := by
  decide +kernel

theorem card_of_mem_six : ∀ δ ∈ six, δ.card = 4 := by
  decide +kernel

theorem mem_six_of_zBar {δ : Finset (Fin 8)} {h : δ.card = 4}
    (hz : zBar δ h = zBar d0 card_d0 ∨ zBar δ h = zBar b0 card_b0 ∨
      zBar δ h = zBar d0 card_d0 * zBar b0 card_b0) : δ ∈ six := by
  rw [zBar_d0_mul_b0] at hz
  rw [six_eq]
  rcases hz with hz | hz | hz
  · rcases eq_or_compl_of_zBar_eq hz.symm with rfl | rfl <;> simp
  · rcases eq_or_compl_of_zBar_eq hz.symm with rfl | rfl <;> simp
  · rcases eq_or_compl_of_zBar_eq hz.symm with rfl | rfl <;> simp

theorem zBar_of_mem_six {δ : Finset (Fin 8)} (hδ : δ ∈ six) (h : δ.card = 4) :
    zBar δ h = zBar d0 card_d0 ∨ zBar δ h = zBar b0 card_b0 ∨
      zBar δ h = zBar d0 card_d0 * zBar b0 card_b0 := by
  rw [zBar_d0_mul_b0]
  rw [six_eq] at hδ
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hδ
  rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl (zBar_compl _ card_d0 h).symm
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl (zBar_compl _ card_b0 h).symm)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr (zBar_compl _ (by decide) h).symm)

section Facts


theorem ae6ParM_d0_b0 : ae6ParM (zBar d0 card_d0) (zBar b0 card_b0) = aeBarOver parS0 := by
  refine le_antisymm (ae6ParM_le fun δ h c hz => ?_) ?_
  · have hδ := mem_six_of_zBar hz
    rintro _ ⟨a, ha, rfl⟩
    exact mkQ_mem_aeBarOver
      ⟨memAt_le_aeSub8 δ h c ha, par_vk.1.2 δ hδ a.perm (vkPred_perm_of_mem_memAt ha)⟩
  · set H := (ae6ParM (zBar d0 card_d0) (zBar b0 card_b0)).comap (mkQ 8) with hH
    have hmem : ∀ δ ∈ six, ∀ (h : δ.card = 4) (c : Bool), memAt δ h c ≤ H := fun δ hδ h c =>
      Subgroup.map_le_iff_le_comap.mp (memBar_le_ae6ParM h c (zBar_of_mem_six hδ h))
    have hvec : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ofVec v ∈ H := by
      refine ofVec_mem_of_pairs fun x y hxy => ?_
      obtain ⟨δ, hδ, hx, hy⟩ := par_vk.2 x y hxy
      have h := card_of_mem_six δ hδ
      exact (sup_le (hmem δ hδ h true) (hmem δ hδ h false)) (pairVec_mem_sup h hx hy hxy)
    have hlift : ∀ σ, inS0 σ = true → ∃ a ∈ H ⊓ aeSub 8, permHom 8 a = σ := by
      refine exists_perm_of_tree (permHom 8) fun g hg => ?_
      obtain ⟨hg6, hgv⟩ := par_vk.1.1 g hg
      have h := card_of_mem_six g.1 hg6
      obtain ⟨a, ha, hap⟩ := exists_mem_memAt_perm h true hgv
      exact ⟨a, ⟨hmem g.1 hg6 h true ha, memAt_le_aeSub8 g.1 h true ha⟩, hap⟩
    refine Subgroup.map_le_iff_le_comap.mpr fun x hx => ?_
    obtain ⟨hxa, hxp⟩ := hx
    obtain ⟨a, ⟨haH, haA⟩, hap⟩ := hlift x.perm hxp
    have hap' : a.perm = x.perm := hap
    have hb : a⁻¹ * x ∈ aeSub 8 := (aeSub 8).mul_mem ((aeSub 8).inv_mem haA) hxa
    have hv : a⁻¹ * x = ofVec (a⁻¹ * x).vec := by
      refine Wr.ext rfl ?_
      show a.perm⁻¹ * x.perm = 1
      rw [hap', inv_mul_cancel]
    have h1 : a⁻¹ * x ∈ H := by
      rw [hv]
      exact hvec _ (mem_aeSub.mp hb).1
    have hx' : x = a * (a⁻¹ * x) := by group
    rw [hx']
    exact H.mul_mem haH h1

theorem exists_conj_memBar_d0 {F : List (Finset (Fin 8))}
    (hA8 : AE.stabFamily F ≤ alternatingGroup (Fin 8))
    (hplanes : ∀ δ : Finset (Fin 8), δ.card = 4 → (∀ σ ∈ dts δ, σ ∈ AE.stabFamily F) → δ ∈ F)
    (htab : ∀ δ ∈ F, ∃ ρ ∈ AE.stabFamily F, d0.map ρ.toEmbedding = δ) {δ : Finset (Fin 8)}
    (h : δ.card = 4) (c : Bool) (hδ : memBar δ h c ≤ aeBarOver (AE.stabFamily F)) :
    ∃ e ∈ aeBarOver (AE.stabFamily F), conjSub e (memBar d0 card_d0 true) = memBar δ h c := by
  have hδF : δ ∈ F := by
    refine hplanes δ h fun σ hσ => ?_
    obtain ⟨a, ha, hap⟩ := exists_mem_memAt_perm h c (vkPred_dts h σ hσ)
    have h1 := mem_aeSubOver_of_mkQ_mem (hδ (show mkQ 8 a ∈ memBar δ h c from ⟨a, ha, rfl⟩))
    rw [← hap]
    exact h1.2
  obtain ⟨ρ, hρ, rfl⟩ := htab δ hδF
  obtain ⟨c₁, hc₁⟩ := conjSub_ofPerm_memBar ρ card_d0 true
  have hg : mkQ 8 (ofPerm ρ) ∈ aeBarOver (AE.stabFamily F) :=
    mkQ_mem_aeBarOver (ofPerm_mem_aeSubOver_of_le hA8 hρ)
  obtain ⟨w, hw, hwc⟩ :=
    exists_conj_memBar (by norm_num) (d0.map ρ.toEmbedding) h (AE.stabFamily F)
  have hw' : mkQ 8 w ∈ aeBarOver (AE.stabFamily F) := mkQ_mem_aeBarOver hw
  cases c₁ <;> cases c
  · exact ⟨_, hg, hc₁⟩
  · refine ⟨(mkQ 8 w)⁻¹ * mkQ 8 (ofPerm ρ),
      (aeBarOver _).mul_mem ((aeBarOver _).inv_mem hw') hg, ?_⟩
    rw [conjSub_mul, hc₁]
    show conjSub (mkQ 8 w)⁻¹ (memBar (d0.map ρ.toEmbedding) h false) =
      memBar (d0.map ρ.toEmbedding) h true
    rw [← hwc]
    exact conjSub_inv_conjSub _ _
  · refine ⟨mkQ 8 w * mkQ 8 (ofPerm ρ), (aeBarOver _).mul_mem hw' hg, ?_⟩
    rw [conjSub_mul, hc₁]
    exact hwc
  · exact ⟨_, hg, hc₁⟩

theorem exists_conj_memBar_planes {F : List (Finset (Fin 8))}
    (hA8 : AE.stabFamily F ≤ alternatingGroup (Fin 8))
    (hplanes : ∀ δ : Finset (Fin 8), δ.card = 4 → (∀ σ ∈ dts δ, σ ∈ AE.stabFamily F) → δ ∈ F)
    (htab : ∀ δ ∈ F, ∃ ρ ∈ AE.stabFamily F, d0.map ρ.toEmbedding = δ)
    {δ δ' : Finset (Fin 8)} (h : δ.card = 4) (h' : δ'.card = 4) (c c' : Bool)
    (hδ : memBar δ h c ≤ aeBarOver (AE.stabFamily F))
    (hδ' : memBar δ' h' c' ≤ aeBarOver (AE.stabFamily F)) :
    ∃ e ∈ aeBarOver (AE.stabFamily F), conjSub e (memBar δ h c) = memBar δ' h' c' := by
  obtain ⟨e₁, he₁, h₁⟩ := exists_conj_memBar_d0 hA8 hplanes htab h c hδ
  obtain ⟨e₂, he₂, h₂⟩ := exists_conj_memBar_d0 hA8 hplanes htab h' c' hδ'
  refine ⟨e₂ * e₁⁻¹, (aeBarOver _).mul_mem he₂ ((aeBarOver _).inv_mem he₁), ?_⟩
  rw [conjSub_mul, ← h₁, conjSub_inv_conjSub, h₂]

theorem ae6ParFacts_parS0 : AE6ParFacts (aeBarOver parS0) where
  card := by rw [card_aeBarOver parS0 parS0_le_alternating, card_parS0]
  overg X h1 h2 := by
    obtain ⟨A, hSA, hA8, rfl⟩ := exists_eq_aeBarOver parS0_le_alternating h1 h2
    rcases parS0_overgroups hSA hA8 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by rw [card_aeBarOver _ hA8, card_agl32]))
    · exact Or.inr (Or.inr (by rw [card_aeBarOver _ hA8, card_parAgl2]))
    · exact Or.inr (Or.inl aeBarOver_alternating)
  orbit X h1 h2 hX δ δ' h h' c c' hδ hδ' := by
    obtain ⟨A, hSA, hA8, rfl⟩ := exists_eq_aeBarOver parS0_le_alternating h1 h2
    rcases parS0_overgroups hSA hA8 with rfl | rfl | rfl | rfl
    · rw [card_aeBarOver _ hA8, card_parS0] at hX
      omega
    · exact exists_conj_memBar_planes hA8 (fun _ h hd => mem_affinePlanes_of_dts h hd)
        (fun _ hδ => exists_plane_perm1 hδ) h h' c c' hδ hδ'
    · exact exists_conj_memBar_planes hA8 (fun _ h hd => mem_planes2_of_dts h hd)
        (fun _ hδ => exists_plane_perm2 hδ) h h' c c' hδ hδ'
    · rw [aeBarOver_alternating, card_ae6AE8] at hX
      omega

theorem ae6ModelPar_proved : AE6ModelPar := by
  intro α β γ hα hβ hγ he
  obtain ⟨σ, rfl, rfl⟩ := exists_perm_d0_b0 hα hβ
    (card_inter_of_symmDiff hα hβ (card_symmDiff_of_zBar_mul he))
  rw [← ofPerm_conj_zBar σ card_d0, ← ofPerm_conj_zBar σ card_b0, ← conjSub_ofPerm_ae6ParM,
    ae6ParM_d0_b0]
  exact ae6ParFacts_conj ae6ParFacts_parS0 σ

end Facts

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
