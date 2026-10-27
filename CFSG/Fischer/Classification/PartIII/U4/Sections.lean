module

public import CFSG.Fischer.Classification.PartIII.U4.Linear2
public import CFSG.Fischer.Classification.PartIII.U4.Classify

public section

namespace CFSG.Fischer.Classification.LocalU4

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.LocalU
  CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

theorem exists_eq_muSet_of_section {g : PG 4} (hg : g ∈ DG 4) {S : Set (PG 4)}
    (hSsub : S ⊆ LocalClass (DG 4) g) (hτ : ∀ a ∈ S, ∀ b ∈ S, a * b * a ∈ S)
    (hT : TwinFree (LocalClass (DG 4) g) S) (hM : MeetsTwins (LocalClass (DG 4) g) S) :
    ∃ q ∈ DG 4, q * g ≠ g * q ∧ S = muSet (DG 4) g q := by
  have hPG : Pair (PG 4) (DG 4) := pair_DG le_rfl
  obtain ⟨c, hc⟩ := isConj_iff.1 (Pair.isConj hPG hg (tq_mem_DG (v₀_ne_zero (n := 2))
    herm_v₀_v₀))
  set S' := (fun s => c * s * c⁻¹) '' S with hS'def
  have hS'sub : S' ⊆ LocalClass (DG 4) (tq (v₀ 2)) := by
    rw [← hc, ← Pair.image_conj_localClass hPG]
    exact Set.image_mono hSsub
  have hτ' : ∀ a ∈ S', ∀ b ∈ S', a * b * a ∈ S' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a, hτ a ha b hb, by group⟩
  have hT' : TwinFree (LocalClass (DG 4) (tq (v₀ 2))) S' := hc ▸ twinFree_conj hPG c hT
  have hM' : MeetsTwins (LocalClass (DG 4) (tq (v₀ 2))) S' := hc ▸ meetsTwins_conj hPG c hM
  obtain ⟨γs, hγS, h1, h2⟩ := exists_section_fun (n := 2) (by norm_num) hS'sub hτ' hT' hM'
  obtain ⟨y, hy⟩ := exists_eq_herm_of_section_two ⟨h1, h2⟩
  have hSy : S' = muY y := by
    rw [muY_eq (by norm_num)]
    ext q
    constructor
    · intro hq
      obtain ⟨α, z, hz0, hz, rfl⟩ := exists_sv_of_mem_localClass (n := 2) (by norm_num)
        (hS'sub hq)
      have hmem := hγS z hz0 hz
      rw [hy z hz0 hz] at hmem
      exact ⟨z, hz0, hz, hT' _ hq _ hmem
        ((isTwin_sv_iff (by norm_num) hz0 hz hz0 hz).2 ⟨1, (one_smul K z).symm⟩)⟩
    · rintro ⟨z, hz0, hz, rfl⟩
      have hmem := hγS z hz0 hz
      rwa [hy z hz0 hz] at hmem
  have hu : tq (uy y) ∈ DG 4 := tq_mem_DG (uy_ne_zero y) (herm_uy_uy y)
  refine ⟨c⁻¹ * tq (uy y) * c⁻¹⁻¹, Pair.conj_mem hPG hu c⁻¹, fun h => ?_, ?_⟩
  · apply tq_uy_not_commute (n := 2) (by norm_num) y
    have h' := (conj_commute_iff c _ _).2 h
    have e : ∀ x : PG 4, c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹ = x := fun x => by group
    rwa [e, hc] at h'
  · have hS : S = (fun s => c⁻¹ * s * c⁻¹⁻¹) '' S' := by
      rw [hS'def, Set.image_image]
      conv_lhs => rw [← Set.image_id S]
      exact Set.image_congr fun s _ => by rw [id]; group
    rw [hS, hSy, muY, Pair.image_conj_muSet hPG, ← hc]
    congr 1
    group

end CFSG.Fischer.Classification.LocalU4
