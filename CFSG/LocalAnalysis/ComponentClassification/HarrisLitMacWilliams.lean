module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitInputs
public import CFSG.Milestones.CLS_connectivity_MacWilliams_four_generator
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools

theorem exists_normal_E8 {X : Type} [Group X] [Finite X] (hX : ¬ SectionalRankLeFour X)
    {Y : Subgroup X} (hY : IsSylowOf 2 Y ⊤) :
    ∃ E : Subgroup X, E ≤ Y ∧ (∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E) ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ e ∈ E, e ^ 2 = 1) ∧ Nat.card E = 8 := by
  classical
  by_contra hno
  apply hX
  intro P hP
  have hMW := CFSG.Milestones.cls_connectivity_macwilliams_four_generator ↥Y hY.isPGroup (by
    intro E hEn hEab hE8
    apply hno
    refine ⟨E.map Y.subtype, map_subtype_le _, ?_, ?_, ?_, ?_⟩
    · rintro y hy _ ⟨e, he, rfl⟩
      exact ⟨⟨y, hy⟩ * e * (⟨y, hy⟩ : ↥Y)⁻¹, hEn.conj_mem e he ⟨y, hy⟩, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg (fun x : ↥E => ((x : ↥Y) : X)) this
    · rintro _ ⟨e, he, rfl⟩
      have := hEab.2 e he
      exact congrArg Subtype.val this
    · rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact hE8)
  obtain ⟨Q, hQ, hPQ⟩ : ∃ Q : Subgroup X, IsSylowOf 2 Q ⊤ ∧ P ≤ Q := by
    obtain ⟨Q, hQ⟩ := (hP.comap_subtype : IsPGroup 2 (P.subgroupOf ⊤)).exists_le_sylow
    exact ⟨_, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, mem_top x⟩, hQ hx, rfl⟩⟩
  obtain ⟨g, -, hg⟩ := hY.exists_mem_conj hQ
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'Y : P' ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hg x).mp (hPQ hx)
    simpa [MulAut.conj_apply] using this
  obtain ⟨s, hs, hcl⟩ := hMW (P'.subgroupOf Y)
  refine ⟨s.image (fun y : ↥Y => g * (y : X) * g⁻¹), Finset.card_image_le.trans hs, ?_⟩
  have himage : ((s.image (fun y : ↥Y => g * (y : X) * g⁻¹) : Finset X) : Set X) =
      (MulAut.conj g).toMonoidHom '' (Y.subtype '' (s : Set ↥Y)) := by
    ext x
    simp [MulAut.conj_apply]
  rw [himage, ← MonoidHom.map_closure, ← MonoidHom.map_closure, hcl, subgroupOf_map_subtype,
    inf_of_le_left hP'Y, hP', Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨x, hx, by group⟩

end CFSG.ComponentClassification.HarrisLit
