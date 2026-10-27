module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeHigh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem isI4PlusIn_top_of_isOmegaStar (hP : Asc82PocketCover) {X : Type} [Group X] {n : ℕ}
    {ε : ℤˣ} (hX : IsOmegaStar X n ε) (hn : n ≤ 7 ∨ (n = 8 ∧ ε = -1))
    (hπ : ¬ (Even n ∧ ε = (-1) ^ (n / 2))) {f : QuaternionGroup 2 →* X}
    (hf : Function.Injective f) :
    IsI4PlusIn (⊤ : Subgroup X) (f (QuaternionGroup.a 2)) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := hX
  letI := i1
  letI := i2
  letI := i3
  have hπQ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim, hs]
    exact hπ
  obtain ⟨e'⟩ := nonempty_omegaGroup_mulEquiv_omegaProj hQ hπQ
  let E : X ≃* omegaGroup hQ := e.trans e'.symm
  have hn' : Module.finrank (ZMod 3) V ≤ 7 ∨
      (Module.finrank (ZMod 3) V = 8 ∧ quadSign Q = -1) := by
    rw [hdim, hs]
    exact hn
  have hf' : Function.Injective (E.toMonoidHom.comp f) := E.injective.comp hf
  have h := isI4PlusIn_top_of_quaternion_omega hP hQ hn' hf'
  have h2 := isI4PlusIn_top_map_mulEquiv E.symm h
  have hback : E.symm ((E.toMonoidHom.comp f) (QuaternionGroup.a 2)) =
      f (QuaternionGroup.a 2) := E.symm_apply_apply _
  rwa [hback] at h2

theorem isI4PlusIn_top_of_isOmegaCover (hP : Asc82PocketCover) {X : Type} [Group X] {n : ℕ}
    {ε : ℤˣ} (hX : IsOmegaCover X n ε) (hn : n ≤ 7 ∨ (n = 8 ∧ ε = -1))
    {f : QuaternionGroup 2 →* X} (hf : Function.Injective f) :
    IsI4PlusIn (⊤ : Subgroup X) (f (QuaternionGroup.a 2)) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := hX
  letI := i1
  letI := i2
  letI := i3
  have hn' : Module.finrank (ZMod 3) V ≤ 7 ∨
      (Module.finrank (ZMod 3) V = 8 ∧ quadSign Q = -1) := by
    rw [hdim, hs]
    exact hn
  have hf' : Function.Injective (e.toMonoidHom.comp f) := e.injective.comp hf
  have h := isI4PlusIn_top_of_quaternion_omega hP hQ hn' hf'
  have h2 := isI4PlusIn_top_map_mulEquiv e.symm h
  have hback : e.symm ((e.toMonoidHom.comp f) (QuaternionGroup.a 2)) =
      f (QuaternionGroup.a 2) := e.symm_apply_apply _
  rwa [hback] at h2

theorem asc82Q8Pocket_of_inputs (hP : Asc82PocketCover) (hG3 : Asc82Omega8PlusPocket)
    (hS : Asc82SchurU43) : Asc82Q8Pocket := by
  intro X _ _ hX f hf
  unfold PocketableQuotient at hX
  rcases hX with h5 | h7 | h8p | h8m | ⟨hqs, h6⟩
  · exact isI4PlusIn_top_of_isOmegaStar hP (isOmegaStar_of_lieModel_psp h5)
      (Or.inl (by norm_num)) (by decide) hf
  · exact isI4PlusIn_top_of_isOmegaStar hP (isOmegaStar_of_lieModel_odd h7)
      (Or.inl (by norm_num)) (by decide) hf
  · exact hG3 X h8p f hf
  · exact isI4PlusIn_top_of_isOmegaStar hP (isOmegaStar_of_lieModel_minus h8m)
      (Or.inr ⟨rfl, rfl⟩) (by decide) hf
  · exact isI4PlusIn_top_of_isOmegaCover hP ((isOmegaCover_iff_isTwoU43 hS hqs).mpr h6)
      (Or.inl (by norm_num)) hf

end CFSG.OddStandard.SmallF3.Omega
