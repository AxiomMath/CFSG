module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem perm5_normal_CIrrPerm (M : Subgroup (Equiv.Perm (Fin 5))) [M.Normal] :
    M = ⊥ ∨ alternatingGroup (Fin 5) ≤ M := by
  by_cases h : M = ⊥
  · exact Or.inl h
  · exact Or.inr (Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((Subgroup.nontrivial_iff_ne_bot M).2 h))

private def threeCycleCIrrPerm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

private theorem threeCycleCIrrPerm_mem :
    threeCycleCIrrPerm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    (show Equiv.Perm.IsSwap (Equiv.swap (0 : Fin 5) 1) from ⟨0, 1, by decide, rfl⟩)
    (show Equiv.Perm.IsSwap (Equiv.swap (1 : Fin 5) 2) from ⟨1, 2, by decide, rfl⟩)

private theorem threeCycleCIrrPerm_ne_one : threeCycleCIrrPerm ≠ 1 := by
  decide

theorem exists_mulEquiv_inf_commutator_of_perm5 (H : Subgroup A5WrTwo)
    (hH : Nonempty (↥H ≃* Equiv.Perm (Fin 5))) :
    Nonempty (↥(H ⊓ commutator A5WrTwo) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨φ⟩ := hH
  let B : Subgroup A5WrTwo := commutator A5WrTwo
  haveI hBnorm : B.Normal := by
    change (commutator A5WrTwo).Normal
    infer_instance
  let K : Subgroup ↥H := B.subgroupOf H
  have hKdvd : K.index ∣ 2 := by
    have h := Subgroup.relIndex_dvd_index_of_normal (H := B) (K := H)
    have hBindex : B.index = 2 := A5WrTwo.index_commutator
    rw [hBindex] at h
    change (B.subgroupOf H).index ∣ 2
    exact h
  rcases (Nat.dvd_prime Nat.prime_two).mp hKdvd with hK1 | hK2
  ·
    exfalso
    have htop : K = ⊤ := (Subgroup.index_eq_one (H := K)).mp hK1
    have hHB : H ≤ B :=
      (Subgroup.subgroupOf_eq_top (H := B) (K := H)).mp (by simpa [K] using htop)
    have hHrange : H ≤ A5WrTwo.baseEmb.range := by
      rw [A5WrTwo.range_baseEmb]
      exact hHB
    let f : Equiv.Perm (Fin 5) →* A5WrTwo := H.subtype.comp φ.symm.toMonoidHom
    have hf_inj : Function.Injective f := H.subtype_injective.comp φ.symm.injective
    have hfrange : f.range ≤ A5WrTwo.baseEmb.range := by
      rintro x ⟨y, rfl⟩
      exact hHrange (φ.symm y).2
    let f' : Equiv.Perm (Fin 5) →* A5WrTwo.baseEmb.range :=
      f.codRestrict A5WrTwo.baseEmb.range
        (fun x => hfrange (MonoidHom.mem_range.mpr ⟨x, rfl⟩))
    have hf'_inj : Function.Injective f' :=
      (MonoidHom.injective_codRestrict f A5WrTwo.baseEmb.range
        (fun x => hfrange (MonoidHom.mem_range.mpr ⟨x, rfl⟩))).mpr hf_inj
    let g : Equiv.Perm (Fin 5) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
      (MonoidHom.ofInjective A5WrTwo.baseEmb_injective).symm.toMonoidHom.comp f'
    have hg_inj : Function.Injective g :=
      (MonoidHom.ofInjective A5WrTwo.baseEmb_injective).symm.injective.comp hf'_inj
    have hker1 : alternatingGroup (Fin 5) ≤
        ((MonoidHom.fst (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).comp g).ker := by
      rcases perm5_normal_CIrrPerm
        ((MonoidHom.fst (alternatingGroup (Fin 5))
          (alternatingGroup (Fin 5))).comp g).ker with h | h
      · exfalso
        have hinj : Function.Injective
            ((MonoidHom.fst (alternatingGroup (Fin 5))
              (alternatingGroup (Fin 5))).comp g) :=
          (MonoidHom.ker_eq_bot_iff _).mp h
        have hcard := Nat.card_le_card_of_injective _ hinj
        have h1 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
          rw [Nat.card_perm, Nat.card_fin]; norm_num
        have h2 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
          rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num
        omega
      · exact h
    have hker2 : alternatingGroup (Fin 5) ≤
        ((MonoidHom.snd (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).comp g).ker := by
      rcases perm5_normal_CIrrPerm
        ((MonoidHom.snd (alternatingGroup (Fin 5))
          (alternatingGroup (Fin 5))).comp g).ker with h | h
      · exfalso
        have hinj : Function.Injective
            ((MonoidHom.snd (alternatingGroup (Fin 5))
              (alternatingGroup (Fin 5))).comp g) :=
          (MonoidHom.ker_eq_bot_iff _).mp h
        have hcard := Nat.card_le_card_of_injective _ hinj
        have h1 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
          rw [Nat.card_perm, Nat.card_fin]; norm_num
        have h2 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
          rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num
        omega
      · exact h
    have hgtriv : ∀ x : Equiv.Perm (Fin 5), x ∈ alternatingGroup (Fin 5) → g x = 1 := by
      intro x hx
      have h1 : (g x).1 = 1 := MonoidHom.mem_ker.mp (hker1 hx)
      have h2 : (g x).2 = 1 := MonoidHom.mem_ker.mp (hker2 hx)
      exact Prod.ext h1 h2
    have hc : threeCycleCIrrPerm = 1 := by
      apply hg_inj
      rw [hgtriv threeCycleCIrrPerm threeCycleCIrrPerm_mem, map_one]
    exact threeCycleCIrrPerm_ne_one hc
  ·
    have hKtoInf : K ≃* ↥(H ⊓ B) :=
      (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_left (H := B) (K := H)).symm).trans
        (Subgroup.subgroupOfEquivOfLe (show H ⊓ B ≤ H from inf_le_left))
    let M : Subgroup (Equiv.Perm (Fin 5)) := K.map (φ : ↥H →* Equiv.Perm (Fin 5))
    have hMindex : M.index = 2 := by
      change (K.map (φ : ↥H →* Equiv.Perm (Fin 5))).index = 2
      rw [Subgroup.index_map_of_bijective (f := (φ : ↥H →* Equiv.Perm (Fin 5))) φ.bijective K,
        hK2]
    have hM : M = alternatingGroup (Fin 5) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hMindex
    exact ⟨hKtoInf.symm.trans
      ((MulEquiv.subgroupMap φ K).trans (MulEquiv.subgroupCongr hM))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
