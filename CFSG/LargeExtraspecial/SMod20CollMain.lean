module

public import CFSG.LargeExtraspecial.SMod20CollCert
public import CFSG.LargeExtraspecial.SMod20UaPolar
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

open scoped Pointwise

attribute [local irreducible] uaPts uPts uPos

@[expose] noncomputable def restrW {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 693))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i)) :
    E →* Equiv.Perm (wPlane i) :=
  (MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i)) (wPlane i)).comp
    (Subgroup.inclusion hW)

theorem restrW_apply {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 693))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i)) (π : E) (x : wPlane i) :
    (restrW hW π x).val = (π : Equiv.Perm (Fin 693)) x.val := rfl

theorem restrW_eq_one_iff {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 693))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i)) (π : E) :
    restrW hW π = 1 ↔ ∀ p ∈ wPlane i, (π : Equiv.Perm (Fin 693)) p = p := by
  constructor
  · intro h p hp
    have := congrArg (fun ν : Equiv.Perm (wPlane i) => (ν ⟨p, hp⟩).val) h
    simpa [restrW_apply] using this
  · intro h
    ext x
    rw [restrW_apply, h x.val x.2]
    rfl

section Main

variable
  {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 693))}

theorem sArr_mem_collI (hi : i < 891) {π : Equiv.Perm (Fin 693)} (hπ : IsPolarAut π)
    (hW : ⇑π '' wPlane i = wPlane i) (hsq : π * π = 1) (hne : ∃ p ∈ wPlane i, π p ≠ p) :
    sArr i π ∈ collI := by
  have h1 : ⇑(1 : Equiv.Perm (Fin 693)) '' wPlane i = wPlane i := by simp
  refine mem_collI (collAdm_sArr hi hπ hW) (by rw [← sArr_mul hi π hW, hsq, sArr_one hi])
    fun h => ?_
  obtain ⟨p, hp, hpp⟩ := hne
  rw [← sArr_one hi, sArr_eq_iff hi hW h1] at h
  exact hpp (h p hp)

variable (hi : i < 891)
  (hN : E ≤ Subgroup.normalizer (T46 : Set (Equiv.Perm (Fin 693))))
  (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i))
  [hE : CFSG.IsElementaryAbelian 2 E]
  (hC : E ⊓ Subgroup.centralizer (UA i : Set (Equiv.Perm (Fin 693))) ≤ UA i)
include hi hN hW hC

omit hi hE in
theorem ker_restrW_le {π : E} (hπ : restrW hW π = 1) : (π : Equiv.Perm (Fin 693)) ∈ UA i := by
  refine hC (Subgroup.mem_inf.2 ⟨π.2, ?_⟩)
  rw [UA, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨p, hp, rfl⟩
  have h := (isPolarAut_of_mem_normalizer (hN π.2)).mul_tvP_mul_inv p
  rw [(restrW_eq_one_iff hW π).1 hπ p hp] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem ker_restrW_fixed {κ : E} (hκ : restrW hW κ = 1) :
    ∃ a < 512, uaPsi i a = κ ∧ ∀ π ∈ E, collAmat (sArr i π) a = a := by
  obtain ⟨a, ha, he⟩ := (mem_UA hi).1 (ker_restrW_le hN hW hC hκ)
  refine ⟨a, ha, he, fun π hπ => ?_⟩
  have hcomm : π * κ = κ * π := by
    have := hE.is_comm.comm ⟨π, hπ⟩ κ
    exact congrArg Subtype.val this
  have hπW : ⇑π '' wPlane i = wPlane i := mem_stabilizer_wPlane.1 (hW hπ)
  refine uaPsi_inj hi (collAmat_lt (fun j hj => (sArr_spec hi hπW (by omega)).1) a) ha ?_
  rw [← conj_uaPsi hi (isPolarAut_of_mem_normalizer (hN hπ)) hπW, he, hcomm, mul_assoc,
    mul_inv_cancel, mul_one]

theorem card_ker_le (T : Finset (Equiv.Perm (Fin 693))) (hT : ∀ π ∈ T, π ∈ E) :
    Nat.card (restrW hW).ker ≤
      ((Finset.range 512).filter fun a => ∀ π ∈ T, collAmat (sArr i π) a = a).card := by
  classical
  have hfix := fun κ : (restrW hW).ker =>
    ker_restrW_fixed hi hN hW hC (κ := κ.1) (MonoidHom.mem_ker.1 κ.2)
  let f : (restrW hW).ker →
      ((Finset.range 512).filter fun a => ∀ π ∈ T, collAmat (sArr i π) a = a) :=
    fun κ => ⟨Classical.choose (hfix κ), by
      obtain ⟨ha, -, hfx⟩ := Classical.choose_spec (hfix κ)
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, fun π hπ => hfx π (hT π hπ)⟩⟩
  have hf : Function.Injective f := by
    intro κ κ' h
    have h' : Classical.choose (hfix κ) = Classical.choose (hfix κ') := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    rw [← (Classical.choose_spec (hfix κ)).2.1, ← (Classical.choose_spec (hfix κ')).2.1, h']
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective f hf

end Main

theorem card_eq_range_mul_ker {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 693))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i)) :
    Nat.card E = Nat.card (restrW hW).range * Nat.card (restrW hW).ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (restrW hW).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (restrW hW)).toEquiv]

@[expose] def sArrOf (i : ℕ) (ν : Equiv.Perm (wPlane i)) : Array ℕ :=
  Array.ofFn (n := 21) fun k => uaPos (uaPts[i]!) (ν ⟨wPt i k.val, wPt_mem i k.2⟩).val

theorem sArrOf_restrW {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 693))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i)) (π : E) :
    sArrOf i (restrW hW π) = sArr i π := rfl

theorem sArrOf_inj {i : ℕ} (hi : i < 891)
    {ν μ : Equiv.Perm (wPlane i)} (h : sArrOf i ν = sArrOf i μ) : ν = μ := by
  ext ⟨x, k, hk, rfl⟩
  have e := congrArg (fun s : Array ℕ => s[k]!) h
  simp only [sArrOf] at e
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn,
    getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn] at e
  obtain ⟨m, hm, hme⟩ := (ν ⟨wPt i k, wPt_mem i hk⟩).2
  obtain ⟨m', hm', hme'⟩ := (μ ⟨wPt i k, wPt_mem i hk⟩).2
  simp only at e
  rw [← hme, ← hme', uaPos_wPt hi hm, uaPos_wPt hi hm'] at e
  rw [← hme, ← hme', e]

section Bound

variable
  {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 693))} (hi : i < 891)
  (hN : E ≤ Subgroup.normalizer (T46 : Set (Equiv.Perm (Fin 693))))
  (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i))
  [hE : CFSG.IsElementaryAbelian 2 E]
  (hC : E ⊓ Subgroup.centralizer (UA i : Set (Equiv.Perm (Fin 693))) ≤ UA i)
include hi hN hW hC

theorem card_le_of_not_le_UA (hEU : ¬ E ≤ UA i) : Nat.card E ≤ 448 := by
  classical
  have hsq : ∀ π ∈ E, π * π = 1 := fun π hπ => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian π hπ
  have hcomm : ∀ π ∈ E, ∀ ρ ∈ E, π * ρ = ρ * π := fun π hπ ρ hρ =>
    congrArg Subtype.val (hE.is_comm.comm ⟨π, hπ⟩ ⟨ρ, hρ⟩)
  have hpa : ∀ π ∈ E, IsPolarAut π := fun π hπ => isPolarAut_of_mem_normalizer (hN hπ)
  have hWπ : ∀ π ∈ E, ⇑π '' wPlane i = wPlane i := fun π hπ =>
    mem_stabilizer_wPlane.1 (hW hπ)
  have hmove : ∀ π : E, restrW hW π ≠ 1 → ∃ p ∈ wPlane i, (π : Equiv.Perm (Fin 693)) p ≠ p :=
    fun π hπ => by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      exact hπ ((restrW_eq_one_iff hW π).2 h)
  have hmem : ∀ π : E, restrW hW π ≠ 1 → sArr i π ∈ collI := fun π hπ =>
    sArr_mem_collI hi (hpa _ π.2) (hWπ _ π.2) (hsq _ π.2) (hmove π hπ)
  have hcommArr : ∀ π ρ : E, collComp (sArr i π) (sArr i ρ) = collComp (sArr i ρ) (sArr i π) :=
    fun π ρ => by
      rw [← sArr_mul hi _ (hWπ _ ρ.2), ← sArr_mul hi _ (hWπ _ π.2), hcomm _ π.2 _ ρ.2]
  obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : E, restrW hW π₁ ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hEU fun π hπ => ker_restrW_le hN hW hC (h ⟨π, hπ⟩)
  rw [card_eq_range_mul_ker hW]
  by_cases h3 : ∃ π₂ : E, restrW hW π₂ ≠ 1 ∧ restrW hW π₂ ≠ restrW hW π₁
  · obtain ⟨π₂, hπ₂, hπ₂₁⟩ := h3
    have hs₁ := hmem π₁ hπ₁
    have hs₂ := hmem π₂ hπ₂
    have hs₁₂ : sArr i π₁ ≠ sArr i π₂ := by
      intro h
      rw [← sArrOf_restrW hW, ← sArrOf_restrW hW] at h
      exact hπ₂₁ (sArrOf_inj hi h).symm
    have hK : Nat.card (restrW hW).ker ≤ 16 := by
      refine (card_ker_le hi hN hW hC {(π₁ : Equiv.Perm (Fin 693)), (π₂ : Equiv.Perm (Fin 693))}
        (by intro π hπ; rcases Finset.mem_insert.1 hπ with rfl | hπ
            · exact π₁.2
            · rw [Finset.mem_singleton.1 hπ]; exact π₂.2)).trans
        (le_trans (Finset.card_le_card ?_) (card_fix₂_le hs₁ hs₂ hs₁₂ (hcommArr π₁ π₂)))
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        forall_eq_or_imp, forall_eq] at ha ⊢
      exact ⟨ha.1, ha.2.1, ha.2.2⟩
    have hR : Nat.card (restrW hW).range ≤ 28 := by
      set R : Set (Equiv.Perm (wPlane i)) :=
        ((restrW hW).range : Set (Equiv.Perm (wPlane i))) with hRdef
      have hR1 : (1 : Equiv.Perm (wPlane i)) ∈ R := (restrW hW).range.one_mem
      have hle : (R \ {1}).ncard ≤ 27 := by
        refine le_trans (Set.ncard_le_ncard_of_injOn (fun ν => collI.toList.idxOf (sArrOf i ν))
          (t := ↑((Finset.range collI.size).filter fun k =>
            collComp (sArr i π₁) collI[k]! = collComp collI[k]! (sArr i π₁) ∧
              collComp (sArr i π₂) collI[k]! = collComp collI[k]! (sArr i π₂))) ?_ ?_
          (Finset.finite_toSet _)) ?_
        · rintro ν ⟨⟨π, rfl⟩, hν1⟩
          have hν : restrW hW π ≠ 1 := hν1
          have hin : sArr i π ∈ collI.toList := Array.mem_toList_iff.2 (hmem π hν)
          have hlt := List.idxOf_lt_length_of_mem hin
          have hlt' : collI.toList.idxOf (sArr i π) < collI.size := by
            rwa [← Array.length_toList]
          have hget : collI[collI.toList.idxOf (sArr i π)]! = sArr i π := by
            rw [getElem!_pos collI (collI.toList.idxOf (sArr i π)) hlt', ← Array.getElem_toList,
              List.getElem_idxOf]
          rw [Finset.mem_coe, Finset.mem_filter, sArrOf_restrW, Finset.mem_range, hget]
          exact ⟨hlt', hcommArr π₁ π, hcommArr π₂ π⟩
        · rintro ν ⟨⟨π, rfl⟩, hν1⟩ μ ⟨⟨ρ, rfl⟩, -⟩ he
          simp only [sArrOf_restrW] at he
          have hin : sArr i π ∈ collI.toList := Array.mem_toList_iff.2 (hmem π hν1)
          have he' := (List.idxOf_inj hin).1 he
          rw [← sArrOf_restrW hW, ← sArrOf_restrW hW] at he'
          exact sArrOf_inj hi he'
        · rw [Set.ncard_coe_finset]
          exact card_comm_le hs₁ hs₂ hs₁₂ (hcommArr π₁ π₂)
      have := Set.ncard_sdiff_singleton_add_one hR1 (Set.toFinite R)
      have e : Nat.card (restrW hW).range = R.ncard := Nat.card_coe_set_eq _
      omega
    calc Nat.card (restrW hW).range * Nat.card (restrW hW).ker ≤ 28 * 16 :=
          Nat.mul_le_mul hR hK
      _ = 448 := by norm_num
  · simp only [not_exists, not_and, not_not] at h3
    have hs₁ := hmem π₁ hπ₁
    have hK : Nat.card (restrW hW).ker ≤ 64 := by
      refine (card_ker_le hi hN hW hC {(π₁ : Equiv.Perm (Fin 693))}
        (fun π hπ => by rw [Finset.mem_singleton.1 hπ]; exact π₁.2)).trans
        (le_trans (Finset.card_le_card ?_) (card_fix_le hs₁))
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_singleton, forall_eq] at ha ⊢
      exact ha
    have hR : Nat.card (restrW hW).range ≤ 2 := by
      have hsub : ((restrW hW).range : Set (Equiv.Perm (wPlane i))) ⊆ {1, restrW hW π₁} := by
        rintro _ ⟨π, rfl⟩
        by_cases h1 : restrW hW π = 1
        · exact Or.inl h1
        · exact Or.inr (h3 π h1)
      have e : Nat.card (restrW hW).range =
          ((restrW hW).range : Set (Equiv.Perm (wPlane i))).ncard := Nat.card_coe_set_eq _
      rw [e]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    calc Nat.card (restrW hW).range * Nat.card (restrW hW).ker ≤ 2 * 64 := Nat.mul_le_mul hR hK
      _ ≤ 448 := by norm_num

theorem rank_le_nine : Nat.card E ≤ 2 ^ 9 := by
  by_cases h : E ≤ UA i
  · exact (Subgroup.card_le_of_le h).trans (card_UA hi).le
  · exact (card_le_of_not_le_UA hi hN hW hC h).trans (by norm_num)

theorem elemAb_eq_UA (hcard : 2 ^ 9 ≤ Nat.card E) : E = UA i := by
  have h : E ≤ UA i := by
    by_contra h
    have := card_le_of_not_le_UA hi hN hW hC h
    omega
  exact Subgroup.eq_of_le_of_card_ge h (by rw [card_UA hi]; exact hcard)

end Bound

end CFSG.LargeExtraspecial.SMod20
