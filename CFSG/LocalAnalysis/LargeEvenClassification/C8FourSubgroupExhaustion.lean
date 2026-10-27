module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroups

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem c8Four_coatom_binary_kernel (i : Fin 896)
    (M : Subgroup (c8FourListedSubgroup i)) (hM : IsCoatom M) :
    ∃ f : c8FourListedSubgroup i →* Multiplicative (ZMod 2), f.ker = M := by
  classical
  let H := c8FourListedSubgroup i
  have hp := c8Four_code_isPGroup.to_subgroup H
  let : M.Normal := pGroup_coatom_normal Nat.prime_two hp M hM
  have hcard : Nat.card (H ⧸ M) = 2 := pGroup_coatom_quotient_card Nat.prime_two hp M hM
  have hcyclic : IsCyclic (H ⧸ M) := isCyclic_of_prime_card hcard
  let e : H ⧸ M ≃* Multiplicative (ZMod 2) := by
    have e := (zmodCyclicMulEquiv hcyclic).symm
    rw [hcard] at e
    exact e
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' M), ?_⟩
  ext g
  change e ((QuotientGroup.mk' M) g) = 1 ↔ g ∈ M
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff g

theorem c8Four_all_binary_characters (i : Fin 896)
    (f : c8FourListedSubgroup i →* Multiplicative (ZMod 2)) :
    ∃ q : Fin 32, f = c8FourRecordCharacter i q := by
  classical
  let r := c8FourRecord i
  let H := c8FourListedSubgroup i
  let values : Fin 5 → ZMod 2 := fun k =>
    if hk : k.val < r.generators.length then
      (f ⟨r.generators[k.val]!, by
        have hmem : r.generators[k.val]! ∈ r.generators := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
          exact List.getElem_mem hk
        exact ((certificateListAll_iff _ _).mp (c8Four_all_records_valid i).2.2.2.1)
          _ hmem⟩).toAdd
    else 0
  let q := c8FourEncodeBits values
  refine ⟨q, ?_⟩
  apply c8FourRecord_hom_ext r (c8Four_all_records_valid i)
  intro x hx
  obtain ⟨k, hk, hvalue⟩ := List.mem_iff_getElem.mp hx
  have hk5 : k < 5 := lt_of_lt_of_le hk (c8Four_all_records_valid i).2.2.2.2.2.2.2
  let j : Fin 5 := ⟨k, hk5⟩
  have hget : r.generators[k]! = x.val := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact hvalue
  apply Multiplicative.ofAdd.symm.injective
  change (f x).toAdd = c8FourPairing (c8FourVector r x.val) q
  have hvector := c8Four_all_vectors i j hk
  change c8FourVector r r.generators[k]! = Fin.ofNat 32 (2 ^ k) at hvector
  rw [hget] at hvector
  rw [hvector]
  have hpair := c8FourPairing_encode values j
  change c8FourPairing (Fin.ofNat 32 (2 ^ k)) q = values j at hpair
  rw [hpair]
  simp only [values, j, dite_eq_left hk]
  congr 1
  apply congrArg f
  apply Subtype.ext
  exact hget.symm

theorem c8Four_character_kernel_listed (i : Fin 896) (q : Fin 32) :
    (c8FourRecordCharacter i q).ker.map (c8FourListedSubgroup i).subtype =
      c8FourListedSubgroup ((c8FourRecord i).children[q.val]!) := by
  ext g
  rw [Subgroup.mem_map]
  change (∃ x : c8FourListedSubgroup i,
    c8FourRecordCharacter i q x = 1 ∧ x.val = g) ↔
      c8FourRecordMem (c8FourRecord ((c8FourRecord i).children[q.val]!)) g
  rw [c8Four_record_character_kernels i q g]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    exact congrArg Multiplicative.toAdd hx
  · intro hg
    refine ⟨⟨g, hg.1⟩, ?_, rfl⟩
    apply Multiplicative.ofAdd.symm.injective
    exact hg.2

theorem c8Four_subgroups_exhaustive (Q : Subgroup C8FourCode) :
    ∃ i : Fin 896, c8FourListedSubgroup i = Q := by
  classical
  have htop : c8FourListedSubgroup 895 = ⊤ := by
    ext g
    change c8FourRecordMem (c8FourRecord 895) g ↔ True
    unfold c8FourRecord
    change c8FourRecordMem c8FourRecordData895 g ↔ True
    have h : ∀ g : C8FourCode, c8FourRecordMem c8FourRecordData895 g := by decide +kernel
    simp [h]
  have hdown : ∀ n : ℕ, ∀ i : Fin 896, Nat.card (c8FourListedSubgroup i) = n →
      ∀ K : Subgroup C8FourCode, K ≤ c8FourListedSubgroup i →
        ∃ j : Fin 896, c8FourListedSubgroup j = K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hcard K hKI
      let H := c8FourListedSubgroup i
      let L := K.comap H.subtype
      have hmap : L.map H.subtype = K := by
        rw [Subgroup.map_comap_eq, H.range_subtype, inf_eq_right.mpr hKI]
      rcases IsCoatomic.eq_top_or_exists_le_coatom L with hL | ⟨M, hM, hLM⟩
      · refine ⟨i, ?_⟩
        rw [← hmap, hL, Subgroup.map_top]
        exact H.range_subtype.symm
      · obtain ⟨f, hf⟩ := c8Four_coatom_binary_kernel i M hM
        obtain ⟨q, hq⟩ := c8Four_all_binary_characters i f
        let j := (c8FourRecord i).children[q.val]!
        have hlisted : c8FourListedSubgroup j = M.map H.subtype := by
          rw [← hf, hq]
          exact (c8Four_character_kernel_listed i q).symm
        have hlt : c8FourListedSubgroup j < H := by
          rw [hlisted]
          have hmapped : M.map H.subtype < (⊤ : Subgroup H).map H.subtype :=
            (Subgroup.map_lt_map_iff_of_injective Subtype.val_injective).mpr
              (lt_top_iff_ne_top.mpr hM.1)
          simpa only [Subgroup.map_top, H.range_subtype] using hmapped
        have hjcard : Nat.card (c8FourListedSubgroup j) < n :=
          hcard ▸ Subgroup.card_lt_of_lt hlt
        have hKj : K ≤ c8FourListedSubgroup j := by
          rw [hlisted, ← hmap]
          exact Subgroup.map_mono hLM
        exact ih _ hjcard j rfl K hKj
  exact hdown _ 895 rfl Q (htop ▸ le_top)

end CFSG.LargeEvenClassification.Helpers
