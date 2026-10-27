module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIM12Data
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

abbrev M12G : Subgroup (Equiv.Perm (Fin 12)) := CFSG.Blueprint.NativeSporadic.M12

@[expose] def mA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def mB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem M12G_eq : M12G = Subgroup.closure {mA, mB} := rfl

theorem tabRep_mA : TabRep m12AT mA := by unfold TabRep; decide

theorem tabRep_mB : TabRep m12BT mB := by unfold TabRep; decide

theorem m12Gens_cover : ∀ a ∈ ({mA, mB} : Set (Equiv.Perm (Fin 12))),
    ∃ j < m12Gens.size, TabRep m12Gens[j]! a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact ⟨0, by decide, tabRep_mA⟩
  · exact ⟨1, by decide, tabRep_mB⟩

theorem m12Gens_tabs : ∀ j < m12Gens.size,
    ∃ a ∈ ({mA, mB} : Set (Equiv.Perm (Fin 12))), TabRep m12Gens[j]! a := by
  intro j hj
  have hj' : j < 2 := hj
  interval_cases j
  · exact ⟨mA, by simp, tabRep_mA⟩
  · exact ⟨mB, by simp, tabRep_mB⟩

theorem hfiMem_iff {T : Array Tab} {x : Tab} : hfiMem T x = true ↔ ∃ k < T.size, T[k]! = x := by
  simp [hfiMem, anyBelow_eq_true]

theorem mem_centTabs_of_commute_gen {n : ℕ} {ER : Array Tab} {t r : Tab}
    {a ra : Equiv.Perm (Fin n)} (ht : t ∈ ER) (hta : TabRep t a) (hr : TabRep r ra)
    (hc : a * ra = ra * a) : t ∈ centTabs n ER r := by
  unfold centTabs
  rw [Array.mem_filter]
  exact ⟨ht, (hta.comp hr).beq_iff (hr.comp hta) |>.2 hc⟩

theorem m12_triple_spec {EM OA OB : Enum} (h : hfiM12Check EM OA OB = true)
    {a b : ↥M12G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b)
    (hcomm : a * b = b * a)
    (ha240 : Nat.card ↥(centralizer ({a} : Set ↥M12G)) = 240)
    (hb240 : Nat.card ↥(centralizer ({b} : Set ↥M12G)) = 240)
    (hab240 : Nat.card ↥(centralizer ({a * b} : Set ↥M12G)) = 240) :
    ∃ g : ↥M12G, g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a * b := by
  simp only [hfiM12Check, Bool.and_eq_true, and_assoc, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h
  obtain ⟨hEnum, hsize, hOrbA, hsizeA, hOrbB, hsizeB, hmemA, hmemB, ha2T, ha1T, hb2T, hb1T,
    hcover, hmain⟩ := h
  have hE : Enumerates M12G EM.tabs.toList := by
    rw [M12G_eq]
    exact enumerates_closure m12Gens_cover m12Gens_tabs hEnum
  have hcard : Nat.card ↥M12G = 95040 := by rw [hE.card, Array.length_toList, hsize]
  have hEel : ∀ x : Tab, hfiMem EM.tabs x = true → ∃ g ∈ M12G, TabRep x g := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hfiMem_iff.1 hx
    exact hE.sound _ (getElem!_mem hk)
  obtain ⟨a₀p, ha₀p, ha₀rep⟩ := hEel _ hmemA
  obtain ⟨b₀p, hb₀p, hb₀rep⟩ := hEel _ hmemB
  let a₀ : ↥M12G := ⟨a₀p, ha₀p⟩
  let b₀ : ↥M12G := ⟨b₀p, hb₀p⟩
  obtain ⟨hsA, hcA, hnA⟩ := conj_orbit (A := {mA, mB}) m12Gens_cover m12Gens_tabs ha₀rep hOrbA
  obtain ⟨hsB, hcB, hnB⟩ := conj_orbit (A := {mA, mB}) m12Gens_cover m12Gens_tabs hb₀rep hOrbB
  obtain ⟨hclA, hcardA⟩ := conjClass_of_tabs_gen (H := M12G) (x := a₀) hsA hcA hnA
  obtain ⟨hclB, hcardB⟩ := conjClass_of_tabs_gen (H := M12G) (x := b₀) hsB hcB hnB
  rw [Array.length_toList, hsizeA] at hcardA
  rw [Array.length_toList, hsizeB] at hcardB
  have hsq : ∀ y : ↥M12G, orderOf y = 2 →
      (y : Equiv.Perm (Fin 12)) ≠ 1 ∧ (y : Equiv.Perm (Fin 12)) * y = 1 := by
    intro y hy
    have h2 : y * y = 1 := by rw [← sq, ← hy]; exact pow_orderOf_eq_one y
    have h1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hy; omega
    exact ⟨fun h' => h1 (Subtype.ext h'), congrArg Subtype.val h2⟩
  have hinvcover : ∀ y : ↥M12G, orderOf y = 2 → IsConj y a₀ ∨ IsConj y b₀ := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hsq y hy
    obtain ⟨i, hi, t, ht, hr⟩ := exists_of_coverOK hE hcover y.2 hy1 hy2
    have hi2 : i < 2 := hi
    interval_cases i
    · exact Or.inl ((hclA y).2 ⟨t, ht, hr⟩)
    · exact Or.inr ((hclB y).2 ⟨t, ht, hr⟩)
  have hgood : ∀ y : ↥M12G, orderOf y = 2 →
      Nat.card ↥(centralizer ({y} : Set ↥M12G)) = 240 → IsConj y a₀ := by
    intro y hy hc
    rcases hinvcover y hy with h1 | h1
    · exact h1
    · exfalso
      have hk := card_carrier_mul_card_centralizer y
      rw [hcard, ConjClasses.mk_eq_mk_iff_isConj.2 h1, hcardB, hc] at hk
      omega
  have hab2 : orderOf (a * b) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
    have hb2 : b * b = 1 := by rw [← sq, ← hb]; exact pow_orderOf_eq_one b
    refine orderOf_eq_prime ?_ ?_
    · calc (a * b) ^ 2 = (a * b) * (a * b) := sq _
        _ = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcomm]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · intro h1
      exact hab ((inv_eq_of_mul_eq_one_right ha2).symm.trans
        (eq_inv_of_mul_eq_one_right h1).symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 (hgood a ha ha240)
  have hb2 : b * b = 1 := by rw [← sq, ← hb]; exact pow_orderOf_eq_one b
  have hx2 : (c * b * c⁻¹) * (c * b * c⁻¹) = 1 := by
    calc (c * b * c⁻¹) * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hxcomm : (c * b * c⁻¹) * a₀ = a₀ * (c * b * c⁻¹) := by
    rw [← hc]
    calc c * b * c⁻¹ * (c * a * c⁻¹) = c * (b * a) * c⁻¹ := by group
      _ = c * (a * b) * c⁻¹ := by rw [hcomm]
      _ = c * a * c⁻¹ * (c * b * c⁻¹) := by group
  have hx1 : c * b * c⁻¹ ≠ 1 := by
    intro h1
    have h2 : b = 1 := by
      have := congrArg (fun z => c⁻¹ * z * c) h1
      simpa [mul_assoc] using this
    rw [h2, orderOf_one] at hb
    omega
  have hxa : c * b * c⁻¹ ≠ a₀ := by
    intro h1
    have h2 : c * b * c⁻¹ = c * a * c⁻¹ := h1.trans hc.symm
    exact hab (mul_left_cancel (mul_right_cancel h2)).symm
  have hxA : IsConj (c * b * c⁻¹) a₀ :=
    (isConj_iff.2 ⟨c⁻¹, by group⟩ : IsConj (c * b * c⁻¹) b).trans (hgood b hb hb240)
  have hax : a₀ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by
    rw [← hc]
    group
  have haxA : IsConj (a₀ * (c * b * c⁻¹)) a₀ := by
    rw [hax]
    exact (isConj_iff.2 ⟨c⁻¹, by group⟩ : IsConj (c * (a * b) * c⁻¹) (a * b)).trans
      (hgood (a * b) hab2 hab240)
  obtain ⟨kx, hkx, hxrep⟩ := hE.exists_pos (c * b * c⁻¹).2
  have hxEM : EM.tabs[kx]! ∈ EM.tabs := Array.mem_def.2 (getElem!_mem hkx)
  have hxC := mem_centTabs_of_commute_gen hxEM hxrep ha₀rep (congrArg Subtype.val hxcomm)
  obtain ⟨k, hk, hkx'⟩ := exists_getElem!_of_mem (Array.mem_def.1 hxC)
  have hk' := (allBelow_eq_true.1 hmain) k hk
  rw [hkx'] at hk'
  have e1 : (comp 12 EM.tabs[kx]! EM.tabs[kx]! == idTab 12) = true :=
    ((hxrep.comp hxrep).beq_iff TabRep.idTab).2 (congrArg Subtype.val hx2)
  have e2 : (EM.tabs[kx]! == idTab 12) = false := by
    rw [← Bool.not_eq_true]
    intro hc'
    exact hx1 (Subtype.ext ((hxrep.beq_iff TabRep.idTab).1 hc'))
  have e3 : (EM.tabs[kx]! == m12a₀T) = false := by
    rw [← Bool.not_eq_true]
    intro hc'
    exact hxa (Subtype.ext ((hxrep.beq_iff ha₀rep).1 hc'))
  have hax' : TabRep (comp 12 m12a₀T EM.tabs[kx]!)
      (((a₀ * (c * b * c⁻¹) : ↥M12G)) : Equiv.Perm (Fin 12)) := ha₀rep.comp hxrep
  have m1 : hfiMem OA.tabs EM.tabs[kx]! = true := by
    obtain ⟨t, ht, hr⟩ := (hclA _).1 hxA
    rw [hfiMem_iff]
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    exact ⟨i, hi, hr.tab_eq hxrep⟩
  have m2 : hfiMem OA.tabs (comp 12 m12a₀T EM.tabs[kx]!) = true := by
    obtain ⟨t, ht, hr⟩ := (hclA _).1 haxA
    rw [hfiMem_iff]
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    exact ⟨i, hi, hr.tab_eq hax'⟩
  simp only [e1, e2, e3, m1, m2, Bool.not_false, Bool.and_self, Bool.not_true,
    Bool.false_or] at hk'
  simp only [anyBelow_eq_true, Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨j, hj, hj1, hj2⟩ := hk'
  obtain ⟨hh, hhM, hhrep⟩ := hE.exists_elt hj
  let hel : ↥M12G := ⟨hh, hhM⟩
  have hh1 : hel * a₀ = (c * b * c⁻¹) * hel :=
    Subtype.ext (((hhrep.comp ha₀rep).eq_iff (hxrep.comp hhrep)).1 hj1)
  have hh2 : hel * (c * b * c⁻¹) = (a₀ * (c * b * c⁻¹)) * hel :=
    Subtype.ext (((hhrep.comp hxrep).eq_iff (hax'.comp hhrep)).1 hj2)
  refine ⟨c⁻¹ * hel * c, ?_, ?_⟩
  · have h3 : hel * a₀ * hel⁻¹ = c * b * c⁻¹ := by rw [hh1]; group
    calc c⁻¹ * hel * c * a * (c⁻¹ * hel * c)⁻¹ = c⁻¹ * (hel * (c * a * c⁻¹) * hel⁻¹) * c := by
          group
      _ = c⁻¹ * (hel * a₀ * hel⁻¹) * c := by rw [hc]
      _ = b := by rw [h3]; group
  · have h3 : hel * (c * b * c⁻¹) * hel⁻¹ = a₀ * (c * b * c⁻¹) := by rw [hh2]; group
    calc c⁻¹ * hel * c * b * (c⁻¹ * hel * c)⁻¹ =
          c⁻¹ * (hel * (c * b * c⁻¹) * hel⁻¹) * c := by group
      _ = c⁻¹ * (a₀ * (c * b * c⁻¹)) * c := by rw [h3]
      _ = a * b := by rw [hax]; group

end CFSG.EvenSporadicStandard.HSStd.HFI
