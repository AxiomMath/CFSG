module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA2Check
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.A2

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four CFSG.PSL3Four.Native

@[expose] def USet : Set (Equiv.Perm (Fin 42)) := {g | ∃ t ∈ uTabs.toList, TabRep t g}

@[expose] def PSet : Set (Equiv.Perm (Fin 42)) := {g | g ∈ S ∧ g 0 = 0}

theorem hU1 : (allBelow uTabs.size fun i =>
    found (indexOf enumS.tabs) enumS.tabs uTabs[i]! && (uTabs[i]!)[0]! == 0 &&
      comp 42 uTabs[i]! uTabs[i]! == idTab 42) = true := scanU1_eq

theorem hU2
    : (allBelow uTabs.size fun i => allBelow uTabs.size fun j =>
    found (indexOf uTabs) uTabs (comp 42 uTabs[i]! uTabs[j]!)) = true := scanU2_eq

theorem hU3
    : found (indexOf uTabs) uTabs (idTab 42) = true := scanU3_eq

theorem hPU : (allBelow enumS.tabs.size fun k =>
    !((enumS.tabs[k]!)[0]! == 0) ||
      ((invTab 42 enumS.tabs[k]!).size == 42 &&
        comp 42 (invTab 42 enumS.tabs[k]!) enumS.tabs[k]! == idTab 42 &&
        allBelow uTabs.size fun j =>
          found (indexOf uTabs) uTabs
            (conjTab 42 enumS.tabs[k]! (invTab 42 enumS.tabs[k]!) uTabs[j]!))) = true := scanPU_eq

theorem hR : (comp 42 r₂T r₂T == idTab 42 &&
    allBelow uTabs.size fun j => found (indexOf uTabs) uTabs (conjTab 42 r₂T r₂T uTabs[j]!)) =
      true := scanR_eq

theorem hA0
    : (found (indexOf uTabs) uTabs a0T && !(a0T == idTab 42) &&
    found (indexOf (centS r₂T)) (centS r₂T) a0T) = true := scanA0_eq

theorem hTrans : (allBelow uTabs.size fun j =>
    uTabs[j]! == idTab 42 ||
      anyBelow enumS.tabs.size fun k =>
        (enumS.tabs[k]!)[0]! == 0 && (invTab 42 enumS.tabs[k]!).size == 42 &&
          comp 42 (invTab 42 enumS.tabs[k]!) enumS.tabs[k]! == idTab 42 &&
          conjTab 42 enumS.tabs[k]! (invTab 42 enumS.tabs[k]!) a0T == uTabs[j]!) = true :=
  scanTrans_eq

theorem hZ
    : (found (indexOf (centS r₂T)) (centS r₂T) zT && zT[0]! == 0 &&
    comp 42 (comp 42 zT zT) zT == idTab 42 && !(zT == idTab 42) &&
    allBelow uTabs.size fun j =>
      !(comp 42 zT uTabs[j]! == comp 42 uTabs[j]! zT) || uTabs[j]! == idTab 42) = true :=
  scanZ_eq

theorem hRed : (allBelow (centS r₂T).size fun i =>
    !(comp 42 (centS r₂T)[i]! (centS r₂T)[i]! == idTab 42) ||
      anyBelow (centS r₂T).size fun j =>
        (invTab 42 (centS r₂T)[j]!).size == 42 &&
          comp 42 (invTab 42 (centS r₂T)[j]!) (centS r₂T)[j]! == idTab 42 &&
          found (indexOf uTabs) uTabs
            (conjTab 42 (centS r₂T)[j]! (invTab 42 (centS r₂T)[j]!) (centS r₂T)[i]!)) = true :=
  scanRed_eq

theorem hWit : (allBelow uTabs.size fun j =>
    !(comp 42 r₂T uTabs[j]! == comp 42 uTabs[j]! r₂T) ||
      anyBelow uTabs.size fun i =>
        comp 42 (comp 42 (comp 42 r₂T uTabs[i]!) r₂T) uTabs[i]! == uTabs[j]!) = true :=
  scanWit_eq

theorem rep_zero {t : Tab} {g : Equiv.Perm (Fin 42)} (h : TabRep t g) : t[0]! = (g 0 : ℕ) := by
  simpa using h.apply 0

theorem zero_of_rep {t : Tab} {g : Equiv.Perm (Fin 42)} (h : TabRep t g) (h0 : t[0]! = 0) :
    g 0 = 0 := by
  have := rep_zero h
  rw [h0] at this
  exact Fin.ext this.symm

theorem rep_zero_of {t : Tab} {g : Equiv.Perm (Fin 42)} (h : TabRep t g) (h0 : g 0 = 0) :
    t[0]! = 0 := by
  rw [rep_zero h, h0]
  rfl

theorem U_sound
    {g : Equiv.Perm (Fin 42)} (hg : g ∈ USet) : g ∈ S ∧ g 0 = 0 ∧ g * g = 1 := by
  obtain ⟨t, ht, hrep⟩ := hg
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  have h := hU1
  rw [allBelow_eq_true] at h
  have hi' := h i (by simpa using hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at hi'
  obtain ⟨⟨hfound, h0⟩, hsq⟩ := hi'
  obtain ⟨g', hg'S, hrep'⟩ := enumerates_S.sound _ (mem_of_found hfound)
  have hgg : g = g' := hrep.perm_eq hrep'
  subst hgg
  exact ⟨hg'S, zero_of_rep hrep h0, ((hrep.comp hrep).eq_iff TabRep.idTab).1 hsq⟩

theorem U_mul
    {a b : Equiv.Perm (Fin 42)} (ha : a ∈ USet) (hb : b ∈ USet) : a * b ∈ USet := by
  obtain ⟨ta, hta, hra⟩ := ha
  obtain ⟨tb, htb, hrb⟩ := hb
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem hta
  obtain ⟨j, hj, rfl⟩ := exists_getElem!_of_mem htb
  have h := hU2
  rw [allBelow_eq_true] at h
  have h1 := h i (by simpa using hi)
  rw [allBelow_eq_true] at h1
  exact ⟨_, mem_of_found (h1 j (by simpa using hj)), hra.comp hrb⟩

theorem U_one
    : (1 : Equiv.Perm (Fin 42)) ∈ USet := ⟨_, mem_of_found hU3, TabRep.idTab⟩

theorem exists_pos_P {p : Equiv.Perm (Fin 42)} (hp : p ∈ PSet) :
    ∃ k < enumS.tabs.size, TabRep enumS.tabs[k]! p ∧ (enumS.tabs[k]!)[0]! = 0 :=
  let ⟨k, hk, hrep⟩ := enumerates_S.exists_pos hp.1
  ⟨k, hk, hrep, rep_zero_of hrep hp.2⟩

theorem U_conj
    {p a : Equiv.Perm (Fin 42)} (hp : p ∈ PSet) (ha : a ∈ USet) :
    p * a * p⁻¹ ∈ USet := by
  obtain ⟨k, hk, hrep, h0⟩ := exists_pos_P hp
  obtain ⟨ta, hta, hra⟩ := ha
  obtain ⟨j, hj, rfl⟩ := exists_getElem!_of_mem hta
  have h := hPU
  rw [allBelow_eq_true] at h
  have h1 := h k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Bool.and_eq_true] at h1
  rcases h1 with h1 | ⟨⟨hsz, hinv⟩, hall⟩
  · exact absurd h0 (by simpa using h1)
  · have hinvrep := hrep.inv (by simpa using hsz) hinv
    rw [allBelow_eq_true] at hall
    exact ⟨_, mem_of_found (hall j (by simpa using hj)), hrep.conjTab hra hinvrep⟩

theorem r₂_sq : r₂ * r₂ = 1 := by
  have h := hR
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ((tabRep_r₂.comp tabRep_r₂).eq_iff TabRep.idTab).1 h.1

theorem U_r
    {a : Equiv.Perm (Fin 42)} (ha : a ∈ USet) : r₂ * a * r₂⁻¹ ∈ USet := by
  obtain ⟨ta, hta, hra⟩ := ha
  obtain ⟨j, hj, rfl⟩ := exists_getElem!_of_mem hta
  have h := hR
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hr2, hall⟩ := h
  have hinvrep : TabRep r₂T r₂⁻¹ := tabRep_r₂.inv tabRep_r₂.1 hr2
  rw [allBelow_eq_true] at hall
  exact ⟨_, mem_of_found (hall j (by simpa using hj)), tabRep_r₂.conjTab hra hinvrep⟩

theorem U_subset_P
    : USet ⊆ PSet := fun _ hg => ⟨(U_sound hg).1, (U_sound hg).2.1⟩

theorem exists_a0
    : ∃ a₀ : Equiv.Perm (Fin 42), TabRep a0T a₀ ∧ a₀ ∈ USet ∧ a₀ ≠ 1 ∧ a₀ ∈ C₂ := by
  have h := hA0
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨hU, hne⟩, hC⟩ := h
  obtain ⟨a₀, ha₀C, hrep⟩ := enumerates_C₂.sound _ (mem_of_found hC)
  exact ⟨a₀, hrep, ⟨_, mem_of_found hU, hrep⟩,
    fun h1 => hne (beq_iff_eq.1 ((hrep.beq_iff TabRep.idTab).2 h1)), ha₀C⟩

theorem trans_a0
    {a₀ : Equiv.Perm (Fin 42)} (hrep : TabRep a0T a₀) {a : Equiv.Perm (Fin 42)}
    (ha : a ∈ USet) (ha1 : a ≠ 1) : ∃ p ∈ PSet, a = p * a₀ * p⁻¹ := by
  obtain ⟨ta, hta, hra⟩ := ha
  obtain ⟨j, hj, rfl⟩ := exists_getElem!_of_mem hta
  have h := hTrans
  rw [allBelow_eq_true] at h
  have h1 := h j (by simpa using hj)
  simp only [Bool.or_eq_true, beq_iff_eq, anyBelow_eq_true, Bool.and_eq_true] at h1
  rcases h1 with h1 | ⟨k, hk, ⟨⟨h0, hsz⟩, hinv⟩, hconj⟩
  · exact absurd ((hra.eq_iff TabRep.idTab).1 h1) ha1
  · obtain ⟨p, hpS, hprep⟩ := enumerates_S.exists_elt hk
    have hinvrep := hprep.inv (by simpa using hsz) hinv
    refine ⟨p, ⟨hpS, zero_of_rep hprep h0⟩, ?_⟩
    exact ((hprep.conjTab hrep hinvrep).eq_iff hra).1 hconj |>.symm

theorem exists_z
    : ∃ z : Equiv.Perm (Fin 42), z ∈ PSet ∧ z ∈ C₂ ∧ z * z * z = 1 ∧
    (∀ a ∈ USet, z * a = a * z → a = 1) := by
  have h := hZ
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hC, h0⟩, h3⟩, hne⟩, hall⟩ := h
  obtain ⟨z, hzC, hrep⟩ := enumerates_C₂.sound _ (mem_of_found hC)
  refine ⟨z, ⟨hzC.2, zero_of_rep hrep h0⟩, hzC, ?_, ?_⟩
  · exact (((hrep.comp hrep).comp hrep).eq_iff TabRep.idTab).1 h3
  · intro a ha hza
    obtain ⟨ta, hta, hra⟩ := ha
    obtain ⟨j, hj, rfl⟩ := exists_getElem!_of_mem hta
    rw [allBelow_eq_true] at hall
    have h1 := hall j (by simpa using hj)
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exfalso
      have : (comp 42 zT uTabs[j]! == comp 42 uTabs[j]! zT) = true :=
        ((hrep.comp hra).beq_iff (hra.comp hrep)).2 hza
      simp only [this] at h1
      exact absurd h1 (by simp)
    · exact (hra.eq_iff TabRep.idTab).1 h1

theorem red_C₂
    {k : Equiv.Perm (Fin 42)} (hk : k ∈ C₂) (hk2 : k * k = 1) :
    ∃ k' ∈ C₂, k' * k * k'⁻¹ ∈ USet := by
  obtain ⟨i, hi, hrep⟩ := enumerates_C₂.exists_pos hk
  have h := hRed
  rw [allBelow_eq_true] at h
  have h1 := h i hi
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, anyBelow_eq_true,
    Bool.and_eq_true] at h1
  rcases h1 with h1 | ⟨j, hj, ⟨⟨hsz, hinv⟩, hfound⟩⟩
  · exfalso
    have : (comp 42 (centS r₂T)[i]! (centS r₂T)[i]! == idTab 42) = true :=
      ((hrep.comp hrep).beq_iff TabRep.idTab).2 hk2
    simp only [this] at h1
    exact absurd h1 (by simp)
  · obtain ⟨k', hk'C, hk'rep⟩ := enumerates_C₂.exists_elt hj
    have hinvrep := hk'rep.inv (by simpa using hsz) hinv
    exact ⟨k', hk'C, _, mem_of_found hfound, hk'rep.conjTab hrep hinvrep⟩

theorem exists_rep_uTabs
    {i : ℕ} (hi : i < uTabs.size) :
    ∃ x : Equiv.Perm (Fin 42), TabRep uTabs[i]! x := by
  have h := hU1
  rw [allBelow_eq_true] at h
  have hi' := h i hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hi'
  obtain ⟨⟨hfound, -⟩, -⟩ := hi'
  obtain ⟨g, -, hrep⟩ := enumerates_S.sound _ (mem_of_found hfound)
  exact ⟨g, hrep⟩

theorem wit_r
    {a : Equiv.Perm (Fin 42)} (ha : a ∈ USet) (hcomm : r₂ * a = a * r₂) :
    ∃ x ∈ USet, r₂ * x * r₂⁻¹ * x = a := by
  obtain ⟨ta, hta, hra⟩ := ha
  obtain ⟨j, hj, rfl⟩ := exists_getElem!_of_mem hta
  have h := hWit
  rw [allBelow_eq_true] at h
  have h1 := h j (by simpa using hj)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, anyBelow_eq_true] at h1
  rcases h1 with h1 | ⟨i, hi, hx⟩
  · exfalso
    have : (comp 42 r₂T uTabs[j]! == comp 42 uTabs[j]! r₂T) = true :=
      ((tabRep_r₂.comp hra).beq_iff (hra.comp tabRep_r₂)).2 hcomm
    simp only [this] at h1
    exact absurd h1 (by simp)
  · obtain ⟨x, hxrep⟩ := exists_rep_uTabs (i := i) hi
    refine ⟨x, ⟨_, getElem!_mem hi, hxrep⟩, ?_⟩
    have hinv : r₂⁻¹ = r₂ := inv_eq_of_mul_eq_one_right r₂_sq
    have hrep4 : TabRep (comp 42 (comp 42 (comp 42 r₂T uTabs[i]!) r₂T) uTabs[i]!)
        (r₂ * x * r₂ * x) := ((tabRep_r₂.comp hxrep).comp tabRep_r₂).comp hxrep
    rw [hinv]
    exact (hrep4.eq_iff hra).1 hx

theorem modelA2 :
    ∃ a₀ z : Equiv.Perm (Fin 42),
    (1 : Equiv.Perm (Fin 42)) ∈ USet ∧ (∀ a ∈ USet, ∀ b ∈ USet, a * b ∈ USet) ∧
    (∀ a ∈ USet, a * a = 1) ∧ (∀ p ∈ PSet, ∀ a ∈ USet, p * a * p⁻¹ ∈ USet) ∧
    (∀ a ∈ USet, r₂ * a * r₂⁻¹ ∈ USet) ∧ USet ⊆ PSet ∧ (∀ p ∈ PSet, p ∈ S) ∧
    a₀ ∈ USet ∧ a₀ ≠ 1 ∧ a₀ ∈ C₂ ∧ (∀ a ∈ USet, a ≠ 1 → ∃ p ∈ PSet, a = p * a₀ * p⁻¹) ∧
    z ∈ PSet ∧ z ∈ C₂ ∧ z * z * z = 1 ∧ (∀ a ∈ USet, z * a = a * z → a = 1) ∧
    (∀ k ∈ C₂, k * k = 1 → ∃ k' ∈ C₂, k' * k * k'⁻¹ ∈ USet) ∧
    (∀ a ∈ USet, r₂ * a = a * r₂ → ∃ x ∈ USet, r₂ * x * r₂⁻¹ * x = a) := by
  obtain ⟨a₀, hrep, ha₀U, ha₀1, ha₀C⟩ := exists_a0
  obtain ⟨z, hzP, hzC, hz3, hzfpf⟩ := exists_z
  exact ⟨a₀, z, U_one, fun _ ha _ hb => U_mul ha hb, fun _ ha => (U_sound ha).2.2,
    fun _ hp _ ha => U_conj hp ha, fun _ ha => U_r ha, U_subset_P, fun _ hp => hp.1, ha₀U, ha₀1,
    ha₀C, fun _ ha ha1 => trans_a0 hrep ha ha1, hzP, hzC, hz3, hzfpf,
    fun _ hk hk2 => red_C₂ hk hk2, fun _ ha hc => wit_r ha hc⟩

end CFSG.QuasithinUnique.Id2519.Tab.A2
