module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylow

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.Sporadic.HeldB CFSG.Monster.B.Co2

abbrev hfTGen32 : ℕ → Equiv.Perm (Fin 32) := resGen hfDelta32_points hfT_preserves

theorem tabRep_hfTTabs32 : ∀ j < hfTTabs32.size, TabRep hfTTabs32[j]! (hfTGen32 j) :=
  tabRep_resGen hfDelta32_points hfT_preserves fun j hj => (tabRep_hfTTabs j hj).2

theorem range_hfPhiT : hfPhiT.range = genGroup 32 hfTTabs32 hfTGen32 :=
  range_restrHom_eq hfDelta32_points hfT_preserves

theorem enumerates_genT32 : Enumerates (genGroup 32 hfTTabs32 hfTGen32) hfTEnum32.tabs.toList :=
  range_hfPhiT ▸ enumerates_hfPhiT

theorem hfPhiT_eq (t : hfT) : hfPhiT t = hfPhi ⟨t, hfT_le_hfT0 t.2⟩ := by
  ext k
  have h1 := hfDelta32_points.pt_restrHom hfT hfT_preserves t k
  have h2 := hfDelta32_points.pt_restrHom hfT0 hfT0_preserves ⟨t, hfT_le_hfT0 t.2⟩ k
  exact congrArg Fin.val (hfDelta32_points.pt_injective (h1.trans h2.symm))

theorem hfPhi_mul_comm_iff (a b : hfT0) :
    hfPhi a * hfPhi b = hfPhi b * hfPhi a ↔ (a : Equiv.Perm (Fin 8330)) * b = b * a := by
  rw [← map_mul, ← map_mul, hfPhi_injective.eq_iff, Subtype.ext_iff, Subgroup.coe_mul,
    Subgroup.coe_mul]

theorem hfPhi_eq_iff (a b : hfT0) :
    hfPhi a = hfPhi b ↔ (a : Equiv.Perm (Fin 8330)) = b := by
  rw [hfPhi_injective.eq_iff, Subtype.ext_iff]

theorem hfPhi_sq_iff (a : hfT0) :
    hfPhi a * hfPhi a = 1 ↔ (a : Equiv.Perm (Fin 8330)) * a = 1 := by
  rw [← map_mul, ← map_one hfPhi, hfPhi_injective.eq_iff, Subtype.ext_iff, Subgroup.coe_mul,
    OneMemClass.coe_one]

theorem hfPhi_eq_one_iff (a : hfT0) : hfPhi a = 1 ↔ (a : Equiv.Perm (Fin 8330)) = 1 := by
  rw [← map_one hfPhi, hfPhi_injective.eq_iff, Subtype.ext_iff, OneMemClass.coe_one]

theorem exists_hfT_of_mem_range {σ : Equiv.Perm (Fin 32)} (hσ : σ ∈ hfPhiT.range) :
    ∃ t : hfT, hfPhi ⟨t, hfT_le_hfT0 t.2⟩ = σ := by
  obtain ⟨t, rfl⟩ := hσ
  exact ⟨t, (hfPhiT_eq t).symm⟩

theorem card_center_hfT : Nat.card (center hfT) = 2 := by
  let e : hfT ≃* hfPhiT.range := MonoidHom.ofInjective hfPhiT_injective
  have h1 : (center hfT).map e.toMonoidHom = center hfPhiT.range := Subgroup.map_center_eq e
  have h0 : Nat.card ((center hfT).map e.toMonoidHom) = Nat.card (center hfT) :=
    Subgroup.card_map_of_injective (f := e.toMonoidHom) (by exact e.injective)
  rw [← h0, h1]
  have h2 : Nat.card (center hfPhiT.range) =
      Nat.card (center (genGroup 32 hfTTabs32 hfTGen32)) := by
    rw [range_hfPhiT]
  rw [h2, card_center_eq_of_enumerates tabRep_hfTTabs32 enumerates_genT32]
  exact hfSylow_check32.2.2.2.2.1

theorem hfTL_mem_hfT {j : ℕ} (hj : j < 5) : hfTL j ∈ hfT :=
  subset_closure ⟨j, by rw [hfTTabs_size]; exact hj, rfl⟩

theorem hfWord_mem {w : List ℕ} (hw : ∀ j ∈ w, j < 5) : (w.map hfTL).prod ∈ hfT := by
  refine hfT.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact hfTL_mem_hfT (hw j hj)

theorem hfTGen32_eq {j : ℕ} (hj : j < 5) : hfTGen32 j = hfPhiT ⟨hfTL j, hfTL_mem_hfT hj⟩ :=
  resGen_of_lt hfDelta32_points hfT_preserves (by rw [hfTTabs_size]; exact hj)

theorem hfPhiT_word : ∀ (w : List ℕ) (hw : ∀ j ∈ w, j < 5),
    hfPhiT ⟨(w.map hfTL).prod, hfWord_mem hw⟩ = (w.map hfTGen32).prod
  | [], _ => by
    have e : (⟨([] : List ℕ).map hfTL |>.prod, hfWord_mem (w := []) (by simp)⟩ : hfT) = 1 :=
      Subtype.ext (by simp)
    rw [e, map_one]
    simp
  | j :: w, hw => by
    have hj : j < 5 := hw j List.mem_cons_self
    have hw' : ∀ i ∈ w, i < 5 := fun i hi => hw i (List.mem_cons_of_mem _ hi)
    have e : (⟨((j :: w).map hfTL).prod, hfWord_mem hw⟩ : hfT) =
        ⟨hfTL j, hfTL_mem_hfT hj⟩ * ⟨(w.map hfTL).prod, hfWord_mem hw'⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, hfPhiT_word w hw', List.map_cons, List.prod_cons, hfTGen32_eq hj]

theorem tabRep_hfWord {w : List ℕ} (hw : ∀ j ∈ w, j < 5) :
    TabRep (wordTabS 32 hfTTabs32 w) (hfPhiT ⟨(w.map hfTL).prod, hfWord_mem hw⟩) := by
  rw [hfPhiT_word w hw]
  exact tabRep_wordTabS tabRep_hfTTabs32 w fun j hj => by
    rw [show hfTTabs32.size = 5 by simp [hfTTabs32, hfTTabs_size]]
    exact hw j hj

@[expose] def hfE (i : ℕ) : Equiv.Perm (Fin 8330) := ((hfEWords.getD i []).map hfTL).prod

theorem hfEWords_lt {i : ℕ} (hi : i < 6) : ∀ j ∈ hfEWords.getD i [], j < 5 :=
  hfSylow_check.2.2.2.2.2.2.1 i hi

theorem hfE_mem {i : ℕ} (hi : i < 6) : hfE i ∈ hfT := hfWord_mem (hfEWords_lt hi)

@[expose] def hfEgrp : Subgroup (Equiv.Perm (Fin 8330)) := closure {g | ∃ i < 6, hfE i = g}

theorem hfEgrp_le : hfEgrp ≤ hfT := by
  rw [hfEgrp, closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact hfE_mem hi

@[expose] def hfEGen32 (i : ℕ) : Equiv.Perm (Fin 32) :=
  if hi : i < 6 then hfPhiT ⟨hfE i, hfE_mem hi⟩ else 1

theorem hfETabs32_size : hfETabs32.size = 6 := by simp [hfETabs32]

theorem tabRep_hfETabs32 : ∀ i < hfETabs32.size, TabRep hfETabs32[i]! (hfEGen32 i) := by
  intro i hi
  have hi6 : i < 6 := hfETabs32_size ▸ hi
  rw [hfETabs32, getElem!_pos _ i (by simpa using hi6), Array.getElem_ofFn]
  simp only [hfEGen32, hi6, ↓reduceDIte]
  exact tabRep_hfWord (hfEWords_lt hi6)

@[expose] def hfEgrpT : Subgroup hfT := closure {t | ∃ i < 6, (t : Equiv.Perm (Fin 8330)) = hfE i}

theorem map_hfEgrpT : hfEgrpT.map hfT.subtype = hfEgrp := by
  rw [hfEgrpT, MonoidHom.map_closure, hfEgrp]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype]
  constructor
  · rintro ⟨t, ⟨i, hi, hti⟩, rfl⟩
    exact ⟨i, hi, hti.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨hfE i, hfE_mem hi⟩, ⟨i, hi, rfl⟩, rfl⟩

theorem map_hfPhiT_hfEgrpT : hfEgrpT.map hfPhiT = genGroup 32 hfETabs32 hfEGen32 := by
  rw [hfEgrpT, MonoidHom.map_closure, genGroup, hfETabs32_size]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ⟨i, hi, hti⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [hfEGen32, hi, ↓reduceDIte]
    exact congrArg hfPhiT (Subtype.ext hti.symm)
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨hfE i, hfE_mem hi⟩, ⟨i, hi, rfl⟩, by simp only [hfEGen32, hi, ↓reduceDIte]⟩

theorem enumerates_genE32 : Enumerates (genGroup 32 hfETabs32 hfEGen32) hfEEnum32.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_hfETabs32) (genGroup_hgens tabRep_hfETabs32)
    hfSylow_check32.2.2.2.2.2.1

theorem hfE_comm {i j : ℕ} (hi : i < 6) (hj : j < 6) : hfE i * hfE j = hfE j * hfE i := by
  have hti := tabRep_hfETabs32 i (hfETabs32_size ▸ hi)
  have htj := tabRep_hfETabs32 j (hfETabs32_size ▸ hj)
  have h := hfSylow_check32.2.2.2.2.2.2.2.1 i hi j hj
  rw [(hti.comp htj).eq_iff (htj.comp hti)] at h
  simp only [hfEGen32, hi, hj, ↓reduceDIte, hfPhiT_eq] at h
  exact (hfPhi_mul_comm_iff ⟨_, hfT_le_hfT0 (hfE_mem hi)⟩ ⟨_, hfT_le_hfT0 (hfE_mem hj)⟩).1 h

theorem hfE_sq {i : ℕ} (hi : i < 6) : hfE i * hfE i = 1 := by
  have hti := tabRep_hfETabs32 i (hfETabs32_size ▸ hi)
  have h := hfSylow_check32.2.2.2.2.2.2.2.2.1 i hi
  rw [(hti.comp hti).eq_iff TabRep.idTab] at h
  simp only [hfEGen32, hi, ↓reduceDIte, hfPhiT_eq] at h
  exact (hfPhi_sq_iff ⟨_, hfT_le_hfT0 (hfE_mem hi)⟩).1 h

theorem hfEgrp_facts : hfEgrp ≤ hfT ∧ hfT ≤ normalizer (hfEgrp : Set (Equiv.Perm (Fin 8330))) ∧
    (∀ x ∈ hfEgrp, ∀ y ∈ hfEgrp, x * y = y * x) ∧ (∀ x ∈ hfEgrp, x * x = 1) ∧
    Nat.card hfEgrp = 64 := by
  have hS : ∀ a ∈ {g | ∃ i < 6, hfE i = g}, ∀ b ∈ {g | ∃ i < 6, hfE i = g}, a * b = b * a := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact hfE_comm hi hj
  have hcard : Nat.card hfEgrp = 64 := by
    rw [← map_hfEgrpT, Subgroup.card_map_of_injective hfT.subtype_injective,
      ← Subgroup.card_map_of_injective hfPhiT_injective, map_hfPhiT_hfEgrpT,
      enumerates_genE32.card, Array.length_toList, hfSylow_check32.2.2.2.2.2.2.1]
  refine ⟨hfEgrp_le, ?_, closure_comm_of_pairwise hS,
    closure_sq_of_pairwise hS (by rintro _ ⟨i, hi, rfl⟩; exact hfE_sq hi), hcard⟩
  have hnorm := le_normalizer_of_normalOK tabRep_hfTTabs32 tabRep_hfETabs32 enumerates_genE32
    hfSylow_check32.2.2.2.2.2.2.2.2.2.1
  have hmemE : ∀ t : hfT, (t : Equiv.Perm (Fin 8330)) ∈ hfEgrp ↔ t ∈ hfEgrpT := by
    intro t
    rw [← map_hfEgrpT]
    constructor
    · rintro ⟨x, hx, hxt⟩
      have : x = t := Subtype.ext hxt
      rwa [this] at hx
    · intro h
      exact ⟨t, h, rfl⟩
  have hconj : ∀ t ∈ hfT, ∀ e ∈ hfEgrp, t * e * t⁻¹ ∈ hfEgrp := by
    intro t ht e he
    have heT := hfEgrp_le he
    have hφt : hfPhiT ⟨t, ht⟩ ∈ genGroup 32 hfTTabs32 hfTGen32 := by
      rw [← range_hfPhiT]; exact ⟨_, rfl⟩
    have hφe : hfPhiT ⟨e, heT⟩ ∈ genGroup 32 hfETabs32 hfEGen32 := by
      rw [← map_hfPhiT_hfEgrpT]
      exact ⟨⟨e, heT⟩, (hmemE ⟨e, heT⟩).1 he, rfl⟩
    have h1 := (mem_normalizer_iff.1 (hnorm hφt) _).1 hφe
    rw [← map_mul, ← map_inv, ← map_mul, ← map_hfPhiT_hfEgrpT,
      Subgroup.mem_map_iff_mem hfPhiT_injective, ← hmemE] at h1
    simpa using h1
  intro t ht
  rw [mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact hconj t ht e he
  · intro he
    have := hconj t⁻¹ (hfT.inv_mem ht) _ he
    simpa [mul_assoc] using this

theorem hfOuterE8Check_spec {m : ℕ} {TT A : Array Tab} (h : hfOuterE8Check m TT A = true)
    {i j : ℕ} (hi : i < A.size) (hj : j < TT.size)
    (hnf : found (indexOf TT) TT A[i]! = false) (ha2 : comp m A[i]! A[i]! = idTab m)
    (hb2 : comp m TT[j]! TT[j]! = idTab m) (hab : comp m TT[j]! A[i]! = comp m A[i]! TT[j]!) :
    ∃ i₁ j₁ k₁, hfTripleOK m TT A[i]! TT[j]! i₁ j₁ k₁ = true := by
  rw [hfOuterE8Check, allBelow_eq_true] at h
  have h1 := h i hi
  rw [hnf, ha2, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.false_or,
    allBelow_eq_true] at h1
  have h2 := h1 j hj
  rw [hb2, hab, beq_self_eq_true, beq_self_eq_true, Bool.not_true, Bool.false_or,
    Bool.false_or] at h2
  rw [hfPairOK] at h2
  split at h2
  · exact ⟨_, _, _, h2⟩
  · exact absurd h2 Bool.false_ne_true

theorem hfTripleOK_spec {m : ℕ} {TT : Array Tab} {a b : Tab} {i j k : ℕ}
    (h : hfTripleOK m TT a b i j k = true) :
    i < TT.size ∧ j < TT.size ∧ k < TT.size ∧ hfE8OK m TT[i]! TT[j]! TT[k]! = true ∧
      (comp m TT[i]! a = comp m a TT[i]! ∧ comp m TT[i]! b = comp m b TT[i]!) ∧
      (comp m TT[j]! a = comp m a TT[j]! ∧ comp m TT[j]! b = comp m b TT[j]!) ∧
      (comp m TT[k]! a = comp m a TT[k]! ∧ comp m TT[k]! b = comp m b TT[k]!) := by
  simp only [hfTripleOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    beq_iff_eq, Bool.and_true] at h
  obtain ⟨⟨⟨⟨hi, hj⟩, hk⟩, he⟩, h1, h2, h3⟩ := h
  exact ⟨hi, hj, hk, he, h1, h2, h3⟩

theorem hfE8OK_spec {m : ℕ} {x y z : Tab} (h : hfE8OK m x y z = true) :
    comp m x x = idTab m ∧ comp m y y = idTab m ∧ comp m z z = idTab m ∧
      comp m x y = comp m y x ∧ comp m x z = comp m z x ∧ comp m y z = comp m z y ∧
      x ≠ idTab m ∧ y ≠ idTab m ∧ y ≠ x ∧ z ≠ idTab m ∧ z ≠ x ∧ z ≠ y ∧ z ≠ comp m x y := by
  simp only [hfE8OK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq] at h
  tauto

theorem hfPhi_comm_of_tab {t s : Tab} (u v : hfT0) (ht : TabRep t (hfPhi u))
    (hs : TabRep s (hfPhi v)) (h : comp 32 t s = comp 32 s t) :
    (u : Equiv.Perm (Fin 8330)) * v = v * u :=
  (hfPhi_mul_comm_iff u v).1 (((ht.comp hs).eq_iff (hs.comp ht)).1 h)

theorem hfPhi_sq_of_tab {t : Tab} (u : hfT0) (ht : TabRep t (hfPhi u))
    (h : comp 32 t t = idTab 32) : (u : Equiv.Perm (Fin 8330)) * u = 1 :=
  (hfPhi_sq_iff u).1 (((ht.comp ht).eq_iff TabRep.idTab).1 h)

theorem hfPhi_ne_one_of_tab {t : Tab} (u : hfT0) (ht : TabRep t (hfPhi u))
    (h : t ≠ idTab 32) : (u : Equiv.Perm (Fin 8330)) ≠ 1 := fun he =>
  h ((ht.eq_iff TabRep.idTab).2 ((hfPhi_eq_one_iff u).2 he))

theorem hfPhi_ne_of_tab {t s : Tab} (u v : hfT0) (ht : TabRep t (hfPhi u))
    (hs : TabRep s (hfPhi v)) (h : t ≠ s) : (u : Equiv.Perm (Fin 8330)) ≠ v := fun he =>
  h ((ht.eq_iff hs).2 ((hfPhi_eq_iff u v).2 he))

theorem hfOuter_e8_aux {A TT : Array Tab} (hEA : Enumerates hfPhi.range A.toList)
    (hET : Enumerates hfPhiT.range TT.toList) (hcheck : hfOuterE8Check 32 TT A = true)
    {a a₁ : Equiv.Perm (Fin 8330)} (ha : a ∈ hfT0) (haP : a ∉ heP) (ha2 : a * a = 1)
    (ha₁ : a₁ ∈ hfT) (ha₁2 : a₁ * a₁ = 1) (hc : a₁ * a = a * a₁) :
    ∃ F : Subgroup (Equiv.Perm (Fin 8330)),
      F ≤ hfT0 ⊓ heP ⊓ centralizer {a} ⊓ centralizer {a₁} ∧
      (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8 := by
  obtain ⟨i, hi, hti⟩ := hEA.exists_pos (⟨⟨a, ha⟩, rfl⟩ : hfPhi ⟨a, ha⟩ ∈ hfPhi.range)
  obtain ⟨j, hj, htj⟩ := hET.exists_pos
    (⟨⟨a₁, ha₁⟩, rfl⟩ : hfPhiT ⟨a₁, ha₁⟩ ∈ hfPhiT.range)
  rw [hfPhiT_eq] at htj
  have hnf : found (indexOf TT) TT A[i]! = false := by
    by_contra hf
    rw [Bool.not_eq_false] at hf
    obtain ⟨σ, hσ, hrep⟩ := hET.sound _ (mem_of_found hf)
    obtain ⟨t, rfl⟩ := exists_hfT_of_mem_range hσ
    have heq : a = t := (hfPhi_eq_iff ⟨a, ha⟩ ⟨t, hfT_le_hfT0 t.2⟩).1 (hti.perm_eq hrep)
    exact haP (heq ▸ hfT_le_heP t.2)
  have hA2 : comp 32 A[i]! A[i]! = idTab 32 :=
    ((hti.comp hti).eq_iff TabRep.idTab).2 ((hfPhi_sq_iff ⟨a, ha⟩).2 ha2)
  have hB2 : comp 32 TT[j]! TT[j]! = idTab 32 :=
    ((htj.comp htj).eq_iff TabRep.idTab).2 ((hfPhi_sq_iff ⟨a₁, hfT_le_hfT0 ha₁⟩).2 ha₁2)
  have hAB : comp 32 TT[j]! A[i]! = comp 32 A[i]! TT[j]! :=
    ((htj.comp hti).eq_iff (hti.comp htj)).2
      ((hfPhi_mul_comm_iff ⟨a₁, hfT_le_hfT0 ha₁⟩ ⟨a, ha⟩).2 hc)
  obtain ⟨i₁, j₁, k₁, hok⟩ := hfOuterE8Check_spec hcheck hi hj hnf hA2 hB2 hAB
  obtain ⟨hi₁, hj₁, hk₁, he8, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hfTripleOK_spec hok
  have hget : ∀ k < TT.size, ∃ t : hfT, TabRep TT[k]! (hfPhi ⟨t, hfT_le_hfT0 t.2⟩) := by
    intro k hk
    obtain ⟨σ, hσ, hrep⟩ := hET.exists_elt hk
    obtain ⟨t, rfl⟩ := exists_hfT_of_mem_range hσ
    exact ⟨t, hrep⟩
  obtain ⟨f₁, hf₁⟩ := hget i₁ hi₁
  obtain ⟨f₂, hf₂⟩ := hget j₁ hj₁
  obtain ⟨f₃, hf₃⟩ := hget k₁ hk₁
  obtain ⟨hx2, hy2, hz2, hxy, hxz, hyz, hx1, hy1, hyx, hz1, hzx, hzy, hzxy⟩ := hfE8OK_spec he8
  have hzxy' : (f₃ : Equiv.Perm (Fin 8330)) ≠ f₁ * f₂ := by
    intro he
    apply hzxy
    rw [hf₃.eq_iff (hf₁.comp hf₂), ← map_mul]
    exact (hfPhi_eq_iff _ _).2 (by rw [Subgroup.coe_mul]; exact he)
  obtain ⟨hFc, hFs, hFcard⟩ := e8_closure (hfPhi_sq_of_tab _ hf₁ hx2) (hfPhi_sq_of_tab _ hf₂ hy2)
    (hfPhi_sq_of_tab _ hf₃ hz2) (hfPhi_comm_of_tab _ _ hf₁ hf₂ hxy)
    (hfPhi_comm_of_tab _ _ hf₁ hf₃ hxz) (hfPhi_comm_of_tab _ _ hf₂ hf₃ hyz)
    (hfPhi_ne_one_of_tab _ hf₁ hx1) (hfPhi_ne_one_of_tab _ hf₂ hy1)
    (hfPhi_ne_of_tab _ _ hf₂ hf₁ hyx) (hfPhi_ne_one_of_tab _ hf₃ hz1)
    (hfPhi_ne_of_tab _ _ hf₃ hf₁ hzx) (hfPhi_ne_of_tab _ _ hf₃ hf₂ hzy) hzxy'
  refine ⟨_, ?_, hFc, hFs, hFcard⟩
  rw [closure_le]
  have hmem : ∀ {t : Tab} (f : hfT), TabRep t (hfPhi ⟨f, hfT_le_hfT0 f.2⟩) →
      comp 32 t A[i]! = comp 32 A[i]! t → comp 32 t TT[j]! = comp 32 TT[j]! t →
      (f : Equiv.Perm (Fin 8330)) ∈ hfT0 ⊓ heP ⊓ centralizer {a} ⊓ centralizer {a₁} := by
    intro t f ht h1 h2
    refine mem_inf.2 ⟨mem_inf.2 ⟨mem_inf.2 ⟨hfT_le_hfT0 f.2, hfT_le_heP f.2⟩, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have := hfPhi_comm_of_tab ⟨(f : Equiv.Perm (Fin 8330)), hfT_le_hfT0 f.2⟩ ⟨a, ha⟩ ht hti h1
      simpa only using this
    · rw [mem_centralizer_singleton_iff]
      have := hfPhi_comm_of_tab ⟨(f : Equiv.Perm (Fin 8330)), hfT_le_hfT0 f.2⟩
        ⟨a₁, hfT_le_hfT0 ha₁⟩ ht htj h2
      simpa only using this
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact hmem f₁ hf₁ h1a h1b
  · exact hmem f₂ hf₂ h2a h2b
  · exact hmem f₃ hf₃ h3a h3b

theorem hfOuter_e8 {a a₁ : Equiv.Perm (Fin 8330)} (ha : a ∈ hfT0) (haP : a ∉ heP)
    (ha2 : orderOf a = 2) (ha₁ : a₁ ∈ hfT0 ⊓ heP) (ha₁2 : a₁ * a₁ = 1) (hc : a₁ * a = a * a₁) :
    ∃ F : Subgroup (Equiv.Perm (Fin 8330)),
      F ≤ hfT0 ⊓ heP ⊓ centralizer {a} ⊓ centralizer {a₁} ∧
      (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8 := by
  rw [hfT0_inf_heP] at ha₁
  have ha2' : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  exact hfOuter_e8_aux enumerates_hfPhi enumerates_hfPhiT
    hfSylow_check32.2.2.2.2.2.2.2.2.2.2 ha haP ha2' ha₁ ha₁2 hc

end CFSG.ComponentClassification.GrSLit.HeldFix
