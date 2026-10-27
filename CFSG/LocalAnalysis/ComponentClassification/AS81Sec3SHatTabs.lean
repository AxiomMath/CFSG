module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Census
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatClosedCert
import all CFSG.Fischer.F4

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Fischer CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

namespace Sec3Mod

open Census SHatClosed

theorem eq_one_of_sigma (g : MulAction.stabilizer OV N0) (h : sigma g = 1) : g = 1 := by
  refine Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective (linMap_ext fun i => ?_)))
  have hmem : (Pi.single i 1 : V₀) ∈ N0 := by
    intro j
    by_cases hij : j = i
    · subst hij
      rw [Pi.single_eq_same]
      decide
    · rw [Pi.single_eq_of_ne hij]
      decide
  have hfix := congrArg (fun p : Equiv.Perm (Fin 64) => p ⟨idx (Pi.single i 1), idx_lt hmem⟩) h
  simp only [Equiv.Perm.coe_one, id_eq] at hfix
  have e1 := bitsV_sigmaFun g ⟨idx (Pi.single i 1), idx_lt hmem⟩
  change bitsV (sigma g ⟨_, _⟩) = _ at e1
  rw [hfix, bitsV_idx hmem] at e1
  change ((g : OV) : V₀ ≃ₗ[F4] V₀) (Pi.single i 1) = (Pi.single i 1 : V₀)
  exact e1.symm

theorem sigma_injective : Function.Injective (sigma : MulAction.stabilizer OV N0 →* _) := by
  intro g g' h
  have h1 : sigma (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := eq_one_of_sigma _ h1
  calc g = g' * (g'⁻¹ * g) := by group
    _ = g' := by rw [h2, mul_one]

@[expose] noncomputable def tabOf (s : MulAction.stabilizer OV N0) : Tab :=
  Array.ofFn (n := 64) fun i => (sigma s i : ℕ)

theorem tabRep_tabOf (s : MulAction.stabilizer OV N0) : TabRep (tabOf s) (sigma s) := by
  refine ⟨Array.size_ofFn, fun i => ?_⟩
  rw [tabOf, getElem!_pos _ _ (by simp), Array.getElem_ofFn]

theorem tabOf_injective : Function.Injective tabOf := by
  intro s s' h
  apply sigma_injective
  have h1 := tabRep_tabOf s'
  rw [← h] at h1
  exact (tabRep_tabOf s).perm_eq h1

theorem tabOf_mul (s s' : MulAction.stabilizer OV N0) :
    comp 64 (tabOf s) (tabOf s') = tabOf (s * s') := by
  have h := (tabRep_tabOf s).comp (tabRep_tabOf s')
  rw [← map_mul] at h
  exact h.tab_eq (tabRep_tabOf _)

theorem tabOf_eq_iff {s s' : MulAction.stabilizer OV N0} : tabOf s = tabOf s' ↔ s = s' :=
  tabOf_injective.eq_iff

theorem mem_invL {s : MulAction.stabilizer OV N0} (h2 : s * s = 1) (h1 : s ≠ 1)
    (ht : tabOf s ∈ lEnum.tabs.toList) : tabOf s ∈ invL.toList := by
  have e1 : comp 64 (tabOf s) (tabOf s) = idTab 64 := by
    rw [tabOf_mul, h2]
    exact (tabRep_tabOf 1).tab_eq (by rw [map_one]; exact TabRep.idTab)
  have e2 : ¬ tabOf s = idTab 64 := by
    intro h
    apply h1
    apply sigma_injective
    rw [map_one]
    exact (tabRep_tabOf s).perm_eq (h ▸ TabRep.idTab)
  rw [invL, Array.toList_filter, List.mem_filter]
  refine ⟨ht, ?_⟩
  simp [isInvol, e1, e2]

theorem fixCount_eq {t : Tab} {p : Equiv.Perm (Fin 64)} (ht : TabRep t p) :
    fixCount t = (Finset.univ.filter fun i : Fin 64 => p i = i).card := by
  rw [fixCount, countBelow_eq]
  symm
  refine Finset.card_bij (fun (i : Fin 64) _ => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
    rw [ht.apply i, hi.2]
    simp
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨⟨k, hk.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Fin.ext ?_⟩
    have h := ht.apply ⟨k, hk.1⟩
    simp only [beq_iff_eq] at hk
    exact h.symm.trans hk.2

theorem fixCount4_eq {t₁ t₂ t₃ t₄ : Tab} {p₁ p₂ p₃ p₄ : Equiv.Perm (Fin 64)} (h₁ : TabRep t₁ p₁)
    (h₂ : TabRep t₂ p₂) (h₃ : TabRep t₃ p₃) (h₄ : TabRep t₄ p₄) :
    fixCount4 t₁ t₂ t₃ t₄ =
      (Finset.univ.filter fun i : Fin 64 => p₁ i = i ∧ p₂ i = i ∧ p₃ i = i ∧ p₄ i = i).card := by
  rw [fixCount4, countBelow_eq]
  symm
  refine Finset.card_bij (fun (i : Fin 64) _ => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
    rw [h₁.apply i, h₂.apply i, h₃.apply i, h₄.apply i, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2]
    simp
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨⟨k, hk.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨hk1, ⟨⟨e1, e2⟩, e3⟩, e4⟩ := hk
    refine ⟨Finset.mem_univ _, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
    · exact (h₁.apply ⟨k, hk1⟩).symm.trans e1
    · exact (h₂.apply ⟨k, hk1⟩).symm.trans e2
    · exact (h₃.apply ⟨k, hk1⟩).symm.trans e3
    · exact (h₄.apply ⟨k, hk1⟩).symm.trans e4

theorem cm_eq_true {i j : ℕ} (hi : i < invL.size) (hj : j < invL.size) :
    cm i j = true ↔ comp 64 invL[i]! invL[j]! = comp 64 invL[j]! invL[i]! := by
  have hs : commMat.size = invL.size := Array.size_map
  have hi' : i < commMat.size := hs ▸ hi
  unfold cm
  rw [getElem!_pos commMat i hi']
  have e1 : commMat[i] = invL.map fun b => comp 64 invL[i] b == comp 64 b invL[i] := by
    simp only [commMat, Array.getElem_map]
  have hj' : j < (invL.map fun b => comp 64 invL[i] b == comp 64 b invL[i]).size := by
    rw [Array.size_map]; exact hj
  rw [e1, getElem!_pos _ j hj', Array.getElem_map, getElem!_pos invL i hi, getElem!_pos invL j hj,
    beq_iff_eq]

theorem mem_centIdx {i j : ℕ} (hi : i < invL.size) :
    j ∈ (centIdx[i]!).toList ↔ j < invL.size ∧ cm i j = true := by
  have hs : centIdx.size = invL.size := by simp [centIdx]
  have hi' : i < centIdx.size := hs ▸ hi
  rw [getElem!_pos centIdx i hi']
  simp [centIdx]

@[expose] noncomputable def posL (s : MulAction.stabilizer OV N0) : ℕ :=
  open Classical in
  if h : tabOf s ∈ invL.toList then Classical.choose (exists_getElem!_of_mem h) else 0

theorem posL_spec {s : MulAction.stabilizer OV N0} (h : tabOf s ∈ invL.toList) :
    posL s < invL.size ∧ invL[posL s]! = tabOf s := by
  rw [posL, dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec (exists_getElem!_of_mem h)

theorem span2_tabOf (a b : MulAction.stabilizer OV N0) :
    span2 (tabOf a) (tabOf b) = #[tabOf a, tabOf b, tabOf (a * b)] := by
  rw [span2, tabOf_mul]

theorem contains_span2 {a b c : MulAction.stabilizer OV N0} :
    (span2 (tabOf a) (tabOf b)).contains (tabOf c) = true ↔ c = a ∨ c = b ∨ c = a * b := by
  rw [span2_tabOf]
  simp [tabOf_eq_iff]

theorem span3_tabOf (a b c : MulAction.stabilizer OV N0) :
    span3 (tabOf a) (tabOf b) (tabOf c) = #[tabOf a, tabOf b, tabOf (a * b), tabOf c,
      tabOf (a * c), tabOf (b * c), tabOf (a * b * c)] := by
  rw [span3, span2_tabOf]
  simp [tabOf_mul]

theorem contains_span3 {a b c d : MulAction.stabilizer OV N0} :
    (span3 (tabOf a) (tabOf b) (tabOf c)).contains (tabOf d) = true ↔
      d = a ∨ d = b ∨ d = a * b ∨ d = c ∨ d = a * c ∨ d = b * c ∨ d = a * b * c := by
  rw [span3_tabOf]
  simp [tabOf_eq_iff]

theorem cm_posL {s s' : MulAction.stabilizer OV N0} (h : tabOf s ∈ invL.toList)
    (h' : tabOf s' ∈ invL.toList) (hc : s * s' = s' * s) : cm (posL s) (posL s') = true := by
  obtain ⟨hp, he⟩ := posL_spec h
  obtain ⟨hp', he'⟩ := posL_spec h'
  rw [cm_eq_true hp hp', he, he', tabOf_mul, tabOf_mul, hc]

@[expose] def re (v : V₀) : V₀ := fun i => ⟨⟨(v i).code.val % 2, by omega⟩⟩

@[expose] def im (v : V₀) : V₀ := fun i => ⟨⟨(v i).code.val / 2, by omega⟩⟩

theorem re_mem (v : V₀) : re v ∈ N0 := fun _ => Nat.mod_lt _ (by norm_num)

theorem im_mem (v : V₀) : im v ∈ N0 := fun i => by
  change (v i).code.val / 2 < 2
  omega

theorem F4_decomp : ∀ c : F4,
    (⟨⟨c.code.val % 2, by omega⟩⟩ : F4) + F4.ω * ⟨⟨c.code.val / 2, by omega⟩⟩ = c := by
  decide

theorem re_add_im (v : V₀) : re v + F4.ω • im v = v :=
  funext fun i => F4_decomp (v i)

theorem re_im_of_mem {y₁ y₂ : V₀} (h₁ : y₁ ∈ N0) (h₂ : y₂ ∈ N0) :
    re (y₁ + F4.ω • y₂) = y₁ ∧ im (y₁ + F4.ω • y₂) = y₂ := by
  have key : ∀ a b : F4, a.code.val < 2 → b.code.val < 2 →
      (⟨⟨(a + F4.ω * b).code.val % 2, by omega⟩⟩ : F4) = a ∧
        (⟨⟨(a + F4.ω * b).code.val / 2, by omega⟩⟩ : F4) = b := by decide
  constructor <;> funext i
  · exact (key (y₁ i) (y₂ i) (h₁ i) (h₂ i)).1
  · exact (key (y₁ i) (y₂ i) (h₁ i) (h₂ i)).2

theorem fix_iff (x : MulAction.stabilizer OV N0) (v : V₀) :
    ((x : OV) : V₀ ≃ₗ[F4] V₀) v = v ↔ ((x : OV) : V₀ ≃ₗ[F4] V₀) (re v) = re v ∧
      ((x : OV) : V₀ ≃ₗ[F4] V₀) (im v) = im v := by
  constructor
  · intro h
    have e1 : ((x : OV) : V₀ ≃ₗ[F4] V₀) (re v) + F4.ω • ((x : OV) : V₀ ≃ₗ[F4] V₀) (im v) =
        re v + F4.ω • im v := by
      rw [← map_smul, ← map_add, re_add_im, h]
    have h1 := re_im_of_mem (apply_mem_N0 x.2 (re_mem v)) (apply_mem_N0 x.2 (im_mem v))
    have h2 := re_im_of_mem (re_mem v) (im_mem v)
    rw [e1] at h1
    exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
  · rintro ⟨h1, h2⟩
    conv_lhs => rw [← re_add_im v]
    rw [map_add, map_smul, h1, h2, re_add_im]

theorem card_fix_V₀ (X : Set (MulAction.stabilizer OV N0)) :
    Nat.card {v : V₀ // ∀ x ∈ X, ((x : OV) : V₀ ≃ₗ[F4] V₀) v = v} =
      Nat.card {v : V₀ // v ∈ N0 ∧ ∀ x ∈ X, ((x : OV) : V₀ ≃ₗ[F4] V₀) v = v} ^ 2 := by
  rw [sq, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun v => (⟨re v.1, re_mem _, fun x hx => ((fix_iff x v.1).mp (v.2 x hx)).1⟩,
        ⟨im v.1, im_mem _, fun x hx => ((fix_iff x v.1).mp (v.2 x hx)).2⟩)
      invFun := fun p => ⟨p.1.1 + F4.ω • p.2.1, fun x hx => by
        rw [map_add, map_smul, p.1.2.2 x hx, p.2.2.2 x hx]⟩
      left_inv := fun v => Subtype.ext (re_add_im v.1)
      right_inv := fun p => Prod.ext (Subtype.ext (re_im_of_mem p.1.2.1 p.2.2.1).1)
        (Subtype.ext (re_im_of_mem p.1.2.1 p.2.2.1).2) }

theorem sigma_fix_iff (x : MulAction.stabilizer OV N0) (i : Fin 64) :
    sigma x i = i ↔ ((x : OV) : V₀ ≃ₗ[F4] V₀) (bitsV i) = bitsV i := by
  have e1 := bitsV_sigmaFun x i
  change bitsV (sigma x i) = _ at e1
  constructor
  · intro h
    rw [← e1, h]
  · intro h
    rw [h] at e1
    apply Fin.ext
    have := congrArg idx e1
    rwa [idx_bitsV (sigma x i).isLt, idx_bitsV i.isLt] at this

theorem card_fix_N0 (X : Set (MulAction.stabilizer OV N0)) :
    Nat.card {i : Fin 64 // ∀ x ∈ X, sigma x i = i} =
      Nat.card {v : V₀ // v ∈ N0 ∧ ∀ x ∈ X, ((x : OV) : V₀ ≃ₗ[F4] V₀) v = v} :=
  Nat.card_congr
    { toFun := fun i => ⟨bitsV i.1, bitsV_mem _, fun x hx => (sigma_fix_iff x i.1).mp (i.2 x hx)⟩
      invFun := fun v => ⟨⟨idx v.1, idx_lt v.2.1⟩, fun x hx => by
        rw [sigma_fix_iff, bitsV_idx v.2.1]
        exact v.2.2 x hx⟩
      left_inv := fun i => Subtype.ext (Fin.ext (idx_bitsV i.1.isLt))
      right_inv := fun v => Subtype.ext (bitsV_idx v.2.1) }

section Census


structure Indep4 (a b c d : MulAction.stabilizer OV N0) : Prop where
  memL : (a : OV) ∈ Lc ∧ (b : OV) ∈ Lc ∧ (c : OV) ∈ Lc ∧ (d : OV) ∈ Lc
  sq : a * a = 1 ∧ b * b = 1 ∧ c * c = 1 ∧ d * d = 1
  ne_one : a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ d ≠ 1
  comm : a * b = b * a ∧ a * c = c * a ∧ a * d = d * a ∧ b * c = c * b ∧ b * d = d * b ∧
    c * d = d * c
  hb : b ≠ a
  hc : ¬ (c = a ∨ c = b ∨ c = a * b)
  hd : ¬ (d = a ∨ d = b ∨ d = a * b ∨ d = c ∨ d = a * c ∨ d = b * c ∨ d = a * b * c)

theorem tabOf_mem {s : MulAction.stabilizer OV N0} (hs : (s : OV) ∈ Lc) :
    tabOf s ∈ lEnum.tabs.toList := by
  have hmem : sigma s ∈ Ls.map sigma := by
    rw [← map_Ls] at hs
    obtain ⟨s', hs', he⟩ := hs
    have e1 : s' = s := Subtype.ext he
    exact ⟨s', hs', by rw [e1]⟩
  obtain ⟨t, ht, hr⟩ := enumerates_L.complete _ hmem
  rwa [hr.tab_eq (tabRep_tabOf s)] at ht


theorem card_fix_of_invol {s : MulAction.stabilizer OV N0} (hs : (s : OV) ∈ Lc) (h2 : s * s = 1)
    (h1 : s ≠ 1) : (Finset.univ.filter fun i : Fin 64 => sigma s i = i).card = 16 := by
  have hmem := mem_invL h2 h1 (tabOf_mem hs)
  have hf := f1_check
  rw [f1OK, Array.all_eq_true'] at hf
  have h := hf _ (Array.mem_toList_iff.mp hmem)
  rw [beq_iff_eq] at h
  rw [← fixCount_eq (tabRep_tabOf s), h]

theorem card_fixV_of_invol {s : MulAction.stabilizer OV N0} (hs : (s : OV) ∈ Lc)
    (h2 : s * s = 1) (h1 : s ≠ 1) :
    Nat.card {v : V₀ // ((s : OV) : V₀ ≃ₗ[F4] V₀) v = v} = 256 := by
  have e1 := card_fix_V₀ {s}
  have e2 := card_fix_N0 {s}
  simp only [Set.mem_singleton_iff, forall_eq] at e1 e2
  rw [e1, ← e2, Nat.card_eq_fintype_card, Fintype.card_subtype, card_fix_of_invol hs h2 h1]
  norm_num

theorem card_fix4 {a b c d : MulAction.stabilizer OV N0} (h : Indep4 a b c d) :
    (Finset.univ.filter fun i : Fin 64 => sigma a i = i ∧ sigma b i = i ∧ sigma c i = i ∧
      sigma d i = i).card = 2 := by
  obtain ⟨⟨haL, hbL, hcL, hdL⟩, ⟨ha2, hb2, hc2, hd2⟩, ⟨ha1, hb1, hc1, hd1⟩,
    ⟨hab, hac, had, hbc, hbd, hcd⟩, hba, hcn, hdn⟩ := h
  have ma := mem_invL ha2 ha1 (tabOf_mem haL)
  have mb := mem_invL hb2 hb1 (tabOf_mem hbL)
  have mc := mem_invL hc2 hc1 (tabOf_mem hcL)
  have md := mem_invL hd2 hd1 (tabOf_mem hdL)
  obtain ⟨pa, ea⟩ := posL_spec ma
  obtain ⟨pb, eb⟩ := posL_spec mb
  obtain ⟨pc, ec⟩ := posL_spec mc
  obtain ⟨pd, ed⟩ := posL_spec md
  have hf := f3_check
  rw [f3OK, allBelow_eq_true] at hf
  have h1 := hf _ pa
  simp only [Array.all_eq_true', Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
  have h2 := h1 _ (Array.mem_toList_iff.mp ((mem_centIdx pa).mpr ⟨pb, cm_posL ma mb hab⟩))
  simp only [ea, eb, tabOf_eq_iff] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hba
  have h3 := h2 _ (Array.mem_toList_iff.mp ((mem_centIdx pa).mpr ⟨pc, cm_posL ma mc hac⟩))
  simp only [ec, contains_span2, cm_posL mb mc hbc] at h3
  rcases h3 with (h3 | h3) | h3
  · exact absurd h3 (by decide)
  · exact absurd h3 hcn
  have h4 := h3 _ (Array.mem_toList_iff.mp ((mem_centIdx pa).mpr ⟨pd, cm_posL ma md had⟩))
  simp only [ed, contains_span3, cm_posL mb md hbd, cm_posL mc md hcd] at h4
  rcases h4 with (h4 | h4) | h4
  · exact absurd h4 (by decide)
  · exact absurd h4 hdn
  rw [fixCount4_eq (tabRep_tabOf a) (tabRep_tabOf b) (tabRep_tabOf c) (tabRep_tabOf d)] at h4
  exact h4

theorem card_comm_le {a b c d : MulAction.stabilizer OV N0} (h : Indep4 a b c d)
    (X : Finset (MulAction.stabilizer OV N0))
    (hX : ∀ x ∈ X, (x : OV) ∈ Lc ∧ x * x = 1 ∧ x ≠ 1 ∧ x * a = a * x ∧ x * b = b * x ∧
      x * c = c * x ∧ x * d = d * x) : X.card ≤ 15 := by
  obtain ⟨⟨haL, hbL, hcL, hdL⟩, ⟨ha2, hb2, hc2, hd2⟩, ⟨ha1, hb1, hc1, hd1⟩,
    ⟨hab, hac, had, hbc, hbd, hcd⟩, hba, hcn, hdn⟩ := h
  have ma := mem_invL ha2 ha1 (tabOf_mem haL)
  have mb := mem_invL hb2 hb1 (tabOf_mem hbL)
  have mc := mem_invL hc2 hc1 (tabOf_mem hcL)
  have md := mem_invL hd2 hd1 (tabOf_mem hdL)
  obtain ⟨pa, ea⟩ := posL_spec ma
  obtain ⟨pb, eb⟩ := posL_spec mb
  obtain ⟨pc, ec⟩ := posL_spec mc
  obtain ⟨pd, ed⟩ := posL_spec md
  have hf := f2_check
  rw [f2OK, allBelow_eq_true] at hf
  have h1 := hf _ pa
  simp only [Array.all_eq_true', Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
  have h2 := h1 _ (Array.mem_toList_iff.mp ((mem_centIdx pa).mpr ⟨pb, cm_posL ma mb hab⟩))
  simp only [ea, eb, tabOf_eq_iff] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hba
  have h3 := h2 _ (Array.mem_toList_iff.mp ((mem_centIdx pa).mpr ⟨pc, cm_posL ma mc hac⟩))
  simp only [ec, contains_span2, cm_posL mb mc hbc] at h3
  rcases h3 with (h3 | h3) | h3
  · exact absurd h3 (by decide)
  · exact absurd h3 hcn
  have h4 := h3 _ (Array.mem_toList_iff.mp ((mem_centIdx pa).mpr ⟨pd, cm_posL ma md had⟩))
  simp only [ed, contains_span3, cm_posL mb md hbd, cm_posL mc md hcd] at h4
  rcases h4 with (h4 | h4) | h4
  · exact absurd h4 (by decide)
  · exact absurd h4 hdn
  set M := (centIdx[posL a]!).filter fun m => cm (posL b) m && cm (posL c) m && cm (posL d) m
    with hM
  have hsub : X.image posL ⊆ M.toList.toFinset := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hxL, hx2, hx1, hxa, hxb, hxc, hxd⟩ := hX x hx
    have mx := mem_invL hx2 hx1 (tabOf_mem hxL)
    rw [List.mem_toFinset, Array.toList_filter, List.mem_filter]
    refine ⟨(mem_centIdx pa).mpr ⟨(posL_spec mx).1, cm_posL ma mx hxa.symm⟩, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨cm_posL mb mx hxb.symm, cm_posL mc mx hxc.symm⟩, cm_posL md mx hxd.symm⟩
  have hinj : Set.InjOn posL X := by
    intro x hx y hy hxy
    obtain ⟨hxL, hx2, hx1, -⟩ := hX x hx
    obtain ⟨hyL, hy2, hy1, -⟩ := hX y hy
    have e1 := (posL_spec (mem_invL hx2 hx1 (tabOf_mem hxL))).2
    have e2 := (posL_spec (mem_invL hy2 hy1 (tabOf_mem hyL))).2
    rw [hxy] at e1
    exact tabOf_injective (e1.symm.trans e2)
  calc X.card = (X.image posL).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ M.toList.toFinset.card := Finset.card_le_card hsub
    _ ≤ M.toList.length := List.toFinset_card_le _
    _ = 15 := by rw [Array.length_toList]; exact h4

theorem exists_mem_not_mem {E : Subgroup OV} (X : Finset OV) (h : X.card < Nat.card E) :
    ∃ x ∈ E, x ∉ X := by
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set OV) ⊆ X := fun x hx => hcon x hx
  have h1 : Nat.card E ≤ X.card := by
    calc Nat.card E = (E : Set OV).ncard := (Nat.card_coe_set_eq _).symm
      _ ≤ (X : Set OV).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet X)
      _ = X.card := Set.ncard_coe_finset X
  omega

theorem exists_indep4 {E : Subgroup OV} (hEL : E ≤ Lc) (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : 8 < Nat.card E) :
    ∃ a b c d : MulAction.stabilizer OV N0, Indep4 a b c d ∧ (a : OV) ∈ E ∧ (b : OV) ∈ E ∧
      (c : OV) ∈ E ∧ (d : OV) ∈ E := by
  classical
  obtain ⟨a, ha, ha1⟩ := exists_mem_not_mem (E := E) {1}
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨b, hb, hb1⟩ := exists_mem_not_mem (E := E) {1, a}
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨c, hc, hc1⟩ := exists_mem_not_mem (E := E) {1, a, b, a * b}
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  have h8 : ({1, a, b, a * b, c, a * c, b * c, a * b * c} : Finset OV).card ≤ 8 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
        ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_four)))))))
  obtain ⟨d, hd, hd1⟩ := exists_mem_not_mem (E := E) {1, a, b, a * b, c, a * c, b * c, a * b * c}
    (lt_of_le_of_lt h8 hcard)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1 hc1 hd1
  set a' : MulAction.stabilizer OV N0 := ⟨a, Lc_le_stab (hEL ha)⟩
  set b' : MulAction.stabilizer OV N0 := ⟨b, Lc_le_stab (hEL hb)⟩
  set c' : MulAction.stabilizer OV N0 := ⟨c, Lc_le_stab (hEL hc)⟩
  set d' : MulAction.stabilizer OV N0 := ⟨d, Lc_le_stab (hEL hd)⟩
  have hne : ∀ {x y : MulAction.stabilizer OV N0}, (x : OV) ≠ y → x ≠ y := fun h e => h (e ▸ rfl)
  have hcm : ∀ {x y : MulAction.stabilizer OV N0}, (x : OV) * y = y * x → x * y = y * x :=
    fun h => Subtype.ext h
  refine ⟨a', b', c', d', ⟨⟨hEL ha, hEL hb, hEL hc, hEL hd⟩,
    ⟨Subtype.ext (hsq a ha), Subtype.ext (hsq b hb), Subtype.ext (hsq c hc),
      Subtype.ext (hsq d hd)⟩,
    ⟨hne ha1, hne hb1.1, hne hc1.1, hne hd1.1⟩,
    ⟨hcm (hcomm a ha b hb), hcm (hcomm a ha c hc), hcm (hcomm a ha d hd), hcm (hcomm b hb c hc),
      hcm (hcomm b hb d hd), hcm (hcomm c hc d hd)⟩, hne hb1.2, ?_, ?_⟩, ha, hb, hc, hd⟩
  · rintro (h | h | h)
    · exact hc1.2.1 (congrArg Subtype.val h)
    · exact hc1.2.2.1 (congrArg Subtype.val h)
    · exact hc1.2.2.2 (congrArg Subtype.val h)
  · rintro (h | h | h | h | h | h | h)
    · exact hd1.2.1 (congrArg Subtype.val h)
    · exact hd1.2.2.1 (congrArg Subtype.val h)
    · exact hd1.2.2.2.1 (congrArg Subtype.val h)
    · exact hd1.2.2.2.2.1 (congrArg Subtype.val h)
    · exact hd1.2.2.2.2.2.1 (congrArg Subtype.val h)
    · exact hd1.2.2.2.2.2.2.1 (congrArg Subtype.val h)
    · exact hd1.2.2.2.2.2.2.2 (congrArg Subtype.val h)

theorem card_le_sixteen {E : Subgroup OV} (hEL : E ≤ Lc) (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ 16 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨a, b, c, d, h4, haE, hbE, hcE, hdE⟩ := exists_indep4 hEL hsq hcomm (by omega)
  set Y := (Set.toFinite {x : MulAction.stabilizer OV N0 | (x : OV) ∈ E ∧ x ≠ 1}).toFinset
    with hY
  have hX := card_comm_le h4 Y fun x hx => by
    rw [hY, Set.Finite.mem_toFinset] at hx
    have hxE := hx.1
    refine ⟨hEL hxE, Subtype.ext (hsq _ hxE), hx.2, Subtype.ext (hcomm _ hxE _ haE),
      Subtype.ext (hcomm _ hxE _ hbE), Subtype.ext (hcomm _ hxE _ hcE),
      Subtype.ext (hcomm _ hxE _ hdE)⟩
  obtain ⟨x, hxE, hxY⟩ := exists_mem_not_mem (E := E) (insert 1 (Y.image Subtype.val))
    (lt_of_le_of_lt (Finset.card_insert_le _ _)
      (lt_of_le_of_lt (Nat.succ_le_succ (Finset.card_image_le.trans hX)) (by omega)))
  apply hxY
  rw [Finset.mem_insert, Finset.mem_image]
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · refine Or.inr ⟨⟨x, Lc_le_stab (hEL hxE)⟩, ?_, rfl⟩
    rw [hY, Set.Finite.mem_toFinset]
    exact ⟨hxE, fun h => hx1 (congrArg Subtype.val h)⟩

theorem card_fix_le_two {E : Subgroup OV} (hEL : E ≤ Lc) (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : Nat.card E = 16) :
    Nat.card {i : Fin 64 // ∀ x : MulAction.stabilizer OV N0, (x : OV) ∈ E → sigma x i = i} ≤
      2 := by
  classical
  obtain ⟨a, b, c, d, h4, haE, hbE, hcE, hdE⟩ := exists_indep4 hEL hsq hcomm (by omega)
  rw [← card_fix4 h4, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi a haE, hi b hbE, hi c hcE, hi d hdE⟩

end Census

end Sec3Mod

end CFSG.ComponentClassification.AS81
