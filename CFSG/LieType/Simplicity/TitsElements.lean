module

public import CFSG.LieType.Simplicity.TitsBits
public import CFSG.LieType.Simplicity.ReeCells

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree TitsBits TitsBits.Letter
open scoped commutatorElement

@[expose] noncomputable def titsG0
    (K : Type) [Field K] : adjointGroup ReeTag.F4.tag K :=
  xElement (τ := ReeTag.F4.tag) (0 : Fin 4) 1 * xElement (τ := ReeTag.F4.tag) (3 : Fin 4) 1

@[expose] noncomputable def titsG1
    (K : Type) [Field K] : adjointGroup ReeTag.F4.tag K :=
  xElement (τ := ReeTag.F4.tag) (2 : Fin 4) 1 * xElement (τ := ReeTag.F4.tag) (1 : Fin 4) 1 *
    (weylElement ReeTag.F4.tag K (2 : Fin 4) * xElement (τ := ReeTag.F4.tag) (1 : Fin 4) 1 *
      (weylElement ReeTag.F4.tag K (2 : Fin 4))⁻¹)

noncomputable abbrev titsZ1
    (K : Type) [Field K] : adjointGroup ReeTag.F4.tag K :=
  nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (0 : Fin 4))

noncomputable abbrev titsZ2
    (K : Type) [Field K] : adjointGroup ReeTag.F4.tag K :=
  nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (1 : Fin 4))

@[expose] def titsG0Word : List Letter := [x 0, x 3]

@[expose] def titsG1Word : List Letter := [x 2, x 1, n 2, x 1, n 2]

@[expose] def titsZ1Word : List Letter := [n 0, n 3]

@[expose] def titsZ2Word : List Letter := [n 1, n 2, n 1, n 2]

section Words

variable {K : Type} [Field K]

theorem titsG0_eq_evalG
    : titsG0 K = evalG K titsG0Word := by
  simp only [titsG0Word, evalG_cons, evalG_nil, mul_one]
  rfl

theorem titsG1_eq_evalG
    [CharP K 2] : titsG1 K = evalG K titsG1Word := by
  change (x 2).elt K * (x 1).elt K * ((n 2).elt K * (x 1).elt K * ((n 2).elt K)⁻¹) = _
  simp only [titsG1Word, evalG_cons, evalG_nil, mul_one, elt_inv, mul_assoc]

theorem titsZ1_eq_evalG :
    titsZ1 K = evalG K titsZ1Word := by
  rw [titsZ1, nrep_eq_prod ReeTag.F4.tag K (isReduced_reeOrbitWord ReeTag.F4 (0 : Fin 4))]
  simp only [titsZ1Word, evalG_cons, evalG_nil]
  rfl

theorem titsZ2_eq_evalG :
    titsZ2 K = evalG K titsZ2Word := by
  rw [titsZ2, nrep_eq_prod ReeTag.F4.tag K (isReduced_reeOrbitWord ReeTag.F4 (1 : Fin 4))]
  simp only [titsZ2Word, evalG_cons, evalG_nil]
  rfl

end Words

namespace TitsBits

section Frobenius

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem perm_idx (i : Fin 4) : ReeTag.F4.perm (idx i) = idx (3 - i) := by
  fin_cases i <;> rfl

theorem reeAut_letter
    (l : Letter) : ReeTag.F4.reeAut K 0 (l.elt K) = l.flip.elt K := by
  cases l with
  | x i =>
    simp only [Letter.elt, Letter.flip]
    rw [ReeTag.reeAut_xElement, one_pow, perm_idx]
  | n i =>
    simp only [Letter.elt, Letter.flip]
    rw [ReeTag.reeAut_weylElement, perm_idx]

theorem reeAut_evalG
    (w : List Letter) :
    ReeTag.F4.reeAut K 0 (evalG K w) = evalG K (w.map Letter.flip) := by
  induction w with
  | nil => simp
  | cons l w ih => rw [evalG_cons, map_mul, reeAut_letter, ih, List.map_cons, evalG_cons]

end Frobenius

end TitsBits

section Frobenius

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem titsG0_mem_reeFixed :
    titsG0 K ∈ reeFixed ReeTag.F4 K 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [mem_reeFixed, titsG0_eq_evalG, reeAut_evalG, evalG_eq_evalG_iff]
  decide +kernel

theorem titsG1_mem_reeFixed :
    titsG1 K ∈ reeFixed ReeTag.F4 K 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [mem_reeFixed, titsG1_eq_evalG, reeAut_evalG, evalG_eq_evalG_iff]
  decide +kernel

end Frobenius

section Identities

variable {K : Type} [Field K] [CharP K ReeTag.F4.prime]

theorem titsG0_mul_self
    : titsG0 K * titsG0 K = 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [titsG0_eq_evalG, ← evalG_append, ← evalG_nil, evalG_eq_evalG_iff]
  decide +kernel

theorem titsG0_ne_one
    : titsG0 K ≠ 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [titsG0_eq_evalG, ← evalG_nil, Ne, evalG_eq_evalG_iff]
  decide +kernel

theorem tits_R1 :
    ⁅titsZ1 K * titsG1 K * (titsZ1 K)⁻¹,
    (titsZ2 K * titsZ1 K) * titsG0 K * (titsZ2 K * titsZ1 K)⁻¹⁆ =
      titsZ2 K * titsG1 K ^ 2 * (titsZ2 K)⁻¹ := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [titsZ1_eq_evalG, titsZ2_eq_evalG, titsG0_eq_evalG, titsG1_eq_evalG]
  simp only [commutatorElement_def, pow_two, ← evalG_append, evalG_inv]
  rw [evalG_eq_evalG_iff]
  decide +kernel

theorem tits_R2
    : ⁅(titsZ1 K * titsZ2 K) * titsG1 K * (titsZ1 K * titsZ2 K)⁻¹, titsG1 K⁆ =
    titsZ1 K * titsG0 K * (titsZ1 K)⁻¹ := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [titsZ1_eq_evalG, titsZ2_eq_evalG, titsG0_eq_evalG, titsG1_eq_evalG]
  simp only [commutatorElement_def, ← evalG_append, evalG_inv]
  rw [evalG_eq_evalG_iff]
  decide +kernel

theorem tits_W
    : ⁅titsG0 K, titsZ1 K⁆ * titsG0 K ≠ titsG0 K * ⁅titsG0 K, titsZ1 K⁆ := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [titsZ1_eq_evalG, titsG0_eq_evalG]
  simp only [commutatorElement_def, ← evalG_append, evalG_inv]
  rw [Ne, evalG_eq_evalG_iff]
  decide +kernel

end Identities

namespace TitsBits

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_one_of_card_eq_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  have := Fintype.ofFinite K
  rcases eq_or_ne c 0 with h | h
  · exact .inl h
  · right
    have h1 := FiniteField.pow_card_sub_one_eq_one c h
    rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h1

theorem eq_one_or_eq_eltElement
    (hK : Nat.card K = 2) {α : Root ReeTag.F4.tag}
    {g : adjointGroup ReeTag.F4.tag K} (hg : g ∈ (nativeRootSubgroups ReeTag.F4.tag K).X α) :
    g = 1 ∨ g = (rootOperatorFamily ReeTag.F4.tag).eltElement α 1 := by
  rw [nativeRootSubgroups_X] at hg
  obtain ⟨c, rfl⟩ := (rootOperatorFamily ReeTag.F4.tag).mem_rootSubgroup.1 hg
  rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
  · exact .inl ((rootOperatorFamily ReeTag.F4.tag).eltElement_zero α)
  · exact .inr rfl

theorem exists_word_of_mem_Uminus
    (hK : Nat.card K = 2) {r : WeylGroup ReeTag.F4.tag}
    {L : List (List Letter)} (hnil : [] ∈ L)
    (hgen : ∀ α : Root ReeTag.F4.tag, 0 < height α.1 → height (r • α).1 < 0 → ∀ w ∈ L,
      ∃ w' ∈ L, (rootOperatorFamily ReeTag.F4.tag).eltElement α 1 * evalG K w = evalG K w')
    {y : adjointGroup ReeTag.F4.tag K} (hy : y ∈ Uminus ReeTag.F4.tag K r) :
    ∃ w ∈ L, y = evalG K w := by
  set S : Set (adjointGroup ReeTag.F4.tag K) := {g | ∃ α : Root ReeTag.F4.tag,
    (0 < height α.1 ∧ height (r • α).1 < 0) ∧ g ∈ (nativeRootSubgroups ReeTag.F4.tag K).X α}
  have hle : Uminus ReeTag.F4.tag K r ≤ Subgroup.closure S :=
    iSup₂_le fun α hα _ hg => Subgroup.subset_closure ⟨α, hα, hg⟩
  have hstep : ∀ g ∈ S, ∀ w ∈ L, ∃ w' ∈ L, g * evalG K w = evalG K w' := by
    rintro g ⟨α, ⟨h1, h2⟩, hg⟩ w hw
    rcases eq_one_or_eq_eltElement hK hg with rfl | rfl
    · exact ⟨w, hw, one_mul _⟩
    · exact hgen α h1 h2 w hw
  have hy' := hle hy
  clear hy
  induction hy' using Subgroup.closure_induction_left with
  | one => exact ⟨[], hnil, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    obtain ⟨w', hw', h⟩ := hstep g hg w hw
    exact ⟨w', hw', h⟩
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    obtain ⟨α, hα, hgα⟩ := hg
    obtain ⟨w', hw', h⟩ := hstep g⁻¹ ⟨α, hα, inv_mem hgα⟩ w hw
    exact ⟨w', hw', h⟩

omit [Finite K] in
theorem closure_of_check
    [CharP K 2] {ω : List (Fin ReeTag.F4.tag.rank)} {L : List (List Letter)}
    (h : ∀ k < ReeTag.F4.tag.rootCertificate.roots.length,
      0 < height (ReeTag.F4.tag.rootCertificate.root k) →
      height (ω.foldr (reflect ReeTag.F4.tag) (ReeTag.F4.tag.rootCertificate.root k)) < 0 →
        ∀ w ∈ L, ∃ w' ∈ L, mul (pack (eltBits k)) (evalB w) % 2 ^ 2704 = evalB w' % 2 ^ 2704)
    (α : Root ReeTag.F4.tag) (h1 : 0 < height α.1)
    (h2 : height ((coxeterSystem ReeTag.F4.tag).wordProd ω • α).1 < 0) (w : List Letter)
    (hw : w ∈ L) :
    ∃ w' ∈ L, (rootOperatorFamily ReeTag.F4.tag).eltElement α 1 * evalG K w = evalG K w' := by
  rw [coe_smul_root, CFSG.LieType.Ree.wordProd_smul, ← root_rootPos α] at h2
  rw [← root_rootPos α] at h1
  obtain ⟨w', hw', hb⟩ := h (rootPos α) (rootPos_lt α) h1 h2 w hw
  exact ⟨w', hw', (((hasBits_eltElement α).mul (hasBits_evalG w)).eq_iff (hasBits_evalG w')).2 hb⟩

omit [Finite K] in
theorem eltElement_mem_Uminus
    {r : WeylGroup ReeTag.F4.tag} {α : Root ReeTag.F4.tag}
    (h1 : 0 < height α.1) (h2 : height (r • α).1 < 0) (c : K) :
    (rootOperatorFamily ReeTag.F4.tag).eltElement α c ∈ Uminus ReeTag.F4.tag K r :=
  le_iSup₂_of_le (f := fun (β : Root ReeTag.F4.tag)
    (_ : 0 < height β.1 ∧ height (r • β).1 < 0) => (nativeRootSubgroups ReeTag.F4.tag K).X β)
    α ⟨h1, h2⟩ le_rfl ((rootOperatorFamily ReeTag.F4.tag).eltElement_mem_rootSubgroup α c)

end Fixed

end TitsBits

section Fixed

variable {K : Type} [Field K] [Finite K]

@[expose] def titsU1Words : List (List Letter) :=
  [[], [x 3], [x 0], [x 0, x 3]]

@[expose] def titsU2Words : List (List Letter) :=
  [[], [n 1, x 2, n 1], [n 2, x 1, n 2], [n 2, x 1, n 2, n 1, x 2, n 1], [x 2],
    [x 2, n 1, x 2, n 1], [x 2, n 2, x 1, n 2], [x 2, n 2, x 1, n 2, n 1, x 2, n 1], [x 1],
    [x 1, n 1, x 2, n 1], [x 1, n 2, x 1, n 2], [x 1, n 2, x 1, n 2, n 1, x 2, n 1], [x 1, x 2],
    [x 1, x 2, n 1, x 2, n 1], [x 1, x 2, n 2, x 1, n 2], [x 1, x 2, n 2, x 1, n 2, n 1, x 2, n 1]]

theorem titsU1Words_closed : ∀ k < ReeTag.F4.tag.rootCertificate.roots.length,
    0 < height (ReeTag.F4.tag.rootCertificate.root k) →
    height ((ReeTag.F4.reeOrbitWord (0 : Fin 4)).foldr (reflect ReeTag.F4.tag)
      (ReeTag.F4.tag.rootCertificate.root k)) < 0 →
      ∀ w ∈ titsU1Words, ∃ w' ∈ titsU1Words,
        mul (pack (eltBits k)) (evalB w) % 2 ^ 2704 = evalB w' % 2 ^ 2704 := by
  decide +kernel

theorem titsU2Words_closed : ∀ k < ReeTag.F4.tag.rootCertificate.roots.length,
    0 < height (ReeTag.F4.tag.rootCertificate.root k) →
    height ((ReeTag.F4.reeOrbitWord (1 : Fin 4)).foldr (reflect ReeTag.F4.tag)
      (ReeTag.F4.tag.rootCertificate.root k)) < 0 →
      ∀ w ∈ titsU2Words, ∃ w' ∈ titsU2Words,
        mul (pack (eltBits k)) (evalB w) % 2 ^ 2704 = evalB w' % 2 ^ 2704 := by
  decide +kernel

theorem titsU1Words_fixed : ∀ w ∈ titsU1Words,
    evalB (w.map Letter.flip) % 2 ^ 2704 = evalB w % 2 ^ 2704 →
      evalB w % 2 ^ 2704 = evalB [] % 2 ^ 2704 ∨
        evalB w % 2 ^ 2704 = evalB titsG0Word % 2 ^ 2704 := by
  decide +kernel

theorem titsU2Words_fixed : ∀ w ∈ titsU2Words,
    evalB (w.map Letter.flip) % 2 ^ 2704 = evalB w % 2 ^ 2704 →
      evalB w % 2 ^ 2704 = evalB [] % 2 ^ 2704 ∨
        evalB w % 2 ^ 2704 = evalB titsG1Word % 2 ^ 2704 ∨
        evalB w % 2 ^ 2704 = evalB (titsG1Word ++ titsG1Word) % 2 ^ 2704 ∨
        evalB w % 2 ^ 2704 = evalB (titsG1Word ++ titsG1Word ++ titsG1Word) % 2 ^ 2704 := by
  decide +kernel

omit [Finite K] in
theorem titsG0_mem_Uminus
    : titsG0 K ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (0 : Fin 4)) := by
  rw [titsG0_eq_evalG, titsG0Word, evalG_cons, evalG_singleton, elt, elt,
    ← eltElement_simpleRoot, ← eltElement_simpleRoot]
  refine mul_mem (eltElement_mem_Uminus ?_ ?_ _) (eltElement_mem_Uminus ?_ ?_ _)
  all_goals try simp only [coe_smul_root, CFSG.LieType.Ree.wordProd_smul]
  all_goals decide +kernel

omit [Finite K] in
theorem titsG1_mem_Uminus
    : titsG1 K ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (1 : Fin 4)) := by
  change xElement (idx 2) 1 * xElement (idx 1) 1 * (weylElement ReeTag.F4.tag K (idx 2) *
    xElement (idx 1) 1 * (weylElement ReeTag.F4.tag K (idx 2))⁻¹) ∈ _
  rw [← eltElement_simpleRoot, ← eltElement_simpleRoot,
    (rootOperatorFamily ReeTag.F4.tag).weylElement_mul_eltElement_mul_inv]
  refine mul_mem (mul_mem (eltElement_mem_Uminus ?_ ?_ _) (eltElement_mem_Uminus ?_ ?_ _))
    (eltElement_mem_Uminus ?_ ?_ _)
  all_goals try simp only [coe_smul_root, simple_smul, CFSG.LieType.Ree.wordProd_smul]
  all_goals decide +kernel

variable [CharP K ReeTag.F4.prime]

theorem eq_one_or_eq_titsG0
    (hK : Nat.card K = 2) {y : adjointGroup ReeTag.F4.tag K}
    (hy : y ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (0 : Fin 4)))
    (hF : ReeTag.F4.reeAut K 0 y = y) :
    y = 1 ∨ y = titsG0 K := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨w, hw, rfl⟩ := exists_word_of_mem_Uminus hK (List.mem_cons_self ..)
    (closure_of_check titsU1Words_closed) hy
  rw [reeAut_evalG, evalG_eq_evalG_iff] at hF
  rw [titsG0_eq_evalG, ← evalG_nil, evalG_eq_evalG_iff, evalG_eq_evalG_iff]
  exact titsU1Words_fixed w hw hF

theorem mem_zpowers_titsG1
    (hK : Nat.card K = 2) {y : adjointGroup ReeTag.F4.tag K}
    (hy : y ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (1 : Fin 4)))
    (hF : ReeTag.F4.reeAut K 0 y = y) :
    y ∈ Subgroup.zpowers (titsG1 K) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨w, hw, rfl⟩ := exists_word_of_mem_Uminus hK (List.mem_cons_self ..)
    (closure_of_check titsU2Words_closed) hy
  rw [reeAut_evalG, evalG_eq_evalG_iff] at hF
  rw [titsG1_eq_evalG]
  rcases titsU2Words_fixed w hw hF with h | h | h | h
  · rw [(evalG_eq_evalG_iff w []).2 h, evalG_nil]
    exact one_mem _
  · rw [(evalG_eq_evalG_iff w titsG1Word).2 h]
    exact Subgroup.mem_zpowers _
  · rw [(evalG_eq_evalG_iff w _).2 h, evalG_append, ← pow_two]
    exact Subgroup.npow_mem_zpowers _ 2
  · rw [(evalG_eq_evalG_iff w _).2 h, evalG_append, evalG_append, ← pow_two, ← pow_succ]
    exact Subgroup.npow_mem_zpowers _ 3

end Fixed

end CFSG.LieType.Simplicity
