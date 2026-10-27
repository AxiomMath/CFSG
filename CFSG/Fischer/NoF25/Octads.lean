module

public import CFSG.Fischer.NoF25.Defs
public import CFSG.Fischer.NoF25.Steiner
public import Mathlib.Tactic.Group

public section

namespace CFSG.Fischer

variable {Y : Type*} [Group Y] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem famProd_comm' (d : ι → Y) (hcomm : ∀ i j, d i * d j = d j * d i) (S T : Finset ι) :
    ((Finset.univ : Finset ι) : Set ι).Pairwise
      (fun i j => Commute (if i ∈ S then d i else 1) (if j ∈ T then d j else 1)) := by
  intro i _ j _ _
  show (if i ∈ S then d i else 1) * (if j ∈ T then d j else 1) =
    (if j ∈ T then d j else 1) * (if i ∈ S then d i else 1)
  split_ifs <;> simp [hcomm]

theorem famProd_comm (d : ι → Y) (hcomm : ∀ i j, d i * d j = d j * d i) (S : Finset ι) :
    ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun Commute fun i => if i ∈ S then d i else 1) :=
  famProd_comm' d hcomm S S

noncomputable def famProd (d : ι → Y) (hcomm : ∀ i j, d i * d j = d j * d i) (S : Finset ι) : Y :=
  Finset.univ.noncommProd (fun i => if i ∈ S then d i else 1) (famProd_comm d hcomm S)

variable (d : ι → Y) (hcomm : ∀ i j, d i * d j = d j * d i)

theorem famProd_empty : famProd d hcomm ∅ = 1 := by
  unfold famProd
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 (fun i _ => by simp), one_pow]

theorem famProd_insert {a : ι} {S : Finset ι} (ha : a ∉ S) :
    famProd d hcomm (insert a S) = d a * famProd d hcomm S := by
  unfold famProd
  rw [← Finset.mul_noncommProd_erase _ (Finset.mem_univ a),
    ← Finset.mul_noncommProd_erase _ (Finset.mem_univ a)]
  rw [ite_eq_left (Finset.mem_insert_self a S), ite_eq_right ha, one_mul]
  congr 1
  apply Finset.noncommProd_congr rfl
  intro i hi
  rw [Finset.mem_erase] at hi
  simp only [Finset.mem_insert, hi.1, false_or]

theorem famProd_singleton (a : ι) : famProd d hcomm {a} = d a := by
  rw [← insert_empty_eq a, famProd_insert d hcomm (Finset.notMem_empty a), famProd_empty, mul_one]

theorem famProd_symmDiff (hsq : ∀ i, d i * d i = 1) (A B : Finset ι) :
    famProd d hcomm (symmDiff A B) = famProd d hcomm A * famProd d hcomm B := by
  unfold famProd
  rw [← Finset.noncommProd_mul_distrib]
  · apply Finset.noncommProd_congr rfl
    intro i _
    simp only [Pi.mul_apply, Finset.mem_symmDiff]
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB, hsq]
  · exact famProd_comm' d hcomm B A

theorem famProd_map (τ : Equiv.Perm ι) (r : Y) (hτ : ∀ i, d (τ i) = r * d i * r⁻¹)
    (S : Finset ι) : famProd d hcomm (S.map τ.toEmbedding) = r * famProd d hcomm S * r⁻¹ := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.map_empty, famProd_empty, mul_one, mul_inv_cancel]
  | insert a S ha ih =>
    have ha' : τ a ∉ S.map τ.toEmbedding := by
      rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact ha
    rw [Finset.map_insert, Equiv.toEmbedding_apply, famProd_insert d hcomm ha',
      famProd_insert d hcomm ha, ih, hτ]
    group

theorem famProd_toFinset (l : List ι) (hl : l.Nodup) :
    famProd d hcomm l.toFinset = (l.map d).prod := by
  induction l with
  | nil => rw [List.toFinset_nil, famProd_empty, List.map_nil, List.prod_nil]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.toFinset_cons, famProd_insert d hcomm (by rw [List.mem_toFinset]; exact hl.1), ih hl.2,
      List.map_cons, List.prod_cons]

omit [Fintype ι] in
theorem card_symmDiff_add_two_mul (A B : Finset ι) :
    (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  have e : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  rw [Finset.inter_comm B A] at h2
  omega

theorem famProd_pair {i j : ι} (hij : i ≠ j) : famProd d hcomm {i, j} = d i * d j := by
  rw [famProd_insert d hcomm (by rwa [Finset.mem_singleton]), famProd_singleton]

theorem famProd_ne_one_of_card_two (hsq : ∀ i, d i * d i = 1) (hinj : Function.Injective d)
    {S : Finset ι} (hS : S.card = 2) : famProd d hcomm S ≠ 1 := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hS
  rw [famProd_pair d hcomm hij]
  intro h
  apply hij
  apply hinj
  rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right (hsq j)]

theorem famProd_ne_one_of_card_four (hsq : ∀ i, d i * d i = 1)
    (hpair : ∀ i j k l, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l → d i * d j ≠ d k * d l)
    {S : Finset ι} (hS : S.card = 4) : famProd d hcomm S ≠ 1 := by
  obtain ⟨i, T, hi, rfl, hT⟩ := Finset.card_eq_succ.1 hS
  obtain ⟨j, k, l, hjk, hjl, hkl, rfl⟩ := Finset.card_eq_three.1 hT
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  obtain ⟨hij, hik, hil⟩ := hi
  have hj : j ∉ ({k, l} : Finset ι) := by simp [hjk, hjl]
  have hi' : i ∉ ({j, k, l} : Finset ι) := by simp [hij, hik, hil]
  rw [famProd_insert d hcomm hi', famProd_insert d hcomm hj, famProd_pair d hcomm hkl]
  intro h
  have h' : (d i * d j) * (d k * d l) = 1 := by rw [← h]; group
  have e := eq_inv_of_mul_eq_one_left h'
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq k), inv_eq_of_mul_eq_one_right (hsq l),
    ← hcomm k l] at e
  exact hpair i j k l hij hkl hik hil hjk hjl e

section Steiner

variable (hsq : ∀ i, d i * d i = 1) (hinj : Function.Injective d)
  (hpair : ∀ i j k l, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l → d i * d j ≠ d k * d l)
  (𝒪 : Finset (Finset ι)) (hcard : ∀ O ∈ 𝒪, O.card = 8)
  (hex : ∀ Y : Finset ι, Y.card = 5 → ∃ O ∈ 𝒪, Y ⊆ O)
  (hrel : ∀ O ∈ 𝒪, famProd d hcomm O = 1)

include hsq hinj hpair hcard hex hrel in
theorem famProd_ne_one_of_card_six {S : Finset ι} (hS : S.card = 6) : famProd d hcomm S ≠ 1 := by
  intro h
  obtain ⟨Y, hYS, hY⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card by omega)
  obtain ⟨O, hO, hYO⟩ := hex Y hY
  have hD : famProd d hcomm (symmDiff S O) = 1 := by
    rw [famProd_symmDiff d hcomm hsq, h, hrel O hO, one_mul]
  have hc := card_symmDiff_add_two_mul S O
  have h5 : 5 ≤ (S ∩ O).card := hY ▸ Finset.card_le_card (Finset.subset_inter hYS hYO)
  have h6 : (S ∩ O).card ≤ 6 := hS ▸ Finset.card_le_card Finset.inter_subset_left
  rw [hS, hcard O hO] at hc
  rcases (show (S ∩ O).card = 5 ∨ (S ∩ O).card = 6 by omega) with h' | h'
  · exact famProd_ne_one_of_card_four d hcomm hsq hpair (by omega) hD
  · exact famProd_ne_one_of_card_two d hcomm hsq hinj (by omega) hD

include hsq hinj hpair hcard hex hrel in
theorem mem_of_famProd_eq_one {S : Finset ι} (hS : S.card = 8) (h : famProd d hcomm S = 1) :
    S ∈ 𝒪 := by
  obtain ⟨Y, hYS, hY⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card by omega)
  obtain ⟨O, hO, hYO⟩ := hex Y hY
  have hD : famProd d hcomm (symmDiff S O) = 1 := by
    rw [famProd_symmDiff d hcomm hsq, h, hrel O hO, one_mul]
  have hc := card_symmDiff_add_two_mul S O
  have h5 : 5 ≤ (S ∩ O).card := hY ▸ Finset.card_le_card (Finset.subset_inter hYS hYO)
  have h8 : (S ∩ O).card ≤ 8 := hS ▸ Finset.card_le_card Finset.inter_subset_left
  rw [hS, hcard O hO] at hc
  rcases (show (S ∩ O).card = 5 ∨ (S ∩ O).card = 6 ∨ (S ∩ O).card = 7 ∨ (S ∩ O).card = 8 by
    omega) with h' | h' | h' | h'
  · exact absurd hD (famProd_ne_one_of_card_six d hcomm hsq hinj hpair 𝒪 hcard hex hrel
      (by omega))
  · exact absurd hD (famProd_ne_one_of_card_four d hcomm hsq hpair (by omega))
  · exact absurd hD (famProd_ne_one_of_card_two d hcomm hsq hinj (by omega))
  · have h0 : symmDiff S O = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [Finset.symmDiff_eq_empty.1 h0]
    exact hO

end Steiner

@[expose] def Realizes (d : ι → Y) (r : Y) (τ : Equiv.Perm ι) : Prop :=
  ∀ i, d (τ i) = r * d i * r⁻¹

omit [Fintype ι] [DecidableEq ι] in
theorem Realizes.mul {r s : Y} {τ σ : Equiv.Perm ι} (h1 : Realizes d r τ)
    (h2 : Realizes d s σ) : Realizes d (r * s) (τ * σ) := by
  intro i
  rw [Equiv.Perm.mul_apply, h1, h2]
  group

omit [Fintype ι] [DecidableEq ι] in
theorem Realizes.inv {r : Y} {τ : Equiv.Perm ι} (h : Realizes d r τ) : Realizes d r⁻¹ τ⁻¹ := by
  intro i
  have e := h (τ⁻¹ i)
  rw [show τ (τ⁻¹ i) = i from τ.apply_symm_apply i] at e
  rw [e]
  group

omit [Group Y] [Fintype ι] [DecidableEq ι] in
theorem ofInjective_symm_val (hinj : Function.Injective d) (x : Set.range d) :
    d ((Equiv.ofInjective d hinj).symm x) = x := by
  have := Equiv.apply_ofInjective_symm hinj x
  exact this

omit [Group Y] [DecidableEq ι] in
theorem fix_eq_image (hinj : Function.Injective d) (σ : Equiv.Perm (Set.range d))
    (τ : Equiv.Perm ι) (h : ∀ i, σ (Equiv.ofInjective d hinj i) = Equiv.ofInjective d hinj (τ i))
    [DecidablePred fun i => τ i = i] :
    {x | σ x = x} = Equiv.ofInjective d hinj '' ↑(Finset.univ.filter fun i => τ i = i) := by
  ext x
  obtain ⟨i, rfl⟩ := (Equiv.ofInjective d hinj).surjective x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and,
    (Equiv.ofInjective d hinj).injective.mem_set_image, h,
    (Equiv.ofInjective d hinj).injective.eq_iff]

section Fix

variable (hsq : ∀ i, d i * d i = 1) (hinj : Function.Injective d)
  (hpair : ∀ i j k l, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l → d i * d j ≠ d k * d l)
  (𝒪 : Finset (Finset ι)) (hcard : ∀ O ∈ 𝒪, O.card = 8)
  (hsteiner : ∀ Y : Finset ι, Y.card = 5 → ∃! O, O ∈ 𝒪 ∧ Y ⊆ O)
  (O₀ : Finset ι) (hO₀ : O₀ ∈ 𝒪) (hrel₀ : famProd d hcomm O₀ = 1)
  (htrans : ∀ O ∈ 𝒪, ∃ r τ, Realizes d r τ ∧ O = O₀.map (Equiv.toEmbedding τ))
  (r₀ : Y) (τ₀ : Equiv.Perm ι) (h₀ : Realizes d r₀ τ₀) (hτ₀ : τ₀ * τ₀ = 1)
  (hfix₀ : (Finset.univ.filter fun i => τ₀ i = i) = O₀)

include hsq hinj hpair hcard hsteiner hO₀ hrel₀ htrans h₀ hτ₀ hfix₀ in
theorem fixSets_range :
    fixSets (inducedPerms (Set.range d)) 8 =
      (fun O : Finset ι => Equiv.ofInjective d hinj '' (O : Set ι)) '' (𝒪 : Set (Finset ι)) := by
  set e := Equiv.ofInjective d hinj with he
  have hev : ∀ i, (e i : Y) = d i := fun i => rfl
  have hrel : ∀ O ∈ 𝒪, famProd d hcomm O = 1 := by
    intro O hO
    obtain ⟨r, τ, hτ, rfl⟩ := htrans O hO
    rw [famProd_map d hcomm τ r hτ, hrel₀, mul_one, mul_inv_cancel]
  have hex : ∀ Y : Finset ι, Y.card = 5 → ∃ O ∈ 𝒪, Y ⊆ O := fun Y hY =>
    (hsteiner Y hY).exists
  ext F
  constructor
  · rintro ⟨σ, ⟨r, hr⟩, hσσ, rfl, hF8⟩
    set τ : Equiv.Perm ι := (e.trans σ).trans e.symm with hτdef
    have hστ : ∀ i, σ (e i) = e (τ i) := fun i => by
      rw [hτdef, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
    have hτ : Realizes d r τ := by
      intro i
      rw [← hev, ← hστ, hr, hev]
    have hττ : τ * τ = 1 := by
      ext i
      apply e.injective
      rw [Equiv.Perm.mul_apply, ← hστ, ← hστ, ← Equiv.Perm.mul_apply, hσσ, Equiv.Perm.one_apply,
        Equiv.Perm.one_apply]
    have hfixE := fix_eq_image d hinj σ τ hστ
    have hcard8 : (Finset.univ.filter fun i => τ i = i).card = 8 := by
      rw [hfixE, Set.ncard_image_of_injective _ e.injective, Set.ncard_coe_finset] at hF8
      exact hF8
    have hpres : ∀ O ∈ 𝒪, O.map τ.toEmbedding ∈ 𝒪 := by
      intro O hO
      apply mem_of_famProd_eq_one d hcomm hsq hinj hpair 𝒪 hcard hex hrel
      · rw [Finset.card_map, hcard O hO]
      · rw [famProd_map d hcomm τ r hτ, hrel O hO, mul_one, mul_inv_cancel]
    exact ⟨_, fix_mem_of_steiner 𝒪 hcard hsteiner τ hττ hpres hcard8, hfixE.symm⟩
  · rintro ⟨O, hO, rfl⟩
    obtain ⟨r, τh, hτh, rfl⟩ := htrans O hO
    set τ : Equiv.Perm ι := τh * τ₀ * τh⁻¹ with hτdef
    have hτ : Realizes d (r * r₀ * r⁻¹) τ := (hτh.mul d h₀).mul d (hτh.inv d)
    set σ : Equiv.Perm (Set.range d) := (e.symm.trans τ).trans e with hσdef
    have hστ : ∀ i, σ (e i) = e (τ i) := fun i => by
      rw [hσdef, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    have hσ : σ ∈ inducedPerms (Set.range d) := by
      refine ⟨r * r₀ * r⁻¹, fun x => ?_⟩
      obtain ⟨i, rfl⟩ := e.surjective x
      rw [hστ, hev, hev, hτ]
    have hττ : τ * τ = 1 := by
      rw [hτdef]
      calc τh * τ₀ * τh⁻¹ * (τh * τ₀ * τh⁻¹) = τh * (τ₀ * τ₀) * τh⁻¹ := by group
        _ = 1 := by rw [hτ₀, mul_one, mul_inv_cancel]
    have hσσ : σ * σ = 1 := by
      ext x
      obtain ⟨i, rfl⟩ := e.surjective x
      rw [Equiv.Perm.mul_apply, hστ, hστ, ← Equiv.Perm.mul_apply, hττ]
      rfl
    have hfixτ : (Finset.univ.filter fun i => τ i = i) = O₀.map τh.toEmbedding := by
      ext i
      rw [Finset.mem_filter, Finset.mem_map_equiv, ← hfix₀, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, hτdef, Equiv.Perm.mul_apply]
      constructor
      · intro h
        have := congrArg τh.symm h
        rwa [Equiv.symm_apply_apply] at this
      · intro h
        rw [show τh⁻¹ i = τh.symm i from rfl, h, Equiv.apply_symm_apply]
    refine ⟨σ, hσ, hσσ, ?_, ?_⟩
    · rw [fix_eq_image d hinj σ τ hστ, hfixτ]
    · rw [Set.ncard_image_of_injective _ e.injective, Set.ncard_coe_finset, Finset.card_map,
        hcard O₀ hO₀]

include hsq hinj hpair hcard hsteiner hO₀ hrel₀ htrans h₀ hτ₀ hfix₀ in
theorem ncard_fixSets_range : (fixSets (inducedPerms (Set.range d)) 8).ncard = 𝒪.card := by
  have hinjO : Function.Injective fun O : Finset ι => Equiv.ofInjective d hinj '' (O : Set ι) :=
    fun _ _ h =>
      Finset.coe_injective ((Set.image_injective.2 (Equiv.ofInjective d hinj).injective) h)
  rw [fixSets_range d hcomm hsq hinj hpair 𝒪 hcard hsteiner O₀ hO₀ hrel₀ htrans r₀ τ₀ h₀ hτ₀
    hfix₀, Set.ncard_image_of_injective _ hinjO, Set.ncard_coe_finset]

end Fix

theorem steiner_of_inter (𝒪 : Finset (Finset ι)) (hcard : ∀ O ∈ 𝒪, O.card = 8)
    (hint : ∀ O ∈ 𝒪, ∀ O' ∈ 𝒪, O ≠ O' → (O ∩ O').card ≤ 4)
    (hnum : 𝒪.card * 56 = (Fintype.card ι).choose 5) :
    ∀ Y : Finset ι, Y.card = 5 → ∃! O, O ∈ 𝒪 ∧ Y ⊆ O := by
  have hdisj : ∀ O ∈ 𝒪, ∀ O' ∈ 𝒪, O ≠ O' →
      Disjoint (O.powersetCard 5) (O'.powersetCard 5) := by
    intro O hO O' hO' hne
    rw [Finset.disjoint_left]
    intro Y hY hY'
    rw [Finset.mem_powersetCard] at hY hY'
    have := Finset.card_le_card (Finset.subset_inter hY.1 hY'.1)
    have := hint O hO O' hO' hne
    omega
  have hsub : 𝒪.biUnion (fun O => O.powersetCard 5) ⊆ Finset.univ.powersetCard 5 := by
    intro Y hY
    rw [Finset.mem_biUnion] at hY
    obtain ⟨O, _, hY⟩ := hY
    rw [Finset.mem_powersetCard] at hY ⊢
    exact ⟨Finset.subset_univ _, hY.2⟩
  have hc : (𝒪.biUnion fun O => O.powersetCard 5).card = (Finset.univ.powersetCard 5 :
      Finset (Finset ι)).card := by
    rw [Finset.card_biUnion hdisj, Finset.card_powersetCard, Finset.card_univ, ← hnum,
      Finset.sum_congr rfl fun O hO => by rw [Finset.card_powersetCard, hcard O hO],
      Finset.sum_const, smul_eq_mul]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub hc.ge
  intro Y hY
  have hmem : Y ∈ 𝒪.biUnion fun O => O.powersetCard 5 := by
    rw [heq, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hY⟩
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨O, hO, hYO⟩ := hmem
  rw [Finset.mem_powersetCard] at hYO
  refine ⟨O, ⟨hO, hYO.1⟩, fun O' hO' => ?_⟩
  by_contra hne
  have := Finset.card_le_card (Finset.subset_inter hO'.2 hYO.1)
  have := hint O' hO'.1 O hO hne
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem exists_realizes_of_tree {n m : ℕ} (F : Fin (n + 1) → Finset ι)
    (par : Fin (n + 1) → Fin (n + 1)) (lab : Fin (n + 1) → Fin m) (π : Fin m → Equiv.Perm ι)
    (r : Fin m → Y) (hπ : ∀ l, Realizes d (r l) (π l))
    (htree : ∀ k : Fin (n + 1), k.val ≠ 0 →
      (par k).val < k.val ∧ F k = (F (par k)).map (π (lab k)).toEmbedding) :
    ∀ k, ∃ s τ, Realizes d s τ ∧ F k = (F 0).map τ.toEmbedding := by
  have key : ∀ (j : ℕ) (k : Fin (n + 1)), k.val = j →
      ∃ s τ, Realizes d s τ ∧ F k = (F 0).map τ.toEmbedding := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro k hk
      by_cases h0 : k.val = 0
      · refine ⟨1, 1, fun i => by rw [Equiv.Perm.one_apply, one_mul, inv_one, mul_one], ?_⟩
        rw [show k = 0 from Fin.ext h0]
        ext i
        rw [Finset.mem_map_equiv]
        rfl
      · obtain ⟨hlt, himg⟩ := htree k h0
        obtain ⟨s, τ, hτ, hpar⟩ := ih _ (hk ▸ hlt) (par k) rfl
        refine ⟨r (lab k) * s, π (lab k) * τ, (hπ (lab k)).mul d hτ, ?_⟩
        rw [himg, hpar, Finset.map_map]
        rfl
  exact fun k => key k.val k rfl

end CFSG.Fischer
