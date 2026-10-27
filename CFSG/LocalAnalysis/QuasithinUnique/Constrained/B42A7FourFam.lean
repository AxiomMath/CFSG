module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Dim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourFamData

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv Equiv.Perm

variable {S : Type} [CommGroup S] [Finite S] {G L A : Subgroup (MulAut S)} {m : ℕ}

theorem family_card_le {N c : ℕ} (F : Fin N → Subgroup S) (hc : ∀ i, Nat.card (F i) = c)
    (hd : ∀ i j, i ≠ j → F i ⊓ F j = ⊥) : N * (c - 1) + 1 ≤ Nat.card S := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let U : Fin N → Finset S := fun i => (Finset.univ.filter (fun x => x ∈ F i)).erase 1
  have hUcard : ∀ i, (U i).card = c - 1 := by
    intro i
    have h1 : (Finset.univ.filter (fun x => x ∈ F i)).card = c := by
      rw [← hc i, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [U]
    rw [Finset.card_erase_of_mem (by simp [one_mem]), h1]
  have hdisj : (Set.univ : Set (Fin N)).PairwiseDisjoint U := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    simp only [U, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    have : x ∈ F i ⊓ F j := ⟨hxi.2, hxj.2⟩
    rw [hd i j hij] at this
    exact hxi.1 (Subgroup.mem_bot.1 this)
  have hunion : (Finset.univ.biUnion U).card = N * (c - 1) := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj (Set.mem_univ i) (Set.mem_univ j) hij)]
    simp [hUcard]
  have hsub : (Finset.univ.biUnion U) ⊆ Finset.univ.erase 1 := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, U, Finset.mem_erase,
      Finset.mem_filter] at hx
    obtain ⟨i, hx1, _⟩ := hx
    simp [hx1]
  have hle := Finset.card_le_card hsub
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card] at hle
  have hpos : 0 < Nat.card S := Nat.card_pos
  omega

theorem swapProd_mem {n : ℕ} (l : List (Fin n × Fin n)) (hlen : l.length % 2 = 0)
    (hne : ∀ p ∈ l, p.1 ≠ p.2) : GenEntry.swapProd l ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup]
  unfold GenEntry.swapProd
  have hsw : ∀ g ∈ l.map (fun p => swap p.1 p.2), g.IsSwap := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact ⟨p.1, p.2, hne p hp, rfl⟩
  rw [Perm.sign_prod_list_swap hsw, List.length_map]
  have : Even l.length := Nat.even_iff.2 hlen
  simp [this.neg_one_pow]

omit [Finite S] in
theorem fixV_conj_inf_eq_bot (C : Bridge.Alt57.Ctx G L m)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) (ι : ↥L ≃* alternatingGroup (Fin m))
    (e : ↥G →* Perm (Fin m)) (hinj : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin m))) (g₁ g₂ : ↥G)
    (hcl : alternatingGroup (Fin m) ≤ Subgroup.closure
      {x | (∃ b ∈ (A.subgroupOf G).map e, x = e g₁ * b * (e g₁)⁻¹) ∨
        (∃ b ∈ (A.subgroupOf G).map e, x = e g₂ * b * (e g₂)⁻¹)}) :
    fixV (A.map (MulAut.conj (g₁ : MulAut S)).toMonoidHom) ⊓
      fixV (A.map (MulAut.conj (g₂ : MulAut S)).toMonoidHom) = ⊥ := by
  set A' : Subgroup ↥G := A.subgroupOf G with hA'
  rw [eq_bot_iff]
  intro v hv
  have hv1 : v ∈ fixV (A.map (MulAut.conj (g₁ : MulAut S)).toMonoidHom) := hv.1
  have hv2 : v ∈ fixV (A.map (MulAut.conj (g₂ : MulAut S)).toMonoidHom) := hv.2
  let Stab : Subgroup ↥G :=
    { carrier := {x | ((x : ↥G) : MulAut S) v = v}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        have hx' : ((x : ↥G) : MulAut S) v = v := hx
        have hy' : ((y : ↥G) : MulAut S) v = v := hy
        show ((x * y : ↥G) : MulAut S) v = v
        rw [Subgroup.coe_mul, MulAut.mul_apply, hy', hx']
      inv_mem' := fun {x} hx => by
        have hx' : ((x : ↥G) : MulAut S) v = v := hx
        show (((x⁻¹ : ↥G) : MulAut S)) v = v
        rw [Subgroup.coe_inv]
        have := congrArg (fun w => ((x : ↥G) : MulAut S)⁻¹ w) hx'
        simpa using this.symm }
  let Hg : Subgroup ↥G := Subgroup.closure
    {x : ↥G | (∃ a ∈ A', x = g₁ * a * g₁⁻¹) ∨ (∃ a ∈ A', x = g₂ * a * g₂⁻¹)}
  have hHS : Hg ≤ Stab := by
    refine (Subgroup.closure_le Stab).2 ?_
    rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · have hmem : ((g₁ : ↥G) : MulAut S) * ((a : ↥G) : MulAut S) * ((g₁ : ↥G) : MulAut S)⁻¹ ∈
          A.map (MulAut.conj (g₁ : MulAut S)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨((a : ↥G) : MulAut S), Subgroup.mem_subgroupOf.1 ha, by simp⟩
      have := hv1 _ hmem
      show (((g₁ * a * g₁⁻¹ : ↥G) : MulAut S)) v = v
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    · have hmem : ((g₂ : ↥G) : MulAut S) * ((a : ↥G) : MulAut S) * ((g₂ : ↥G) : MulAut S)⁻¹ ∈
          A.map (MulAut.conj (g₂ : MulAut S)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨((a : ↥G) : MulAut S), Subgroup.mem_subgroupOf.1 ha, by simp⟩
      have := hv2 _ hmem
      show (((g₂ * a * g₂⁻¹ : ↥G) : MulAut S)) v = v
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hAle : alternatingGroup (Fin m) ≤ Hg.map e := by
    refine hcl.trans ?_
    rw [Subgroup.closure_le]
    rintro _ (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩), rfl⟩
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩), rfl⟩
  have hvL : v ∈ fixV L := by
    intro l hl
    have hlA : (ι ⟨l, hl⟩ : Perm (Fin m)) ∈ alternatingGroup (Fin m) := (ι ⟨l, hl⟩).2
    obtain ⟨h, hh, hel⟩ := Subgroup.mem_map.1 (hAle hlA)
    have : h = ⟨l, C.le_G hl⟩ := hinj (by rw [hel, hL ⟨l, hl⟩])
    have hS' := hHS hh
    rw [this] at hS'
    exact hS'
  rw [fixV_eq_bot_of_irr hirr C.nonab] at hvL
  exact hvL

set_option maxRecDepth 100000 in
theorem swap01_conj_x5 : ∀ x ∈ x5, swap 0 1 * x * (swap 0 1)⁻¹ = x := by decide +kernel

omit [Finite S] in
theorem sign_eq_neg_one_of_not_mem {σ : Perm (Fin 7)} (h : σ ∉ alternatingGroup (Fin 7)) :
    Perm.sign σ = -1 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with h' | h'
  · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h') h
  · exact h'

theorem typeB_false (C : Bridge.Alt57.Ctx G L 7) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hA : IsFFStarOffender G A) (ι : ↥L ≃* alternatingGroup (Fin 7)) (e : ↥G →* Perm (Fin 7))
    (hinj : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin 7)))
    (hS : Nat.card S = 2 ^ 4) (hcard : Nat.card A = 4)
    (hB : ∃ a b c' d e' f : Fin 7, [a, b, c', d, e', f].Nodup ∧
      swap a b * swap c' d ∈ (A.subgroupOf G).map e ∧
      swap a b * swap e' f ∈ (A.subgroupOf G).map e ∧
      swap c' d * swap e' f ∈ (A.subgroupOf G).map e) : False := by
  classical
  obtain ⟨a, b, c', d, e', f, hnd, h1, h2, h3⟩ := hB
  set B : Subgroup (Perm (Fin 7)) := (A.subgroupOf G).map e with hBdef
  obtain ⟨σ, hσ⟩ := exists_perm_list [0, 1, 2, 3, 4, 5] [a, b, c', d, e', f] (by decide) hnd rfl
  have s0 : σ 0 = a := hσ 0 (by simp)
  have s1 : σ 1 = b := hσ 1 (by simp)
  have s2 : σ 2 = c' := hσ 2 (by simp)
  have s3 : σ 3 = d := hσ 3 (by simp)
  have s4 : σ 4 = e' := hσ 4 (by simp)
  have s5 : σ 5 = f := hσ 5 (by simp)
  have hX : ∀ x ∈ x5, σ * x * σ⁻¹ ∈ B := by
    intro x hx
    simp only [x5, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [conj_swap_mul_swap, s0, s1, s2, s3]
      exact h1
    · rw [conj_swap_mul_swap, s0, s1, s4, s5]
      exact h2
    · rw [conj_swap_mul_swap, s2, s3, s4, s5]
      exact h3
  have hswap01 := swap01_conj_x5
  obtain ⟨τ, hτ, hτX⟩ : ∃ τ ∈ alternatingGroup (Fin 7), ∀ x ∈ x5, τ * x * τ⁻¹ ∈ B := by
    by_cases hev : σ ∈ alternatingGroup (Fin 7)
    · exact ⟨σ, hev, hX⟩
    · refine ⟨σ * swap 0 1, ?_, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
          sign_eq_neg_one_of_not_mem hev, Equiv.Perm.sign_swap (by decide)]
        decide
      · intro x hx
        have e1 : (σ * swap 0 1) * x * (σ * swap 0 1)⁻¹ = σ * (swap 0 1 * x * (swap 0 1)⁻¹) * σ⁻¹ := by
          group
        rw [e1, hswap01 x hx]
        exact hX x hx
  have hlift : ∀ i : Fin 6, ∃ g : ↥G,
      e g = τ * GenEntry.swapProd (cj5.getD i.val []) * τ⁻¹ := by
    intro i
    have hmem : GenEntry.swapProd (cj5.getD i.val []) ∈ alternatingGroup (Fin 7) := by
      have hc : cj5.getD i.val [] ∈ cj5 := by
        have hlen : cj5.length = 6 := by decide
        rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
        exact List.getElem_mem _
      obtain ⟨hl1, hl2⟩ := cj5_even _ hc
      exact swapProd_mem _ hl1 hl2
    have hf : τ * GenEntry.swapProd (cj5.getD i.val []) * τ⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup (Fin 7)).mul_mem ((alternatingGroup (Fin 7)).mul_mem hτ hmem)
        ((alternatingGroup (Fin 7)).inv_mem hτ)
    obtain ⟨l, hl⟩ := ι.surjective ⟨_, hf⟩
    exact ⟨⟨(l : MulAut S), C.le_G l.2⟩, by rw [hL, hl]⟩
  choose g hg using hlift
  let K : Fin 6 → Subgroup S := fun i =>
    fixV (A.map (MulAut.conj ((g i : ↥G) : MulAut S)).toMonoidHom)
  have hd : ∀ i j : Fin 6, i < j → K i ⊓ K j = ⊥ := by
    intro i j hij
    obtain ⟨t, ht, ht1, ht2⟩ := tab5_cover i j hij
    have heok := ent5_ok (⟨x5, xt5, [cj5.getD t.1 [], cj5.getD t.2.1 []], t.2.2⟩ : GenEntry 7)
      (List.mem_map.2 ⟨t, ht, rfl⟩)
    have hcl0 := cert_conj_closure (by norm_num) τ
      (⟨x5, xt5, [cj5.getD t.1 [], cj5.getD t.2.1 []], t.2.2⟩ : GenEntry 7) heok hτX
    refine fixV_conj_inf_eq_bot C hirr ι e hinj hL (g i) (g j) (hcl0.trans (Subgroup.closure_mono ?_))
    rintro _ ⟨c, hc, b, hb, rfl⟩
    have hc' : c ∈ [τ * GenEntry.swapProd (cj5.getD t.1 []) * τ⁻¹,
        τ * GenEntry.swapProd (cj5.getD t.2.1 []) * τ⁻¹] := by
      simpa [GenEntry.conjugators, GenEntry.swapProd] using hc
    rw [ht1, ht2] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact Or.inl ⟨b, hb, by rw [hg i]⟩
    · exact Or.inr ⟨b, hb, by rw [hg j]⟩
  have hK : ∀ i j : Fin 6, i ≠ j → K i ⊓ K j = ⊥ := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hd i j h
    · rw [inf_comm]
      exact hd j i h
  have hKc : ∀ i : Fin 6, Nat.card (K i) = Nat.card (fixV A) := fun i =>
    card_fixV_map_conj A _
  have hcount := family_card_le K hKc hK
  have hoff := hA.card_le (bot_le : (⊥ : Subgroup (MulAut S)) ≤ A)
  rw [B1.card_bot_mul_card_fixV] at hoff
  have hS16 : Nat.card S = 16 := by rw [hS]; norm_num
  rw [hS16] at hcount hoff
  rw [hcard] at hoff
  omega

end CFSG.QuasithinUnique.B42A57
