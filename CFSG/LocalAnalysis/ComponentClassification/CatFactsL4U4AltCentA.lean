module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxAlt
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace AltCent

open CFSG Subgroup Equiv Equiv.Perm
open scoped commutatorElement

variable {m : ℕ}

theorem perm_apply_inv (f : Perm (Fin m)) (x : Fin m) : f (f⁻¹ x) = x := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

abbrev altOff (s : Finset (Fin m)) : Subgroup (Perm (Fin m)) :=
  (alternatingGroup {x : Fin m // x ∉ s}).map
    (ofSubtype : Perm {x : Fin m // x ∉ s} →* Perm (Fin m))

theorem mem_altOff {s : Finset (Fin m)} {x : Perm (Fin m)} (hx : ∀ a ∈ s, x a = a)
    (hsign : sign x = 1) : x ∈ altOff s := by
  have h₁ : ∀ y, x y ∉ s ↔ y ∉ s := by
    intro y
    constructor
    · intro h hy
      exact h (by rw [hx y hy]; exact hy)
    · intro h hxy
      apply h
      have h2 : x (x y) = x y := hx _ hxy
      have h3 : x y = y := x.injective h2
      rw [← h3]
      exact hxy
  have h₂ : ∀ y, x y ≠ y → y ∉ s := fun y hy hys => hy (hx y hys)
  refine ⟨x.subtypePerm h₁, ?_, ofSubtype_subtypePerm h₁ h₂⟩
  rw [SetLike.mem_coe, mem_alternatingGroup, sign_subtypePerm x h₁ h₂, hsign]

theorem apply_eq_of_mem_altOff {s : Finset (Fin m)} {x : Perm (Fin m)} (hx : x ∈ altOff s)
    {a : Fin m} (ha : a ∈ s) : x a = a := by
  obtain ⟨y, -, rfl⟩ := hx
  exact ofSubtype_apply_of_not_mem y (by simpa using ha)

theorem card_compl (s : Finset (Fin m)) :
    Fintype.card {x : Fin m // x ∉ s} = m - s.card := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : Fin m => x ∉ s) = Finset.univ \ s := by
    ext x
    simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin]

theorem card_altOff (s : Finset (Fin m)) (hs : 2 ≤ m - s.card) :
    Nat.card (altOff s) = (m - s.card).factorial / 2 := by
  have : Nontrivial {x : Fin m // x ∉ s} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [card_compl s]; omega)
  rw [card_map_of_injective ofSubtype_injective, Nat.card_eq_fintype_card,
    card_alternatingGroup, card_compl s]

theorem isSimpleGroup_altOff (s : Finset (Fin m)) (hs : 5 ≤ m - s.card) :
    IsSimpleGroup ↥(altOff s) := by
  have h1 : IsSimpleGroup (alternatingGroup {x : Fin m // x ∉ s}) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, card_compl s]; exact hs)
  exact (MulEquiv.isSimpleGroup_congr (equivMapOfInjective _ _ ofSubtype_injective)).mp h1

theorem three_cycle_mem_altOff {s : Finset (Fin m)} {a b c : Fin m} (ha : a ∉ s) (hb : b ∉ s)
    (hc : c ∉ s) (hab : b ≠ a) (hac : a ≠ c) : swap b a * swap a c ∈ altOff s := by
  refine mem_altOff (fun y hy => ?_) ?_
  · have hya : y ≠ a := fun h => ha (h ▸ hy)
    have hyb : y ≠ b := fun h => hb (h ▸ hy)
    have hyc : y ≠ c := fun h => hc (h ▸ hy)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hya hyc, swap_apply_of_ne_of_ne hyb hya]
  · rw [Perm.sign_mul, sign_swap hab, sign_swap hac]
    rfl

theorem eq_of_comm_altOff {s : Finset (Fin m)} (hs : 5 ≤ m - s.card) {ρ : Perm (Fin m)}
    (hρ : ∀ x ∈ altOff s, ρ * x = x * ρ) {a : Fin m} (ha : a ∉ s) : ρ a = a := by
  classical
  set t : Finset (Fin m) := (Finset.univ \ s).erase a with ht
  have htcard : t.card = m - s.card - 1 := by
    rw [ht, Finset.card_erase_of_mem (by simp [ha]),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hb]; omega : 0 < (t.erase b).card)
  obtain ⟨d, hd⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hc, Finset.card_erase_of_mem hb]; omega :
      0 < ((t.erase b).erase c).card)
  obtain ⟨e, he⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hd, Finset.card_erase_of_mem hc,
      Finset.card_erase_of_mem hb]; omega : 0 < (((t.erase b).erase c).erase d).card)
  simp only [ht, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and] at hb hc hd he
  obtain ⟨hba, hbs⟩ := hb
  obtain ⟨hcb, hca, hcs⟩ := hc
  obtain ⟨hdc, hdb, hda, hds⟩ := hd
  obtain ⟨hed, hec, heb, hea, hes⟩ := he
  have hn1 : List.Nodup [b, a, c] := by simp [hba, hca.symm, hcb.symm]
  have hn2 : List.Nodup [d, a, e] := by simp [hda, hea.symm, hed.symm]
  have h1 := Idx.apply_mem_support_of_comm
    (hρ _ (three_cycle_mem_altOff ha hbs hcs hba hca.symm)) (a := a)
    (by rw [support_swap_mul_swap hn1]; simp)
  have h2 := Idx.apply_mem_support_of_comm
    (hρ _ (three_cycle_mem_altOff ha hds hes hda hea.symm)) (a := a)
    (by rw [support_swap_mul_swap hn2]; simp)
  rw [support_swap_mul_swap hn1] at h1
  rw [support_swap_mul_swap hn2] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 | h1
  · rcases h2 with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) hdb.symm
    · exact h2
    · exact absurd (h1.symm.trans h2) heb.symm
  · exact h1
  · rcases h2 with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) hdc.symm
    · exact h2
    · exact absurd (h1.symm.trans h2) hec.symm

theorem sign_of_mem_altOff {s : Finset (Fin m)} {x : Perm (Fin m)} (hx : x ∈ altOff s) :
    sign x = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [sign_ofSubtype]
  exact hy

theorem conj_mem_altOff {s : Finset (Fin m)} {σ : Perm (Fin m)} (hσ : ∀ a, σ a ∈ s ↔ a ∈ s)
    {x : Perm (Fin m)} (hx : x ∈ altOff s) : σ * x * σ⁻¹ ∈ altOff s := by
  refine mem_altOff (fun a ha => ?_) ?_
  · have h1 : σ⁻¹ a ∈ s := by
      rw [← hσ, perm_apply_inv]
      exact ha
    rw [Perm.mul_apply, Perm.mul_apply, apply_eq_of_mem_altOff hx h1, perm_apply_inv]
  · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, sign_of_mem_altOff hx, mul_one,
      Int.units_mul_self]

theorem le_alternatingGroup_of_perfect {X : Subgroup (Perm (Fin m))} (hX : ⁅X, X⁆ = X) :
    X ≤ alternatingGroup (Fin m) := by
  calc X = ⁅X, X⁆ := hX.symm
    _ ≤ ⁅(⊤ : Subgroup (Perm (Fin m))), ⊤⁆ := commutator_mono le_top le_top
    _ ≤ alternatingGroup (Fin m) := alternatingGroup.commutator_perm_le

theorem mem_support_iff_of_comm {π x : Perm (Fin m)} (hx : x * π = π * x) (a : Fin m) :
    x a ∈ π.support ↔ a ∈ π.support := by
  rw [mem_support, mem_support]
  have h1 : π (x a) = x (π a) := by
    have := congrArg (fun f : Perm (Fin m) => f a) hx
    simpa [Perm.mul_apply] using this.symm
  rw [h1]
  exact ⟨fun h h' => h (by rw [h']), fun h h' => h (x.injective h')⟩

theorem fixes_support_of_perfect {π : Perm (Fin m)} {X : Subgroup (Perm (Fin m))}
    (hX : ⁅X, X⁆ = X) (hXπ : ∀ x ∈ X, x * π = π * x) (hcard : π.support.card ≤ 4) :
    ∀ x ∈ X, ∀ a ∈ π.support, x a = a := by
  classical
  let r : ↥X →* Perm {a : Fin m // a ∈ π.support} :=
    { toFun := fun x => (x : Perm (Fin m)).subtypePerm (mem_support_iff_of_comm (hXπ x x.2))
      map_one' := by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
  have hsolv : Group.IsSolvable (Perm {a : Fin m // a ∈ π.support}) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hcard)
  have hrp : Group.IsPerfect ↥r.range := Group.IsPerfect.range r
  have hrs : Group.IsSolvable ↥r.range := subgroup_solvable_of_solvable _
  have hsub : Subsingleton ↥r.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable _ hrs
  intro x hx a ha
  have h1 : r ⟨x, hx⟩ = 1 := by
    have : (⟨r ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩ : ↥r.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have h2 := congrArg (fun f : Perm {a : Fin m // a ∈ π.support} => (f ⟨a, ha⟩ : Fin m)) h1
  simpa [r] using h2

section Double

variable {i j k l f₁ f₂ : Fin m} {π : Perm (Fin m)}

theorem ne_of_nodup4 (hn : [i, j, k, l].Nodup) :
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp at hn

theorem ne_of_nodup6 (hn : [i, j, k, l, f₁, f₂].Nodup) :
    i ≠ f₁ ∧ i ≠ f₂ ∧ j ≠ f₁ ∧ j ≠ f₂ ∧ k ≠ f₁ ∧ k ≠ f₂ ∧ l ≠ f₁ ∧ l ≠ f₂ ∧ f₁ ≠ f₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp at hn

@[expose] def Orbitwise (π σ : Perm (Fin m)) : Prop :=
  ∀ p ∈ π.support, σ p = p ∨ σ p = π p

theorem orbitwise_conj {σ c : Perm (Fin m)} (hσ : Orbitwise π σ) (hc : c * π = π * c) :
    Orbitwise π (c * σ * c⁻¹) := by
  intro p hp
  have hc' : c⁻¹ * π = π * c⁻¹ := by
    calc c⁻¹ * π = c⁻¹ * (π * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * π) * c⁻¹ := by rw [hc]
      _ = π * c⁻¹ := by group
  have hp' : c⁻¹ p ∈ π.support := (mem_support_iff_of_comm hc' p).mpr hp
  have hπc : π (c⁻¹ p) = c⁻¹ (π p) := by
    have := congrArg (fun f : Perm (Fin m) => f p) hc'
    simpa [Perm.mul_apply] using this.symm
  rcases hσ _ hp' with h | h
  · left
    rw [Perm.mul_apply, Perm.mul_apply, h, perm_apply_inv]
  · right
    rw [Perm.mul_apply, Perm.mul_apply, h, hπc, perm_apply_inv]

theorem dt_apply (hπ : π = swap i j * swap k l) (hn : [i, j, k, l].Nodup) :
    π i = j ∧ π j = i ∧ π k = l ∧ π l = k ∧
      ∀ a, a ≠ i → a ≠ j → a ≠ k → a ≠ l → π a = a := by
  obtain ⟨hij, hik, hil, hjk, hjl, hkl⟩ := ne_of_nodup4 hn
  subst hπ
  refine ⟨?_, ?_, ?_, ?_, fun a hai haj hak hal => ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hik hil, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hjk hjl, swap_apply_right]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hak hal, swap_apply_of_ne_of_ne hai haj]

theorem mem_dt_support (hπ : π = swap i j * swap k l) (hn : [i, j, k, l].Nodup) {p : Fin m}
    (hp : p ∈ π.support) : p = i ∨ p = j ∨ p = k ∨ p = l := by
  obtain ⟨-, -, -, -, h5⟩ := dt_apply hπ hn
  by_contra h
  simp only [not_or] at h
  exact (mem_support.mp hp) (h5 p h.1 h.2.1 h.2.2.1 h.2.2.2)

theorem orbitwise_of_comm (hπ : π = swap i j * swap k l) (hn : [i, j, k, l, f₁, f₂].Nodup)
    {σ : Perm (Fin m)} (hσπ : σ * π = π * σ)
    (hσg : σ * (swap i j * swap f₁ f₂) = (swap i j * swap f₁ f₂) * σ) : Orbitwise π σ := by
  have hn4 : [i, j, k, l].Nodup := hn.sublist (by simp)
  obtain ⟨hπi, hπj, hπk, hπl, -⟩ := dt_apply hπ hn4
  obtain ⟨hij, hik, hil, hjk, hjl, hkl⟩ := ne_of_nodup4 hn4
  obtain ⟨hi1, hi2, hj1, hj2, hk1, hk2, hl1, hl2, -⟩ := ne_of_nodup6 hn
  set g := swap i j * swap f₁ f₂ with hg
  have hgi : g i = j := by rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hi1 hi2, swap_apply_left]
  have hgj : g j = i := by rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hj1 hj2, swap_apply_right]
  have hgk : g k = k := by
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hk1 hk2,
      swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have hgl : g l = l := by
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hl1 hl2,
      swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)]
  have hcomm : ∀ a, σ (g a) = g (σ a) := fun a => congrArg (fun f : Perm (Fin m) => f a) hσg
  have hcommπ : ∀ a, σ (π a) = π (σ a) := fun a => congrArg (fun f : Perm (Fin m) => f a) hσπ
  have hsupp : ∀ a ∈ π.support, σ a ∈ π.support := fun a ha =>
    (mem_support_iff_of_comm hσπ a).mpr ha
  have hmem : ∀ x, x ∈ π.support → x = i ∨ x = j ∨ x = k ∨ x = l :=
    fun x hx => mem_dt_support hπ hn4 hx
  have hi_supp : i ∈ π.support := mem_support.mpr (by rw [hπi]; exact Ne.symm hij)
  have hj_supp : j ∈ π.support := mem_support.mpr (by rw [hπj]; exact hij)
  have hk_supp : k ∈ π.support := mem_support.mpr (by rw [hπk]; exact Ne.symm hkl)
  have hl_supp : l ∈ π.support := mem_support.mpr (by rw [hπl]; exact hkl)
  have hIJ : ∀ p, (p = i ∨ p = j) → σ p = i ∨ σ p = j := by
    intro p hp
    have hgp : g p = π p := by rcases hp with rfl | rfl <;> simp [hgi, hgj, hπi, hπj]
    have h1 : π (σ p) = g (σ p) := by rw [← hcommπ, ← hgp, hcomm]
    have hps : p ∈ π.support := by rcases hp with rfl | rfl <;> assumption
    rcases hmem _ (hsupp p hps) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [h, hgk] at h1
      exact (mem_support.mp (h ▸ hsupp p hps)) h1
    · exfalso
      rw [h, hgl] at h1
      exact (mem_support.mp (h ▸ hsupp p hps)) h1
  have hKL : ∀ p, (p = k ∨ p = l) → σ p = k ∨ σ p = l := by
    intro p hp
    have hgp : g p = p := by rcases hp with rfl | rfl <;> simp [hgk, hgl]
    have h1 : g (σ p) = σ p := by rw [← hcomm, hgp]
    have hps : p ∈ π.support := by rcases hp with rfl | rfl <;> assumption
    rcases hmem _ (hsupp p hps) with h | h | h | h
    · exfalso
      rw [h, hgi] at h1
      exact hij h1.symm
    · exfalso
      rw [h, hgj] at h1
      exact hij h1
    · exact Or.inl h
    · exact Or.inr h
  intro p hp
  rcases hmem p hp with rfl | rfl | rfl | rfl
  · rcases hIJ _ (Or.inl rfl) with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hπi.symm)
  · rcases hIJ _ (Or.inr rfl) with h | h
    · exact Or.inr (h.trans hπj.symm)
    · exact Or.inl h
  · rcases hKL _ (Or.inl rfl) with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hπk.symm)
  · rcases hKL _ (Or.inr rfl) with h | h
    · exact Or.inr (h.trans hπl.symm)
    · exact Or.inl h

theorem eq_one_or_eq_of_comm (hπ : π = swap i j * swap k l) (hn : [i, j, k, l].Nodup)
    {σ : Perm (Fin m)} (hσ : Orbitwise π σ)
    (hσg : σ * (swap i k * swap j l) = (swap i k * swap j l) * σ)
    (hσF : ∀ a, a ≠ i → a ≠ j → a ≠ k → a ≠ l → σ a = a) : σ = 1 ∨ σ = π := by
  obtain ⟨hπi, hπj, hπk, hπl, hπF⟩ := dt_apply hπ hn
  obtain ⟨hij, hik, hil, hjk, hjl, hkl⟩ := ne_of_nodup4 hn
  set g := swap i k * swap j l with hg
  have hgi : g i = k := by rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hij hil, swap_apply_left]
  have hgj : g j = l := by
    rw [hg, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hkl)]
  have hcomm : ∀ a, σ (g a) = g (σ a) := fun a => congrArg (fun f : Perm (Fin m) => f a) hσg
  have hi_supp : i ∈ π.support := mem_support.mpr (by rw [hπi]; exact Ne.symm hij)
  have hj_supp : j ∈ π.support := mem_support.mpr (by rw [hπj]; exact hij)
  rcases hσ i hi_supp with h1 | h1
  ·
    have hσj : σ j = j := by
      rcases hσ j hj_supp with h | h
      · exact h
      · exfalso
        rw [hπj] at h
        exact hij (σ.injective (h.trans h1.symm)).symm
    have hσk : σ k = k := by rw [← hgi, hcomm, h1]
    have hσl : σ l = l := by rw [← hgj, hcomm, hσj]
    left
    ext a
    by_cases hai : a = i
    · rw [hai, h1]; rfl
    by_cases haj : a = j
    · rw [haj, hσj]; rfl
    by_cases hak : a = k
    · rw [hak, hσk]; rfl
    by_cases hal : a = l
    · rw [hal, hσl]; rfl
    rw [hσF a hai haj hak hal]; rfl
  ·
    rw [hπi] at h1
    have hσj : σ j = i := by
      rcases hσ j hj_supp with h | h
      · exfalso
        exact hij (σ.injective (h1.trans h.symm))
      · rw [h, hπj]
    have hgi' : g j = l := hgj
    have hσk : σ k = l := by rw [← hgi, hcomm, h1, hgj]
    have hσl : σ l = k := by rw [← hgj, hcomm, hσj, hgi]
    right
    ext a
    by_cases hai : a = i
    · rw [hai, h1, hπi]
    by_cases haj : a = j
    · rw [haj, hσj, hπj]
    by_cases hak : a = k
    · rw [hak, hσk, hπk]
    by_cases hal : a = l
    · rw [hal, hσl, hπl]
    rw [hσF a hai haj hak hal, hπF a hai haj hak hal]

end Double

end AltCent

end CFSG.ComponentClassification.CatFactsL4U4
