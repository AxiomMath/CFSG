module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

variable {n : ℕ}

theorem exists_perm_color {ι : Type} [DecidableEq ι] (c c' : Fin n → ι)
    (h : ∀ k, (Finset.univ.filter fun x => c x = k).card =
      (Finset.univ.filter fun x => c' x = k).card) :
    ∃ p : Equiv.Perm (Fin n), ∀ x, c' (p x) = c x := by
  classical
  let φ : ∀ k, {x // c x = k} ≃ {x // c' x = k} := fun k =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]; exact h k)
  refine ⟨(Equiv.sigmaFiberEquiv c).symm.trans
    ((Equiv.sigmaCongrRight φ).trans (Equiv.sigmaFiberEquiv c')), fun x => ?_⟩
  show c' ((Equiv.sigmaFiberEquiv c') ((Equiv.sigmaCongrRight φ) ((Equiv.sigmaFiberEquiv c).symm x)))
    = c x
  have h1 : (Equiv.sigmaFiberEquiv c).symm x = ⟨c x, ⟨x, rfl⟩⟩ := rfl
  rw [h1]
  show c' (φ (c x) ⟨x, rfl⟩).1 = c x
  exact (φ (c x) ⟨x, rfl⟩).2

theorem fiber_card (s t s' t' : Finset (Fin n)) (hs : s.card = s'.card) (ht : t.card = t'.card)
    (hst : (s ∩ t).card = (s' ∩ t').card) :
    ∀ k : Bool × Bool, (Finset.univ.filter fun x => (decide (x ∈ s), decide (x ∈ t)) = k).card =
      (Finset.univ.filter fun x => (decide (x ∈ s'), decide (x ∈ t')) = k).card := by
  classical
  have h1 := Finset.card_sdiff_add_card_inter s t
  have h2 := Finset.card_sdiff_add_card_inter s' t'
  have h3 := Finset.card_sdiff_add_card_inter t s
  have h4 := Finset.card_sdiff_add_card_inter t' s'
  have h5 := Finset.card_union_add_card_inter s t
  have h6 := Finset.card_union_add_card_inter s' t'
  rw [Finset.inter_comm t s] at h3
  rw [Finset.inter_comm t' s'] at h4
  rintro ⟨a, b⟩
  cases a <;> cases b
  · have e : (Finset.univ.filter fun x => (decide (x ∈ s), decide (x ∈ t)) = (false, false)) =
        (s ∪ t)ᶜ := by ext x; simp
    have e' : (Finset.univ.filter fun x => (decide (x ∈ s'), decide (x ∈ t')) = (false, false)) =
        (s' ∪ t')ᶜ := by ext x; simp
    rw [e, e', Finset.card_compl, Finset.card_compl]
    omega
  · have e : (Finset.univ.filter fun x => (decide (x ∈ s), decide (x ∈ t)) = (false, true)) =
        t \ s := by ext x; simp [and_comm]
    have e' : (Finset.univ.filter fun x => (decide (x ∈ s'), decide (x ∈ t')) = (false, true)) =
        t' \ s' := by ext x; simp [and_comm]
    rw [e, e']
    omega
  · have e : (Finset.univ.filter fun x => (decide (x ∈ s), decide (x ∈ t)) = (true, false)) =
        s \ t := by ext x; simp
    have e' : (Finset.univ.filter fun x => (decide (x ∈ s'), decide (x ∈ t')) = (true, false)) =
        s' \ t' := by ext x; simp
    rw [e, e']
    omega
  · have e : (Finset.univ.filter fun x => (decide (x ∈ s), decide (x ∈ t)) = (true, true)) =
        s ∩ t := by ext x; simp
    have e' : (Finset.univ.filter fun x => (decide (x ∈ s'), decide (x ∈ t')) = (true, true)) =
        s' ∩ t' := by ext x; simp
    rw [e, e']
    exact hst

theorem exists_perm_pair (α β δ : Finset (Fin n)) (hα : α.card = 4) (hβ : β.card = 4)
    (hδ : δ.card = 4) (hi : (α ∩ β).card = (α ∩ δ).card) :
    ∃ p : Equiv.Perm (Fin n), (∀ x, p x ∈ α ↔ x ∈ α) ∧ (∀ x, p x ∈ δ ↔ x ∈ β) := by
  classical
  obtain ⟨p, hp⟩ := exists_perm_color (fun x => (decide (x ∈ α), decide (x ∈ β)))
    (fun x => (decide (x ∈ α), decide (x ∈ δ)))
    (fiber_card α β α δ rfl (by rw [hβ, hδ]) hi)
  refine ⟨p, fun x => ?_, fun x => ?_⟩
  · have := congrArg Prod.fst (hp x)
    simpa using this
  · have := congrArg Prod.snd (hp x)
    simpa using this

theorem swap_mem_iff {S : Finset (Fin n)} {x y : Fin n} (h : x ∈ S ↔ y ∈ S) (w : Fin n) :
    Equiv.swap x y w ∈ S ↔ w ∈ S := by
  by_cases hx : w = x
  · subst hx; rw [Equiv.swap_apply_left]; exact h.symm
  · by_cases hy : w = y
    · subst hy; rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

theorem map_eq_of_iff (p : Equiv.Perm (Fin n)) (s t : Finset (Fin n))
    (h : ∀ x, p x ∈ t ↔ x ∈ s) : s.map p.toEmbedding = t := by
  ext y
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mpr hx
  · intro hy
    refine ⟨p.symm y, ?_, Equiv.apply_symm_apply _ _⟩
    rw [← h, Equiv.apply_symm_apply]; exact hy

theorem exists_even_perm_stab (α β δ : Finset (Fin n)) (hα : α.card = 4) (hβ : β.card = 4)
    (hδ : δ.card = 4) (hi : (α ∩ β).card = (α ∩ δ).card) :
    ∃ p : Equiv.Perm (Fin n), Equiv.Perm.sign p = 1 ∧ α.map p.toEmbedding = α ∧
      β.map p.toEmbedding = δ := by
  classical
  obtain ⟨p, hpα, hpδ⟩ := exists_perm_pair α β δ hα hβ hδ hi
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h
  · exact ⟨p, h, map_eq_of_iff p α α hpα, map_eq_of_iff p β δ hpδ⟩
  ·
    obtain ⟨x, y, hxy, hxα, hyα, hxyδ⟩ : ∃ x y : Fin n, x ≠ y ∧ x ∈ α ∧ y ∈ α ∧
        (x ∈ δ ↔ y ∈ δ) := by
      by_cases h2 : 2 ≤ (α ∩ δ).card
      · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (α ∩ δ).card)
        exact ⟨x, y, hxy, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hy).1,
          ⟨fun _ => (Finset.mem_inter.mp hy).2, fun _ => (Finset.mem_inter.mp hx).2⟩⟩
      · have h3 : 1 < (α \ δ).card := by
          have := Finset.card_sdiff_add_card_inter α δ
          omega
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h3
        exact ⟨x, y, hxy, (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hy).1,
          ⟨fun h => absurd h (Finset.mem_sdiff.mp hx).2,
            fun h => absurd h (Finset.mem_sdiff.mp hy).2⟩⟩
    refine ⟨Equiv.swap x y * p, ?_, map_eq_of_iff _ α α fun w => ?_, map_eq_of_iff _ β δ fun w => ?_⟩
    · rw [map_mul, h, Equiv.Perm.sign_swap hxy]; decide
    · exact (swap_mem_iff ⟨fun _ => hyα, fun _ => hxα⟩ (p w)).trans (hpα w)
    · exact (swap_mem_iff hxyδ (p w)).trans (hpδ w)

theorem map_inter_card (p : Equiv.Perm (Fin n)) (s t : Finset (Fin n)) :
    (s.map p.toEmbedding ∩ t.map p.toEmbedding).card = (s ∩ t).card := by
  rw [← Finset.map_inter, Finset.card_map]

theorem closed_of_block {X : Set (Finset (Fin n))} (hXc : ∀ x ∈ X, x.card = 4)
    (hrule : ∀ x ∈ X, ∀ y ∈ X, ∀ p : Equiv.Perm (Fin n), Equiv.Perm.sign p = 1 →
      x.map p.toEmbedding ∈ X → y.map p.toEmbedding ∈ X)
    {α β : Finset (Fin n)} (hα : α ∈ X) (hβ : β ∈ X) :
    ∀ γ ∈ X, ∀ δ : Finset (Fin n), δ.card = 4 → (γ ∩ δ).card = (α ∩ β).card → δ ∈ X := by
  intro γ hγ δ hδ hi
  obtain ⟨q, hq, hqα⟩ := exists_even_perm (hXc α hα) (hXc γ hγ)
  have hα' : γ.map q⁻¹.toEmbedding = α := by
    rw [← hqα, map_map_perm, inv_mul_cancel, map_perm_one]
  have hδ0 : (δ.map q⁻¹.toEmbedding).card = 4 := by rw [Finset.card_map]; exact hδ
  have hi0 : (α ∩ β).card = (α ∩ δ.map q⁻¹.toEmbedding).card := by
    rw [← hi, ← map_inter_card q⁻¹ γ δ, hα']
  obtain ⟨p, hp, hpα, hpβ⟩ := exists_even_perm_stab α β (δ.map q⁻¹.toEmbedding) (hXc α hα)
    (hXc β hβ) hδ0 hi0
  have hmem : δ.map q⁻¹.toEmbedding ∈ X := by
    have := hrule α hα β hβ p hp (by rw [hpα]; exact hα)
    rwa [hpβ] at this
  have := hrule α hα _ hmem q hq (by rw [hqα]; exact hγ)
  rwa [map_map_perm, mul_inv_cancel, map_perm_one] at this

theorem exists_common_nbr (hn : 9 ≤ n) {γ δ : Finset (Fin n)} (hγ : γ.card = 4) (hδ : δ.card = 4)
    (h3 : (γ ∩ δ).card = 3) {i : ℕ} (hi : i ≤ 2) :
    ∃ ε : Finset (Fin n), ε.card = 4 ∧ (γ ∩ ε).card = i ∧ (δ ∩ ε).card = i := by
  classical
  have hR : 4 ≤ ((γ ∪ δ)ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_union_add_card_inter γ δ
    omega
  obtain ⟨Ci, hCi, hCic⟩ := Finset.exists_subset_card_eq (s := γ ∩ δ) (n := i) (by omega)
  obtain ⟨Rj, hRj, hRjc⟩ := Finset.exists_subset_card_eq (s := (γ ∪ δ)ᶜ) (n := 4 - i) (by omega)
  have hdisj : Disjoint Ci Rj := by
    rw [Finset.disjoint_left]
    intro x hx hxR
    have := hRj hxR
    have h1 := hCi hx
    rw [Finset.mem_compl, Finset.mem_union] at this
    exact this (Or.inl (Finset.mem_inter.mp h1).1)
  refine ⟨Ci ∪ Rj, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hCic, hRjc]; omega
  · have : γ ∩ (Ci ∪ Rj) = Ci := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxγ, hxC | hxR⟩
        · exact hxC
        · have := hRj hxR
          rw [Finset.mem_compl, Finset.mem_union] at this
          exact absurd (Or.inl hxγ) this
      · intro hx
        exact ⟨(Finset.mem_inter.mp (hCi hx)).1, Or.inl hx⟩
    rw [this, hCic]
  · have : δ ∩ (Ci ∪ Rj) = Ci := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxγ, hxC | hxR⟩
        · exact hxC
        · have := hRj hxR
          rw [Finset.mem_compl, Finset.mem_union] at this
          exact absurd (Or.inr hxγ) this
      · intro hx
        exact ⟨(Finset.mem_inter.mp (hCi hx)).2, Or.inl hx⟩
    rw [this, hCic]

theorem johnson_connected {X : Set (Finset (Fin n))} {α : Finset (Fin n)} (hαc : α.card = 4)
    (hα : α ∈ X)
    (hcl3 : ∀ γ ∈ X, ∀ δ : Finset (Fin n), δ.card = 4 → (γ ∩ δ).card = 3 → δ ∈ X) :
    ∀ δ : Finset (Fin n), δ.card = 4 → δ ∈ X := by
  classical
  suffices h : ∀ d : ℕ, ∀ δ : Finset (Fin n), δ.card = 4 → (δ \ α).card = d → δ ∈ X by
    exact fun δ hδ => h _ δ hδ rfl
  intro d
  induction d with
  | zero =>
    intro δ hδ hd
    have hsub : δ ⊆ α := by
      intro x hx
      by_contra hxα
      have : x ∈ δ \ α := Finset.mem_sdiff.mpr ⟨hx, hxα⟩
      rw [Finset.card_eq_zero] at hd
      rw [hd] at this
      simp at this
    have : δ = α := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [this]; exact hα
  | succ d ih =>
    intro δ hδ hd
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (δ \ α).card)
    have hcards : (α \ δ).card = (δ \ α).card := by
      have h1 := Finset.card_sdiff_add_card_inter α δ
      have h2 := Finset.card_sdiff_add_card_inter δ α
      rw [Finset.inter_comm δ α] at h2
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (α \ δ).card)
    have hxδ : x ∈ δ := (Finset.mem_sdiff.mp hx).1
    have hxα : x ∉ α := (Finset.mem_sdiff.mp hx).2
    have hyα : y ∈ α := (Finset.mem_sdiff.mp hy).1
    have hyδ : y ∉ δ := (Finset.mem_sdiff.mp hy).2
    have hyne : y ∉ δ.erase x := fun h => hyδ (Finset.mem_of_mem_erase h)
    have hcard' : (insert y (δ.erase x)).card = 4 := by
      rw [Finset.card_insert_of_notMem hyne, Finset.card_erase_of_mem hxδ]; omega
    have hdiff : (insert y (δ.erase x)) \ α = (δ \ α).erase x := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hz | ⟨hzx, hzδ⟩, hzα⟩
        · exact absurd (hz ▸ hyα) hzα
        · exact ⟨hzx, hzδ, hzα⟩
      · rintro ⟨hzx, hzδ, hzα⟩
        exact ⟨Or.inr ⟨hzx, hzδ⟩, hzα⟩
    have hmem := ih (insert y (δ.erase x)) hcard' (by
      rw [hdiff, Finset.card_erase_of_mem hx]; omega)
    refine hcl3 _ hmem δ hδ ?_
    have : insert y (δ.erase x) ∩ δ = δ.erase x := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hz | hz, hzδ⟩
        · exact absurd (hz ▸ hzδ) hyδ
        · exact hz
      · intro hz
        exact ⟨Or.inr hz, hz.2⟩
    rw [this, Finset.card_erase_of_mem hxδ]; omega

theorem fourSetPrim_ge_nine (hn : 9 ≤ n) : FourSetPrim n := by
  intro X hXc α hα hex rule γ hγ
  obtain ⟨β, hβ, hne⟩ := hex
  have hi3 : (α ∩ β).card ≤ 3 := by
    by_contra hcon
    have h4 : (α ∩ β).card = 4 := by
      have := Finset.card_le_card (Finset.inter_subset_left : α ∩ β ⊆ α)
      have := hXc α hα
      omega
    have e1 : α ∩ β = α :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h4, hXc α hα])
    have e2 : α ⊆ β := by rw [← e1]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le e2 (by rw [hXc α hα, hXc β hβ])).symm
  have hcl := closed_of_block hXc rule hα hβ
  have hcl3 : ∀ γ ∈ X, ∀ δ : Finset (Fin n), δ.card = 4 → (γ ∩ δ).card = 3 → δ ∈ X := by
    intro γ hγ δ hδ h3
    by_cases hi : (α ∩ β).card = 3
    · exact hcl γ hγ δ hδ (h3.trans hi.symm)
    · obtain ⟨ε, hε, hγε, hδε⟩ := exists_common_nbr hn (hXc γ hγ) hδ h3
        (i := (α ∩ β).card) (by omega)
      have hεX := hcl γ hγ ε hε hγε
      exact hcl ε hεX δ hδ (by rw [Finset.inter_comm]; exact hδε)
  exact johnson_connected (hXc α hα) hα hcl3 γ hγ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
