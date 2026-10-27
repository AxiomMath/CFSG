module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def invs : Finset (Perm (Fin 5)) := Finset.univ.filter fun g => g * g = 1

@[expose] def IsSw (g : Perm (Fin 5)) : Prop := ∃ x y : Fin 5, x ≠ y ∧ g = swap x y

instance (g : Perm (Fin 5)) : Decidable (IsSw g) := by unfold IsSw; infer_instance

theorem isSw_iff (g : Perm (Fin 5)) : IsSw g ↔ g.IsSwap := Iff.rfl

@[expose] def fixOf (a b : Perm (Fin 5)) : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun x => isEven x ∧ pact a x = x ∧ pact b x = x

@[expose] def four (a b : Perm (Fin 5)) : Finset (Perm (Fin 5)) := {1, a, b, a * b}

@[expose] def SwapOK (a b : Perm (Fin 5)) : Prop :=
  ∀ g ∈ four a b, g = 1 ∨ IsSw g ∨ ∃ s ∈ four a b, ∃ t ∈ four a b, IsSw s ∧ IsSw t ∧ g = s * t

instance (a b : Perm (Fin 5)) : Decidable (SwapOK a b) := by unfold SwapOK; infer_instance

theorem ff_pair : ∀ a ∈ invs, ∀ b ∈ invs, a * b = b * a →
    16 ≤ (four a b).card * (fixOf a b).card → SwapOK a b := by
  decide +kernel

theorem three_dep : ∀ a ∈ invs, ∀ b ∈ invs, ∀ c ∈ invs, a * b = b * a → a * c = c * a →
    b * c = c * b → c ∈ four a b ∨ b ∈ four a c ∨ a ∈ four b c := by
  decide +kernel

theorem mem_invs {g : Perm (Fin 5)} : g ∈ invs ↔ g * g = 1 := by simp [invs]

theorem mem_four {a b g : Perm (Fin 5)} : g ∈ four a b ↔ g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  simp [four]

theorem exists_four (P : Subgroup (Perm (Fin 5))) (hP : ∀ a ∈ P, a * a = 1)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∃ a ∈ P, ∃ b ∈ P, ∀ g, g ∈ P ↔ g ∈ four a b := by
  classical
  have hsub : ∀ a ∈ P, ∀ b ∈ P, ∀ g ∈ four a b, g ∈ P := by
    intro a ha b hb g hg
    rcases mem_four.1 hg with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ha
    · exact hb
    · exact mul_mem ha hb
  by_cases h1 : ∀ g ∈ P, g = 1
  · refine ⟨1, one_mem _, 1, one_mem _, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
    · rw [h1 g hg]; simp [four]
    · exact hsub 1 (one_mem _) 1 (one_mem _) g hg
  push Not at h1
  obtain ⟨a, haP, ha1⟩ := h1
  by_cases h2 : ∀ g ∈ P, g ∈ four a 1
  · exact ⟨a, haP, 1, one_mem _, fun g => ⟨h2 g, hsub a haP 1 (one_mem _) g⟩⟩
  push Not at h2
  obtain ⟨b, hbP, hb⟩ := h2
  by_cases h3 : ∀ g ∈ P, g ∈ four a b
  · exact ⟨a, haP, b, hbP, fun g => ⟨h3 g, hsub a haP b hbP g⟩⟩
  push Not at h3
  obtain ⟨c, hcP, hcn⟩ := h3
  exfalso
  have hb1 : b ≠ 1 := fun h => hb (by rw [h]; simp [four])
  have hba : b ≠ a := fun h => hb (by rw [h]; simp [four])
  have hcm := mem_four (a := a) (b := b) (g := c)
  have haa := hP a haP
  have hbb := hP b hbP
  have hcc := hP c hcP
  have hab := hc a haP b hbP
  have hac := hc a haP c hcP
  have hbc := hc b hbP c hcP
  rcases three_dep a (mem_invs.2 haa) b (mem_invs.2 hbb) c (mem_invs.2 hcc) hab hac hbc with h | h | h
  · exact hcn h
  · rcases mem_four.1 h with h | h | h | h
    · exact hb1 h
    · exact hba h
    · exact hcn (mem_four.2 (Or.inr (Or.inr (Or.inl h.symm))))
    · apply hcn
      refine mem_four.2 (Or.inr (Or.inr (Or.inr ?_)))
      have : c = a * (a * c) := by rw [← mul_assoc, haa, one_mul]
      rw [this, ← h]
  · rcases mem_four.1 h with h | h | h | h
    · exact ha1 h
    · exact hba h.symm
    · exact hcn (mem_four.2 (Or.inr (Or.inl h.symm)))
    · apply hcn
      refine mem_four.2 (Or.inr (Or.inr (Or.inr ?_)))
      have : c = b * (b * c) := by rw [← mul_assoc, hbb, one_mul]
      rw [this, ← h, hab]

@[expose] def FixΔ (P : Subgroup (Perm (Fin 5))) : Set (evenWeight 5) :=
  {w | ∀ σ ∈ P, vact σ w = w}

theorem exists_four_card (P : Subgroup (Perm (Fin 5))) (hP : ∀ a ∈ P, a * a = 1)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∃ a ∈ P, ∃ b ∈ P, (∀ g, g ∈ P ↔ g ∈ four a b) ∧ Nat.card P = (four a b).card ∧
      Nat.card (FixΔ P) = (fixOf a b).card := by
  classical
  obtain ⟨a, haP, b, hbP, hab⟩ := exists_four P hP hc
  refine ⟨a, haP, b, hbP, hab, ?_, ?_⟩
  · have h : ((P : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5))) = ↑(four a b) := by
      ext g; simpa using hab g
    rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  · rw [← Fintype.card_coe (fixOf a b), ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1.1, by
          simp only [fixOf, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w.1.2, congrArg Subtype.val (w.2 a haP), congrArg Subtype.val (w.2 b hbP)⟩⟩
        invFun := fun x => ⟨⟨x.1, by
          have := x.2
          simp only [fixOf, Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this.1⟩, by
          intro σ hσ
          have hx := x.2
          simp only [fixOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          apply Subtype.ext
          rcases mem_four.1 ((hab σ).1 hσ) with rfl | rfl | rfl | rfl
          · rfl
          · exact hx.2.1
          · exact hx.2.2
          · show pact (a * b) x.1 = x.1
            rw [pact_mul, hx.2.2, hx.2.1]⟩
        left_inv := fun w => rfl
        right_inv := fun x => rfl }

theorem swapGen_of_ff (P : Subgroup (Perm (Fin 5))) (hP : ∀ a ∈ P, a * a = 1)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hff : 16 ≤ Nat.card P * Nat.card (FixΔ P)) :
    ∀ g ∈ P, g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ P ∧ s.IsSwap} := by
  classical
  obtain ⟨a, haP, b, hbP, hab, hcardP, hfix⟩ := exists_four_card P hP hc
  rw [hcardP, hfix] at hff
  have hOK := ff_pair a (mem_invs.2 (hP a haP)) b (mem_invs.2 (hP b hbP)) (hc a haP b hbP) hff
  intro g hg
  rcases hOK g ((hab g).1 hg) with h | h | ⟨s, hs, t, ht, hsw, htw, rfl⟩
  · rw [h]; exact one_mem _
  · exact Subgroup.subset_closure ⟨hg, (isSw_iff g).1 h⟩
  · exact mul_mem (Subgroup.subset_closure ⟨(hab s).2 hs, (isSw_iff s).1 hsw⟩)
      (Subgroup.subset_closure ⟨(hab t).2 ht, (isSw_iff t).1 htw⟩)

theorem ff_pair_le : ∀ a ∈ invs, ∀ b ∈ invs, a * b = b * a →
    (four a b).card * (fixOf a b).card ≤ 16 := by
  decide +kernel

theorem card_mul_fix_le (P : Subgroup (Perm (Fin 5))) (hP : ∀ a ∈ P, a * a = 1)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Nat.card P * Nat.card (FixΔ P) ≤ 16 := by
  obtain ⟨a, haP, b, hbP, -, hcardP, hfix⟩ := exists_four_card P hP hc
  rw [hcardP, hfix]
  exact ff_pair_le a (mem_invs.2 (hP a haP)) b (mem_invs.2 (hP b hbP)) (hc a haP b hbP)

theorem swap_comm_disjoint : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → swap a b ≠ swap c d →
    swap a b * swap c d = swap c d * swap a b → (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) := by
  decide +kernel

theorem swap_noncomm : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b * swap c d ≠ swap c d * swap a b →
    (swap a b * swap c d) ^ 3 = 1 ∧ swap a b * swap c d ≠ 1 := by
  decide +kernel

theorem no_three_disjoint : ∀ a b c d x y : Fin 5, a ≠ b → c ≠ d → x ≠ y →
    (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) → (x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b) →
    (x ≠ c ∧ x ≠ d ∧ y ≠ c ∧ y ≠ d) → False := by
  decide +kernel

theorem card_centralizer_swap : ∀ a b : Fin 5, a ≠ b →
    (Finset.univ.filter fun g : Perm (Fin 5) => g * swap a b = swap a b * g).card = 12 := by
  decide +kernel

@[expose] def e2 (a b : Fin 5) : Fin 5 → ZMod 2 := Pi.single a 1 + Pi.single b 1

theorem isEven_e2 : ∀ a b : Fin 5, a ≠ b → isEven (e2 a b) := by decide +kernel

theorem swap_fix_e2 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) →
    pact (swap a b) (e2 a b) = e2 a b ∧ pact (swap c d) (e2 a b) = e2 a b := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fix_pair : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) →
    ∀ g : Perm (Fin 5), pact g (e2 a b) = e2 a b → pact g (e2 c d) = e2 c d →
      g = 1 ∨ g = swap a b ∨ g = swap c d ∨ g = swap a b * swap c d := by
  decide +kernel

theorem disjoint_swap_of (a b c d : Fin 5) (h : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    (swap a b).Disjoint (swap c d) := by
  intro x
  by_cases hx : x = a ∨ x = b
  · right
    rcases hx with rfl | rfl
    · exact swap_apply_of_ne_of_ne h.1 h.2.1
    · exact swap_apply_of_ne_of_ne h.2.2.1 h.2.2.2
  · left
    push Not at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem card_centralizer_swap' {t : Perm (Fin 5)} (ht : t.IsSwap) :
    Nat.card (Subgroup.centralizer ({t} : Set (Perm (Fin 5)))) = 12 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := ht
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_centralizer_swap a b hab]
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem conj_isSwap (d s : Perm (Fin 5)) (hs : s.IsSwap) : (d * s * d⁻¹).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  exact ⟨d a, d b, d.injective.ne hab, (swap_apply_apply d a b).symm⟩

theorem exists_swap_of_swapGen (J : Subgroup (Perm (Fin 5))) (hJ1 : ∃ j ∈ J, j ≠ 1)
    (hJs : ∀ g ∈ J, g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ J ∧ s.IsSwap}) :
    ∃ t ∈ J, t.IsSwap := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj, hj1⟩ := hJ1
  have hset : {s : Perm (Fin 5) | s ∈ J ∧ s.IsSwap} = ∅ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hcon s h.1 h.2
  have := hJs j hj
  rw [hset, Subgroup.closure_empty, Subgroup.mem_bot] at this
  exact hj1 this

theorem swap_core (D J : Subgroup (Perm (Fin 5))) (hD : Nat.card D = 8) (hJD : J ≤ D)
    (hJn : ∀ d ∈ D, ∀ j ∈ J, d * j * d⁻¹ ∈ J) (hJ1 : ∃ j ∈ J, j ≠ 1)
    (hJs : ∀ g ∈ J, g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ J ∧ s.IsSwap}) :
    ∃ τ₁ τ₂ : Perm (Fin 5), τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
      J = Subgroup.closure {τ₁, τ₂} ∧ (∃ d ∈ D, d * τ₁ * d⁻¹ = τ₂) ∧
      ∀ g : Perm (Fin 5), (∀ w ∈ FixΔ J, vact g w = w) → g ∈ J := by
  classical
  have hex : ∃ t ∈ J, t.IsSwap := exists_swap_of_swapGen J hJ1 hJs
  obtain ⟨t, htJ, htsw⟩ := hex
  have hcomm : ∀ s ∈ D, s.IsSwap → ∀ u ∈ D, u.IsSwap → s ≠ u → s * u = u * s := by
    intro s hs hsw u hu huw hne
    by_contra hnc
    obtain ⟨a, b, hab, rfl⟩ := hsw
    obtain ⟨c, d, hcd, rfl⟩ := huw
    obtain ⟨h3, h1⟩ := swap_noncomm a b c d hab hcd hnc
    have hmem : swap a b * swap c d ∈ D := mul_mem hs hu
    have hord : orderOf (swap a b * swap c d) = 3 := by
      have hdvd : orderOf (swap a b * swap c d) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) h1
      · exact h
    have h8 : orderOf (⟨swap a b * swap c d, hmem⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord, hD] at h8
    omega
  have hnc : ∀ t₀ ∈ J, t₀.IsSwap → ∃ d ∈ D, d * t₀ * d⁻¹ ≠ t₀ := by
    intro t₀ ht₀J ht₀sw
    by_contra hcon
    push Not at hcon
    have hDC : D ≤ Subgroup.centralizer ({t₀} : Set (Perm (Fin 5))) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h2 := hcon d hd
      calc h * d = (d * h * d⁻¹) * d := by rw [h2]
        _ = d * h := by group
    have hdvd := Subgroup.card_dvd_of_le hDC
    rw [hD, card_centralizer_swap' ht₀sw] at hdvd
    omega
  have hsecond : ∃ t' ∈ J, t'.IsSwap ∧ t' ≠ t := by
    obtain ⟨d, hd, hdne⟩ := hnc t htJ htsw
    exact ⟨d * t * d⁻¹, hJn d hd t htJ, conj_isSwap d t htsw, hdne⟩
  obtain ⟨t', ht'J, ht'sw, hne⟩ := hsecond
  have hcm := hcomm t (hJD htJ) htsw t' (hJD ht'J) ht'sw hne.symm
  obtain ⟨a, b, hab, rfl⟩ := htsw
  obtain ⟨c, d, hcd, rfl⟩ := ht'sw
  have hdis := swap_comm_disjoint a b c d hab hcd hne.symm hcm
  have hall : ∀ u ∈ J, u.IsSwap → u = swap a b ∨ u = swap c d := by
    intro u hu hsw
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    obtain ⟨x, y, hxy, rfl⟩ := hsw
    have hc1 := hcomm _ (hJD hu) ⟨x, y, hxy, rfl⟩ _ (hJD htJ) ⟨a, b, hab, rfl⟩ hn1
    have hc2 := hcomm _ (hJD hu) ⟨x, y, hxy, rfl⟩ _ (hJD ht'J) ⟨c, d, hcd, rfl⟩ hn2
    have d1 := swap_comm_disjoint x y a b hxy hab hn1 hc1
    have d2 := swap_comm_disjoint x y c d hxy hcd hn2 hc2
    exact no_three_disjoint a b c d x y hab hcd hxy hdis d1 d2
  have hJeq : J = Subgroup.closure {swap a b, swap c d} := by
    apply le_antisymm
    · intro g hg
      refine Subgroup.closure_mono ?_ (hJs g hg)
      rintro s ⟨hsJ, hssw⟩
      rcases hall s hsJ hssw with rfl | rfl <;> simp
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact htJ
      · exact ht'J
  refine ⟨swap a b, swap c d, ⟨a, b, hab, rfl⟩, ⟨c, d, hcd, rfl⟩, disjoint_swap_of a b c d hdis,
    hJeq, ?_, ?_⟩
  · obtain ⟨d', hd', hne'⟩ := hnc (swap a b) htJ ⟨a, b, hab, rfl⟩
    refine ⟨d', hd', ?_⟩
    rcases hall _ (hJn d' hd' _ htJ) (conj_isSwap d' _ ⟨a, b, hab, rfl⟩) with h | h
    · exact absurd h hne'
    · exact h
  intro g hg
  have hfix : ∀ (x y z w : Fin 5) (hxy : x ≠ y),
      (pact (swap x y) (e2 x y) = e2 x y ∧ pact (swap z w) (e2 x y) = e2 x y) →
      (⟨e2 x y, isEven_e2 x y hxy⟩ : evenWeight 5) ∈ FixΔ (Subgroup.closure {swap x y, swap z w}) := by
    intro x y z w hxy ⟨h1, h2⟩ σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | rfl
      · exact Subtype.ext h1
      · exact Subtype.ext h2
    | one => exact vact_one _
    | mul s s' _ _ hs hs' => rw [vact_mul, hs', hs]
    | inv s _ hs =>
      have := congrArg (vact s⁻¹) hs
      rw [← vact_mul, inv_mul_cancel, vact_one] at this
      exact this.symm
  have hdis' : c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b :=
    ⟨hdis.1.symm, hdis.2.2.1.symm, hdis.2.1.symm, hdis.2.2.2.symm⟩
  have hv1 := hfix a b c d hab (swap_fix_e2 a b c d hab hcd hdis)
  have hv2 := hfix c d a b hcd (swap_fix_e2 c d a b hcd hab hdis')
  rw [← hJeq] at hv1
  rw [Set.pair_comm, ← hJeq] at hv2
  have h1 := hg _ hv1
  have h2 := hg _ hv2
  rcases fix_pair a b c d hab hcd hdis g (congrArg Subtype.val h1) (congrArg Subtype.val h2) with
    rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact htJ
  · exact ht'J
  · exact mul_mem htJ ht'J

end CFSG.QuasithinUnique.AppC
