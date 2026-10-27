module

public import CFSG.LieType.Chevalley.TwistUnipotent
public import CFSG.LieType.Chevalley.TorusCentralizer
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank

variable {τ : Tag}

@[expose] def pairFree (τ : Tag) (α β : Fin τ.rank → ℤ) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    (List.range 7).all fun a => (List.range 7).all fun b =>
      !(decide (1 ≤ a) && decide (1 ≤ b) &&
        decide (τ.rootCertificate.root k = a • α + b • β))

@[expose] def coeffBound (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    (List.finRange τ.rank).all fun i => decide (τ.rootCertificate.root k i ≤ 6)

theorem coeffBound_eq_true : ∀ τ : Tag, coeffBound τ = true := by
  intro τ
  cases τ <;> decide +kernel

theorem not_isRoot_of_pairFree {α β : Fin τ.rank → ℤ} (hα : ∀ i, 0 ≤ α i) (hα0 : α ≠ 0)
    (hβ : ∀ i, 0 ≤ β i) (hβ0 : β ≠ 0) (hpf : pairFree τ α β = true) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ¬ IsRoot τ (a • α + b • β) := by
  intro h
  obtain ⟨k, hk, hkv⟩ := (RootCertificate.isRoot_iff τ.rootCertificate_check).1 h
  have hbound : ∀ i, (a • α + b • β) i ≤ 6 := by
    intro i
    have := coeffBound_eq_true τ
    simp only [coeffBound, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
      decide_eq_true_eq] at this
    rw [← hkv]
    exact this k hk i
  have hlarge : ∀ (γ δ : Fin τ.rank → ℤ) (c d : ℕ), (∀ i, 0 ≤ γ i) → γ ≠ 0 → (∀ i, 0 ≤ δ i) →
      (∀ i, (c • γ + d • δ) i ≤ 6) → c ≤ 6 := by
    intro γ δ c d hγ hγ0 hδ hcd
    obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hγ0 (funext hcon)
    have h1 := hcd i
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul] at h1
    have h2 : 1 ≤ γ i := by have := hγ i; omega
    have h3 : 0 ≤ (d : ℤ) * δ i := mul_nonneg (by positivity) (hδ i)
    have h4 : (c : ℤ) ≤ c * γ i := by nlinarith
    omega
  have ha6 := hlarge α β a b hα hα0 hβ hbound
  have hb6 := hlarge β α b a hβ hβ0 hα (fun i => by rw [add_comm]; exact hbound i)
  simp only [pairFree, List.all_eq_true, List.mem_range] at hpf
  have := hpf k hk a (by omega) b (by omega)
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
  rcases this with (h1 | h1) | h1
  · exact h1 ha
  · exact h1 hb
  · exact h1 hkv

variable {K : Type} [Field K]

@[expose] noncomputable def rootHom (α : Root τ) : Multiplicative K →* adjointGroup τ K where
  toFun c := (rootOperatorFamily τ).eltElement α (Multiplicative.toAdd c)
  map_one' := (rootOperatorFamily τ).eltElement_zero α
  map_mul' _ _ := (rootOperatorFamily τ).eltElement_add α _ _

theorem rootHom_injective (α : Root τ) : Function.Injective (rootHom (K := K) α) :=
  fun _ _ h => Multiplicative.toAdd.injective (eltElement_injective α h)

theorem commute_rootHom_of_not_isRoot {α β : Root τ} (hα : 0 < height α.1)
    (hβ : 0 < height β.1) (hne : α ≠ β)
    (hfree : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • α.1 + b • β.1))
    (c d : Multiplicative K) : Commute (rootHom α c) (rootHom β d) := by
  have h := commContained_pos K α β hα hβ hne _
    ((rootOperatorFamily τ).eltElement_mem_rootSubgroup α (Multiplicative.toAdd c)) _
    ((rootOperatorFamily τ).eltElement_mem_rootSubgroup β (Multiplicative.toAdd d))
  have hbot : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
      (rootOperatorFamily τ).rootSubgroup K γ) = ⊥ :=
    iSup₂_eq_bot.2 fun γ ⟨a, b, ha, hb, hγ⟩ => absurd (hγ ▸ γ.2) (hfree a b ha hb)
  rw [hbot, Subgroup.mem_bot] at h
  change rootHom α c * rootHom β d = rootHom β d * rootHom α c
  change (rootOperatorFamily τ).eltElement α (Multiplicative.toAdd c) *
      (rootOperatorFamily τ).eltElement β (Multiplicative.toAdd d) =
    (rootOperatorFamily τ).eltElement β (Multiplicative.toAdd d) *
      (rootOperatorFamily τ).eltElement α (Multiplicative.toAdd c)
  calc _ = (rootOperatorFamily τ).eltElement α (Multiplicative.toAdd c) *
        (rootOperatorFamily τ).eltElement β (Multiplicative.toAdd d) *
        ((rootOperatorFamily τ).eltElement α (Multiplicative.toAdd c))⁻¹ *
        ((rootOperatorFamily τ).eltElement β (Multiplicative.toAdd d))⁻¹ *
        ((rootOperatorFamily τ).eltElement β (Multiplicative.toAdd d) *
          (rootOperatorFamily τ).eltElement α (Multiplicative.toAdd c)) := by group
    _ = _ := by rw [h, one_mul]

@[expose] def pairCheck (τ : Tag) (α β : Fin τ.rank → ℤ) : Bool :=
  decide (0 < height α) && decide (0 < height β) && decide (List.ofFn α ≠ List.ofFn β) &&
    (List.finRange τ.rank).all (fun i => decide (0 ≤ α i)) &&
    (List.finRange τ.rank).all (fun i => decide (0 ≤ β i)) && pairFree τ α β

theorem commute_rootHom_of_pairCheck {α β : Root τ} (h : pairCheck τ α.1 β.1 = true)
    (c d : Multiplicative K) : Commute (rootHom α c) (rootHom β d) := by
  simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨⟨hα, hβ⟩, hne⟩, hαn⟩, hβn⟩, hpf⟩ := h
  have hα0 : α.1 ≠ 0 := fun h0 => by rw [h0] at hα; simp [height] at hα
  have hβ0 : β.1 ≠ 0 := fun h0 => by rw [h0] at hβ; simp [height] at hβ
  exact commute_rootHom_of_not_isRoot hα hβ (fun h' => hne (by rw [h']))
    (fun a b ha hb => not_isRoot_of_pairFree hαn hα0 hβn hβ0 hpf ha hb) c d

theorem commute_of_mem_X_of_pairCheck {α β : Root τ} (h : pairCheck τ α.1 β.1 = true)
    {x y : adjointGroup τ K} (hx : x ∈ (rootOperatorFamily τ).rootSubgroup K α)
    (hy : y ∈ (rootOperatorFamily τ).rootSubgroup K β) : Commute x y := by
  obtain ⟨c, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hy
  exact commute_rootHom_of_pairCheck h (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)

variable [Finite K]

theorem injective_rootPi {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → Root τ)
    (hpos : ∀ i, 0 < height (α i).1)
    (hcomm : Pairwise fun i j => ∀ x y : Multiplicative K,
      Commute (rootHom (α i) x) (rootHom (α j) y))
    (w : ι → WeylGroup τ) (hneg : ∀ i, height ((w i) • (α i).1) < 0)
    (hsep : ∀ i j, i ≠ j → 0 < height ((w i) • (α j).1)) :
    Function.Injective (MonoidHom.noncommPiCoprod (fun i => rootHom (K := K) (α i)) hcomm) := by
  refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep _ (fun i => ?_)
    (fun i => rootHom_injective _)
  rw [disjoint_iff, eq_bot_iff]
  have h1 : (rootHom (K := K) (α i)).range ≤ Uminus τ K (w i) := by
    rintro _ ⟨c, rfl⟩
    exact mem_Uminus_of_mem_X (hpos i) (hneg i)
      ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)
  have h2 : (⨆ (j : ι) (_ : j ≠ i), (rootHom (K := K) (α j)).range) ≤ Uplus τ K (w i) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨c, rfl⟩
    exact mem_Uplus_of_mem_X (hpos j) (hsep i j (Ne.symm hj))
      ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)
  calc _ ≤ Uminus τ K (w i) ⊓ Uplus τ K (w i) := inf_le_inf h1 h2
    _ = ⊥ := by rw [inf_comm, Uplus_inf_Uminus]

theorem iSupIndep_X_of_separated {ι : Type*} (α : ι → Root τ)
    (hpos : ∀ i, 0 < height (α i).1) (w : ι → WeylGroup τ)
    (hneg : ∀ i, height ((w i) • (α i).1) < 0)
    (hsep : ∀ i j, i ≠ j → 0 < height ((w i) • (α j).1)) :
    iSupIndep fun i => (nativeRootSubgroups τ K).X (α i) := by
  intro i
  rw [disjoint_iff, eq_bot_iff]
  have h1 : (nativeRootSubgroups τ K).X (α i) ≤ Uminus τ K (w i) := fun x hx =>
    mem_Uminus_of_mem_X (hpos i) (hneg i) hx
  have h2 : (⨆ (j : ι) (_ : j ≠ i), (nativeRootSubgroups τ K).X (α j)) ≤ Uplus τ K (w i) :=
    iSup₂_le fun j hj x hx => mem_Uplus_of_mem_X (hpos j) (hsep i j (Ne.symm hj)) hx
  calc _ ≤ Uminus τ K (w i) ⊓ Uplus τ K (w i) := inf_le_inf h1 h2
    _ = ⊥ := by rw [inf_comm, Uplus_inf_Uminus]

theorem le_pRank_of_rootPi {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → Root τ)
    (hpos : ∀ i, 0 < height (α i).1)
    (hcomm : Pairwise fun i j => ∀ x y : Multiplicative K,
      Commute (rootHom (α i) x) (rootHom (α j) y))
    (w : ι → WeylGroup τ) (hneg : ∀ i, height ((w i) • (α i).1) < 0)
    (hsep : ∀ i j, i ≠ j → 0 < height ((w i) • (α j).1)) {p f : ℕ} [hp : Fact p.Prime]
    [CharP K p] (hK : Nat.card K = p ^ f) :
    Fintype.card ι * f ≤ pRank p (⊤ : Subgroup (adjointGroup τ K)) := by
  refine le_pRank_of_injective hp.out.one_lt (fun a b => mul_comm a b) (fun a => ?_) ?_ _
    (injective_rootPi α hpos hcomm w hneg hsep) le_top
  · funext i
    change Multiplicative.ofAdd (p • Multiplicative.toAdd (a i)) = 1
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rfl
  · rw [Nat.card_pi, Finset.prod_const, Finset.card_univ,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK,
      ← pow_mul, mul_comm]

end CFSG.LieType.Chevalley
