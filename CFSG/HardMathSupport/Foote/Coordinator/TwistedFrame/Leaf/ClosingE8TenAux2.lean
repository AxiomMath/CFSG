module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux1
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false

variable {L : Type} [Field L]


structure InvE (U : Submodule L (Fn L)) : Prop where
  supp : ∀ u ∈ U, ∀ ν, ν ∉ deg1Roots → u ν = 0
  E : ∀ γ ∈ gens12, ∀ u ∈ U, Eop aE8 γ u ∈ U

theorem Eop_Eop_neg (γ : Fin Tag.E8.rank → ℤ) (u : Fn L) (ν : Fin Tag.E8.rank → ℤ) :
    Eop aE8 γ (Eop aE8 (-γ) u) ν = ((aE8 γ (ν - γ) * aE8 (-γ) ν : ℤ) : L) * u ν := by
  rw [Eop_apply, Eop_apply, show ν - γ - -γ = ν by abel]
  push_cast
  ring

theorem coef_plus {γ ν : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8) (hγ0 : γ 7 = 0)
    (hν : ν ∈ deg1Roots) :
    (ν - γ ∈ rootFinset Tag.E8 → (aE8 γ (ν - γ) * aE8 (-γ) ν) ^ 2 = 1) ∧
      (ν - γ ∉ rootFinset Tag.E8 → aE8 γ (ν - γ) * aE8 (-γ) ν = 0) := by
  have hnγ : -γ ∈ rootFinset Tag.E8 := by
    rw [mem_rootFinset] at hγ ⊢
    exact IsRoot.neg hγ
  have hnγ0 : (-γ) 7 = 0 := by rw [Pi.neg_apply, hγ0, neg_zero]
  obtain ⟨h1, h2⟩ := adm_aE8 (-γ) hnγ hnγ0 ν hν
  constructor
  · intro h
    have hsum : -γ + ν ∈ rootFinset Tag.E8 := by rwa [neg_add_eq_sub]
    have hνγ : ν - γ ∈ deg1Roots := by
      rw [mem_deg1Roots]
      refine ⟨mem_rootFinset.1 h, ?_⟩
      have h7 := (mem_deg1Roots.1 hν).2
      show (ν - γ) 7 = 1
      rw [Pi.sub_apply, h7, hγ0, sub_zero]
    have h3 := (adm_aE8 γ hγ hγ0 (ν - γ) hνγ).1
      (by rw [add_sub_cancel]; exact mem_rootFinset.2 (mem_deg1Roots.1 hν).1)
    have h4 := h1 hsum
    have e3 : aE8 γ (ν - γ) ^ 2 = 1 := by
      rcases (abs_eq (zero_le_one)).1 h3 with h | h <;> simp [h]
    have e4 : aE8 (-γ) ν ^ 2 = 1 := by
      rcases (abs_eq (zero_le_one)).1 h4 with h | h <;> simp [h]
    rw [mul_pow, e3, e4, one_mul]
  · intro h
    have hsum : -γ + ν ∉ rootFinset Tag.E8 := by rwa [neg_add_eq_sub]
    rw [h2 hsum, mul_zero]

theorem Eop4_apply {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8) (hγ0 : γ 7 = 0)
    (u : Fn L) (hu : ∀ ν, ν ∉ deg1Roots → u ν = 0) (ν : Fin Tag.E8.rank → ℤ) :
    Eop aE8 γ (Eop aE8 (-γ) (Eop aE8 γ (Eop aE8 (-γ) u))) ν =
      if ν - γ ∈ rootFinset Tag.E8 then u ν else 0 := by
  rw [Eop_Eop_neg, Eop_Eop_neg]
  by_cases hν : ν ∈ deg1Roots
  · obtain ⟨h1, h2⟩ := coef_plus hγ hγ0 hν
    by_cases h : ν - γ ∈ rootFinset Tag.E8
    · rw [if_pos h]
      have e : (((aE8 γ (ν - γ) * aE8 (-γ) ν : ℤ) : L)) ^ 2 = 1 := by
        rw [← Int.cast_pow, h1 h, Int.cast_one]
      calc (((aE8 γ (ν - γ) * aE8 (-γ) ν : ℤ) : L)) *
            ((((aE8 γ (ν - γ) * aE8 (-γ) ν : ℤ) : L)) * u ν)
          = (((aE8 γ (ν - γ) * aE8 (-γ) ν : ℤ) : L)) ^ 2 * u ν := by ring
        _ = u ν := by rw [e, one_mul]
    · rw [if_neg h, h2 h]
      simp
  · rw [hu ν hν]
    simp

@[expose] def ind (γ : Fin Tag.E8.rank → ℤ) (s : ℤ) (u : Fn L) : Fn L :=
  fun ν => if typ γ ν = s then u ν else 0

theorem typ_eq_one {γ ν : Fin Tag.E8.rank → ℤ} (hν : ν ∈ deg1Roots) (hγ : γ ∈ simp6) :
    typ γ ν = 1 ↔ ν - γ ∈ rootFinset Tag.E8 := by
  have hx := typ_excl ν hν γ hγ
  unfold typ
  by_cases h1 : ν - γ ∈ rootFinset Tag.E8 <;> by_cases h2 : ν + γ ∈ rootFinset Tag.E8 <;>
    simp [h1, h2] at hx ⊢

theorem typ_eq_neg_one {γ ν : Fin Tag.E8.rank → ℤ} (hν : ν ∈ deg1Roots) (hγ : γ ∈ simp6) :
    typ γ ν = -1 ↔ ν + γ ∈ rootFinset Tag.E8 := by
  have hx := typ_excl ν hν γ hγ
  unfold typ
  by_cases h1 : ν - γ ∈ rootFinset Tag.E8 <;> by_cases h2 : ν + γ ∈ rootFinset Tag.E8 <;>
    simp [h1, h2] at hx ⊢

theorem typ_cases {γ ν : Fin Tag.E8.rank → ℤ} (hν : ν ∈ deg1Roots) (hγ : γ ∈ simp6) :
    typ γ ν = 1 ∨ typ γ ν = -1 ∨ typ γ ν = 0 := by
  have hx := typ_excl ν hν γ hγ
  unfold typ
  by_cases h1 : ν - γ ∈ rootFinset Tag.E8 <;> by_cases h2 : ν + γ ∈ rootFinset Tag.E8 <;>
    simp [h1, h2] at hx ⊢

theorem neg_mem_simp {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ simp6) :
    γ ∈ gens12 ∧ -γ ∈ gens12 ∧ γ ∈ rootFinset Tag.E8 ∧ γ 7 = 0 ∧
      -γ ∈ rootFinset Tag.E8 ∧ (-γ) 7 = 0 := by
  obtain ⟨h1, h2⟩ := simp6_sub γ hγ
  obtain ⟨a1, a2, -⟩ := gens12_data γ h1
  obtain ⟨b1, b2, -⟩ := gens12_data (-γ) h2
  exact ⟨h1, h2, a1, a2, b1, b2⟩

variable {U : Submodule L (Fn L)}

theorem ind_mem (hU : InvE U) {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ simp6) {s : ℤ}
    (hs : s = 1 ∨ s = -1 ∨ s = 0) {u : Fn L} (hu : u ∈ U) : ind γ s u ∈ U := by
  obtain ⟨g1, g2, r1, d1, r2, d2⟩ := neg_mem_simp hγ
  have hsupp := hU.supp u hu
  have hp : Eop aE8 γ (Eop aE8 (-γ) (Eop aE8 γ (Eop aE8 (-γ) u))) ∈ U :=
    hU.E γ g1 _ (hU.E (-γ) g2 _ (hU.E γ g1 _ (hU.E (-γ) g2 _ hu)))
  have hm : Eop aE8 (-γ) (Eop aE8 γ (Eop aE8 (-γ) (Eop aE8 γ u))) ∈ U :=
    hU.E (-γ) g2 _ (hU.E γ g1 _ (hU.E (-γ) g2 _ (hU.E γ g1 _ hu)))
  have ep : ind γ 1 u = Eop aE8 γ (Eop aE8 (-γ) (Eop aE8 γ (Eop aE8 (-γ) u))) := by
    funext ν
    rw [Eop4_apply r1 d1 u hsupp ν, ind]
    by_cases hν : ν ∈ deg1Roots
    · simp only [typ_eq_one hν hγ]
    · simp [hsupp ν hν]
  have em : ind γ (-1) u = Eop aE8 (-γ) (Eop aE8 γ (Eop aE8 (-γ) (Eop aE8 γ u))) := by
    have := Eop4_apply (L := L) r2 d2 u hsupp
    rw [neg_neg] at this
    funext ν
    rw [this ν, ind]
    by_cases hν : ν ∈ deg1Roots
    · have : ν - -γ = ν + γ := by abel
      simp only [typ_eq_neg_one hν hγ, this]
    · simp [hsupp ν hν]
  rcases hs with rfl | rfl | rfl
  · rw [ep]; exact hp
  · rw [em]; exact hm
  · have e0 : ind γ 0 u = u - ind γ 1 u - ind γ (-1) u := by
      funext ν
      simp only [ind, Pi.sub_apply]
      by_cases hν : ν ∈ deg1Roots
      · rcases typ_cases hν hγ with h | h | h <;> simp [h]
      · simp [hsupp ν hν]
    rw [e0]
    exact U.sub_mem (U.sub_mem hu (by rw [ep]; exact hp)) (by rw [em]; exact hm)

theorem single_mem_of_coord_ne (hU : InvE U) {u : Fn L} (hu : u ∈ U)
    {μ₀ : Fin Tag.E8.rank → ℤ} (hμ₀ : μ₀ ∈ deg1Roots) (h0 : u μ₀ ≠ 0) :
    (Pi.single μ₀ (1 : L) : Fn L) ∈ U := by
  classical
  suffices H : ∀ n : ℕ, ∀ u ∈ U, u μ₀ ≠ 0 →
      (deg1Roots.filter fun ν => u ν ≠ 0).card = n → (Pi.single μ₀ (1 : L) : Fn L) ∈ U from
    H _ u hu h0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hu h0 hn
    by_cases hall : ∀ ν ∈ deg1Roots, ν ≠ μ₀ → u ν = 0
    · have hu' : u = Pi.single μ₀ (u μ₀) := by
        funext ν
        by_cases hν : ν ∈ deg1Roots
        · by_cases he : ν = μ₀
          · subst he; simp
          · rw [Pi.single_eq_of_ne he, hall ν hν he]
        · rw [hU.supp u hu ν hν, Pi.single_eq_of_ne]
          rintro rfl
          exact hν hμ₀
      have : (Pi.single μ₀ (1 : L) : Fn L) = (u μ₀)⁻¹ • u := by
        funext ν
        rw [hu']
        by_cases he : ν = μ₀
        · subst he; simp [h0]
        · simp [Pi.single_eq_of_ne he]
      rw [this]
      exact U.smul_mem _ hu
    · push Not at hall
      obtain ⟨ν, hν, hne, hνu⟩ := hall
      obtain ⟨γ, hγ, hty⟩ : ∃ γ ∈ simp6, typ γ ν ≠ typ γ μ₀ := by
        by_contra hcon
        push Not at hcon
        have : typVec ν = typVec μ₀ := List.map_congr_left hcon
        exact hne (Multiset.inj_on_of_nodup_map typVec_nodup ν hν μ₀ hμ₀ this)
      have hcases := typ_cases hμ₀ hγ
      set u' := ind γ (typ γ μ₀) u with hu'
      have hu'U : u' ∈ U := ind_mem hU hγ (by rcases hcases with h | h | h <;> simp [h]) hu
      have hu'μ : u' μ₀ ≠ 0 := by simpa [hu', ind] using h0
      have hsub : (deg1Roots.filter fun x => u' x ≠ 0) ⊂ (deg1Roots.filter fun x => u x ≠ 0) := by
        refine (Finset.ssubset_iff_of_subset ?_).2 ⟨ν, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_filter, hu', ind] at hx ⊢
          refine ⟨hx.1, ?_⟩
          by_cases h : typ γ x = typ γ μ₀
          · simpa [h] using hx.2
          · simp [h] at hx
        · simp [hν, hνu]
        · simp [hu', ind, hty]
      exact ih _ (by rw [← hn]; exact Finset.card_lt_card hsub) u' hu'U hu'μ rfl

theorem single_move (hU : InvE U) {γ μ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ gens12)
    (hμ : μ ∈ deg1Roots) (hs : μ + γ ∈ rootFinset Tag.E8)
    (h : (Pi.single μ (1 : L) : Fn L) ∈ U) : (Pi.single (μ + γ) (1 : L) : Fn L) ∈ U := by
  obtain ⟨hγr, hγ0, -⟩ := gens12_data γ hγ
  have hE := hU.E γ hγ _ h
  rw [Eop_single] at hE
  have habs := ((adm_aE8 γ hγr hγ0 μ hμ).1 (by rwa [add_comm]))
  have hne : (aE8 γ μ : L) ≠ 0 := by
    rcases (abs_eq zero_le_one).1 habs with h' | h' <;> simp [h']
  have : (Pi.single (μ + γ) (1 : L) : Fn L) =
      (aE8 γ μ : L)⁻¹ • (Pi.single (μ + γ) ((aE8 γ μ : L) * 1) : Fn L) := by
    funext ν
    by_cases he : ν = μ + γ
    · subst he; simp [inv_mul_cancel₀ hne]
    · simp [Pi.single_eq_of_ne he]
  rw [this]
  exact U.smul_mem _ hE

theorem single_mem_of_cls (hU : InvE U) {μ ν : Fin Tag.E8.rank → ℤ} (hμ : μ ∈ mRoots)
    (hν : ν ∈ mRoots) (hc : cls μ = cls ν) (h : (Pi.single μ (1 : L) : Fn L) ∈ U) :
    (Pi.single ν (1 : L) : Fn L) ∈ U := by
  have hd : ∀ x ∈ mRoots, x ∈ deg1Roots := fun x hx => by
    rw [mem_deg1Roots]
    obtain ⟨a, b, -⟩ := mem_mRoots.1 hx
    exact ⟨a, b⟩
  have hstep : ∀ x ∈ mRoots, (Pi.single x (1 : L) : Fn L) ∈ U ↔
      (Pi.single (descendStep x) (1 : L) : Fn L) ∈ U := by
    intro x hx
    rcases descendStep_spec x hx with h1 | ⟨γ, hγ, hxγ, h2⟩
    · rw [h1]
    · rw [h2]
      obtain ⟨g1, g2, -⟩ := neg_mem_simp hγ
      have hxγ' : x - γ ∈ deg1Roots := hd _ hxγ
      constructor
      · intro hx'
        have := single_move hU g2 (hd x hx) (by rw [← sub_eq_add_neg]; exact mem_mRoots.1 hxγ |>.1 |> mem_rootFinset.2) hx'
        rwa [← sub_eq_add_neg] at this
      · intro hx'
        have := single_move hU g1 hxγ' (by rw [sub_add_cancel]; exact mem_rootFinset.2 (mem_mRoots.1 hx).1) hx'
        rwa [sub_add_cancel] at this
  have hmem : ∀ n, ∀ x ∈ mRoots, descendStep^[n] x ∈ mRoots := by
    intro n
    induction n with
    | zero => intro x hx; exact hx
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply]
      refine ih _ ?_
      rcases descendStep_spec x hx with h1 | ⟨γ, hγ, hxγ, h2⟩
      · rw [h1]; exact hx
      · rw [h2]; exact hxγ
  have hiter : ∀ n, ∀ x ∈ mRoots, (Pi.single x (1 : L) : Fn L) ∈ U ↔
      (Pi.single (descendStep^[n] x) (1 : L) : Fn L) ∈ U := by
    intro n
    induction n with
    | zero => intro x hx; exact Iff.rfl
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply, hstep x hx]
      exact ih _ (by
        rcases descendStep_spec x hx with h1 | ⟨γ, hγ, hxγ, h2⟩
        · rw [h1]; exact hx
        · rw [h2]; exact hxγ)
  have hlow : ∀ x ∈ mRoots, (Pi.single x (1 : L) : Fn L) ∈ U ↔
      (Pi.single (lowRep (cls x)) (1 : L) : Fn L) ∈ U := by
    intro x hx
    rw [hiter 10 x hx]
    have := lowOf_eq x hx
    unfold lowOf at this
    rw [this]
  rw [hlow ν hν, ← hc, ← hlow μ hμ]
  exact h

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
