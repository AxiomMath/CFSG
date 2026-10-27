module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Norm

public section

namespace GL83.CompFam

variable {p : ℕ} [Fact p.Prime] {S : Type*} [Group S] [DecidableEq S]

def supp (x : ZMod p → S) : Finset (ZMod p) := Finset.univ.filter fun j => x j ≠ 1

theorem mem_supp {x : ZMod p → S} {j : ZMod p} : j ∈ supp x ↔ x j ≠ 1 := by
  simp [supp]

theorem supp_commutator_subset (u v : ZMod p → S) :
    supp (u * v * u⁻¹ * v⁻¹) ⊆ supp u ∩ supp v := by
  intro j hj
  rw [mem_supp] at hj
  rw [Finset.mem_inter, mem_supp, mem_supp]
  constructor
  · intro hu
    apply hj
    simp [hu]
  · intro hv
    apply hj
    simp [hv]

theorem exists_supp_subset (hS : IsSimpleGroup S) (X : Subgroup (ZMod p → S))
    (hproj : ∀ (j : ZMod p) (s : S), ∃ x ∈ X, x j = s) {T : Finset (ZMod p)}
    {y : ZMod p → S} (hyX : y ∈ X) (hyT : supp y ⊆ T) {j : ZMod p} (hy : y j ≠ 1) (s : S) :
    ∃ u ∈ X, supp u ⊆ T ∧ u j = s := by
  let N : Subgroup S :=
    { carrier := {s | ∃ u ∈ X, supp u ⊆ T ∧ u j = s}
      mul_mem' := by
        rintro _ _ ⟨u, hu, huT, rfl⟩ ⟨v, hv, hvT, rfl⟩
        refine ⟨u * v, X.mul_mem hu hv, ?_, rfl⟩
        intro i hi
        rw [mem_supp] at hi
        by_contra hiT
        apply hi
        have h1 : u i = 1 := by
          by_contra h; exact hiT (huT (mem_supp.2 h))
        have h2 : v i = 1 := by
          by_contra h; exact hiT (hvT (mem_supp.2 h))
        simp [h1, h2]
      one_mem' := ⟨1, X.one_mem, by intro i hi; simp [mem_supp] at hi, rfl⟩
      inv_mem' := by
        rintro _ ⟨u, hu, huT, rfl⟩
        refine ⟨u⁻¹, X.inv_mem hu, ?_, rfl⟩
        intro i hi
        rw [mem_supp] at hi
        apply huT
        rw [mem_supp]
        intro h
        apply hi
        simp [h] }
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨u, hu, huT, rfl⟩ := hn
    obtain ⟨x, hx, hxj⟩ := hproj j g
    refine ⟨x * u * x⁻¹, X.mul_mem (X.mul_mem hx hu) (X.inv_mem hx), ?_, by simp [hxj]⟩
    intro i hi
    rw [mem_supp] at hi
    apply huT
    rw [mem_supp]
    intro h
    apply hi
    simp [h]
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    have : y j ∈ N := ⟨y, hyX, hyT, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hy this
  · have : s ∈ N := by rw [h]; trivial
    exact this

theorem supp_eq_of_mem_inter (hS : IsSimpleGroup S) (hnab : ∃ s t : S, s * t ≠ t * s)
    (X : Subgroup (ZMod p → S)) (hproj : ∀ (j : ZMod p) (s : S), ∃ x ∈ X, x j = s) {m : ℕ}
    (hmin : ∀ x ∈ X, x ≠ 1 → m ≤ (supp x).card) {y₁ y₂ : ZMod p → S} (h₁ : y₁ ∈ X)
    (h₂ : y₂ ∈ X) (hm₁ : (supp y₁).card = m) (hm₂ : (supp y₂).card = m) {j : ZMod p}
    (hj₁ : j ∈ supp y₁) (hj₂ : j ∈ supp y₂) : supp y₁ = supp y₂ := by
  by_contra hne
  obtain ⟨s, t, hst⟩ := hnab
  obtain ⟨u, hu, huT, huj⟩ := exists_supp_subset hS X hproj h₁ (subset_rfl) (mem_supp.1 hj₁) s
  obtain ⟨v, hv, hvT, hvj⟩ := exists_supp_subset hS X hproj h₂ (subset_rfl) (mem_supp.1 hj₂) t
  set c := u * v * u⁻¹ * v⁻¹ with hc
  have hcX : c ∈ X := X.mul_mem (X.mul_mem (X.mul_mem hu hv) (X.inv_mem hu)) (X.inv_mem hv)
  have hsub : supp c ⊆ supp y₁ ∩ supp y₂ :=
    (supp_commutator_subset u v).trans (Finset.inter_subset_inter huT hvT)
  have hlt : (supp y₁ ∩ supp y₂).card < m := by
    rw [← hm₁]
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, ?_⟩)
    intro heq
    apply hne
    have hsub12 : supp y₁ ⊆ supp y₂ := by
      rw [← heq]; exact Finset.inter_subset_right
    exact Finset.eq_of_subset_of_card_le hsub12 (by rw [hm₁, hm₂])
  have hc1 : c = 1 := by
    by_contra hc1
    have := hmin c hcX hc1
    have := (Finset.card_le_card hsub).trans_lt hlt
    omega
  have hcomm : u * v = v * u := by
    have h := hc1
    rw [hc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  have := congrFun hcomm j
  simp only [Pi.mul_apply, huj, hvj] at this
  exact hst this

theorem pi_dichotomy [Finite S] (hS : IsSimpleGroup S) (hnab : ∃ s t : S, s * t ≠ t * s)
    (X : Subgroup (ZMod p → S)) (hproj : ∀ (j : ZMod p) (s : S), ∃ x ∈ X, x j = s)
    (hshift : ∀ x ∈ X, shiftHom (p := p) S x ∈ X) :
    X = ⊤ ∨ ∀ x ∈ X, ∀ j, x j = 1 → x = 1 := by
  classical
  by_cases hfull : ∀ x ∈ X, ∀ j, x j = 1 → x = 1
  · exact Or.inr hfull
  refine Or.inl ?_
  obtain ⟨x₀, hx₀X, j₀, hx₀j, hx₀1⟩ : ∃ x ∈ X, ∃ j, x j = 1 ∧ x ≠ 1 := by
    by_contra h
    apply hfull
    intro x hx j hxj
    by_contra hx1
    exact h ⟨x, hx, j, hxj, hx1⟩
  have hex : ∃ n, ∃ x ∈ X, x ≠ 1 ∧ (supp x).card = n := ⟨_, x₀, hx₀X, hx₀1, rfl⟩
  have hmin : ∀ x ∈ X, x ≠ 1 → Nat.find hex ≤ (supp x).card :=
    fun x hx hx1 => Nat.find_min' hex ⟨x, hx, hx1, rfl⟩
  obtain ⟨y, hyX, hy1, hym⟩ := Nat.find_spec hex
  have hTnonempty : ∃ t, t ∈ supp y := by
    by_contra h
    apply hy1
    funext i
    by_contra hi
    exact h ⟨i, mem_supp.2 hi⟩
  have hTne : supp y ≠ Finset.univ := by
    intro h
    have h1 := hmin x₀ hx₀X hx₀1
    have h2 : Nat.find hex = Fintype.card (ZMod p) := by rw [← hym, h, Finset.card_univ]
    have h3 : supp x₀ = Finset.univ :=
      Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (h2 ▸ h1))
    have h4 : j₀ ∈ supp x₀ := h3 ▸ Finset.mem_univ j₀
    exact (mem_supp.1 h4) hx₀j
  have htrans : ∀ n : ℕ, ∀ x ∈ X, (fun i : ZMod p => x (i - n)) ∈ X := by
    intro n
    induction n with
    | zero =>
      intro x hx
      have h0 : (fun i : ZMod p => x (i - ((0 : ℕ) : ZMod p))) = x := by
        funext i
        congr 1
        push_cast
        ring
      rw [h0]
      exact hx
    | succ n ih =>
      intro x hx
      have := hshift _ (ih x hx)
      convert this using 1
      funext i
      simp only [shiftHom_apply, Nat.cast_succ]
      congr 1
      ring
  have hT1 : (supp y).card = 1 := by
    by_contra hne
    have hpos : 0 < (supp y).card := Finset.card_pos.2 hTnonempty
    obtain ⟨t₁, ht₁, t₂, ht₂, ht12⟩ := Finset.one_lt_card.1 (by omega : 1 < (supp y).card)
    set k : ZMod p := t₂ - t₁ with hk
    have hk0 : k ≠ 0 := sub_ne_zero.2 ht12.symm
    have hy'X : (fun i : ZMod p => y (i - k)) ∈ X := by
      have := htrans k.val y hyX
      simpa [ZMod.natCast_zmod_val] using this
    have hsupp' : ∀ j, j ∈ supp (fun i : ZMod p => y (i - k)) ↔ j - k ∈ supp y := by
      intro j; simp [mem_supp]
    have hcard' : (supp (fun i : ZMod p => y (i - k))).card = Nat.find hex := by
      rw [← hym]
      refine Finset.card_bij (fun j _ => j - k) (fun j hj => (hsupp' j).1 hj)
        (fun a _ b _ h => sub_left_injective h) (fun j hj => ⟨j + k, ?_, by simp⟩)
      rw [hsupp']
      simpa using hj
    have heq := supp_eq_of_mem_inter hS hnab X hproj hmin hyX hy'X hym hcard' ht₂
      ((hsupp' t₂).2 (by
        have h : t₂ - k = t₁ := by rw [hk]; ring
        rw [h]; exact ht₁))
    have hiff : ∀ j, j ∈ supp y ↔ j - k ∈ supp y := by
      intro j
      rw [← hsupp', ← heq]
    have hall : ∀ n : ℕ, t₁ + n * k ∈ supp y := by
      intro n
      induction n with
      | zero => simpa using ht₁
      | succ n ih =>
        rw [hiff]
        have : t₁ + ((n + 1 : ℕ) : ZMod p) * k - k = t₁ + n * k := by push_cast; ring
        rw [this]
        exact ih
    apply hTne
    refine Finset.eq_univ_of_forall fun j => ?_
    have h1 := hall ((j - t₁) * k⁻¹).val
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hk0, mul_one] at h1
    have h2 : t₁ + (j - t₁) = j := by ring
    rwa [h2] at h1
  obtain ⟨t₀, ht₀⟩ := Finset.card_eq_one.1 hT1
  have ht₀y : t₀ ∈ supp y := by rw [ht₀]; exact Finset.mem_singleton_self t₀
  have hsingle : ∀ s : S, Pi.mulSingle t₀ s ∈ X := by
    intro s
    obtain ⟨u, huX, huT, hut⟩ :=
      exists_supp_subset hS X hproj hyX subset_rfl (mem_supp.1 ht₀y) s
    have hu : u = Pi.mulSingle t₀ s := by
      funext i
      by_cases hi : i = t₀
      · subst hi; simp [hut]
      · have h1 : u i = 1 := by
          by_contra h
          have := huT (mem_supp.2 h)
          rw [ht₀, Finset.mem_singleton] at this
          exact hi this
        simp [h1, hi]
    exact hu ▸ huX
  have hsingle' : ∀ (j : ZMod p) (s : S), Pi.mulSingle j s ∈ X := by
    intro j s
    have := htrans (j - t₀).val _ (hsingle s)
    convert this using 1
    funext i
    simp only [ZMod.natCast_zmod_val, Pi.mulSingle_apply, sub_eq_iff_eq_add]
    have h : t₀ + (j - t₀) = j := by ring
    rw [h]
  refine (Subgroup.eq_top_iff' X).2 fun f => ?_
  rw [← Finset.noncommProd_mulSingle f]
  exact Subgroup.noncommProd_mem X _ fun j _ => hsingle' j (f j)

end GL83.CompFam
