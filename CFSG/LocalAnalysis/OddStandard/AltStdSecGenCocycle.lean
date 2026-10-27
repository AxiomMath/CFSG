module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenAsm

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

section Cocycle

variable {G : Type*} [Group G] {n : ℕ}

@[expose] def RFSame (φ : RootFamily G n) (S S' : Finset (Fin n)) (hS : S.card = 3)
    (hS' : S'.card = 3) : Prop :=
  ∀ (x : Perm (Fin n)) (hx : x ∈ altSub Sᶜ) (hx' : x ∈ altSub S'ᶜ),
    φ S hS ⟨x, hx⟩ = φ S' hS' ⟨x, hx'⟩

@[expose] def RFOpp (φ : RootFamily G n) (z : G) (S S' : Finset (Fin n)) (hS : S.card = 3)
    (hS' : S'.card = 3) : Prop :=
  ∀ (x : Perm (Fin n)) (hx : x ∈ altSub Sᶜ) (hx' : x ∈ altSub S'ᶜ),
    φ S hS ⟨x, hx⟩ = z * φ S' hS' ⟨x, hx'⟩ * z⁻¹

theorem exists_common_cyc3_of_card (S S' S'' : Finset (Fin n))
    (hcard : (S ∪ S' ∪ S'').card + 3 ≤ n) :
    ∃ x : Perm (Fin n), x ≠ 1 ∧ x ∈ altSub Sᶜ ∧ x ∈ altSub S'ᶜ ∧ x ∈ altSub S''ᶜ := by
  classical
  obtain ⟨R, hR, hRav⟩ := exists_root_avoiding (n := n)
    ((S ∪ S' ∪ S'').image Fin.val) (by
      have h1 := Finset.card_image_le (s := S ∪ S' ∪ S'') (f := Fin.val)
      omega)
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hR
  have hfix : ∀ (T : Finset (Fin n)), (∀ s ∈ T, s ∈ S ∪ S' ∪ S'') →
      cyc3 a b c ∈ altSub (Tᶜ) := by
    intro T hT
    refine mem_altSub.2 ⟨sign_cyc3 hab hbc, fun i hi => ?_⟩
    have hiT : i ∈ T := by simpa using hi
    refine cyc3_apply_of_ne ?_ ?_ ?_
    · rintro rfl
      exact hRav i (by simp) (Finset.mem_image_of_mem _ (hT i hiT))
    · rintro rfl
      exact hRav i (by simp) (Finset.mem_image_of_mem _ (hT i hiT))
    · rintro rfl
      exact hRav i (by simp) (Finset.mem_image_of_mem _ (hT i hiT))
  refine ⟨cyc3 a b c, ?_, hfix S (fun s hs => by simp [hs]), hfix S' (fun s hs => by simp [hs]),
    hfix S'' (fun s hs => by simp [hs])⟩
  intro h1
  have := cyc3_apply_left (x := a) (y := b) (z := c) hab hac
  rw [h1] at this
  exact hab (by simpa using this)

@[expose] def cjHom (z : G) (b : Bool) : G →* G :=
  bif b then (MulAut.conj z).toMonoidHom else MonoidHom.id G

theorem cjHom_true (z g : G) : cjHom z true g = z * g * z⁻¹ := rfl

theorem cjHom_false (z g : G) : cjHom z false g = g := rfl

theorem cjHom_cjHom {z : G} (hz : z * z = 1) (b b' : Bool) (g : G) :
    cjHom z b (cjHom z b' g) = cjHom z (xor b b') g := by
  cases b <;> cases b'
  · rfl
  · rfl
  · rfl
  · show z * (z * g * z⁻¹) * z⁻¹ = g
    calc z * (z * g * z⁻¹) * z⁻¹ = (z * z) * g * (z * z)⁻¹ := by group
      _ = g := by rw [hz]; group

theorem eq_or_fixed_of_cjHom_eq {z : G} {g : G} {b b' : Bool}
    (h : cjHom z b g = cjHom z b' g) : b = b' ∨ g = z * g * z⁻¹ := by
  cases b <;> cases b'
  · exact Or.inl rfl
  · exact Or.inr h
  · exact Or.inr h.symm
  · exact Or.inl rfl

@[expose] def RFRel (φ : RootFamily G n) (z : G) (b : Bool) (S S' : Finset (Fin n))
    (hS : S.card = 3) (hS' : S'.card = 3) : Prop :=
  ∀ (x : Perm (Fin n)) (hx : x ∈ altSub Sᶜ) (hx' : x ∈ altSub S'ᶜ),
    φ S hS ⟨x, hx⟩ = cjHom z b (φ S' hS' ⟨x, hx'⟩)

structure RootFamily.IsPreWLift (φ : RootFamily G n) (z : G)
    (ι : alternatingGroup (Fin n) →* G) : Prop where
  sq : z * z = 1
  diag : ∀ (S : Finset (Fin n)) (hS : S.card = 3) (x : ↥(altSub Sᶜ)),
    φ S hS x * (z * φ S hS x * z⁻¹) =
      ι (Subgroup.inclusion (altSub_le_alternatingGroup Sᶜ) x)
  comm : ∀ (S : Finset (Fin n)) (hS : S.card = 3) (x y : ↥(altSub Sᶜ)),
    φ S hS x * (z * φ S hS y * z⁻¹) = (z * φ S hS y * z⁻¹) * φ S hS x
  rigid : ∀ (S : Finset (Fin n)) (hS : S.card = 3) (x : ↥(altSub Sᶜ)),
    φ S hS x = z * φ S hS x * z⁻¹ → x = 1

variable {φ : RootFamily G n} {z : G} {ι : alternatingGroup (Fin n) →* G}

theorem RFRel.cocycle_of_card (h : φ.IsPreWLift z ι) {b b' b'' : Bool}
    {S S' S'' : Finset (Fin n)} {hS : S.card = 3} {hS' : S'.card = 3} {hS'' : S''.card = 3}
    (hcard : (S ∪ S' ∪ S'').card + 3 ≤ n)
    (h₁ : RFRel φ z b S S' hS hS') (h₂ : RFRel φ z b' S' S'' hS' hS'')
    (h₃ : RFRel φ z b'' S S'' hS hS'') : b'' = xor b b' := by
  obtain ⟨x, hx1, hxS, hxS', hxS''⟩ := exists_common_cyc3_of_card S S' S'' hcard
  have e₁ := h₁ x hxS hxS'
  have e₂ := h₂ x hxS' hxS''
  have e₃ := h₃ x hxS hxS''
  rw [e₂, cjHom_cjHom h.sq] at e₁
  rw [e₁] at e₃
  rcases eq_or_fixed_of_cjHom_eq e₃ with h4 | h4
  · exact h4.symm
  · exact absurd (congrArg Subtype.val (h.rigid S'' hS'' ⟨x, hxS''⟩ h4)) (by simpa using hx1)

theorem RFRel.cocycle_of_family (hn : 11 ≤ n) (h : φ.IsPreWLift z ι)
    (t : ∀ (S S' : Finset (Fin n)), S.card = 3 → S'.card = 3 → Bool)
    (ht : ∀ (S S' : Finset (Fin n)) (hS : S.card = 3) (hS' : S'.card = 3),
      RFRel φ z (t S S' hS hS') S S' hS hS')
    {S S' S'' : Finset (Fin n)} (hS : S.card = 3) (hS' : S'.card = 3) (hS'' : S''.card = 3) :
    t S S'' hS hS'' = xor (t S S' hS hS') (t S' S'' hS' hS'') := by
  classical
  by_cases hcard : (S ∪ S' ∪ S'').card + 3 ≤ n
  · exact RFRel.cocycle_of_card h hcard (ht S S' hS hS') (ht S' S'' hS' hS'') (ht S S'' hS hS'')
  have hu1 := Finset.card_union_add_card_inter S S'
  have hu2 := Finset.card_union_add_card_inter (S ∪ S') S''
  have hi1 : (S ∩ S').card = 0 := by omega
  have hi2 : ((S ∪ S') ∩ S'').card = 0 := by omega
  rw [Finset.card_eq_zero] at hi1 hi2
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
  obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < S'.card)
  obtain ⟨c, hc⟩ := Finset.card_pos.1 (by omega : 0 < S''.card)
  have hab : a ≠ b := by
    rintro rfl
    have : a ∈ S ∩ S' := Finset.mem_inter.2 ⟨ha, hb⟩
    rw [hi1] at this
    simp at this
  have hac : a ≠ c := by
    rintro rfl
    have : a ∈ (S ∪ S') ∩ S'' := Finset.mem_inter.2 ⟨Finset.mem_union_left _ ha, hc⟩
    rw [hi2] at this
    simp at this
  have hbc : b ≠ c := by
    rintro rfl
    have : b ∈ (S ∪ S') ∩ S'' := Finset.mem_inter.2 ⟨Finset.mem_union_right _ hb, hc⟩
    rw [hi2] at this
    simp at this
  set T : Finset (Fin n) := {a, b, c} with hTdef
  have hT : T.card = 3 := by
    rw [hTdef, Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_pair hbc]
  have hcard₁ : (S ∪ S' ∪ T).card + 3 ≤ n := by
    have hsub : S ∪ S' ∪ T ⊆ S ∪ S' ∪ {c} := by
      intro x hx
      simp only [hTdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with (hx | hx) | hx | hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl (hx ▸ ha))
      · exact Or.inl (Or.inr (hx ▸ hb))
      · exact Or.inr hx
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S ∪ S') {c}
    rw [Finset.card_singleton] at h2
    omega
  have hcard₂ : (S' ∪ S'' ∪ T).card + 3 ≤ n := by
    have hsub : S' ∪ S'' ∪ T ⊆ S' ∪ S'' ∪ {a} := by
      intro x hx
      simp only [hTdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with (hx | hx) | hx | hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
      · exact Or.inl (Or.inl (hx ▸ hb))
      · exact Or.inl (Or.inr (hx ▸ hc))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S' ∪ S'') {a}
    have h3 := Finset.card_union_le S' S''
    rw [Finset.card_singleton] at h2
    omega
  have hcard₃ : (S ∪ S'' ∪ T).card + 3 ≤ n := by
    have hsub : S ∪ S'' ∪ T ⊆ S ∪ S'' ∪ {b} := by
      intro x hx
      simp only [hTdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with (hx | hx) | hx | hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl (hx ▸ ha))
      · exact Or.inr hx
      · exact Or.inl (Or.inr (hx ▸ hc))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S ∪ S'') {b}
    have h3 := Finset.card_union_le S S''
    rw [Finset.card_singleton] at h2
    omega
  have e₁ := RFRel.cocycle_of_card h hcard₁ (ht S S' hS hS') (ht S' T hS' hT) (ht S T hS hT)
  have e₂ := RFRel.cocycle_of_card h hcard₂ (ht S' S'' hS' hS'') (ht S'' T hS'' hT)
    (ht S' T hS' hT)
  have e₃ := RFRel.cocycle_of_card h hcard₃ (ht S S'' hS hS'') (ht S'' T hS'' hT) (ht S T hS hT)
  rw [e₂, e₃] at e₁
  revert e₁
  generalize t S S'' hS hS'' = a
  generalize t S S' hS hS' = b
  generalize t S' S'' hS' hS'' = c
  generalize t S'' T hS'' hT = d
  revert a b c d
  decide

theorem conj_conj_of_sq {z : G} (hz : z * z = 1) (g : G) : z * (z * g * z⁻¹) * z⁻¹ = g :=
  cjHom_cjHom hz true true g

theorem exists_consistent_of_dichotomy (hn : 11 ≤ n) (h : φ.IsPreWLift z ι)
    (hdich : ∀ (S S' : Finset (Fin n)) (hS : S.card = 3) (hS' : S'.card = 3),
      RFSame φ S S' hS hS' ∨ RFOpp φ z S S' hS hS')
    {S₁ : Finset (Fin n)} (hS₁ : S₁.card = 3) :
    ∃ φ' : RootFamily G n, φ'.IsWLift z ι := by
  have hrel : ∀ (S S' : Finset (Fin n)) (hS : S.card = 3) (hS' : S'.card = 3),
      ∃ b, RFRel φ z b S S' hS hS' := fun S S' hS hS' =>
    (hdich S S' hS hS').elim (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
  choose t ht using hrel
  refine ⟨fun S hS => (cjHom z (t S₁ S hS₁ hS)).comp (φ S hS), ?_, ?_, ?_⟩
  · unfold RootFamily.Agree
    intro S hS S' hS' x hx hx'
    simp only [MonoidHom.comp_apply]
    rw [ht S S' hS hS' x hx hx', cjHom_cjHom h.sq]
    have hc := RFRel.cocycle_of_family hn h t ht hS₁ hS hS'
    rw [hc]
  · intro S hS x
    simp only [MonoidHom.comp_apply]
    cases t S₁ S hS₁ hS
    · simpa [cjHom_false] using h.diag S hS x
    · rw [cjHom_true, conj_conj_of_sq h.sq, ← h.comm S hS x x]
      simpa using h.diag S hS x
  · intro S hS x y
    simp only [MonoidHom.comp_apply]
    cases t S₁ S hS₁ hS
    · simpa [cjHom_false] using h.comm S hS x y
    · rw [cjHom_true, cjHom_true, conj_conj_of_sq h.sq]
      exact (h.comm S hS y x).symm

end Cocycle

end CFSG.OddStandard.AltStdSec
