module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.TwoTwo
public import CFSG.CGT.PushingUpLit.CGT6X.End3Mod

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.CGT6

section Faithful

theorem slAct_faithful {f : ℕ} (s : Matrix.SpecialLinearGroup (Fin 2) (Fq f))
    (h : ∀ m, slAct f s m = m) : s = 1 :=
  sl2_eq_one_of_mulVec_fix s fun w => by
    have := h (Multiplicative.ofAdd w)
    simpa [slAct] using this

theorem altAct_faithful {n : ℕ} (hn : 3 ≤ n) (s : alternatingGroup (Fin n))
    (h : ∀ m, altAct n s m = m) : s = 1 := by
  classical
  have hmem : ∀ i j : Fin n, i ≠ j →
      Multiplicative.ofAdd (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) ∈
        G6.coreMod n := by
    intro i j hij
    rw [G6.mem_coreMod]
    simp [Finset.sum_add_distrib, Finset.sum_pi_single']
    decide
  have hmove : ∀ i j : Fin n, i ≠ j → (s : Equiv.Perm (Fin n)) i ≠ i →
      (s : Equiv.Perm (Fin n)) i = j := by
    intro i j hij hsi
    have h1 := h ⟨_, hmem i j hij⟩
    have h2 := congrArg (fun m : ↥(G6.coreMod n) => Multiplicative.toAdd (m : G6.PermMod n)
      ((s : Equiv.Perm (Fin n)) i)) h1
    simp [altAct, G6.coreAct, G6.permAct_apply, Pi.single_apply, hij, hsi] at h2
    exact h2
  by_contra hs1
  have hsne : (s : Equiv.Perm (Fin n)) ≠ 1 := fun h' => hs1 (Subtype.ext h')
  obtain ⟨i, hi⟩ : ∃ i, (s : Equiv.Perm (Fin n)) i ≠ i := by
    by_contra hall
    push Not at hall
    exact hsne (Equiv.ext hall)
  have hcard : 1 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Finset.one_lt_card.mp hcard
  have e₁ := hmove i j₁ (Ne.symm (Finset.ne_of_mem_erase hj₁)) hi
  have e₂ := hmove i j₂ (Ne.symm (Finset.ne_of_mem_erase hj₂)) hi
  exact hj (e₁.symm.trans e₂)

end Faithful

section Transfer

variable {V : Type} [CommGroup V] [Finite V] {Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem indec_commV (hcg : CommGen Y) (hsq : SimpleQuot Y) :
    ∀ A B : Subgroup ↥(commV Y), GInv (resHom Y).range A → GInv (resHom Y).range B →
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥ := by
  intro A B hA hB hAB hsup
  have hC : ∀ N : Subgroup V, (∀ g ∈ Y, ∀ n ∈ N, g n ∈ N) → N ≤ commV Y →
      N ≤ commV Y ⊓ fixV Y ∨ N = commV Y := by
    intro N hN hNU
    have hNC : ∀ g ∈ Y, ∀ n ∈ N ⊔ (commV Y ⊓ fixV Y), g n ∈ N ⊔ (commV Y ⊓ fixV Y) := by
      intro g hg n hn
      obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hn
      rw [map_mul, hc.2 g hg]
      exact mul_mem (Subgroup.mem_sup_left (hN g hg a ha)) (Subgroup.mem_sup_right hc)
    have hle : commV Y ⊓ fixV Y ≤ N ⊔ (commV Y ⊓ fixV Y) := le_sup_right
    have hle2 : N ⊔ (commV Y ⊓ fixV Y) ≤ commV Y := sup_le hNU inf_le_left
    rcases hsq.2 _ hNC hle hle2 with h | h
    · exact Or.inl (le_sup_left.trans h.le)
    · right
      apply le_antisymm hNU
      apply hcg N
      intro g hg u hu
      rw [← h] at hu
      obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
      have : g (a * c) * (a * c)⁻¹ = g a * a⁻¹ := by
        rw [map_mul, hc.2 g hg, mul_inv_rev]
        group
      rw [this]
      exact mul_mem (hN g hg a ha) (inv_mem ha)
  let A' : Subgroup V := A.map (commV Y).subtype
  let B' : Subgroup V := B.map (commV Y).subtype
  have hA'inv : ∀ g ∈ Y, ∀ a ∈ A', g a ∈ A' := by
    rintro g hg _ ⟨a, ha, rfl⟩
    exact ⟨resHom Y ⟨g, hg⟩ a, hA _ ⟨⟨g, hg⟩, rfl⟩ a ha, rfl⟩
  have hB'inv : ∀ g ∈ Y, ∀ b ∈ B', g b ∈ B' := by
    rintro g hg _ ⟨b, hb, rfl⟩
    exact ⟨resHom Y ⟨g, hg⟩ b, hB _ ⟨⟨g, hg⟩, rfl⟩ b hb, rfl⟩
  have hA'U : A' ≤ commV Y := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hB'U : B' ≤ commV Y := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hsup' : A' ⊔ B' = commV Y := by
    rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htop : ∀ N : Subgroup ↥(commV Y), N.map (commV Y).subtype = commV Y → N = ⊤ := by
    intro N hN
    rw [eq_top_iff]
    intro w _
    have : (w : V) ∈ N.map (commV Y).subtype := by
      rw [hN]
      exact w.2
    obtain ⟨w', hw', hww'⟩ := this
    have hw'w : w' = w := Subtype.ext hww'
    rwa [← hw'w]
  rcases hC A' hA'inv hA'U with hAC | hAU
  · rcases hC B' hB'inv hB'U with hBC | hBU
    · exfalso
      apply hsq.1
      have h1 := sup_le hAC hBC
      rw [hsup'] at h1
      exact le_antisymm h1 inf_le_left
    · left
      have hBt := htop B hBU
      rw [hBt, inf_top_eq] at hAB
      exact hAB
  · right
    have hAt := htop A hAU
    rw [hAt, top_inf_eq] at hAB
    exact hAB

omit [Finite V] in
theorem commV_resHom_range (hcg : CommGen Y) : commV (resHom Y).range = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hN : commV Y ≤ (commV (resHom Y).range).map (commV Y).subtype := by
    apply hcg
    intro g hg u hu
    have hgu : g u * u⁻¹ ∈ commV Y := mul_mem (commV_invariant hg hu) (inv_mem hu)
    refine ⟨⟨g u * u⁻¹, hgu⟩, ?_, rfl⟩
    have h1 : (⟨g u * u⁻¹, hgu⟩ : ↥(commV Y)) =
        resHom Y ⟨g, hg⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(commV Y))⁻¹ := Subtype.ext rfl
    rw [h1]
    exact Subgroup.subset_closure ⟨resHom Y ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, ⟨u, hu⟩, rfl⟩
  obtain ⟨w', hw', hww'⟩ := hN w.2
  have hw'w : w' = w := Subtype.ext hww'
  rwa [← hw'w]

variable {S M : Type} [Group S] [Group M] {act : S → M → M}

omit [Finite V] in
theorem section_on_commV (hcg : CommGen Y) (hfaith : ∀ s : S, (∀ m, act s m = m) → s = 1)
    (hsec : IsNatSectionBy act Y (commV Y) (commV Y ⊓ fixV Y)) :
    IsNatSectionBy act (resHom Y).range (commV (resHom Y).range)
      (commV (resHom Y).range ⊓ fixV (resHom Y).range) ∧
    Nat.card ↥(commV (resHom Y).range ⊓ fixV (resHom Y).range) =
      Nat.card ↥(commV Y ⊓ fixV Y) := by
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hsec
  have hinj : Function.Injective (resHom Y) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have htriv : ∀ u : ↥(commV Y), (g : MulAut V) (u : V) = u := by
      intro u
      have := congrArg (fun φ : MulAut ↥(commV Y) => ((φ u : ↥(commV Y)) : V)) hg
      simpa [CGT6.resHom_apply] using this
    have hθ : θ g = 1 := by
      apply hfaith
      intro m
      obtain ⟨u, rfl⟩ := hβs m
      have hp : (g : MulAut V) (u : V) ∈ commV Y := commV_invariant g.2 u.2
      have h1 := hβe g u hp
      have h2 : (⟨(g : MulAut V) (u : V), hp⟩ : ↥(commV Y)) = u := Subtype.ext (htriv u)
      rw [h2] at h1
      exact h1.symm
    exact θ.injective (by rw [hθ, map_one])
  have hU1 := commV_resHom_range hcg
  let e : ↥Y ≃* ↥(resHom Y).range := MonoidHom.ofInjective hinj
  let θ' : ↥(resHom Y).range ≃* S := e.symm.trans θ
  let β' : ↥(commV (resHom Y).range) →* M := β.comp (commV (resHom Y).range).subtype
  have hβ's : Function.Surjective β' := by
    intro m
    obtain ⟨u, hu⟩ := hβs m
    exact ⟨⟨u, by rw [hU1]; exact Subgroup.mem_top u⟩, hu⟩
  have hβ'k : β'.ker = (commV (resHom Y).range ⊓ fixV (resHom Y).range).subgroupOf
      (commV (resHom Y).range) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (w : ↥(commV Y)) ∈ β.ker := h
      rw [hβk, Subgroup.mem_subgroupOf] at h1
      refine ⟨w.2, ?_⟩
      rintro x ⟨g, rfl⟩
      exact Subtype.ext (h1.2 g g.2)
    · rintro ⟨-, hw⟩
      show β (w : ↥(commV Y)) = 1
      have : (w : ↥(commV Y)) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        refine ⟨(w : ↥(commV Y)).2, fun g hg => ?_⟩
        have := hw (resHom Y ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
        exact congrArg Subtype.val this
      exact this
  refine ⟨⟨fun x hx p hp => commV_invariant hx hp, θ', β', hβ's, hβ'k, ?_⟩, ?_⟩
  · intro x p hp
    obtain ⟨g, rfl⟩ := e.surjective x
    have hgp : (g : MulAut V) ((p : ↥(commV Y)) : V) ∈ commV Y :=
      commV_invariant g.2 (p : ↥(commV Y)).2
    have h1 := hβe g (p : ↥(commV Y)) hgp
    have h2 : θ' (e g) = θ g := by simp [θ']
    rw [h2]
    exact h1
  · apply Nat.card_congr
    refine Equiv.ofBijective
      (fun w : ↥(commV (resHom Y).range ⊓ fixV (resHom Y).range) =>
        (⟨((w : ↥(commV Y)) : V), (w : ↥(commV Y)).2,
          fun g hg => congrArg Subtype.val (w.2.2 (resHom Y ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩)⟩ :
          ↥(commV Y ⊓ fixV Y))) ⟨?_, ?_⟩
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(commV Y ⊓ fixV Y) => (z : V)) h
    · intro v
      refine ⟨⟨⟨v.1, v.2.1⟩, ?_, ?_⟩, rfl⟩
      · rw [hU1]
        exact Subgroup.mem_top _
      · intro x hx
        obtain ⟨g, rfl⟩ := hx
        exact Subtype.ext (v.2.2 g g.2)

theorem card_fix_le_of_sl (hM2 : H1NaturalSL2) (hV : ∀ v : V, v ^ 2 = 1) (hcg : CommGen Y)
    (hsq : SimpleQuot Y) {f : ℕ} (hf : 2 ≤ f)
    (hsec : IsNatSectionBy (slAct f) Y (commV Y) (commV Y ⊓ fixV Y)) :
    Nat.card ↥(commV Y ⊓ fixV Y) ≤ 2 ^ f := by
  obtain ⟨hsec', hcard⟩ := section_on_commV hcg slAct_faithful hsec
  have hVU : ∀ u : ↥(commV Y), u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV u)
  have h := (hM2 f hf ↥(commV Y) hVU (resHom Y).range (indec_commV hcg hsq) hsec').2
  rw [← hcard]
  exact h

theorem fix_eq_bot_of_alt (hV : ∀ v : V, v ^ 2 = 1) (hcg : CommGen Y) (hsq : SimpleQuot Y)
    (hsec : IsNatSectionBy (altAct 5) Y (commV Y) (commV Y ⊓ fixV Y)) :
    commV Y ⊓ fixV Y = ⊥ := by
  obtain ⟨hsec', hcard⟩ := section_on_commV hcg (altAct_faithful (by norm_num)) hsec
  have hVU : ∀ u : ↥(commV Y), u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV u)
  have h := emb_two_two ↥(commV Y) hVU (resHom Y).range 5 (by norm_num) (by decide)
    (indec_commV hcg hsq) (commV (resHom Y).range ⊓ fixV (resHom Y).range)
    (commV (resHom Y).range) inf_le_left
    (fun g hg a ha => by rw [ha.2 g hg]; exact ha)
    (fun g hg a ha => commV_invariant hg ha)
    (fun g hg a ha => ha.2 g hg)
    (fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩) hsec'
  have h1 : Nat.card ↥(commV (resHom Y).range ⊓ fixV (resHom Y).range) = 1 := by
    rw [h.1]
    exact Subgroup.card_bot
  rw [hcard] at h1
  exact Subgroup.card_eq_one.mp h1

end Transfer

end CFSG.CGT.PushingUpLit.CGT6X.End3
