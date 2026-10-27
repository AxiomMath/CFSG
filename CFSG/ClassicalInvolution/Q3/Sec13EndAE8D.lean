module

public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8C

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

open scoped commutatorElement

variable {Ω : Set (Subgroup G)} {u : G}

section ae8dT8

private theorem ae8d_pair_meet {a b : Fin 8} {t : Finset (Fin 8)}
    (h : (({a, b} : Finset (Fin 8)) ∩ t).Nonempty) : a ∈ t ∨ b ∈ t := by
  obtain ⟨x, hx⟩ := h
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with ⟨rfl | rfl, hxt⟩
  · exact Or.inl hxt
  · exact Or.inr hxt

private theorem ae8d_eq_pair {x y : Fin 8} {t : Finset (Fin 8)} (hxy : x ≠ y)
    (ht : t.card = 2) (hx : x ∈ t) (hy : y ∈ t) : t = {x, y} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · exact Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩
  · exact le_of_eq (by rw [ht, Finset.card_pair hxy])

private theorem ae8d_majority {A B C : Prop} (h1 : A ∨ B) (h2 : B ∨ C) (h3 : A ∨ C) :
    (A ∧ B) ∨ (B ∧ C) ∨ (A ∧ C) := by
  tauto

theorem ae8d_star_of_pairwise (F : Finset {s : Finset (Fin 8) // s.card = 2})
    (hF : ∀ s ∈ F, ∀ t ∈ F, ((s : Finset (Fin 8)) ∩ (t : Finset (Fin 8))).Nonempty)
    (h4 : 4 ≤ F.card) : ∃ i : Fin 8, ∀ s ∈ F, i ∈ (s : Finset (Fin 8)) := by
  obtain ⟨s1, hs1⟩ : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, b, hab, hs1eq⟩ := Finset.card_eq_two.mp s1.2
  have hclaim : (∀ t ∈ F, a ∈ (t : Finset (Fin 8))) ∨
      (∀ t ∈ F, b ∈ (t : Finset (Fin 8))) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨t1, ht1, ht1a⟩, ⟨t2, ht2, ht2b⟩⟩ := hcon
    have h1 := hF s1 hs1 t1 ht1
    have h2 := hF s1 hs1 t2 ht2
    rw [hs1eq] at h1 h2
    have hb1 : b ∈ (t1 : Finset (Fin 8)) := (ae8d_pair_meet h1).resolve_left ht1a
    have ha2 : a ∈ (t2 : Finset (Fin 8)) := (ae8d_pair_meet h2).resolve_right ht2b
    have ht1card : (t1 : Finset (Fin 8)).card = 2 := t1.2
    have ht2card : (t2 : Finset (Fin 8)).card = 2 := t2.2
    have hc1' : 1 < (t1 : Finset (Fin 8)).card := by omega
    obtain ⟨c, hc1, hcb⟩ := Finset.exists_mem_ne hc1' b
    have hca : c ≠ a := by
      rintro rfl
      exact ht1a hc1
    have ht1eq : (t1 : Finset (Fin 8)) = {b, c} :=
      ae8d_eq_pair (Ne.symm hcb) ht1card hb1 hc1
    have h12 := hF t1 ht1 t2 ht2
    rw [ht1eq] at h12
    have hc2 : c ∈ (t2 : Finset (Fin 8)) := (ae8d_pair_meet h12).resolve_left ht2b
    have ht2eq : (t2 : Finset (Fin 8)) = {a, c} :=
      ae8d_eq_pair (Ne.symm hca) ht2card ha2 hc2
    have hbc : b ≠ c := Ne.symm hcb
    have hac : a ≠ c := Ne.symm hca
    have hcover : ∀ t ∈ F, (t : Finset (Fin 8)) = {a, b} ∨
        (t : Finset (Fin 8)) = {b, c} ∨ (t : Finset (Fin 8)) = {a, c} := by
      intro t ht
      have e1 := hF s1 hs1 t ht
      have e2 := hF t1 ht1 t ht
      have e3 := hF t2 ht2 t ht
      rw [hs1eq] at e1
      rw [ht1eq] at e2
      rw [ht2eq] at e3
      have hmaj := ae8d_majority (ae8d_pair_meet e1) (ae8d_pair_meet e2)
        (ae8d_pair_meet e3)
      rcases hmaj with ⟨hat, hbt⟩ | ⟨hbt, hct⟩ | ⟨hat, hct⟩
      · exact Or.inl (ae8d_eq_pair hab t.2 hat hbt)
      · exact Or.inr (Or.inl (ae8d_eq_pair hbc t.2 hbt hct))
      · exact Or.inr (Or.inr (ae8d_eq_pair hac t.2 hat hct))
    have hsub : F.image Subtype.val ⊆ {{a, b}, {b, c}, {a, c}} := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      rcases hcover t ht with h | h | h <;> simp [h]
    have hle : (F.image Subtype.val).card ≤ 3 :=
      (Finset.card_le_card hsub).trans Finset.card_le_three
    rw [Finset.card_image_of_injective F Subtype.val_injective] at hle
    omega
  rcases hclaim with h | h
  · exact ⟨a, h⟩
  · exact ⟨b, h⟩

theorem ae8d_card_star (p : Fin 8) :
    (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
      p ∈ (s : Finset (Fin 8))).card = 7 := by
  revert p
  decide

private theorem ae8d_two_others :
    ∀ i : Fin 8, ∃ m m' : Fin 8, m ≠ i ∧ m' ≠ i ∧ m ≠ m' := by
  decide

private theorem ae8d_third : ∀ i k : Fin 8, i ≠ k → ∃ m : Fin 8, m ≠ i ∧ m ≠ k := by
  decide

private theorem ae8d_star_through (f : Equiv.Perm {s : Finset (Fin 8) // s.card = 2})
    (hf : ∀ s t : {s : Finset (Fin 8) // s.card = 2},
      ((s : Finset (Fin 8)) ∩ (t : Finset (Fin 8))).Nonempty ↔
        ((f s : Finset (Fin 8)) ∩ (f t : Finset (Fin 8))).Nonempty) (i : Fin 8) :
    ∃ j : Fin 8, ∀ s : {s : Finset (Fin 8) // s.card = 2},
      i ∈ (s : Finset (Fin 8)) → j ∈ (f s : Finset (Fin 8)) := by
  have hcard : ((Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
      i ∈ (s : Finset (Fin 8))).image f).card = 7 := by
    rw [Finset.card_image_of_injective _ f.injective, ae8d_card_star]
  have hpair : ∀ u ∈ (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
      i ∈ (s : Finset (Fin 8))).image f,
      ∀ v ∈ (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
      i ∈ (s : Finset (Fin 8))).image f,
      ((u : Finset (Fin 8)) ∩ (v : Finset (Fin 8))).Nonempty := by
    intro u hu v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    exact (hf s t).mp ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hs).2,
      (Finset.mem_filter.mp ht).2⟩⟩
  obtain ⟨j, hj⟩ := ae8d_star_of_pairwise _ hpair (by omega)
  refine ⟨j, fun s hs => hj (f s) (Finset.mem_image_of_mem f ?_)⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩

theorem T8_exists_perm (f : Equiv.Perm {s : Finset (Fin 8) // s.card = 2})
    (hf : ∀ s t : {s : Finset (Fin 8) // s.card = 2},
      ((s : Finset (Fin 8)) ∩ (t : Finset (Fin 8))).Nonempty ↔
        ((f s : Finset (Fin 8)) ∩ (f t : Finset (Fin 8))).Nonempty) :
    ∃! σ : Equiv.Perm (Fin 8), ∀ s : {s : Finset (Fin 8) // s.card = 2},
      (f s : Finset (Fin 8)) = (s : Finset (Fin 8)).image σ := by
  choose τ hτ using fun i : Fin 8 => ae8d_star_through f hf i
  have hG : ∀ i : Fin 8, (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
      i ∈ (s : Finset (Fin 8))).image f =
      (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
        τ i ∈ (s : Finset (Fin 8))) := by
    intro i
    apply Finset.eq_of_subset_of_card_le
    · intro u hu
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ i s (Finset.mem_filter.mp hs).2⟩
    · have h1 := ae8d_card_star i
      have h2 := ae8d_card_star (τ i)
      rw [Finset.card_image_of_injective _ f.injective]
      omega
  have hτinj : Function.Injective τ := by
    intro i k hik
    by_contra hne
    have h2 : (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
        τ i ∈ (s : Finset (Fin 8))) =
        (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
        τ k ∈ (s : Finset (Fin 8))) := by
      rw [hik]
    have h4 := Finset.image_injective f.injective ((hG i).trans (h2.trans (hG k).symm))
    obtain ⟨m, hmi, hmk⟩ := ae8d_third i k hne
    have hmem : (⟨{i, m}, Finset.card_pair (Ne.symm hmi)⟩ :
        {s : Finset (Fin 8) // s.card = 2}) ∈
        (Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
          i ∈ (s : Finset (Fin 8))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self i {m}⟩
    rw [h4] at hmem
    have hk : k ∈ ({i, m} : Finset (Fin 8)) := (Finset.mem_filter.mp hmem).2
    rcases Finset.mem_insert.mp hk with h | h
    · exact hne h.symm
    · exact hmk (Finset.mem_singleton.mp h).symm
  have hτbij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτinj
  have hP : ∀ s : {s : Finset (Fin 8) // s.card = 2},
      (f s : Finset (Fin 8)) = (s : Finset (Fin 8)).image τ := by
    intro s
    obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp s.2
    have ha : a ∈ (s : Finset (Fin 8)) := by
      rw [hsab]
      exact Finset.mem_insert_self a {b}
    have hb : b ∈ (s : Finset (Fin 8)) := by
      rw [hsab]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have hfs : (f s : Finset (Fin 8)).card = 2 := (f s).2
    have h1 : (f s : Finset (Fin 8)) = {τ a, τ b} :=
      ae8d_eq_pair (fun h => hab (hτinj h)) hfs (hτ a s ha) (hτ b s hb)
    rw [h1, hsab, Finset.image_insert, Finset.image_singleton]
  refine ⟨Equiv.ofBijective τ hτbij, fun s => hP s, ?_⟩
  intro σ' hσ'
  apply Equiv.ext
  intro i
  show σ' i = τ i
  have key : ∀ m : Fin 8, m ≠ i → σ' i = τ i ∨ σ' i = τ m := by
    intro m hm
    have hi : i ≠ m := Ne.symm hm
    have hmem : σ' i ∈ (f ⟨{i, m}, Finset.card_pair hi⟩ : Finset (Fin 8)) := by
      rw [hσ' ⟨{i, m}, Finset.card_pair hi⟩]
      exact Finset.mem_image_of_mem σ' (Finset.mem_insert_self i {m})
    rw [hP ⟨{i, m}, Finset.card_pair hi⟩] at hmem
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hmem
    have hx' : x ∈ ({i, m} : Finset (Fin 8)) := hx
    rcases Finset.mem_insert.mp hx' with h | h
    · left
      rw [h] at hxe
      exact hxe.symm
    · right
      rw [Finset.mem_singleton.mp h] at hxe
      exact hxe.symm
  obtain ⟨m, m', hmi, hm'i, hmm'⟩ := ae8d_two_others i
  by_contra hne
  have e1 : σ' i = τ m := (key m hmi).resolve_left hne
  have e2 : σ' i = τ m' := (key m' hm'i).resolve_left hne
  exact hmm' (hτinj (e1.symm.trans e2))

end ae8dT8

section ae8dPrim

open scoped Pointwise

private lemma ae8d_third_b : ∀ a b : Fin 8, ∃ c : Fin 8, c ≠ a ∧ c ≠ b := by
  decide

private lemma ae8d_pair (K : Subgroup (Equiv.Perm (Fin 8)))
    (hK : ∀ s t : {s : Finset (Fin 8) // s.card = 2}, ∃ g ∈ K,
      (s : Finset (Fin 8)).image g = (t : Finset (Fin 8)))
    {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g ∈ K, ({a, b} : Finset (Fin 8)).image g = {c, d} :=
  hK ⟨{a, b}, Finset.card_pair hab⟩ ⟨{c, d}, Finset.card_pair hcd⟩

private lemma ae8d_pt (K : Subgroup (Equiv.Perm (Fin 8)))
    (hK : ∀ s t : {s : Finset (Fin 8) // s.card = 2}, ∃ g ∈ K,
      (s : Finset (Fin 8)).image g = (t : Finset (Fin 8)))
    (a b : Fin 8) : ∃ g ∈ K, g a = b := by
  by_cases hab : a = b
  · exact ⟨1, K.one_mem, by simp [hab]⟩
  obtain ⟨c, hca, hcb⟩ := ae8d_third_b a b
  obtain ⟨g₁, hg₁K, hg₁⟩ := ae8d_pair K hK hab (Ne.symm hcb)
  have hmem₁ : g₁ a ∈ ({b, c} : Finset (Fin 8)) := by
    rw [← hg₁]
    exact Finset.mem_image_of_mem _ (by simp)
  have hx : g₁ a ≠ a := by
    intro h
    rw [h] at hmem₁
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₁
    rcases hmem₁ with h' | h'
    · exact hab h'
    · exact hca h'.symm
  obtain ⟨g₂, hg₂K, hg₂⟩ := ae8d_pair K hK hab hx.symm
  have hmem₂ : g₂ b ∈ ({a, g₁ a} : Finset (Fin 8)) := by
    rw [← hg₂]
    exact Finset.mem_image_of_mem _ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₂
  rcases hmem₂ with h | h
  · exact ⟨g₂⁻¹, K.inv_mem hg₂K, Equiv.Perm.inv_eq_iff_eq.mpr h.symm⟩
  · refine ⟨g₂⁻¹ * g₁, K.mul_mem (K.inv_mem hg₂K) hg₁K, ?_⟩
    rw [Equiv.Perm.mul_apply]
    exact Equiv.Perm.inv_eq_iff_eq.mpr h.symm

private lemma ae8d_trivial (K : Subgroup (Equiv.Perm (Fin 8)))
    (hK : ∀ s t : {s : Finset (Fin 8) // s.card = 2}, ∃ g ∈ K,
      (s : Finset (Fin 8)).image g = (t : Finset (Fin 8)))
    {B : Set (Fin 8)} (hB : MulAction.IsBlock ↥K B) :
    MulAction.IsTrivialBlock B := by
  unfold MulAction.IsTrivialBlock
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hns, hne⟩ := hcon
  obtain ⟨x, hx, x', hx', hxx'⟩ : ∃ x ∈ B, ∃ x' ∈ B, x ≠ x' := by
    by_contra! h
    apply hns
    intro x hx x' hx'
    exact h x hx x' hx'
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B := by
    by_contra! h
    exact hne (Set.eq_univ_of_forall h)
  have hxz : x ≠ z := by
    rintro rfl
    exact hz hx
  obtain ⟨g, hgK, hg⟩ := ae8d_pair K hK hxx' hxz
  have hxmem : x ∈ ({x, x'} : Finset (Fin 8)).image g := by
    rw [hg]
    simp
  obtain ⟨y, hy, hgy⟩ := Finset.mem_image.mp hxmem
  have hyB : y ∈ B := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h <;> rw [h] <;> assumption
  have hgyB : (⟨g, hgK⟩ : ↥K) • y ∈ B := by
    show g y ∈ B
    rw [hgy]
    exact hx
  have hgB : (⟨g, hgK⟩ : ↥K) • B = B := hB.smul_eq_of_mem hyB hgyB
  have hzmem : z ∈ ({x, x'} : Finset (Fin 8)).image g := by
    rw [hg]
    simp
  obtain ⟨y', hy', hgy'⟩ := Finset.mem_image.mp hzmem
  have hy'B : y' ∈ B := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with h | h <;> rw [h] <;> assumption
  have hzg : z ∈ (⟨g, hgK⟩ : ↥K) • B := Set.mem_smul_set.mpr ⟨y', hy'B, hgy'⟩
  rw [hgB] at hzg
  exact hz hzg

theorem ae8d_isPreprimitive (K : Subgroup (Equiv.Perm (Fin 8)))
    (hK : ∀ s t : {s : Finset (Fin 8) // s.card = 2}, ∃ g ∈ K,
      (s : Finset (Fin 8)).image g = (t : Finset (Fin 8))) :
    MulAction.IsPreprimitive ↥K (Fin 8) := by
  have hpt : MulAction.IsPretransitive ↥K (Fin 8) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hgK, hgab⟩ := ae8d_pt K hK a b
    exact ⟨⟨g, hgK⟩, hgab⟩
  exact ⟨fun hB => ae8d_trivial K hK hB⟩

theorem ae8d_isThreeCycle_of_extend (ι : Fin 6 ↪ Fin 8) (τ : Equiv.Perm (Fin 6))
    (hτ : τ.IsThreeCycle) (ρ : Equiv.Perm (Fin 8))
    (h1 : ∀ i : Fin 6, ρ (ι i) = ι (τ i)) (h2 : ∀ j : Fin 8, j ∉ Set.range ι → ρ j = j) :
    ρ.IsThreeCycle := by
  have hsupp : ρ.support = τ.support.map ι := by
    ext j
    rw [Equiv.Perm.mem_support, Finset.mem_map]
    constructor
    · intro hj
      by_cases hr : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hr
        refine ⟨i, Equiv.Perm.mem_support.mpr ?_, rfl⟩
        intro hi
        apply hj
        rw [h1, hi]
      · exact absurd (h2 j hr) hj
    · rintro ⟨i, hi, rfl⟩
      rw [h1]
      intro h
      exact (Equiv.Perm.mem_support.mp hi) (ι.injective h)
  refine card_support_eq_three_iff.mp ?_
  rw [hsupp, Finset.card_map]
  exact hτ.card_support

end ae8dPrim

section ae8dInj

theorem ae8d_inj_of_stars (p : Fin 6 → Fin 8)
    (S : Fin 6 → Fin 6 → {s : Finset (Fin 8) // s.card = 2})
    (hinj : ∀ a b a' b' : Fin 6, a ≠ b → a' ≠ b' → S a b = S a' b' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (hmem : ∀ a b : Fin 6, a ≠ b →
      p a ∈ (S a b : Finset (Fin 8)) ∧ p b ∈ (S a b : Finset (Fin 8))) :
    Function.Injective p := by
  intro a b hpab
  by_contra hab
  have key : ∀ c : Fin 6, c ≠ a → c ≠ b → p c = p a := by
    intro c hca hcb
    by_contra hc
    have hne : p a ≠ p c := fun h => hc h.symm
    have hac : a ≠ c := fun h => hca h.symm
    have hbc : b ≠ c := fun h => hcb h.symm
    have hcard : ({p a, p c} : Finset (Fin 8)).card = 2 := Finset.card_pair hne
    have hsub1 : ({p a, p c} : Finset (Fin 8)) ⊆ (S a c : Finset (Fin 8)) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hmem a c hac).1
      · exact (hmem a c hac).2
    have hsub2 : ({p a, p c} : Finset (Fin 8)) ⊆ (S b c : Finset (Fin 8)) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hpab]
        exact (hmem b c hbc).1
      · exact (hmem b c hbc).2
    have e1 : ({p a, p c} : Finset (Fin 8)) = (S a c : Finset (Fin 8)) :=
      Finset.eq_of_subset_of_card_le hsub1 (Eq.trans (S a c).2 hcard.symm).le
    have e2 : ({p a, p c} : Finset (Fin 8)) = (S b c : Finset (Fin 8)) :=
      Finset.eq_of_subset_of_card_le hsub2 (Eq.trans (S b c).2 hcard.symm).le
    have hSeq : S a c = S b c := Subtype.ext (e1.symm.trans e2)
    rcases hinj a c b c hac hbc hSeq with h | h
    · exact hab h.1
    · exact hac h.1
  have hall : ∀ c : Fin 6, p c = p a := by
    intro c
    by_cases hca : c = a
    · rw [hca]
    · by_cases hcb : c = b
      · rw [hcb, hpab]
      · exact key c hca hcb
  have hcardT : (Finset.univ.filter fun x : Fin 6 × Fin 6 => x.1 < x.2).card = 15 := by
    decide
  have hinjOn : Set.InjOn (fun x : Fin 6 × Fin 6 => S x.1 x.2)
      (↑(Finset.univ.filter fun x : Fin 6 × Fin 6 => x.1 < x.2) : Set (Fin 6 × Fin 6)) := by
    intro x hx y hy hxy
    have hx' : x.1 < x.2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    have hy' : y.1 < y.2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    have hxy' : S x.1 x.2 = S y.1 y.2 := hxy
    rcases hinj x.1 x.2 y.1 y.2 hx'.ne hy'.ne hxy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · have h3 : x.1 < x.1 := by
        calc x.1 < x.2 := hx'
          _ = y.1 := h2
          _ < y.2 := hy'
          _ = x.1 := h1.symm
      exact absurd h3 (lt_irrefl _)
  have himg : ((Finset.univ.filter fun x : Fin 6 × Fin 6 => x.1 < x.2).image
      (fun x : Fin 6 × Fin 6 => S x.1 x.2)).card = 15 := by
    rw [Finset.card_image_of_injOn hinjOn, hcardT]
  have hsub : ((Finset.univ.filter fun x : Fin 6 × Fin 6 => x.1 < x.2).image
      (fun x : Fin 6 × Fin 6 => S x.1 x.2)) ⊆
      Finset.univ.filter fun s : {s : Finset (Fin 8) // s.card = 2} =>
        p a ∈ (s : Finset (Fin 8)) := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
    have hx' : x.1 < x.2 := (Finset.mem_filter.1 hx).2
    have h4 : p x.1 ∈ (S x.1 x.2 : Finset (Fin 8)) := (hmem x.1 x.2 hx'.ne).1
    rw [hall x.1] at h4
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h4⟩
  have hle := Finset.card_le_card hsub
  rw [himg, ae8d_card_star (p a)] at hle
  omega

end ae8dInj

theorem ae8d_trivial_of_perfect {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    {A : Type*} [CommGroup A] (φ : Y →* A) (y : Y) : φ y = 1 := by
  have h : commutator Y ≤ φ.ker := by
    show ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ ≤ φ.ker
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)]
  rw [hperf] at h
  exact MonoidHom.mem_ker.mp (h (Subgroup.mem_top y))

theorem ae8d_delta_conj (u g x : G) : x ∈ Delta u ↔ g * x * g⁻¹ ∈ Delta u := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨g * h, by group⟩
  · rintro ⟨h, hh⟩
    refine ⟨g⁻¹ * h, ?_⟩
    have hx : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hx, hh]
    group

@[expose] def ae8d_cg (u g : G) : ↥(Delta u) ≃ ↥(Delta u) :=
  Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun x => ae8d_delta_conj u g x

theorem ae8d_cg_val (u g : G) (x : ↥(Delta u)) : ((ae8d_cg u g x : ↥(Delta u)) : G) =
    g * (x : G) * g⁻¹ := rfl

theorem ae8d_cg_mul (u g h : G) (x : ↥(Delta u)) :
    ae8d_cg u (g * h) x = ae8d_cg u g (ae8d_cg u h x) :=
  Subtype.ext (by rw [ae8d_cg_val, ae8d_cg_val, ae8d_cg_val]; group)

theorem ae8d_cg_one (u : G) (x : ↥(Delta u)) : ae8d_cg u 1 x = x :=
  Subtype.ext (by rw [ae8d_cg_val]; group)

@[expose] def ae8d_F {u : G} (E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2}) (g : G) :
    Equiv.Perm {s : Finset (Fin 8) // s.card = 2} :=
  (E.symm.trans (ae8d_cg u g)).trans E

theorem ae8d_F_apply {u : G} (E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2}) (g : G)
    (s : {s : Finset (Fin 8) // s.card = 2}) :
    ae8d_F E g s = E (ae8d_cg u g (E.symm s)) := rfl

theorem ae8d_F_mul {u : G} (E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2}) (g h : G)
    (s : {s : Finset (Fin 8) // s.card = 2}) :
    ae8d_F E (g * h) s = ae8d_F E g (ae8d_F E h s) := by
  rw [ae8d_F_apply, ae8d_F_apply, ae8d_F_apply, E.symm_apply_apply, ae8d_cg_mul]

theorem ae8d_F_one {u : G} (E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2})
    (s : {s : Finset (Fin 8) // s.card = 2}) : ae8d_F E 1 s = s := by
  rw [ae8d_F_apply, ae8d_cg_one, E.apply_symm_apply]

theorem ae8d_meet_iff {u : G} (E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2})
    (hE : ∀ x y : ↥(Delta u), (x ≠ y ∧ ((x : G) * y) ∈ Delta u) ↔
      (x ≠ y ∧ ((E x : Finset (Fin 8)) ∩ (E y : Finset (Fin 8))).Nonempty))
    (x y : ↥(Delta u)) :
    ((E x : Finset (Fin 8)) ∩ (E y : Finset (Fin 8))).Nonempty ↔
      (x = y ∨ (x : G) * y ∈ Delta u) := by
  by_cases h : x = y
  · subst h
    simp only [Finset.inter_self, true_or, iff_true]
    exact Finset.card_pos.mp (by rw [(E x).2]; norm_num)
  · have := hE x y
    simp only [h, ne_eq, not_false_eq_true, true_and] at this
    simp only [h, false_or]
    exact this.symm

theorem ae8d_F_meet {u : G} (E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2})
    (hE : ∀ x y : ↥(Delta u), (x ≠ y ∧ ((x : G) * y) ∈ Delta u) ↔
      (x ≠ y ∧ ((E x : Finset (Fin 8)) ∩ (E y : Finset (Fin 8))).Nonempty))
    (g : G) (s t : {s : Finset (Fin 8) // s.card = 2}) :
    ((s : Finset (Fin 8)) ∩ (t : Finset (Fin 8))).Nonempty ↔
      ((ae8d_F E g s : Finset (Fin 8)) ∩ (ae8d_F E g t : Finset (Fin 8))).Nonempty := by
  obtain ⟨x, rfl⟩ := E.surjective s
  obtain ⟨y, rfl⟩ := E.surjective t
  rw [ae8d_meet_iff E hE, ae8d_F_apply, ae8d_F_apply, E.symm_apply_apply,
    E.symm_apply_apply, ae8d_meet_iff E hE]
  rw [(ae8d_cg u g).injective.eq_iff]
  have h1 : ((ae8d_cg u g x : G)) * ((ae8d_cg u g y : G)) = g * ((x : G) * y) * g⁻¹ := by
    rw [ae8d_cg_val, ae8d_cg_val]
    group
  rw [h1]
  exact or_congr_right (ae8d_delta_conj u g _)


structure Points (u : G) where
  E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2}
  π : G →* Equiv.Perm (Fin 8)
  adj : ∀ x y : ↥(Delta u), (x ≠ y ∧ ((x : G) * y) ∈ Delta u) ↔
    (x ≠ y ∧ ((E x : Finset (Fin 8)) ∩ (E y : Finset (Fin 8))).Nonempty)
  equivariant : ∀ (g : G) (x y : ↥(Delta u)), (y : G) = g * x * g⁻¹ →
    (E y : Finset (Fin 8)) = (E x : Finset (Fin 8)).image (π g)

theorem exists_points (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c} (cl : Classes co) :
    Nonempty (Points u) := by
  obtain ⟨E, hE⟩ := exists_pairs H cl
  have hT : ∀ g : G, ∃! σ : Equiv.Perm (Fin 8), ∀ s : {s : Finset (Fin 8) // s.card = 2},
      (ae8d_F E g s : Finset (Fin 8)) = (s : Finset (Fin 8)).image σ := fun g =>
    T8_exists_perm (ae8d_F E g) (ae8d_F_meet E hE g)
  choose π hπ using fun g => (hT g).exists
  have huniq : ∀ g : G, ∀ σ : Equiv.Perm (Fin 8),
      (∀ s : {s : Finset (Fin 8) // s.card = 2},
        (ae8d_F E g s : Finset (Fin 8)) = (s : Finset (Fin 8)).image σ) → σ = π g :=
    fun g σ hσ => (hT g).unique hσ (hπ g)
  have hmul : ∀ g h : G, π (g * h) = π g * π h := by
    intro g h
    symm
    refine huniq (g * h) _ fun s => ?_
    rw [ae8d_F_mul, hπ g, hπ h, Finset.image_image]
    rfl
  have hone : π 1 = 1 := by
    refine (huniq 1 1 fun s => ?_).symm
    rw [ae8d_F_one, Equiv.Perm.coe_one, Finset.image_id]
  refine ⟨⟨E, MonoidHom.mk' π hmul, hE, fun g x y hy => ?_⟩⟩
  have h1 : ae8d_F E g (E x) = E y := by
    rw [ae8d_F_apply, E.symm_apply_apply]
    congr 1
    exact Subtype.ext (by rw [ae8d_cg_val, hy])
  rw [← h1]
  exact hπ g (E x)

theorem ae8d_delta_mem_zGroup {c : Chart Ω u} {co : Coords c} (cl : Classes co) {x : G}
    (hx : x ∈ Delta u) : x ∈ zGroup Ω := by
  obtain ⟨h, -⟩ := (cl.u_class x).mp hx
  exact h

theorem ae8d_wt_single (i : Fin 6) : wt (Pi.single i (1 : ZMod 2) : Fin 6 → ZMod 2) = 1 := by
  revert i
  decide

theorem ae8d_zGroup_le_closure {c : Chart Ω u} {co : Coords c} (cl : Classes co) :
    zGroup Ω ≤ Subgroup.closure (Delta u) := by
  let f : Multiplicative (Fin 6 → ZMod 2) →* G :=
    (zGroup Ω).subtype.comp co.e.symm.toMonoidHom
  have hδ : ∀ v : Fin 6 → ZMod 2, (wt v = 1 ∨ wt v = 2) →
      f (Multiplicative.ofAdd v) ∈ Subgroup.closure (Delta u) := by
    intro v hv
    apply Subgroup.subset_closure
    have hval : (co.e ⟨(co.e.symm (Multiplicative.ofAdd v) : G),
        (co.e.symm (Multiplicative.ofAdd v)).2⟩).toAdd = v := by
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    refine (cl.u_class (f (Multiplicative.ofAdd v))).mpr
      ⟨(co.e.symm (Multiplicative.ofAdd v)).2, ?_⟩
    show wt (co.e ⟨(co.e.symm (Multiplicative.ofAdd v) : G),
        (co.e.symm (Multiplicative.ofAdd v)).2⟩).toAdd = 1 ∨
      wt (co.e ⟨(co.e.symm (Multiplicative.ofAdd v) : G),
        (co.e.symm (Multiplicative.ofAdd v)).2⟩).toAdd = 2 ∨
      wt (co.e ⟨(co.e.symm (Multiplicative.ofAdd v) : G),
        (co.e.symm (Multiplicative.ofAdd v)).2⟩).toAdd = 5 ∨
      wt (co.e ⟨(co.e.symm (Multiplicative.ofAdd v) : G),
        (co.e.symm (Multiplicative.ofAdd v)).2⟩).toAdd = 6
    rw [hval]
    rcases hv with h | h <;> simp [h]
  have hT : (Subgroup.closure (Delta u)).comap f = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hsplit : v = ∏ i, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd v i)) := by
      rw [← ofAdd_sum, Finset.univ_sum_single, ofAdd_toAdd]
    rw [hsplit]
    refine Subgroup.prod_mem _ fun i _ => ?_
    show f (Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd v i))) ∈
      Subgroup.closure (Delta u)
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (Multiplicative.toAdd v i) with h | h
    · rw [h]
      simp
    · rw [h]
      exact hδ _ (Or.inl (ae8d_wt_single i))
  intro d hd
  have h2 : Multiplicative.ofAdd (co.e ⟨d, hd⟩).toAdd ∈ (Subgroup.closure (Delta u)).comap f := by
    rw [hT]
    exact Subgroup.mem_top _
  have h1 : f (Multiplicative.ofAdd (co.e ⟨d, hd⟩).toAdd) = d := by
    simp [f]
  rw [Subgroup.mem_comap, h1] at h2
  exact h2

@[expose] def ae8d_dv (a b : Fin 6) : Fin 6 → ZMod 2 := Pi.single a 1 + Pi.single b 1

theorem ae8d_dv_add : ∀ a b b' : Fin 6, ae8d_dv a b + ae8d_dv a b' = ae8d_dv b b' := by
  decide

theorem ae8d_pair_eq : ∀ a b a' b' : Fin 6, a ≠ b → a' ≠ b' → ae8d_dv a b = ae8d_dv a' b' →
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  decide

theorem ae8d_card_ne : ∀ a : Fin 6, (Finset.univ.filter fun b : Fin 6 => b ≠ a).card = 5 := by
  decide

theorem ae8d_three_points : ∀ a : Fin 6, ∃ b b' : Fin 6, b ≠ a ∧ b' ≠ a ∧ b ≠ b' := by
  decide

theorem ae8d_perm_dv (σ : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    (fun i => ae8d_dv a b (σ.symm i)) = ae8d_dv (σ a) (σ b) := by
  funext i
  simp only [ae8d_dv, Pi.add_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem ae8d_delta_of_wt {c : Chart Ω u} {co : Coords c} (cl : Classes co) (v : Fin 6 → ZMod 2)
    (hv : wt v = 1 ∨ wt v = 2) :
    ((co.e.symm (Multiplicative.ofAdd v) : ↥(zGroup Ω)) : G) ∈ Delta u := by
  refine (cl.u_class _).mpr ⟨(co.e.symm (Multiplicative.ofAdd v)).2, ?_⟩
  have hval : (co.e ⟨((co.e.symm (Multiplicative.ofAdd v) : ↥(zGroup Ω)) : G),
      (co.e.symm (Multiplicative.ofAdd v)).2⟩).toAdd = v := by
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  rw [hval]
  rcases hv with h | h <;> simp [h]

namespace Points

variable {c : Chart Ω u} {co : Coords c}

@[expose] def ae8d_dl (cl : Classes co) (a b : Fin 6) (h : a ≠ b) : ↥(Delta u) :=
  ⟨((co.e.symm (Multiplicative.ofAdd (ae8d_dv a b)) : ↥(zGroup Ω)) : G),
    ae8d_delta_of_wt cl (ae8d_dv a b) (Or.inr (by
      revert a b
      decide))⟩

end Points


theorem ae8d_dv_comm (a b : Fin 6) : ae8d_dv a b = ae8d_dv b a := by
  unfold ae8d_dv
  exact add_comm _ _

theorem ae8d_wt_dv : ∀ a b : Fin 6, a ≠ b → wt (ae8d_dv a b) = 2 := by
  decide

theorem ae8d_two_points {p : Fin 6 → Fin 8} (hp : Function.Injective p) :
    ∃ q₁ q₂ : Fin 8, q₁ ≠ q₂ ∧ ∀ j : Fin 8, j ∉ Set.range p ↔ (j = q₁ ∨ j = q₂) := by
  classical
  set T : Finset (Fin 8) := Finset.univ \ Finset.univ.image p with hT
  have hcard : T.card = 2 := by
    rw [hT, Finset.card_sdiff, Finset.inter_univ, Finset.card_image_of_injective _ hp]
    simp
  obtain ⟨q₁, q₂, hq, hTeq⟩ := Finset.card_eq_two.mp hcard
  refine ⟨q₁, q₂, hq, fun j => ?_⟩
  have hmem : j ∈ T ↔ j ∉ Set.range p := by
    simp [hT, Set.mem_range]
  rw [← hmem, hTeq]
  simp

theorem ae8d_swap_mul {q₁ q₂ : Fin 8} (hq : q₁ ≠ q₂) {ρ ρ' : Equiv.Perm (Fin 8)}
    (h1 : ρ q₁ = q₁ ∨ ρ q₁ = q₂) (h2 : ρ q₂ = q₁ ∨ ρ q₂ = q₂)
    (h1' : ρ' q₁ = q₁ ∨ ρ' q₁ = q₂) (h2' : ρ' q₂ = q₁ ∨ ρ' q₂ = q₂) :
    (if (ρ * ρ') q₁ = q₂ then (1 : ZMod 2) else 0) =
      (if ρ q₁ = q₂ then 1 else 0) + (if ρ' q₁ = q₂ then 1 else 0) := by
  have hr : ρ q₁ ≠ ρ q₂ := fun h => hq (ρ.injective h)
  have hr' : ρ' q₁ ≠ ρ' q₂ := fun h => hq (ρ'.injective h)
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [Equiv.Perm.mul_apply]
  rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;>
    rcases h1' with e1' | e1' <;> rcases h2' with e2' | e2' <;>
    simp_all

theorem ae8d_S_eq_pair {x y : Fin 8} (hxy : x ≠ y) (t : {s : Finset (Fin 8) // s.card = 2})
    (hx : x ∈ (t : Finset (Fin 8))) (hy : y ∈ (t : Finset (Fin 8))) :
    (t : Finset (Fin 8)) = {x, y} :=
  ae8d_eq_pair hxy t.2 hx hy

namespace Points

variable {c : Chart Ω u} {co : Coords c}

theorem ae8d_dl_val (cl : Classes co) {a b : Fin 6} (h : a ≠ b) :
    ((ae8d_dl cl a b h : ↥(Delta u)) : G) =
      ((co.e.symm (Multiplicative.ofAdd (ae8d_dv a b)) : ↥(zGroup Ω)) : G) :=
  rfl

theorem ae8d_dl_mul (cl : Classes co) {a b b' : Fin 6} (hab : a ≠ b) (hab' : a ≠ b')
    (hbb' : b ≠ b') :
    ((ae8d_dl cl a b hab : ↥(Delta u)) : G) * ((ae8d_dl cl a b' hab' : ↥(Delta u)) : G) ∈
      Delta u := by
  have h : ((ae8d_dl cl a b hab : ↥(Delta u)) : G) * ((ae8d_dl cl a b' hab' : ↥(Delta u)) : G) =
      ((co.e.symm (Multiplicative.ofAdd (ae8d_dv b b')) : ↥(zGroup Ω)) : G) := by
    rw [ae8d_dl_val, ae8d_dl_val, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, ae8d_dv_add]
  rw [h]
  exact ae8d_delta_of_wt cl (ae8d_dv b b') (Or.inr (ae8d_wt_dv b b' hbb'))

theorem ae8d_dl_inj (cl : Classes co) {a b a' b' : Fin 6} (hab : a ≠ b) (hab' : a' ≠ b')
    (h : ae8d_dl cl a b hab = ae8d_dl cl a' b' hab') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  have h2 := congrArg Subtype.val h
  rw [ae8d_dl_val, ae8d_dl_val] at h2
  have h3 : co.e.symm (Multiplicative.ofAdd (ae8d_dv a b)) =
      co.e.symm (Multiplicative.ofAdd (ae8d_dv a' b')) := Subtype.ext h2
  have h4 := congrArg co.e h3
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h4
  have h5 := congrArg Multiplicative.toAdd h4
  rw [toAdd_ofAdd, toAdd_ofAdd] at h5
  exact ae8d_pair_eq a b a' b' hab hab' h5

@[expose] def ae8d_S (cl : Classes co) (pt : Points u) (a b : Fin 6) :
    {s : Finset (Fin 8) // s.card = 2} :=
  if h : a ≠ b then pt.E (ae8d_dl cl a b h) else ⟨{0, 1}, by decide⟩

theorem ae8d_S_ne (cl : Classes co) (pt : Points u) {a b : Fin 6} (h : a ≠ b) :
    ae8d_S cl pt a b = pt.E (ae8d_dl cl a b h) :=
  dif_pos h

theorem ae8d_S_inj (cl : Classes co) (pt : Points u) {a b a' b' : Fin 6} (hab : a ≠ b)
    (hab' : a' ≠ b') (h : ae8d_S cl pt a b = ae8d_S cl pt a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  rw [ae8d_S_ne cl pt hab, ae8d_S_ne cl pt hab'] at h
  exact ae8d_dl_inj cl hab hab' (pt.E.injective h)

theorem ae8d_center (cl : Classes co) (pt : Points u) (a : Fin 6) :
    ∃ p : Fin 8, ∀ b : Fin 6, b ≠ a → p ∈ (ae8d_S cl pt a b : Finset (Fin 8)) := by
  classical
  set F : Finset {s : Finset (Fin 8) // s.card = 2} :=
    (Finset.univ.filter fun b : Fin 6 => b ≠ a).image (fun b => ae8d_S cl pt a b) with hFdef
  have hF : ∀ s ∈ F, ∀ t ∈ F, ((s : Finset (Fin 8)) ∩ (t : Finset (Fin 8))).Nonempty := by
    intro s hs t ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_filter] at hb hb'
    by_cases hbb : b = b'
    · subst hbb
      rw [Finset.inter_self]
      exact Finset.card_pos.mp (by rw [(ae8d_S cl pt a b).2]; norm_num)
    · have hab : a ≠ b := hb.2.symm
      have hab' : a ≠ b' := hb'.2.symm
      have hne : ae8d_dl cl a b hab ≠ ae8d_dl cl a b' hab' := fun h => by
        rcases ae8d_dl_inj cl hab hab' h with h1 | h1
        · exact hbb h1.2
        · exact hb.2 h1.2
      have hmul := ae8d_dl_mul cl hab hab' hbb
      have hm := (pt.adj _ _).mp ⟨hne, hmul⟩
      rw [ae8d_S_ne cl pt hab, ae8d_S_ne cl pt hab']
      exact hm.2
  have h4 : 4 ≤ F.card := by
    have hcard : F.card = 5 := by
      rw [hFdef, Finset.card_image_of_injOn, ← ae8d_card_ne a]
      intro b hb b' hb' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hb hb'
      rcases ae8d_S_inj cl pt hb.symm hb'.symm h with h1 | h1
      · exact h1.2
      · exact absurd h1.2 hb
    omega
  obtain ⟨p, hp⟩ := ae8d_star_of_pairwise F hF h4
  refine ⟨p, fun b hb => hp _
    (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩))⟩

end Points


theorem ae8d_zGroup_conj (H : End18.Hyp Ω) (g : G) {d : G} (hd : d ∈ zGroup Ω) :
    g * d * g⁻¹ ∈ zGroup Ω := by
  have hle : zGroup Ω ≤ (zGroup Ω).comap (MulAut.conj g).toMonoidHom := by
    show Subgroup.closure {z | ∃ L ∈ Ω, IsUniqueInvolution L z} ≤ _
    rw [Subgroup.closure_le]
    rintro z ⟨L, hL, hz⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact Subgroup.subset_closure ⟨conjSub g L, H.endHyp.thmD.hyp.conjInvariant g L hL, hz.conj g⟩
  exact hle hd

namespace Points

variable {c : Chart Ω u} {co : Coords c}

theorem exists_chartLines (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) :
    ∃ ι : Fin 6 ↪ Fin 8, ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      (∀ i : Fin 6, pt.π (y : G) (ι i) = ι ((c.ψ y : AE.Wr 6).perm i)) ∧
      ∀ j : Fin 8, j ∉ Set.range ι → pt.π (y : G) j = j := by
  choose p hp using ae8d_center cl pt
  have hmem : ∀ a b : Fin 6, a ≠ b → p a ∈ (ae8d_S cl pt a b : Finset (Fin 8)) ∧
      p b ∈ (ae8d_S cl pt a b : Finset (Fin 8)) := by
    intro a b hab
    refine ⟨hp a b hab.symm, ?_⟩
    have hsymm : ae8d_S cl pt a b = ae8d_S cl pt b a := by
      rw [ae8d_S_ne cl pt hab, ae8d_S_ne cl pt hab.symm]
      congr 1
      apply Subtype.ext
      rw [ae8d_dl_val, ae8d_dl_val, ae8d_dv_comm a b]
    rw [hsymm]
    exact hp b a hab
  have hpinj : Function.Injective p :=
    ae8d_inj_of_stars p (fun a b => ae8d_S cl pt a b)
      (fun a b a' b' hab hab' h => ae8d_S_inj cl pt hab hab' h) hmem
  have hstep : ∀ y : ↥(pSpan (Generic.centMembers Ω u)), ∀ a : Fin 6,
      pt.π (y : G) (p a) = p ((c.ψ y : AE.Wr 6).perm a) := by
    intro y
    set σ : Equiv.Perm (Fin 6) := (c.ψ y : AE.Wr 6).perm with hσdef
    have hpair : ∀ a b : Fin 6, ∀ hab : a ≠ b,
        ((ae8d_S cl pt (σ a) (σ b) : {s : Finset (Fin 8) // s.card = 2}) : Finset (Fin 8)) =
          ((ae8d_S cl pt a b : {s : Finset (Fin 8) // s.card = 2}) : Finset (Fin 8)).image
            (pt.π (y : G)) := by
      intro a b hab
      have hab' : σ a ≠ σ b := fun h => hab (σ.injective h)
      set dZ : ↥(zGroup Ω) := co.e.symm (Multiplicative.ofAdd (ae8d_dv a b)) with hdZ
      set dZ' : ↥(zGroup Ω) := ⟨(y : G) * (dZ : G) * (y : G)⁻¹, ae8d_zGroup_conj H _ dZ.2⟩
        with hdZ'
      have h0 : (co.e dZ).toAdd = ae8d_dv a b := by
        rw [hdZ, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      have hdv : (co.e dZ').toAdd = ae8d_dv (σ a) (σ b) := by
        rw [co.act y dZ dZ' rfl, h0, ae8d_perm_dv]
      have hval : co.e dZ' = Multiplicative.ofAdd (ae8d_dv (σ a) (σ b)) := by
        rw [← hdv, ofAdd_toAdd]
      have hdZ'' : dZ' = co.e.symm (Multiplicative.ofAdd (ae8d_dv (σ a) (σ b))) :=
        (co.e.eq_symm_apply).mpr hval
      have hy' : ((ae8d_dl cl (σ a) (σ b) hab' : ↥(Delta u)) : G) =
          (y : G) * ((ae8d_dl cl a b hab : ↥(Delta u)) : G) * (y : G)⁻¹ := by
        rw [ae8d_dl_val, ae8d_dl_val, ← hdZ'']
      have h2 := pt.equivariant (y : G) (ae8d_dl cl a b hab) (ae8d_dl cl (σ a) (σ b) hab') hy'
      rw [ae8d_S_ne cl pt hab', ae8d_S_ne cl pt hab]
      exact h2
    intro a
    obtain ⟨b, b', hb, hb', hbb'⟩ := ae8d_three_points a
    have hab1 : σ a ≠ σ b := fun h => hb (σ.injective h).symm
    have hab2 : σ a ≠ σ b' := fun h => hb' (σ.injective h).symm
    have h1 : pt.π (y : G) (p a) ∈ (ae8d_S cl pt (σ a) (σ b) : Finset (Fin 8)) := by
      rw [hpair a b hb.symm]
      exact Finset.mem_image_of_mem _ (hmem a b hb.symm).1
    have h2 : pt.π (y : G) (p a) ∈ (ae8d_S cl pt (σ a) (σ b') : Finset (Fin 8)) := by
      rw [hpair a b' hb'.symm]
      exact Finset.mem_image_of_mem _ (hmem a b' hb'.symm).1
    have hS1 : ((ae8d_S cl pt (σ a) (σ b) : {s : Finset (Fin 8) // s.card = 2}) :
        Finset (Fin 8)) = {p (σ a), p (σ b)} :=
      ae8d_S_eq_pair (hpinj.ne hab1) _ (hmem (σ a) (σ b) hab1).1 (hmem (σ a) (σ b) hab1).2
    have hS2 : ((ae8d_S cl pt (σ a) (σ b') : {s : Finset (Fin 8) // s.card = 2}) :
        Finset (Fin 8)) = {p (σ a), p (σ b')} :=
      ae8d_S_eq_pair (hpinj.ne hab2) _ (hmem (σ a) (σ b') hab2).1 (hmem (σ a) (σ b') hab2).2
    rw [hS1, Finset.mem_insert, Finset.mem_singleton] at h1
    rw [hS2, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      rcases h2 with h2 | h2
      · exact hb (σ.injective (hpinj (h1.symm.trans h2)))
      · exact hbb' (σ.injective (hpinj (h1.symm.trans h2)))
  have hcomp : ∀ y : ↥(pSpan (Generic.centMembers Ω u)), ∀ j : Fin 8,
      j ∉ Set.range p → pt.π (y : G) j ∉ Set.range p := by
    intro y j hj hρj
    obtain ⟨a, ha⟩ := hρj
    apply hj
    have h1 := hstep y ((c.ψ y : AE.Wr 6).perm.symm a)
    rw [Equiv.apply_symm_apply] at h1
    exact ⟨(c.ψ y : AE.Wr 6).perm.symm a, (pt.π (y : G)).injective (h1.trans ha)⟩
  obtain ⟨q₁, q₂, hq, hcq⟩ := ae8d_two_points hpinj
  have hq1 : q₁ ∉ Set.range p := (hcq q₁).mpr (Or.inl rfl)
  have hq2 : q₂ ∉ Set.range p := (hcq q₂).mpr (Or.inr rfl)
  have hpres : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      (pt.π (y : G) q₁ = q₁ ∨ pt.π (y : G) q₁ = q₂) ∧
        (pt.π (y : G) q₂ = q₁ ∨ pt.π (y : G) q₂ = q₂) :=
    fun y => ⟨(hcq _).mp (hcomp y q₁ hq1), (hcq _).mp (hcomp y q₂ hq2)⟩
  let chi : ↥(pSpan (Generic.centMembers Ω u)) →* Multiplicative (ZMod 2) :=
    MonoidHom.mk'
      (fun y => Multiplicative.ofAdd (if pt.π (y : G) q₁ = q₂ then (1 : ZMod 2) else 0))
      (fun y y' => by
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
        rw [← ofAdd_add, Subgroup.coe_mul, map_mul]
        congr 1
        exact ae8d_swap_mul hq (hpres y).1 (hpres y).2 (hpres y').1 (hpres y').2)
  have hfix : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      pt.π (y : G) q₁ = q₁ ∧ pt.π (y : G) q₂ = q₂ := by
    intro y
    have h := ae8d_trivial_of_perfect c.perfect chi y
    change Multiplicative.ofAdd (if pt.π (y : G) q₁ = q₂ then (1 : ZMod 2) else 0) = 1 at h
    have h' : (if pt.π (y : G) q₁ = q₂ then (1 : ZMod 2) else 0) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    have hne : pt.π (y : G) q₁ ≠ q₂ := fun h2 => by simp [h2] at h'
    have h1 : pt.π (y : G) q₁ = q₁ := (hpres y).1.resolve_right hne
    have h2 : pt.π (y : G) q₂ = q₂ := by
      rcases (hpres y).2 with h2 | h2
      · exact absurd ((pt.π (y : G)).injective (h2.trans h1.symm)).symm hq
      · exact h2
    exact ⟨h1, h2⟩
  refine ⟨⟨p, hpinj⟩, fun y => ⟨fun i => hstep y i, fun j hj => ?_⟩⟩
  rcases (hcq j).mp hj with rfl | rfl
  · exact (hfix y).1
  · exact (hfix y).2

end Points


namespace Points

variable {c : Chart Ω u} {co : Coords c}

theorem range_eq (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) :
    pt.π.range = alternatingGroup (Fin 8) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    let χ : G →* ℤˣ := (Equiv.Perm.sign : Equiv.Perm (Fin 8) →* ℤˣ).comp pt.π
    have hY : ∀ y : ↥(pSpan (Generic.centMembers Ω u)), χ (y : G) = 1 := by
      intro y
      have h := ae8d_trivial_of_perfect c.perfect
        (χ.comp (pSpan (Generic.centMembers Ω u)).subtype) y
      exact h
    obtain ⟨L₀, hL₀, -⟩ := c.label_surj ({0, 1, 2, 3} : Finset (Fin 6)) (by decide) true
    have hL₀Ω : L₀ ∈ Ω := (Generic.mem_centMembers.mp hL₀).1
    have hΩK : ∀ L ∈ Ω, L ≤ χ.ker := by
      intro L hL x hx
      obtain ⟨k, hk⟩ := H.endHyp.thmD.trans L₀ hL₀Ω L hL
      rw [← hk, mem_conjSub_iff] at hx
      have hx0 : k⁻¹ * x * k ∈ pSpan (Generic.centMembers Ω u) :=
        le_pSpan hL₀ hx
      have hxk : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      rw [MonoidHom.mem_ker, hxk, map_mul, map_mul, map_inv,
        show χ (k⁻¹ * x * k) = 1 from hY ⟨_, hx0⟩, mul_one, mul_inv_cancel]
    have htop : (⊤ : Subgroup G) ≤ χ.ker := by
      rw [← H.endHyp.thmD.gen]
      exact pSpan_le hΩK
    exact (MonoidHom.mem_ker.mp (htop (Subgroup.mem_top g)))
  ·
    have hK : ∀ s t : {s : Finset (Fin 8) // s.card = 2}, ∃ g ∈ pt.π.range,
        (s : Finset (Fin 8)).image g = (t : Finset (Fin 8)) := by
      intro s t
      obtain ⟨x, rfl⟩ := pt.E.surjective s
      obtain ⟨x', rfl⟩ := pt.E.surjective t
      obtain ⟨h, hh⟩ := x.2
      obtain ⟨k, hk⟩ := x'.2
      refine ⟨pt.π (k * h⁻¹), MonoidHom.mem_range.mpr ⟨k * h⁻¹, rfl⟩, ?_⟩
      have hyeq : (x' : G) = (k * h⁻¹) * (x : G) * (k * h⁻¹)⁻¹ := by
        rw [hk, hh]
        group
      exact (pt.equivariant (k * h⁻¹) x x' hyeq).symm
    have hprim := ae8d_isPreprimitive pt.π.range hK
    set τ : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2 with hτdef
    have hτ : τ.IsThreeCycle := card_support_eq_three_iff.mp (by decide)
    have hbτ : AE.Wr.ofPerm τ ∈ AE.aeSub 6 := by
      rw [AE.mem_aeSub]
      refine ⟨?_, hτ.sign⟩
      simp [AE.Wr.wsum, AE.Wr.ofPerm]
    set y : ↥(pSpan (Generic.centMembers Ω u)) := c.ψ.symm ⟨AE.Wr.ofPerm τ, hbτ⟩ with hy
    have hperm : (c.ψ y : AE.Wr 6).perm = τ := by
      rw [hy, MulEquiv.apply_symm_apply]
      rfl
    obtain ⟨ι, hι⟩ := exists_chartLines H cl pt
    have hcyc := hι y
    have h1 : ∀ i : Fin 6, pt.π (y : G) (ι i) = ι (τ i) := fun i => by
      rw [← hperm]
      exact hcyc.1 i
    have h3 : (pt.π (y : G)).IsThreeCycle :=
      ae8d_isThreeCycle_of_extend ι τ hτ (pt.π (y : G)) h1 hcyc.2
    exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3
      (MonoidHom.mem_range.mpr ⟨y, rfl⟩)


end Points

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
