module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section SetStab

variable {α : Type*}

@[expose] def permSetStab (S : Set α) : Subgroup (Perm α) where
  carrier := {g | ∀ x, g x ∈ S ↔ x ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [perm_apply_inv_apply] at h
    exact h.symm

theorem mem_permSetStab {S : Set α} {g : Perm α} :
    g ∈ permSetStab S ↔ ∀ x, g x ∈ S ↔ x ∈ S :=
  Iff.rfl

@[expose] def restrictSet (S : Set α) : ↥(permSetStab S) →* Perm S where
  toFun g := (g : Perm α).subtypePerm g.2
  map_one' := rfl
  map_mul' _ _ := rfl

end SetStab

variable {m n : ℕ}

@[expose] noncomputable def restrictPerm (ι : Fin m ↪ Fin n) :
    ↥(permSetStab (Set.range ι)) →* Perm (Fin m) :=
  (Equiv.ofInjective ι ι.injective).symm.permCongrHom.toMonoidHom.comp (restrictSet (Set.range ι))

theorem restrictPerm_apply_apply (ι : Fin m ↪ Fin n) (g : ↥(permSetStab (Set.range ι)))
    (i : Fin m) : ι (restrictPerm ι g i) = (g : Perm (Fin n)) (ι i) := by
  change ι ((Equiv.ofInjective ι ι.injective).symm
    ((restrictSet (Set.range ι) g) ((Equiv.ofInjective ι ι.injective) i))) = _
  rw [Equiv.apply_ofInjective_symm ι.injective]
  rfl

theorem altLift_mem_permSetStab (ι : Fin m ↪ Fin n) (σ : alternatingGroup (Fin m)) :
    (altLift ι σ : Perm (Fin n)) ∈ permSetStab (Set.range ι) := by
  intro x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [altLift_apply_apply]
    exact ⟨fun _ => ⟨i, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  · rw [altLift_apply_of_notMem ι σ hx]

theorem mem_permSetStab_of_apply_eq {ι : Fin m ↪ Fin n} {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) {g : Perm (Fin n)} (hg : g ω = ω) :
    g ∈ permSetStab (Set.range ι) := by
  intro x
  rw [hι, hι]
  constructor
  · rintro h rfl
    exact h hg
  · intro h hgx
    exact h (g.injective (hgx.trans hg.symm))

theorem mem_permSetStab_of_pair {ι : Fin m ↪ Fin n} {p q : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) {g : Perm (Fin n)}
    (hg : g p = p ∧ g q = q ∨ g p = q ∧ g q = p) : g ∈ permSetStab (Set.range ι) := by
  intro x
  rw [hι, hι]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · subst hx
      rcases hg with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact h1 h3
      · exact h2 h3
    · subst hx
      rcases hg with ⟨-, h3⟩ | ⟨-, h3⟩
      · exact h2 h3
      · exact h1 h3
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases hg with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact h1 (g.injective (hx.trans h3.symm))
      · exact h2 (g.injective (hx.trans h4.symm))
    · rcases hg with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact h2 (g.injective (hx.trans h4.symm))
      · exact h1 (g.injective (hx.trans h3.symm))

theorem eq_one_of_apply_eq_of_range_ne {ι : Fin m ↪ Fin n} {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) {g : Perm (Fin n)} (hg : g ∈ permSetStab (Set.range ι))
    (hfix : ∀ i, g (ι i) = ι i) : g = 1 := by
  refine Equiv.ext fun x => ?_
  rw [Perm.one_apply]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [hfix]
  · have hgx : g x ∉ Set.range ι := fun h => hx ((hg x).1 h)
    rw [hι, not_not] at hx hgx
    rw [hgx, hx]

theorem apply_eq_or_eq_of_range_ne_ne {ι : Fin m ↪ Fin n} {p q : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) {g : Perm (Fin n)}
    (hg : g ∈ permSetStab (Set.range ι)) {x : Fin n} (hx : x = p ∨ x = q) : g x = p ∨ g x = q := by
  have hxR : x ∉ Set.range ι := fun h => by
    rcases hx with rfl | rfl
    · exact ((hι _).1 h).1 rfl
    · exact ((hι _).1 h).2 rfl
  have hgx : g x ∉ Set.range ι := fun h => hxR ((hg x).1 h)
  rw [hι, not_and_or, not_not, not_not] at hgx
  exact hgx

theorem eq_one_or_eq_swap_of_range_ne_ne {ι : Fin m ↪ Fin n} {p q : Fin n} (hpq : p ≠ q)
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) {g : Perm (Fin n)}
    (hg : g ∈ permSetStab (Set.range ι)) (hfix : ∀ i, g (ι i) = ι i) :
    g = 1 ∨ g = swap p q := by
  have hin : ∀ x, x ∈ Set.range ι → g x = x := fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact hfix i
  rcases apply_eq_or_eq_of_range_ne_ne hι hg (Or.inl rfl) with hp | hp
  · have hq : g q = q := by
      rcases apply_eq_or_eq_of_range_ne_ne hι hg (Or.inr rfl) with hq | hq
      · exact absurd (g.injective (hq.trans hp.symm)) (Ne.symm hpq)
      · exact hq
    left
    refine Equiv.ext fun x => ?_
    rw [Perm.one_apply]
    by_cases hx : x ∈ Set.range ι
    · exact hin x hx
    · rw [hι, not_and_or, not_not, not_not] at hx
      rcases hx with rfl | rfl
      · exact hp
      · exact hq
  · have hq : g q = p := by
      rcases apply_eq_or_eq_of_range_ne_ne hι hg (Or.inr rfl) with hq | hq
      · exact hq
      · exact absurd (g.injective (hq.trans hp.symm)) (Ne.symm hpq)
    right
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ Set.range ι
    · have hxp : x ≠ p := ((hι x).1 hx).1
      have hxq : x ≠ q := ((hι x).1 hx).2
      rw [hin x hx, swap_apply_of_ne_of_ne hxp hxq]
    · rw [hι, not_and_or, not_not, not_not] at hx
      rcases hx with rfl | rfl
      · rw [hp, swap_apply_left]
      · rw [hq, swap_apply_right]

theorem swap_mem_permSetStab {ι : Fin m ↪ Fin n} {p q : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) : swap p q ∈ permSetStab (Set.range ι) :=
  mem_permSetStab_of_pair hι (Or.inr ⟨swap_apply_left p q, swap_apply_right p q⟩)

theorem mul_swap_eq_swap_mul {ι : Fin m ↪ Fin n} {p q : Fin n} (hpq : p ≠ q)
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) {g : Perm (Fin n)}
    (hg : g ∈ permSetStab (Set.range ι)) : g * swap p q = swap p q * g := by
  have h1 : swap (g p) (g q) = swap p q := by
    rcases apply_eq_or_eq_of_range_ne_ne hι hg (Or.inl rfl) with hp | hp <;>
      rcases apply_eq_or_eq_of_range_ne_ne hι hg (Or.inr rfl) with hq | hq
    · exact absurd (g.injective (hp.trans hq.symm)) hpq
    · rw [hp, hq]
    · rw [hp, hq, swap_comm]
    · exact absurd (g.injective (hp.trans hq.symm)) hpq
  have h2 := swap_apply_apply g p q
  rw [h1] at h2
  calc g * swap p q = g * swap p q * g⁻¹ * g := by group
    _ = swap p q * g := by rw [← h2]

theorem eq_one_of_apply_eq_of_range_ne_ne {ι : Fin m ↪ Fin n} {p q : Fin n} (hpq : p ≠ q)
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) {g : Perm (Fin n)}
    (hg : g ∈ permSetStab (Set.range ι)) (hgA : g ∈ alternatingGroup (Fin n))
    (hfix : ∀ i, g (ι i) = ι i) : g = 1 := by
  have hout : ∀ x, x ∉ Set.range ι → g x = p ∨ g x = q := fun x hx => by
    have hgx : g x ∉ Set.range ι := fun h => hx ((hg x).1 h)
    rw [hι, not_and_or, not_not, not_not] at hgx
    exact hgx
  have hpR : p ∉ Set.range ι := fun h => ((hι p).1 h).1 rfl
  have hqR : q ∉ Set.range ι := fun h => ((hι q).1 h).2 rfl
  have hin : ∀ x, x ∈ Set.range ι → g x = x := fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact hfix i
  rcases hout p hpR with hp | hp
  · have hq : g q = q := by
      rcases hout q hqR with hq | hq
      · exact absurd (g.injective (hq.trans hp.symm)) (Ne.symm hpq)
      · exact hq
    refine Equiv.ext fun x => ?_
    rw [Perm.one_apply]
    by_cases hx : x ∈ Set.range ι
    · exact hin x hx
    · rw [hι, not_and_or, not_not, not_not] at hx
      rcases hx with rfl | rfl
      · exact hp
      · exact hq
  · exfalso
    have hq : g q = p := by
      rcases hout q hqR with hq | hq
      · exact hq
      · exact absurd (g.injective (hq.trans hp.symm)) (Ne.symm hpq)
    have hsw : g = swap p q := by
      refine Equiv.ext fun x => ?_
      by_cases hx : x ∈ Set.range ι
      · have hxp : x ≠ p := ((hι x).1 hx).1
        have hxq : x ≠ q := ((hι x).1 hx).2
        rw [hin x hx, swap_apply_of_ne_of_ne hxp hxq]
      · rw [hι, not_and_or, not_not, not_not] at hx
        rcases hx with rfl | rfl
        · rw [hp, swap_apply_left]
        · rw [hq, swap_apply_right]
    rw [hsw, mem_alternatingGroup, sign_swap hpq] at hgA
    exact absurd hgA (by decide)

theorem exists_embedding_range_compl (s : Finset (Fin n)) (hm : m + s.card = n) :
    ∃ ι : Fin m ↪ Fin n, ∀ x, x ∈ Set.range ι ↔ x ∉ s := by
  classical
  have hcard : Fintype.card (sᶜ : Finset (Fin n)) = m := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  set e := Fintype.equivFinOfCardEq hcard
  refine ⟨e.symm.toEmbedding.trans (Function.Embedding.subtype _), fun x => ?_⟩
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.mem_compl.1 (e.symm i).2
  · intro hx
    exact ⟨e ⟨x, Finset.mem_compl.2 hx⟩, by simp⟩

theorem exists_embedding_range_ne (hmn : m + 1 = n) (ω : Fin n) :
    ∃ ι : Fin m ↪ Fin n, ∀ x, x ∈ Set.range ι ↔ x ≠ ω := by
  obtain ⟨ι, hι⟩ := exists_embedding_range_compl {ω} (by rw [Finset.card_singleton]; exact hmn)
  exact ⟨ι, fun x => (hι x).trans (by rw [Finset.mem_singleton])⟩

theorem exists_embedding_range_ne_ne (hmn : m + 2 = n) {p q : Fin n} (hpq : p ≠ q) :
    ∃ ι : Fin m ↪ Fin n, ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q := by
  classical
  obtain ⟨ι, hι⟩ := exists_embedding_range_compl {p, q}
    (by rw [Finset.card_pair hpq]; exact hmn)
  refine ⟨ι, fun x => (hι x).trans ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]

section Pre

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin n)}
  {S T : Subgroup (Perm (Fin n))}

@[expose] def preSub (ψ : ↥H →* Perm (Fin n)) (S : Subgroup (Perm (Fin n))) :
    Subgroup (MulAut V) :=
  (S.comap ψ).map H.subtype

theorem mem_preSub {x : MulAut V} : x ∈ preSub ψ S ↔ ∃ hx : x ∈ H, ψ ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hx, hψ⟩
    exact ⟨⟨x, hx⟩, hψ, rfl⟩

theorem coe_mem_preSub {x : ↥H} : (x : MulAut V) ∈ preSub ψ S ↔ ψ x ∈ S :=
  mem_preSub.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem preSub_le : preSub ψ S ≤ H :=
  Subgroup.map_subtype_le _

theorem preSub_mono (h : S ≤ T) : preSub ψ S ≤ preSub ψ T :=
  Subgroup.map_mono (Subgroup.comap_mono h)

@[expose] noncomputable def restrictHom (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n)
    (K : Subgroup (MulAut V)) (hK : K ≤ preSub ψ (permSetStab (Set.range ι))) :
    ↥K →* Perm (Fin m) :=
  (restrictPerm ι).comp ((ψ.comp (Subgroup.inclusion (hK.trans preSub_le))).codRestrict _
    fun k => (coe_mem_preSub (ψ := ψ) (x := Subgroup.inclusion (hK.trans preSub_le) k)).1 (hK k.2))

variable {ι : Fin m ↪ Fin n} {K : Subgroup (MulAut V)}
  {hK : K ≤ preSub ψ (permSetStab (Set.range ι))}

theorem restrictHom_apply_apply (k : ↥K) (i : Fin m) :
    ι (restrictHom ψ ι K hK k i) = ψ (Subgroup.inclusion (hK.trans preSub_le) k) (ι i) :=
  restrictPerm_apply_apply ι _ i

theorem restrictHom_eq_iff (k : ↥K) (σ : Perm (Fin m)) :
    restrictHom ψ ι K hK k = σ ↔
      ∀ i, ψ (Subgroup.inclusion (hK.trans preSub_le) k) (ι i) = ι (σ i) := by
  constructor
  · rintro rfl i
    exact (restrictHom_apply_apply k i).symm
  · intro h
    ext i
    exact congrArg Fin.val (ι.injective ((restrictHom_apply_apply k i).trans (h i)))

theorem restrictHom_eq_one_iff (k : ↥K) :
    restrictHom ψ ι K hK k = 1 ↔ ∀ i, ψ (Subgroup.inclusion (hK.trans preSub_le) k) (ι i) = ι i :=
  restrictHom_eq_iff k 1

theorem apply_mem_permSetStab (k : ↥K) :
    ψ (Subgroup.inclusion (hK.trans preSub_le) k) ∈ permSetStab (Set.range ι) :=
  (coe_mem_preSub (ψ := ψ) (x := Subgroup.inclusion (hK.trans preSub_le) k)).1 (hK k.2)

theorem restrictHom_injective (hψ : Function.Injective ψ)
    (h : ∀ k : ↥K, (∀ i, ψ (Subgroup.inclusion (hK.trans preSub_le) k) (ι i) = ι i) →
      ψ (Subgroup.inclusion (hK.trans preSub_le) k) = 1) :
    Function.Injective (restrictHom ψ ι K hK) := by
  refine (injective_iff_map_eq_one _).2 fun k hk => ?_
  have h1 : Subgroup.inclusion (hK.trans preSub_le) k = 1 :=
    hψ ((h k ((restrictHom_eq_one_iff k).1 hk)).trans (map_one ψ).symm)
  exact Subtype.ext (show (k : MulAut V) = 1 from congrArg (fun x : ↥H => (x : MulAut V)) h1)

theorem restrictHom_eq_of_eq_altLift {k : ↥K} {σ : alternatingGroup (Fin m)}
    (h : ψ (Subgroup.inclusion (hK.trans preSub_le) k) = altLift ι σ) :
    restrictHom ψ ι K hK k = σ :=
  (restrictHom_eq_iff k σ).2 fun i => by rw [h, altLift_apply_apply]

theorem exists_restrictHom_eq_altLift (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin n) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ K)
    (σ : alternatingGroup (Fin m)) :
    ∃ k : ↥K, restrictHom ψ ι K hK k = σ ∧
      ∃ hk : (k : MulAut V) ∈ H, ψ ⟨k, hk⟩ = altLift ι σ := by
  obtain ⟨h, hh⟩ := hA (altLift ι σ).2
  have hhK : (h : MulAut V) ∈ K :=
    hKmem h (hh ▸ (altLift ι σ).2) (hh ▸ altLift_mem_permSetStab ι σ)
  refine ⟨⟨h, hhK⟩, restrictHom_eq_of_eq_altLift hh, h.2, hh⟩

theorem alternatingGroup_le_range_restrictHom (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin n) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ K) :
    alternatingGroup (Fin m) ≤ (restrictHom ψ ι K hK).range := fun σ hσ => by
  obtain ⟨k, hk, -⟩ := exists_restrictHom_eq_altLift (hK := hK) hA hKmem ⟨σ, hσ⟩
  exact ⟨k, hk⟩

theorem isFFStarOffender_of_le_of_le {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hAK : A ≤ K) : IsFFStarOffender K A :=
  ⟨hAK, hA.2⟩

end Pre

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
