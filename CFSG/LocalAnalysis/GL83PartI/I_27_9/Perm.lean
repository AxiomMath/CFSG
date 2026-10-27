module

public import CFSG.LocalAnalysis.GL83PartI.I_23_1
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

namespace GL83.PiGen

open Equiv Equiv.Perm MulAction
open GL83 GL83.CompFam

section Basic

variable {Ω : Type*}

@[expose] def fixSet (E : Subgroup (Perm Ω)) : Set Ω := {ω | ∀ e ∈ E, e ω = ω}

theorem mem_fixSet {E : Subgroup (Perm Ω)} {ω : Ω} : ω ∈ fixSet E ↔ ∀ e ∈ E, e ω = ω := Iff.rfl

theorem fixSet_anti {E F : Subgroup (Perm Ω)} (h : E ≤ F) : fixSet F ⊆ fixSet E :=
  fun _ hω e he => hω e (h he)

theorem card_fixSet_modEq {p : ℕ} [Fact p.Prime] [Finite Ω] {E : Subgroup (Perm Ω)}
    (hE : IsPGroup p E) :
    Nat.card Ω ≡ Nat.card (fixSet E) [MOD p] := by
  have h := hE.card_modEq_card_fixedPoints Ω
  have hfix : MulAction.fixedPoints E Ω = fixSet E := by
    ext ω
    simp [MulAction.mem_fixedPoints, fixSet, Subgroup.smul_def, Perm.smul_def]
  rw [hfix] at h
  exact h

@[expose] def stabIn (R : Subgroup (Perm Ω)) (ω : Ω) : Subgroup (Perm Ω) :=
  (stabilizer R ω).map R.subtype

theorem stabIn_le (R : Subgroup (Perm Ω)) (ω : Ω) : stabIn R ω ≤ R := Subgroup.map_subtype_le _

theorem mem_fixSet_stabIn (R : Subgroup (Perm Ω)) (ω : Ω) : ω ∈ fixSet (stabIn R ω) := by
  rintro _ ⟨g, hg, rfl⟩
  have := mem_stabilizer_iff.1 hg
  rwa [Subgroup.smul_def, Perm.smul_def] at this

theorem card_stabIn (R : Subgroup (Perm Ω)) (ω : Ω) :
    Nat.card (stabIn R ω) = Nat.card (stabilizer R ω) :=
  Subgroup.card_map_of_injective R.subtype_injective

theorem card_mul_card_stabIn (R : Subgroup (Perm Ω)) (ω : Ω) :
    Nat.card R = Nat.card (orbit R ω) * Nat.card (stabIn R ω) := by
  rw [card_stabIn, ← Nat.card_prod]
  exact (Nat.card_congr (orbitProdStabilizerEquivGroup R ω)).symm

end Basic

section Double

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def Y2 (p : ℕ) (R : Subgroup (Perm Ω)) : Set (Perm Ω) :=
  {y | y ∈ alternatingGroup Ω ∧ (∃ j : ℕ, y ^ (2 ^ j) = 1) ∧
    ∃ E : Subgroup (Perm Ω), E ≤ R ∧ Nat.card R ≤ p * Nat.card E ∧ ∀ e ∈ E, e * y = y * e}

omit [Fintype Ω] in
theorem swap_mul_swap_comm {a b d e : Ω} (hda : d ≠ a) (hdb : d ≠ b) (hea : e ≠ a)
    (heb : e ≠ b) : swap a b * swap d e = swap d e * swap a b := by
  rw [Equiv.mul_swap_eq_swap_mul, swap_apply_of_ne_of_ne hda hdb, swap_apply_of_ne_of_ne hea heb]

theorem sign_swap_mul_swap {a b d e : Ω} (hab : a ≠ b) (hde : d ≠ e) :
    swap a b * swap d e ∈ alternatingGroup Ω := by
  rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hde]
  rfl

theorem swap_mul_swap_mem_Y2 {p : ℕ} {R E : Subgroup (Perm Ω)} (hER : E ≤ R)
    (hEi : Nat.card R ≤ p * Nat.card E) {a b d e : Ω} (ha : a ∈ fixSet E) (hb : b ∈ fixSet E)
    (hd : d ∈ fixSet E) (he : e ∈ fixSet E) (hab : a ≠ b) (hde : d ≠ e) (hda : d ≠ a)
    (hdb : d ≠ b) (hea : e ≠ a) (heb : e ≠ b) : swap a b * swap d e ∈ Y2 p R := by
  refine ⟨sign_swap_mul_swap hab hde, ⟨1, ?_⟩, E, hER, hEi, fun g hg => ?_⟩
  · have hc := swap_mul_swap_comm hda hdb hea heb
    calc (swap a b * swap d e) ^ (2 ^ 1) = swap a b * swap d e * (swap a b * swap d e) := by
          rw [pow_one, sq]
      _ = swap a b * (swap d e * swap a b) * swap d e := by group
      _ = swap a b * (swap a b * swap d e) * swap d e := by rw [hc]
      _ = 1 := by simp
  · have h1 : Commute g (swap a b) := by
      show g * swap a b = swap a b * g
      rw [Equiv.mul_swap_eq_swap_mul, ha g hg, hb g hg]
    have h2 : Commute g (swap d e) := by
      show g * swap d e = swap d e * g
      rw [Equiv.mul_swap_eq_swap_mul, hd g hg, he g hg]
    exact (h1.mul_right h2).eq

@[expose] def tri (a b c : Ω) : Perm Ω := swap a c * swap a b

theorem tri_mem_closure_Y2 {p : ℕ} {R E : Subgroup (Perm Ω)} (hER : E ≤ R)
    (hEi : Nat.card R ≤ p * Nat.card E) {a b c d e : Ω} (ha : a ∈ fixSet E) (hb : b ∈ fixSet E)
    (hc : c ∈ fixSet E) (hd : d ∈ fixSet E) (he : e ∈ fixSet E) (hab : a ≠ b) (hac : a ≠ c)
    (hde : d ≠ e) (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) (hea : e ≠ a) (heb : e ≠ b)
    (hec : e ≠ c) : tri a b c ∈ Subgroup.closure (Y2 p R) := by
  have h1 : swap a c * swap d e ∈ Y2 p R :=
    swap_mul_swap_mem_Y2 hER hEi ha hc hd he hac hde hda hdc hea hec
  have h2 : swap d e * swap a b ∈ Y2 p R := by
    have := swap_mul_swap_mem_Y2 hER hEi hd he ha hb hde hab (Ne.symm hda) (Ne.symm hea)
      (Ne.symm hdb) (Ne.symm heb)
    exact this
  have : tri a b c = (swap a c * swap d e) * (swap d e * swap a b) := by
    rw [tri, mul_assoc, ← mul_assoc (swap d e) (swap d e), swap_mul_self, one_mul]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure h1) (Subgroup.subset_closure h2)

theorem eq_one_of_mem_altOn_of_apply {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {g : Perm Ω} (hg : g ∈ altOn ({a, b, c} : Set Ω)) (hga : g a = a) : g = 1 := by
  obtain ⟨hgA, hgs⟩ := mem_altOn.1 hg
  have hmem : ∀ x, x ∈ ({a, b, c} : Set Ω) → g x ∈ ({a, b, c} : Set Ω) := by
    intro x hx
    by_contra hgx
    have h1 := hgs (g x) hgx
    have : g x = x := g.injective h1
    exact hgx (by rw [this]; exact hx)
  have hb : g b = b ∨ g b = c := by
    have h1 := hmem b (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h | h | h
    · exact absurd (g.injective (h.trans hga.symm)) (Ne.symm hab)
    · exact Or.inl h
    · exact Or.inr h
  have hc : g c = b ∨ g c = c := by
    have h1 := hmem c (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h | h | h
    · exact absurd (g.injective (h.trans hga.symm)) (Ne.symm hac)
    · exact Or.inl h
    · exact Or.inr h
  rcases hb with hb | hb
  · have hc' : g c = c := by
      rcases hc with h | h
      · exact absurd (g.injective (h.trans hb.symm)) (Ne.symm hbc)
      · exact h
    ext x
    by_cases hx : x ∈ ({a, b, c} : Set Ω)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> simp [*]
    · simpa using hgs x hx
  · have hc' : g c = b := by
      rcases hc with h | h
      · exact h
      · exact absurd (g.injective (h.trans hb.symm)) (Ne.symm hbc)
    have hgs' : g = swap b c := by
      ext x
      by_cases hx : x ∈ ({a, b, c} : Set Ω)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · rw [hga, swap_apply_of_ne_of_ne hab hac]
        · rw [hb, swap_apply_left]
        · rw [hc', swap_apply_right]
      · rw [hgs x hx, swap_apply_of_ne_of_ne]
        · intro h; exact hx (by simp [h])
        · intro h; exact hx (by simp [h])
    have := mem_alternatingGroup.1 hgA
    rw [hgs', Perm.sign_swap hbc] at this
    exact absurd this (by decide)

theorem tri_mem_altOn {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) :
    tri a b c ∈ altOn ({a, b, c} : Set Ω) := by
  refine mem_altOn.2 ⟨sign_swap_mul_swap hac hab, fun x hx => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  rw [tri, Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2.1, swap_apply_of_ne_of_ne hx.1 hx.2.2]

omit [Fintype Ω] in
theorem tri_apply_a {a b c : Ω} (hab : a ≠ b) (hbc : b ≠ c) : tri a b c a = b := by
  rw [tri, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hab) hbc]

omit [Fintype Ω] in
theorem tri_apply_b (a b c : Ω) : tri a b c b = c := by
  rw [tri, Perm.mul_apply, swap_apply_right, swap_apply_left]

omit [Fintype Ω] in
theorem tri_apply_c {a b c : Ω} (hac : a ≠ c) (hbc : b ≠ c) : tri a b c c = a := by
  rw [tri, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), swap_apply_right]

theorem apply_mem_of_mem_altOn {S : Set Ω} {g : Perm Ω} (hg : g ∈ altOn S) {x : Ω} (hx : x ∈ S) :
    g x ∈ S := by
  by_contra hgx
  have h1 := (mem_altOn.1 hg).2 (g x) hgx
  have : g x = x := g.injective h1
  exact hgx (by rw [this]; exact hx)

theorem altOn_three_le_zpowers {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    altOn ({a, b, c} : Set Ω) ≤ Subgroup.zpowers (tri a b c) := by
  intro g hg
  have ht := tri_mem_altOn hab hac (Ω := Ω) (b := b)
  have ha : g a ∈ ({a, b, c} : Set Ω) := apply_mem_of_mem_altOn hg (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  have hta := tri_apply_a hab hbc
  have htb := tri_apply_b a b c
  rcases ha with ha | ha | ha
  · rw [eq_one_of_mem_altOn_of_apply hab hac hbc hg ha]
    exact Subgroup.one_mem _
  · have h1 : (tri a b c)⁻¹ * g ∈ altOn ({a, b, c} : Set Ω) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hg
    have h2 : ((tri a b c)⁻¹ * g) a = a := by
      rw [Perm.mul_apply, ha, Perm.inv_eq_iff_eq.2 hta.symm]
    have h3 := eq_one_of_mem_altOn_of_apply hab hac hbc h1 h2
    have : g = tri a b c := by
      have := congrArg (fun z => tri a b c * z) h3
      simpa using this
    rw [this]
    exact Subgroup.mem_zpowers _
  · have h1 : (tri a b c)⁻¹ * ((tri a b c)⁻¹ * g) ∈ altOn ({a, b, c} : Set Ω) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hg)
    have h2 : ((tri a b c)⁻¹ * ((tri a b c)⁻¹ * g)) a = a := by
      rw [Perm.mul_apply, Perm.mul_apply, ha, Perm.inv_eq_iff_eq.2 htb.symm,
        Perm.inv_eq_iff_eq.2 hta.symm]
    have h3 := eq_one_of_mem_altOn_of_apply hab hac hbc h1 h2
    have : g = tri a b c * tri a b c := by
      have := congrArg (fun z => tri a b c * (tri a b c * z)) h3
      simpa using this
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem altOn_le_closure_Y2 {p : ℕ} {R E : Subgroup (Perm Ω)} (hER : E ≤ R)
    (hEi : Nat.card R ≤ p * Nat.card E) (h5 : 5 ≤ Nat.card (fixSet E)) {T : Set Ω}
    (hT : T ⊆ fixSet E) (hT3 : T.ncard = 3) : altOn T ≤ Subgroup.closure (Y2 p R) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.1 hT3
  have hdiff : 1 < (fixSet E \ {a, b, c}).ncard := by
    rw [Set.ncard_sdiff hT, hT3, ← Nat.card_coe_set_eq]
    omega
  obtain ⟨d, e, hd, he, hde⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 hdiff
  have hmem : ∀ x ∈ ({a, b, c} : Set Ω), x ∈ fixSet E := fun x hx => hT hx
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have hc := hmem c (by simp)
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hd he
  refine (altOn_three_le_zpowers hab hac hbc).trans (Subgroup.zpowers_le.2 ?_)
  exact tri_mem_closure_Y2 hER hEi ha hb hc hd.1 he.1 hab hac hde hd.2.1 hd.2.2.1 hd.2.2.2
    he.2.1 he.2.2.1 he.2.2.2

omit [DecidableEq Ω] in
theorem exists_two_mem_fixSet {E : Subgroup (Perm Ω)} (h5 : 5 ≤ Nat.card (fixSet E)) {F : Set Ω}
    (hF : F.ncard ≤ 3) :
    ∃ d e, d ∈ fixSet E ∧ e ∈ fixSet E ∧ d ∉ F ∧ e ∉ F ∧ d ≠ e := by
  have h1 : (fixSet E).ncard - F.ncard ≤ (fixSet E \ F).ncard :=
    Set.le_ncard_sdiff F (fixSet E) (Set.toFinite _)
  have h2 : 1 < (fixSet E \ F).ncard := by
    rw [Nat.card_coe_set_eq] at h5
    omega
  obtain ⟨d, e, hd, he, hde⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 h2
  exact ⟨d, e, hd.1, he.1, hd.2, he.2, hde⟩

theorem alternatingGroup_le_closure_Y2_of_family {p : ℕ} {R : Subgroup (Perm Ω)}
    (ℰ : Set (Subgroup (Perm Ω)))
    (hℰ : ∀ E ∈ ℰ, E ≤ R ∧ Nat.card R ≤ p * Nat.card E ∧ 5 ≤ Nat.card (fixSet E))
    (hcover : ∀ ω : Ω, ∃ E ∈ ℰ, ω ∈ fixSet E) (ω₀ : Ω) (hω₀ : ∀ E ∈ ℰ, ω₀ ∈ fixSet E) :
    alternatingGroup Ω ≤ Subgroup.closure (Y2 p R) := by
  classical
  let ι : Type _ := {T : Set Ω // ∃ E ∈ ℰ, T ⊆ fixSet E ∧ T.ncard = 3}
  have hS3 : ∀ T : ι, 3 ≤ T.1.ncard := fun T => by
    obtain ⟨E, -, -, h3⟩ := T.2
    omega
  have hcov : (⋃ T : ι, T.1) = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    obtain ⟨E, hE, hωE⟩ := hcover ω
    obtain ⟨d, e, hd, he, hdn, hen, hde⟩ :=
      exists_two_mem_fixSet (hℰ E hE).2.2 (F := {ω}) (by simp)
    have hdω : ω ≠ d := fun h => hdn (by simp [h])
    have heω : ω ≠ e := fun h => hen (by simp [h])
    refine Set.mem_iUnion.2 ⟨⟨{ω, d, e}, E, hE, ?_, Set.ncard_eq_three.2 ⟨ω, d, e, hdω, heω, hde,
      rfl⟩⟩, by simp⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hωE
    · exact hd
    · exact he
  have hlink : ∀ T : ι, ∃ T'' : ι, ω₀ ∈ T''.1 ∧ (T.1 ∩ T''.1).Nonempty := by
    intro T
    by_cases hT : ω₀ ∈ T.1
    · exact ⟨T, hT, ω₀, hT, hT⟩
    · obtain ⟨E, hE, hTE, hT3⟩ := T.2
      obtain ⟨t, ht⟩ : T.1.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      have hω₀E : ω₀ ∈ fixSet E := hω₀ E hE
      obtain ⟨u, v, hu, hv, hun, hvn, huv⟩ :=
        exists_two_mem_fixSet (hℰ E hE).2.2 (F := {ω₀, t})
          ((Set.ncard_insert_le ω₀ {t}).trans (by simp))
      have hu' : u ≠ ω₀ ∧ u ≠ t := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hun
      have htω : ω₀ ≠ t := fun h => hT (h ▸ ht)
      refine ⟨⟨{ω₀, t, u}, E, hE, ?_, Set.ncard_eq_three.2 ⟨ω₀, t, u, htω, hu'.1.symm,
        hu'.2.symm, rfl⟩⟩, by simp, t, ht, by simp⟩
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hω₀E
      · exact hTE ht
      · exact hu
  have hconn : ∀ i j : ι, Relation.ReflTransGen (fun a b : ι => (a.1 ∩ b.1).Nonempty) i j := by
    intro i j
    obtain ⟨i', hi', hii'⟩ := hlink i
    obtain ⟨j', hj', hjj'⟩ := hlink j
    refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single hii')
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single ⟨ω₀, hi', hj'⟩)
        (Relation.ReflTransGen.single ?_))
    obtain ⟨x, hx1, hx2⟩ := hjj'
    exact ⟨x, hx2, hx1⟩
  have : Nonempty Ω := ⟨ω₀⟩
  have hgen := iSup_altOn_eq_alternatingGroup (S := fun T : ι => T.1) hS3 hcov hconn
  rw [← hgen]
  refine iSup_le fun T => ?_
  obtain ⟨E, hE, hTE, hT3⟩ := T.2
  obtain ⟨hER, hEi, h5E⟩ := hℰ E hE
  exact altOn_le_closure_Y2 hER hEi h5E hTE hT3

theorem alternatingGroup_le_closure_Y2_of_card_le {p : ℕ} {R : Subgroup (Perm Ω)}
    (h5 : 5 ≤ Fintype.card Ω) (hR : Nat.card R ≤ p) (ω₀ : Ω) :
    alternatingGroup Ω ≤ Subgroup.closure (Y2 p R) := by
  have hfix : fixSet (⊥ : Subgroup (Perm Ω)) = Set.univ := by
    ext ω
    simp [fixSet, Subgroup.mem_bot]
  refine alternatingGroup_le_closure_Y2_of_family {⊥} ?_ (fun ω => ⟨⊥, rfl, ?_⟩) ω₀ (fun E hE => ?_)
  · intro E hE
    rw [Set.mem_singleton_iff] at hE
    subst hE
    refine ⟨bot_le, ?_, ?_⟩
    · simpa using hR
    · rw [hfix, Nat.card_univ, Nat.card_eq_fintype_card]
      exact h5
  · rw [hfix]
    trivial
  · rw [Set.mem_singleton_iff] at hE
    subst hE
    rw [hfix]
    trivial

theorem alternatingGroup_le_closure_Y2 {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    {R : Subgroup (Perm Ω)} (hR : IsPGroup p R) (h5 : 5 ≤ Fintype.card Ω)
    (hn : Fintype.card Ω % p = 2) (horb : ∀ ω : Ω, Nat.card (orbit R ω) ≤ p) :
    alternatingGroup Ω ≤ Subgroup.closure (Y2 p R) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hmod : ∀ E : Subgroup (Perm Ω), E ≤ R →
      Fintype.card Ω ≡ Nat.card (fixSet E) [MOD p] := by
    intro E hE
    have := card_fixSet_modEq (p := p) (hR.to_le hE)
    rwa [Nat.card_eq_fintype_card] at this
  have hFR : 2 ≤ Nat.card (fixSet R) := by
    have h := hmod R le_rfl
    by_contra hlt
    have h1 : Nat.card (fixSet R) % p = Nat.card (fixSet R) :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : Fintype.card Ω % p = Nat.card (fixSet R) % p := h
    omega
  let P : Subgroup (Perm Ω) → Prop := fun E =>
    E ≤ R ∧ Nat.card R ≤ p * Nat.card E ∧ 5 ≤ Nat.card (fixSet E)
  have hgood : ∀ ω : Ω, ω ∉ fixSet R → P (stabIn R ω) ∧ ω ∈ fixSet (stabIn R ω) := by
    intro ω hω
    refine ⟨⟨stabIn_le R ω, ?_, ?_⟩, mem_fixSet_stabIn R ω⟩
    · rw [card_mul_card_stabIn R ω]
      exact Nat.mul_le_mul_right _ (horb ω)
    · have hsub : fixSet R ⊆ fixSet (stabIn R ω) := fixSet_anti (stabIn_le R ω)
      have hss : fixSet R ⊂ fixSet (stabIn R ω) :=
        ⟨hsub, fun h => hω (h (mem_fixSet_stabIn R ω))⟩
      have hlt : Nat.card (fixSet R) < Nat.card (fixSet (stabIn R ω)) := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.ncard_lt_ncard hss
      have h1 := hmod R le_rfl
      have h2 := hmod (stabIn R ω) (stabIn_le R ω)
      have h3 : Nat.card (fixSet R) ≡ Nat.card (fixSet (stabIn R ω)) [MOD p] := h1.symm.trans h2
      have h4 := (Nat.modEq_iff_dvd' hlt.le).1 h3
      have h5' : p ≤ Nat.card (fixSet (stabIn R ω)) - Nat.card (fixSet R) :=
        Nat.le_of_dvd (by omega) h4
      omega
  have hcover : ∀ ω : Ω, ∃ E, P E ∧ ω ∈ fixSet E := by
    intro ω
    by_cases hnt : ∃ ω', ω' ∉ fixSet R
    · by_cases hω : ω ∈ fixSet R
      · obtain ⟨ω', hω'⟩ := hnt
        exact ⟨stabIn R ω', (hgood ω' hω').1, fixSet_anti (stabIn_le R ω') hω⟩
      · exact ⟨stabIn R ω, (hgood ω hω).1, (hgood ω hω).2⟩
    · have hall : ∀ ω', ω' ∈ fixSet R := fun ω' => by
        by_contra h
        exact hnt ⟨ω', h⟩
      have hfix : fixSet R = Set.univ := Set.eq_univ_of_forall hall
      refine ⟨R, ⟨le_rfl, ?_, ?_⟩, hall ω⟩
      · have : 1 ≤ p := hp.one_lt.le
        nlinarith [Nat.card_pos (α := R)]
      · rw [hfix, Nat.card_univ, Nat.card_eq_fintype_card]
        exact h5
  have hω₀ : ∃ ω₀, ω₀ ∈ fixSet R := by
    by_contra h
    have h' : ∀ ω, ω ∉ fixSet R := fun ω hω => h ⟨ω, hω⟩
    have : fixSet R = ∅ := Set.eq_empty_of_forall_notMem h'
    rw [this] at hFR
    simp at hFR
  obtain ⟨ω₀, hω₀R⟩ := hω₀
  exact alternatingGroup_le_closure_Y2_of_family {E | P E} (fun E hE => hE) hcover ω₀
    (fun E hE => fixSet_anti hE.1 hω₀R)

end Double

end GL83.PiGen
