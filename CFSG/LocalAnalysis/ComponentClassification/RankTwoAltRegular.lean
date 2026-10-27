module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltLocalB
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOrbit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIIShape

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoHypIIY
open scoped commutatorElement

section Witness

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem qWitness_of_le_nE_local (ι : β ↪ α) {E' : Subgroup (Perm β)} {E : Subgroup (Perm α)}
    (hE : ∀ x ∈ E', ∃ y ∈ E, ∀ b, y (ι b) = ι (x b)) {P : Subgroup (Perm β)}
    (hP : P ≤ nE (alternatingGroup β) E') (hPP : ⁅P, P⁆ = P) (hPe : Even (Nat.card P)) :
    QWitness (alternatingGroup α) E := by
  refine ⟨P.map (viaEmbeddingHom ι), (Subgroup.map_mono hP).trans (map_nE_le ι hE), ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hPP]
  · rwa [Subgroup.card_map_of_injective (viaEmbeddingHom_injective ι)]

theorem yWitness_of_le_nE_local (ι : β ↪ α) {E' : Subgroup (Perm β)} {E : Subgroup (Perm α)}
    (hE : ∀ x ∈ E', ∃ y ∈ E, ∀ b, y (ι b) = ι (x b)) {P : Subgroup (Perm β)}
    (hP : P ≤ nE (alternatingGroup β) E') (hPp : IsPGroup 2 P)
    (hcard : Nat.card ↥(E ⊓ alternatingGroup α) < Nat.card P) :
    YWitness (alternatingGroup α) E := by
  refine Or.inr ⟨P.map (viaEmbeddingHom ι), (Subgroup.map_mono hP).trans (map_nE_le ι hE),
    hPp.map _, ?_⟩
  rwa [Subgroup.card_map_of_injective (viaEmbeddingHom_injective ι)]

omit [Fintype α] [DecidableEq β] in
theorem eq_viaEmbeddingHom_of (ι : β ↪ α) {y : Perm α} {m : Perm β}
    (hy : ∀ b, y (ι b) = ι (m b)) (hfix : ∀ x, x ∉ Set.range ι → y x = x) :
    y = viaEmbeddingHom ι m := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨b, rfl⟩ := hx
    rw [hy, viaEmbeddingHom_apply_image]
  · rw [hfix x hx, viaEmbeddingHom_apply_of_notMem ι m hx]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem eq_map_of_free (ι : β ↪ α) {E : Subgroup (Perm α)} {E' : Subgroup (Perm β)}
    (hgen : ∀ m ∈ E', viaEmbeddingHom ι m ∈ E) {b₀ : β}
    (hfree : ∀ e ∈ E, e (ι b₀) = ι b₀ → e = 1)
    (hcov : ∀ e ∈ E, ∃ m ∈ E', e (ι b₀) = ι (m b₀)) :
    E = E'.map (viaEmbeddingHom ι) := by
  apply le_antisymm
  · intro e he
    obtain ⟨m, hm, hme⟩ := hcov e he
    have h1 : (viaEmbeddingHom ι m)⁻¹ * e = 1 := by
      refine hfree _ (E.mul_mem (E.inv_mem (hgen m hm)) he) ?_
      rw [Perm.mul_apply, hme, Perm.inv_eq_iff_eq, viaEmbeddingHom_apply_image]
    exact ⟨m, hm, inv_mul_eq_one.mp h1⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact hgen m hm

end Witness

@[expose] def eq4 : Fin 4 ≃ Pt 1 where
  toFun i := ((0, ⟨i / 2, by omega⟩), ⟨i % 2, by omega⟩)
  invFun p := ⟨2 * p.1.2 + p.2, by omega⟩
  left_inv := by decide
  right_inv := by decide

@[expose] def eq8 : Fin 8 ≃ Pt 2 where
  toFun i := ((⟨i / 4, by omega⟩, ⟨(i / 2) % 2, by omega⟩), ⟨i % 2, by omega⟩)
  invFun p := ⟨4 * p.1.1 + 2 * p.1.2 + p.2, by omega⟩
  left_inv := by decide
  right_inv := by decide

@[expose] def eq12 : Fin 6 × Fin 2 ≃ Pt 3 where
  toFun p := ((⟨p.1 / 2, by omega⟩, ⟨p.1 % 2, by omega⟩), p.2)
  invFun q := (⟨2 * q.1.1 + q.1.2, by omega⟩, q.2)
  left_inv := by decide
  right_inv := by decide

theorem eq4_klein_a : ∀ i, eq4 ((swap 0 1 * swap 2 3 : Perm (Fin 4)) i) = aM 1 (eq4 i) := by
  decide
theorem eq4_klein_b : ∀ i, eq4 ((swap 0 2 * swap 1 3 : Perm (Fin 4)) i) = bM 1 (eq4 i) := by
  decide
theorem eq8_a8 : ∀ i, eq8 (a8 i) = aM 2 (eq8 i) := by decide
theorem eq8_b8 : ∀ i, eq8 (b8 i) = bM 2 (eq8 i) := by decide
theorem eq8_c8 : ∀ i, eq8 (c8 i) = cM (eq8 i) := by decide
theorem eq12_a12 : ∀ p, eq12 (a12 p) = aM 3 (eq12 p) := by decide
theorem eq12_b12 : ∀ p, eq12 (b12 p) = bM 3 (eq12 p) := by decide

theorem kleinFour_trans : ∀ p : Fin 4, ∃ m ∈ kleinFour, m 0 = p := by
  have h1 : (swap 0 1 * swap 2 3 : Perm (Fin 4)) ∈ kleinFour := subset_closure (Set.mem_insert _ _)
  have h2 : (swap 0 2 * swap 1 3 : Perm (Fin 4)) ∈ kleinFour :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  intro p
  fin_cases p
  · exact ⟨1, one_mem _, rfl⟩
  · exact ⟨_, h1, by decide⟩
  · exact ⟨_, h2, by decide⟩
  · exact ⟨_, mul_mem h1 h2, by decide⟩

theorem e8_trans : ∀ p : Fin 8, ∃ m ∈ e8, m 0 = p := by
  intro p
  fin_cases p
  · exact ⟨1, one_mem _, rfl⟩
  · exact ⟨_, a8_mem_e8, by decide⟩
  · exact ⟨_, b8_mem_e8, by decide⟩
  · exact ⟨_, mul_mem a8_mem_e8 b8_mem_e8, by decide⟩
  · exact ⟨_, c8_mem_e8, by decide⟩
  · exact ⟨_, mul_mem a8_mem_e8 c8_mem_e8, by decide⟩
  · exact ⟨_, mul_mem b8_mem_e8 c8_mem_e8, by decide⟩
  · exact ⟨_, mul_mem (mul_mem a8_mem_e8 b8_mem_e8) c8_mem_e8, by decide⟩

section Embed

variable {α : Type*}

@[expose] noncomputable def orbitEmb {ya yb : Perm α} (ha2 : ya * ya = 1) (hb2 : yb * yb = 1)
    (hab : ya * yb = yb * ya) {m : ℕ} (r : Fin m → α)
    (hreg : ∀ k (s j : Fin 2), (pw ya s * pw yb j) (r k) = r k → s = 0 ∧ j = 0)
    (horb : ∀ k l (s j : Fin 2), (pw ya s * pw yb j) (r k) = r l → k = l) : Pt m ↪ α :=
  ⟨orbitMap ya yb r, orbitMap_injective ha2 hb2 hab hreg horb⟩

theorem orbitEmb_apply {ya yb : Perm α} (ha2 : ya * ya = 1) (hb2 : yb * yb = 1)
    (hab : ya * yb = yb * ya) {m : ℕ} (r : Fin m → α) (hreg) (horb) (p : Pt m) :
    orbitEmb ha2 hb2 hab r hreg horb p = orbitMap ya yb r p := rfl

end Embed

section Structure

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem apply_eq_self_of_apply_eq_self (h7 : 7 ≤ Fintype.card α) {E : Subgroup (Perm α)}
    (hE : IsElemAbelian 2 E) (hQ : ¬ QWitness (alternatingGroup α) E) {e e' : Perm α}
    (he : e ∈ E) (he' : e' ∈ E) (he1 : e ≠ 1) {x : α} (hx : e x = x) : e' x = x := by
  have hinv : ∀ y ∈ E, ∀ p, y (y p) = p := fun y hy p => by
    have h := hE.2 y hy
    rw [sq] at h
    rw [← Perm.mul_apply, h, Perm.one_apply]
  have hcomm : ∀ p, e' (e p) = e (e' p) := fun p => by
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨e', he'⟩ ⟨e, he⟩)
    simp only [Subgroup.coe_mul] at h
    rw [← Perm.mul_apply, h, Perm.mul_apply]
  by_contra h
  exact hQ (qWitness_of_twoOrbit' (by omega) he' he (hinv e' he') (hinv e he) hcomm (Or.inr h7)
    he1 hx h)

theorem five_le_card_of_mem {G : Type*} [Group G] [DecidableEq G] {H : Subgroup G}
    {x₁ x₂ x₃ x₄ x₅ : G} (h : [x₁, x₂, x₃, x₄, x₅].Nodup) (h₁ : x₁ ∈ H) (h₂ : x₂ ∈ H)
    (h₃ : x₃ ∈ H) (h₄ : x₄ ∈ H) (h₅ : x₅ ∈ H) [Finite H] : 5 ≤ Nat.card H := by
  have hsub : ((([x₁, x₂, x₃, x₄, x₅].toFinset : Finset G)) : Set G) ⊆ (H : Set G) := by
    intro x hx
    simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_ofPred_eq] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hfin : (H : Set G).Finite := Set.toFinite _
  have hc := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup h] at hc
  calc 5 ≤ (H : Set G).ncard := hc
    _ = Nat.card H := (Nat.card_coe_set_eq _).symm

theorem eq_kleinFour_map (h7 : 7 ≤ Fintype.card α) {E : Subgroup (Perm α)}
    (hE : IsElemAbelian 2 E) (h4 : 4 ≤ Nat.card E)
    (hQ : ¬ QWitness (alternatingGroup α) E) (hY : ¬ YWitness (alternatingGroup α) E)
    (h24 : 4 < Nat.card E → ∀ a ∈ alternatingGroup α, ∀ t ∈ E,
      (∀ x ∈ E, ∃ y ∈ E, t * (a⁻¹ * x * a) * t⁻¹ = a⁻¹ * y * a) →
        ∀ x ∈ E, t * (a⁻¹ * x * a) = a⁻¹ * x * a * t) :
    ∃ ι : Fin 4 ↪ α, E = kleinFour.map (viaEmbeddingHom ι) := by
  classical
  have hinv : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have h := hE.2 x hx
    rwa [sq] at h
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsub2 : ∀ u : Perm α, ¬ (E : Set (Perm α)) ⊆ {1, u} := by
    intro u hu
    have h := Set.ncard_le_ncard hu (Set.toFinite _)
    have h2 : ({1, u} : Set (Perm α)).ncard ≤ 2 := Set.ncard_insert_le _ _ |>.trans (by simp)
    rw [← Nat.card_coe_set_eq] at h
    have : Nat.card E ≤ 2 := h.trans h2
    omega
  obtain ⟨ya, hya, hya1⟩ : ∃ y ∈ E, y ≠ 1 := by
    by_contra h
    push Not at h
    exact hsub2 1 fun y hy => Or.inl (h y hy)
  obtain ⟨yb, hyb, hyb1, hyab⟩ : ∃ y ∈ E, y ≠ 1 ∧ y ≠ ya := by
    by_contra h
    push Not at h
    refine hsub2 ya fun y hy => ?_
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (h y hy hy1)
  have ha2 := hinv ya hya
  have hb2 := hinv yb hyb
  have hab := hcomm ya hya yb hyb
  have hfix := fun {e e'} => @apply_eq_self_of_apply_eq_self α _ _ h7 E hE hQ e e'
  have hpwE : ∀ s j : Fin 2, pw ya s * pw yb j ∈ E := by
    intro s j
    fin_cases s <;> fin_cases j <;> simp only [pw] <;> simp [hya, hyb, mul_mem]
  have hpw1 : ∀ s j : Fin 2, pw ya s * pw yb j = 1 → s = 0 ∧ j = 0 := by
    intro s j h
    fin_cases s <;> fin_cases j <;> simp only [pw] at h ⊢ <;> simp at h ⊢
    · exact hyb1 h
    · exact hya1 h
    · exact hyab ((inv_eq_of_mul_eq_one_right h).symm.trans (inv_eq_of_mul_eq_one_right ha2))
  have hfree : ∀ e ∈ E, ∀ p, ya p ≠ p → e p = p → e = 1 := fun e he p hp hep => by
    by_contra he1
    exact hp (hfix he hya he1 hep)
  have hout : ∀ e ∈ E, ∀ p, ya p = p → e p = p := fun e he p hp => hfix hya he hya1 hp
  have hmoved : ∀ e ∈ E, ∀ p, ya p ≠ p → ya (e p) ≠ e p := fun e he p hp h => by
    apply hp
    have h' : e (ya p) = e p := by
      rw [← Perm.mul_apply, ← hcomm ya hya e he, Perm.mul_apply, h]
    exact e.injective h'
  have hreg0 : ∀ p, ya p ≠ p → ∀ s j : Fin 2, (pw ya s * pw yb j) p = p → s = 0 ∧ j = 0 :=
    fun p hp s j h => hpw1 s j (hfree _ (hpwE s j) p hp h)
  have hwinv : ∀ (s j : Fin 2) p, (pw ya s * pw yb j) ((pw ya s * pw yb j) p) = p := by
    intro s j p
    rw [← Perm.mul_apply, pw_mul_pw_mul_self ha2 hb2 hab, Perm.one_apply]
  have hwmove : ∀ (s j : Fin 2) p, ya p ≠ p → ya ((pw ya s * pw yb j) p) ≠ (pw ya s * pw yb j) p :=
    fun s j p hp => hmoved _ (hpwE s j) p hp
  have hrange : ∀ {m : ℕ} (r : Fin m → α) (hreg) (horb) {β : Type} (e : β ≃ Pt m) (x : α),
      (∃ k, ∃ s j : Fin 2, (pw ya s * pw yb j) (r k) = x) →
      x ∈ Set.range ((e.toEmbedding).trans (orbitEmb ha2 hb2 hab r hreg horb)) := by
    rintro m r hreg horb β e x ⟨k, s, j, rfl⟩
    exact ⟨e.symm ((k, j), s), by simp [orbitEmb_apply, orbitMap]⟩
  obtain ⟨r1, hr1⟩ : ∃ r, ya r ≠ r := by
    by_contra h
    push Not at h
    exact hya1 (Equiv.ext h)
  by_cases h2 : ∃ r2, ya r2 ≠ r2 ∧ ∀ s j : Fin 2, (pw ya s * pw yb j) r1 ≠ r2
  · obtain ⟨r2, hr2, hr12⟩ := h2
    by_cases h3 : ∃ r3, ya r3 ≠ r3 ∧ (∀ s j : Fin 2, (pw ya s * pw yb j) r1 ≠ r3) ∧
        ∀ s j : Fin 2, (pw ya s * pw yb j) r2 ≠ r3
    ·
      exfalso
      obtain ⟨r3, hr3, hr13, hr23⟩ := h3
      let r : Fin 3 → α := ![r1, r2, r3]
      have hreg : ∀ k (s j : Fin 2), (pw ya s * pw yb j) (r k) = r k → s = 0 ∧ j = 0 := by
        intro k
        fin_cases k
        · exact hreg0 r1 hr1
        · exact hreg0 r2 hr2
        · exact hreg0 r3 hr3
      have hsymm : ∀ (s j : Fin 2) {p q : α}, (pw ya s * pw yb j) p = q →
          (pw ya s * pw yb j) q = p := fun s j p q h => by rw [← h, hwinv]
      have horb : ∀ k l (s j : Fin 2), (pw ya s * pw yb j) (r k) = r l → k = l := by
        intro k l s j h
        fin_cases k <;> fin_cases l
        · rfl
        · exact absurd h (hr12 s j)
        · exact absurd h (hr13 s j)
        · exact absurd (hsymm s j h) (hr12 s j)
        · rfl
        · exact absurd h (hr23 s j)
        · exact absurd (hsymm s j h) (hr13 s j)
        · exact absurd (hsymm s j h) (hr23 s j)
        · rfl
      set ι := eq12.toEmbedding.trans (orbitEmb ha2 hb2 hab r hreg horb) with hι
      have hιapp : ∀ i, ι i = orbitMap ya yb r (eq12 i) := fun i => rfl
      have hmatch := forall_mem_closure_pair ι hya hyb
        (fun i => by rw [hιapp, hιapp, orbitMap_aM ha2, eq12_a12])
        (fun i => by rw [hιapp, hιapp, orbitMap_bM hb2 hab, eq12_b12])
      have hPP : ⁅(alternatingGroup (Fin 6)).map dbl, (alternatingGroup (Fin 6)).map dbl⁆ =
          (alternatingGroup (Fin 6)).map dbl := by
        rw [← Subgroup.map_commutator, commutator_alternatingGroup_eq_self (by simp)]
      have hPe : Even (Nat.card ((alternatingGroup (Fin 6)).map dbl)) := by
        rw [Subgroup.card_map_of_injective dbl_injective]
        exact even_card_alternatingGroup (by simp)
      exact hQ (qWitness_of_le_nE_local ι hmatch dbl_alternatingGroup_le_nE hPP hPe)
    ·
      exfalso
      push Not at h3
      have hM : ∀ p, ya p ≠ p → (∃ s j : Fin 2, (pw ya s * pw yb j) r1 = p) ∨
          ∃ s j : Fin 2, (pw ya s * pw yb j) r2 = p := by
        intro p hp
        by_cases h : ∃ s j : Fin 2, (pw ya s * pw yb j) r1 = p
        · exact Or.inl h
        · push Not at h
          exact Or.inr (h3 p hp h)
      have hsymm : ∀ (s j : Fin 2) {p q : α}, (pw ya s * pw yb j) p = q →
          (pw ya s * pw yb j) q = p := fun s j p q h => by rw [← h, hwinv]
      by_cases hc : ∃ yc ∈ E, ∀ s j : Fin 2, yc ≠ pw ya s * pw yb j
      ·
        obtain ⟨yc, hyc, hyc4⟩ := hc
        have hc2 := hinv yc hyc
        have hac := hcomm ya hya yc hyc
        have hbc := hcomm yb hyb yc hyc
        have hc1 : yc ≠ 1 := by simpa [pw] using hyc4 0 0
        have hca : yc ≠ ya := by simpa [pw] using hyc4 1 0
        have hcb : yc ≠ yb := by simpa [pw] using hyc4 0 1
        have hcab : yc ≠ ya * yb := by simpa [pw] using hyc4 1 1
        have hcr_move : ya (yc r1) ≠ yc r1 := hmoved yc hyc r1 hr1
        have hnot : ∀ s j : Fin 2, (pw ya s * pw yb j) r1 ≠ yc r1 := by
          intro s j h
          apply hyc4 s j
          have h1 : (pw ya s * pw yb j) * yc = 1 :=
            hfree _ (E.mul_mem (hpwE s j) hyc) r1 hr1 (by rw [Perm.mul_apply, ← h, hwinv])
          have hw2 := pw_mul_pw_mul_self ha2 hb2 hab s j
          calc yc = (pw ya s * pw yb j) * ((pw ya s * pw yb j) * yc) := by
                rw [← mul_assoc, hw2, one_mul]
            _ = pw ya s * pw yb j := by rw [h1, mul_one]
        let r : Fin 2 → α := ![r1, yc r1]
        have hreg : ∀ k (s j : Fin 2), (pw ya s * pw yb j) (r k) = r k → s = 0 ∧ j = 0 := by
          intro k
          fin_cases k
          · exact hreg0 r1 hr1
          · exact hreg0 (yc r1) hcr_move
        have horb : ∀ k l (s j : Fin 2), (pw ya s * pw yb j) (r k) = r l → k = l := by
          intro k l s j h
          fin_cases k <;> fin_cases l
          · rfl
          · exact absurd h (hnot s j)
          · exact absurd (hsymm s j h) (hnot s j)
          · rfl
        obtain ⟨ι, hιapp⟩ : ∃ ι : Fin 8 ↪ α, ∀ i, ι i = orbitMap ya yb r (eq8 i) :=
          ⟨eq8.toEmbedding.trans (orbitEmb ha2 hb2 hab r hreg horb), fun i => rfl⟩
        have hrange' : ∀ x, (∃ k, ∃ s j : Fin 2, (pw ya s * pw yb j) (r k) = x) →
            x ∈ Set.range ι := by
          rintro x ⟨k, s, j, rfl⟩
          exact ⟨eq8.symm ((k, j), s), by rw [hιapp]; simp [orbitMap]⟩
        have hmem_range : ∀ x, ya x ≠ x → x ∈ Set.range ι := by
          intro x hx
          rcases hM x hx with ⟨s, j, hsj⟩ | ⟨s, j, hsj⟩
          · exact hrange' x ⟨0, s, j, hsj⟩
          · rcases hM (yc r1) hcr_move with ⟨s', j', h'⟩ | ⟨s', j', h'⟩
            · exact absurd h' (hnot s' j')
            · refine hrange' x ⟨1, s + s', j + j', ?_⟩
              show (pw ya (s + s') * pw yb (j + j')) (yc r1) = x
              rw [← pw_mul_pw_mul ha2 hb2 hab, Perm.mul_apply, hsymm s' j' h', hsj]
        have hout' : ∀ e ∈ E, ∀ x, x ∉ Set.range ι → e x = x := fun e he x hx =>
          hout e he x (by by_contra h; exact hx (hmem_range x h))
        have hka : ya = viaEmbeddingHom ι a8 :=
          eq_viaEmbeddingHom_of ι (fun i => by rw [hιapp, hιapp, orbitMap_aM ha2, eq8_a8])
            (hout' ya hya)
        have hkb : yb = viaEmbeddingHom ι b8 :=
          eq_viaEmbeddingHom_of ι (fun i => by rw [hιapp, hιapp, orbitMap_bM hb2 hab, eq8_b8])
            (hout' yb hyb)
        have hkc : yc = viaEmbeddingHom ι c8 :=
          eq_viaEmbeddingHom_of ι
            (fun i => by rw [hιapp, hιapp, orbitMap_cM hc2 hac hbc (r := r) rfl, eq8_c8])
            (hout' yc hyc)
        have hgen : ∀ m ∈ e8, viaEmbeddingHom ι m ∈ E := by
          have : e8.map (viaEmbeddingHom ι) ≤ E := by
            rw [e8, MonoidHom.map_closure, closure_le]
            rintro _ ⟨x, hx, rfl⟩
            rcases hx with rfl | rfl | rfl
            · rw [← hka]
              exact hya
            · rw [← hkb]
              exact hyb
            · rw [← hkc]
              exact hyc
          exact fun m hm => this ⟨m, hm, rfl⟩
        have hι0 : ι 0 = r1 := by rw [hιapp]; rfl
        have hEeq : E = e8.map (viaEmbeddingHom ι) :=
          eq_map_of_free ι hgen (b₀ := 0) (fun e he he0 => hfree e he r1 hr1 (hι0 ▸ he0))
            fun e he => by
              obtain ⟨b, hb⟩ := hmem_range (e (ι 0)) (by rw [hι0]; exact hmoved e he r1 hr1)
              obtain ⟨m, hm, hm0⟩ := e8_trans b
              exact ⟨m, hm, by rw [hm0, hb]⟩
        have h5 : 4 < Nat.card E := by
          have f3 : ya * yb ≠ 1 := fun h => hyab ((inv_eq_of_mul_eq_one_right h).symm.trans
            (inv_eq_of_mul_eq_one_right ha2))
          have f6 : ya * yb ≠ ya := fun h => hyb1 (mul_left_cancel (h.trans (mul_one ya).symm))
          have f8 : ya * yb ≠ yb := fun h => hya1 (mul_right_cancel (h.trans (one_mul yb).symm))
          have hnd : [1, ya, yb, ya * yb, yc].Nodup := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
              List.nodup_nil, and_true]
            exact ⟨⟨hya1.symm, hyb1.symm, f3.symm, hc1.symm⟩, ⟨hyab.symm, f6.symm, hca.symm⟩,
              ⟨f8.symm, hcb.symm⟩, hcab.symm, not_false⟩
          have := five_le_card_of_mem hnd (one_mem E) hya hyb (mul_mem hya hyb) hyc
          omega
        obtain ⟨a, ha_def⟩ : ∃ a : Perm α, a = viaEmbeddingHom ι a3 := ⟨_, rfl⟩
        have ha : a ∈ alternatingGroup α := ha_def ▸
          viaEmbeddingHom_mem_alternatingGroup ι (mem_alternatingGroup.2 sign_a3)
        have hnorm : ∀ x ∈ E, ∃ y ∈ E, ya * (a⁻¹ * x * a) * ya⁻¹ = a⁻¹ * y * a := by
          intro x hx
          rw [hEeq] at hx
          obtain ⟨m, hm, rfl⟩ := hx
          have hm' := conj_a3a8_mem_e8 hm
          refine ⟨viaEmbeddingHom ι ((a3 * a8 * a3⁻¹) * m * (a3 * a8 * a3⁻¹)⁻¹), hgen _ hm', ?_⟩
          have hgrp : a8 * (a3⁻¹ * m * a3) * a8⁻¹ =
              a3⁻¹ * ((a3 * a8 * a3⁻¹) * m * (a3 * a8 * a3⁻¹)⁻¹) * a3 := by group
          calc ya * (a⁻¹ * viaEmbeddingHom ι m * a) * ya⁻¹
              = viaEmbeddingHom ι a8 * ((viaEmbeddingHom ι a3)⁻¹ * viaEmbeddingHom ι m *
                  viaEmbeddingHom ι a3) * (viaEmbeddingHom ι a8)⁻¹ := by rw [hka, ha_def]
            _ = viaEmbeddingHom ι (a8 * (a3⁻¹ * m * a3) * a8⁻¹) := by
                simp only [map_mul, map_inv]
            _ = viaEmbeddingHom ι (a3⁻¹ * ((a3 * a8 * a3⁻¹) * m * (a3 * a8 * a3⁻¹)⁻¹) * a3) := by
                rw [hgrp]
            _ = (viaEmbeddingHom ι a3)⁻¹ *
                  viaEmbeddingHom ι ((a3 * a8 * a3⁻¹) * m * (a3 * a8 * a3⁻¹)⁻¹) *
                  viaEmbeddingHom ι a3 := by
                simp only [map_mul, map_inv]
            _ = a⁻¹ * viaEmbeddingHom ι ((a3 * a8 * a3⁻¹) * m * (a3 * a8 * a3⁻¹)⁻¹) * a := by
                rw [ha_def]
        have hcomm' := h24 h5 a ha ya hya hnorm yc hyc
        have h1 : ya * (a⁻¹ * yc * a) = viaEmbeddingHom ι (a8 * (a3⁻¹ * c8 * a3)) := by
          rw [hka, hkc, ha_def, map_mul, map_mul, map_mul, map_inv]
        have h2 : a⁻¹ * yc * a * ya = viaEmbeddingHom ι (a3⁻¹ * c8 * a3 * a8) := by
          rw [hka, hkc, ha_def, map_mul, map_mul, map_mul, map_inv]
        rw [h1, h2] at hcomm'
        exact a8_not_commute (viaEmbeddingHom_injective ι hcomm')
      ·
        push Not at hc
        let r : Fin 2 → α := ![r1, r2]
        have hreg : ∀ k (s j : Fin 2), (pw ya s * pw yb j) (r k) = r k → s = 0 ∧ j = 0 := by
          intro k
          fin_cases k
          · exact hreg0 r1 hr1
          · exact hreg0 r2 hr2
        have horb : ∀ k l (s j : Fin 2), (pw ya s * pw yb j) (r k) = r l → k = l := by
          intro k l s j h
          fin_cases k <;> fin_cases l
          · rfl
          · exact absurd h (hr12 s j)
          · exact absurd (hsymm s j h) (hr12 s j)
          · rfl
        set ι := eq8.toEmbedding.trans (orbitEmb ha2 hb2 hab r hreg horb) with hι
        have hιapp : ∀ i, ι i = orbitMap ya yb r (eq8 i) := fun i => rfl
        have hmatch := forall_mem_closure_pair ι hya hyb
          (fun i => by rw [hιapp, hιapp, orbitMap_aM ha2, eq8_a8])
          (fun i => by rw [hιapp, hιapp, orbitMap_bM hb2 hab, eq8_b8])
        have hcard : Nat.card E ≤ 4 := by
          have hsub : (E : Set (Perm α)) ⊆
              ((({1, ya, yb, ya * yb} : Finset (Perm α))) : Set (Perm α)) := by
            intro x hx
            obtain ⟨s, j, rfl⟩ := hc x hx
            fin_cases s <;> fin_cases j <;> simp [pw]
          have h := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h
          exact h.trans Finset.card_le_four
        refine hY (yWitness_of_le_nE_local ι hmatch e8_le_nE isPGroup_e8 ?_)
        have hinf : Nat.card ↥(E ⊓ alternatingGroup α) ≤ Nat.card E :=
          Subgroup.card_le_of_le inf_le_left
        have := five_le_card_e8
        omega
  ·
    push Not at h2
    let r : Fin 1 → α := ![r1]
    have hreg : ∀ k (s j : Fin 2), (pw ya s * pw yb j) (r k) = r k → s = 0 ∧ j = 0 := by
      intro k
      fin_cases k
      exact hreg0 r1 hr1
    have horb : ∀ k l (s j : Fin 2), (pw ya s * pw yb j) (r k) = r l → k = l :=
      fun k l _ _ _ => Subsingleton.elim k l
    set ι := eq4.toEmbedding.trans (orbitEmb ha2 hb2 hab r hreg horb) with hι
    have hιapp : ∀ i, ι i = orbitMap ya yb r (eq4 i) := fun i => rfl
    have hmem_range : ∀ x, ya x ≠ x → x ∈ Set.range ι := fun x hx => by
      obtain ⟨s, j, hsj⟩ := h2 x hx
      exact hrange r hreg horb eq4 x ⟨0, s, j, hsj⟩
    have hout' : ∀ e ∈ E, ∀ x, x ∉ Set.range ι → e x = x := fun e he x hx =>
      hout e he x (by by_contra h; exact hx (hmem_range x h))
    have hka : ya = viaEmbeddingHom ι (swap 0 1 * swap 2 3) :=
      eq_viaEmbeddingHom_of ι (fun i => by rw [hιapp, hιapp, orbitMap_aM ha2, eq4_klein_a])
        (hout' ya hya)
    have hkb : yb = viaEmbeddingHom ι (swap 0 2 * swap 1 3) :=
      eq_viaEmbeddingHom_of ι (fun i => by rw [hιapp, hιapp, orbitMap_bM hb2 hab, eq4_klein_b])
        (hout' yb hyb)
    have hgen : ∀ m ∈ kleinFour, viaEmbeddingHom ι m ∈ E := by
      have : kleinFour.map (viaEmbeddingHom ι) ≤ E := by
        rw [kleinFour, MonoidHom.map_closure, closure_le]
        rintro _ ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl
        · rw [← hka]
          exact hya
        · rw [← hkb]
          exact hyb
      exact fun m hm => this ⟨m, hm, rfl⟩
    have hι0 : ι 0 = r1 := rfl
    refine ⟨ι, eq_map_of_free ι hgen (b₀ := 0)
      (fun e he he0 => hfree e he r1 hr1 (hι0 ▸ he0)) fun e he => ?_⟩
    obtain ⟨b, hb⟩ := hmem_range (e (ι 0)) (by rw [hι0]; exact hmoved e he r1 hr1)
    obtain ⟨m, hm, hm0⟩ := kleinFour_trans b
    exact ⟨m, hm, by rw [hm0, hb]⟩

end Structure

end CFSG.ComponentClassification.RankTwoAlt
