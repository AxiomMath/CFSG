module

public import CFSG.ClassicalInvolution.Phan.Phan3D4Sound
public import CFSG.ClassicalInvolution.Phan.Phan3SL3Pres
public import CFSG.ClassicalInvolution.Phan.Phan3D4Order

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ClassicalInvolution.PhanD4 (edgeSrc edgeTgt edgeD_iff)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

theorem wordVal_mem_closure_range {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (w : List (Fin n × Bool)) : wordVal g w ∈ Subgroup.closure (Set.range g) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    simp only [wordVal, List.map_cons, List.prod_cons] at ih ⊢
    refine Subgroup.mul_mem _ ?_ ih
    obtain ⟨i, b⟩ := l
    cases b
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
    · exact Subgroup.subset_closure ⟨i, rfl⟩

theorem wordVal_eq_one_of_forall {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (hg : ∀ i, g i = 1) (w : List (Fin n × Bool)) : wordVal g w = 1 := by
  induction w with
  | nil => simp [wordVal]
  | cons l w ih =>
    simp only [wordVal, List.map_cons, List.prod_cons] at ih ⊢
    obtain ⟨i, b⟩ := l
    cases b <;> simp [letterVal, hg i, ih]

theorem eq_comm_of_wordVal_commWord8 {Y : Type*} [Group Y] (x : Fin 8 → Y) {g h : Fin 8}
    (hw : wordVal x (commWord8 g h) = 1) : x g * x h = x h * x g := by
  simp only [commWord8, wordVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    letterVal, Bool.cond_true, Bool.cond_false, mul_one] at hw
  have h1 : x g * x h * ((x g)⁻¹ * (x h)⁻¹) = 1 := by rw [mul_assoc]; exact hw
  rw [← mul_inv_rev] at h1
  exact mul_inv_eq_one.1 h1

theorem commutes_closure {X : Type*} [Group X] {S T : Set X}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure T, a * b = b * a := by
  have h1 : ∀ s ∈ S, ∀ b ∈ Subgroup.closure T, s * b = b * s := by
    intro s hs b hb
    have : Subgroup.closure T ≤ Subgroup.centralizer {s} := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact h s hs t ht
    have hb' := this hb
    rw [Subgroup.mem_centralizer_iff] at hb'
    exact hb' s rfl
  intro a ha b hb
  have : Subgroup.closure S ≤ Subgroup.centralizer {b} := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (h1 s hs b hb).symm
  have ha' := this ha
  rw [Subgroup.mem_centralizer_iff] at ha'
  exact (ha' b rfl).symm

@[expose] def ctIdx (k : Fin 4) (u : Fin 2) : Fin 8 := ⟨2 * k.val + u.val, by omega⟩

@[expose] def ctσ (k : Fin 4) : Fin 8 := ctIdx k 0

@[expose] def ctτ (k : Fin 4) : Fin 8 := ctIdx k 1

@[expose] def ctEdgeGen (i j : Fin 4) : Fin 4 → Fin 8 := ![ctσ i, ctτ i, ctσ j, ctτ j]

theorem sl3EdgeRels_eq : ∀ e : Fin 3, sl3EdgeRels (edgeSrc e).val (edgeTgt e).val =
    sl3Rels.map (List.map fun l => (ctEdgeGen (edgeSrc e) (edgeTgt e) l.1, l.2)) := by
  decide +kernel

theorem exists_edge_gen : ∀ j : Fin 8, ∃ e : Fin 3, ∃ g : Fin 4,
    ctEdgeGen (edgeSrc e) (edgeTgt e) g = j := by
  decide +kernel

theorem exists_node : ∀ j : Fin 8, ∃ k : Fin 4, j = ctσ k ∨ j = ctτ k := by
  decide +kernel

theorem commWord8_mem_d4CtRels : ∀ p ∈ ([(0, 2), (0, 3), (2, 3)] : List (Fin 4 × Fin 4)),
    ∀ u v : Fin 2, commWord8 (ctIdx p.1 u) (ctIdx p.2 v) ∈ d4CtRels := by
  decide +kernel

theorem edgeRels_mem (e : Fin 3) :
    ∀ w ∈ sl3EdgeRels (edgeSrc e).val (edgeTgt e).val, w ∈ d4CtRels := by
  intro w hw
  have h : ∀ e : Fin 3, ((edgeSrc e).val, (edgeTgt e).val) = (0, 1) ∨
      ((edgeSrc e).val, (edgeTgt e).val) = (1, 2) ∨ ((edgeSrc e).val, (edgeTgt e).val) = (1, 3) := by
    decide
  rcases h e with h | h | h <;> simp only [Prod.mk.injEq] at h <;> rw [h.1, h.2] at hw <;>
    simp only [d4CtRels, List.mem_append] <;> tauto

theorem ctEdgeGen_centre : ∀ e : Fin 3,
    ctEdgeGen (edgeSrc e) (edgeTgt e) (![2, 0, 0] e) = ctσ 1 := by
  decide +kernel

variable (hc : D4Checks)

section Simple

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
  (π : PhanD4Group →* G) (hπ : Function.Surjective π)

@[expose] noncomputable def ctG (π : PhanD4Group →* G) (k : Fin 8) : G := π (ctEltP k)

@[expose] def ctNode (π : PhanD4Group →* G) (k : Fin 4) : Subgroup G :=
  Subgroup.closure {ctG π (ctσ k), ctG π (ctτ k)}

include hc hnab hπ

theorem wordVal_ctG_eq_one {v : List (Fin 8 × Bool)} (h : v ∈ d4CtRels) :
    wordVal (ctG π) v = 1 := by
  have h3 := d4N_le_ker hc hnab π hπ (wordVal_ctEltP_mem hc h)
  rw [MonoidHom.mem_ker] at h3
  have h4 : wordVal (ctG π) v = π (wordVal ctEltP v) := wordVal_map π ctEltP v
  rw [h4, h3]

theorem wordVal_ctG_eq_gen (i : Fin 8) :
    wordVal (ctG π) (decodeWord 8 phanInCtCodes[i.val]!) = π (PresentedGroup.of i) := by
  have h3 := d4N_le_ker hc hnab π hπ (gen_mem_d4N hc i)
  rw [MonoidHom.mem_ker, map_mul, map_inv] at h3
  have h4 : wordVal (ctG π) (decodeWord 8 phanInCtCodes[i.val]!) =
      π (wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!)) := wordVal_map π ctEltP _
  rw [h4]
  exact inv_mul_eq_one.1 h3

theorem exists_ctG_ne_one : ∃ j : Fin 8, ctG π j ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ j, ctG π j = 1 := fun j => not_not.1 fun h => hcon ⟨j, h⟩
  have h1 : ∀ i : Fin 8, π (PresentedGroup.of i) = 1 := fun i => by
    rw [← wordVal_ctG_eq_gen hc hnab π hπ i]
    exact wordVal_eq_one_of_forall _ hcon' _
  have h2 : π = 1 := PresentedGroup.ext fun i => by rw [h1 i]; rfl
  obtain ⟨x, y, hxy⟩ := hnab
  obtain ⟨px, rfl⟩ := hπ x
  obtain ⟨py, rfl⟩ := hπ y
  rw [h2] at hxy
  exact hxy (by simp)

theorem exists_edgeHom {K : Type} [Field K] (hK : Nat.card K = 3) (e : Fin 3) :
    ∃ θ : SL(3, K) →* G, ∀ g : Fin 4,
      θ (sl3Gen K g) = ctG π (ctEdgeGen (edgeSrc e) (edgeTgt e) g) := by
  refine sl3_lift_of_card hK hc.sl3 (fun g => ctG π (ctEdgeGen (edgeSrc e) (edgeTgt e) g)) ?_
  intro r hr
  have h1 := wordVal_map_reindex (MonoidHom.id G) (ctG π)
    (fun g => ctG π (ctEdgeGen (edgeSrc e) (edgeTgt e) g)) (ctEdgeGen (edgeSrc e) (edgeTgt e))
    (fun g => rfl) r
  rw [MonoidHom.id_apply] at h1
  rw [← h1]
  refine wordVal_ctG_eq_one hc hnab π hπ (edgeRels_mem e _ ?_)
  rw [sl3EdgeRels_eq e]
  exact List.mem_map.2 ⟨r, hr, rfl⟩

theorem exists_edgeHoms {K : Type} [Field K] (hK : Nat.card K = 3) :
    ∃ θ : Fin 3 → (SL(3, K) →* G),
      (∀ e g, θ e (sl3Gen K g) = ctG π (ctEdgeGen (edgeSrc e) (edgeTgt e) g)) ∧
        ∀ e g, θ e (sl3Gen K g) ≠ 1 := by
  choose θ hθ using exists_edgeHom hc hnab π hπ hK
  have hiff : ∀ e, θ e = 1 ↔ ctG π (ctσ 1) = 1 := by
    intro e
    constructor
    · intro he
      have := hθ e (![2, 0, 0] e)
      rw [he, ctEdgeGen_centre e] at this
      exact this.symm
    · intro h
      refine sl3_hom_eq_one_of_gen hK (θ e) (![2, 0, 0] e) ?_
      rw [hθ e, ctEdgeGen_centre e]
      exact h
  have hne : ctG π (ctσ 1) ≠ 1 := by
    intro h1
    obtain ⟨j, hj⟩ := exists_ctG_ne_one hc hnab π hπ
    obtain ⟨e, g, rfl⟩ := exists_edge_gen j
    apply hj
    rw [← hθ e g, (hiff e).2 h1]
    rfl
  refine ⟨θ, hθ, fun e g h => hne ?_⟩
  exact (hiff e).1 (sl3_hom_eq_one_of_gen hK (θ e) g h)

theorem ctNode_commutes (i j : Fin 4)
    (hmem : ∀ u v : Fin 2, commWord8 (ctIdx i u) (ctIdx j v) ∈ d4CtRels) :
    ∀ a ∈ ctNode π i, ∀ b ∈ ctNode π j, a * b = b * a := by
  have hgen : ∀ u v : Fin 2, ctG π (ctIdx i u) * ctG π (ctIdx j v) =
      ctG π (ctIdx j v) * ctG π (ctIdx i u) := fun u v =>
    eq_comm_of_wordVal_commWord8 _ (wordVal_ctG_eq_one hc hnab π hπ (hmem u v))
  refine commutes_closure ?_
  intro s hs t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact hgen 0 0
  · exact hgen 0 1
  · exact hgen 1 0
  · exact hgen 1 1

theorem iSup_ctNode : ⨆ k, ctNode π k = ⊤ := by
  have h2 : (⊤ : Subgroup PhanD4Group).map π ≤ Subgroup.closure (Set.range (ctG π)) := by
    rw [← PresentedGroup.closure_range_of, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, ← wordVal_ctG_eq_gen hc hnab π hπ i]
    exact wordVal_mem_closure_range _ _
  have h3 : Subgroup.closure (Set.range (ctG π)) ≤ ⨆ k, ctNode π k := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := exists_node j
    refine Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure ?_)
    rcases hk with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, rfl⟩ := hπ g
  exact h3 (h2 ⟨p, Subgroup.mem_top _, rfl⟩)

theorem exists_ctChain {K : Type} [Field K] (hK : Nat.card K = 3) :
    ∃ U : Fin 4 → Subgroup G,
      (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
        ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ i j : Fin 4, edgeD 4 i j → ∃ W, WeakCT.LinearBlockStandardPair K W (U i) (U j)) ∧
      ⨆ k, U k = ⊤ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨θ, hθ, hne⟩ := exists_edgeHoms hc hnab π hπ hK
  have c02 := ctNode_commutes hc hnab π hπ 0 2
    (fun u v => commWord8_mem_d4CtRels (0, 2) (by simp) u v)
  have c03 := ctNode_commutes hc hnab π hπ 0 3
    (fun u v => commWord8_mem_d4CtRels (0, 3) (by simp) u v)
  have c23 := ctNode_commutes hc hnab π hπ 2 3
    (fun u v => commWord8_mem_d4CtRels (2, 3) (by simp) u v)
  refine ⟨ctNode π, ?_, ?_, iSup_ctNode hc hnab π hπ⟩
  · intro i j hij h1 h2
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact absurd (by decide) h1
        | exact absurd (by decide) h2
        | exact c02
        | exact c03
        | exact c23
        | exact fun a ha b hb => (c02 b hb a ha).symm
        | exact fun a ha b hb => (c03 b hb a ha).symm
        | exact fun a ha b hb => (c23 b hb a ha).symm
  · intro i j hij
    obtain ⟨e, rfl, rfl⟩ := (edgeD_iff i j).1 hij
    refine ⟨(θ e).range, linearBlockStandardPair_of_hom hK (θ e)
      (sl3_ker_le_center (θ e) 0 (hne e 0)) ?_ ?_⟩
    · rw [hθ e 0, hθ e 1]
      rfl
    · rw [hθ e 2, hθ e 3]
      rfl

end Simple

end CFSG.ClassicalInvolution.Phan.Q3G
