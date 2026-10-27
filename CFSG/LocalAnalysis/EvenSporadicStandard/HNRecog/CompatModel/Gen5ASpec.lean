module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Gen5ACheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5I50

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.EvenSporadicStandard.HNRecog.Simple2S5

theorem gen5aOK_eq : gen5aOK = true := by decide +kernel

theorem smallPerms_getElem (l a : ℕ) :
    (HNUnitaryBridge.smallPerms[l]!)[a]! = (HNUnitaryBridge.smallPermLists[l]!)[a]! := by
  unfold HNUnitaryBridge.smallPerms
  by_cases hl : l < HNUnitaryBridge.smallPermLists.size
  · rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, getElem!_pos _ l hl]
    simp
  · rw [getElem!_neg (Array.map List.toArray HNUnitaryBridge.smallPermLists) l (by simpa using hl),
      getElem!_neg HNUnitaryBridge.smallPermLists l hl]
    change (#[] : Array ℕ)[a]! = ([] : List ℕ)[a]!
    simp

theorem gen5aPt_eq {σ : ℕ → Equiv.Perm (Fin 50)}
    (hσ : ∀ l < 6, ∀ x : Fin 50,
      ((σ l x : Fin 50) : ℕ) = (HNUnitaryBridge.smallPermLists[l]!)[(x : ℕ)]!)
    (w : List ℕ) (hw : ∀ l ∈ w, l < 6) (x : Fin 50) :
    (((w.map σ).prod x : Fin 50) : ℕ) = gen5aPt w x := by
  induction w with
  | nil => simp [gen5aPt]
  | cons l w ih =>
    have hl : l < 6 := hw l List.mem_cons_self
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, hσ l hl, ih']
    simp [gen5aPt]

theorem gen5aEq_iff {σ : ℕ → Equiv.Perm (Fin 50)}
    (hσ : ∀ l < 6, ∀ x : Fin 50,
      ((σ l x : Fin 50) : ℕ) = (HNUnitaryBridge.smallPermLists[l]!)[(x : ℕ)]!)
    {u v : List ℕ} : gen5aEq u v = true ↔
      (∀ l ∈ u, l < 6) ∧ (∀ l ∈ v, l < 6) ∧ (u.map σ).prod = (v.map σ).prod := by
  simp only [gen5aEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    beq_iff_eq]
  constructor
  · rintro ⟨⟨hu, hv⟩, h⟩
    refine ⟨hu, hv, Equiv.ext fun x => Fin.ext ?_⟩
    rw [gen5aPt_eq hσ u hu x, gen5aPt_eq hσ v hv x]
    exact h x.val x.2
  · rintro ⟨hu, hv, h⟩
    refine ⟨⟨hu, hv⟩, fun x hx => ?_⟩
    have := congrArg (fun p : Equiv.Perm (Fin 50) => ((p ⟨x, hx⟩ : Fin 50) : ℕ)) h
    simpa only [gen5aPt_eq hσ u hu, gen5aPt_eq hσ v hv] using this

theorem gen5a_model_of_words (σ : Fin 6 → Equiv.Perm (Fin 50))
    (hcl : Subgroup.closure (Set.range σ) = i50) {T T' Y₁ Y₂ : Equiv.Perm (Fin 50)}
    (hT : T ∈ i50) (hT' : T' ∈ i50) (hY₁ : Y₁ ∈ i50) (hY₂ : Y₂ ∈ i50) (hTT : T * T = 1)
    (hT1 : T ≠ 1) (hTT' : T' * T' = 1) (hT'1 : T' ≠ 1) (hne : T ≠ T') (hcomm : T * T' = T' * T)
    (hY₁T : Y₁ * T = T * Y₁) (hY₂T' : Y₂ * T' = T' * Y₂)
    (hgen : ∀ k : Fin 6, ∃ w : List ℕ, σ k = (w.map fun l => if l = 0 then Y₁ else Y₂).prod) :
    ∃ t t' : ↥i50, orderOf t = 2 ∧ orderOf t' = 2 ∧ t ≠ t' ∧ t * t' = t' * t ∧
      Subgroup.closure ((Subgroup.centralizer ({t} : Set ↥i50) : Set ↥i50) ∪
        (Subgroup.centralizer ({t'} : Set ↥i50) : Set ↥i50)) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ {S : Equiv.Perm (Fin 50)} (hS : S ∈ i50), S * S = 1 → S ≠ 1 →
      orderOf (⟨S, hS⟩ : ↥i50) = 2 := by
    intro S hS h2 h1
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  refine ⟨⟨T, hT⟩, ⟨T', hT'⟩, hord hT hTT hT1, hord hT' hTT' hT'1,
    fun h => hne (congrArg Subtype.val h), Subtype.ext hcomm, ?_⟩
  set K : Subgroup ↥i50 := Subgroup.closure ((Subgroup.centralizer ({(⟨T, hT⟩ : ↥i50)} :
    Set ↥i50) : Set ↥i50) ∪ (Subgroup.centralizer ({(⟨T', hT'⟩ : ↥i50)} : Set ↥i50) :
    Set ↥i50)) with hK
  have hY₁K : (⟨Y₁, hY₁⟩ : ↥i50) ∈ K :=
    Subgroup.subset_closure (Or.inl (Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext hY₁T)))
  have hY₂K : (⟨Y₂, hY₂⟩ : ↥i50) ∈ K :=
    Subgroup.subset_closure (Or.inr (Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext hY₂T')))
  have hY₁L : Y₁ ∈ K.map i50.subtype := ⟨⟨Y₁, hY₁⟩, hY₁K, rfl⟩
  have hY₂L : Y₂ ∈ K.map i50.subtype := ⟨⟨Y₂, hY₂⟩, hY₂K, rfl⟩
  have hσL : ∀ k : Fin 6, σ k ∈ K.map i50.subtype := by
    intro k
    obtain ⟨w, hw⟩ := hgen k
    rw [hw]
    refine list_prod_mem fun g hg => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
    by_cases hl : l = 0
    · simpa [hl] using hY₁L
    · simpa [hl] using hY₂L
  have hle : i50 ≤ K.map i50.subtype :=
    hcl.symm.le.trans ((Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact hσL k))
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨k, hk, hkg⟩ := hle g.2
  have : k = g := Subtype.ext hkg
  rwa [← this]

theorem gen5a_model :
    ∃ t t' : ↥i50, orderOf t = 2 ∧ orderOf t' = 2 ∧ t ≠ t' ∧ t * t' = t' * t ∧
      Subgroup.closure ((Subgroup.centralizer ({t} : Set ↥i50) : Set ↥i50) ∪
        (Subgroup.centralizer ({t'} : Set ↥i50) : Set ↥i50)) = ⊤ := by
  obtain ⟨σ, hσ, hcl⟩ := exists_gens_i50
  let σ' : ℕ → Equiv.Perm (Fin 50) := fun l => if h : l < 6 then σ ⟨l, h⟩ else 1
  have hσ' : ∀ l < 6, ∀ x : Fin 50,
      ((σ' l x : Fin 50) : ℕ) = (HNUnitaryBridge.smallPermLists[l]!)[(x : ℕ)]! := by
    intro l hl x
    simp only [σ', dif_pos hl]
    rw [hσ ⟨l, hl⟩ x, smallPerms_getElem]
  have hmem : ∀ l, σ' l ∈ i50 := by
    intro l
    by_cases hl : l < 6
    · simp only [σ', dif_pos hl]
      exact hcl ▸ Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩
    · simp only [σ', dif_neg hl]
      exact one_mem _
  have hprod : ∀ w : List ℕ, (w.map σ').prod ∈ i50 := fun w =>
    list_prod_mem fun g hg => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
      exact hmem l
  have hOK := gen5aOK_eq
  simp only [gen5aOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    beq_iff_eq] at hOK
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩, h10⟩ := hOK
  have hiff : ∀ {u v : List ℕ}, gen5aEq u v = true ↔
      (∀ l ∈ u, l < 6) ∧ (∀ l ∈ v, l < 6) ∧ (u.map σ').prod = (v.map σ').prod :=
    fun {u v} => gen5aEq_iff (σ := σ') hσ'
  have hvt : ∀ l ∈ gen5aWt, l < 6 := by decide
  have hvt' : ∀ l ∈ gen5aWt', l < 6 := by decide
  have hne1 : ∀ {u : List ℕ}, (∀ l ∈ u, l < 6) → gen5aEq u [] = false → (u.map σ').prod ≠ 1 := by
    intro u hu h e
    have := (hiff (u := u) (v := [])).2 ⟨hu, by simp, by simpa using e⟩
    exact Bool.false_ne_true (h.symm.trans this)
  have hexp : ∀ w : List ℕ, ((gen5aExp w).map σ').prod =
      (w.map fun l => if l = 0 then (gen5aWy₁.map σ').prod else (gen5aWy₂.map σ').prod).prod := by
    intro w
    induction w with
    | nil => simp [gen5aExp]
    | cons l w ih =>
      have : gen5aExp (l :: w) = (if l = 0 then gen5aWy₁ else gen5aWy₂) ++ gen5aExp w := by
        simp only [gen5aExp, List.flatMap_cons]
      rw [this, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]
      by_cases hl : l = 0 <;> simp [hl]
  refine gen5a_model_of_words σ hcl (T := (gen5aWt.map σ').prod) (T' := (gen5aWt'.map σ').prod)
    (Y₁ := (gen5aWy₁.map σ').prod) (Y₂ := (gen5aWy₂.map σ').prod) (hprod _) (hprod _) (hprod _)
    (hprod _) ?_ (hne1 hvt h2) ?_ (hne1 hvt' h4) ?_ ?_ ?_ ?_ ?_
  · simpa [List.map_append, List.prod_append] using (hiff.1 h1).2.2
  · simpa [List.map_append, List.prod_append] using (hiff.1 h3).2.2
  · intro e
    have := hiff.2 ⟨hvt, hvt', e⟩
    exact Bool.false_ne_true (h5.symm.trans this)
  · simpa [List.map_append, List.prod_append] using (hiff.1 h6).2.2
  · simpa [List.map_append, List.prod_append] using (hiff.1 h7).2.2
  · simpa [List.map_append, List.prod_append] using (hiff.1 h8).2.2
  · intro k
    refine ⟨gen5aWords.getD k [], ?_⟩
    have := (hiff.1 (h10 k k.2)).2.2
    rw [hexp] at this
    rw [this]
    simp [σ']

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
