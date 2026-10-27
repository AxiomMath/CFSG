module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open Equiv Subgroup
open scoped Pointwise

private def subprods {G : Type*} [Group G] : List G → List G
  | [] => [1]
  | g :: gs => subprods gs ++ (subprods gs).map (g * ·)

section generic

variable {G : Type*} [Group G]

private theorem one_mem_subprods : ∀ gs : List G, (1 : G) ∈ subprods gs
  | [] => by simp [subprods]
  | _ :: gs => by simp [subprods, one_mem_subprods gs]

private theorem length_subprods : ∀ gs : List G, (subprods gs).length = 2 ^ gs.length
  | [] => by simp [subprods]
  | _ :: gs => by
    simp only [subprods, List.length_append, List.length_map, length_subprods gs,
      List.length_cons, pow_succ]
    ring

private theorem subprods_mem_closure : ∀ (gs : List G) (y : G), y ∈ subprods gs →
    y ∈ Subgroup.closure {g | g ∈ gs}
  | [], y, hy => by
    simp only [subprods, List.mem_singleton] at hy
    subst hy
    exact one_mem _
  | g :: gs, y, hy => by
    have hmono : Subgroup.closure {x | x ∈ gs} ≤ Subgroup.closure {x | x ∈ g :: gs} :=
      Subgroup.closure_mono fun x hx => List.mem_cons_of_mem g hx
    simp only [subprods, List.mem_append, List.mem_map] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact hmono (subprods_mem_closure gs y hy)
    · exact mul_mem (subset_closure (by simp)) (hmono (subprods_mem_closure gs z hz))

private theorem mem_subprods_of_mem_closure {gs : List G} (hinv : ∀ g ∈ gs, g * g = 1)
    (hcl : ∀ g ∈ gs, ∀ y ∈ subprods gs, g * y ∈ subprods gs) {y : G}
    (hy : y ∈ Subgroup.closure {g | g ∈ gs}) : y ∈ subprods gs := by
  induction hy using Subgroup.closure_induction_left with
  | one => exact one_mem_subprods gs
  | mul_left x hx y _ ih => exact hcl x hx y ih
  | inv_mul_cancel x hx y _ ih =>
    rw [inv_eq_of_mul_eq_one_right (hinv x hx)]
    exact hcl x hx y ih

private theorem natCard_closure {gs : List G} (hinv : ∀ g ∈ gs, g * g = 1)
    (hcl : ∀ g ∈ gs, ∀ y ∈ subprods gs, g * y ∈ subprods gs) (hnd : (subprods gs).Nodup) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = 2 ^ gs.length := by
  classical
  have hset : ((Subgroup.closure {g | g ∈ gs} : Subgroup G) : Set G) =
      ↑(subprods gs).toFinset := by
    ext y
    simp only [SetLike.mem_coe, List.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨mem_subprods_of_mem_closure hinv hcl, subprods_mem_closure gs y⟩
  have h1 : Nat.card (Subgroup.closure {g | g ∈ gs}) =
      ((Subgroup.closure {g | g ∈ gs} : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, length_subprods]

private theorem natCard_sup_of_le_normalizer (E K : Subgroup G)
    (hK : K ≤ normalizer (E : Set G)) (hdisj : ∀ x ∈ E, x ∈ K → x = 1) :
    Nat.card ↥(E ⊔ K) = Nat.card E * Nat.card K := by
  have hset : ((E ⊔ K : Subgroup G) : Set G) = (E : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left E K hK
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective (fun p : E × K => (⟨(p.1 : G) * p.2,
    mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ : ↥(E ⊔ K)))
    ⟨?_, ?_⟩).symm
  · rintro ⟨⟨e₁, he₁⟩, ⟨k₁, hk₁⟩⟩ ⟨⟨e₂, he₂⟩, ⟨k₂, hk₂⟩⟩ h
    have h' : e₁ * k₁ = e₂ * k₂ := congrArg Subtype.val h
    have hmem : e₂⁻¹ * e₁ ∈ E := mul_mem (inv_mem he₂) he₁
    have hmem' : e₂⁻¹ * e₁ ∈ K := by
      have : e₂⁻¹ * e₁ = k₂ * k₁⁻¹ := by
        calc e₂⁻¹ * e₁ = e₂⁻¹ * (e₁ * k₁) * k₁⁻¹ := by group
          _ = e₂⁻¹ * (e₂ * k₂) * k₁⁻¹ := by rw [h']
          _ = k₂ * k₁⁻¹ := by group
      rw [this]
      exact mul_mem hk₂ (inv_mem hk₁)
    have he : e₁ = e₂ := (inv_mul_eq_one.mp (hdisj _ hmem hmem')).symm
    subst he
    have hk : k₁ = k₂ := mul_left_cancel h'
    subst hk
    rfl
  · rintro ⟨x, hx⟩
    have hx' : x ∈ (E : Set G) * (K : Set G) := hset ▸ hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

end generic

section tables

variable {n : ℕ}

private def tab (σ : Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

private def tcomp (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

private abbrev tid (n : ℕ) : List ℕ := tab (1 : Perm (Fin n))

private def subprodsL (e : List ℕ) : List (List ℕ) → List (List ℕ)
  | [] => [e]
  | g :: gs => subprodsL e gs ++ (subprodsL e gs).map (tcomp g)

private theorem tab_mul (σ τ : Perm (Fin n)) : tab (σ * τ) = tcomp (tab σ) (tab τ) := by
  apply List.ext_getElem
  · simp [tab, tcomp]
  · intro i h₁ h₂
    simp [tab, tcomp, List.getD_eq_getElem?_getD, List.getElem?_ofFn]

private theorem tab_injective : Function.Injective (tab : Perm (Fin n) → List ℕ) := by
  intro σ τ h
  have h' := List.ofFn_injective h
  ext i
  exact congrFun h' i

private theorem map_tab_subprods : ∀ gs : List (Perm (Fin n)),
    (subprods gs).map tab = subprodsL (tid n) (gs.map tab)
  | [] => by simp [subprods, subprodsL]
  | g :: gs => by
    simp only [subprods, subprodsL, List.map_append, List.map_cons, ← map_tab_subprods gs]
    congr 1
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro y _
    simp [Function.comp, tab_mul]

private theorem mem_subprodsL {gs : List (Perm (Fin n))} {y : Perm (Fin n)}
    (hy : y ∈ subprods gs) : tab y ∈ subprodsL (tid n) (gs.map tab) := by
  rw [← map_tab_subprods]
  exact List.mem_map.mpr ⟨y, hy, rfl⟩

private abbrev TableClosed (n : ℕ) (gs : List (Perm (Fin n))) : Prop :=
  (∀ a ∈ gs.map tab, tcomp a a = tid n) ∧
  (∀ a ∈ gs.map tab, ∀ b ∈ subprodsL (tid n) (gs.map tab),
    tcomp a b ∈ subprodsL (tid n) (gs.map tab)) ∧
  (subprodsL (tid n) (gs.map tab)).Nodup

private abbrev TablePair (n : ℕ) (gsE gsK : List (Perm (Fin n))) : Prop :=
  (∀ b ∈ subprodsL (tid n) (gsE.map tab), tcomp b b = tid n) ∧
  (∀ b ∈ subprodsL (tid n) (gsE.map tab),
    b ∈ subprodsL (tid n) (gsK.map tab) → b = tid n) ∧
  (∀ a ∈ gsK.map tab, ∀ b ∈ subprodsL (tid n) (gsE.map tab),
    tcomp (tcomp a b) a ∈ subprodsL (tid n) (gsE.map tab))

private theorem TableClosed.involutions {gs : List (Perm (Fin n))} (h : TableClosed n gs) :
    ∀ g ∈ gs, g * g = 1 := by
  obtain ⟨h1, -, -⟩ := h
  intro g hg
  apply tab_injective
  rw [tab_mul]
  exact h1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)

private theorem TableClosed.mul_mem {gs : List (Perm (Fin n))} (h : TableClosed n gs) :
    ∀ g ∈ gs, ∀ y ∈ subprods gs, g * y ∈ subprods gs := by
  obtain ⟨-, h2, -⟩ := h
  intro g hg y hy
  have h2 := h2 (tab g) (List.mem_map.mpr ⟨g, hg, rfl⟩) (tab y) (mem_subprodsL hy)
  rw [← tab_mul, ← map_tab_subprods] at h2
  obtain ⟨z, hz, hz'⟩ := List.mem_map.mp h2
  exact (tab_injective hz') ▸ hz

private theorem TableClosed.nodup {gs : List (Perm (Fin n))} (h : TableClosed n gs) :
    (subprods gs).Nodup := by
  obtain ⟨-, -, h3⟩ := h
  rw [← map_tab_subprods] at h3
  exact List.Nodup.of_map tab h3

end tables

private theorem exists_sylow_of_tables {n : ℕ} (hn : 2 ≤ n) (gsE gsK : List (Perm (Fin n)))
    (m : ℕ) (hE : TableClosed n gsE) (hK : TableClosed n gsK) (hEK : TablePair n gsE gsK)
    (hlen : 3 ≤ gsE.length)
    (hsE : ∀ g ∈ gsE, Perm.sign g = 1) (hsK : ∀ g ∈ gsK, Perm.sign g = 1)
    (hcard : n.factorial / 2 = 2 ^ (gsE.length + gsK.length) * m) (hm : ¬ 2 ∣ m) :
    ∃ (S : Sylow 2 (alternatingGroup (Fin n))) (A : Subgroup (alternatingGroup (Fin n))),
      (S : Subgroup (alternatingGroup (Fin n))) ≤ normalizer (A : Set (alternatingGroup (Fin n))) ∧
        (∀ a ∈ A, a * a = 1) ∧ 8 ≤ Nat.card A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨hsq, hdisj, hnorm⟩ := hEK
  have hinvE := hE.involutions
  have hinvK := hK.involutions
  have hclE := hE.mul_mem
  have hclK := hK.mul_mem
  set E : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ gsE} with hEdef
  set K : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ gsK} with hKdef
  set Q : Subgroup (Perm (Fin n)) := alternatingGroup (Fin n) with hQdef
  have hEQ : E ≤ Q :=
    (Subgroup.closure_le _).mpr fun g hg => Perm.mem_alternatingGroup.mpr (hsE g hg)
  have hKQ : K ≤ Q :=
    (Subgroup.closure_le _).mpr fun g hg => Perm.mem_alternatingGroup.mpr (hsK g hg)
  have hEcard : Nat.card E = 2 ^ gsE.length := natCard_closure hinvE hclE hE.nodup
  have hKcard : Nat.card K = 2 ^ gsK.length := natCard_closure hinvK hclK hK.nodup
  have hKnorm : K ≤ normalizer (E : Set (Perm (Fin n))) := by
    rw [hKdef, Subgroup.closure_le]
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 := hnorm (tab g) (List.mem_map.mpr ⟨g, hg, rfl⟩) (tab a)
      (mem_subprodsL (mem_subprods_of_mem_closure hinvE hclE ha))
    rw [← tab_mul, ← tab_mul, ← map_tab_subprods] at h1
    obtain ⟨z, hz, hz'⟩ := List.mem_map.mp h1
    rw [inv_eq_of_mul_eq_one_right (hinvK g hg), ← tab_injective hz']
    exact subprods_mem_closure gsE z hz
  have hdisj' : ∀ x ∈ E, x ∈ K → x = 1 := fun x hxE hxK =>
    tab_injective (hdisj _ (mem_subprodsL (mem_subprods_of_mem_closure hinvE hclE hxE))
      (mem_subprodsL (mem_subprods_of_mem_closure hinvK hclK hxK)))
  have hPcard : Nat.card ↥(E ⊔ K) = 2 ^ (gsE.length + gsK.length) := by
    rw [natCard_sup_of_le_normalizer E K hKnorm hdisj', hEcard, hKcard, pow_add]
  have hPQ : E ⊔ K ≤ Q := sup_le hEQ hKQ
  have hPnorm : E ⊔ K ≤ normalizer (E : Set (Perm (Fin n))) :=
    sup_le Subgroup.le_normalizer hKnorm
  have hP'card : Nat.card ((E ⊔ K).subgroupOf Q) = 2 ^ (gsE.length + gsK.length) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv, hPcard]
  have hQcard : Nat.card Q = 2 ^ (gsE.length + gsK.length) * m := by
    rw [hQdef, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hcard
  have hidx : ¬ 2 ∣ ((E ⊔ K).subgroupOf Q).index := by
    have h1 := Subgroup.card_mul_index ((E ⊔ K).subgroupOf Q)
    rw [hP'card, hQcard] at h1
    have h2 : ((E ⊔ K).subgroupOf Q).index = m :=
      Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rwa [h2]
  refine ⟨(IsPGroup.of_card hP'card).toSylow hidx, E.subgroupOf Q, ?_, ?_, ?_⟩
  · intro x hx
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have hn' := Subgroup.mem_normalizer_iff.mp (hPnorm hx)
    exact (hn' (a : Perm (Fin n))).mp ha
  · intro a ha
    have ha' : (a : Perm (Fin n)) ∈ E := ha
    have h1 : (a : Perm (Fin n)) * a = 1 := by
      apply tab_injective
      rw [tab_mul]
      exact hsq _ (mem_subprodsL (mem_subprods_of_mem_closure hinvE hclE ha'))
    exact Subtype.ext h1
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv, hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ gsE.length := Nat.pow_le_pow_right (by norm_num) hlen

private def gensE (n : ℕ) [NeZero n] : List (Perm (Fin n)) :=
  [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7]

private def gensK₂ (n : ℕ) [NeZero n] : List (Perm (Fin n)) :=
  [swap 0 1 * swap 4 5, swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7]

private def gensK₃ (n : ℕ) [NeZero n] : List (Perm (Fin n)) :=
  gensK₂ n ++ [swap 0 1 * swap 8 9]

private theorem sylow_alternating_of_le (n : ℕ) (h8 : 8 ≤ n) (h11 : n ≤ 11) :
    ∃ (S : Sylow 2 (alternatingGroup (Fin n))) (A : Subgroup (alternatingGroup (Fin n))),
      (S : Subgroup (alternatingGroup (Fin n))) ≤ normalizer (A : Set (alternatingGroup (Fin n))) ∧
        (∀ a ∈ A, a * a = 1) ∧ 8 ≤ Nat.card A := by
  interval_cases n
  · exact exists_sylow_of_tables (by norm_num) (gensE 8) (gensK₂ 8) 315 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by simp [gensE, Perm.sign_mul, Perm.sign_swap'])
      (by simp [gensK₂, Perm.sign_mul, Perm.sign_swap']) (by decide +kernel) (by decide)
  · exact exists_sylow_of_tables (by norm_num) (gensE 9) (gensK₂ 9) 2835 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by simp [gensE, Perm.sign_mul, Perm.sign_swap'])
      (by simp [gensK₂, Perm.sign_mul, Perm.sign_swap']) (by decide +kernel) (by decide)
  · exact exists_sylow_of_tables (by norm_num) (gensE 10) (gensK₃ 10) 14175 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by simp [gensE, Perm.sign_mul, Perm.sign_swap'])
      (by simp [gensK₃, gensK₂, Perm.sign_mul, Perm.sign_swap']) (by decide +kernel)
      (by decide)
  · exact exists_sylow_of_tables (by norm_num) (gensE 11) (gensK₃ 11) 155925 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by simp [gensE, Perm.sign_mul, Perm.sign_swap'])
      (by simp [gensK₃, gensK₂, Perm.sign_mul, Perm.sign_swap']) (by decide +kernel)
      (by decide)

theorem leafAlt_holds : LeafAlt := by
  intro X _ _ n hn hn' ⟨e⟩
  obtain ⟨S, A, hSA, hA2, hA8⟩ := sylow_alternating_of_le n hn hn'
  exact SylowFourJoined.of_mulEquiv e.symm (sylowFourJoined_of_normal_elemAbelian S hSA hA2 hA8)

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
