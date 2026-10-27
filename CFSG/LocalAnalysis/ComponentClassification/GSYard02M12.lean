module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylow
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

namespace SylowTab

open CFSG Subgroup Equiv
open scoped Pointwise

section subprods

variable {G : Type*} [Group G]

@[expose] def subprods : List G → List G
  | [] => [1]
  | g :: gs => subprods gs ++ (subprods gs).map (g * ·)

theorem one_mem_subprods : ∀ gs : List G, (1 : G) ∈ subprods gs
  | [] => by simp [subprods]
  | _ :: gs => by simp [subprods, one_mem_subprods gs]

theorem length_subprods : ∀ gs : List G, (subprods gs).length = 2 ^ gs.length
  | [] => by simp [subprods]
  | _ :: gs => by
    simp only [subprods, List.length_append, List.length_map, length_subprods gs,
      List.length_cons, pow_succ]
    ring

theorem subprods_mem_closure : ∀ (gs : List G) (y : G), y ∈ subprods gs →
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

theorem mem_subprods_of_mem_closure {gs : List G} (hinv : ∀ g ∈ gs, g * g = 1)
    (hcl : ∀ g ∈ gs, ∀ y ∈ subprods gs, g * y ∈ subprods gs) {y : G}
    (hy : y ∈ Subgroup.closure {g | g ∈ gs}) : y ∈ subprods gs := by
  induction hy using Subgroup.closure_induction_left with
  | one => exact one_mem_subprods gs
  | mul_left x hx y _ ih => exact hcl x hx y ih
  | inv_mul_cancel x hx y _ ih =>
    rw [inv_eq_of_mul_eq_one_right (hinv x hx)]
    exact hcl x hx y ih

theorem natCard_closure {gs : List G} (hinv : ∀ g ∈ gs, g * g = 1)
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

theorem natCard_sup_of_le_normalizer (E K : Subgroup G)
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

end subprods

section tables

variable {n : ℕ}

@[expose] def tab (σ : Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

@[expose] def tcomp (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

@[expose] abbrev tid (n : ℕ) : List ℕ := tab (1 : Perm (Fin n))

@[expose] def subprodsL (e : List ℕ) : List (List ℕ) → List (List ℕ)
  | [] => [e]
  | g :: gs => subprodsL e gs ++ (subprodsL e gs).map (tcomp g)

theorem tab_mul (σ τ : Perm (Fin n)) : tab (σ * τ) = tcomp (tab σ) (tab τ) := by
  apply List.ext_getElem
  · simp [tab, tcomp]
  · intro i h₁ h₂
    simp [tab, tcomp, List.getD_eq_getElem?_getD, List.getElem?_ofFn]

theorem tab_injective : Function.Injective (tab : Perm (Fin n) → List ℕ) := by
  intro σ τ h
  have h' := List.ofFn_injective h
  ext i
  exact congrFun h' i

theorem map_tab_subprods : ∀ gs : List (Perm (Fin n)),
    (subprods gs).map tab = subprodsL (tid n) (gs.map tab)
  | [] => by simp [subprods, subprodsL]
  | g :: gs => by
    simp only [subprods, subprodsL, List.map_append, List.map_cons, ← map_tab_subprods gs]
    congr 1
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro y _
    simp [Function.comp, tab_mul]

theorem mem_subprodsL {gs : List (Perm (Fin n))} {y : Perm (Fin n)}
    (hy : y ∈ subprods gs) : tab y ∈ subprodsL (tid n) (gs.map tab) := by
  rw [← map_tab_subprods]
  exact List.mem_map.mpr ⟨y, hy, rfl⟩

@[expose] abbrev TableClosed (n : ℕ) (gs : List (Perm (Fin n))) : Prop :=
  (∀ a ∈ gs.map tab, tcomp a a = tid n) ∧
  (∀ a ∈ gs.map tab, ∀ b ∈ subprodsL (tid n) (gs.map tab),
    tcomp a b ∈ subprodsL (tid n) (gs.map tab)) ∧
  (subprodsL (tid n) (gs.map tab)).Nodup

@[expose] abbrev TablePair (n : ℕ) (gsE gsK : List (Perm (Fin n))) : Prop :=
  (∀ b ∈ subprodsL (tid n) (gsE.map tab), tcomp b b = tid n) ∧
  (∀ b ∈ subprodsL (tid n) (gsE.map tab),
    b ∈ subprodsL (tid n) (gsK.map tab) → b = tid n) ∧
  (∀ a ∈ gsK.map tab, ∀ b ∈ subprodsL (tid n) (gsE.map tab),
    tcomp (tcomp a b) a ∈ subprodsL (tid n) (gsE.map tab))

theorem TableClosed.involutions {gs : List (Perm (Fin n))} (h : TableClosed n gs) :
    ∀ g ∈ gs, g * g = 1 := by
  obtain ⟨h1, -, -⟩ := h
  intro g hg
  apply tab_injective
  rw [tab_mul]
  exact h1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)

theorem TableClosed.mul_mem {gs : List (Perm (Fin n))} (h : TableClosed n gs) :
    ∀ g ∈ gs, ∀ y ∈ subprods gs, g * y ∈ subprods gs := by
  obtain ⟨-, h2, -⟩ := h
  intro g hg y hy
  have h2 := h2 (tab g) (List.mem_map.mpr ⟨g, hg, rfl⟩) (tab y) (mem_subprodsL hy)
  rw [← tab_mul, ← map_tab_subprods] at h2
  obtain ⟨z, hz, hz'⟩ := List.mem_map.mp h2
  exact (tab_injective hz') ▸ hz

theorem TableClosed.nodup {gs : List (Perm (Fin n))} (h : TableClosed n gs) :
    (subprods gs).Nodup := by
  obtain ⟨-, -, h3⟩ := h
  rw [← map_tab_subprods] at h3
  exact List.Nodup.of_map tab h3

theorem mem_normalizer_of_tables {gs : List (Perm (Fin n))} (hcl : TableClosed n gs)
    {s : Perm (Fin n)}
    (h : ∀ a ∈ subprodsL (tid n) (gs.map tab), ∃ b ∈ subprodsL (tid n) (gs.map tab),
      tcomp (tab s) a = tcomp b (tab s)) :
    s ∈ Subgroup.normalizer ((Subgroup.closure {g | g ∈ gs} : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) := by
  classical
  have hinv := hcl.involutions
  have hclos := hcl.mul_mem
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hx' := mem_subprods_of_mem_closure hinv hclos hx
  obtain ⟨b, hb, hbt⟩ := h (tab x) (mem_subprodsL hx')
  rw [← map_tab_subprods] at hb
  obtain ⟨c, hc, hct⟩ := List.mem_map.mp hb
  have hsx : s * x = c * s := tab_injective (by rw [tab_mul, tab_mul, hbt, hct])
  have hconj : s * x * s⁻¹ = c := by
    rw [hsx, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact subprods_mem_closure gs c hc

theorem sylowFourJoined_of_tables (G : Subgroup (Perm (Fin n))) (gsE gsK : List (Perm (Fin n)))
    (m : ℕ) (hEG : ∀ g ∈ gsE, g ∈ G) (hKG : ∀ g ∈ gsK, g ∈ G)
    (hE : TableClosed n gsE) (hK : TableClosed n gsK) (hEK : TablePair n gsE gsK)
    (hlen : 3 ≤ gsE.length) (hcard : Nat.card G = 2 ^ (gsE.length + gsK.length) * m)
    (hm : ¬ 2 ∣ m) : SylowFourJoined G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsq, hdisj, hnorm⟩ := hEK
  have hinvE := hE.involutions
  have hinvK := hK.involutions
  have hclE := hE.mul_mem
  have hclK := hK.mul_mem
  set E : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ gsE} with hEdef
  set K : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ gsK} with hKdef
  have hEG' : E ≤ G := (Subgroup.closure_le _).mpr hEG
  have hKG' : K ≤ G := (Subgroup.closure_le _).mpr hKG
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
  have hPG : E ⊔ K ≤ G := sup_le hEG' hKG'
  have hPnorm : E ⊔ K ≤ normalizer (E : Set (Perm (Fin n))) :=
    sup_le Subgroup.le_normalizer hKnorm
  have hP'card : Nat.card ((E ⊔ K).subgroupOf G) = 2 ^ (gsE.length + gsK.length) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hPcard]
  have hidx : ¬ 2 ∣ ((E ⊔ K).subgroupOf G).index := by
    have h1 := Subgroup.card_mul_index ((E ⊔ K).subgroupOf G)
    rw [hP'card, hcard] at h1
    have h2 : ((E ⊔ K).subgroupOf G).index = m :=
      Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rwa [h2]
  refine sylowFourJoined_of_normal_elemAbelian ((IsPGroup.of_card hP'card).toSylow hidx)
    (A := E.subgroupOf G) ?_ ?_ ?_
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
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG').toEquiv, hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ gsE.length := Nat.pow_le_pow_right (by norm_num) hlen

end tables

end SylowTab

open SylowTab
open CFSG Subgroup Blueprint

def m12a₁ : Equiv.Perm (Fin 12) := M12Cover.s₁ * M12Cover.s₄ * M12Cover.s₃ * M12Cover.s₄

def m12a₂ : Equiv.Perm (Fin 12) :=
  M12Cover.s₁ * M12Cover.s₂ * M12Cover.s₄ * M12Cover.s₁ * M12Cover.s₄

def m12a₃ : Equiv.Perm (Fin 12) := M12Cover.s₃ * M12Cover.s₃

def m12gsA : List (Equiv.Perm (Fin 12)) := [m12a₁, m12a₂, m12a₃]

@[expose] abbrev m12A : Subgroup (Equiv.Perm (Fin 12)) := Subgroup.closure {g | g ∈ m12gsA}

theorem m12_tableClosed : TableClosed 12 m12gsA := by decide +kernel

theorem m12_square : ∀ b ∈ subprodsL (tid 12) (m12gsA.map tab), tcomp b b = tid 12 := by
  decide +kernel

theorem m12_norm₁ : ∀ a ∈ subprodsL (tid 12) (m12gsA.map tab),
    ∃ b ∈ subprodsL (tid 12) (m12gsA.map tab), tcomp (tab M12Cover.s₁) a = tcomp b (tab M12Cover.s₁) := by
  decide +kernel

theorem m12_norm₂ : ∀ a ∈ subprodsL (tid 12) (m12gsA.map tab),
    ∃ b ∈ subprodsL (tid 12) (m12gsA.map tab), tcomp (tab M12Cover.s₂) a = tcomp b (tab M12Cover.s₂) := by
  decide +kernel

theorem m12_norm₃ : ∀ a ∈ subprodsL (tid 12) (m12gsA.map tab),
    ∃ b ∈ subprodsL (tid 12) (m12gsA.map tab), tcomp (tab M12Cover.s₃) a = tcomp b (tab M12Cover.s₃) := by
  decide +kernel

theorem m12_norm₄ : ∀ a ∈ subprodsL (tid 12) (m12gsA.map tab),
    ∃ b ∈ subprodsL (tid 12) (m12gsA.map tab), tcomp (tab M12Cover.s₄) a = tcomp b (tab M12Cover.s₄) := by
  decide +kernel

theorem m12A_le_S : m12A ≤ M12Cover.S := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  simp only [m12gsA, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact mul_mem (mul_mem (mul_mem M12Cover.s₁_mem_S M12Cover.s₄_mem_S)
      M12Cover.s₃_mem_S) M12Cover.s₄_mem_S
  · exact mul_mem (mul_mem (mul_mem (mul_mem M12Cover.s₁_mem_S M12Cover.s₂_mem_S)
      M12Cover.s₄_mem_S) M12Cover.s₁_mem_S) M12Cover.s₄_mem_S
  · exact mul_mem M12Cover.s₃_mem_S M12Cover.s₃_mem_S

theorem m12_S_le_normalizer : M12Cover.S ≤ Subgroup.normalizer (m12A : Set (Equiv.Perm (Fin 12))) := by
  refine (Subgroup.closure_le _).mpr fun s hs => ?_
  have hs' : s = M12Cover.s₁ ∨ s = M12Cover.s₂ ∨ s = M12Cover.s₃ ∨ s = M12Cover.s₄ := by
    simpa using hs
  rcases hs' with rfl | rfl | rfl | rfl
  · exact mem_normalizer_of_tables m12_tableClosed m12_norm₁
  · exact mem_normalizer_of_tables m12_tableClosed m12_norm₂
  · exact mem_normalizer_of_tables m12_tableClosed m12_norm₃
  · exact mem_normalizer_of_tables m12_tableClosed m12_norm₄

theorem sylowFourJoined_M12 :
    SylowFourJoined NativeSporadic.M12 := by
  have hA₀M : m12A ≤ NativeSporadic.M12 := m12A_le_S.trans M12Cover.S_le_M12
  have hA₀card : Nat.card m12A = 8 :=
    (natCard_closure m12_tableClosed.involutions m12_tableClosed.mul_mem
      m12_tableClosed.nodup).trans rfl
  have hA2' : ∀ a ∈ m12A, a * a = 1 := by
    intro a ha
    have ha' := mem_subprods_of_mem_closure m12_tableClosed.involutions
      m12_tableClosed.mul_mem ha
    apply tab_injective
    rw [tab_mul]
    exact m12_square _ (mem_subprodsL ha')
  have hSA : (M12Cover.sylow : Subgroup NativeSporadic.M12) ≤
      normalizer ((m12A.subgroupOf NativeSporadic.M12 : Subgroup NativeSporadic.M12) :
        Set NativeSporadic.M12) := by
    rw [M12Cover.coe_sylow]
    intro x hx
    have hx' : (x : Equiv.Perm (Fin 12)) ∈ M12Cover.S := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : (n : Equiv.Perm (Fin 12)) ∈ m12A := Subgroup.mem_subgroupOf.mp hn
    have hN := Subgroup.mem_normalizer_iff.mp (m12_S_le_normalizer hx') (n : Equiv.Perm (Fin 12))
    exact Subgroup.mem_subgroupOf.mpr (hN.mp hn')
  have hA2 : ∀ a ∈ m12A.subgroupOf NativeSporadic.M12, a * a = 1 := fun a ha =>
    Subtype.ext (hA2' (a : Equiv.Perm (Fin 12)) (Subgroup.mem_subgroupOf.mp ha))
  have hA8 : 8 ≤ Nat.card (m12A.subgroupOf NativeSporadic.M12) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv, hA₀card]
  exact sylowFourJoined_of_normal_elemAbelian M12Cover.sylow hSA hA2 hA8

theorem leafM12_holds : LeafSporadic .M12 := by
  intro X _ _ _ _ hX
  obtain ⟨e⟩ := hX
  have e' : ↥NativeSporadic.M12 ≃* X := e.symm
  exact SylowFourJoined.of_mulEquiv e' sylowFourJoined_M12

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
