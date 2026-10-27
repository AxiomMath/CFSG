module

public import CFSG.CGT.PushingUpLit.Orth.OrthWit

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv

variable {G : Type*} [Group G] {M Q : Subgroup G}

theorem card_mul_relIndex' {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := (H.subgroupOf K).card_mul_index
  have h2 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2] at h1
  exact h1

def preConj (g : G) (H : Subgroup G) : Subgroup G where
  carrier := {x | g * x * g⁻¹ ∈ H}
  mul_mem' := fun {a b} ha hb => by
    show g * (a * b) * g⁻¹ ∈ H
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact H.mul_mem ha hb
  one_mem' := by
    show g * 1 * g⁻¹ ∈ H
    simp
  inv_mem' := fun {a} ha => by
    show g * a⁻¹ * g⁻¹ ∈ H
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact H.inv_mem ha

theorem card_preConj (g : G) (H : Subgroup G) : Nat.card (preConj g H) = Nat.card H :=
  Nat.card_congr
    { toFun := fun x => ⟨g * x * g⁻¹, x.2⟩
      invFun := fun y => ⟨g⁻¹ * y * g, by
        show g * (g⁻¹ * (y : G) * g) * g⁻¹ ∈ H
        have e : g * (g⁻¹ * (y : G) * g) * g⁻¹ = y := by group
        rw [e]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }

namespace OrthCfg

variable (C : OrthCfg G M Q)

include C

open Classical in
noncomputable def Lfin : Finset G := {C.elt p1, C.elt p2, C.elt p3, C.elt p4}

theorem elt_p_mem_Q1 (v : Vec5) (hv : v 0 = v 1) : C.elt v ∈ C.Q1 := C.mem_Q1_iff.2 ⟨v, hv, rfl⟩

theorem mem_Lfin_Q1 {x : G} (hx : x ∈ C.Lfin) : x ∈ C.Q1 := by
  classical
  simp only [Lfin, Finset.mem_insert, Finset.mem_singleton] at hx
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩, ⟨-, h4⟩⟩ := p_props
  rcases hx with rfl | rfl | rfl | rfl
  · exact C.elt_p_mem_Q1 _ h1
  · exact C.elt_p_mem_Q1 _ h2
  · exact C.elt_p_mem_Q1 _ h3
  · exact C.elt_p_mem_Q1 _ h4

theorem wt_cases_of_not_mem {x : G} (hx : x ∈ C.Q1) (hx1 : x ≠ 1) (hxL : x ∉ C.Lfin) :
    wt (C.vec x) = 1 ∨ wt (C.vec x) = 2 ∨ wt (C.vec x) = 4 ∨ wt (C.vec x) = 5 := by
  classical
  obtain ⟨v, hv, rfl⟩ := C.mem_Q1_iff.1 hx
  rw [C.vec_elt]
  have h0 : v ≠ 0 := fun h => hx1 (by rw [h, C.elt_zero])
  have h1 : wt v ≠ 0 := fun h => h0 (eq_zero_of_wt_zero v h)
  have h2 := wt_le_five v
  have h3 : wt v ≠ 3 := by
    intro h
    apply hxL
    simp only [Lfin, Finset.mem_insert, Finset.mem_singleton]
    rcases eq_p_of_wt3 v hv h with rfl | rfl | rfl | rfl <;> simp
  omega

theorem wt3_mem_Lfin {x : G} (hx : x ∈ C.Q1) (h : wt (C.vec x) = 3) : x ∈ C.Lfin := by
  classical
  obtain ⟨v, hv, rfl⟩ := C.mem_Q1_iff.1 hx
  rw [C.vec_elt] at h
  simp only [Lfin, Finset.mem_insert, Finset.mem_singleton]
  rcases eq_p_of_wt3 v hv h with rfl | rfl | rfl | rfl <;> simp

theorem Q1_le_of_Lfin_le {U : Subgroup G} (hU : ∀ x ∈ C.Lfin, x ∈ U) : C.Q1 ≤ U := by
  classical
  intro y hy
  obtain ⟨v, hv, rfl⟩ := C.mem_Q1_iff.1 hy
  obtain ⟨a, b, c, d, hvs⟩ := span_p v hv
  have m1 : C.elt p1 ∈ U := hU _ (by simp [Lfin])
  have m2 : C.elt p2 ∈ U := hU _ (by simp [Lfin])
  have m3 : C.elt p3 ∈ U := hU _ (by simp [Lfin])
  have m4 : C.elt p4 ∈ U := hU _ (by simp [Lfin])
  rw [hvs, C.elt_add, C.elt_add, C.elt_add]
  have e1 : C.elt (if a then p1 else 0) ∈ U := by
    split_ifs
    · exact m1
    · rw [C.elt_zero]; exact U.one_mem
  have e2 : C.elt (if b then p2 else 0) ∈ U := by
    split_ifs
    · exact m2
    · rw [C.elt_zero]; exact U.one_mem
  have e3 : C.elt (if c then p3 else 0) ∈ U := by
    split_ifs
    · exact m3
    · rw [C.elt_zero]; exact U.one_mem
  have e4 : C.elt (if d then p4 else 0) ∈ U := by
    split_ifs
    · exact m4
    · rw [C.elt_zero]; exact U.one_mem
  exact U.mul_mem (U.mul_mem (U.mul_mem e1 e2) e3) e4

open Classical in
theorem mem_M_of_counting [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    (hcent : ∀ v : Vec5, (wt v = 1 ∨ wt v = 2 ∨ wt v = 4 ∨ wt v = 5) →
      Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    {P : Subgroup G} (hQ1P : C.Q1 ≤ P) (hrel : C.Q1.relIndex P = 2) {g : G}
    (hgP : ∀ p ∈ P, g⁻¹ * p * g ∈ P) : g ∈ M := by
  by_contra hgM
  have hP32 : Nat.card P = 32 := by
    have := card_mul_relIndex' hQ1P
    rw [C.card_Q1, hrel] at this
    omega
  set B : Subgroup G := preConj g C.Q1 with hBd
  have hBP : B ≤ P := fun x hx => by
    have h1 : g * x * g⁻¹ ∈ P := hQ1P hx
    have := hgP _ h1
    simpa [mul_assoc] using this
  have hBcard : Nat.card B = 16 := (card_preConj g C.Q1).trans C.card_Q1
  have hBrel : B.relIndex P = 2 := by
    have := card_mul_relIndex' hBP
    rw [hBcard, hP32] at this
    omega
  set W : Subgroup G := C.Q1 ⊓ B with hWd
  have hWP : W ≤ P := inf_le_left.trans hQ1P
  have hWrel : W.relIndex P ≤ 4 := by
    have := Subgroup.relIndex_inf_le (H := C.Q1) (K := B) (L := P)
    rw [hrel, hBrel] at this
    exact this
  have hW8 : 8 ≤ Nat.card W := by
    have h1 := card_mul_relIndex' hWP
    rw [hP32] at h1
    by_contra hlt
    have h2 : Nat.card W * W.relIndex P ≤ 7 * 4 :=
      Nat.mul_le_mul (by omega) hWrel
    omega
  have hWdvd : Nat.card W ∣ 16 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : W ≤ C.Q1)
    rwa [C.card_Q1] at this
  set W' : Subgroup G := preConj g⁻¹ W with hW'd
  have hW'card : Nat.card W' = Nat.card W := card_preConj g⁻¹ W
  have hW'Q1 : W' ≤ C.Q1 := fun x hx => by
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ W := hx
    have h2 : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ ∈ C.Q1 := h1.2
    have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rwa [e] at h2
  let N : Set G := {x | x ∈ W ∧ x ≠ 1 ∧ x ∉ C.Lfin}
  let D : Set G := (W' : Set G) ∩ (C.Lfin : Set G)
  have hmap : ∀ x ∈ N, g * x * g⁻¹ ∈ D := by
    rintro x ⟨hxW, hx1, hxL⟩
    have hxQ1 : x ∈ C.Q1 := hxW.1
    have hgxQ1 : g * x * g⁻¹ ∈ C.Q1 := hxW.2
    refine ⟨?_, ?_⟩
    · show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ W
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e]
      exact hxW
    · have hw : wt (C.vec (g * x * g⁻¹)) = 3 := by
        by_contra hne
        have hc := C.wt_cases_of_not_mem hxQ1 hx1 hxL
        have hy1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
          have := congrArg (fun t => g⁻¹ * t * g) h
          simpa [mul_assoc] using this)
        have hw0 : C.vec (g * x * g⁻¹) ≠ 0 := fun h =>
          hy1 ((C.vec_eq_zero_iff (C.Q1_le_Q hgxQ1)).1 h)
        have hw5 := wt_le_five (C.vec (g * x * g⁻¹))
        have hwn0 : wt (C.vec (g * x * g⁻¹)) ≠ 0 := fun h => hw0 (eq_zero_of_wt_zero _ h)
        have hwc : wt (C.vec (g * x * g⁻¹)) = 1 ∨ wt (C.vec (g * x * g⁻¹)) = 2 ∨
            wt (C.vec (g * x * g⁻¹)) = 4 ∨ wt (C.vec (g * x * g⁻¹)) = 5 := by omega
        apply hgM
        refine C.fusion_ctrl hrig hc hwc (hcent _ hc) (hcent _ hwc) ?_
        rw [C.elt_vec (C.Q1_le_Q hxQ1), C.elt_vec (C.Q1_le_Q hgxQ1)]
      exact C.wt3_mem_Lfin hgxQ1 hw
  have hinj : Set.InjOn (fun x : G => g * x * g⁻¹) N := by
    intro a _ b _ hab
    have h1 : g * a * g⁻¹ = g * b * g⁻¹ := hab
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [h1]
      _ = b := by group
  have hND : N.ncard ≤ D.ncard :=
    Set.ncard_le_ncard_of_injOn (fun x : G => g * x * g⁻¹) hmap hinj
  have hWsub : (W : Set G) ⊆ (N ∪ ((W : Set G) ∩ (C.Lfin : Set G))) ∪ {1} := by
    intro x hx
    by_cases h1 : x = 1
    · right; exact h1
    · left
      by_cases h2 : x ∈ C.Lfin
      · right; exact ⟨hx, h2⟩
      · left; exact ⟨hx, h1, h2⟩
  have hWcount : Nat.card W ≤ N.ncard + ((W : Set G) ∩ (C.Lfin : Set G)).ncard + 1 := by
    have h1 := Set.ncard_le_ncard hWsub
    have h2 := Set.ncard_union_le (N ∪ ((W : Set G) ∩ (C.Lfin : Set G))) {1}
    have h3 := Set.ncard_union_le N ((W : Set G) ∩ (C.Lfin : Set G))
    rw [Set.ncard_singleton] at h2
    have h4 : Nat.card W = (W : Set G).ncard := rfl
    omega
  have hLcard : C.Lfin.card ≤ 4 := by
    unfold Lfin
    exact Finset.card_le_four
  have ha : ((W : Set G) ∩ (C.Lfin : Set G)).ncard ≤ 4 := by
    have := Set.ncard_le_ncard (Set.inter_subset_right (s := (W : Set G)) (t := (C.Lfin : Set G)))
    rw [Set.ncard_coe_finset] at this
    omega
  have hDsub : D ⊆ (C.Lfin : Set G) := Set.inter_subset_right
  have ha' : D.ncard ≤ 4 := by
    have := Set.ncard_le_ncard hDsub
    rw [Set.ncard_coe_finset] at this
    omega
  by_cases hLW : (C.Lfin : Set G) ⊆ (W : Set G)
  · have hQ1W : C.Q1 ≤ W := C.Q1_le_of_Lfin_le fun x hx => hLW hx
    have hWeq : Nat.card W = 16 := by
      have := Subgroup.card_le_of_le hQ1W
      rw [C.card_Q1] at this
      have h2 := Subgroup.card_le_of_le (inf_le_left : W ≤ C.Q1)
      rw [C.card_Q1] at h2
      omega
    have hsum : Nat.card W ≤ D.ncard + ((W : Set G) ∩ (C.Lfin : Set G)).ncard + 1 := by omega
    omega
  · have ha3 : ((W : Set G) ∩ (C.Lfin : Set G)).ncard ≤ 3 := by
      have hss : ((W : Set G) ∩ (C.Lfin : Set G)) ⊂ (C.Lfin : Set G) := by
        refine ⟨Set.inter_subset_right, fun h => hLW ?_⟩
        intro x hx
        exact (h hx).1
      have := Set.ncard_lt_ncard hss
      rw [Set.ncard_coe_finset] at this
      omega
    by_cases hLW' : (C.Lfin : Set G) ⊆ (W' : Set G)
    · exfalso
      have hQ1W' : C.Q1 ≤ W' := C.Q1_le_of_Lfin_le fun x hx => hLW' hx
      have hW'16 : Nat.card W' = 16 := by
        have h1 := Subgroup.card_le_of_le hQ1W'
        rw [C.card_Q1] at h1
        have h2 := Subgroup.card_le_of_le hW'Q1
        rw [C.card_Q1] at h2
        omega
      have hWeq : Nat.card W = 16 := by rw [← hW'card]; exact hW'16
      have hWQ : W = C.Q1 :=
        Subgroup.eq_of_le_of_card_ge (inf_le_left : W ≤ C.Q1) (by rw [hWeq, C.card_Q1])
      apply hLW
      intro x hx
      rw [SetLike.mem_coe, hWQ]
      exact C.mem_Lfin_Q1 hx
    · have ha'3 : D.ncard ≤ 3 := by
        have hss : D ⊂ (C.Lfin : Set G) := by
          refine ⟨Set.inter_subset_right, fun h => hLW' ?_⟩
          intro x hx
          exact (h hx).1
        have := Set.ncard_lt_ncard hss
        rw [Set.ncard_coe_finset] at this
        omega
      omega

theorem centralizer_le_M_cent [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    (h5 : ∀ v : Vec5, v ≠ 0 → ∃ P : Subgroup G,
      IsO2 (Subgroup.centralizer ({C.elt v} : Set G)) P ∧
        Subgroup.centralizer ({C.elt v} : Set G) ⊓ Subgroup.centralizer (P : Set G) ≤ P)
    {v : Vec5} (hv : wt v = 1 ∨ wt v = 2 ∨ wt v = 4 ∨ wt v = 5) :
    Subgroup.centralizer ({C.elt v} : Set G) ≤ M := by
  have h0 : wt (0 : Vec5) = 0 := by decide
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; omega
  rcases hv with h | h | h | h
  · exact hrig v ⟨hv0, Or.inl h⟩
  · exact C.centralizer_le_M_wt2 hrig h5 h
  · exact hrig v ⟨hv0, Or.inr (Or.inl h)⟩
  · exact hrig v ⟨hv0, Or.inr (Or.inr h)⟩

theorem centralizer_le_M_v3 [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    (h5 : ∀ v : Vec5, v ≠ 0 → ∃ P : Subgroup G,
      IsO2 (Subgroup.centralizer ({C.elt v} : Set G)) P ∧
        Subgroup.centralizer ({C.elt v} : Set G) ⊓ Subgroup.centralizer (P : Set G) ≤ P) :
    Subgroup.centralizer ({C.elt v3} : Set G) ≤ M := by
  by_contra hKM
  obtain ⟨P, hP, hC⟩ := h5 v3 (by decide)
  obtain ⟨-, -, -, hPQ1, hrel⟩ := C.witness_structure hrig (Or.inr rfl) hP hC hKM
  have hQ1P : C.Q1 ≤ P := hPQ1 ▸ inf_le_left
  apply hKM
  intro g hg
  refine C.mem_M_of_counting hrig (fun v hv => C.centralizer_le_M_cent hrig h5 hv) hQ1P hrel ?_
  intro p hp
  have := hP.normal g⁻¹ (Subgroup.inv_mem _ hg) p hp
  simpa using this

theorem centralizer_le_M [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    (h5 : ∀ v : Vec5, v ≠ 0 → ∃ P : Subgroup G,
      IsO2 (Subgroup.centralizer ({C.elt v} : Set G)) P ∧
        Subgroup.centralizer ({C.elt v} : Set G) ⊓ Subgroup.centralizer (P : Set G) ≤ P)
    {v : Vec5} (hv : v ≠ 0) : Subgroup.centralizer ({C.elt v} : Set G) ≤ M := by
  have h1 := wt_le_five v
  have h2 : wt v ≠ 0 := fun h => hv (eq_zero_of_wt_zero v h)
  by_cases h3 : wt v = 3
  · obtain ⟨m, hm, hmv⟩ := C.exists_conj_of_wt_eq (v := v3) (w := v) (by rw [wt_v3, h3])
    exact C.centralizer_le_M_of_conj hm hmv (C.centralizer_le_M_v3 hrig h5)
  · exact C.centralizer_le_M_cent hrig h5 (by omega)

end OrthCfg

end CFSG.CGT.PushingUpLit.Orth
