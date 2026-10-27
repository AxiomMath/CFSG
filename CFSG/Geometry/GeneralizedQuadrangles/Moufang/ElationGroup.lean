module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.RootGroups
public import CFSG.Quasithin.Recognition.Stroth.MoufangTitsAxioms
public import CFSG.Geometry.GeneralizedPolygons.Geodesic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.GH74.BNPair
open CFSG.Geometry.GeneralizedPolygons
open scoped Pointwise

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

section Definition

variable (H : Type) [Group H] [MulAction H V]

@[expose] def elationGroup (Γ : SimpleGraph V) (v : ZMod 8 → V) : Subgroup H :=
  Subgroup.closure ((rootGroup H Γ (v 6) (v 7) (v 0) : Set H) ∪
    (rootGroup H Γ (v 7) (v 0) (v 1) : Set H) ∪ (rootGroup H Γ (v 0) (v 1) (v 2) : Set H))

end Definition

section Main

variable {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem whorlGroup_fix_self (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {p : V} {θ : H}
    (hθ : θ ∈ whorlGroup H Γ p) : θ • p = p := by
  classical
  have h3 : 3 ≤ (Γ.neighborFinset p).card := by
    rw [card_neighborFinset_eq_degree]
    exact hT p
  obtain ⟨L₁, hL₁, L₂, hL₂, hL₁₂⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (Γ.neighborFinset p).card)
  rw [mem_neighborFinset] at hL₁ hL₂
  have hfix₁ : θ • L₁ = L₁ := (mem_fixingSubgroup_iff H).mp hθ L₁ hL₁
  have hfix₂ : θ • L₂ = L₂ := (mem_fixingSubgroup_iff H).mp hθ L₂ hL₂
  have hdist : Γ.dist L₁ L₂ = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hL₁.symm hL₂ hL₁₂
  have hθ₁ : Γ.Adj L₁ (θ • p) := by
    have h := (GraphAction.adj_smul θ p L₁).mpr hL₁
    simpa [hfix₁] using h.symm
  have hθ₂ : Γ.Adj L₂ (θ • p) := by
    have h := (GraphAction.adj_smul θ p L₂).mpr hL₂
    simpa [hfix₂] using h.symm
  exact (existsUnique_commonNeighbor hP hdist).unique ⟨hθ₁, hθ₂⟩ ⟨hL₁.symm, hL₂.symm⟩

theorem elationGroup_le_whorlGroup (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) :
    elationGroup H Γ v ≤ whorlGroup H Γ (v 0) := by
  refine (Subgroup.closure_le (whorlGroup H Γ (v 0))).mpr ?_
  intro x hx
  simp only [Set.mem_union] at hx
  rcases hx with (hx | hx) | hx
  · exact ((mem_rootGroup H).mp hx).2.2
  · exact ((mem_rootGroup H).mp hx).2.1
  · exact ((mem_rootGroup H).mp hx).1

theorem aptRoot_eq_rootGroup (v : ZMod 8 → V) (k : ℤ) :
    aptRoot H Γ 4 v k =
      rootGroup H Γ (v ((k + 1 : ℤ) : ZMod 8)) (v ((k + 2 : ℤ) : ZMod 8))
        (v ((k + 3 : ℤ) : ZMod 8)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_rootGroup]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      exact (mem_aptRoot.mp hx) 1 (by norm_num) (by norm_num) w hw
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      exact (mem_aptRoot.mp hx) 2 (by norm_num) (by norm_num) w hw
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      exact (mem_aptRoot.mp hx) 3 (by norm_num) (by norm_num) w hw
  · intro x hx
    rw [mem_aptRoot]
    intro i hi1 hi3 w hw
    interval_cases i
    · exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hx).1 w hw
    · exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hx).2.1 w hw
    · exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hx).2.2 w hw

theorem rootGroup_five (v : ZMod 8 → V) :
    rootGroup H Γ (v 6) (v 7) (v 0) = aptRoot H Γ 4 v 5 := by
  rw [aptRoot_eq_rootGroup]
  have h1 : ((5 + 1 : ℤ) : ZMod 8) = 6 := by decide
  have h2 : ((5 + 2 : ℤ) : ZMod 8) = 7 := by decide
  have h3 : ((5 + 3 : ℤ) : ZMod 8) = 0 := by decide
  rw [h1, h2, h3]

theorem rootGroup_six (v : ZMod 8 → V) :
    rootGroup H Γ (v 7) (v 0) (v 1) = aptRoot H Γ 4 v 6 := by
  rw [aptRoot_eq_rootGroup]
  have h1 : ((6 + 1 : ℤ) : ZMod 8) = 7 := by decide
  have h2 : ((6 + 2 : ℤ) : ZMod 8) = 0 := by decide
  have h3 : ((6 + 3 : ℤ) : ZMod 8) = 1 := by decide
  rw [h1, h2, h3]

theorem rootGroup_seven (v : ZMod 8 → V) :
    rootGroup H Γ (v 0) (v 1) (v 2) = aptRoot H Γ 4 v 7 := by
  rw [aptRoot_eq_rootGroup]
  have h1 : ((7 + 1 : ℤ) : ZMod 8) = 0 := by decide
  have h2 : ((7 + 2 : ℤ) : ZMod 8) = 1 := by decide
  have h3 : ((7 + 3 : ℤ) : ZMod 8) = 2 := by decide
  rw [h1, h2, h3]

section OppositeCount

theorem card_opposite_of_adj (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {x y z : V}
    (hxy : Γ.Adj x y) (hyz : Γ.Adj y z) :
    (Finset.univ.filter fun w => Γ.dist x w = 4).card =
      (Γ.degree y - 1) ^ 2 * (Γ.degree z - 1) := by
  classical
  obtain ⟨c⟩ := hP.isBipartite
  obtain ⟨s, t, hs, ht, -, hdeg⟩ := hP.exists_order (by norm_num) hT c
  have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hcy : c x ≠ c y := c.valid hxy
  have hcz : c z = c x := by
    have hne := c.valid hyz
    rcases hfin (c x) with hx | hx <;> rcases hfin (c y) with hy | hy <;>
      rcases hfin (c z) with hz | hz <;> simp_all
  rcases hfin (c x) with hx0 | hx1
  · have hy1 : c y = 1 := by
      rcases hfin (c y) with hy | hy
      · exact absurd (hx0.trans hy.symm) hcy
      · exact hy
    have hz0 : c z = 0 := by rw [hcz, hx0]
    have hdy : Γ.degree y = s + 1 := by
      rw [hdeg y, if_neg (by rw [hy1]; decide)]
    have hdz : Γ.degree z = t + 1 := by
      rw [hdeg z, if_pos hz0]
    have hcard := card_opposite hP hT c hdeg hx0
    rw [hcard, hdy, hdz]
    simp
  · have hy0 : c y = 0 := by
      rcases hfin (c y) with hy | hy
      · exact hy
      · exact absurd (hx1.trans hy.symm) hcy
    have hz1 : c z = 1 := by rw [hcz, hx1]
    let dc : Γ.Coloring (Fin 2) := SimpleGraph.Coloring.mk (fun v => 1 - c v) (by
      intro v w h
      have hne := c.valid h
      have hfin' : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
      rcases hfin' (c v) with hv | hv <;> rcases hfin' (c w) with hw | hw
      · exact absurd (hv.trans hw.symm) hne
      · rw [hv, hw]; simp
      · rw [hv, hw]; simp
      · exact absurd (hv.trans hw.symm) hne)
    have hdeg' : ∀ v, Γ.degree v = if dc v = 0 then s + 1 else t + 1 := by
      intro v
      rcases hfin (c v) with hv | hv
      · rw [hdeg v, if_pos hv]
        have hdc : dc v ≠ 0 := by
          show 1 - c v ≠ 0
          rw [hv]; decide
        rw [if_neg hdc]
      · rw [hdeg v, if_neg (by rw [hv]; decide)]
        have hdc : dc v = 0 := by
          show 1 - c v = 0
          rw [hv]; decide
        rw [if_pos hdc]
    have hdcx : dc x = 0 := by
      show 1 - c x = 0
      rw [hx1]; decide
    have hcard := card_opposite (hP := hP) (hT := hT) (c := dc) (s := t) (t := s)
      (hdeg := hdeg') (x := x) (hx := hdcx)
    have hdy : Γ.degree y = t + 1 := by rw [hdeg y, if_pos hy0]
    have hdz : Γ.degree z = s + 1 := by
      rw [hdeg z, if_neg (by rw [hz1]; decide)]
    rw [hcard, hdy, hdz]
    simp

end OppositeCount


theorem mem_elationGroup_iff_exists_prod (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) {x : H} :
    x ∈ elationGroup H Γ v ↔
      ∃ a ∈ rootGroup H Γ (v 6) (v 7) (v 0),
        ∃ b ∈ rootGroup H Γ (v 7) (v 0) (v 1),
          ∃ c ∈ rootGroup H Γ (v 0) (v 1) (v 2), a * b * c = x := by
  classical
  let U5 := rootGroup H Γ (v 6) (v 7) (v 0)
  let U6 := rootGroup H Γ (v 7) (v 0) (v 1)
  let U7 := rootGroup H Γ (v 0) (v 1) (v 2)
  have a0 : (aptPath hv.2 6) 0 = v 6 := by
    rw [aptPath_apply hv.2 6 (i := 0) (by norm_num)]
    exact congrArg v (by decide)
  have a1 : (aptPath hv.2 6) 1 = v 7 := by
    rw [aptPath_apply hv.2 6 (i := 1) (by norm_num)]
    exact congrArg v (by decide)
  have a2 : (aptPath hv.2 6) 2 = v 0 := by
    rw [aptPath_apply hv.2 6 (i := 2) (by norm_num)]
    exact congrArg v (by decide)
  have a3 : (aptPath hv.2 6) 3 = v 1 := by
    rw [aptPath_apply hv.2 6 (i := 3) (by norm_num)]
    exact congrArg v (by decide)
  have a4 : (aptPath hv.2 6) 4 = v 2 := by
    rw [aptPath_apply hv.2 6 (i := 4) (by norm_num)]
    exact congrArg v (by decide)
  have c0 : ((aptPath hv.2 6).take 3 (by norm_num)) 0 = v 6 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 6) 3 (by norm_num) (i := 0) (by norm_num), a0]
  have c1 : ((aptPath hv.2 6).take 3 (by norm_num)) 1 = v 7 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 6) 3 (by norm_num) (i := 1) (by norm_num), a1]
  have c2 : ((aptPath hv.2 6).take 3 (by norm_num)) 2 = v 0 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 6) 3 (by norm_num) (i := 2) (by norm_num), a2]
  have c3 : ((aptPath hv.2 6).take 3 (by norm_num)) 3 = v 1 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 6) 3 (by norm_num) (i := 3) (by norm_num), a3]
  have b0 : (aptPath hv.2 7) 0 = v 7 := by
    rw [aptPath_apply hv.2 7 (i := 0) (by norm_num)]
    exact congrArg v (by decide)
  have b1 : (aptPath hv.2 7) 1 = v 0 := by
    rw [aptPath_apply hv.2 7 (i := 1) (by norm_num)]
    exact congrArg v (by decide)
  have b2 : (aptPath hv.2 7) 2 = v 1 := by
    rw [aptPath_apply hv.2 7 (i := 2) (by norm_num)]
    exact congrArg v (by decide)
  have b3 : (aptPath hv.2 7) 3 = v 2 := by
    rw [aptPath_apply hv.2 7 (i := 3) (by norm_num)]
    exact congrArg v (by decide)
  have d0 : ((aptPath hv.2 7).take 3 (by norm_num)) 0 = v 7 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 7) 3 (by norm_num) (i := 0) (by norm_num), b0]
  have d1 : ((aptPath hv.2 7).take 3 (by norm_num)) 1 = v 0 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 7) 3 (by norm_num) (i := 1) (by norm_num), b1]
  have d2 : ((aptPath hv.2 7).take 3 (by norm_num)) 2 = v 1 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 7) 3 (by norm_num) (i := 2) (by norm_num), b2]
  have d3 : ((aptPath hv.2 7).take 3 (by norm_num)) 3 = v 2 := by
    rw [GPath.take_apply_of_le (aptPath hv.2 7) 3 (by norm_num) (i := 3) (by norm_num), b3]
  have h56 : ∀ a ∈ U5, ∀ b ∈ U6, Commute a b := by
    intro a ha b hb
    let p : GPath Γ 3 := (aptPath hv.2 6).take 3 (by norm_num)
    have hp : p.NoBack := (aptPath_noBack (by norm_num) hv 6).take 3 (by norm_num)
    have hg : a ∈ rootGroup H Γ (p 0) (p 1) (p 2) := by
      dsimp [p]
      rw [c0, c1, c2]
      exact ha
    have hh : b ∈ rootGroup H Γ (p 1) (p 2) (p 3) := by
      dsimp [p]
      rw [c1, c2, c3]
      exact hb
    exact commute_of_mem_rootGroup_consecutive hP hT p hp hg hh
  have h67 : ∀ b ∈ U6, ∀ c ∈ U7, Commute b c := by
    intro b hb c hc
    let p : GPath Γ 3 := (aptPath hv.2 7).take 3 (by norm_num)
    have hp : p.NoBack := (aptPath_noBack (by norm_num) hv 7).take 3 (by norm_num)
    have hg : b ∈ rootGroup H Γ (p 0) (p 1) (p 2) := by
      dsimp [p]
      rw [d0, d1, d2]
      exact hb
    have hh : c ∈ rootGroup H Γ (p 1) (p 2) (p 3) := by
      dsimp [p]
      rw [d1, d2, d3]
      exact hc
    exact commute_of_mem_rootGroup_consecutive hP hT p hp hg hh
  have h57 : ∀ a ∈ U5, ∀ c ∈ U7, a * c * a⁻¹ * c⁻¹ ∈ U6 := by
    intro a ha c hc
    let p : GPath Γ 4 := aptPath hv.2 6
    have hp : p.NoBack := aptPath_noBack (by norm_num) hv 6
    have hg : a ∈ rootGroup H Γ (p 0) (p 1) (p 2) := by
      dsimp [p]
      rw [a0, a1, a2]
      exact ha
    have hh : c ∈ rootGroup H Γ (p 2) (p 3) (p 4) := by
      dsimp [p]
      rw [a2, a3, a4]
      exact hc
    have h := commutatorElement_mem_rootGroup p hg hh
    have hU6 : rootGroup H Γ (p 1) (p 2) (p 3) = U6 := by
      dsimp [p, U6]
      rw [a1, a2, a3]
    rwa [hU6] at h
  let P : Subgroup H :=
    { carrier := {y | ∃ a ∈ U5, ∃ b ∈ U6, ∃ c ∈ U7, a * b * c = y}
      one_mem' := ⟨1, U5.one_mem, 1, U6.one_mem, 1, U7.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨a1, ha1, b1, hb1, c1, hc1, rfl⟩ ⟨a2, ha2, b2, hb2, c2, hc2, rfl⟩
        let w1 : H := c1 * a2 * c1⁻¹ * a2⁻¹
        have hw1 : w1 ∈ U6 := by
          dsimp [w1]
          have h := U6.inv_mem (h57 a2 ha2 c1 hc1)
          convert h using 1
          group
        have hbw : b1 * w1 ∈ U6 := U6.mul_mem hb1 hw1
        have hsw : (b1 * w1) * a2 = a2 * (b1 * w1) :=
          (h56 a2 ha2 _ hbw).eq.symm
        have hcb : c1 * b2 = b2 * c1 := (h67 b2 hb2 c1 hc1).eq.symm
        refine ⟨a1 * a2, U5.mul_mem ha1 ha2, (b1 * w1) * b2, U6.mul_mem hbw hb2,
          c1 * c2, U7.mul_mem hc1 hc2, ?_⟩
        symm
        calc
          a1 * b1 * c1 * (a2 * b2 * c2)
              = a1 * b1 * (c1 * a2) * b2 * c2 := by group
          _ = a1 * b1 * (w1 * a2 * c1) * b2 * c2 := by
                rw [show c1 * a2 = w1 * a2 * c1 by dsimp [w1]; group]
          _ = a1 * ((b1 * w1) * a2) * c1 * b2 * c2 := by group
          _ = a1 * (a2 * (b1 * w1)) * c1 * b2 * c2 := by rw [hsw]
          _ = a1 * a2 * (b1 * w1) * (c1 * b2) * c2 := by group
          _ = a1 * a2 * (b1 * w1) * (b2 * c1) * c2 := by rw [hcb]
          _ = a1 * a2 * ((b1 * w1) * b2) * (c1 * c2) := by group
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, c, hc, rfl⟩
        let w2 : H := c⁻¹ * a⁻¹ * c * a
        have hw2 : w2 ∈ U6 := by
          dsimp [w2]
          have h := h57 a⁻¹ (U5.inv_mem ha) c⁻¹ (U7.inv_mem hc)
          have h' := U6.inv_mem h
          convert h' using 1
          group
        have hbw2 : b⁻¹ * w2 ∈ U6 := U6.mul_mem (U6.inv_mem hb) hw2
        have hbc : b⁻¹ * c⁻¹ = c⁻¹ * b⁻¹ :=
          (h67 b⁻¹ (U6.inv_mem hb) c⁻¹ (U7.inv_mem hc)).eq
        have hsw2 : (b⁻¹ * w2) * a⁻¹ = a⁻¹ * (b⁻¹ * w2) :=
          (h56 a⁻¹ (U5.inv_mem ha) _ hbw2).eq.symm
        refine ⟨a⁻¹, U5.inv_mem ha, b⁻¹ * w2, hbw2, c⁻¹, U7.inv_mem hc, ?_⟩
        symm
        calc
          (a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹ := by group
          _ = b⁻¹ * c⁻¹ * a⁻¹ := by rw [← hbc]
          _ = b⁻¹ * (c⁻¹ * a⁻¹) := by group
          _ = b⁻¹ * (w2 * a⁻¹ * c⁻¹) := by
                rw [show c⁻¹ * a⁻¹ = w2 * a⁻¹ * c⁻¹ by dsimp [w2]; group]
          _ = (b⁻¹ * w2) * a⁻¹ * c⁻¹ := by group
          _ = a⁻¹ * (b⁻¹ * w2) * c⁻¹ := by rw [hsw2]
    }
  have hEP : elationGroup H Γ v = P := by
    refine le_antisymm ?_ ?_
    · rw [elationGroup]
      refine (Subgroup.closure_le P).mpr ?_
      intro y hy
      simp only [Set.mem_union] at hy
      rcases hy with (hy | hy) | hy
      · exact ⟨y, by simpa [U5] using hy, 1, U6.one_mem, 1, U7.one_mem, by simp⟩
      · exact ⟨1, U5.one_mem, y, by simpa [U6] using hy, 1, U7.one_mem, by simp⟩
      · exact ⟨1, U5.one_mem, 1, U6.one_mem, y, by simpa [U7] using hy, by simp⟩
    · intro y hy
      rw [elationGroup]
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inl (Or.inl (by simpa [U5] using ha))))
        (Subgroup.subset_closure (Or.inl (Or.inr (by simpa [U6] using hb)))))
        (Subgroup.subset_closure (Or.inr (by simpa [U7] using hc)))
  rw [hEP]
  exact Iff.rfl

theorem eq_of_prod_eq_prod (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) {a₁ a₂ b₁ b₂ c₁ c₂ : H}
    (ha₁ : a₁ ∈ rootGroup H Γ (v 6) (v 7) (v 0))
    (ha₂ : a₂ ∈ rootGroup H Γ (v 6) (v 7) (v 0))
    (hb₁ : b₁ ∈ rootGroup H Γ (v 7) (v 0) (v 1))
    (hb₂ : b₂ ∈ rootGroup H Γ (v 7) (v 0) (v 1))
    (hc₁ : c₁ ∈ rootGroup H Γ (v 0) (v 1) (v 2))
    (hc₂ : c₂ ∈ rootGroup H Γ (v 0) (v 1) (v 2))
    (heq : a₁ * b₁ * c₁ = a₂ * b₂ * c₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  classical
  have ha₁' : a₁ ∈ aptRoot H Γ 4 v 5 := by rwa [rootGroup_five] at ha₁
  have ha₂' : a₂ ∈ aptRoot H Γ 4 v 5 := by rwa [rootGroup_five] at ha₂
  have hb₁' : b₁ ∈ aptRoot H Γ 4 v 6 := by rwa [rootGroup_six] at hb₁
  have hb₂' : b₂ ∈ aptRoot H Γ 4 v 6 := by rwa [rootGroup_six] at hb₂
  have hc₁' : c₁ ∈ aptRoot H Γ 4 v 7 := by rwa [rootGroup_seven] at hc₁
  have hc₂' : c₂ ∈ aptRoot H Γ 4 v 7 := by rwa [rootGroup_seven] at hc₂
  have hlist : intList (5 : ℤ) 7 = [5, 6, 7] := by decide
  have h65 : (6 : ℤ) ≠ 5 := by norm_num
  have h75 : (7 : ℤ) ≠ 5 := by norm_num
  have h76 : (7 : ℤ) ≠ 6 := by norm_num
  let f : ℤ → H := fun k => if k = 5 then a₁ else if k = 6 then b₁ else c₁
  let g : ℤ → H := fun k => if k = 5 then a₂ else if k = 6 then b₂ else c₂
  have hf : ∀ k ∈ intList (5 : ℤ) 7, f k ∈ aptRoot H Γ 4 v k := by
    intro k hk
    rw [hlist] at hk
    simp at hk
    rcases hk with rfl | rfl | rfl
    · simpa [f] using ha₁'
    · simpa [f, h65] using hb₁'
    · simpa [f, h65, h75, h76] using hc₁'
  have hg : ∀ k ∈ intList (5 : ℤ) 7, g k ∈ aptRoot H Γ 4 v k := by
    intro k hk
    rw [hlist] at hk
    simp at hk
    rcases hk with rfl | rfl | rfl
    · simpa [g] using ha₂'
    · simpa [g, h65] using hb₂'
    · simpa [g, h65, h75, h76] using hc₂'
  have hprod : ((intList (5 : ℤ) 7).map f).prod = ((intList (5 : ℤ) 7).map g).prod := by
    rw [hlist]
    simpa [f, g, mul_assoc] using heq
  have huniq := aptRoot_prod_unique hv (by norm_num : 3 ≤ 4) hP hT (a := (5 : ℤ)) (b := 7)
    (by norm_num) (by norm_num) hf hg hprod
  refine ⟨?_, ?_, ?_⟩
  · have h := huniq 5 (by rw [hlist]; simp)
    simpa [f, g] using h
  · have h := huniq 6 (by rw [hlist]; simp)
    simpa [f, g, h65] using h
  · have h := huniq 7 (by rw [hlist]; simp)
    simpa [f, g, h65, h75, h76] using h

theorem card_elationGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) :
    Nat.card (elationGroup H Γ v) =
      (Γ.degree (v 1) - 1) * (Γ.degree (v 2) - 1) * (Γ.degree (v 3) - 1) := by
  classical
  let U5 := rootGroup H Γ (v 6) (v 7) (v 0)
  let U6 := rootGroup H Γ (v 7) (v 0) (v 1)
  let U7 := rootGroup H Γ (v 0) (v 1) (v 2)
  have e51 : (aptPath hv.2 5) 1 = v 6 := by
    rw [aptPath_apply hv.2 5 (i := 1) (by norm_num)]
    exact congrArg v (by decide)
  have e52 : (aptPath hv.2 5) 2 = v 7 := by
    rw [aptPath_apply hv.2 5 (i := 2) (by norm_num)]
    exact congrArg v (by decide)
  have e53 : (aptPath hv.2 5) 3 = v 0 := by
    rw [aptPath_apply hv.2 5 (i := 3) (by norm_num)]
    exact congrArg v (by decide)
  have e54 : (aptPath hv.2 5) 4 = v 1 := by
    rw [aptPath_apply hv.2 5 (i := 4) (by norm_num)]
    exact congrArg v (by decide)
  have e61 : (aptPath hv.2 6) 1 = v 7 := by
    rw [aptPath_apply hv.2 6 (i := 1) (by norm_num)]
    exact congrArg v (by decide)
  have e62 : (aptPath hv.2 6) 2 = v 0 := by
    rw [aptPath_apply hv.2 6 (i := 2) (by norm_num)]
    exact congrArg v (by decide)
  have e63 : (aptPath hv.2 6) 3 = v 1 := by
    rw [aptPath_apply hv.2 6 (i := 3) (by norm_num)]
    exact congrArg v (by decide)
  have e64 : (aptPath hv.2 6) 4 = v 2 := by
    rw [aptPath_apply hv.2 6 (i := 4) (by norm_num)]
    exact congrArg v (by decide)
  have e71 : (aptPath hv.2 7) 1 = v 0 := by
    rw [aptPath_apply hv.2 7 (i := 1) (by norm_num)]
    exact congrArg v (by decide)
  have e72 : (aptPath hv.2 7) 2 = v 1 := by
    rw [aptPath_apply hv.2 7 (i := 2) (by norm_num)]
    exact congrArg v (by decide)
  have e73 : (aptPath hv.2 7) 3 = v 2 := by
    rw [aptPath_apply hv.2 7 (i := 3) (by norm_num)]
    exact congrArg v (by decide)
  have e74 : (aptPath hv.2 7) 4 = v 3 := by
    rw [aptPath_apply hv.2 7 (i := 4) (by norm_num)]
    exact congrArg v (by decide)
  have hcard5 : Nat.card U5 = Γ.degree (v 1) - 1 := by
    let p : GPath Γ 4 := aptPath hv.2 5
    have hp : p.NoBack := aptPath_noBack (by norm_num) hv 5
    have h := card_rootGroup (H := H) hP hT hM p hp
    have hg : rootGroup H Γ (p 1) (p 2) (p 3) = U5 := by
      dsimp [p, U5]
      rw [e51, e52, e53]
    have h4 : p 4 = v 1 := by dsimp [p]; exact e54
    rwa [hg, h4] at h
  have hcard6 : Nat.card U6 = Γ.degree (v 2) - 1 := by
    let p : GPath Γ 4 := aptPath hv.2 6
    have hp : p.NoBack := aptPath_noBack (by norm_num) hv 6
    have h := card_rootGroup (H := H) hP hT hM p hp
    have hg : rootGroup H Γ (p 1) (p 2) (p 3) = U6 := by
      dsimp [p, U6]
      rw [e61, e62, e63]
    have h4 : p 4 = v 2 := by dsimp [p]; exact e64
    rwa [hg, h4] at h
  have hcard7 : Nat.card U7 = Γ.degree (v 3) - 1 := by
    let p : GPath Γ 4 := aptPath hv.2 7
    have hp : p.NoBack := aptPath_noBack (by norm_num) hv 7
    have h := card_rootGroup (H := H) hP hT hM p hp
    have hg : rootGroup H Γ (p 1) (p 2) (p 3) = U7 := by
      dsimp [p, U7]
      rw [e71, e72, e73]
    have h4 : p 4 = v 3 := by dsimp [p]; exact e74
    rwa [hg, h4] at h
  let prodMap : (↥U5 × ↥U6 × ↥U7) → ↥(elationGroup H Γ v) := fun p =>
    ⟨(p.1 : H) * (p.2.1 : H) * (p.2.2 : H),
      (mem_elationGroup_iff_exists_prod hP hT v hv).mpr
        ⟨p.1, p.1.2, p.2.1, p.2.1.2, p.2.2, p.2.2.2, rfl⟩⟩
  have hinj : Function.Injective prodMap := by
    rintro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
    have heq : (a1 : H) * b1 * c1 = (a2 : H) * b2 * c2 := congrArg Subtype.val h
    obtain ⟨h1, h2, h3⟩ :=
      eq_of_prod_eq_prod hP hT v hv a1.2 a2.2 b1.2 b2.2 c1.2 c2.2 heq
    have h1' : a1 = a2 := Subtype.ext h1
    have h2' : b1 = b2 := Subtype.ext h2
    have h3' : c1 = c2 := Subtype.ext h3
    rw [h1', h2', h3']
  have hsurj : Function.Surjective prodMap := by
    intro x
    obtain ⟨a, ha, b, hb, c, hc, hx⟩ :=
      (mem_elationGroup_iff_exists_prod hP hT v hv).mp x.2
    refine ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ?_⟩
    exact Subtype.ext hx
  have hcard : Nat.card (elationGroup H Γ v) = Nat.card (↥U5 × ↥U6 × ↥U7) :=
    (Nat.card_congr (Equiv.ofBijective prodMap ⟨hinj, hsurj⟩)).symm
  rw [hcard, Nat.card_prod, Nat.card_prod, hcard5, hcard6, hcard7, Nat.mul_assoc]

theorem exists_mem_elationGroup_smul_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v)
    {w : V} (hw : Γ.dist (v 0) w = 4) :
    ∃ g ∈ elationGroup H Γ v, (g : H) • v 4 = w := by
  classical
  have h70 : Γ.Adj (v 7) (v 0) := by
    have h := hv.2 7
    have e : ((7 : ZMod 8) + 1) = 0 := by decide
    simpa [e] using h
  have hw7 : Γ.dist w (v 7) = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP hw h70.symm
  let z6 : V := proj hP hw7
  have hz6adj : Γ.Adj (v 7) z6 := proj_adj hP hw7
  have hwz6 : Γ.dist w z6 = 2 := proj_dist hP hw7
  let z5 : V := commonNeighbor hP hwz6
  have hwz5 : Γ.Adj w z5 := commonNeighbor_adj_left hP hwz6
  have hz5z6 : Γ.Adj z5 z6 := (commonNeighbor_adj_right hP hwz6).symm
  let z : ℤ → V := fun s =>
    if s = 4 then w else if s = 5 then z5 else if s = 6 then z6
      else if s = 7 then v 7 else v 0
  have hz4 : z 4 = w := by simp [z]
  have hz5 : z 5 = z5 := by simp [z]
  have hz6 : z 6 = z6 := by simp [z]
  have hz7 : z 7 = v 7 := by simp [z]
  have hz8 : z 8 = v 0 := by simp [z]
  have hzb : z 7 = apt (n := 4) v 7 := by
    rw [hz7]
    show v 7 = v ((7 : ℤ) : ZMod 8)
    exact (congrArg v (by decide)).symm
  have hzb1 : z 8 = apt (n := 4) v 8 := by
    rw [hz8]
    show v 0 = v ((8 : ℤ) : ZMod 8)
    exact congrArg v (by decide : (0 : ZMod 8) = ((8 : ℤ) : ZMod 8))
  have hadj : ∀ s : ℤ, 4 ≤ s → s ≤ 7 → Γ.Adj (z s) (z (s + 1)) := by
    intro s hs4 hs7
    interval_cases s
    · simpa [hz4, hz5] using hwz5
    · simpa [hz5, hz6] using hz5z6
    · simpa [hz6, hz7] using hz6adj.symm
    · simpa [hz7, hz8] using h70
  have hnb : ∀ s : ℤ, 4 ≤ s → s + 2 ≤ 8 → z s ≠ z (s + 2) := by
    intro s hs4 hs8
    have hs6 : s ≤ 6 := by omega
    interval_cases s
    · rw [hz4, show (4 : ℤ) + 2 = 6 by norm_num, hz6]
      intro h
      have hd : Γ.dist w z6 = 0 := by rw [h, SimpleGraph.dist_self]
      omega
    · rw [hz5, show (5 : ℤ) + 2 = 7 by norm_num, hz7]
      intro h
      have hd : Γ.dist w (v 7) = 1 := by
        rw [h] at hwz5
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hwz5
      omega
    · rw [hz6, show (6 : ℤ) + 2 = 8 by norm_num, hz8]
      intro h
      have hd : Γ.dist w z6 = 4 := by
        rw [h, SimpleGraph.dist_comm]
        exact hw
      omega
  obtain ⟨y, hy, -, hyz⟩ := exists_smul_apt_path (D := H) (n := 4) (t := v) hv
    (by norm_num) hM (a := (4 : ℤ)) (b := (7 : ℤ)) (by norm_num) (by norm_num)
    z hzb hzb1 hadj hnb
  have hsup_le : (⨆ s ∈ Set.Ioc (4 : ℤ) 7, aptRoot H Γ 4 v s) ≤ elationGroup H Γ v := by
    refine iSup_le fun s => iSup_le fun hs => ?_
    have hs' : s = 5 ∨ s = 6 ∨ s = 7 := by
      obtain ⟨h1, h2⟩ := hs
      omega
    rcases hs' with rfl | rfl | rfl
    · rw [← rootGroup_five]
      intro x hx
      exact Subgroup.subset_closure (Or.inl (Or.inl hx))
    · rw [← rootGroup_six]
      intro x hx
      exact Subgroup.subset_closure (Or.inl (Or.inr hx))
    · rw [← rootGroup_seven]
      intro x hx
      exact Subgroup.subset_closure (Or.inr hx)
  refine ⟨y, hsup_le hy, ?_⟩
  have h4apt : apt (n := 4) v 4 = v 4 := by
    show v ((4 : ℤ) : ZMod 8) = v 4
    exact congrArg v (by decide)
  rw [← h4apt, hyz 4 (by norm_num) (by norm_num), hz4]

theorem existsUnique_elationGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) {w : V}
    (hw : Γ.dist (v 0) w = 4) : ∃! g : elationGroup H Γ v, (g : H) • v 4 = w := by
  classical
  haveI : Fintype ↥(elationGroup H Γ v) :=
    Fintype.ofInjective (fun g : ↥(elationGroup H Γ v) => fun y : V => (g : H) • y) (by
      intro g h hgh
      apply Subtype.ext
      exact eq_of_smul_eq_smul (m₁ := (g : H)) (m₂ := (h : H)) (fun y => congrFun hgh y))
  have a0apt : apt (n := 4) v 0 = v 0 := by
    show v ((0 : ℤ) : ZMod 8) = v 0
    exact congrArg v (by decide)
  have a4apt : apt (n := 4) v 4 = v 4 := by
    show v ((4 : ℤ) : ZMod 8) = v 4
    exact congrArg v (by decide)
  have hv4 : Γ.dist (v 0) (v 4) = 4 := by
    have h := hP.isGeodesic_of_noBack (by norm_num : 4 ≤ 4)
      (aptPath_noBack (by norm_num) hv 0)
    simpa [GPath.IsGeodesic, a0apt, a4apt] using h
  have h01 : Γ.Adj (v 0) (v 1) := by
    have h := hv.2 0
    have e : ((0 : ZMod 8) + 1) = 1 := by decide
    simpa [e] using h
  have h12 : Γ.Adj (v 1) (v 2) := by
    have h := hv.2 1
    have e : ((1 : ZMod 8) + 1) = 2 := by decide
    simpa [e] using h
  have h23 : Γ.Adj (v 2) (v 3) := by
    have h := hv.2 2
    have e : ((2 : ZMod 8) + 1) = 3 := by decide
    simpa [e] using h
  let O := {y : V // Γ.dist (v 0) y = 4}
  have hfix0 : ∀ g : elationGroup H Γ v, (g : H) • v 0 = v 0 := fun g =>
    whorlGroup_fix_self hP hT (elationGroup_le_whorlGroup v hv g.2)
  let f : ↥(elationGroup H Γ v) → O := fun g =>
    ⟨(g : H) • v 4, by
      have hd := GPath.dist_smul hP.connected (g : H) (v 0) (v 4)
      rwa [hfix0 g, hv4] at hd⟩
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, hgw⟩ := exists_mem_elationGroup_smul_eq hP hT hM v hv x.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgw⟩
  have hcardE : Fintype.card ↥(elationGroup H Γ v) =
      (Γ.degree (v 1) - 1) * (Γ.degree (v 2) - 1) * (Γ.degree (v 3) - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_elationGroup hP hT hM v hv
  have hcardO : Fintype.card O =
      (Γ.degree (v 1) - 1) ^ 2 * (Γ.degree (v 2) - 1) := by
    dsimp [O]
    rw [Fintype.card_subtype]
    exact card_opposite_of_adj hP hT h01 h12
  have hdeg13 : Γ.degree (v 1) = Γ.degree (v 3) :=
    hP.degree_eq_of_adj_of_adj (by norm_num) hT h12.symm h23
  have hcardEq : Fintype.card ↥(elationGroup H Γ v) = Fintype.card O := by
    rw [hcardE, hcardO, hdeg13]
    ring
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcardEq⟩
  obtain ⟨g0, hg0, hg0w⟩ := exists_mem_elationGroup_smul_eq hP hT hM v hv hw
  refine ⟨⟨g0, hg0⟩, hg0w, ?_⟩
  intro g hg
  apply hbij.1
  exact Subtype.ext (hg.trans hg0w.symm)

end Main

end CFSG.Geometry.GeneralizedQuadrangles

