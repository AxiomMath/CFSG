module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Tri3

variable {Q : Type*} [Group Q]

structure Tri3 (C0 C1 C2 : Subgroup Q) : Prop where
  comm01 : ∀ u ∈ C0, ∀ w ∈ C1, u * w = w * u
  comm02 : ∀ u ∈ C0, ∀ w ∈ C2, u * w = w * u
  comm12 : ∀ u ∈ C1, ∀ w ∈ C2, u * w = w * u
  cen0 : ∀ z ∈ C0, (∀ w ∈ C0, z * w = w * z) → z = 1
  cen1 : ∀ z ∈ C1, (∀ w ∈ C1, z * w = w * z) → z = 1
  cen2 : ∀ z ∈ C2, (∀ w ∈ C2, z * w = w * z) → z = 1

namespace Tri3

variable {C0 C1 C2 : Subgroup Q} (T : Tri3 C0 C1 C2)

include T

theorem sup01_comm2 {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ C0) (h1 : P1 ≤ C1) (h2 : P2 ≤ C2) :
    ∀ p ∈ P0 ⊔ P1, ∀ r ∈ P2, p * r = r * p := by
  intro p hp r hr
  have hle : P0 ⊔ P1 ≤ Subgroup.centralizer ({r} : Set Q) := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact T.comm02 u (h0 hu) r (h2 hr)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact T.comm12 u (h1 hu) r (h2 hr)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hp)

theorem mem_join {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ C0) (h1 : P1 ≤ C1) (h2 : P2 ≤ C2) {z : Q}
    (hz : z ∈ P0 ⊔ P1 ⊔ P2) : ∃ u ∈ P0, ∃ v ∈ P1, ∃ w ∈ P2, u * v * w = z := by
  obtain ⟨q, hq, w, hw, rfl⟩ := t113_mem_sup (T.sup01_comm2 h0 h1 h2) hz
  obtain ⟨u, hu, v, hv, rfl⟩ := t113_mem_sup
    (fun p hp r hr => T.comm01 p (h0 hp) r (h1 hr)) hq
  exact ⟨u, hu, v, hv, w, hw, rfl⟩

theorem join_eq_one {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ C0) (h1 : P1 ≤ C1) (h2 : P2 ≤ C2) {z : Q}
    (hz : z ∈ P0 ⊔ P1 ⊔ P2) (c0 : ∀ m ∈ C0, z * m = m * z) (c1 : ∀ m ∈ C1, z * m = m * z)
    (c2 : ∀ m ∈ C2, z * m = m * z) : z = 1 := by
  obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := T.mem_join h0 h1 h2 hz
  have hu1 : u = 1 := by
    refine T.cen0 u (h0 hu) fun m hm => ?_
    have a1 : Commute (u * v * w) m := c0 m hm
    have a2 : Commute v m := (T.comm01 m hm v (h1 hv)).symm
    have a3 : Commute w m := (T.comm02 m hm w (h2 hw)).symm
    have : Commute (u * v * w * w⁻¹ * v⁻¹) m := ((a1.mul_left a3.inv_left).mul_left a2.inv_left)
    have e : u * v * w * w⁻¹ * v⁻¹ = u := by group
    rw [e] at this
    exact this.eq
  subst hu1
  have hv1 : v = 1 := by
    refine T.cen1 v (h1 hv) fun m hm => ?_
    have a1 : Commute (1 * v * w) m := c1 m hm
    have a3 : Commute w m := (T.comm12 m hm w (h2 hw)).symm
    have : Commute (1 * v * w * w⁻¹) m := a1.mul_left a3.inv_left
    have e : 1 * v * w * w⁻¹ = v := by group
    rw [e] at this
    exact this.eq
  subst hv1
  have hw1 : w = 1 := by
    refine T.cen2 w (h2 hw) fun m hm => ?_
    simpa using c2 m hm
  subst hw1
  simp

theorem join_elem {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ C0) (h1 : P1 ≤ C1) (h2 : P2 ≤ C2)
    (e0 : IsElemAbelian 3 P0) (e1 : IsElemAbelian 3 P1) (e2 : IsElemAbelian 3 P2) :
    IsElemAbelian 3 (P0 ⊔ P1 ⊔ P2) ∧
      Nat.card ↥(P0 ⊔ P1 ⊔ P2) = Nat.card P0 * Nat.card P1 * Nat.card P2 := by
  have hi01 : P0 ⊓ P1 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact T.cen0 z (h0 hz.1) fun w hw => (T.comm01 w hw z (h1 hz.2)).symm
  obtain ⟨f01, c01⟩ := t113_sup_elemAbelian e0 e1
    (fun p hp r hr => T.comm01 p (h0 hp) r (h1 hr)) hi01
  have hi2 : (P0 ⊔ P1) ⊓ P2 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine T.join_eq_one h0 h1 h2 (Subgroup.mem_sup_left hz.1) ?_ ?_ ?_
    · exact fun m hm => (T.comm02 m hm z (h2 hz.2)).symm
    · exact fun m hm => (T.comm12 m hm z (h2 hz.2)).symm
    · exact fun m hm => T.sup01_comm2 h0 h1 le_rfl z hz.1 m hm
  obtain ⟨f, c⟩ := t113_sup_elemAbelian f01 e2 (T.sup01_comm2 h0 h1 h2) hi2
  exact ⟨f, by rw [c, c01]⟩

theorem zpowers_join {y0 y1 y2 : Q} (m0 : y0 ∈ C0) (m1 : y1 ∈ C1) (m2 : y2 ∈ C2)
    (o0 : orderOf y0 = 3) (o1 : orderOf y1 = 3) (o2 : orderOf y2 = 3) :
    IsElemAbelian 3 (Subgroup.zpowers y0 ⊔ Subgroup.zpowers y1 ⊔ Subgroup.zpowers y2) ∧
      Nat.card ↥(Subgroup.zpowers y0 ⊔ Subgroup.zpowers y1 ⊔ Subgroup.zpowers y2) = 27 ∧
      ∀ z ∈ Subgroup.zpowers y0 ⊔ Subgroup.zpowers y1 ⊔ Subgroup.zpowers y2,
        (∀ m ∈ C0, z * m = m * z) → (∀ m ∈ C1, z * m = m * z) → (∀ m ∈ C2, z * m = m * z) →
          z = 1 := by
  have h0 : Subgroup.zpowers y0 ≤ C0 := Subgroup.zpowers_le.2 m0
  have h1 : Subgroup.zpowers y1 ≤ C1 := Subgroup.zpowers_le.2 m1
  have h2 : Subgroup.zpowers y2 ≤ C2 := Subgroup.zpowers_le.2 m2
  obtain ⟨e0, c0⟩ := t113_zpowers_elem o0
  obtain ⟨e1, c1⟩ := t113_zpowers_elem o1
  obtain ⟨e2, c2⟩ := t113_zpowers_elem o2
  obtain ⟨hel, hcard⟩ := T.join_elem h0 h1 h2 e0 e1 e2
  exact ⟨hel, by rw [hcard, c0, c1, c2], fun z hz a b c => T.join_eq_one h0 h1 h2 hz a b c⟩

end Tri3

theorem t113_commute_conj {f g y : Q} (hfg : f * g = g * f) (hfy : f * y = y * f) :
    f * (g⁻¹ * y * g) = (g⁻¹ * y * g) * f := by
  have hg : Commute f g := hfg
  have hy : Commute f y := hfy
  exact ((hg.inv_right.mul_right hy).mul_right hg).eq

theorem t113_comm_join {f y0 y1 y2 : Q} (h0 : f * y0 = y0 * f) (h1 : f * y1 = y1 * f)
    (h2 : f * y2 = y2 * f) :
    ∀ z ∈ Subgroup.zpowers y0 ⊔ Subgroup.zpowers y1 ⊔ Subgroup.zpowers y2, f * z = z * f := by
  have hle : Subgroup.zpowers y0 ⊔ Subgroup.zpowers y1 ⊔ Subgroup.zpowers y2 ≤
      Subgroup.centralizer ({f} : Set Q) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> refine Subgroup.zpowers_le.2 ?_ <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
  intro z hz
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem t113_comm_gLBConj {f g : Q} {L : Subgroup Q} (hfg : f * g = g * f)
    (hfL : ∀ l ∈ L, f * l = l * f) :
    ∀ m ∈ CFSG.Open.GLBConj g L, f * m = m * f := by
  intro m hm
  have h1 : g * m * g⁻¹ ∈ L := (CFSG.LocalAnalysis.GLTheoremB.mem_gLBConj).1 hm
  have := t113_commute_conj hfg (hfL _ h1)
  have e : g⁻¹ * (g * m * g⁻¹) * g = m := by group
  rwa [e] at this

end Tri3

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
