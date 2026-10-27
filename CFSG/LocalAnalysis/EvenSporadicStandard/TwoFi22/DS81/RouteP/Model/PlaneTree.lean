module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Subgroups

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.Sporadic.Th.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

structure PlaneTripleFacts (pa pb : Array ℕ) (T : TripleTree) : Prop where
  root : T.us[0]! = 0 ∧ T.vs[0]! = 1 ∧ T.ws[0]! = 2
  edge : ∀ k, 0 < k → k < T.us.size → T.par[k]! < k ∧
    ((T.lab[k]! = 0 ∧ T.us[k]! = pa[T.us[T.par[k]!]!]! ∧ T.vs[k]! = pa[T.vs[T.par[k]!]!]! ∧
        T.ws[k]! = pa[T.ws[T.par[k]!]!]!) ∨
      (T.lab[k]! = 1 ∧ T.us[k]! = pb[T.us[T.par[k]!]!]! ∧ T.vs[k]! = pb[T.vs[T.par[k]!]!]! ∧
        T.ws[k]! = pb[T.ws[T.par[k]!]!]!))
  cover : ∀ u v w : ℕ, u < 24 → v < 24 → w < 24 → u ≠ v → u ≠ w → v ≠ w →
    T.pos[576 * u + 24 * v + w]! < T.us.size ∧ T.us[T.pos[576 * u + 24 * v + w]!]! = u ∧
      T.vs[T.pos[576 * u + 24 * v + w]!]! = v ∧ T.ws[T.pos[576 * u + 24 * v + w]!]! = w

theorem PlaneTripleFacts.of_tripleOK {pa pb : Array ℕ} {T : TripleTree}
    (h : tripleOK pa pb T = true) : PlaneTripleFacts pa pb T := by
  unfold tripleOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, -, -, -, -, hu, hv, hw, hedge, hcover⟩ := h
  refine ⟨⟨hu, hv, hw⟩, fun k hk0 hk => ?_, fun u v w hu hv hw huv huw hvw => ?_⟩
  · have h1 := allIn_one_iff.1 hedge k hk0 hk
    simp only [tripleEdge, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq, and_assoc] at h1
    exact h1
  · have h1 := allIn_zero_iff.1 (allIn_zero_iff.1 (allIn_zero_iff.1 hcover u hu) v hv) w hw
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      and_assoc] at h1
    rcases h1 with ((h | h) | h) | h
    · exact absurd h huv
    · exact absurd h huw
    · exact absurd h hvw
    · exact h

def PlaneReach (u v w : Fin 24) : Prop :=
  ∃ g ∈ Zq, g • x0 = planePt u ∧ g • x1 = planePt v ∧ g • x2 = planePt w

theorem planeReach_root : PlaneReach 0 1 2 :=
  ⟨1, Zq.one_mem, by rw [one_smul, planePt_zero], by rw [one_smul, planePt_one],
    by rw [one_smul, planePt_two]⟩

theorem PlaneReach.smul_a
    {u v w : Fin 24} (h : PlaneReach u v w) : PlaneReach (PA u) (PA v) (PA w) := by
  obtain ⟨g, hg, h0, h1, h2⟩ := h
  refine ⟨aElt * g, Zq.mul_mem aElt_mem_Zq hg, ?_, ?_, ?_⟩
  · rw [mul_smul, h0, aElt_smul_planePt]
  · rw [mul_smul, h1, aElt_smul_planePt]
  · rw [mul_smul, h2, aElt_smul_planePt]

theorem PlaneReach.smul_b
    {u v w : Fin 24} (h : PlaneReach u v w) : PlaneReach (PB u) (PB v) (PB w) := by
  obtain ⟨g, hg, h0, h1, h2⟩ := h
  refine ⟨bElt * g, Zq.mul_mem bElt_mem_Zq hg, ?_, ?_, ?_⟩
  · rw [mul_smul, h0, bElt_smul_planePt]
  · rw [mul_smul, h1, bElt_smul_planePt]
  · rw [mul_smul, h2, bElt_smul_planePt]

theorem planeReach_nodes
    {T : TripleTree} (hT : PlaneTripleFacts planeAArr planeBArr T) :
    ∀ k < T.us.size, ∃ u v w : Fin 24, T.us[k]! = u.val ∧ T.vs[k]! = v.val ∧
      T.ws[k]! = w.val ∧ PlaneReach u v w := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨0, 1, 2, hT.root.1, hT.root.2.1, hT.root.2.2, planeReach_root⟩
    · obtain ⟨hpar, hedge⟩ := hT.edge k hk0 hk
      obtain ⟨u, v, w, hu, hv, hw, hr⟩ := ih _ hpar (hpar.trans hk)
      rcases hedge with ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
      · exact ⟨PA u, PA v, PA w, by rw [h1, hu]; rfl, by rw [h2, hv]; rfl,
          by rw [h3, hw]; rfl, hr.smul_a⟩
      · exact ⟨PB u, PB v, PB w, by rw [h1, hu]; rfl, by rw [h2, hv]; rfl,
          by rw [h3, hw]; rfl, hr.smul_b⟩

theorem tripleFacts :
    PlaneTripleFacts planeAArr planeBArr (tripleTree ()) :=
  PlaneTripleFacts.of_tripleOK objFacts.triple

theorem planeReach_of_distinct
    {u v w : Fin 24} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : PlaneReach u v w := by
  obtain ⟨hk, h1, h2, h3⟩ := tripleFacts.cover u.val v.val w.val u.isLt v.isLt w.isLt
    (fun h => huv (Fin.ext h)) (fun h => huw (Fin.ext h)) (fun h => hvw (Fin.ext h))
  obtain ⟨u', v', w', hu', hv', hw', hr⟩ := planeReach_nodes tripleFacts _ hk
  have eu : u' = u := Fin.ext (hu'.symm.trans h1)
  have ev : v' = v := Fin.ext (hv'.symm.trans h2)
  have ew : w' = w := Fin.ext (hw'.symm.trans h3)
  subst eu ev ew
  exact hr

theorem exists_mem_Zq_smul_base_triple
    {p q r : Ω} (hp : p ∈ plane) (hq : q ∈ plane)
    (hr : r ∈ plane) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ g ∈ Zq, g • x0 = p ∧ g • x1 = q ∧ g • x2 = r := by
  obtain ⟨u, rfl⟩ := mem_plane_iff.1 hp
  obtain ⟨v, rfl⟩ := mem_plane_iff.1 hq
  obtain ⟨w, rfl⟩ := mem_plane_iff.1 hr
  exact planeReach_of_distinct (fun h => hpq (congrArg planePt h))
    (fun h => hpr (congrArg planePt h)) (fun h => hqr (congrArg planePt h))

theorem Zq_threeTransitive
    {p q r p' q' r' : Ω} (hp : p ∈ plane) (hq : q ∈ plane) (hr : r ∈ plane) (hp' : p' ∈ plane)
    (hq' : q' ∈ plane) (hr' : r' ∈ plane) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpq' : p' ≠ q') (hpr' : p' ≠ r') (hqr' : q' ≠ r') :
    ∃ g ∈ Zq, g • p = p' ∧ g • q = q' ∧ g • r = r' := by
  obtain ⟨g₁, hg₁, h10, h11, h12⟩ := exists_mem_Zq_smul_base_triple hp hq hr hpq hpr hqr
  obtain ⟨g₂, hg₂, h20, h21, h22⟩ := exists_mem_Zq_smul_base_triple hp' hq' hr' hpq' hpr' hqr'
  refine ⟨g₂ * g₁⁻¹, Zq.mul_mem hg₂ (Zq.inv_mem hg₁), ?_, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 h10.symm, h20]
  · rw [mul_smul, inv_smul_eq_iff.2 h11.symm, h21]
  · rw [mul_smul, inv_smul_eq_iff.2 h12.symm, h22]

theorem exists_mem_plane_ne_two (p q : Ω) : ∃ r ∈ plane, r ≠ p ∧ r ≠ q := by
  have h : ({p, q} : Finset Ω).card < plane.card := by
    rw [card_plane]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨r, hr, hrn⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨r, hr, fun h => hrn (by simp [h]), fun h => hrn (by simp [h])⟩

theorem Zq_twoTransitive
    {p q p' q' : Ω} (hp : p ∈ plane) (hq : q ∈ plane) (hp' : p' ∈ plane) (hq' : q' ∈ plane)
    (hpq : p ≠ q) (hpq' : p' ≠ q') : ∃ g ∈ Zq, g • p = p' ∧ g • q = q' := by
  obtain ⟨r, hr, hrp, hrq⟩ := exists_mem_plane_ne_two p q
  obtain ⟨r', hr', hrp', hrq'⟩ := exists_mem_plane_ne_two p' q'
  obtain ⟨g, hg, h1, h2, -⟩ := Zq_threeTransitive hp hq hr hp' hq' hr' hpq hrp.symm hrq.symm
    hpq' hrp'.symm hrq'.symm
  exact ⟨g, hg, h1, h2⟩

theorem exists_swap01 :
    ∃ s ∈ Zq, s • x0 = x1 ∧ s • x1 = x0 :=
  Zq_twoTransitive x0_mem_plane x1_mem_plane x1_mem_plane x0_mem_plane x0_ne_x1 x0_ne_x1.symm

theorem exists_s2 :
    ∃ s ∈ Zp ⊓ Zq ⊓ Ze'', s • x1 = x2 ∧ s • x2 = x1 := by
  obtain ⟨g, hg, h0, h1, h2⟩ := Zq_threeTransitive x0_mem_plane x1_mem_plane x2_mem_plane
    x0_mem_plane x2_mem_plane x1_mem_plane x0_ne_x1 x0_ne_x2 x1_ne_x2 x0_ne_x2 x0_ne_x1
    x1_ne_x2.symm
  have hZp : g ∈ Zp := by
    rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]
    exact h0
  exact ⟨g, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hZp, hg⟩, mem_Ze''_iff.2 (Or.inr ⟨h1, h2⟩)⟩,
    h1, h2⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
