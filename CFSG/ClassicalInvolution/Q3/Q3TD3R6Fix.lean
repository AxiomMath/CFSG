module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R6Scal
public import CFSG.ClassicalInvolution.RouteD.TWED6Fix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.RouteD.TWE.D6
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

local macro "d6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem pattern_plus_six3 (c : TCtx3 .POmegaPlus 6 Ω K z) {β : Subgroup G} {t : G}
    (htz : t * z * t⁻¹ = z) {M : Subgroup G}
    (nd : DNodes3 6 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {x : spinGroup (quadPlus 6 (GaloisField 3 1))}
    {α : spinGroup (quadPlus 6 (GaloisField 3 1)) ≃* spinGroup (quadPlus 6 (GaloisField 3 1))}
    {g₀ : (Fin 6 ⊕ Fin 6 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 6 ⊕ Fin 6 → GaloisField 3 1)}
    (hn2 : locImg Ω z (nd.J ⟨2, by omega⟩) =
      ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField 3 1)))
    (hconj : ∀ y v, spinAction (quadPlus 6 (GaloisField 3 1)) (α y) (g₀ v) =
      g₀ (spinAction (quadPlus 6 (GaloisField 3 1)) y v))
    (hscal : ∀ y,
      polar (quadPlus 6 (GaloisField 3 1)) (spinAction (quadPlus 6 (GaloisField 3 1)) x
        ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadPlus 6 (GaloisField 3 1)) (spinAction (quadPlus 6 (GaloisField 3 1)) x
        ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = y) :
    PartnerPatternPlus3 6 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have hm3 : 3 ≤ 6 := by norm_num
  have hQ : (polarBilin (quadPlus 6 (GaloisField 3 1))).Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1)
  obtain ⟨j, hjmem, hjimg, hjK, hjc, hjp⟩ :=
    c.exists_nodes_plus3 (by norm_num : 4 ≤ 6) (Equiv.refl _) (fun _ _ => rfl)
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y' : G) ∈ locLayer Ω z := y'.2
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hlocmk : locMk Ω z y' = c.d.ψ x := hy'
  let ψ' : ↥(spinGroup (quadPlus 6 (GaloisField 3 1))) →* locQuot Ω z := c.d.ψ
  set F₀ : HypFrame (quadPlus 6 (GaloisField 3 1)) 6 := plusFrame 6 (GaloisField 3 1) hm3
    with hF₀
  have hg : spinAction (quadPlus 6 (GaloisField 3 1)) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField 3 1)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have cq := centralQuot3_plus (m := 6) (by norm_num : 4 ≤ 6)
  have hSpow : ∀ a : Fin 6, Pow3 (rankOne (plusDatum 6 (GaloisField 3 1) hm3).rootGroup a) :=
    fun a => cq.pow3 _ (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a)
  have hRfix : ∀ a : Fin 6, 1 ≤ a.val → ∀ r ∈ (rankOne (plusDatum 6 (GaloisField 3 1) hm3).rootGroup
      a).map (MulAut.conj x).toMonoidHom, α r = r := by
    intro a ha
    refine eq_of_fixed_of_pow3 (spinAction (quadPlus 6 (GaloisField 3 1)))
      (ker_spinAction_le_center _) cq.cop α (MulAut.conj g₀) (fun y => ?_) ((hSpow a).map _) ?_
    · refine LinearEquiv.ext fun v => ?_
      show spinAction _ (α y) v = g₀ (spinAction _ y (g₀⁻¹ v))
      have e1 : g₀ (g₀⁻¹ v) = v := by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      have := hconj y (g₀⁻¹ v)
      rw [e1] at this
      exact this
    · rintro _ ⟨s, hs, rfl⟩
      have hshs : (MulAut.conj x).toMonoidHom s = x * s * x⁻¹ := rfl
      have hhO : spinAction (quadPlus 6 (GaloisField 3 1)) ((MulAut.conj x).toMonoidHom s) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField 3 1)) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ _ v
      have hfixv : ∀ r, spinAction (quadPlus 6 (GaloisField 3 1)) ((MulAut.conj x).toMonoidHom s)
          (spinAction (quadPlus 6 (GaloisField 3 1)) x (F₀.vec ⟨0, by omega⟩ r)) =
          spinAction (quadPlus 6 (GaloisField 3 1)) x (F₀.vec ⟨0, by omega⟩ r) := by
        intro r
        rw [hshs, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          ← LinearEquiv.mul_apply (spinAction _ x⁻¹), ← map_mul, inv_mul_cancel, map_one]
        show spinAction _ x (spinAction _ s (F₀.vec ⟨0, by omega⟩ r)) = _
        rw [rankOne_fix_vec_zero_plus hm3 (by omega : 0 < a.val) hs r]
      have hcomm := commute_of_scalar_on_perp hQ (imgPair F₀ ⟨0, by omega⟩ hg) hg₀O hhO
        (ε := 1) (one_mul 1)
        (fun y hy => by
          rw [one_smul]
          exact hscal y (HypPair.mem_perp.mp hy).1 (HypPair.mem_perp.mp hy).2)
        (fun q hq => by
          obtain ⟨a₁, b₁, rfl⟩ := (mem_hypPlane_iff _).mp hq
          rw [map_add, map_smul, map_smul]
          exact congrArg₂ (· + ·) (congrArg (a₁ • ·) (hfixv true))
            (congrArg (b₁ • ·) (hfixv false)))
      show g₀ * spinAction _ _ * g₀⁻¹ = _
      rw [hcomm]
      group
  have hfix : ∀ a : Fin 6, 1 ≤ a.val → ∀ u ∈ locImg Ω z (conjSub (y' : G) (j a)),
      locAut hΩ.conjInvariant htz u = u := by
    intro a ha u hu
    rw [locImg_conjSub_layer (j a) y', hjimg a] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ : ∃ s : ↥(spinGroup (quadPlus 6 (GaloisField 3 1))),
        s ∈ rankOne (plusDatum 6 (GaloisField 3 1) hm3).rootGroup a ∧ c.d.ψ s = v :=
      Subgroup.mem_map.mp hv
    rw [hlocmk]
    have hαs : α (x * s * x⁻¹) = x * s * x⁻¹ := hRfix a ha _ ⟨s, hs, rfl⟩
    have hu1 : (MulAut.conj (c.d.ψ x)).toMonoidHom (c.d.ψ s) = c.d.ψ (x * s * x⁻¹) := by
      change (MulAut.conj (ψ' x)).toMonoidHom (ψ' s) = ψ' (x * s * x⁻¹)
      simp [map_mul, map_inv]
    rw [hu1, ← hαθ, hαs]
  have hKJ2 : Commutes K (nd.J ⟨2, by omega⟩) := by
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne3 (by d6_idx)) (by d6_idx)
  have hn2z : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm hKJ2)
  have hr0 : rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup
      (⟨0, by norm_num⟩ : Fin 6) =
      rootSL2 (plusFrame 6 (GaloisField 3 1) hm3) 0 1 (by omega) (by omega) (by omega)
        true false :=
    rankOne_plusDatum_of_lt (K := GaloisField 3 1) (m := 6) hm3 (k := ⟨0, by norm_num⟩)
      (by norm_num)
  have hpair0 : ∀ a : Fin 6, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (conjSub (y' : G) (j a)) := by
    intro a ha
    have ha0 : a = (⟨0, by norm_num⟩ : Fin 6) := Fin.ext ha
    rw [ha0]
    have hmemy : conjSub (y' : G) (j (⟨0, by norm_num⟩ : Fin 6)) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y' : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j (⟨0, by norm_num⟩ : Fin 6), (hjmem (⟨0, by norm_num⟩ : Fin 6)).1, rfl⟩
    have heq : conjSub (y' : G) (j (⟨0, by norm_num⟩ : Fin 6)) = nd.J ⟨2, by omega⟩ := by
      refine c.eq_of_locImg_eq hmemy hn2z ?_
      rw [locImg_conjSub_layer (j (⟨0, by norm_num⟩ : Fin 6)) y',
        hjimg (⟨0, by norm_num⟩ : Fin 6), hn2, hlocmk, hr0]
      change Subgroup.map (MulAut.conj (ψ' x)).toMonoidHom (Subgroup.map ψ' _) =
        Subgroup.map ψ' (Subgroup.map (MulAut.conj x).toMonoidHom _)
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext s
      simp [map_mul, map_inv]
    rw [heq]
    obtain ⟨W, hW⟩ := nd.pair_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by d6_idx)
    rw [h1] at hW
    exact ⟨W, hW⟩
  exact PartnerPatternPlus3.of_locAut c (j := j) (fun a => (hjmem a).1) hjK hjc hjp hy htz hfix
    hpair0

end Group

end CFSG.ClassicalInvolution.Q3.Q3TD
