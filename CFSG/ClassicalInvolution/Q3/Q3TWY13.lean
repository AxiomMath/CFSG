module

public import CFSG.ClassicalInvolution.Q3.Q3TWY12

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY
  CFSG.ClassicalInvolution.Q3.Q3TWC
open QuadraticMap
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair longBlock shortBlock)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem pattern_odd3 {m : ℕ} (hm3 : 3 ≤ m) (c : TCtx3 .POmegaOdd m Ω K z) {β : Subgroup G} {t : G}
    (htz : t * z * t⁻¹ = z) {N₀ : Subgroup G} (hN₀Ω : N₀ ∈ Ω) (hKN : Commutes K N₀)
    (hβN : ∃ W, LinearBlockStandardPair 𝔽₃ W β N₀)
    {x : spinGroup (quadOdd m 𝔽₃)}
    {α : spinGroup (quadOdd m 𝔽₃) ≃* spinGroup (quadOdd m 𝔽₃)}
    {g₀ : (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃)} {ε : 𝔽₃}
    (hn2 : locImg Ω z N₀ =
      ((rootSL2 (oddFrame m 𝔽₃).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃))
    (hconj : ∀ y v, spinAction (quadOdd m 𝔽₃) (α y) (g₀ v) =
      g₀ (spinAction (quadOdd m 𝔽₃) y v))
    (hε : ε * ε = 1)
    (hscal : ∀ y,
      polar (quadOdd m 𝔽₃) (spinAction (quadOdd m 𝔽₃) x
        ((oddFrame m 𝔽₃).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadOdd m 𝔽₃) (spinAction (quadOdd m 𝔽₃) x
        ((oddFrame m 𝔽₃).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = ε • y) :
    PartnerPatternBPair3 m Ω K β t := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hQ : (polarBilin (quadOdd m 𝔽₃)).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd m 𝔽₃ h2
  have cq := centralQuot3_odd (m := m) hm3
  obtain ⟨j, hjmem, hjY, hjpow, hjK, hjc, hjp, hjsp, hjimg⟩ := exists_nodes_odd_full3 hm3 c
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y' : G) ∈ locLayer Ω z := y'.2
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hlocmk : locMk Ω z y' = c.d.ψ x := hy'
  let ψ' : ↥(spinGroup (quadOdd m 𝔽₃)) →* locQuot Ω z := c.d.ψ
  set F₀ : HypFrame (quadOdd m 𝔽₃) m := (oddFrame m 𝔽₃).toHypFrame with hF₀
  have hg : spinAction (quadOdd m 𝔽₃) x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hRfix : ∀ a : Fin m, 1 ≤ a.val → ∀ r ∈ (rankOne (oddDatum m 𝔽₃).rootGroup a).map
      (MulAut.conj x).toMonoidHom, α r = r := by
    intro a ha
    refine eq_of_fixed_of_pow3 (spinAction (quadOdd m 𝔽₃)) (ker_spinAction_le_center _) cq.cop
      α (MulAut.conj g₀) (fun y => ?_) ((pow3_rankOne_oddDatum3 hm3 c.hY a).map _) ?_
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
      have hhO : spinAction (quadOdd m 𝔽₃) ((MulAut.conj x).toMonoidHom s) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ _ v
      have hfixv : ∀ r, spinAction (quadOdd m 𝔽₃) ((MulAut.conj x).toMonoidHom s)
          (spinAction (quadOdd m 𝔽₃) x (F₀.vec ⟨0, by omega⟩ r)) =
          spinAction (quadOdd m 𝔽₃) x (F₀.vec ⟨0, by omega⟩ r) := by
        intro r
        rw [hshs, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          ← LinearEquiv.mul_apply (spinAction _ x⁻¹), ← map_mul, inv_mul_cancel, map_one]
        show spinAction _ x (spinAction _ s (F₀.vec ⟨0, by omega⟩ r)) = _
        rw [rankOne_fix_vec_zero (by omega) (by omega : 0 < a.val) hs r]
      have hcomm := commute_of_scalar_on_perp hQ (imgPair F₀ ⟨0, by omega⟩ hg) hg₀O hhO hε
        (fun y hy => hscal y (HypPair.mem_perp.mp hy).1 (HypPair.mem_perp.mp hy).2)
        (fun q hq => by
          obtain ⟨a₁, b₁, rfl⟩ := (mem_hypPlane_iff _).mp hq
          rw [map_add, map_smul, map_smul]
          exact congrArg₂ (· + ·) (congrArg (a₁ • ·) (hfixv true))
            (congrArg (b₁ • ·) (hfixv false)))
      show g₀ * spinAction _ _ * g₀⁻¹ = _
      rw [hcomm]
      group
  have hfix : ∀ a : Fin m, 1 ≤ a.val → ∀ u ∈ locImg Ω z (conjSub (y' : G) (j a)),
      locAut hΩ.conjInvariant htz u = u := by
    intro a ha u hu
    rw [locImg_conjSub_layer (j a) y', hjimg a] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ : ∃ s : ↥(spinGroup (quadOdd m 𝔽₃)),
        s ∈ rankOne (oddDatum m 𝔽₃).rootGroup a ∧ c.d.ψ s = v :=
      Subgroup.mem_map.mp hv
    rw [hlocmk]
    have hαs : α (x * s * x⁻¹) = x * s * x⁻¹ := hRfix a ha _ ⟨s, hs, rfl⟩
    have hu1 : (MulAut.conj (c.d.ψ x)).toMonoidHom (c.d.ψ s) = c.d.ψ (x * s * x⁻¹) := by
      change (MulAut.conj (ψ' x)).toMonoidHom (ψ' s) = ψ' (x * s * x⁻¹)
      simp [map_mul, map_inv]
    rw [hu1, ← hαθ, hαs]
  have hn2z : N₀ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₀Ω c.hz.mem (commutes_symm hKN)
  have hr0 : rankOne (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D.rootGroup
      (⟨0, by omega⟩ : Fin m) =
      rootSL2 (oddFrame m 𝔽₃).toHypFrame 0 1 (by omega) (by omega) (by omega) true false :=
    rankOne_oddDatum_of_lt (K := 𝔽₃) (k := ⟨0, by omega⟩) (by show 0 + 1 < m; omega)
  have hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair 𝔽₃ W β (conjSub (y' : G) (j a)) := by
    intro a ha
    have ha0 : a = (⟨0, by omega⟩ : Fin m) := Fin.ext ha
    rw [ha0]
    have hmemy : conjSub (y' : G) (j ⟨0, by omega⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y' : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by omega⟩, (hjmem ⟨0, by omega⟩ (by omega)).1, rfl⟩
    have heq : conjSub (y' : G) (j ⟨0, by omega⟩) = N₀ := by
      refine c.eq_of_locImg_eq hmemy hn2z ?_
      rw [locImg_conjSub_layer (j ⟨0, by omega⟩) y', hjimg ⟨0, by omega⟩, hn2, hlocmk, hr0]
      change Subgroup.map (MulAut.conj (ψ' x)).toMonoidHom (Subgroup.map ψ' _) =
        Subgroup.map ψ' (Subgroup.map (MulAut.conj x).toMonoidHom _)
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext s
      simp [map_mul, map_inv]
    rw [heq]
    exact hβN
  exact PartnerPatternBPair3.of_locAut hΩ c.hP1 c.hO3 (j := j)
    (fun a ha => (hjmem a ha).1.1) hjY hjpow hjK c.locLayer_le_normalizer hjc hjp hjsp hy htz
    hfix hpair0

end Group

end CFSG.ClassicalInvolution.Q3.Q3TWY
