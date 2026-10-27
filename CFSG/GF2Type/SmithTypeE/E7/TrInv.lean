module

public import CFSG.GF2Type.SmithTypeE.E7.TrRep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod CFSG.RankThree.OrthogonalInvolutions Module
  QuadraticMap

theorem linv_apply (A : V ≃ₗ[ZMod 2] V) (v : V) : A⁻¹ v = A.symm v := rfl

section Concl


@[expose] def InvConcl7 (a : TD6) : Prop :=
  5 ≤ finrank (ZMod 2) (commSpace (rhoMod a)) ∧
    ∀ q : QuadraticForm (ZMod 2) V, (∀ u v, polar q u v = fModel u v) →
      (∀ i < 75735, q (wtV i) = 0) → (∀ v ∈ commSpace (rhoMod a), q v = 0) →
      ∀ N : Submodule (ZMod 2) V, N ≠ ⊥ → N ≤ commSpace (rhoMod a) →
        (∀ k : ℕ, k < 365211 → tvElt k * a = a * tvElt k → ∀ n ∈ N, tvEquiv k n ∈ N) →
        ∃ i < 75735, wtV i ∈ N

theorem invConcl7_of_conj (g a : TD6) (h : InvConcl7 (g * a * g⁻¹)) : InvConcl7 a := by
  obtain ⟨hdim, hM⟩ := h
  have hcs : commSpace (rhoMod (g * a * g⁻¹)) =
      (commSpace (rhoMod a)).map (rhoMod g : V →ₗ[ZMod 2] V) := by
    rw [map_mul, map_mul, map_inv]
    exact commSpace_conj _ _
  refine ⟨?_, ?_⟩
  · rw [hcs, LinearEquiv.finrank_map_eq] at hdim
    exact hdim
  intro q hpol hwt hsing N hN hNle hinv
  have hgi : ((rhoMod g)⁻¹ : V ≃ₗ[ZMod 2] V) = rhoMod g⁻¹ := (map_inv rhoMod g).symm
  let q' : QuadraticForm (ZMod 2) V := q.comp ((rhoMod g)⁻¹ : V ≃ₗ[ZMod 2] V).toLinearMap
  have hpol' : ∀ u v, polar q' u v = fModel u v := by
    intro u v
    have e : polar q' u v = polar q ((rhoMod g)⁻¹ u) ((rhoMod g)⁻¹ v) := by
      simp only [q', polar, comp_apply, LinearEquiv.coe_coe, map_add]
    rw [e, hpol, hgi, fModel_rhoMod]
  have hwt' : ∀ i < 75735, q' (wtV i) = 0 := by
    intro i hi
    show q ((rhoMod g)⁻¹ (wtV i)) = 0
    rw [hgi, show wtV i = wtV (⟨i, hi⟩ : Fin 75735).val from rfl, rhoMod_wtV]
    exact hwt _ (g⁻¹ • (⟨i, hi⟩ : Fin 75735)).2
  have hsing' : ∀ v ∈ commSpace (rhoMod (g * a * g⁻¹)), q' v = 0 := by
    intro v hv
    rw [hcs] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    show q ((rhoMod g)⁻¹ (rhoMod g w)) = 0
    rw [linv_apply, LinearEquiv.symm_apply_apply]
    exact hsing w hw
  have hN' : N.map (rhoMod g : V →ₗ[ZMod 2] V) ≠ ⊥ := by
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    refine Submodule.ne_bot_iff _ |>.2 ⟨rhoMod g n, Submodule.mem_map_of_mem hn, ?_⟩
    intro h
    exact hn0 ((rhoMod g).injective (h.trans (map_zero _).symm))
  have hNle' : N.map (rhoMod g : V →ₗ[ZMod 2] V) ≤ commSpace (rhoMod (g * a * g⁻¹)) := by
    rw [hcs]
    exact Submodule.map_mono hNle
  have hinv' : ∀ k : ℕ, k < 365211 → tvElt k * (g * a * g⁻¹) = (g * a * g⁻¹) * tvElt k →
      ∀ n ∈ N.map (rhoMod g : V →ₗ[ZMod 2] V),
        tvEquiv k n ∈ N.map (rhoMod g : V →ₗ[ZMod 2] V) := by
    intro k hk hcomm n hn
    obtain ⟨n₀, hn₀, rfl⟩ := hn
    obtain ⟨k', hk'⟩ : ∃ k' : Fin 365211, k' = ((g⁻¹ : TD6) : Equiv.Perm (Fin 365211)) ⟨k, hk⟩ :=
      ⟨_, rfl⟩
    have hgk' : ((g : TD6) : Equiv.Perm (Fin 365211)) k' = ⟨k, hk⟩ := by
      rw [hk']
      change ((g : Equiv.Perm (Fin 365211)) * ((g : Equiv.Perm (Fin 365211))⁻¹)) ⟨k, hk⟩ = ⟨k, hk⟩
      rw [mul_inv_cancel]
      rfl
    have hconj : tvElt k'.val = g⁻¹ * tvElt k * g := by
      apply Subtype.ext
      have h1 := mul_tvP_mul_inv (g⁻¹).2 ⟨k, hk⟩
      rw [← hk'] at h1
      rw [tvElt_coe k'.2, Subgroup.coe_mul, Subgroup.coe_mul, tvElt_coe hk]
      have h2 : tvP ⟨k'.val, k'.2⟩ = tvP k' := rfl
      rw [h2, ← h1]
      simp only [Subgroup.coe_inv, inv_inv]
    have hcomm' : tvElt k'.val * a = a * tvElt k'.val := by
      rw [hconj]
      calc g⁻¹ * tvElt k * g * a = g⁻¹ * (tvElt k * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * tvElt k) * g := by rw [hcomm]
        _ = a * (g⁻¹ * tvElt k * g) := by group
    have h1 := hinv k'.val k'.2 hcomm' n₀ hn₀
    refine ⟨tvEquiv k'.val n₀, h1, ?_⟩
    have e := rhoMod_conj_tvEquiv g k'
    rw [hgk'] at e
    have e2 := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (rhoMod g n₀)) e
    simp only [LinearEquiv.mul_apply, linv_apply, LinearEquiv.symm_apply_apply] at e2
    exact e2
  obtain ⟨i, hi, hiN⟩ := hM q' hpol' hwt' hsing' _ hN' hNle' hinv'
  obtain ⟨n, hn, hni⟩ := hiN
  refine ⟨(g⁻¹ • (⟨i, hi⟩ : Fin 75735)).val, (g⁻¹ • (⟨i, hi⟩ : Fin 75735)).2, ?_⟩
  have e : wtV (g⁻¹ • (⟨i, hi⟩ : Fin 75735)).val = n := by
    have h1 := rhoMod_wtV g⁻¹ ⟨i, hi⟩
    rw [map_inv] at h1
    have h2 : (rhoMod g)⁻¹ (wtV i) = n := by
      rw [← hni]
      exact LinearEquiv.symm_apply_apply _ _
    exact h1.symm.trans h2
  rw [e]
  exact hn

end Concl

section Rep

variable
  {j : ℕ}

theorem invConcl7_rep (hj : j < 7) : InvConcl7 (repElt j) := by
  refine ⟨?_, ?_⟩
  · have := eight_le_finrank_commSpace hj
    omega
  · intro q hpol hwt hsing N hN hNle hinv
    by_cases hj26 : j = 2 ∨ j = 6
    · exfalso
      obtain ⟨v, hv, hq⟩ := not_totallySingular hj26 hpol hwt
      exact hq (hsing v hv)
    · have hj' : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      refine m1_rep hj' hN hNle (fun k hk n hn => ?_)
      obtain ⟨hk1, hk2⟩ := gens_ok hj' k hk
      exact hinv k hk1 (commute_tvElt_repElt hj hk1 hk2) n hn

theorem involutionFacts7 (a : TD6) (ha : a * a = 1) (ha1 : a ≠ 1) : InvConcl7 a := by
  obtain ⟨j, hj, hm, g, hg⟩ := exists_conj_rep a ha ha1
  apply invConcl7_of_conj g
  rw [hg, repElt_eq_omega hj hm]
  exact invConcl7_rep hj

end Rep

end CFSG.GF2Type.SmithTypeE.E7
