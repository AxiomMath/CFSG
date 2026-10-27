module

public import CFSG.ClassicalInvolution.Q3.Q3TWY13
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1


section Model

variable {V : Type} [AddCommGroup V] [Module 𝔽₃ V] [FiniteDimensional 𝔽₃ V] {Q : QuadraticForm 𝔽₃ V}

theorem exists_spin_pair3_gen_Q (hQ : Q.Nondegenerate) {m : ℕ} (hm : 4 ≤ m) (F₀ : HypFrame Q m)
    (hdim : 9 ≤ Module.finrank 𝔽₃ V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars 𝔽₃ V))
    {R₀ R₁ : Subgroup (spinGroup Q)} (hR₀ : R₀ ∈ 𝓕) (hR₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair 𝔽₃ W R₀ R₁) :
    ∃ x : spinGroup Q,
      R₀ = ((rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom) := by
  classical
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  let L : ℕ → Subgroup (V ≃ₗ[𝔽₃] V) := fun a => (if a = 0 then R₀ else R₁).map (spinAction Q)
  have hL0 : L 0 = R₀.map (spinAction Q) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction Q) := by simp [L]
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let i : ℕ → (V ≃ₗ[𝔽₃] V) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental Q (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  have hadjV : ModelAdj (scalars 𝔽₃ V) (R₀.map (spinAction Q)) (R₁.map (spinAction Q)) :=
    cq.modelAdj hR₀ hR₁ hadj
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hi₀ hi₁ hadjV
  have hVchain : VChain Q 2 L i := by
    refine ⟨hi, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => by omega⟩
    · have : a = 0 := by omega
      subst this
      simpa [i] using cm
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using N
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using C
    · have : a = 0 := by omega
      subst this
      obtain ⟨W, hW⟩ := hlin
      have := hasSingularVector_of_linearPair3 hi₀ hi₁ cm N C
        ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
      simpa [i] using this
  obtain ⟨pp, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hVchain (le_refl 2)
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ F₀ (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 F₀ a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction Q) := by
    intro a ha
    have := La_range_eq_of_pairs F₀ (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  refine ⟨x, ?_, ?_⟩
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₀)
      (rootSL2_map_conj_pow3 _ 0 1 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₁)
      (rootSL2_map_conj_pow3 _ 1 2 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL1]; exact hnode 1 (by omega))

end Model

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {tY : StatedLieTag}
  {nY : ℕ} {N : Subgroup G}

theorem conjSub_eq3 (cx : TCtx3 tY nY Ω N x) {L : Subgroup G}
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hwx : w ∈ locLayer Ω x)
    {r : (modelUniv tY nY 3 1 Nat.prime_three).K} (hr : cx.d.ψ r = locElt Ω x w hwx)
    (hN : conjSub w L = L) : conjSub r R = R := by
  refine eq_of_map_eq_of_pow3 cx.d.ψ cx.d.ker_le cx.ker_cop ((cx.hY.pow3 R hR).conjSub r)
    (cx.hY.pow3 R hR) ?_
  have h1 := locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w, hwx⟩
  rw [hN, hLR] at h1
  have h2 : (conjSub r R).map cx.d.ψ =
      (R.map cx.d.ψ).map (MulAut.conj (locMk Ω x ⟨w, hwx⟩)).toMonoidHom := by
    show (R.map (MulAut.conj r).toMonoidHom).map cx.d.ψ = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    rw [show locMk Ω x ⟨w, hwx⟩ = locElt Ω x w hwx from rfl, ← hr]
  rw [h2, ← h1]

theorem modelAdj_of_adj3 (cx : TCtx3 tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) R R' := by
  obtain ⟨r, hr, hψr⟩ := exists_involution_of_fund3 cx hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund3 cx hL' hR' hLR' hw'
  have hcen : ⁅r, r'⁆ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K := by
    refine cx.d.ker_le ?_
    have hcomm : cx.d.ψ r * cx.d.ψ r' = cx.d.ψ r' * cx.d.ψ r := by
      rw [hψr, hψr', locElt_mul, locElt_mul]
      congr 1
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  refine ⟨fun h => hne (cx.eq_of_locImg_eq hL hL' (by rw [hLR, hLR', h])), ?_, r, r', hr, hr',
    hcen, ?_⟩
  · intro h
    exact hnc ((cx.commutes_iff_fund hL hL' hR hLR hLR').mpr h)
  · intro y hy
    have h := conjSub_eq3 cx hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN
    rw [← h]
    exact ⟨y, hy, rfl⟩

end Group

end CFSG.ClassicalInvolution.Q3.Q3TWY
