module

public import CFSG.ClassicalInvolution.Q3.Q3TWY28
public import CFSG.ClassicalInvolution.Q3.Q3TWY22
public import CFSG.ClassicalInvolution.Q3.Q3TWY10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local macro "nd_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.DAdj, edgeD]; done)
    | (simp [DNodes3.DAdj, edgeD]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


section Recognition

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {M : Subgroup G}

theorem recognition_odd3 {u : ℕ} (c : TCtx3 .POmegaOdd (u + 5) Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair 𝔽₃ W K β) (hMz : M ∈ centralizingMembers Ω {z})
    (nd : DNodes3 (u + 5) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM) (hdt : ChainDT3 u Rz) :
    ∃ (x : spinGroup (quadOdd (u + 5) 𝔽₃)) (tM : Bool)
      (α : spinGroup (quadOdd (u + 5) 𝔽₃) ≃* spinGroup (quadOdd (u + 5) 𝔽₃))
      (g₀ : (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃]
        (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃)),
      (∀ a (ha : a ≤ u + 1), Rz (a + 2) = ((rootSL2 (oddFrame (u + 5) 𝔽₃).toHypFrame a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      RzM = ((rootSL2 (oddFrame (u + 5) 𝔽₃).toHypFrame (u + 3) (u + 4) (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd (u + 5) 𝔽₃) ∧ g₀ * g₀ = 1 ∧
      (∀ y v, spinAction (quadOdd (u + 5) 𝔽₃) (α y) (g₀ v) =
        g₀ (spinAction (quadOdd (u + 5) 𝔽₃) y v)) := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaOdd (u + 5) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, by norm_num⟩
  have cq := centralQuot3_odd (m := u + 5) (by omega)
  have hQ : (quadOdd (u + 5) 𝔽₃).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd (u + 5) 𝔽₃ h2)
  have hdim : 9 ≤ Module.finrank 𝔽₃ (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
    omega
  let θ : spinGroup (quadOdd (u + 5) 𝔽₃) →* locQuot Ω z := c.d.ψ
  let σ := locAut c.hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range3 c htz h2t hKt (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadOdd (u + 5) 𝔽₃))},
      L ∈ centralizingMembers Ω {z} → locImg Ω z L = R.map θ → Commutes β L →
      ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 htz hL).mp
      (fun n hn => Subgroup.mem_centralizer_singleton_iff.mpr (hβL t ht.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, hxR, hxtw, tM, hxM⟩ := spin_chain_recognition_gen3 hQ (s := u + 1) (by omega)
    (oddFrame (u + 5) 𝔽₃).toHypFrame hdim cq (R := fun a => Rz (a + 2)) (Rtw := Rz (u + 4))
    (RM := RzM) (fun a ha => hch.fund (a + 2) (by omega) (by omega))
    (hch.fund (u + 4) (by omega) (by omega)) hch.fundM
    (fun a ha => hch.adj h0 (a := a + 2) (b := a + 3) (by omega) (by omega) (by omega)
      (by omega) (by nd_idx))
    (fun a ha => hch.lin h0 (a := a + 2) (b := a + 3) (by omega) (by omega) (by omega)
      (by omega) (by nd_idx))
    (fun a b hab hb => hch.comm h0 (a := a + 2) (b := b + 2) (by omega) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (a := ⟨a + 2, by omega⟩) (b := ⟨b + 2, by omega⟩)
        (Fin.ne_of_val_ne (by nd_idx)) (by nd_idx)))
    (fun a ha => hch.commM h0 hMz (a := a + 2) (by omega) (by omega)) hdt.dist
    (hch.ne h0 (a := u + 4) (b := u + 3) (by omega) (by omega) (by omega) (by omega)
      (by omega))
    hdt.twin
  have hfixR : ∀ r ∈ Rz (u + 1 + 2), σ (θ r) = θ r := fun r hr =>
    hfixσ (node_mem_z3 c nd h0 (a := u + 3) (by omega) (by omega))
      (hch.img (u + 3) (by omega) (by omega))
      (node_commutes_β3 nd h1 (a := u + 3) (by omega) (by omega)) r hr
  have hfixtw : ∀ r ∈ Rz (u + 4), σ (θ r) = θ r := fun r hr =>
    hfixσ (node_mem_z3 c nd h0 (a := u + 4) (by omega) (by omega))
      (hch.img (u + 4) (by omega) (by omega))
      (node_commutes_β3 nd h1 (a := u + 4) (by omega) (by omega)) r hr
  obtain ⟨α, g₀, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_twin_odd3 (m := u + 5) (by omega) θ
    c.d.ker_le c.ker_cop σ hσ2 hσr (R := Rz (u + 4)) (R' := Rz (u + 1 + 2)) (a := u + 1)
    (b := u + 2) (by omega) (by omega) (by omega) x hxtw (hxR (u + 1) le_rfl)
    (c.hY.pow3 _ (hch.fund (u + 4) (by omega) (by omega)))
    (c.hY.pow3 _ (hch.fund (u + 1 + 2) (by omega) (by omega))) hfixtw hfixR
  exact ⟨x, tM, α, g₀, hxR, hxM, hαθ, hg₀O, hg₀2, hconj⟩

end Recognition

end CFSG.ClassicalInvolution.Q3.Q3TWY
