module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptGraph

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

section Frames

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem te6AdaptedFrames_of_isolated' (hf : 1 ≤ f) (hMFZ : Gaps.FundNoncentral p)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeU p f 5 Ω z)
    (c : UCtx p f 5 Ω K z) (nd : UNodes c) (hF1 : TE6PartnerIsolated c nd)
    (hF2 : TE6NotGraphField' c nd) : TE6AdaptedFrames p f hf c nd := by
  classical
  intro N hN hNK hNj Θ hΘ v hv α hα
  have hp2 := c.hp2
  have hq := c.hq
  have hK := c.card_eq
  have hvz : v * z * v⁻¹ = z := partner_involution_commutes c.hp2 c.hz hv hNK
  have hv2 : v * v = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one v
    rwa [hv.orderOf_eq_two] at this
  obtain ⟨α', g, φ, hα', hmat, hiso, hφ, hα2⟩ := hΘ.exists_alpha hvz hv2
  have : Group.IsPerfect (Su (GaloisField p (2 * f)) p f 6) := isPerfect_su_gen hK hq (by norm_num)
  have hαα : α = α' := ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hΘ.ker_le α α'
    (fun x => by rw [hα x, hα' x])
  subst hαα
  have hφ1 : φ = RingEquiv.refl _ := hF2 N hN hNK hNj Θ hΘ v hv α g φ hα hmat hiso hφ hα2
  subst hφ1
  have hmat' : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := fun x => by
    rw [hmat x]
    simp
  obtain ⟨lam, hsq, hν⟩ := exists_lam hf hp2 hq hmat' hα2 hiso
  have hw0 : Θ (te6Inv p f) = nd.w 0 := map_te6Inv_eq hΘ
  have hvw : v * nd.w 0 * v⁻¹ = nd.w 0 := by
    have h1 : v * (z * nd.w 0) = (z * nd.w 0) * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (hN.2 hv.mem)
    have h2 : v * z = z * v := by
      have := hvz
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h3 : z * (v * nd.w 0) = z * (nd.w 0 * v) := by
      calc z * (v * nd.w 0) = (z * v) * nd.w 0 := by rw [mul_assoc]
        _ = (v * z) * nd.w 0 := by rw [h2]
        _ = v * (z * nd.w 0) := by rw [mul_assoc]
        _ = (z * nd.w 0) * v := h1
        _ = z * (nd.w 0 * v) := by rw [mul_assoc]
    rw [mul_left_cancel h3, mul_inv_cancel_right]
  have hfixw : (MulAut.conj v) (Θ (te6Inv p f)) = Θ (te6Inv p f) := by
    rw [hw0]
    exact hvw
  obtain ⟨u, hu⟩ := lift_matrix_of_fixed (n := 6) hK (by norm_num : 3 ≤ 6) hΘ.ker_le
    (σ := MulAut.conj v) (α := α) (fun x => hα x) (x := te6Inv p f) hfixw
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
      Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) with hGi
  set W : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) := suMat (te6Inv p f) with hWdef
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : Gm * W * Gi = (u : GaloisField p (2 * f)) • W := (hmat' (te6Inv p f)).symm.trans hu
  have htr : Matrix.trace (Gm * W * Gi) = Matrix.trace W := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have hu1 : (u : GaloisField p (2 * f)) = 1 := by
    rw [h1, Matrix.trace_smul, trace_te6Inv, smul_eq_mul] at htr
    have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := c.h2
    have h3 : ((u : GaloisField p (2 * f)) - 1) * 2 = 0 := by linear_combination htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right h2)
  have hW : Gm * W = W * Gm := by
    rw [hu1, one_smul] at h1
    calc Gm * W = Gm * W * (Gi * Gm) := by rw [hGiG, Matrix.mul_one]
      _ = (Gm * W * Gi) * Gm := by simp only [Matrix.mul_assoc]
      _ = W * Gm := by rw [h1]
  have hlam0 : lam ≠ 0 := by
    intro h0
    rcases hν with h | h <;> (rw [h0] at h; simp at h)
  have hiso' : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f) Gm * Gm = 1 := hiso
  have hIso : IsoSquare (unitaryInvolution (GaloisField p (2 * f)) p f) Gm lam :=
    ⟨fun u v => by rw [herm_mulVec, hiso', Matrix.one_mulVec], hsq, hlam0⟩
  rcases hν with hν | hν
  · exfalso
    obtain ⟨W', hWnd, hW2, hWE, c0, hc0⟩ := exists_fixed_plane hf hp2 hIso hν hW
    have hfix := alpha_fixes_planeGroupU hf hmat' hIso hWnd hc0
    have hR := planeGroupU_mem hK hp2 (by norm_num : 2 ≤ 5 + 1) hWnd hW2
    obtain ⟨hRmem, hRK⟩ := hΘ.member _ hR
    obtain ⟨i, hi⟩ := hR
    have hperf := Subgroup.isPerfect_iff.mp (c.isPerfect_of_isLongRootSU2 hi)
    have hcomm := commutes_of_alpha_fixed hMFZ hsingle hshape hΘ hN.1 hv hNK hα hperf hfix
    have hvis : (planeGroupU (GaloisField p (2 * f)) p f W').map Θ ∈
        centralizingMembers Ω {z * nd.w 0, z} := by
      rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
      refine ⟨hRmem, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hw0, ← map_mul, ← map_mul]
      have := planeGroupU_le_centralizer hp2 hf hWnd hW2 hWE hx
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      rw [this]
    exact hF1 N hN hNK hNj _ hvis hRK hcomm
  · have hdata : IsotropicData (unitaryInvolution (GaloisField p (2 * f)) p f) Gm lam :=
      ⟨hIso, hν⟩
    obtain ⟨P, hAB⟩ := exists_adaptedBasis hf hp2 hdata hW
    exact adaptedFrame_of_adaptedBasis hf hp2 hq hmat' hAB

end Frames

section Final

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.Theorem5

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem te6Adaptation_of_partner (hf : 1 ≤ f) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeU p f 5 Ω z) (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}
    (hβ : IsPartnerU c nd β) (hn3 : ¬ Commutes β (nd.j 3))
    (hP1x : LocalOddCentral Ω {z * nd.w 0}) : TE6Adaptation hf nd := by
  obtain ⟨Dz, -⟩ := id hshape
  exact te6Adaptation_of_adaptedFrames hf hMFZ hsingle hshape c nd
    (te6AdaptedFrames_of_isolated' hf hMFZ hsingle hshape c nd
      (te6PartnerIsolated_of_partner hMFZ hIH c nd hsingle Dz hβ hn3 hP1x)
      (te6NotGraphField_of_partner hMFZ hIH c nd hsingle hshape hβ hn3 hP1x))

theorem routeD_typeU_five_of_partner (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω)
    (hP1x : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → LocalOddCentral Ω {z * nd.w 0}) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 :=
  routeD_typeU_five_of_adaptation_noexc hp2 hadm hq hΩ hex hK hsingle hconn hz hshape hP1 hMFZ hIH
    hP1x fun c nd {_} hβ hn => te6Adaptation_of_partner hadm.2.1 hMFZ hIH hsingle hshape c nd hβ hn
      (hP1x c nd hβ hn)

end Final

end CFSG.ClassicalInvolution.RouteD.NonClassical
