module

public import CFSG.ClassicalInvolution.Q3.Q3E6TAdapt
public import CFSG.ClassicalInvolution.Q3.Q3E6TFrames
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptClass

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC Module
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

omit [Group G] in
theorem eq_of_mem_of_orderOf_eq_two3 [Group G] {L : Subgroup G}
    (hL : classicalInvolutionOddCore L = ⊥) {z : G} (hz : IsClassicalMember3 L z) {y : G}
    (hy : y ∈ L) (hy2 : orderOf y = 2) : y = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hL
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have key : ∀ {y : G} (hy : y ∈ L) (hy2 : orderOf y = 2), e ⟨y, hy⟩ = -1 := by
    intro y hy hy2
    have hyy : y * y = 1 := by
      rw [← pow_two]
      have := pow_orderOf_eq_one y
      rwa [hy2] at this
    have h1 : (⟨y, hy⟩ : ↥L) * ⟨y, hy⟩ = 1 := Subtype.ext hyy
    have h3 : e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1 := by rw [← map_mul, h1, map_one]
    rcases sl2_sq_eq_one h2 h3 with h | h
    · exfalso
      have : (⟨y, hy⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
      have h4 : y = 1 := congrArg Subtype.val this
      rw [h4, orderOf_one] at hy2
      omega
    · exact h
  have := e.injective ((key hy hy2).trans (key hz.mem hz.orderOf_eq_two).symm)
  exact congrArg Subtype.val this

variable [Finite G]

theorem map_zEltU_eq3 {c : UCtx3 5 (conjClass3 K) K z} {nd : UNodes3 c}
    {Θ : Su (GaloisField 3 2) 3 1 6 →* G} (hΘ : TE6Chart3 c nd Θ) {a : ℕ} (ha : a < 5) :
    Θ (zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha)) = nd.w a := by
  have hnode : zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha) ∈
      (blockEmb2 (GaloisField 3 2) 3 1 5 ⟨a, ha⟩).range := by
    rw [range_blockEmb2_eq_LcU_nodePair two_ne_zero_gf9 ha]
    exact (isLongRootSU2_LcU two_ne_zero_gf9 c.hn (nodePair 5 a ha)).mem
  have hmem : Θ (zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha)) ∈ nd.j a := by
    rw [← hΘ.block ⟨a, ha⟩]
    exact Subgroup.mem_map_of_mem Θ hnode
  have hsq : Θ (zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha)) *
      Θ (zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha)) = 1 := by
    rw [← map_mul, zEltU_mul_self, map_one]
  have hne : Θ (zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha)) ≠ 1 := fun h1 =>
    zEltU_not_mem_center card_gf9 two_ne_zero_gf9 (by norm_num : 3 ≤ 5 + 1) (nodePair 5 a ha)
      (hΘ.ker_le (MonoidHom.mem_ker.mpr h1))
  have hord : orderOf (Θ (zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha))) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hne
  exact eq_of_mem_of_orderOf_eq_two3 (c.hex (nd.j a) (nd.mem a ha).1) (nd.isCl a ha) hmem hord

theorem map_te6Inv_eq3 {c : UCtx3 5 (conjClass3 K) K z} {nd : UNodes3 c}
    {Θ : Su (GaloisField 3 2) 3 1 6 →* G} (hΘ : TE6Chart3 c nd Θ) :
    Θ (te6Inv 3 1) = nd.w 0 :=
  map_zEltU_eq3 hΘ (by norm_num : 0 < 5)

section Involutory

variable {g : GL (Fin 6) (GaloisField 3 2)}
  {α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6}

theorem sq_scalar_of_involutory3
    (hα : ∀ x : Su (GaloisField 3 2) 3 1 6,
      ((α x : GL (Fin 6) (GaloisField 3 2)) :
        Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((x : GL (Fin 6) (GaloisField 3 2)) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 2)))
    (hα2 : α.comp α = MonoidHom.id _) :
    ∃ a : GaloisField 3 2, (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
      (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        a • (1 : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_gf9
  refine eq_smul_one_of_commute (unitaryFieldData_te6 (p := 3) (f := 1) le_rfl)
    (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : 3 ≤ 6) _ ?_
  intro y hy
  set x : Su (GaloisField 3 2) 3 1 6 :=
    (suEquivUnitarySU (GaloisField 3 2) 3 1 hK 6).symm ⟨y, hy⟩ with hx
  have hxy : ((x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6)
      (GaloisField 3 2)) = (y : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) := rfl
  have e0 : α (α x) = x := DFunLike.congr_fun hα2 x
  have e := congrArg (fun z : Su (GaloisField 3 2) 3 1 6 =>
    ((z : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))) e0
  simp only [hα] at e
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) :
      Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hGi
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hxy] at e
  calc Gm * Gm * (y : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))
      = (Gm * (Gm * (y : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) * Gi) * Gi) *
          (Gm * Gm) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Gi Gm Gm, hGiG, Matrix.one_mul, hGiG, Matrix.mul_one]
    _ = (y : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) * (Gm * Gm) := by rw [e]


theorem exists_lam3
    (hα : ∀ x : Su (GaloisField 3 2) 3 1 6,
      ((α x : GL (Fin 6) (GaloisField 3 2)) :
        Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((x : GL (Fin 6) (GaloisField 3 2)) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 2)))
    (hα2 : α.comp α = MonoidHom.id _)
    (hiso : conjTr (unitaryInvolution (GaloisField 3 2) 3 1)
      (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) = 1) :
    ∃ lam : GaloisField 3 2,
      (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
          (lam * lam) • (1 : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) ∧
      (unitaryInvolution (GaloisField 3 2) 3 1 lam * lam = 1 ∨
        unitaryInvolution (GaloisField 3 2) 3 1 lam * lam = -1) := by
  set σ := unitaryInvolution (GaloisField 3 2) 3 1 with hσ
  obtain ⟨a, ha⟩ := sq_scalar_of_involutory3 hα hα2
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))
    with hGm
  have h1 : conjTr σ (Gm * Gm) * (Gm * Gm) = 1 := by
    rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ Gm) Gm Gm, hiso,
      Matrix.one_mul, hiso]
  rw [ha] at h1
  have h2 : conjTr σ (a • (1 : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))) = σ a • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [conjTr]
    · simp [conjTr, hij, Ne.symm hij]
  rw [h2, Matrix.smul_mul, Matrix.one_mul] at h1
  have hN : σ a * a = 1 := by
    have := congrFun (congrFun h1 0) 0
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  obtain ⟨lam, hlam⟩ := exists_sqrt_of_norm_one (p := 3) (f := 1) (by norm_num : (3 : ℕ) ≠ 2)
    le_rfl hN
  refine ⟨lam, by rw [hlam, ha], ?_⟩
  have h3 : (σ lam * lam) * (σ lam * lam) = 1 := by
    calc (σ lam * lam) * (σ lam * lam) = σ (lam * lam) * (lam * lam) := by rw [map_mul]; ring
      _ = 1 := by rw [hlam, hN]
  exact mul_self_eq_one_iff.mp h3

end Involutory

section Isolated

@[expose] def TE6PartnerIsolated3 (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) : Prop :=
  ∀ N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0},
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N (nd.j 0)) →
    ∀ L ∈ centralizingMembers (conjClass3 K) {z * nd.w 0, z}, L ≠ K → ¬ Commutes N L

@[expose] def TE6NotGraphField3 (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) : Prop :=
  ∀ N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0},
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N (nd.j 0)) →
    ∀ Θ : Su (GaloisField 3 2) 3 1 6 →* G, TE6Chart3 c nd Θ →
    ∀ v : G, IsClassicalMember3 N v →
    ∀ (α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6)
      (g : GL (Fin 6) (GaloisField 3 2)) (φ : GaloisField 3 2 ≃+* GaloisField 3 2),
      (∀ x, Θ (α x) = v * Θ x * v⁻¹) →
      (∀ x, ((α x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          φ.mapMatrix ((x : GL (Fin 6) (GaloisField 3 2)) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))) →
      conjTr (unitaryInvolution (GaloisField 3 2) 3 1)
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) = 1 →
      (φ = RingEquiv.refl (GaloisField 3 2) ∨ φ = unitaryInvolution (GaloisField 3 2) 3 1) →
      α.comp α = MonoidHom.id _ → φ = RingEquiv.refl (GaloisField 3 2)

end Isolated

section Frames


theorem commutes_member_of_centralizes3 (c : UCtx3 5 (conjClass3 K) K z)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z)
    {N : Subgroup G} (hN : N ∈ conjClass3 K) {v : G} (hv : IsClassicalMember3 N v)
    (hNK : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) {M : Subgroup G}
    (hM : M ∈ centralizingMembers (conjClass3 K) {z}) (hMK : Commutes K M)
    (hMv : M ≤ Subgroup.centralizer ({v} : Set G)) : Commutes N M := by
  classical
  obtain ⟨W, hW⟩ := hNK
  have hnK : ¬ Commutes K N := not_commutes_of_linearBlockStandardPair hW
  obtain ⟨ι, hι, D, -, -⟩ := hshape
  obtain ⟨h, hh⟩ := hsingle N hN
  have ht_eq : v = h * z * h⁻¹ := involution_unique3 hv (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral (conjClass3 K) {v} := by
    rw [ht_eq]
    exact Gaps.localOddCentral_conj c.hΩ.conjInvariant h z c.hP1
  have hO3t : LocalOddThreeFree3 (conjClass3 K) v := by
    rw [ht_eq]
    exact localOddThreeFree3_conj c.hΩ.conjInvariant h z c.hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 c.hΩ.conjInvariant h z D
  rw [← ht_eq] at Dt
  exact ((commutes_iff_le_centralizer3 (Gaps.fundNoncentral 3) c.hΩ c.hex hP1t hO3t Dt hN hv hM.1
    hMK.symm hnK).mpr hMv).symm

theorem te6AdaptedFrames3_of_isolated
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z)
    (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) (hF1 : TE6PartnerIsolated3 c nd)
    (hF2 : TE6NotGraphField3 c nd) : TE6AdaptedFrames3 c nd := by
  classical
  intro N hN hNK hNj Θ hΘ v hv α hα
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_gf9
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hvz : v * z * v⁻¹ = z := partner_involution_commutes3 c.hz hv hNK
  have hv2 : v * v = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one v
    rwa [hv.orderOf_eq_two] at this
  obtain ⟨α', g, φ, hα', hmat, hiso, hφ, hα2⟩ := hΘ.exists_alpha hvz hv2
  have : Group.IsPerfect (Su (GaloisField 3 2) 3 1 6) := isPerfect_su_three_le (by norm_num)
  have hαα : α = α' := ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hΘ.ker_le α α'
    (fun x => by rw [hα x, hα' x])
  subst hαα
  have hφ1 : φ = RingEquiv.refl _ := hF2 N hN hNK hNj Θ hΘ v hv α g φ hα hmat hiso hφ hα2
  subst hφ1
  have hmat' : ∀ x : Su (GaloisField 3 2) 3 1 6,
      ((α x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) :=
    fun x => by
    rw [hmat x]
    simp
  obtain ⟨lam, hsq, hν⟩ := exists_lam3 hmat' hα2 hiso
  have hw0 : Θ (te6Inv 3 1) = nd.w 0 := map_te6Inv_eq3 hΘ
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
  have hfixw : (MulAut.conj v) (Θ (te6Inv 3 1)) = Θ (te6Inv 3 1) := by
    rw [hw0]
    exact hvw
  obtain ⟨u, hu⟩ := lift_matrix_of_fixed (n := 6) hK (by norm_num : 3 ≤ 6) hΘ.ker_le
    (σ := MulAut.conj v) (α := α) (fun x => hα x) (x := te6Inv 3 1) hfixw
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hGi
  set W : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) := suMat (te6Inv 3 1) with hWdef
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : Gm * W * Gi = (u : GaloisField 3 2) • W := (hmat' (te6Inv 3 1)).symm.trans hu
  have htr : Matrix.trace (Gm * W * Gi) = Matrix.trace W := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have htr2 : Matrix.trace W = (2 : GaloisField 3 2) := trace_te6Inv
  have hu1 : (u : GaloisField 3 2) = 1 := by
    rw [h1, Matrix.trace_smul, htr2, smul_eq_mul] at htr
    have h3 : ((u : GaloisField 3 2) - 1) * 2 = 0 := by linear_combination htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right two_ne_zero_gf9)
  have hW : Gm * W = W * Gm := by
    rw [hu1, one_smul] at h1
    calc Gm * W = Gm * W * (Gi * Gm) := by rw [hGiG, Matrix.mul_one]
      _ = (Gm * W * Gi) * Gm := by simp only [Matrix.mul_assoc]
      _ = W * Gm := by rw [h1]
  have hlam0 : lam ≠ 0 := by
    intro h0
    rcases hν with h | h <;> (rw [h0] at h; simp at h)
  have hiso' : conjTr (unitaryInvolution (GaloisField 3 2) 3 1) Gm * Gm = 1 := hiso
  have hIso : IsoSquare (unitaryInvolution (GaloisField 3 2) 3 1) Gm lam :=
    ⟨fun u v => by rw [herm_mulVec, hiso', Matrix.one_mulVec], hsq, hlam0⟩
  rcases hν with hν | hν
  · exfalso
    obtain ⟨W', hWnd, hW2, hWE, c0, hc0⟩ := exists_fixed_plane le_rfl hp2 hIso hν hW
    have hfix := alpha_fixes_planeGroupU le_rfl hmat' hIso hWnd hc0
    have hR := planeGroupU_mem hK hp2 (by norm_num : 2 ≤ 5 + 1) hWnd hW2
    obtain ⟨hRmem, hRK⟩ := hΘ.member _ hR
    have hMK : Commutes K ((planeGroupU (GaloisField 3 2) 3 1 W').map Θ) :=
      fun k hk x hx => hΘ.commutes_K_range k hk x (Subgroup.map_le_range Θ _ hx)
    have hMv : (planeGroupU (GaloisField 3 2) 3 1 W').map Θ ≤
        Subgroup.centralizer ({v} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (TE6Chart3.centralizes_of_fixed hα (hfix x hx)).symm
    have hcomm := commutes_member_of_centralizes3 c hsingle hshape hN.1 hv hNK hRmem hMK hMv
    have hvis : (planeGroupU (GaloisField 3 2) 3 1 W').map Θ ∈
        centralizingMembers (conjClass3 K) {z * nd.w 0, z} := by
      rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
      refine ⟨hRmem, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hw0, ← map_mul, ← map_mul]
      have := planeGroupU_le_centralizer hp2 le_rfl hWnd hW2 hWE hx
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      rw [this]
    exact hF1 N hN hNK hNj _ hvis hRK hcomm
  · have hdata : IsotropicData (unitaryInvolution (GaloisField 3 2) 3 1) Gm lam := ⟨hIso, hν⟩
    obtain ⟨P, hAB⟩ := exists_adaptedBasis le_rfl hp2 hdata hW
    exact adaptedFrame_of_adaptedBasis3 hmat' hAB

end Frames

end CFSG.ClassicalInvolution.Q3.Q3E6T
