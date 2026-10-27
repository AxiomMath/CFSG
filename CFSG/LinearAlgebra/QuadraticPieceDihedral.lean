module

public import CFSG.GroupTheory.QuadraticPlaneIsometry
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviUnipotent
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock

public section

namespace CFSG.LinearAlgebra

open QuadraticMap TauCeti.QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

section Restrict

variable [FiniteDimensional F V]

theorem restrictEquiv_pow_apply (U : Submodule F V) (g : V ≃ₗ[F] V)
    (h1 : ∀ v ∈ U, g v ∈ U) (h2 : ∀ v ∈ U, g⁻¹ v ∈ U) (n : ℕ) (v : U) :
    ((restrictEquiv U g h1 h2 ^ n) v : V) = (g ^ n) (v : V) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, coe_restrictEquiv, pow_succ g,
      LinearEquiv.mul_apply]

theorem restrictEquiv_inv (U : Submodule F V) (g : V ≃ₗ[F] V)
    (h1 : ∀ v ∈ U, g v ∈ U) (h2 : ∀ v ∈ U, g⁻¹ v ∈ U) :
    (restrictEquiv U g h1 h2)⁻¹ = restrictEquiv U g⁻¹ h2 h1 := by
  rw [inv_eq_iff_mul_eq_one]
  ext v
  simp [LinearEquiv.mul_apply, coe_restrictEquiv]

theorem restrictEquiv_mem_orthogonalGroup {Q : QuadraticForm F V} {e : V ≃ₗ[F] V}
    (he : e ∈ orthogonalGroup Q) {U : Submodule F V} (h1 : ∀ v ∈ U, e v ∈ U)
    (h2 : ∀ v ∈ U, e⁻¹ v ∈ U) :
    restrictEquiv U e h1 h2 ∈ orthogonalGroup (Q.comp U.subtype) := by
  rw [mem_orthogonalGroup_iff]
  intro v
  change Q ((restrictEquiv U e h1 h2 v : U) : V) = Q (v : V)
  rw [coe_restrictEquiv]
  exact (mem_orthogonalGroup_iff.mp he) (v : V)

end Restrict

section Pieces

variable [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {x : V ≃ₗ[F] V}

theorem commute_of_isPGroup_of_pieces (h2 : (2 : F) ≠ 0) (hp : Odd p)
    {x : V ≃ₗ[F] V} (hxQ : x ∈ orthogonalGroup Q) (hxp : x ^ p = 1)
    {ι : Type*} [Fintype ι] (P : ι → Submodule F V) (hspan : ⨆ i, P i = ⊤)
    (hxP : ∀ i, ∀ v ∈ P i, x v ∈ P i)
    (hplane : ∀ i, (∀ v ∈ P i, x v = v) ∨
      ∃ xP : P i ≃ₗ[F] P i, (∀ v, (xP v : V) = x v) ∧
        (QuadraticMap.polarBilin (Q.comp (P i).subtype)).Nondegenerate ∧
        Module.finrank F (P i) = 2 ∧ LinearEquiv.det xP = 1)
    {S : Subgroup (V ≃ₗ[F] V)} (hS2 : IsPGroup 2 S)
    (hSQ : S ≤ orthogonalGroup Q)
    (hxS : x ∈ Subgroup.normalizer (S : Set (V ≃ₗ[F] V)))
    (hSP : ∀ s ∈ S, ∀ i, ∀ v ∈ P i, s v ∈ P i) :
    ∀ s ∈ S, s * x = x * s := by
  intro s hs
  have hxS' : ∀ t ∈ S, x * t * x⁻¹ ∈ S := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp hxS t).mp ht
  have hxinvP : ∀ i, ∀ v ∈ P i, x⁻¹ v ∈ P i := fun i =>
    CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hxP i)
  set y : V ≃ₗ[F] V := s * x * s⁻¹ * x⁻¹ with hy
  have hyS : y ∈ S := by
    rw [hy]
    simpa only [mul_assoc] using S.mul_mem hs (hxS' s⁻¹ (S.inv_mem hs))
  have hyP : ∀ i, ∀ v ∈ P i, y v ∈ P i := by
    intro i v hv
    show s (x (s⁻¹ (x⁻¹ v))) ∈ P i
    exact hSP s hs i _ (hxP i _ (hSP s⁻¹ (S.inv_mem hs) i _ (hxinvP i v hv)))
  have hyPowFix : ∀ i, ∀ v ∈ P i, (y ^ p) v = v := by
    intro i v hv
    let a := restrictEquiv (P i) x (hxP i)
      (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hxP i))
    let b := restrictEquiv (P i) s (hSP s hs i)
      (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hSP s hs i))
    let r := restrictEquiv (P i) y (hyP i)
      (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hyP i))
    have ha_pow : a ^ p = 1 := by
      ext w
      rw [restrictEquiv_pow_apply, hxp]
      rfl
    have hr : r ^ p = 1 := by
      have hb_inv : b⁻¹ = restrictEquiv (P i) s⁻¹
          (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hSP s hs i))
          (hSP s hs i) := by
        rw [restrictEquiv_inv]
      have ha_inv : a⁻¹ = restrictEquiv (P i) x⁻¹
          (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hxP i)) (hxP i) := by
        rw [restrictEquiv_inv]
      have hreq : r = b * a * b⁻¹ * a⁻¹ := by
        ext w
        simp only [r, a, b, hb_inv, ha_inv, hy, LinearEquiv.mul_apply,
          coe_restrictEquiv]
      rcases hplane i with hfix | ⟨xP, hagree, hQp, hdim, hdet⟩
      · have ha_one : a = 1 := by
          ext w
          rw [coe_restrictEquiv]
          exact hfix w w.2
        rw [hreq, ha_one]
        group
      · have ha_xP : a = xP := by
          ext w
          rw [coe_restrictEquiv]
          exact (hagree w).symm
        have hbO : b ∈ orthogonalGroup (Q.comp (P i).subtype) :=
          restrictEquiv_mem_orthogonalGroup (hSQ hs) (hSP s hs i)
            (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hSP s hs i))
        have haO : a ∈ orthogonalGroup (Q.comp (P i).subtype) :=
          restrictEquiv_mem_orthogonalGroup hxQ (hxP i)
            (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hxP i))
        have hadet : LinearEquiv.det a = 1 := by rw [ha_xP, hdet]
        have hcomm := CFSG.GroupTheory.isometry_commute_or_inv_of_det_eq_one
          h2 hQp hdim hbO
        rcases hcomm with hcomm | hinv
        · have h1 : b * a * b⁻¹ = a := by
            rw [hcomm a haO hadet]
            group
          rw [hreq, h1, mul_inv_cancel, one_pow]
        · have h1 : b * a * b⁻¹ = a⁻¹ := hinv a haO hadet
          have hsq : a⁻¹ * a⁻¹ = (a ^ 2)⁻¹ := by group
          rw [hreq, h1, hsq, inv_pow, ← pow_mul, Nat.mul_comm, pow_mul, ha_pow, one_pow,
            inv_one]
    have h := restrictEquiv_pow_apply (P i) y (hyP i)
      (CFSG.SeitzReduction.OmegaPilot.symm_mem_of_mapsTo (hyP i)) p ⟨v, hv⟩
    rw [hr] at h
    exact h.symm
  have hy_pow_one : y ^ p = 1 := by
    have hz : (y ^ p).toLinearMap - 1 = 0 := by
      rw [← LinearMap.ker_eq_top, ← top_le_iff, ← hspan]
      refine iSup_le fun i w hw => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
      change (y ^ p) w - w = 0
      rw [hyPowFix i w hw, sub_self]
    ext v
    have h := congrArg (fun f : V →ₗ[F] V => f v) hz
    simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using h
  have hdvd : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy_pow_one
  have hodd : Odd (orderOf y) := Odd.of_dvd_nat hp hdvd
  obtain ⟨k, hk⟩ := hS2.exists_orderOf_eq_pow (⟨y, hyS⟩ : S)
  have hk' : orderOf y = 2 ^ k := by simpa only [Subgroup.orderOf_mk] using hk
  have hk0 : k = 0 := by
    by_contra hne
    rw [hk'] at hodd
    exact (Nat.not_odd_iff_even.mpr (by rw [Nat.even_pow]; exact ⟨even_two, hne⟩)) hodd
  have hy_one : y = 1 := by
    rw [← orderOf_eq_one_iff, hk', hk0, pow_zero]
  rw [hy] at hy_one
  calc s * x = (s * x * s⁻¹ * x⁻¹) * (x * s) := by group
    _ = x * s := by rw [hy_one, one_mul]

end Pieces

end CFSG.LinearAlgebra

end
