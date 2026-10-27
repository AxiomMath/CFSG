module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STDiag

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace sub_mem_commSpace)

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem commSp_simAct (γ : simGroup Q) (t : OGroup Q) :
    commSp (simAct Q γ t) = (commSp t).map (γ : V →ₗ[ZMod 3] V) := by
  change commSpace ((simAct Q γ t : OGroup Q) : V ≃ₗ[ZMod 3] V) =
    (commSpace (t : V ≃ₗ[ZMod 3] V)).map (γ : V →ₗ[ZMod 3] V)
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V).symm m) -
      (γ : V ≃ₗ[ZMod 3] V).symm m, sub_mem_commSpace (t : V ≃ₗ[ZMod 3] V) _, ?_⟩
    simpa only [map_sub, coe_simAct, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply, LinearEquiv.coe_coe] using hm
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    refine ⟨(γ : V ≃ₗ[ZMod 3] V) v, ?_⟩
    simp only [coe_simAct, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, map_sub, LinearEquiv.coe_coe]

private theorem invDim_simAct (γ : simGroup Q) (t : OGroup Q) :
    invDim (simAct Q γ t) = invDim t := by
  simp only [invDim]
  rw [commSp_simAct]
  exact LinearEquiv.finrank_map_eq _ _

private theorem orthToSim_simAct (γ : simGroup Q) (t : OGroup Q) :
    orthToSim Q (simAct Q γ t) = γ * orthToSim Q t * γ⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_orthToSim, coe_simAct]

theorem sec9t_commute_of_phiSim (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    {g : OGroup Q} (hg : g * g = 1) (hev : Even (invDim g)) (γ : simGroup Q)
    (hc : (QuotientGroup.mk γ : ProjSim Q) * phiSim Q g = phiSim Q g * QuotientGroup.mk γ) :
    (γ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) = (g : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V) := by
  have hphi : phiSim Q (simAct Q γ g) = phiSim Q g := by
    have h1 : phiSim Q (simAct Q γ g) =
        (QuotientGroup.mk γ : ProjSim Q) * phiSim Q g *
          (QuotientGroup.mk γ : ProjSim Q)⁻¹ := by
      simp only [phiSim, MonoidHom.comp_apply, projOrthToProjSim_toProj, orthToSim_simAct,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1, hc, mul_assoc, mul_inv_cancel, mul_one]
  have hker : phiSim Q (simAct Q γ g * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hphi, mul_inv_cancel]
  rcases phiSim_eq_one_iff.mp hker with h1 | h1
  · have hsim : simAct Q γ g = g := by
      have := congrArg (fun z => z * g) h1
      simpa [mul_assoc] using this
    have hcoe : (γ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V)⁻¹ =
        (g : V ≃ₗ[ZMod 3] V) := by
      have hcong := congrArg (fun t : OGroup Q => (t : V ≃ₗ[ZMod 3] V)) hsim
      simpa only [coe_simAct] using hcong
    exact (mul_inv_eq_iff_eq_mul).mp hcoe
  · have hsim : simAct Q γ g = piOrth Q * g := by
      have := congrArg (fun z => z * g) h1
      simpa [mul_assoc] using this
    have hdim : invDim g = Module.finrank (ZMod 3) V - invDim g := by
      calc invDim g = invDim (simAct Q γ g) := (invDim_simAct γ g).symm
        _ = invDim (piOrth Q * g) := by rw [hsim]
        _ = Module.finrank (ZMod 3) V - invDim g := by
            have := congrArg Prod.fst (invType_piOrth_mul hQ hg)
            simpa only [invType] using this
    rw [h6] at hdim
    have hle : invDim g ≤ 6 := by rw [← h6]; exact invDim_le g
    obtain ⟨k, hk⟩ := hev
    omega

theorem sec9t_lift_diag (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft)
    (hn : 3 ≤ n) (hsq : ∀ g ∈ Ft, g * g = 1) (hev : ∀ g ∈ Ft, Even (invDim g))
    {u : ProjSim Q} (hu : ∀ g ∈ Ft, u * phiSim Q g = phiSim Q g * u) :
    ∃ (g : OGroup Q) (T : Finset (Fin n)), phiSim Q g = u ∧
      ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective u
  have hcomm : ∀ g ∈ Ft, (γ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) =
      (g : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V) :=
    fun g hg => sec9t_commute_of_phiSim hQ h6 (hsq g hg) (hev g hg) γ (hu g hg)
  have hscalar : ∀ i, ∃ x : ZMod 3, x ≠ 0 ∧ (γ : V ≃ₗ[ZMod 3] V) (b i) = x • b i :=
    fun i => sec9t_scalar_of_commute hb hn hcomm i
  obtain ⟨c, hc⟩ := γ.2
  have hc1 : c = 1 := by
    let i0 : Fin n := ⟨0, by omega⟩
    obtain ⟨x, hx, hxw⟩ := hscalar i0
    exact sec9t_multiplier_eq_one hc hx hxw (IsEvenFrame.map_ne_zero hQ hb hn i0)
  have hmem : (γ : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    isSimilitude_one_iff.mp (hc1 ▸ hc)
  let g' : OGroup Q := ⟨(γ : V ≃ₗ[ZMod 3] V), hmem⟩
  obtain ⟨T, hT⟩ := sec9t_exists_signs (b := b) hscalar
  refine ⟨g', T, ?_, ?_⟩
  · rw [show phiSim Q g' = QuotientGroup.mk (orthToSim Q g') from rfl,
      show orthToSim Q g' = γ from Subtype.ext rfl]
  · intro i
    exact hT i

end CFSG.OddStandard.SmallF3.Omega
