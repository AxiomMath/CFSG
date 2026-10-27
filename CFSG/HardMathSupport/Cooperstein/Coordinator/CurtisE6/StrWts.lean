module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Digits
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Wts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open scoped MatrixGroups


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem exists_sq_unit (u : Kˣ) : ∃ z : Kˣ, z ^ 2 = u := by
  have hinj : Function.Injective (fun z : Kˣ => z ^ 2) := by
    intro a b h
    have h1 : (a : K) ^ 2 = (b : K) ^ 2 := by
      have := congrArg Units.val h
      simpa using this
    have h2 : frobenius K 2 (a : K) = frobenius K 2 (b : K) := by
      simpa [frobenius_def] using h1
    exact Units.ext ((frobenius_inj K 2) h2)
  obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.1 hinj u
  exact ⟨z, hz⟩

theorem hm_conj_xr (i s : N6) (t : Kˣ) (c : K) :
    e6Data_valid.hm K i t * e6Data_valid.xm K (Pi.single s 1) c * (e6Data_valid.hm K i t)⁻¹ =
      e6Data_valid.xm K (Pi.single s 1) (((t ^ Tag.cartan .E6 i s : Kˣ) : K) * c) := by
  rw [e6Data_valid.hm_conj_xm K (isRoot_single _ s) i t c, MinData.toWeight_single]

theorem hm_conj_yr (i s : N6) (t : Kˣ) (c : K) :
    e6Data_valid.hm K i t * e6Data_valid.xm K (-Pi.single s 1) c * (e6Data_valid.hm K i t)⁻¹ =
      e6Data_valid.xm K (-Pi.single s 1) (((t ^ (-Tag.cartan .E6 i s) : Kˣ) : K) * c) := by
  rw [e6Data_valid.hm_conj_xm K (isRoot_neg_single _ s) i t c, MinData.toWeight_neg, Pi.neg_apply,
    MinData.toWeight_single]

theorem conj_rankOne_eq (i s : N6) (t z : Kˣ) (hz : z ^ 2 = t ^ Tag.cartan .E6 i s)
    (g : SL(2, K)) :
    e6Data_valid.hm K i t * rankOne6 K s g * (e6Data_valid.hm K i t)⁻¹ =
      e6Data_valid.hm K s z * rankOne6 K s g * (e6Data_valid.hm K s z)⁻¹ := by
  have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  have hz' : z ^ (2 : ℤ) = t ^ Tag.cartan .E6 i s := by rw [zpow_ofNat]; exact hz
  let f₁ : SL(2, K) →* ↥(e6Data_valid.minGroup K) :=
    (MulAut.conj (e6Data_valid.hm K i t)).toMonoidHom.comp (rankOne6 K s)
  let f₂ : SL(2, K) →* ↥(e6Data_valid.minGroup K) :=
    (MulAut.conj (e6Data_valid.hm K s z)).toMonoidHom.comp (rankOne6 K s)
  have hle : Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) ≤ MonoidHom.eqLocus f₁ f₂ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show f₁ (uElt c) = f₂ (uElt c)
      simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rankOne6_u, hm_conj_xr, Tag.cartan_self]
      rw [hz']
    · show f₁ (lElt c) = f₂ (lElt c)
      simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rankOne6_l, hm_conj_yr, Tag.cartan_self]
      rw [show z ^ (-2 : ℤ) = t ^ (-Tag.cartan .E6 i s) by rw [zpow_neg, hz', zpow_neg]]
  have hg : g ∈ MonoidHom.eqLocus f₁ f₂ := hle (by rw [hcl]; exact Subgroup.mem_top g)
  exact hg

theorem hm_inv (i : N6) (t : Kˣ) : (e6Data_valid.hm K i t)⁻¹ = e6Data_valid.hm K i t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← e6Data_valid.hm_mul, mul_inv_cancel, e6Data_valid.hm_one]

theorem weight_shift (ρ : Representation k ↥(e6Data_valid.minGroup K) V) (s : N6) {y : V}
    (E : N6 → ℤ)
    (hy : ∀ i t, ρ (e6Data_valid.hm K i t) y = kp (k := k) K t (E i) • y) (m : ℤ) {e : V}
    (he : e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y)
    (hes : ∀ z : Kˣ, ρ (e6Data_valid.hm K s z) e = kp (k := k) K z (E s - 2 * m) • e) (i : N6)
    (t : Kˣ) : ρ (e6Data_valid.hm K i t) e = kp (k := k) K t (E i - Tag.cartan .E6 i s * m) • e := by
  obtain ⟨z, hz⟩ := exists_sq_unit (t ^ Tag.cartan .E6 i s)
  have hclaim : ∀ e' ∈ orbitSpan (ρ.comp (rankOne6 K s)) y,
      ρ (e6Data_valid.hm K i t) e' = (kp (k := k) K t (E i) * kp (k := k) K z (-E s)) •
        ρ (e6Data_valid.hm K s z) e' := by
    intro e' he'
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      show ρ (e6Data_valid.hm K i t) (ρ (rankOne6 K s g) y) =
        _ • ρ (e6Data_valid.hm K s z) (ρ (rankOne6 K s g) y)
      have h1 : e6Data_valid.hm K i t * rankOne6 K s g =
          (e6Data_valid.hm K s z * rankOne6 K s g * (e6Data_valid.hm K s z)⁻¹) *
            e6Data_valid.hm K i t := by
        rw [← conj_rankOne_eq i s t z hz g]; group
      rw [act_mul, h1, ← act_mul, ← act_mul, ← act_mul, hy i t, map_smul, hm_inv, hy s z⁻¹,
        kp_inv_unit, map_smul, map_smul, map_smul, map_smul, smul_smul]
    | zero => simp
    | add x y _ _ hx hy' => rw [map_add, map_add, hx, hy', smul_add]
    | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]
  rw [hclaim e he, hes z, smul_smul]
  congr 1
  have h1 : kp (k := k) K z (-E s) * kp (k := k) K z (E s - 2 * m) =
      kp (k := k) K z (2 * (-m)) := by
    rw [← kp_add]; congr 1; ring
  have h2 : kp (k := k) K z (2 * (-m)) = kp (k := k) K t (Tag.cartan .E6 i s * (-m)) := by
    rw [← kp_zpow_unit, zpow_ofNat, hz, kp_zpow_unit]
  rw [mul_assoc, h1, h2, ← kp_add]
  congr 1
  ring

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
