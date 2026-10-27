module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Weights
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Strings
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section StringWts


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
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

theorem dC_conj_xC (i j : Fin τ.rank) (t : Kˣ) (c : K) :
    dC τ K i t * xC τ K j c * (dC τ K i t)⁻¹ = xC τ K j (((t ^ τ.cartan i j : Kˣ) : K) * c) :=
  Subtype.ext (CFSG.StandardType.RootCentExc.torusElt_conj_xUnit i j t c)

theorem dC_conj_yC (i j : Fin τ.rank) (t : Kˣ) (c : K) :
    dC τ K i t * yC τ K j c * (dC τ K i t)⁻¹ = yC τ K j (((t ^ (-τ.cartan i j) : Kˣ) : K) * c) :=
  Subtype.ext (CFSG.StandardType.RootCentExc.torusElt_conj_yUnit i j t c)

theorem conj_rankOne_eq (i s : Fin τ.rank) (t z : Kˣ) (hz : z ^ 2 = t ^ τ.cartan i s)
    (g : SL(2, K)) :
    dC τ K i t * rankOne τ K s g * (dC τ K i t)⁻¹ =
      dC τ K s z * rankOne τ K s g * (dC τ K s z)⁻¹ := by
  have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  have hz' : z ^ (2 : ℤ) = t ^ τ.cartan i s := by rw [zpow_ofNat]; exact hz
  let f₁ : SL(2, K) →* adjointGroup τ K :=
    (MulAut.conj (dC τ K i t)).toMonoidHom.comp (rankOne τ K s)
  let f₂ : SL(2, K) →* adjointGroup τ K :=
    (MulAut.conj (dC τ K s z)).toMonoidHom.comp (rankOne τ K s)
  have hle : Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) ≤ MonoidHom.eqLocus f₁ f₂ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show f₁ (uElt c) = f₂ (uElt c)
      simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rankOne_u, dC_conj_xC, Tag.cartan_self]
      rw [hz']
    · show f₁ (lElt c) = f₂ (lElt c)
      simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rankOne_l, dC_conj_yC, Tag.cartan_self]
      rw [show z ^ (-2 : ℤ) = t ^ (-τ.cartan i s) by rw [zpow_neg, hz', zpow_neg]]
  have hg : g ∈ MonoidHom.eqLocus f₁ f₂ := hle (by rw [hcl]; exact Subgroup.mem_top g)
  exact hg

theorem kpow_inv_unit (t : Kˣ) (f : ℤ) : kpow (k := k) K t⁻¹ f = kpow K t (-f) := by
  have := kpow_zpow_unit (k := k) (K := K) t (-1) f
  rw [zpow_neg_one] at this
  rw [this]; congr 1; ring

theorem dC_inv (i : Fin τ.rank) (t : Kˣ) : (dC τ K i t)⁻¹ = dC τ K i t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← dC_mul, mul_inv_cancel, dC_one]

theorem weight_shift (ρ : Representation k (adjointGroup τ K) V) (s : Fin τ.rank) {y : V}
    (E : Fin τ.rank → ℤ)
    (hy : ∀ i t, ρ (dC τ K i t) y = kpow (k := k) K t (E i) • y) (m : ℤ) {e : V}
    (he : e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y)
    (hes : ∀ z : Kˣ, ρ (dC τ K s z) e = kpow (k := k) K z (E s - 2 * m) • e) (i : Fin τ.rank)
    (t : Kˣ) : ρ (dC τ K i t) e = kpow (k := k) K t (E i - τ.cartan i s * m) • e := by
  obtain ⟨z, hz⟩ := exists_sq_unit (t ^ τ.cartan i s)
  have hclaim : ∀ e' ∈ orbitSpan (ρ.comp (rankOne τ K s)) y,
      ρ (dC τ K i t) e' = (kpow (k := k) K t (E i) * kpow (k := k) K z (-E s)) •
        ρ (dC τ K s z) e' := by
    intro e' he'
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      show ρ (dC τ K i t) (ρ (rankOne τ K s g) y) = _ • ρ (dC τ K s z) (ρ (rankOne τ K s g) y)
      have h1 : dC τ K i t * rankOne τ K s g =
          (dC τ K s z * rankOne τ K s g * (dC τ K s z)⁻¹) * dC τ K i t := by
        rw [← conj_rankOne_eq i s t z hz g]; group
      rw [act_mul, h1, ← act_mul, ← act_mul, ← act_mul, hy i t, map_smul, dC_inv, hy s z⁻¹,
        kpow_inv_unit, map_smul, map_smul, map_smul, map_smul, smul_smul]
    | zero => simp
    | add x y _ _ hx hy' => rw [map_add, map_add, hx, hy', smul_add]
    | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]
  rw [hclaim e he, hes z, smul_smul]
  congr 1
  have h1 : kpow (k := k) K z (-E s) * kpow (k := k) K z (E s - 2 * m) =
      kpow (k := k) K z (2 * (-m)) := by
    rw [← kpow_add]; congr 1; ring
  have h2 : kpow (k := k) K z (2 * (-m)) = kpow (k := k) K t (τ.cartan i s * (-m)) := by
    rw [← kpow_zpow_unit, zpow_ofNat, hz, kpow_zpow_unit]
  rw [mul_assoc, h1, h2, ← kpow_add]
  congr 1
  ring

end StringWts

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
