module

public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_conj_eq_rootDiagAut_of_innerDiagonal
    {τ : Tag} {F : Type} [Field F] [Finite F] (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hF : Odd (Nat.card F)) {α : MulAut (adjointGroup τ F)} {g : adjointGroup τ F}
    {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) =
      (g : ModGL τ F) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1) :
    ∃ (ψ : MulAut (adjointGroup τ F)) (b : Fin τ.rank → Fˣ), (∀ i, b i = 1 ∨ b i = -1) ∧
      ψ * α * ψ⁻¹ = rootDiagAut τ F b := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set L := AlgebraicClosure F
  set ι := algebraMap F L with hι
  set p := ringChar F with hp_def
  have hpF : CharP F p := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : F, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set bL : Fin τ.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i) with hbL
  set x := baseChangeGL ι (g : ModGL τ F) * rootDiagUnit τ bL with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness τ F hF L ι
  have hgG : baseChangeGL ι (g : ModGL τ F) ∈ adjointGroup τ L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup τ L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift τ L bL).1
  have hdb : baseChangeGL ι (rootDiagUnit τ a) = rootDiagUnit τ bL :=
    baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup τ F,
      x * baseChangeGL ι (h : ModGL τ F) * x⁻¹ = baseChangeGL ι (α h : ModGL τ F) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ F hF L Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit τ bL) = rootDiagUnit τ bL := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag bL) = rootDiag bL
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup τ F) => φ h) hα
    simpa [sq] using this
  have hx2 : x ^ 2 = 1 := by
    refine hfaith _ (pow_mem hxG 2) fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * baseChangeGL ι h * x⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * x * baseChangeGL ι h =
        (x * (x * baseChangeGL ι h * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = baseChangeGL ι h * (x * x) := by rw [h1, h2]
  obtain ⟨h, -, a', ha', hxa, hHh, -, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ F L hτ hF Fr hFr hxR hx2
  set b : Fin τ.rank → Fˣ := fun i => if a' i = 1 then 1 else -1 with hb_def
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h1 : a' i = 1 <;> simp [hb_def, h1]
  have hab : (fun i => Units.map (algebraMap F L).toMonoidHom (b i)) = a' := by
    funext i
    by_cases h1 : a' i = 1
    · simp [hb_def, h1]
    · have h2 : a' i = -1 := (ha' i).resolve_left h1
      rw [h2]
      simp only [hb_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hdb' : baseChangeGL ι (rootDiagUnit τ b) = rootDiagUnit τ a' := by
    rw [baseChangeGL_rootDiagUnit, ← hab]
  set H := (adjointGroup τ F).map (baseChangeGL ι) with hH
  let eι : adjointGroup τ F ≃* H := (adjointGroup τ F).equivMapOfInjective (baseChangeGL ι) hinj
  let eh : H ≃* H := (H.equivMapOfInjective (MulAut.conj h).toMonoidHom
    (MulAut.conj h).injective).trans (MulEquiv.subgroupCongr hHh)
  let ψ : MulAut (adjointGroup τ F) := (eι.trans eh).trans eι.symm
  have hψ : ∀ c : adjointGroup τ F,
      baseChangeGL ι (ψ c : ModGL τ F) = h * baseChangeGL ι (c : ModGL τ F) * h⁻¹ := by
    intro c
    have h1 : eι (ψ c) = eh (eι c) := MulEquiv.apply_symm_apply eι _
    exact congrArg Subtype.val h1
  have hψinv : ∀ c : adjointGroup τ F,
      baseChangeGL ι (ψ⁻¹ c : ModGL τ F) = h⁻¹ * baseChangeGL ι (c : ModGL τ F) * h := by
    intro c
    have h1 := hψ (ψ⁻¹ c)
    rw [show ψ (ψ⁻¹ c) = c from MulAut.apply_inv_self _ ψ c] at h1
    rw [h1]
    group
  refine ⟨ψ, b, hb, MulEquiv.ext fun c => Subtype.ext (hinj ?_)⟩
  change baseChangeGL ι (ψ (α (ψ⁻¹ c)) : ModGL τ F) =
    baseChangeGL ι (rootDiagAut τ F b c : ModGL τ F)
  rw [hψ, ← hxconj, hψinv, coe_rootDiagAut, map_mul, map_mul, map_inv, hdb', ← hxa]
  group

end CFSG.ComponentClassification.Burgoyne.E2
