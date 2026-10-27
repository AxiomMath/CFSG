module

public import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases
public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal
public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem exceptional_inner_diagonal_involution_fixed_p_components
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hK : Odd (Nat.card K))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (M : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))))
    (hM : CFSG.IsPComponent ℓ M) : CFSG.IsQuasisimple M := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  set ι := algebraMap K L with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set b : Fin τ.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL τ K) * rootDiagUnit τ b with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness τ K hK L ι
  have hgG : baseChangeGL ι (g : ModGL τ K) ∈ adjointGroup τ L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup τ L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift τ L b).1
  have hdb : baseChangeGL ι (rootDiagUnit τ a) = rootDiagUnit τ b := baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup τ K,
      x * baseChangeGL ι (h : ModGL τ K) * x⁻¹ = baseChangeGL ι (α h : ModGL τ K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK L Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit τ b) = rootDiagUnit τ b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
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
    have := congrArg (fun φ : MulAut (adjointGroup τ K) => φ h) hα
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
  obtain ⟨-, -, -, -, -, -, -, hcomp⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ K L hτ hK Fr hFr hxR hx2
  let φ : adjointGroup τ K →* ModGL τ L := (baseChangeGL ι).comp (adjointGroup τ K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))).map φ =
      (adjointGroup τ K).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL τ K) * x = x * baseChangeGL ι (c : ModGL τ K)
      calc baseChangeGL ι (c : ModGL τ K) * x =
          (x * baseChangeGL ι (c : ModGL τ K) * x⁻¹) * x := by rw [h1]
        _ = x * baseChangeGL ι (c : ModGL τ K) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * baseChangeGL ι c * x⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  let e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))) ≃*
      ↥((adjointGroup τ K).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x}) :=
    (Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)
  exact OddToralFixed.pComponent_quasisimple_of_mulEquiv e (hcomp ℓ hℓ) M hM

theorem exceptional_quadratic_field_involution_fixed_p_components
    (hK : ringChar K ≠ 2)
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K}
    {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (M : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))))
    (hM : CFSG.IsPComponent ℓ M) : CFSG.IsQuasisimple M := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))).map
      (adjointGroup τ K).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ K) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))) ≃*
      ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  exact OddToralFixed.pComponent_quasisimple_of_mulEquiv (e₁.trans e₂)
    (fun J hJ => odd_Chevalley_coordinate_field_fixed_p_components τ K hK δ ℓ hℓ J hJ) M hM

theorem odd_G2_F4_E8_all_involution_fixed_p_components
    (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (α : MulAut (adjointGroup τ K)) (hα : α ^ 2 = 1) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (L : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))))
    (hL : CFSG.IsPComponent ℓ L) : CFSG.IsQuasisimple L := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have hτ4 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  by_cases h3 : τ = .G2 ∧ p = 3
  ·
    obtain ⟨hG2, rfl⟩ := h3
    obtain rfl : τ = ReeTag.G2.tag := hG2
    have : CharP K ReeTag.G2.prime := ringChar.of_eq hchar
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hcard hα with ⟨g, a, hαg⟩ |
      ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hb, rfl⟩
    · exact exceptional_inner_diagonal_involution_fixed_p_components hτ4 hK hαg hα ℓ hℓ L hL
    · exact exceptional_quadratic_field_involution_fixed_p_components hK2 Nat.prime_three he hKe
        δ hδ hαg hα ℓ hℓ L hL
    · exact (CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b K
        (hb ▸ hcard) g hα).2.1 ℓ hℓ L hL
  · have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
      rcases hτ with h | h | h
      · exact Or.inr (Or.inr ⟨h, fun h' => h3 ⟨h, hchar ▸ h'⟩⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hK hα with ⟨g, a, hαg⟩ |
      ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
    · exact exceptional_inner_diagonal_involution_fixed_p_components hτ4 hK hαg hα ℓ hℓ L hL
    · exact exceptional_quadratic_field_involution_fixed_p_components hK2 hq he hKe δ hδ hαg hα
        ℓ hℓ L hL

end CFSG.LieType.AlgebraicGroups
