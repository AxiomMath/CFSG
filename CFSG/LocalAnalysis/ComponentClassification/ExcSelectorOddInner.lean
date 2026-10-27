module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddToral
public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem isComponentOf_map_of_injective {C C' : Type} [Group C] [Group C'] (f : C →* C')
    (hf : Function.Injective f) {L F : Subgroup C} (h : Assembly.IsComponentOf L F) :
    Assembly.IsComponentOf (L.map f) (F.map f) :=
  ⟨Subgroup.map_mono h.1, assembly_isSubnormal_map f h.2.1,
    assembly_isQuasisimple_of_equiv (L.equivMapOfInjective f hf) h.2.2⟩

theorem not_smallType_of_map_eq {C C' X' : Type} [Group C] [Group C'] [Group X'] (ψ : C →* C')
    (hψ : Function.Injective ψ) (ι : X' →* C') (hι : Function.Injective ι) {F : Subgroup C}
    {X : Subgroup X'} (hF : F.map ψ = X.map ι)
    (hX : ∀ M : Subgroup X', Assembly.IsComponentOf M X → ¬ SmallType M) {L : Subgroup C}
    (hL : Assembly.IsComponentOf L F) : ¬ SmallType L := by
  have hL' := isComponentOf_map_of_injective ψ hψ hL
  rw [hF] at hL'
  have hM := isComponentOf_comap_of_injective ι hι hL'
  have hLr : L.map ψ ≤ ι.range := hL'.1.trans (Subgroup.map_le_range _ _)
  have e : L ≃* ((L.map ψ).comap ι) := (L.equivMapOfInjective ψ hψ).trans
    ((((L.map ψ).comap ι).equivMapOfInjective _ hι).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLr))).symm
  exact fun hs => hX _ hM ((smallType_congr e).1 hs)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem odd_inner_diagonal_not_smallType (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hK : Odd (Nat.card K)) {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K}
    {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) {L : Subgroup (adjointGroup τ K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set Lc := AlgebraicClosure K
  set ι := algebraMap K Lc with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP Lc p := charP_of_injective_algebraMap (algebraMap K Lc).injective p
  have hK2 : ringChar K ≠ 2 := by
    intro h2
    have h2' : p = 2 := h2
    rw [Nat.card_eq_fintype_card, hcard, h2'] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  set Fr := iterateFrobenius Lc p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set b : Fin τ.rank → Lcˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL τ K) * rootDiagUnit τ b with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness τ K hK Lc ι
  have hgG : baseChangeGL ι (g : ModGL τ K) ∈ adjointGroup τ Lc := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup τ Lc :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift τ Lc b).1
  have hdb : baseChangeGL ι (rootDiagUnit τ a) = rootDiagUnit τ b := baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup τ K,
      x * baseChangeGL ι (h : ModGL τ K) * x⁻¹ = baseChangeGL ι (α h : ModGL τ K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK Lc Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit τ b) = rootDiagUnit τ b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup τ Lc ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
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
  obtain ⟨h, -, a', ha', -, -, hCh, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ K Lc hτ hK Fr hFr hxR
      hx2
  set H := (adjointGroup τ K).map (baseChangeGL ι) with hH
  let φ : adjointGroup τ K →* ModGL τ Lc := (baseChangeGL ι).comp (adjointGroup τ K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (fixedSubgroup α).map φ = H ⊓ Subgroup.centralizer {x} := by
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
  set b' : Fin τ.rank → Kˣ := fun i => if a' i = 1 then 1 else -1 with hb'_def
  have hb' : ∀ i, b' i = 1 ∨ b' i = -1 := fun i => by
    by_cases h1 : a' i = 1 <;> simp [hb'_def, h1]
  have hab : (fun i => Units.map (algebraMap K Lc).toMonoidHom (b' i)) = a' := by
    funext i
    by_cases h1 : a' i = 1
    · simp [hb'_def, h1]
    · have h2 : a' i = -1 := (ha' i).resolve_left h1
      rw [h2]
      simp only [hb'_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hXK := map_baseChangeGL_toralCentralizer (algebraMap K Lc) b'
  rw [hab] at hXK
  refine not_smallType_of_map_eq ((MulAut.conj h).toMonoidHom.comp φ)
    ((MulAut.conj h).injective.comp hφ) (baseChangeGL ι) (baseChangeGL_injective ι) ?_
    (fun M hM => toral_component_not_smallType hK2 b' hb' hM) hL
  rw [← Subgroup.map_map, hmap, hCh, hXK]

end CFSG.ComponentClassification.ExcSelector
