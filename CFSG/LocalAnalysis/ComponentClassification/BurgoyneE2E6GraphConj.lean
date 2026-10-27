module

public import CFSG.LieType.Chevalley.CLSOddE6AllInvolutionFourGroup
public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def e6GraphSign (K : Type) [Field K] : Fin TwistTag.E6.tag.rank → Kˣ :=
  ![1, -1, 1, 1, 1, 1]

theorem map_e6GraphSign {K L : Type} [Field K] [Field L] (ι : K →+* L) :
    (fun i => Units.map ι.toMonoidHom (e6GraphSign K i)) = e6GraphSign L := by
  funext i
  change Fin 6 at i
  fin_cases i <;> ext <;> simp [e6GraphSign]


theorem exists_conj_eq_graph_of_graphCoset {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) {g : adjointGroup TwistTag.E6.tag K}
    {a : Fin TwistTag.E6.tag.rank → Kˣ} {α : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hα : α ^ 2 = 1) :
    ∃ ψ : MulAut (adjointGroup TwistTag.E6.tag K), ψ * α * ψ⁻¹ = diagramConjAut TwistTag.E6 K ∨
      ψ * α * ψ⁻¹ =
        rootDiagAut TwistTag.E6.tag K (e6GraphSign K) * diagramConjAut TwistTag.E6 K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  set Fr := iterateFrobenius k p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have halg := OddE6AllInvolution.isAlgebraic_zmod_algebraicClosure K p
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness TwistTag.E6.tag K hK k ι
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hdb : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag a) = rootDiagUnit TwistTag.E6.tag b :=
    baseChangeGL_rootDiagUnit ι a
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 K) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : adjointGroup TwistTag.E6.tag K,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * (x * P)⁻¹ =
        baseChangeGL ι (α h : ModGL TwistTag.E6.tag K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  obtain ⟨-, hHR, hRnorm, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group TwistTag.E6.tag K hK k Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hRF : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)) =
        adjointGroup TwistTag.E6.tag k ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag k p n (P ^ 0) y = y ↔ Units.map (entrywiseHom Fr) y = y
    rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one]
  have hxR : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)) := by
    rw [hRF]
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup TwistTag.E6.tag K) => φ h) hα
    simpa [sq] using this
  have hP2 : P * P = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 k
    rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
  have hPG : ∀ y ∈ adjointGroup TwistTag.E6.tag k,
      P * y * P⁻¹ ∈ adjointGroup TwistTag.E6.tag k := by
    have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.E6 k 1)
    rw [zpow_one] at hQ
    exact hQ
  have hx2 : (x * P) ^ 2 = 1 := by
    have hsqG : (x * P) ^ 2 ∈ adjointGroup TwistTag.E6.tag k := by
      have e : (x * P) ^ 2 = x * (P * x * P⁻¹) * (P * P) := by
        rw [sq]
        group
      rw [e, hP2, mul_one]
      exact mul_mem hxG (hPG x hxG)
    refine hfaith _ hsqG fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * P * baseChangeGL ι h * (x * P)⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * P * (x * P) * baseChangeGL ι h =
        (x * P * (x * P * baseChangeGL ι h * (x * P)⁻¹) * (x * P)⁻¹) * (x * P * (x * P)) := by
          group
      _ = baseChangeGL ι h * (x * P * (x * P)) := by rw [h1, h2]
  obtain ⟨-, -, -, hnode⟩ :=
    E6_rational_graph_coset_fixed_components p hp2 n.pos k halg 0 (Or.inl rfl)
  obtain ⟨⟨y, hyR, hyA⟩, -⟩ := hnode x hxR hx2
  rw [hRF] at hyR
  have hyN := hRnorm hyR
  set H := (adjointGroup TwistTag.E6.tag K).map (baseChangeGL ι) with hH
  have hHy : H.map (MulAut.conj y).toMonoidHom = H := by
    refine le_antisymm ?_ fun z hz => ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hyN z).1 hz
    · refine ⟨y⁻¹ * z * y, ?_, by simp [mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hyN) z).1 hz
      simpa using this
  let eι : adjointGroup TwistTag.E6.tag K ≃* H :=
    (adjointGroup TwistTag.E6.tag K).equivMapOfInjective (baseChangeGL ι) hinj
  let eh : H ≃* H := (H.equivMapOfInjective (MulAut.conj y).toMonoidHom
    (MulAut.conj y).injective).trans (MulEquiv.subgroupCongr hHy)
  let ψ : MulAut (adjointGroup TwistTag.E6.tag K) := (eι.trans eh).trans eι.symm
  have hψ : ∀ c : adjointGroup TwistTag.E6.tag K,
      baseChangeGL ι (ψ c : ModGL TwistTag.E6.tag K) =
        y * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * y⁻¹ := by
    intro c
    have h1 : eι (ψ c) = eh (eι c) := MulEquiv.apply_symm_apply eι _
    exact congrArg Subtype.val h1
  have hψinv : ∀ c : adjointGroup TwistTag.E6.tag K,
      baseChangeGL ι (ψ⁻¹ c : ModGL TwistTag.E6.tag K) =
        y⁻¹ * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * y := by
    intro c
    have h1 := hψ (ψ⁻¹ c)
    rw [show ψ (ψ⁻¹ c) = c from MulAut.apply_inv_self _ ψ c] at h1
    rw [h1]
    group
  have hconj : ∀ c : adjointGroup TwistTag.E6.tag K,
      baseChangeGL ι (((ψ * α * ψ⁻¹) c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) =
        (y * (x * P) * y⁻¹) * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) *
          (y * (x * P) * y⁻¹)⁻¹ := by
    intro c
    change baseChangeGL ι (ψ (α (ψ⁻¹ c)) : ModGL TwistTag.E6.tag K) = _
    rw [hψ, ← hxconj, hψinv]
    group
  refine ⟨ψ, ?_⟩
  rcases hyA with h | h
  · left
    refine MulEquiv.ext fun c => Subtype.ext (hinj ?_)
    rw [hconj, h, coe_diagramConjAut, map_mul, map_mul, map_inv, hPι]
  · right
    refine MulEquiv.ext fun c => Subtype.ext (hinj ?_)
    have hsd : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag (e6GraphSign K)) =
        rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] := by
      rw [baseChangeGL_rootDiagUnit, map_e6GraphSign]
      rfl
    rw [hconj, h, MulAut.mul_apply, coe_rootDiagAut, coe_diagramConjAut, map_mul, map_mul,
      map_mul, map_mul, map_inv, map_inv, hPι, hsd, ← hPdef]
    group

end CFSG.ComponentClassification.Burgoyne.E2
