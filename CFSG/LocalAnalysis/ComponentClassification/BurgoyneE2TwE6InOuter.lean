module

public import CFSG.LieType.Chevalley.CLSOddTwistedE6AllInvolutionFourGroup
public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset
public import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4Sub

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.LieType.Chevalley.OddE6AllInvolution (isAlgebraic_zmod_algebraicClosure)

@[expose] def normConjAut {G : Type*} [Group G] {H : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) : MulAut H where
  toFun h := ⟨y * h * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy h).mp h.2⟩
  invFun h := ⟨y⁻¹ * h * y, by
    have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) h).mp h.2
    rwa [inv_inv] at h'⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem twE6_outer_involution_conj
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (hα : α ^ 2 = 1)
    (hαo : α ∉ twistedE6Inn K σ) :
    ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ψ * α * ψ⁻¹ = fieldActor (t := TwistTag.E6) σ σ ∨ ψ * α * ψ⁻¹ = twE6SignAut σ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hKo : Nat.card K = (p ^ f) ^ TwistTag.E6.order := hK
  obtain ⟨-, -, -, -, -, hΔ, -, -, ⟨Θ, -, -, -, -, -, hsq⟩, hσP, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨g, u, hform⟩ : ∃ g u, α = MulAut.conj g *
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ σ := by
    rcases hsq α hα with hinn | ⟨-, g, u, h⟩
    · exact absurd hinn hαo
    · exact ⟨g, u, h⟩
  set D := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) with hD
  have hαg : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * D * diagramMap TwistTag.E6 K * h *
        (diagramMap TwistTag.E6 K)⁻¹ * D⁻¹ * (g : ModGL TwistTag.E6.tag K)⁻¹ := fun h => by
    rw [hform, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hΔ, hσP, ← hD]
    group
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK'
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFr_def, iterateFrobenius_def]
  have hFrι : ∀ c : K, Fr (ι c) = ι (σ c) := fun c => by rw [hFr, hσ, map_pow]
  have halg := isAlgebraic_zmod_algebraicClosure K p
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ :=
    fun i => Units.map ι.toMonoidHom (compatDiag TwistTag.E6 σ.toRingHom u i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ := odd_diagram_fixed_ambient_centralizer_trivial TwistTag.E6 hp hf
    hodd K hKo σ.toRingHom hσ k ι
  obtain ⟨-, -, hHR, hHN, -, -, -⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.E6
    hp hf hodd K hKo σ.toRingHom hσ k Fr hFr
  have hgH : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) := ⟨g, g.2, rfl⟩
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG hgH
  have hbG := (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k := mul_mem hgG hbG
  have hdb : baseChangeGL ι D = rootDiagUnit TwistTag.E6.tag b := baseChangeGL_rootDiagUnit ι _
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 K) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * (x * P)⁻¹ =
        baseChangeGL ι (α h : ModGL TwistTag.E6.tag K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  have hFb : twistHom TwistTag.E6 k Fr (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    refine twistHom_rootDiagUnit fun i => Units.ext ?_
    change ι ((compatDiag TwistTag.E6 σ.toRingHom u (TwistTag.E6.perm i) : Kˣ) : K) =
      Fr (ι ((compatDiag TwistTag.E6 σ.toRingHom u i : Kˣ) : K))
    rw [compatDiag_perm, hFrι]
    rfl
  have hbR : rootDiagUnit TwistTag.E6.tag b ∈ twistedFixedGroup TwistTag.E6 k Fr :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 k Fr).2 ⟨hbG, hFb⟩
  have hxR : x ∈ twistedFixedGroup TwistTag.E6 k Fr := mul_mem (hHR hgH) hbR
  have hRF : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (P ^ 1)) = twistedFixedGroup TwistTag.E6 k Fr := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag k p f (P ^ 1) y = y ↔ twistHom TwistTag.E6 k Fr y = y
    rw [frobTwistGL_apply, pow_one, CFSG.LieType.Chevalley.twistHom_apply]
  have hα2 : ∀ h, α (α h) = h := fun h => by
    rw [← MulAut.mul_apply, ← sq, hα, MulAut.one_apply]
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
    E6_rational_graph_coset_fixed_components p hp2 hf k halg 1 (Or.inr rfl)
  obtain ⟨⟨y, hyR, hyA⟩, -⟩ := hnode x (hRF ▸ hxR) hx2
  rw [hRF] at hyR
  have hyN := OddTwistedE6AllInvolution.mem_normalizer_of_subgroupOf_normal hHR hHN hyR
  set e := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).equivMapOfInjective
    (baseChangeGL ι) hinj with he
  set ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    (e.trans (normConjAut hyN)).trans e.symm with hψ
  have hψι : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      baseChangeGL ι (ψ h : ModGL TwistTag.E6.tag K) =
        y * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * y⁻¹ := by
    intro h
    have h1 : ((e (ψ h) : (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
        (baseChangeGL ι)) : ModGL TwistTag.E6.tag k) =
        baseChangeGL ι (ψ h : ModGL TwistTag.E6.tag K) := rfl
    rw [← h1, hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hψinv : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      baseChangeGL ι (ψ⁻¹ h : ModGL TwistTag.E6.tag K) =
        y⁻¹ * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * y := by
    intro h
    have h1 := hψι (ψ⁻¹ h)
    rw [show ψ (ψ⁻¹ h) = h by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]] at h1
    calc baseChangeGL ι (ψ⁻¹ h : ModGL TwistTag.E6.tag K) =
        y⁻¹ * (y * baseChangeGL ι (ψ⁻¹ h : ModGL TwistTag.E6.tag K) * y⁻¹) * y := by group
      _ = y⁻¹ * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * y := by rw [← h1]
  have hconj : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      baseChangeGL ι ((ψ * α * ψ⁻¹) h : ModGL TwistTag.E6.tag K) =
        (y * (x * P) * y⁻¹) * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) *
          (y * (x * P) * y⁻¹)⁻¹ := by
    intro h
    rw [MulAut.mul_apply, MulAut.mul_apply, hψι, ← hxconj, hψinv]
    group
  refine ⟨ψ, ?_⟩
  rcases hyA with hA | hA
  · left
    refine MulEquiv.ext fun h => Subtype.ext (baseChangeGL_injective ι ?_)
    rw [hconj, hA, hσP, map_mul, map_mul, map_inv, hPι]
  · right
    have hιA : baseChangeGL ι (twistA K) =
        rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * P := by
      rw [twistA, map_mul, baseChangeGL_rootDiagUnit, hPι]
      congr 2
      funext i
      change Fin 6 at i
      fin_cases i <;> ext <;> simp [signTuple]
    refine MulEquiv.ext fun h => Subtype.ext (baseChangeGL_injective ι ?_)
    rw [hconj, hA, coe_twE6SignAut hp hp2 hf hK σ hσ, map_mul, map_mul, map_inv, hιA]

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In
