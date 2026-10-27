module

public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer
public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset
public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem odd_twisted_E6_outer_involution_fixed_p_components
    {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (hα : α ^ 2 = 1)
    (hαo : α ∉ twistedE6Inn K σ) (r : ℕ) (hr : r.Prime)
    (L : Subgroup (α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))))
    (hL : CFSG.IsPComponent r L) : CFSG.IsQuasisimple L := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
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
  have hcharK : ringChar K = p := by
    obtain ⟨n, hpn, hcard⟩ := FiniteField.card K (ringChar K)
    have h1 : ringChar K ∣ p ^ (f * 2) := by
      rw [pow_mul, ← hK, Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self _ n.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hpn hp).1 (hpn.dvd_of_dvd_pow h1)
  have : CharP K p := hcharK ▸ ringChar.charP K
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFr_def, iterateFrobenius_def]
  have hFrι : ∀ c : K, Fr (ι c) = ι (σ c) := fun c => by rw [hFr, hσ, map_pow]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y :=
      congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ :=
    fun i => Units.map ι.toMonoidHom (compatDiag TwistTag.E6 σ.toRingHom u i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ := odd_diagram_fixed_ambient_centralizer_trivial TwistTag.E6 hp hf
    hodd K hKo σ.toRingHom hσ k ι
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.E6
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
    rw [frobTwistGL_apply, pow_one, twistHom_apply]
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
  obtain ⟨-, hcomp⟩ := hnode x (hRF ▸ hxR) hx2
  have hHder : ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (P ^ 1)), fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (P ^ 1))⁆ =
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) := by
    rw [hRF]
    exact hder
  let φ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (P ^ 1)), fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p f (P ^ 1))⁆ ⊓ Subgroup.centralizer {x * P} := by
    rw [hHder]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P) =
        x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K)
      calc baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P) =
          (x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P)⁻¹) * (x * P) := by
            rw [h1]
        _ = x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * P * baseChangeGL ι c * (x * P)⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  exact OddToralFixed.pComponent_quasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)) (hcomp r hr) L hL

end CFSG.LieType.Chevalley
