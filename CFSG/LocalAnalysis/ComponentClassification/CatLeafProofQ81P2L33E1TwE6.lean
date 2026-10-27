module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1E6Graph

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_isPGroup_twistedE6_outer
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hodd : Odd (p ^ f)) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hα : α ^ 2 = 1)
    (hαo : α ∉ twistedE6Inn K σ) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
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
  have halg := ExcSelector.isAlgebraic_algebraicClosure (K := K) p
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
  have hxR' : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (P ^ 1)) := by
    rw [hRF]
    exact hxR
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
  have hHder : ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (P ^ 1)), fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (P ^ 1))⁆ =
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) := by
    rw [hRF]
    exact hder
  let φ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (fixedSubgroup α).map φ =
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
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨S, hS, hSp, hS1⟩ :=
    exists_perfect_rational_graph_coset p hp2 hf halg (Or.inr rfl) hxR' hx2
  exact not_isPGroup_of_perfect_le_map φ hφ (hS.trans hmap.symm.le) hSp hS1

theorem not_isPGroup_twistedE6
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα : α ^ 2 = 1) (hα1 : α ≠ 1)
    (hinn : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, x ^ 2 = 1 → x ≠ 1 →
      ∃ X : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        X ≤ fixedSubgroup (MulAut.conj x) ∧ ⁅X, X⁆ = X ∧ 2 ∣ Nat.card X) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  by_cases hαi : α ∈ twistedE6Inn K σ
  · obtain ⟨x, rfl⟩ := hαi
    have hx : x ^ 2 = 1 :=
      mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
        (by rw [map_pow, hα, map_one])
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hα1 (map_one _)
    obtain ⟨X, hXF, hXp, hX2⟩ := hinn x hx hx1
    exact not_isPGroup_of_perfect hXF hXp hX2
  · exact not_isPGroup_twistedE6_outer hp hf hodd hK σ hσ hα hαi

end CFSG.ComponentClassification.HarrisLit.L33.E1
