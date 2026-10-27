module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6Graph
public import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddTwisted

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem odd_E6_pure_graph_not_smallType {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    {g : adjointGroup TwistTag.E6.tag K} {a : Fin TwistTag.E6.tag.rank → Kˣ}
    {α : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hα : α ^ 2 = 1) {L : Subgroup (adjointGroup TwistTag.E6.tag K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
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
  have halg := isAlgebraic_algebraicClosure (K := K) p
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
  obtain ⟨-, hHR, -, hder⟩ :=
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
  have hHder : ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)), fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p n (P ^ 0))⁆ =
      (adjointGroup TwistTag.E6.tag K).map (baseChangeGL ι) := by
    rw [hRF]
    exact hder
  let φ : adjointGroup TwistTag.E6.tag K →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (adjointGroup TwistTag.E6.tag K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (fixedSubgroup α).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)), fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p n (P ^ 0))⁆ ⊓ Subgroup.centralizer {x * P} := by
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
  have hL' := isComponentOf_map_of_injective φ hφ hL
  rw [hmap] at hL'
  exact fun hs => e6_rational_graph_coset_not_smallType p hp2 n.pos halg (Or.inl rfl) hxR hx2 hL'
    ((smallType_congr (L.equivMapOfInjective φ hφ)).1 hs)

theorem odd_twistedE6_outer_not_smallType {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hodd : Odd (p ^ f)) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hα : α ^ 2 = 1)
    (hαo : α ∉ twistedE6Inn K σ) {L : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
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
  have halg := isAlgebraic_algebraicClosure (K := K) p
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
  have hL' := isComponentOf_map_of_injective φ hφ hL
  rw [hmap] at hL'
  exact fun hs => e6_rational_graph_coset_not_smallType p hp2 hf halg (Or.inr rfl) hxR' hx2 hL'
    ((smallType_congr (L.equivMapOfInjective φ hφ)).1 hs)

theorem twistedFixedGroup_E6_component_not_smallType {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) {M : Subgroup (ModGL TwistTag.E6.tag K)}
    (hM : Assembly.IsComponentOf M (twistedFixedGroup TwistTag.E6 K σ.toRingHom)) :
    ¬ SmallType M := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have h := ((odd_diagram_field_fixed_p_components TwistTag.E6 K hK σ).2.2 2 Nat.prime_two _
    (isPComponent_two_subgroupOf hM)).2
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hM.1,
    inf_eq_left.2 (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom)] at h
  rw [h]
  exact graphFixedRootGroup_E6_odd_not_smallType hK σ.toRingHom σ.surjective

theorem odd_E6_not_smallType {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    (α : MulAut (adjointGroup Tag.E6 K)) (hα : α ^ 2 = 1) {L : Subgroup (adjointGroup Tag.E6 K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have h1 : ∀ x : ModGL Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF α
  have hσ2 := hsq α g a σ ε hgaσ hα
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε with hε | hε
    ·
      refine odd_inner_diagonal_not_smallType (τ := Tag.E6) (Or.inr (Or.inr (Or.inl rfl))) hK
        (g := g) (a := a) (fun h => ?_) hα hL
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    ·
      refine odd_E6_pure_graph_not_smallType hK (g := g) (a := a) (fun h => ?_) hα hL
      exact (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)
  ·
    obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hcard σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hcard]
    rcases hε with hε | hε
    ·
      refine odd_quadratic_field_not_smallType hK2 hp he hKe σ hσc (g := g) (a := a)
        (fun h => ?_) hα hL
      rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]
    ·
      obtain ⟨-, β, hβ, hβα⟩ :=
        exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl))
        ((sq α).symm.trans hα)
      have hβfix : (fixedSubgroup β).map (adjointGroup TwistTag.E6.tag K).subtype =
          twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
        ext y
        simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨u.2, ?_⟩
          change twistHom TwistTag.E6 K σ.toRingHom (u : ModGL TwistTag.E6.tag K) = u
          rw [twistHom_apply, ← hβ u]
          exact congrArg Subtype.val hu
        · rintro ⟨hyG, hyσ⟩
          refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
          change (β ⟨y, hyG⟩ : ModGL TwistTag.E6.tag K) = y
          rw [hβ]
          change twistHom TwistTag.E6 K σ.toRingHom y = y at hyσ
          rw [twistHom_apply] at hyσ
          exact hyσ
      let e₂ : ↥(fixedSubgroup β) ≃* ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) :=
        (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
          (MulEquiv.subgroupCongr hβfix)
      exact not_smallType_of_subgroupEquiv (e₁.trans e₂)
        (fun M hM => twistedFixedGroup_E6_component_not_smallType hK2 σ hM) hL

theorem odd_twistedE6_not_smallType {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα : α ^ 2 = 1) {L : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  by_cases hαi : α ∈ twistedE6Inn K σ
  · obtain ⟨x, rfl⟩ := hαi
    have hx : x ^ 2 = 1 :=
      mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
        (by rw [map_pow, hα, map_one])
    exact odd_twisted_inner_not_smallType TwistTag.E6 hp hp2 hf hK σ hσ x hx hL
  · exact odd_twistedE6_outer_not_smallType hp hf hodd hK σ hσ hα hαi hL

end CFSG.ComponentClassification.ExcSelector
