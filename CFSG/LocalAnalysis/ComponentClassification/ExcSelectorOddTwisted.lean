module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddRational
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddGFE
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K]

theorem odd_E7_inner_not_smallType (hK : Odd (Nat.card K))
    {α : MulAut (adjointGroup .E7 K)} {g : adjointGroup .E7 K} {a : Fin Tag.E7.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) =
      (g : ModGL .E7 K) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹)
    (hα : α ^ 2 = 1) {L : Subgroup (adjointGroup .E7 K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set Lc := AlgebraicClosure K
  set ι := algebraMap K Lc with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  have : CharP Lc p := charP_of_injective_algebraMap (algebraMap K Lc).injective p
  set Fr := iterateFrobenius Lc p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set b : Fin Tag.E7.rank → Lcˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL .E7 K) * rootDiagUnit .E7 b with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hK Lc ι
  have hgG : baseChangeGL ι (g : ModGL .E7 K) ∈ adjointGroup .E7 Lc := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup .E7 Lc :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift .E7 Lc b).1
  have hdb : baseChangeGL ι (rootDiagUnit .E7 a) = rootDiagUnit .E7 b :=
    baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup .E7 K,
      x * baseChangeGL ι (h : ModGL .E7 K) * x⁻¹ = baseChangeGL ι (α h : ModGL .E7 K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hK Lc Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit .E7 b) = rootDiagUnit .E7 b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup .E7 Lc ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup .E7 K) => φ h) hα
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
  obtain ⟨h7, -, -⟩ := e7_twisted_e6_triality_rational_inner_not_smallType p Lc hp2
    (isAlgebraic_zmod_of_isAlgClosure p K Lc) n n.pos
  have hF1 : frobTwistGL .E7 Lc p n 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hRR : fixedPointsIn (adjointGroup .E7 Lc) (frobTwistGL .E7 Lc p n 1) =
      adjointGroup .E7 Lc ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [hF1]
  set Y := (adjointGroup .E7 K).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} with hY_def
  have hY : ⁅fixedPointsIn (adjointGroup .E7 Lc) (frobTwistGL .E7 Lc p n 1),
      fixedPointsIn (adjointGroup .E7 Lc) (frobTwistGL .E7 Lc p n 1)⁆ ⊓
        Subgroup.centralizer {x} = Y := by
    rw [hRR, hder]
  let φ : adjointGroup .E7 K →* ModGL .E7 Lc := (baseChangeGL ι).comp (adjointGroup .E7 K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (fixedSubgroup α).map φ = Y := by
    ext y
    simp only [hY_def, Subgroup.mem_map, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL .E7 K) * x = x * baseChangeGL ι (c : ModGL .E7 K)
      calc baseChangeGL ι (c : ModGL .E7 K) * x =
          (x * baseChangeGL ι (c : ModGL .E7 K) * x⁻¹) * x := by rw [h1]
        _ = x * baseChangeGL ι (c : ModGL .E7 K) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * baseChangeGL ι c * x⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  have hL' := isComponentOf_map_of_injective φ hφ hL
  rw [hmap, ← hY] at hL'
  have hns := h7 x (hRR ▸ hxR) hx2 _ hL'
  exact fun hs => hns ((smallType_congr (L.equivMapOfInjective φ hφ)).1 hs)

theorem odd_E7_not_smallType (hK : Odd (Nat.card K)) (α : MulAut (adjointGroup .E7 K))
    (hα : α ^ 2 = 1) {L : Subgroup (adjointGroup .E7 K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  rcases odd_E7_involution_inner_or_quadratic hK hα with ⟨g, a, hαg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · exact odd_E7_inner_not_smallType hK hαg hα hL
  · exact odd_quadratic_field_not_smallType hK2 hq he hKe δ hδ hαg hα hL

theorem isAlgebraic_algebraicClosure (p : ℕ) [Fact p.Prime] [CharP (AlgebraicClosure K) p] :
    letI := ZMod.algebra (AlgebraicClosure K) p;
      Algebra.IsAlgebraic (ZMod p) (AlgebraicClosure K) := by
  let _ : Algebra (ZMod p) (AlgebraicClosure K) := ZMod.algebra (AlgebraicClosure K) p
  refine ⟨fun y => ?_⟩
  obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset _)
  have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
  have : Fintype E := Fintype.ofFinite E
  have hpow : y ^ Fintype.card E = y :=
    congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
  refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
  rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]

theorem odd_twisted_inner_not_smallType (t : TwistTag) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (x : graphFixedRootGroup t K σ.toRingHom) (hx : x ^ 2 = 1)
    {L : Subgroup (graphFixedRootGroup t K σ.toRingHom)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup (MulAut.conj x))) : ¬ SmallType L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hKm : Nat.card K = p ^ (t.order * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp
    (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero t.order_pos.ne' (by omega))) hKm
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have halg := isAlgebraic_algebraicClosure (K := K) p
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group t
    hp hf hodd K hK σ.toRingHom hσ k Fr hFr
  have hRF : fixedPointsIn (adjointGroup t.tag k)
      (frobTwistGL t.tag k p f (diagramMap t k)) = twistedFixedGroup t k Fr := rfl
  set y := baseChangeGL ι (x : ModGL t.tag K) with hydef
  have hyR : y ∈ fixedPointsIn (adjointGroup t.tag k)
      (frobTwistGL t.tag k p f (diagramMap t k)) := by
    rw [hRF]
    exact hHR ⟨x, x.2, rfl⟩
  have hy2 : y ^ 2 = 1 := by
    rw [hydef, ← map_pow, ← Subgroup.coe_pow, hx, Subgroup.coe_one, map_one]
  have hns : ∀ M : Subgroup (ModGL t.tag k), Assembly.IsComponentOf M
      (⁅fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p f (diagramMap t k)),
        fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p f (diagramMap t k))⁆ ⊓
          Subgroup.centralizer {y}) → ¬ SmallType M := by
    have h := e7_twisted_e6_triality_rational_inner_not_smallType p k hp2 halg f hf
    cases t
    · exact h.2.1 y hyR hy2
    · exact h.2.2 y hyR hy2
  let φ : graphFixedRootGroup t K σ.toRingHom →* ModGL t.tag k :=
    (baseChangeGL ι).comp (graphFixedRootGroup t K σ.toRingHom).subtype
  have hφ : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hmap : (fixedSubgroup (MulAut.conj x)).map φ =
      ⁅fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p f (diagramMap t k)),
        fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p f (diagramMap t k))⁆ ⊓
        Subgroup.centralizer {y} := by
    rw [hRF, hder]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have hc' : x * c * x⁻¹ = c := hc
      have hcx : c * x = x * c := by
        calc c * x = x * c * x⁻¹ * x := by rw [hc']
          _ = x * c := by group
      change baseChangeGL ι (c : ModGL t.tag K) * y = y * baseChangeGL ι (c : ModGL t.tag K)
      rw [hydef, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcx]
    · rintro ⟨⟨c, hc, rfl⟩, hcy⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      change x * ⟨c, hc⟩ * x⁻¹ = ⟨c, hc⟩
      have hcx : (⟨c, hc⟩ : graphFixedRootGroup t K σ.toRingHom) * x = x * ⟨c, hc⟩ := by
        refine Subtype.ext (baseChangeGL_injective ι ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hcy
      rw [← hcx]
      group
  have hL' := isComponentOf_map_of_injective φ hφ hL
  rw [hmap] at hL'
  exact fun hs => hns _ hL' ((smallType_congr (L.equivMapOfInjective φ hφ)).1 hs)

end CFSG.ComponentClassification.ExcSelector
