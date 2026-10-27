module

public import CFSG.LieType.AlgebraicGroups.OddG2F4E8AllInvolutionComponents
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem isAlgebraic_zmod_of_isAlgClosure (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K]
    [CharP K p] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p] :
    letI := ZMod.algebra L p; Algebra.IsAlgebraic (ZMod p) L := by
  let _ : Algebra (ZMod p) L := ZMod.algebra L p
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have : IsScalarTower (ZMod p) K L := IsScalarTower.of_algebraMap_eq fun x => by
    have h : algebraMap (ZMod p) L = (algebraMap K L).comp (algebraMap (ZMod p) K) :=
      Subsingleton.elim _ _
    exact RingHom.congr_fun h x
  have : Module.Finite (ZMod p) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (ZMod p) K := Algebra.IsAlgebraic.of_finite (ZMod p) K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  exact Algebra.IsAlgebraic.trans (ZMod p) K L

theorem isPComponent_subgroupOf_of_eq {G : Type*} [Group G] {ℓ : ℕ} {A B L : Subgroup G}
    (h : A = B) (hL : CFSG.IsPComponent ℓ (L.subgroupOf B)) :
    CFSG.IsPComponent ℓ (L.subgroupOf A) := by
  subst h
  exact hL

variable {K : Type} [Field K] [Finite K]

theorem odd_E7_involution_inner_or_quadratic
    (hK : Odd (Nat.card K))
    {α : MulAut (adjointGroup .E7 K)} (hα : α ^ 2 = 1) :
    (∃ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ), ∀ h : adjointGroup .E7 K,
      (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a * h *
        (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹) ∨
    ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ Nat.card K = (p ^ e) ^ 2 ∧ ∃ δ : K ≃+* K,
      (∀ c, δ c = c ^ (p ^ e)) ∧ ∃ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
        ∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a *
          Units.map (entrywiseHom δ.toRingHom) (h : ModGL .E7 K) * (rootDiagUnit .E7 a)⁻¹ *
            (g : ModGL .E7 K)⁻¹ := by
  obtain ⟨p, f, hp, -, hf, -, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have h1 : ∀ x : ModGL .E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF α
  have hQ : exactQ .E7 K ε = 1 := rfl
  have hα' : ∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) = (g : ModGL .E7 K) *
      rootDiagUnit .E7 a * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E7 K) *
        (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹ := fun h => by
    rw [hgaσ h, hQ, mul_one, inv_one, mul_one]
  by_cases hσ1 : σ = 1
  · subst hσ1
    exact Or.inl ⟨g, a, fun h => by rw [hα' h, h1]⟩
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hcard σ (hsq α g a σ ε hgaσ hα) hσ1
    refine Or.inr ⟨p, f / 2, hp, ?_, ?_, σ, hσc, g, a, hα'⟩
    · obtain ⟨m, rfl⟩ := hev
      omega
    · rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hcard]

theorem E7_inner_diagonal_involution_fixed_p_components
    (hK : Odd (Nat.card K))
    {α : MulAut (adjointGroup .E7 K)} {g : adjointGroup .E7 K} {a : Fin Tag.E7.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) =
      (g : ModGL .E7 K) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹)
    (hα : α ^ 2 = 1) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (M : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K))))
    (hM : CFSG.IsPComponent ℓ M) : CFSG.IsQuasisimple M := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  set ι := algebraMap K L with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set b : Fin Tag.E7.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL .E7 K) * rootDiagUnit .E7 b with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hK L ι
  have hgG : baseChangeGL ι (g : ModGL .E7 K) ∈ adjointGroup .E7 L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup .E7 L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift .E7 L b).1
  have hdb : baseChangeGL ι (rootDiagUnit .E7 a) = rootDiagUnit .E7 b :=
    baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup .E7 K,
      x * baseChangeGL ι (h : ModGL .E7 K) * x⁻¹ = baseChangeGL ι (α h : ModGL .E7 K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hK L Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit .E7 b) = rootDiagUnit .E7 b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup .E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
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
  obtain ⟨h7, -, -⟩ := e7_twisted_e6_triality_rational_inner_involution_fixed_p_components p L
    hp2 (isAlgebraic_zmod_of_isAlgClosure p K L) n n.pos
  have hF1 : frobTwistGL .E7 L p n 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hRR : fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p n 1) =
      adjointGroup .E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [hF1]
  set Y := (adjointGroup .E7 K).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} with hY_def
  have hY : ⁅fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p n 1),
      fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p n 1)⁆ ⊓
        Subgroup.centralizer {x} = Y := by
    rw [hRR, hder]
  have hcomp : ∀ N : Subgroup Y, CFSG.IsPComponent ℓ N → CFSG.IsQuasisimple N := by
    intro N hN
    have hNY : (N.map Y.subtype).subgroupOf Y = N :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective N
    have hq := h7 x (hRR ▸ hxR) hx2 ℓ hℓ (N.map Y.subtype)
      (by rw [hY]; exact Subgroup.map_subtype_le N)
      (isPComponent_subgroupOf_of_eq hY (by rw [hNY]; exact hN))
    exact (isQuasisimple_congr (N.equivMapOfInjective _ Y.subtype_injective)).2 hq
  let φ : adjointGroup .E7 K →* ModGL .E7 L := (baseChangeGL ι).comp (adjointGroup .E7 K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K))).map φ = Y := by
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
  let e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K))) ≃* ↥Y :=
    (Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)
  exact OddToralFixed.pComponent_quasisimple_of_mulEquiv e hcomp M hM

theorem odd_E7_all_involution_fixed_p_components
    (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (α : MulAut (adjointGroup .E7 K)) (hα : α ^ 2 = 1) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (L : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K))))
    (hL : CFSG.IsPComponent ℓ L) : CFSG.IsQuasisimple L := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  rcases odd_E7_involution_inner_or_quadratic hK hα with ⟨g, a, hαg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · exact E7_inner_diagonal_involution_fixed_p_components hK hαg hα ℓ hℓ L hL
  · exact exceptional_quadratic_field_involution_fixed_p_components hK2 hq he hKe δ hδ hαg hα
      ℓ hℓ L hL

end CFSG.LieType.AlgebraicGroups
