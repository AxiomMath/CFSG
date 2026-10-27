module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryGlue

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Matrix
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.D4RC (rcl_map_fix_eq)
open CFSG.RankThree.Classical2 (conjSLn coe_conjSLn fixSubgroup)
open scoped Matrix MatrixGroups Pointwise

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section SL3

variable {ℓ f : ℕ} [Fact ℓ.Prime] {L k : Type} [Field L] [Field k] [Algebra k L] [IsAlgClosure k L]

theorem exists_sym2_hom_fixed_three [CharP L ℓ] (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f)
    (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Lˣ) (Φ Ψ : SL(3, L) ≃* SL(3, L))
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + Matrix.single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f))
    (c : ∀ i j : Fin 3, i ≠ j → Lˣ)
    (hΨ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      Ψ (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection hij.symm ((c i j hij : L) * t))
    (hcomm : ∀ X, Φ (Ψ X) = Ψ (Φ X)) (hΨ2 : ∀ X, Ψ (Ψ X) = X)
    (hC2 : ∀ B : Matrix (Fin 3) (Fin 3) k, Bᵀ = B → B.det ≠ 0 →
      ∃ (P : GL (Fin 3) k) (a : k), B = a • ((P : Matrix (Fin 3) (Fin 3) k) * sym2Form k *
        (P : Matrix (Fin 3) (Fin 3) k)ᵀ)) :
    ∃ θ : SL(2, k) →* SL(3, L), (∀ s, θ s ∈ fixSubgroup Φ ⊓ fixSubgroup Ψ) ∧
      (∀ s, θ s = 1 ↔ s = 1 ∨ s = -1) ∧
      Nat.card θ.range = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) / 2 ∧
      (4 ≤ ℓ ^ f → ⁅θ.range, θ.range⁆ = θ.range ∧ IsSimpleGroup θ.range) := by
  classical
  obtain ⟨g, Bk, hsym, hdet, hfix⟩ := exists_orthogonal_frame (k := k) hℓ2 hf hk π b Φ Ψ hΦ c hΨ
    hcomm hΨ2
  obtain ⟨P, a, hB⟩ := hC2 Bk hsym hdet
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  let ι : SL(3, k) →* SL(3, L) :=
    (conjSLn g).comp ((Matrix.SpecialLinearGroup.map (algebraMap k L)).comp (conjSLn P))
  have hι : Function.Injective ι := fun x y h =>
    conjSLn_injective P (mapSL_algebraMap_injective (conjSLn_injective g h))
  let R : Subgroup SL(3, k) := (sym2Hom k).range
  have hℓp : ℓ.Prime := Fact.out
  have : CharP k ℓ := (algebraMap k L).charP_iff_charP ℓ |>.2 inferInstance
  have h2k : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k ℓ] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_two).1 h')
  refine ⟨ι.comp (sym2Hom k), ?_, ?_, ?_, ?_⟩
  · intro Z
    have hY := conj_sym2_form P a Z
    rw [← hB] at hY
    obtain ⟨h1, h2⟩ := hfix _ hY
    exact ⟨h1, h2⟩
  · intro s
    rw [MonoidHom.comp_apply, ← map_one ι, hι.eq_iff, sym2Hom_eq_one_iff]
  · rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hι]
    have h := nat_card_range_sym2Hom (F := k) h2k
    rw [card_SL2_field, hk] at h
    omega
  · intro hq4
    have hk4 : 4 ≤ Nat.card k := by rw [hk]; exact hq4
    rw [MonoidHom.range_comp]
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.map_commutator, commutator_range_sym2Hom hk4]
    have : IsSimpleGroup R := sym2_range_simple h2k hk4
    exact (Subgroup.equivMapOfInjective R ι hι).isSimpleGroup_congr.mp this

end SL3

section Main


variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem exists_Px_hom_three (F : D4PhiFrame ℓ f K σ (-1) p L) (hℓ2 : ℓ ≠ 2)
    (hq3 : 3 ≤ ℓ ^ f) {x : 𝒞[K, σ]} {i : Fin 4} (sp : D4PhiSpecial F x i) (hc1 : sp.c = 1)
    (D : D4PhiAlgData F i)
    (w : 𝒞[K, σ]) (s : ModGL TwistTag.D4.tag L) (hs : s ∈ torusGroup TwistTag.D4.tag L)
    (hw2 : w * w = 1) (hιw : triEmb K σ L w = F.g0 * (s * trialityOpposition L) * F.g0⁻¹)
    (hC2 : ∀ B : Matrix (Fin 3) (Fin 3) (fixSubfield σ), Bᵀ = B → B.det ≠ 0 →
      ∃ (P : GL (Fin 3) (fixSubfield σ)) (a : fixSubfield σ), B = a •
        ((P : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) * sym2Form (fixSubfield σ) *
          (P : Matrix (Fin 3) (Fin 3) (fixSubfield σ))ᵀ)) :
    ∃ θ : SL(2, fixSubfield σ) →* 𝒞[K, σ], (∀ t, θ t ∈ d4phiPx sp) ∧
      (∀ t, θ t * w = w * θ t) ∧ (∀ t, θ t = 1 ↔ t = 1 ∨ t = -1) ∧
      Nat.card θ.range = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) / 2 ∧
      (4 ≤ ℓ ^ f → ⁅θ.range, θ.range⁆ = θ.range ∧ IsSimpleGroup θ.range) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ F.hf F.hK σ F.hσ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set ω : ModGL TwistTag.D4.tag L := s * trialityOpposition L with hω
  obtain ⟨Ψ, cΨ, hΨρ, hΨt⟩ := exists_graph_action_opposition D.frame hs
  have hcommK := d4Q_hcomm (ℓ := ℓ) (f := f) K σ F.hσ L
  have hιfix := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcommK w
  have hωfix : F.n * twistHom TwistTag.D4 L Fr ω * F.n⁻¹ = ω := by
    rw [hιw, map_mul, map_mul, map_inv, F.hg0] at hιfix
    exact conj_cancel_aux F.g0 F.n _ _ (by simpa [mul_assoc] using hιfix)
  have hω2 : ω * ω = 1 := by
    refine sq_eq_one_aux F.g0 ω ?_
    rw [← hιw, ← map_mul, hw2, map_one]
  have hΨρ' : ∀ X, ω * D.ρ X * ω⁻¹ = D.ρ (Ψ X) := hΨρ
  have hcomm : ∀ X, D.Φ' (Ψ X) = Ψ (D.Φ' X) := fun X => by
    apply D.frame.injective
    calc D.ρ (D.Φ' (Ψ X)) = F.n * twistHom TwistTag.D4 L Fr (D.ρ (Ψ X)) * F.n⁻¹ :=
          (D.Φ_eq _).symm
      _ = F.n * twistHom TwistTag.D4 L Fr (ω * D.ρ X * ω⁻¹) * F.n⁻¹ := by rw [hΨρ']
      _ = (F.n * twistHom TwistTag.D4 L Fr ω * F.n⁻¹) *
            (F.n * twistHom TwistTag.D4 L Fr (D.ρ X) * F.n⁻¹) *
            (F.n * twistHom TwistTag.D4 L Fr ω * F.n⁻¹)⁻¹ := conj_twist_aux _ _ _ _
      _ = ω * D.ρ (D.Φ' X) * ω⁻¹ := by rw [hωfix, D.Φ_eq]
      _ = D.ρ (Ψ (D.Φ' X)) := hΨρ' _
  have hΨ2 : ∀ X, Ψ (Ψ X) = X := fun X => by
    apply D.frame.injective
    rw [← hΨρ', ← hΨρ', invol_conj_aux ω _ hω2]
  obtain ⟨π, β, hshape'⟩ := D.shape rfl
  obtain ⟨θ0, hθ0fix, hθ0ker, hθ0card, hθ0ps⟩ := exists_sym2_hom_fixed_three (k := fixSubfield σ)
    hℓ2 F.hf hkc hq3 π β D.Φ' Ψ hshape' cΨ hΨt hcomm hΨ2 hC2
  have hrange : D.ρ.range = rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    rw [D.frame.range, D.sigma_eq]
  have hQP : (fixSubgroup D.Φ').map D.ρ = d4phiQ F i :=
    rcl_map_fix_eq D.frame.injective hrange D.Φ_eq
  obtain ⟨-, -, -, -, -, hQle, -, -⟩ := d4phi_psi_props F sp
  have hψ : Function.Injective (d4phiPsi sp) := d4QPsi_injective triEmb_injective F.g0 sp.c x
  have hρQ : ∀ t, D.ρ (θ0 t) ∈ d4phiQ F i := fun t => by
    rw [← hQP]
    exact ⟨θ0 t, (hθ0fix t).1, rfl⟩
  have hρψ : ∀ t, D.ρ (θ0 t) ∈ (d4phiPsi sp).range := fun t => hQle (hρQ t)
  set θ'' : SL(2, fixSubfield σ) →* Subgroup.centralizer ({x} : Set 𝒞[K, σ]) :=
    ((MonoidHom.ofInjective hψ).symm : (d4phiPsi sp).range ≃* _).toMonoidHom.comp
      ((D.ρ.comp θ0).codRestrict (d4phiPsi sp).range hρψ) with hθ''
  have hθ''ψ : ∀ t, d4phiPsi sp (θ'' t) = D.ρ (θ0 t) := fun t => by
    have := MonoidHom.apply_ofInjective_symm hψ
      ⟨D.ρ (θ0 t), hρψ t⟩
    exact this
  have hθ''c : θ''.range.map (d4phiPsi sp) = (θ0.range).map D.ρ := by
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp]
    congr 1
    exact MonoidHom.ext fun t => hθ''ψ t
  set θ : SL(2, fixSubfield σ) →* 𝒞[K, σ] := (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype.comp θ''
    with hθdef
  have hθrange : θ.range = θ''.range.map (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype := by
    rw [hθdef, MonoidHom.range_comp]
  refine ⟨θ, fun t => ?_, fun t => ?_, fun t => ?_, ?_, ?_⟩
  · refine ⟨θ'' t, ?_, rfl⟩
    show d4phiPsi sp (θ'' t) ∈ d4phiQ F i
    rw [hθ''ψ]
    exact hρQ t
  · have hfixΨ : Ψ (θ0 t) = θ0 t := (hθ0fix t).2
    have hcommω : ω * D.ρ (θ0 t) * ω⁻¹ = D.ρ (θ0 t) := by rw [hΨρ', hfixΨ]
    have hψy : d4phiPsi sp (θ'' t) = F.g0⁻¹ * triEmb K σ L ((θ'' t : _) : 𝒞[K, σ]) * F.g0 := by
      rw [d4phiPsi, d4QPsi_apply, hc1, one_mul, inv_one, mul_one]
    rw [← hθ''ψ, hψy] at hcommω
    have hωeq : ω = F.g0⁻¹ * triEmb K σ L w * F.g0 := by
      rw [hιw]; group
    rw [hωeq] at hcommω
    have h1 : triEmb K σ L w * triEmb K σ L ((θ'' t : _) : 𝒞[K, σ]) =
        triEmb K σ L ((θ'' t : _) : 𝒞[K, σ]) * triEmb K σ L w := by
      have h2 := comm_of_conj_eq_aux F.g0 (F.g0⁻¹ * triEmb K σ L w * F.g0)
        (F.g0⁻¹ * triEmb K σ L ((θ'' t : _) : 𝒞[K, σ]) * F.g0) hcommω
      simpa [mul_assoc] using h2
    have h3 : triEmb K σ L (w * ((θ'' t : _) : 𝒞[K, σ])) =
        triEmb K σ L (((θ'' t : _) : 𝒞[K, σ]) * w) := by
      rw [map_mul, map_mul]; exact h1
    exact (triEmb_injective (K := K) (σ := σ) (L := L) h3).symm
  · show (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype (θ'' t) = 1 ↔ _
    rw [← hθ0ker t]
    constructor
    · intro h
      have h1 : θ'' t = 1 := Subtype.ext h
      have h2 : D.ρ (θ0 t) = 1 := by rw [← hθ''ψ, h1, map_one]
      exact D.frame.injective (h2.trans (map_one D.ρ).symm)
    · intro h
      have h2 : d4phiPsi sp (θ'' t) = 1 := by rw [hθ''ψ, h, map_one]
      have h1 : θ'' t = 1 := hψ (h2.trans (map_one (d4phiPsi sp)).symm)
      rw [h1]
      rfl
  · rw [hθrange, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      ← Subgroup.card_map_of_injective hψ, hθ''c,
      Subgroup.card_map_of_injective D.frame.injective, hθ0card]
  · intro hq4
    obtain ⟨hperf0, hsimple0⟩ := hθ0ps hq4
    have hperf'' : ⁅θ''.range, θ''.range⁆ = θ''.range := by
      apply Subgroup.map_injective hψ
      rw [Subgroup.map_commutator, hθ''c, ← Subgroup.map_commutator, hperf0]
    refine ⟨?_, ?_⟩
    · rw [hθrange, ← Subgroup.map_commutator, hperf'']
    have e : θ.range ≃* θ0.range :=
      (MulEquiv.subgroupCongr hθrange).trans <|
      (Subgroup.equivMapOfInjective θ''.range (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype
        (Subgroup.subtype_injective _)).symm.trans <|
      (Subgroup.equivMapOfInjective θ''.range (d4phiPsi sp) hψ).trans <|
      (MulEquiv.subgroupCongr hθ''c).trans <|
      (Subgroup.equivMapOfInjective θ0.range D.ρ D.frame.injective).symm
    exact e.isSimpleGroup_congr.mpr hsimple0

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
