module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenOACheck
public import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Dim

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


namespace KSNotAll24

theorem exists_torV_eq_of_cube_one {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin τ.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1) :
    ∃ ζ : Lˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ ∃ v : Fin τ.rank → ZMod 3, torV ζ v = a := by
  classical
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ζ₀ := hζ₀.isUnit (by norm_num)
  have hζ : IsPrimitiveRoot ((hu.unit : Lˣ) : L) 3 := by simpa using hζ₀
  have hω : orderOf hu.unit = 3 := (IsPrimitiveRoot.coe_units_iff.1 hζ).eq_orderOf.symm
  obtain ⟨ω, hωdef⟩ : ∃ ω : Lˣ, ω = hu.unit := ⟨_, rfl⟩
  rw [← hωdef] at hω
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  have hω2 : ((ω : L) ^ 2 + (ω : L) + 1) = 0 := by
    have hω3' : ((ω : L)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
    have hω1' : ((ω : L)) ≠ 1 := by
      intro h
      exact hω1 (Units.ext h)
    have h2 : ((ω : L) - 1) * ((ω : L) ^ 2 + (ω : L) + 1) = 0 := by
      have h := hω3'
      calc
        ((ω : L) - 1) * ((ω : L) ^ 2 + (ω : L) + 1) = ((ω : L)) ^ 3 - 1 := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := by norm_num
    have h3' : ((ω : L) - 1) ≠ 0 := sub_ne_zero.mpr hω1'
    exact (mul_eq_zero.mp h2).resolve_left h3'
  have hex : ∀ i, ∃ k : ZMod 3, ω ^ k.val = a i := fun i => by
    have hμ : ((a i : L)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ha i, Units.val_one]
    obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK432.exists_zmod_three_pow_eq hω2 hμ
    exact ⟨k, Units.ext (by simpa using hk)⟩
  choose k hk using hex
  exact ⟨ω, hω3, hω1, k, funext fun i => hk i⟩

theorem exists_torus_conj_of_cube_one_with_conjugator {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) {x : ModGL Tag.E6 K}
    (hxL : baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
      adjointGroup Tag.E6 (AlgebraicClosure K))
    (hx3 : x ^ 3 = 1) :
    ∃ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) ∧
      (rootDiagUnit Tag.E6 a = 1 → x = 1) ∧
      Module.finrank K (LinearMap.ker ((x : Module.End K (RootModule Tag.E6 K)) - 1)) =
        Module.finrank (AlgebraicClosure K) (LinearMap.ker
          ((rootDiag a : Module.End (AlgebraicClosure K) (RootModule Tag.E6 (AlgebraicClosure K)))
            - 1)) ∧
      ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g = rootDiagUnit Tag.E6 a := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp, hpK⟩ : ∃ p, Nat.Prime p ∧ ringChar K = p :=
    ⟨ringChar K, CharP.char_is_prime K (ringChar K), rfl⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := hpK ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hp3 : p ≠ 3 := hpK ▸ hK3
  have hL3 : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) p]
    exact hp3
  obtain ⟨sL, hsL⟩ : ∃ g, g = baseChangeGL (algebraMap K (AlgebraicClosure K)) x := ⟨_, rfl⟩
  have hsLG : sL ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := hsL ▸ hxL
  have hsL3 : sL ^ 3 = 1 := by rw [hsL, ← map_pow, hx3, map_one]
  have hfin : ((Subgroup.zpowers sL : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :
      Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite :=
    (finite_zpowers).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hsL3⟩)
  have hexp : ∀ x ∈ Subgroup.zpowers sL, x ^ 3 = 1 := by
    rintro _ ⟨n, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsL3, one_zpow]
  have hzle : Subgroup.zpowers sL ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [Subgroup.zpowers_le]
    exact hsLG
  obtain ⟨c₁, hc₁, hc₁m⟩ := exists_conj_le_monomial_bar (ℓ := p) (p := 3) hp3
    (isAlgebraic_zmod_algebraicClosure_of_finite K p) hzle hfin hexp
  have hn := hc₁m sL (Subgroup.mem_zpowers sL)
  have hn3 : (c₁ * sL * c₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hsL3, mul_one, mul_inv_cancel]
  obtain ⟨c₂, hc₂, hc₂t⟩ := exists_conj_mem_torusGroup_of_mem_monomial
    monomialToralAt_E6_three hL3 hn hn3
  obtain ⟨t, ht⟩ : ∃ t, t = (c₂ * c₁) * sL * (c₂ * c₁)⁻¹ := ⟨_, rfl⟩
  have ht' : t = c₂ * (c₁ * sL * c₁⁻¹) * c₂⁻¹ := by rw [ht]; group
  have htT : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := ht' ▸ hc₂t
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom htT
  have hta : t = rootDiagUnit Tag.E6 a := ha.symm
  have ht3 : t ^ 3 = 1 := by rw [ht, conj_pow, hsL3, mul_one, mul_inv_cancel]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnitHom Tag.E6 (AlgebraicClosure K) (a ^ 3) =
        rootDiagUnitHom Tag.E6 (AlgebraicClosure K) 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit Tag.E6 a) ^ 3 = 1
      rw [← hta, ht3]
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (τ := Tag.E6)
      (K := AlgebraicClosure K) h1
    intro i
    have := congrFun h2 i
    simpa using this
  refine ⟨a, ha3, fun h1 => ?_, ?_, (c₂ * c₁)⁻¹, ?_, ?_⟩
  · have ht1 : (c₂ * c₁) * sL * (c₂ * c₁)⁻¹ = 1 := by rw [← ht, hta]; exact h1
    have : sL = 1 :=
      mul_left_cancel (a := c₂ * c₁) ((mul_inv_eq_one.1 ht1).trans (mul_one _).symm)
    apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
    rw [← hsL, this, map_one]
  · have hdimL : Module.finrank (AlgebraicClosure K)
        (LinearMap.ker ((sL : Module.End (AlgebraicClosure K) (RootModule Tag.E6
          (AlgebraicClosure K))) - 1)) =
        Module.finrank K (LinearMap.ker ((x : Module.End K (RootModule Tag.E6 K)) - 1)) := by
      have h := finrank_ker_baseChangeEnd (L := AlgebraicClosure K)
        ((x : Module.End K (RootModule Tag.E6 K)) - 1)
      rw [baseChangeEnd_sub_aux, baseChangeEnd_one_aux] at h
      rw [hsL, coe_baseChangeGL, h]
    have h := finrank_ker_conj_sub_one (c₂ * c₁) sL
    rw [← ht] at h
    rw [← hdimL, ← h, hta]
    rfl
  · exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hc₂ hc₁)
  · rw [inv_inv, ← hsL, ← ht, hta]

theorem exists_torus_conj_of_cube_one {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    {x : ModGL Tag.E6 K}
    (hxL : baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
      adjointGroup Tag.E6 (AlgebraicClosure K))
    (hx3 : x ^ 3 = 1) :
    ∃ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) ∧
      (rootDiagUnit Tag.E6 a = 1 → x = 1) ∧
      Module.finrank K (LinearMap.ker ((x : Module.End K (RootModule Tag.E6 K)) - 1)) =
        Module.finrank (AlgebraicClosure K) (LinearMap.ker
          ((rootDiag a : Module.End (AlgebraicClosure K) (RootModule Tag.E6 (AlgebraicClosure K)))
            - 1)) := by
  obtain ⟨a, ha3, ha1, hdim, _, _, _⟩ :=
    exists_torus_conj_of_cube_one_with_conjugator hK3 hxL hx3
  exact ⟨a, ha3, ha1, hdim⟩

local instance e6NeZeroRankKS : NeZero Tag.E6.rank := ⟨by decide⟩

theorem e6KerCount_mem_of_ne_zero :
    ∀ a b c d e f : ZMod 3, e6ConjVec a b c d e f ≠ 0 →
      e6KerCount (e6ConjVec a b c d e f) ∈ ({18, 22, 24, 30, 40} : Finset ℕ) := by
  decide +kernel

theorem finrank_ker_rootDiag_mem {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1) (ha1 : rootDiagUnit Tag.E6 a ≠ 1) :
    Module.finrank L (LinearMap.ker
      ((rootDiag a : Module.End L (RootModule Tag.E6 L)) - 1)) ∈
        ({24, 28, 30, 36, 46} : Set ℕ) := by
  classical
  obtain ⟨ω, hω3, hω1, x₀, hax⟩ := exists_torV_eq_of_cube_one h3 ha
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    apply ha1
    rw [← hax]
    have : torV ω (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
      funext i
      simp [torV]
    rw [this]
    exact rootDiagUnit_one
  have hx0' : x₀ = e6ConjVec (x₀ 0) (x₀ 1) (x₀ 2) (x₀ 3) (x₀ 4) (x₀ 5) := by
    funext i
    fin_cases i <;> rfl
  have hmem := e6KerCount_mem_of_ne_zero (x₀ 0) (x₀ 1) (x₀ 2) (x₀ 3) (x₀ 4) (x₀ 5)
    (by rw [← hx0']; exact hx0)
  rw [← hx0'] at hmem
  have hcount := finrank_ker_rootDiag_sub_one_card a
  have hc : ((rootFinset .E6).filter fun α => rootChar a α = 1).card = e6KerCount x₀ := by
    rw [← hax]
    exact card_filter_rootChar_torV hω3 hω1 x₀
  rw [hc] at hcount
  change _ = 6 + _ at hcount
  rw [hcount]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem exists_coroot_conj_of_cube_one_of_finrank_eq_thirtysix
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) {x : ModGL Tag.E6 K}
    (hxL : baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
      adjointGroup Tag.E6 (AlgebraicClosure K))
    (hx3 : x ^ 3 = 1)
    (hdim : Module.finrank K (LinearMap.ker ((x : Module.End K (RootModule Tag.E6 K)) - 1)) = 36) :
    ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      ∃ ρ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 ρ ∧
      ∃ ζ : (AlgebraicClosure K)ˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g =
          rootDiagUnit Tag.E6 (fun j => ζ ^ (iform ρ (Pi.single j 1) : ℤ)) := by
  classical
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 3).1 h0
    exact hK3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 this)
  obtain ⟨a, ha3, ha1, hdim_eq, g, hg, hconj⟩ :=
    exists_torus_conj_of_cube_one_with_conjugator hK3 hxL hx3
  obtain ⟨ζ, hζ3, hζ1, v, hv⟩ := exists_torV_eq_of_cube_one h3L ha3
  have hdimL : Module.finrank (AlgebraicClosure K)
      (LinearMap.ker ((rootDiag a : Module.End (AlgebraicClosure K)
        (RootModule Tag.E6 (AlgebraicClosure K))) - 1)) = 36 := by
    rw [← hdim_eq, hdim]
  have hcard_v : e6KerCount v = 30 := by
    have h := hdimL
    rw [finrank_ker_rootDiag_sub_one_card a] at h
    have h2 : ((rootFinset .E6).filter fun α => rootChar a α = 1).card = e6KerCount v := by
      rw [← hv]
      exact card_filter_rootChar_torV hζ3 hζ1 v
    rw [h2] at h
    change 6 + _ = 36 at h
    omega
  obtain ⟨ρ, hρ, hcoord⟩ := e6Cen_coroot_of_kerCount v hcard_v
  have ha_eq : a = fun j => ζ ^ (iform ρ (Pi.single j 1) : ℤ) := by
    funext j
    rw [← hv]
    simp only [torV]
    rw [hcoord j]
    exact SmallQ3.zpow_val_intCast hζ3 (iform ρ (Pi.single j 1))
  refine ⟨g, hg, ρ, hρ, ζ, hζ3, hζ1, ?_⟩
  rw [hconj, ha_eq]

theorem exists_cube_root_algebraicClosure {K : Type} [Field K] (c : Kˣ) :
    ∃ u : (AlgebraicClosure K)ˣ,
      u ^ 3 = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (c : K))
    (by norm_num : 0 < 3)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact (c.ne_zero ((map_eq_zero _).1 hz.symm))
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

end KSNotAll24

@[expose] def TwE6Order3Dim : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ h : twistedE6InndiagGL K σ, h ^ 3 = 1 → h ≠ 1 →
      Module.finrank K (LinearMap.ker (((h : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) - 1)) ∈ ({24, 28, 30, 36, 46} : Set ℕ)

theorem twE6Order3Dim_holds : TwE6Order3Dim := by
  intro K _ _ σ q hK3 hσ hKq h3 hq2 h hh3 hh1
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hxL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL TwistTag.E6.tag K) ∈
      adjointGroup Tag.E6 (AlgebraicClosure K) :=
    map_twistedE6InndiagGL_le σ (algebraMap K (AlgebraicClosure K))
      KSNotAll24.exists_cube_root_algebraicClosure (Subgroup.mem_map_of_mem _ h.2)
  have hx3 : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  obtain ⟨a, ha3, ha1, hdim⟩ :=
    KSNotAll24.exists_torus_conj_of_cube_one (x := (h : ModGL TwistTag.E6.tag K)) hK3 hxL hx3
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 3).1 h0
    exact hK3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 this)
  have key := KSNotAll24.finrank_ker_rootDiag_mem h3L ha3
    (fun h1 => hh1 (Subtype.ext (ha1 h1)))
  rw [← hdim] at key
  exact key

end Dim

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
