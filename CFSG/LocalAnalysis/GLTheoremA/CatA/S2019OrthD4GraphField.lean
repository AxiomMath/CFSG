module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientGraphField
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Outer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwisted
import CFSG.SignalizerFunctorTheorem.CatalogBridge.TwistedOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.SignalizerFunctorTheorem.CatalogBridge CFSG.SignalizerFunctorTheorem.NonLocalExc
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Invariance

variable {G : Type} [Group G]

theorem s2019FixCentralizes_of_inv {p : ℕ} {β : MulAut G} (h : S2019FixCentralizes p β⁻¹) :
    S2019FixCentralizes p β := by
  have e : fixSubgroup β⁻¹ = fixSubgroup β := fixedSubgroup_inv_eq β
  intro L hL
  rw [← e] at hL
  exact h L hL

theorem s2019FixCentralizes_of_conj [Finite G] {p : ℕ} (hp : p.Prime) (ψ β : MulAut G)
    (h : S2019FixCentralizes p (ψ * β * ψ⁻¹)) : S2019FixCentralizes p β := by
  have e : MulAut.congr ψ β = ψ * β * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  exact s2019FixCentralizes_of_congr hp ψ β (e ▸ h)

end Invariance

section Twist


theorem s2019FixCentralizes_twistedEntrywiseAut_D4 {ℓ e : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ e) ^ 3)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    S2019FixCentralizes 3 (twistedEntrywiseAut TwistTag.D4 j T) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨σ, r, hr, hσ, hfix⟩ : ∃ (σ : K ≃+* K) (r : ℕ), (r = 1 ∨ r = 2) ∧
      (∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) ∧
      fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T) =
        fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ) := by
    rcases hj with rfl | rfl
    · exact ⟨T, 1, Or.inl rfl, fun c => by rw [pow_one]; exact hT c, rfl⟩
    · have hT3 : T ^ 3 = 1 := by
        refine RingEquiv.ext fun c => ?_
        change T (T (T c)) = c
        rw [hT, hT, hT, ← pow_mul, ← pow_mul,
          show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
      have hinv : ∀ c, (T⁻¹) c = c ^ ((ℓ ^ e) ^ 2) := by
        have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
        intro c
        rw [h1, pow_two]
        change T (T c) = _
        rw [hT, hT, ← pow_mul, sq]
      exact ⟨T⁻¹, 2, Or.inr rfl, hinv, fixedSubgroup_twistedEntrywiseAut_D4_two T⟩
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨-, -, hΓ, hsimple, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    ℓ e hℓ he K hK L r hr σ.toRingHom (fun c => hσ c) (iterateFrobenius L ℓ e)
    (fun c => iterateFrobenius_def ℓ e c)
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  have hC₀X : C₀ ≤ adjointGroup TwistTag.D4.tag K :=
    (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom).trans
      (twistedFixedGroup_le_adjointGroup TwistTag.D4 K σ.toRingHom)
  set J : Subgroup (adjointGroup TwistTag.D4.tag K) :=
    C₀.subgroupOf (adjointGroup TwistTag.D4.tag K) with hJ
  have hfixJ : fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T) = J := by
    change fixedSubgroup _ = _
    rw [hfix, fixedSubgroup_twistedEntrywiseAut_one TwistTag.D4 σ, hΓ]
  haveI : IsSimpleGroup C₀ := hsimple
  have hJs : IsSimpleGroup J := (Subgroup.subgroupOfEquivOfLe hC₀X).isSimpleGroup
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hJn : NonLocalized J := by
    choose a ha using exists_orbit_mem TwistTag.D4
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element TwistTag.D4.tag
    have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K w₀ ∈ C₀ :=
      canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
    have hyJ : ∀ i, (orbitX TwistTag.D4 K σ.toRingHom (a i) 1 : ModGL TwistTag.D4.tag K) ∈ C₀ :=
      fun i => graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
        (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom (a i) 1)
    have hyU : ∀ i, (orbitX TwistTag.D4 K σ.toRingHom (a i) 1 : ModGL TwistTag.D4.tag K) ∈
        posUnipotent TwistTag.D4.tag K := fun i =>
      (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom (a i) 1)).1
    let F := AlgebraicClosure K
    haveI : CharP F ℓ := charP_of_injective_algebraMap (algebraMap K F).injective ℓ
    let ρ : ↥(adjointGroup TwistTag.D4.tag K) →* Module.End F (Label TwistTag.D4.tag → F) :=
      (adjRep TwistTag.D4.tag K F).comp (adjointGroup TwistTag.D4.tag K).subtype
    have hρ : Function.Injective ρ :=
      (adjRep_injective TwistTag.D4.tag K F).comp Subtype.val_injective
    have hcard := (triality_both_orientations_exact_finite_order ℓ e hℓ he K hK r hr
      σ.toRingHom (fun c => hσ c)).1
    have hcardJ : Nat.card J = Nat.card C₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC₀X).toEquiv
    obtain ⟨s, e', hs, hdvd, hnd⟩ := exists_prime_pow_dvd_not_dvd_factorial_D4 hℓ he
      (fun h => hℓ2 h.1)
    obtain ⟨R, hRJ, hR⟩ := exists_le_subgroup_card_not_dvd_factorial (J := J) (n := 28)
      (exists_subgroup_card_not_dvd_factorial (hcardJ.trans hcard) hs hdvd hnd)
    have h28 : TwistTag.D4.tag.rank + TwistTag.D4.tag.rootCount = 28 := by decide
    have hR' : ¬ Nat.card R ∣ (Module.finrank F (Label TwistTag.D4.tag → F)).factorial := by
      rw [finrank_label_pi, card_label_eq, h28]
      exact hR
    exact nonLocalized_of_regular_data (τ := TwistTag.D4.tag) ℓ
      (X := adjointGroup TwistTag.D4.tag K) le_rfl hC₀X hJs
      (y := fun i => (orbitX TwistTag.D4 K σ.toRingHom (a i) 1 : ModGL TwistTag.D4.tag K))
      hyJ hyU (c := fun _ => 1) (fun _ => one_ne_zero)
      (fun i => hasCoord_orbitX_one σ.toRingHom (a i) (ha i)) hw₀ hn ρ hρ R hRJ hR'
  haveI : Finite (adjointGroup TwistTag.D4.tag K) := Subtype.finite
  refine s2019FixCentralizes_of_nonLocalized 3 _ (J := J) hfixJ.symm.le ?_ hJs hJn
  rw [hfixJ, Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)

theorem s2019FixCentralizes_d4_graphField {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0) (hσ : σ ≠ 1)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    S2019FixCentralizes 3 α := by
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  have hσ3 := sigma_pow_three_eq_one_of_cube α hα3 g a σ ε hα
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, hf0, pow_zero] at this
    omega
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three (Fact.out : ℓ.Prime) hf K hK σ hord
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le 2
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  rcases hσT with rfl | rfl
  · obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef _ hT α hα3
      g a ε hα
    have h1 := s2019FixCentralizes_twistedEntrywiseAut_D4 hℓ2 he K hK' _ hT (ε : ℤ) (by omega)
    rw [← hψ] at h1
    exact s2019FixCentralizes_of_conj Nat.prime_three ψ α h1
  · obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) α hα3 g a ε hα
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    have h1 := s2019FixCentralizes_twistedEntrywiseAut_D4 hℓ2 he K hK' T hT (3 - (ε : ℤ))
      (by omega)
    rw [← hshift, ← hψ] at h1
    exact s2019FixCentralizes_of_inv (s2019FixCentralizes_of_conj Nat.prime_three ψ α⁻¹ h1)

end Twist

end CFSG.LocalAnalysis.GLTheoremA.S2019
