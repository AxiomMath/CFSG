module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyCover3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3InnerAll
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3OuterRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOffenderAssembly

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.Quasithin

section Small

theorem natCast_surjective_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = p) (k : K) : ∃ n : ℕ, (n : K) = k := by
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hbij : Function.Bijective f :=
    f.injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])
  obtain ⟨m, rfl⟩ := hbij.2 k
  refine ⟨m.val, ?_⟩
  rw [← map_natCast f m.val, ZMod.natCast_zmod_val]

end Small

section Final

open CFSG.SectionRank.OddCover in
theorem primeUnitaryThreeExclusion : PrimeUnitaryThreeExclusionProp := by
  classical
  intro p hp hp5 W _ _ hW Lb hperf hirr hmod B hBN hB1 hB2
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hp2 : p ≠ 2 := by omega
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hK2 : Nat.card K = p ^ 2 := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK2
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 2) hKcard
  have h : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK]; ring⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hH : ((-1 : ℤ) = 1 ∧ Nat.card K = p ∧ StatedSU 3 (p ^ 1) K = StatedSL 3 K) ∨
      ((-1 : ℤ) = -1 ∧ Nat.card K = p ^ 2 ∧ StatedSU 3 (p ^ 1) K = StatedSU 3 p K) :=
    Or.inr ⟨rfl, hK2, by rw [pow_one]⟩
  obtain ⟨φ, hφs, hφc, hφk⟩ := exists_cover_hom (ε := -1) (H := StatedSU 3 (p ^ 1) K) hp hp2 hH
    hperf hodd e
  have hperfSU : Group.IsPerfect ↥(StatedSU 3 (p ^ 1) K) := isPerfect_prime_three hp hp2 hH
  have hperfSUI : Group.IsPerfect ↥(SUI h) :=
    Group.IsPerfect.ofSurjective (f := (eSU h).toMonoidHom) (eSU h).surjective
  let D : CoverDataU h Lb := coverDataU_of_cover h e φ hφs hφc hφk
  have hkerodd : Odd (Nat.card φ.ker) := by
    have hdvd := Subgroup.card_dvd_of_le hφk
    rw [(CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.2] at hdvd
    exact Odd.of_dvd_nat (by decide : Odd 3) (hdvd.trans (Nat.gcd_dvd_left 3 _))
  have hkerc : ∀ g ∈ φ.ker, ∀ x : ↥(StatedSU 3 (p ^ 1) K), g * x = x * g := by
    intro g hg x
    have h1 := hφk hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
    obtain ⟨r, hr⟩ := h1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hr]
    exact ((commute_scalar r (x : GL (Fin 3) K)).eq).symm
  let ρ₀ : ↥(StatedSU 3 (p ^ 1) K) →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    binaryLin.comp (Lb.subtype.comp φ)
  have hρ₀ : ∀ g, ρ₀ g = 1 →
      ∃ r : Kˣ, (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r := by
    intro g hg
    have h1 : ((φ g : ↥Lb) : MulAut W) = 1 := binaryLin_injective (by rw [map_one]; exact hg)
    have h2' : φ g = 1 := Subtype.ext h1
    have h3 := hφk (MonoidHom.mem_ker.2 h2')
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h3
    obtain ⟨r, hr⟩ := h3
    exact ⟨r, hr.symm⟩
  have hB2' : ∀ a ∈ B, a * a = 1 := fun a ha => by
    have := hB2.2 a ha
    rwa [pow_two] at this
  have hbN : ∀ a ∈ B, a ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := fun a ha => hBN ha
  have hin : ∀ t ∈ B, t ∈ Lb → t ≠ 1 →
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin t))) := by
    intro t htB htL ht1
    obtain ⟨g, hg2, hgt⟩ := exists_involution_lift φ hkerodd (t := (⟨t, htL⟩ : ↥Lb))
      (Subtype.ext (hB2' t htB)) (MonoidHom.mem_range.2 (hφs _))
    have hg1 : g ≠ 1 := fun h' => ht1 (by
      have := hgt
      rw [h', map_one] at this
      exact congrArg Subtype.val this.symm)
    have h4 := inner_rank_ge_four_unitary hp5 hK ρ₀ hρ₀ hg2 hg1
    have e1 : ρ₀ g = binaryLin t := by simp [ρ₀, hgt]
    rwa [e1] at h4
  have hcard : ∀ T : Subgroup (MulAut W), T ≤ B → T ≤ Lb → Nat.card T ≤ 4 := by
    intro T hTB hTL
    have hcT : Nat.card (T.subgroupOf Lb) ≤ 4 := by
      refine card_le_of_lifts φ hkerc hkerodd 4
        (fun T' hT' => card_le_four_of_det_one h2 (H := StatedSU 3 (p ^ 1) K)
          (fun x hx => CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU hx) T' hT')
        (T.subgroupOf Lb) (fun x _ => MonoidHom.mem_range.2 (hφs x)) (fun x hx => ?_)
        (fun x hx y hy => ?_)
      · exact Subtype.ext (hB2' _ (hTB hx))
      · exact Subtype.ext (hB2.1 _ (hTB hx) _ (hTB hy))
    have : Nat.card (T.subgroupOf Lb) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    omega
  let F := ↥(CFSG.LieType.Steinberg.fixedSubfield K p 1)
  have : Finite F := inferInstance
  have : Fintype F := Fintype.ofFinite F
  have hFcardN : Nat.card F = p := by
    have := CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := p) (f := 1) hK
    rwa [pow_one] at this
  have hFcard : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card]; exact hFcardN
  have : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by rw [pow_one]; exact hFcard)
  let ι : F →+* K := (CFSG.LieType.Steinberg.fixedSubfield K p 1).subtype
  have hι : ∀ x : F, h.bar (ι x) = ι x := fun x => by
    have h1 := x.2
    rw [CFSG.LieType.Steinberg.mem_fixedSubfield,
      CFSG.LieType.BorelTits.unitaryInvolution_apply] at h1
    rw [h.bar_apply]
    exact h1
  have hfix : ∀ m : K, h.bar m = m → ∃ x : F, ι x = m := fun m hm =>
    ⟨⟨m, by
      rw [CFSG.LieType.Steinberg.mem_fixedSubfield,
        CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply]
      exact hm⟩, rfl⟩
  have hFK : ∀ k : F, ∃ n : ℕ, (n : F) = k := natCast_surjective_of_card_prime hFcardN
  have hout : ∀ a ∈ B, a ∉ Lb →
      2 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin a))) := by
    intro a haB haL
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a haB) (hB2' a haB) with
      h' | ⟨A, hAs, hAA, hβ⟩
    · exact absurd h' haL
    · exact D.outer_rank ι hFcard hp5 hι hfix hFK hperfSUI (hbN a haB) (hB2' a haB) A hAs hAA hβ
  have hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ Lb → a' ∉ Lb → a * a' ∈ Lb := by
    intro a haB a' ha'B haL ha'L
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a haB) (hB2' a haB) with
      h' | ⟨A, -, -, hβ⟩
    · exact absurd h' haL
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a' ha'B) (hB2' a' ha'B) with
      h'' | ⟨A', -, -, hβ'⟩
    · exact absurd h'' ha'L
    have hsq : a * a' * (a * a') = 1 := by
      calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hB2.1 a' ha'B a haB]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [hB2' a haB, hB2' a' ha'B, one_mul]
    exact D.mul_mem hperfSUI hW hirr.2 hodd (hbN a haB) (hbN a' ha'B) hβ hβ' hsq
  by_contra hne
  push Not at hne
  let Fx : Submodule (ZMod 2) (Additive W) :=
    { carrier := {x | ∀ a ∈ B, binaryLin a x = x}
      add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
      zero_mem' := fun a _ => map_zero _
      smul_mem' := fun c x hx a ha => by rw [map_smul, hx a ha] }
  have hfixc : Nat.card Fx = Nat.card (fixV B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => congrArg Additive.toMul (x.2 a ha)⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun a ha => congrArg Additive.ofMul (w.2 a ha)⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
  have hpgrp : IsPGroup 2 B := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hB2.2 a a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : Module.finrank (ZMod 2) (Additive W) - Module.finrank (ZMod 2) Fx ≤
      Nat.log 2 (Nat.card B) := by
    refine finrank_sub_le_log_of_card_le Fx hk ?_
    rw [hcardE, hfixc]
    exact hne
  exact no_offender_of_ranks binaryLin Lb B hB1 Fx (fun a ha x hx => hx a ha) hin hcard hout hidx
    hoff

end Final


end CFSG.QuasithinUnique.Setup.Family
