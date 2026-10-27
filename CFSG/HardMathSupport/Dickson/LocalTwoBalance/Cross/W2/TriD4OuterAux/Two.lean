module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.PGL
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.PGUTwo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoToral
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)

set_option linter.unusedSectionVars false

section Group

variable {Y : Type*} [Group Y]

theorem eq_bot_of_equiv_normal_coprime {H : Subgroup Y} {R : Type*} [Group R] (e : ↥H ≃* R)
    (hN : ∀ M : Subgroup R, M.Normal → Nat.Coprime 3 (Nat.card M) → M = ⊥)
    (N : Subgroup Y) (hNle : N ≤ H) (hNn : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  set M : Subgroup R := N'.map e.toMonoidHom with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm r => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hm
    obtain ⟨g, rfl⟩ := e.surjective r
    refine ⟨g * x * g⁻¹, ?_, by simp⟩
    exact hNn g.1 g.2 x.1 hx
  have hMcard : Nat.card M = Nat.card N := by
    rw [hM, Subgroup.card_map_of_injective e.injective, hN']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
  have hMbot := hN M hMn (hMcard ▸ hcop)
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have h1 : e.toMonoidHom (⟨n, hNle hn⟩ : ↥H) ∈ M := ⟨_, hn, rfl⟩
  rw [hMbot, Subgroup.mem_bot] at h1
  have h2 : (⟨n, hNle hn⟩ : ↥H) = 1 := e.injective (by simpa using h1)
  exact congrArg Subtype.val h2

theorem eq_one_of_equiv_central {H : Subgroup Y} {R : Type*} [Group R] (e : ↥H ≃* R)
    (hZ : ∀ z : R, (∀ x, z * x = x * z) → z = 1) :
    ∀ z ∈ H, (∀ x ∈ H, z * x = x * z) → z = 1 := by
  intro z hz hcomm
  have h : (⟨z, hz⟩ : ↥H) = 1 := by
    apply e.injective
    rw [map_one]
    refine hZ _ fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hcomm y.1 y.2))
  exact congrArg Subtype.val h

theorem exists_two_subgroup_of_dvd [Finite Y] (H : Subgroup Y) {n : ℕ}
    (hdvd : 2 ^ n ∣ Nat.card H) :
    ∃ U : Subgroup Y, U ≤ H ∧ IsPGroup 2 U ∧ 2 ^ n ≤ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H) 2 hdvd
  refine ⟨K.map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have hK' : IsPGroup 2 K := IsPGroup.of_card hK
    exact hK'.map H.subtype
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hK]

end Group

section Main


theorem card_projImage_glPi_three {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) :
    Nat.card ↥(projImage (glPi π 3 (p ^ f) K)) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
  rw [Sec16.ProofKSL3Two.card_projImage_glPi hK, Sec13.card_slPi_three hK]

theorem coreFreeAt_of_equiv_projImage {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {π : Bool} {F : Type} [Field F] (hF : PiField π 2 f F) (hπ : Even f → π = true)
    (hZ : ∀ z : ↥(projImage (glPi π 3 (2 ^ f) F)), (∀ x, z * x = x * z) → z = 1)
    (hN : ∀ M : Subgroup ↥(projImage (glPi π 3 (2 ^ f) F)), M.Normal →
      Nat.Coprime 3 (Nat.card M) → M = ⊥)
    (e : ↥(fixSub φ) ≃* ↥(projImage (glPi π 3 (2 ^ f) F))) : CoreFreeAt 3 φ := by
  have := hF.finite
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_injective (fun x => (x : ModGL TwistTag.D4.tag K)) Subtype.val_injective
  have hcard : Nat.card ↥(fixSub φ) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    rw [Nat.card_congr e.toEquiv, card_projImage_glPi_three hF, mul_assoc]
  refine ⟨fun N hNle hNn hcop => eq_bot_of_equiv_normal_coprime e hN N hNle hNn hcop, ?_⟩
  refine trialityFaithfulTwo_holds f hf K hK σ hσ φ (eq_one_of_equiv_central e hZ) ?_ ?_
  · have hdvd : 2 ^ (f * 3) ∣ Nat.card ↥(fixSub φ) := by
      rw [hcard, pow_mul]
      exact dvd_mul_right _ _
    obtain ⟨U, hUle, hU2, hUcard⟩ := exists_two_subgroup_of_dvd (fixSub φ) hdvd
    exact ⟨U, hUle, hU2, by rwa [pow_mul] at hUcard⟩
  · intro hfe ζ hζ2 hζout _ hζfix
    have hπ' := hπ hfe
    subst hπ'
    refine outer_involution_false_of_dvd_two hf hfe hK hσ φ ?_ ζ hζ2 hζout hζfix
    rw [hcard]
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      simpa using this
    simp only [cond_true]
    rw [h1]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_mul_right _ _) _) _

theorem two_pow_mod_three_even {f : ℕ} (hf : Even f) : 2 ^ f % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hf
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_odd {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem pgu_two_props {p f : ℕ} {K : Type} [Field K] (hK : PiField false p f K) (h2 : p ^ f = 2) :
    (∀ z : ↥(projImage (glPi false 3 (p ^ f) K)), (∀ x, z * x = x * z) → z = 1) ∧
    (∀ N : Subgroup ↥(projImage (glPi false 3 (p ^ f) K)), N.Normal →
      Nat.Coprime 3 (Nat.card N) → N = ⊥) := by
  obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hK.prime h2
  have := hK.finite
  have hq : ModThree false (2 ^ 1) := by
    show (2 ^ 1) % 3 = 2
    norm_num
  refine ⟨pgu_two_center_trivial hK hq, fun N hN hcop => ?_⟩
  have hcard : Nat.card ↥(projImage (glPi false 3 (2 ^ 1) K)) = 2 ^ 3 * 3 ^ 3 := by
    rw [card_projImage_glPi_three hK]
    norm_num
  have hdvd : Nat.card N ∣ 2 ^ 3 * 3 ^ 3 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hdvd2 : Nat.card N ∣ 2 ^ 3 :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 3 hcop.symm) hdvd)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pgu_two_no_normal_two_group hK hq N (IsPGroup.of_card hk)

theorem coreFreeAt_three_D4_outer_two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    CoreFreeAt 3 φ := by
  have hG2 : CoreFreeAt 3 (fieldActor (t := TwistTag.D4) σ σ) :=
    coreFreeAt_three_fieldActor_self Nat.prime_two (by norm_num) hf hK σ hσ
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hφ3
    (by exact hφ) with ⟨β, hβ | hβ⟩ | he₂
  · rw [hβ]
    exact hG2.conj β
  · rw [hβ]
    exact hG2.inv.conj β
  · obtain ⟨e₂⟩ := he₂
    have hfix : fixSub φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    let ef : ↥(fixSub φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfix
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
      have hPi : PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
      have hq : ModThree true (2 ^ f) := two_pow_mod_three_even hfe
      have hf2 : 2 ≤ f := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have hq2 : 2 < 2 ^ f :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact coreFreeAt_of_equiv_projImage hf hK hσ φ hPi (fun _ => rfl)
        (pgl_center_trivial hPi hq hq2)
        (fun N hN hc => pgl_normal_coprime_eq_bot hPi hq hq2 N hc) (ef.trans (e₂.trans e₃))
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K σ hK hσ
      have hPi : PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
      have hq : ModThree false (2 ^ f) := two_pow_mod_three_odd hfo
      have hnoteven : ¬ Even f := Nat.not_even_iff_odd.2 hfo
      by_cases hf1 : f = 1
      · subst hf1
        obtain ⟨hZ, hN⟩ := pgu_two_props hPi (by norm_num)
        exact coreFreeAt_of_equiv_projImage hf hK hσ φ hPi (fun h => absurd h hnoteven)
          hZ hN (ef.trans (e₂.trans e₃))
      · have hf3 : 3 ≤ f := by
          obtain ⟨k, hk⟩ := hfo
          omega
        have hq2 : 2 < 2 ^ f :=
          lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
        exact coreFreeAt_of_equiv_projImage hf hK hσ φ hPi (fun h => absurd h hnoteven)
          (pgl_center_trivial hPi hq hq2)
          (fun N hN hc => pgl_normal_coprime_eq_bot hPi hq hq2 N hc) (ef.trans (e₂.trans e₃))

end Main

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
