module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSp
public import CFSG.Sporadic.Schreier.TitsInner

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem card_fusionZStar_le_fixed {K : Type} [Group K] [Finite K] {α : MulAut K}
    (P : Subgroup (fixedSubgroup α)) :
    Nat.card (P ⧸ Open.fusionZStar P) ≤ Nat.card (fixedSubgroup α) :=
  (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans
    (Subgroup.card_le_card_group P)

theorem five_le_of_psl2 {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Z .PSL 2 p m) : 5 ≤ p ^ m := by
  obtain ⟨hp, hm1, -, -, h23⟩ := admissible_of_lieModel h
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases (show p = 2 ∨ 3 ≤ p by omega) with h | h
    · exact absurd h hp2
    · exact h
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  have hle : p ≤ p ^ m := Nat.le_self_pow (by omega) p
  have h3 : p ^ m ≠ 3 := fun h3 => h23 (by rw [h3])
  obtain ⟨j, hj⟩ := hodd
  omega

theorem sixty_le_card_of_psl2 {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Z .PSL 2 p m) : 60 ≤ Nat.card Z := by
  have hc := card_mul_two_of_psl2 hp2 h
  have h5 := cube_mono (five_le_of_psl2 hp2 h)
  norm_num at h5
  omega

theorem card_fixedSubgroup_lt {K : Type} [Group K] [Finite K] {α : MulAut K}
    (hα : orderOf α = 2) : Nat.card (fixedSubgroup α) < Nat.card K := by
  have hne : fixedSubgroup α ≠ ⊤ := by
    intro htop
    have h1 : α = 1 := MulEquiv.ext fun x => by
      have : x ∈ fixedSubgroup α := htop ▸ Subgroup.mem_top x
      exact AschbacherToolkit.mem_fixedSubgroup.mp this
    rw [h1, orderOf_one] at hα
    exact absurd hα (by norm_num)
  exact lt_of_le_of_ne (Subgroup.card_le_card_group _)
    (fun h => hne ((Subgroup.card_eq_iff_eq_top _).mp h))

theorem le_half_of_dvd_of_lt {d n : ℕ} (hd : d ∣ n) (hlt : d < n) : d ≤ n / 2 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases k with _ | _ | k
  · simp at hlt
  · simp at hlt
  · exact Nat.mul_le_mul_left d (by omega)

theorem noOddPSL2_L24
    {K : Type} [Group K] (hm : Blueprint.LieModel K .PSL 2 2 2) : NoOddPSL2 K := by
  intro α hα _ P _ p m hp2 hL
  have hc := card_of_lieModel hm
  simp only [lieOrderNumerator, lieOrderDivisor] at hc
  norm_num at hc
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hlt := card_fixedSubgroup_lt hα
  have hd : Nat.card (fixedSubgroup α) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
  rw [hc] at hlt hd
  have h30 : Nat.card (fixedSubgroup α) ≤ 30 := le_half_of_dvd_of_lt hd hlt
  have h1 := card_fusionZStar_le_fixed P
  have h2 := sixty_le_card_of_psl2 hp2 hL
  omega

theorem noOddPSL2_L32
    {K : Type} [Group K] (hm : Blueprint.LieModel K .PSL 3 2 1) : NoOddPSL2 K := by
  intro α hα _ P _ p m hp2 hL
  have hc := card_of_lieModel hm
  simp only [lieOrderNumerator, lieOrderDivisor] at hc
  norm_num [Finset.prod_Icc_succ_top] at hc
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hlt := card_fixedSubgroup_lt hα
  have hdX : Nat.card (↥P ⧸ Open.fusionZStar ↥P) ∣ Nat.card K :=
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card P)).trans
      (Subgroup.card_subgroup_dvd_card _)
  have hX := card_fusionZStar_le_fixed P
  rw [hc] at hlt hdX
  have hq := card_mul_two_of_psl2 hp2 hL
  have h5 := five_le_of_psl2 hp2 hL
  have hodd : Odd (p ^ m) := ((admissible_of_lieModel hL).1.odd_of_ne_two hp2).pow
  set Q := p ^ m with hQ
  have hQ7 : Q ≤ 7 := by
    by_contra h8
    have := cube_mono (show 8 ≤ Q by omega)
    norm_num at this
    omega
  interval_cases Q
  · norm_num at hq
    have hc : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 60 := by omega
    rw [hc] at hdX
    norm_num at hdX
  · exact absurd hodd (by decide)
  · norm_num at hq
    omega

theorem ringEquiv_eq_one_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (σ : F ≃+* F) : σ = 1 := by
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl
    (by rw [hF, pow_one])
  have hinj : Function.Injective (ZMod.castHom (dvd_refl 2) F) := (ZMod.castHom _ F).injective
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl 2) F) :=
    (Function.Injective.bijective_of_nat_card_le hinj (by rw [hF, Nat.card_zmod]))
  refine RingEquiv.ext fun x => ?_
  show σ x = x
  obtain ⟨y, rfl⟩ := hbij.2 x
  have h := RingHom.ext_zmod (σ.toRingHom.comp (ZMod.castHom (dvd_refl 2) F))
    (ZMod.castHom (dvd_refl 2) F)
  exact congrArg (fun φ : ZMod 2 →+* F => φ y) h

theorem noOddPSL2_Sp62
    {K : Type} [Group K] (hm : Blueprint.LieModel K .PSp 3 2 1) : NoOddPSL2 K := by
  intro α _ hαo
  exfalso
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel (admissible_of_lieModel hm) hm
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hF
  have : NeZero 3 := ⟨by norm_num⟩
  have hgen := (automorphism_generation (K := F) (r := 3) le_rfl).1
  have hmem : MulAut.congr e α ∈ spSemilinearAutGroup 3 F := hgen ▸ Subgroup.mem_top _
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut hmem
  rw [ringEquiv_eq_one_of_card_two (by rw [hF, pow_one]) φ, map_one, mul_one] at hgφ
  have hin : MulAut.congr e α ∈ inner (StatedProj (StatedSp 3 F)) := hgφ ▸ spInner_mem_inner g
  exact hαo ((FixedFourGroup.congr_mem_inner_iff e α).mp hin)

theorem noOddPSL2_Sz8
    {K : Type} [Group K] (hm : Blueprint.LieModel K .twistedB2 0 2 3) : NoOddPSL2 K := by
  intro α hα hαo
  exfalso
  have hsz : Blueprint.SuzukiModel K 2 3 := by
    rcases hm with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  exact hαo (Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 3 (Or.inl hsz)
    α hα2)

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
