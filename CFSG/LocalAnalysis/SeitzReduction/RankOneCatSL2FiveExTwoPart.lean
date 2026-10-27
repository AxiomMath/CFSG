module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

@[expose] def InvolutionTwoPart (J : Type) [Group J] (k : ℕ) : Prop :=
  ∀ α : MulAut J, orderOf α = 2 → 2 ^ k ∣ Nat.card (fixedSubgroup α)

@[expose] def ExcTwoPartInput (t : StatedLieTag) (p f k : ℕ) : Prop :=
  ∀ (J : Type) [Group J], LieModel J t 0 p f → InvolutionTwoPart J k

theorem InvolutionTwoPart.of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    {k : ℕ} (h : InvolutionTwoPart J' k) : InvolutionTwoPart J k := by
  intro α hα
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  rw [Nat.card_congr (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e α).toEquiv]
  exact h _ hβ

namespace FiveEx

theorem eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨r, rfl⟩ := hq
  have h : (2 * r + 1) ^ 2 - 1 = 4 * (r * (r + 1)) := Nat.sub_eq_of_eq_add (by ring)
  rw [h]
  obtain ⟨s, hs⟩ := Nat.even_mul_succ_self r
  rw [hs]
  exact ⟨s, by ring⟩

theorem eight_dvd_pow_two_mul_sub_one {q : ℕ} (hq : Odd q) (m : ℕ) : 8 ∣ q ^ (2 * m) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 m
  rw [one_pow, ← pow_mul] at h
  exact (eight_dvd_sq_sub_one hq).trans h

theorem mul_dvd_mul_mul_mul (M A B : ℕ) : A * B ∣ M * A * B :=
  Nat.mul_dvd_mul (Nat.dvd_mul_left A M) dvd_rfl

theorem mul_dvd_mul_mul_mul_mul (M A B C : ℕ) : A * C ∣ M * A * B * C :=
  Nat.mul_dvd_mul ((Nat.dvd_mul_left A M).mul_right B) dvd_rfl

theorem mul_mul_dvd_mul_mul_mul_mul (M A B C : ℕ) : A * B * C ∣ M * A * B * C :=
  Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.dvd_mul_left A M) dvd_rfl) dvd_rfl

theorem two_pow_six_dvd_of_mul_eq {c d N : ℕ} (hN : c * d = N) (h64 : 2 ^ 6 ∣ N)
    (hd : Nat.Coprime (2 ^ 6) d) : 2 ^ 6 ∣ c :=
  hd.dvd_of_dvd_mul_right (hN ▸ h64)

theorem coprime_two_pow_six_gcd_three (n : ℕ) : Nat.Coprime (2 ^ 6) (Nat.gcd 3 n) :=
  Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 n) (by norm_num)

theorem two_pow_six_dvd_mul {A B : ℕ} (hA : 8 ∣ A) (hB : 8 ∣ B) : 2 ^ 6 ∣ A * B := by
  have h := Nat.mul_dvd_mul hA hB
  norm_num at h ⊢
  exact h

end FiveEx

section Orders

open FiveEx in
theorem two_pow_six_dvd_card_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (hp2 : p ≠ 2) (h : LieModel X t 0 p f) :
    2 ^ 6 ∣ Nat.card X := by
  have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel h
  have hq : Odd (p ^ f) := (hadm.1.eq_two_or_odd'.resolve_left hp2).pow
  have hcard := SeitzReduction.CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm h
    (by rintro rfl; exact absurd ht (by decide))
  have h2 : 8 ∣ (p ^ f) ^ 2 - 1 := eight_dvd_pow_two_mul_sub_one hq 1
  have h6 : 8 ∣ (p ^ f) ^ 6 - 1 := eight_dvd_pow_two_mul_sub_one hq 3
  have h8 : 8 ∣ (p ^ f) ^ 8 - 1 := eight_dvd_pow_two_mul_sub_one hq 4
  have hc1 : Nat.Coprime (2 ^ 6) 1 := Nat.coprime_one_right _
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [lieOrderNumerator, lieOrderDivisor] at hcard
    exact two_pow_six_dvd_of_mul_eq hcard
      ((two_pow_six_dvd_mul h6 h2).trans (mul_dvd_mul_mul_mul _ _ _)) hc1
  · simp only [lieOrderNumerator, lieOrderDivisor] at hcard
    exact two_pow_six_dvd_of_mul_eq hcard
      ((two_pow_six_dvd_mul h6 h2).trans (mul_dvd_mul_mul_mul _ _ _)) hc1
  · simp only [lieOrderNumerator, lieOrderDivisor] at hcard
    exact two_pow_six_dvd_of_mul_eq hcard
      ((two_pow_six_dvd_mul h6 h2).trans (mul_dvd_mul_mul_mul_mul _ _ _ _))
      (coprime_two_pow_six_gcd_three _)
  · simp only [lieOrderNumerator, lieOrderDivisor] at hcard
    have hg : Nat.gcd 2 (p ^ f - 1) = 2 := Nat.gcd_eq_left (by
      obtain ⟨r, hr⟩ := hq
      exact ⟨r, by omega⟩)
    rw [hg] at hcard
    have h512 : 2 ^ 7 ∣ Nat.card X * 2 := by
      rw [hcard]
      have h3 := Nat.mul_dvd_mul (Nat.mul_dvd_mul h8 h6) h2
      exact (show 2 ^ 7 ∣ 8 * 8 * 8 by norm_num).trans
        (h3.trans (mul_mul_dvd_mul_mul_mul_mul _ _ _ _))
    rw [pow_succ] at h512
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h512
  · simp only [lieOrderNumerator, lieOrderDivisor] at hcard
    exact two_pow_six_dvd_of_mul_eq hcard
      ((two_pow_six_dvd_mul h8 h2).trans (mul_dvd_mul_mul_mul _ _ _)) hc1
  · simp only [lieOrderNumerator, lieOrderDivisor] at hcard
    exact two_pow_six_dvd_of_mul_eq hcard
      ((two_pow_six_dvd_mul h6 h2).trans (mul_dvd_mul_mul_mul_mul _ _ _ _))
      (coprime_two_pow_six_gcd_three _)
  · simp only [lieOrderNumerator, lieOrderDivisor] at hcard
    exact two_pow_six_dvd_of_mul_eq hcard
      ((two_pow_six_dvd_mul h6 h2).trans (mul_dvd_mul_mul_mul _ _ _)) hc1

end Orders

section Toral

namespace FiveEx

theorem cartanChar_prod_zpow_eq_pow {τ : Tag} {K : Type} [Field K]
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {d : ℕ} (hB : B * τ.cartan = (d : ℤ) • 1)
    (a : Fin τ.rank → Kˣ) : cartanChar (fun i => ∏ j, a j ^ B j i) = a ^ d := by
  funext l
  calc ∏ i, (∏ j, a j ^ B j i) ^ τ.cartan i l
      = ∏ i, ∏ j, a j ^ (B j i * τ.cartan i l) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    _ = ∏ j, ∏ i, a j ^ (B j i * τ.cartan i l) := Finset.prod_comm
    _ = ∏ j, a j ^ ((B * τ.cartan) j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, Finset.prod_zpow_eq_zpow_sum]
    _ = (a ^ d) l := by
        rw [hB]
        simp [Matrix.one_apply]

theorem rootDiagUnit_pow_mem_torusGroup {τ : Tag} {K : Type} [Field K]
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {d : ℕ} (hB : B * τ.cartan = (d : ℤ) • 1)
    (a : Fin τ.rank → Kˣ) : rootDiagUnit τ (a ^ d) ∈ torusGroup τ K := by
  rw [← cartanChar_prod_zpow_eq_pow hB a, ← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup i _

end FiveEx

open FiveEx in
theorem two_pow_dvd_card_toralCentralizer {τ : Tag} {K : Type} [Field K] [Finite K]
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {d : ℕ} (hB : B * τ.cartan = (d : ℤ) • 1)
    (hd : Odd d) {s : ℕ} (hs : 2 ^ s ∣ Nat.card K - 1) (b : Fin τ.rank → Kˣ) :
    2 ^ (s * τ.rank) ∣ Nat.card (toralCentralizer τ K b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := Sylow.exists_subgroup_card_pow_prime (G := Kˣ) 2 (n := s)
    (by rw [Nat.card_units]; exact hs)
  let φ : (Fin τ.rank → μ) →* ModGL τ K :=
    (rootDiagUnitHom τ K).comp (MonoidHom.compLeft μ.subtype _)
  have hφ : Function.Injective φ := fun x y hxy => by
    have h1 : (fun i => (x i : Kˣ)) = fun i => (y i : Kˣ) := rootDiagUnit_injective hxy
    funext i
    exact Subtype.ext (congrFun h1 i)
  have hcardG : Nat.card (Fin τ.rank → μ) = 2 ^ (s * τ.rank) := by
    rw [Nat.card_fun, hμ, Nat.card_fin, ← pow_mul]
  have hle : φ.range ≤ toralCentralizer τ K b := by
    rintro _ ⟨x, rfl⟩
    refine torusGroup_le_toralCentralizer b ?_
    have hcop : Nat.Coprime (Nat.card (Fin τ.rank → μ)) d := by
      rw [hcardG]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hd)
    obtain ⟨y, hy⟩ := (powCoprime hcop).surjective x
    rw [powCoprime_apply] at hy
    rw [← hy, map_pow]
    have hφy : φ y = rootDiagUnit τ (fun i => (y i : Kˣ)) := rfl
    have hpow : rootDiagUnit τ ((fun i => (y i : Kˣ)) ^ d) =
        rootDiagUnit τ (fun i => (y i : Kˣ)) ^ d :=
      map_pow (rootDiagUnitHom τ K) _ d
    rw [hφy, ← hpow]
    exact rootDiagUnit_pow_mem_torusGroup hB _
  have h1 : Nat.card φ.range = 2 ^ (s * τ.rank) := by
    rw [← hcardG]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
  rw [← h1]
  exact Subgroup.card_dvd_of_le hle

theorem two_pow_dvd_card_fixed_innerDiag {τ : Tag} {K : Type} [Field K] [Finite K]
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hKodd : Odd (Nat.card K))
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {d : ℕ} (hB : B * τ.cartan = (d : ℤ) • 1)
    (hd : Odd d) {s : ℕ} (hs : 2 ^ s ∣ Nat.card K - 1)
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) : 2 ^ (s * τ.rank) ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨b, -, -, ⟨Θ⟩⟩ :=
    ComponentClassification.CatLeafProof.exists_toralCentralizer_equiv_of_innerDiag hτ hKodd hαg hα
  rw [Nat.card_congr Θ.toEquiv]
  exact two_pow_dvd_card_toralCentralizer hB hd hs b

namespace FiveEx

theorem card_SL2_eq {K : Type} [Field K] [Finite K] :
    Nat.card (SL2 K) = (Nat.card K ^ 2 - 1) * Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 := Matrix.card_SL_mul_card_units (n := Fin 2) (R := K)
  rw [Matrix.card_GL_field 2, Nat.card_units, Fin.prod_univ_two, ← Nat.card_eq_fintype_card] at h1
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h1
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq1 : 0 < Nat.card K - 1 := by omega
  have h2 : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
    rw [sq, Nat.mul_sub_one]
  apply Nat.eq_of_mul_eq_mul_right hq1
  rw [h1, h2]
  ring

end FiveEx

open FiveEx in
theorem two_pow_dvd_card_toralCentralizer_G2 {K : Type} [Field K] [Finite K]
    (hKodd : Odd (Nat.card K)) {s : ℕ} (hs : 2 ^ s ∣ Nat.card K ^ 2 - 1)
    (b : Fin Tag.G2.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    2 ^ (2 * s - 1) ∣ Nat.card (toralCentralizer .G2 K b) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, hcases, hstruct, -⟩ := odd_G2_toral_involution_fixed_p_components K hKodd b hb
  obtain ⟨α₀, β₀, hc⟩ : ∃ α₀ β₀ : Fin Tag.G2.rank → ℤ,
      (b = ![-1, 1] ∧ α₀ = ![0, 1] ∧ β₀ = ![2, 3]) ∨
        (b = ![1, -1] ∧ α₀ = ![1, 0] ∧ β₀ = ![1, 2]) ∨
          (b = ![-1, -1] ∧ α₀ = ![1, 1] ∧ β₀ = ![1, 3]) := by
    rcases hcases with h | h | h | h
    · exact absurd h hb1
    · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩)⟩
    · exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
  obtain ⟨-, -, -, -, ⟨μ, hμ1, hμ2, hμs, hμk⟩, ⟨eα⟩, ⟨eβ⟩, hSX, -, -, -⟩ := hstruct α₀ β₀ hc
  have hkr := Subgroup.card_ker_mul_card_range μ
  rw [MonoidHom.range_eq_top.2 hμs, Subgroup.card_top, Nat.card_prod,
    ← Nat.card_congr eα.toEquiv, ← Nat.card_congr eβ.toEquiv] at hkr
  have key : ∀ u : μ.ker, (u.1.2 : ModGL Tag.G2 K) = ((u.1.1 : ModGL Tag.G2 K))⁻¹ := by
    intro u
    have hu : μ u.1 = 1 := u.2
    have hsplit : u.1 = (u.1.1, 1) * (1, u.1.2) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [hsplit, map_mul] at hu
    have hu' := congrArg (fun z => ((z : ↥(rootSpan Tag.G2 K (rootCharKernel b))) :
      ModGL Tag.G2 K)) hu
    simp only [Subgroup.coe_mul, Subgroup.coe_one, hμ1, hμ2] at hu'
    exact eq_inv_of_mul_eq_one_right hu'
  have hker : Nat.card μ.ker ≤ 2 := by
    let ι : μ.ker → center ↥(rootSubgroup Tag.G2 K α₀ ⊔ rootSubgroup Tag.G2 K (-α₀)) :=
      fun u => ⟨u.1.1, (hμk u.1 u.2).1⟩
    have hι : Function.Injective ι := by
      intro u v huv
      have h1 : u.1.1 = v.1.1 := congrArg Subtype.val huv
      refine Subtype.ext (Prod.ext h1 (Subtype.ext ?_))
      rw [key u, key v, h1]
    calc Nat.card μ.ker ≤ Nat.card (center ↥(rootSubgroup Tag.G2 K α₀ ⊔
          rootSubgroup Tag.G2 K (-α₀))) := Nat.card_le_card_of_injective ι hι
      _ = Nat.card (center (SL2 K)) := (Nat.card_congr (Subgroup.centerCongr eα).toEquiv).symm
      _ ≤ 2 := by
        rw [Nat.card_congr Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.toEquiv]
        simp only [Fintype.card_fin]
        exact card_rootsOfUnity K 2
  have hker1 : 1 ≤ Nat.card μ.ker := Nat.card_pos
  have hk2 : Nat.card μ.ker ∣ 2 := by
    rcases (by omega : Nat.card μ.ker = 1 ∨ Nat.card μ.ker = 2) with h | h
    · rw [h]
      exact one_dvd 2
    · rw [h]
  have h8 : 2 ^ s ∣ Nat.card (SL2 K) := by
    rw [card_SL2_eq]
    exact hs.mul_right _
  have h64 : 2 ^ (2 * s) ∣ Nat.card μ.ker * Nat.card (rootSpan Tag.G2 K (rootCharKernel b)) := by
    rw [hkr, two_mul, pow_add]
    exact Nat.mul_dvd_mul h8 h8
  have hS5 : 2 ^ (2 * s - 1) ∣ Nat.card (rootSpan Tag.G2 K (rootCharKernel b)) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · exact one_dvd _
    have h2 := h64.trans (Nat.mul_dvd_mul_right hk2 _)
    rw [show 2 * s = 2 * s - 1 + 1 by omega, pow_succ, mul_comm] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  exact hS5.trans (Subgroup.card_dvd_of_le hSX)

end Toral

section Field

theorem two_pow_six_dvd_card_fixed_field {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K}
    {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) : 2 ^ 6 ∣ Nat.card (fixedSubgroup α) := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (fixedSubgroup β).map (adjointGroup τ K).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ K) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(fixedSubgroup β) ≃* ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  obtain ⟨-, -, -, hJΓ, -, -, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K δ
  have hdvd : Nat.card (adjointGroup τ (fixSubfield δ)) ∣ Nat.card (fixedSubgroup α) := by
    have hc : Nat.card (fixedSubgroup α) = Nat.card (entrywiseFixedGroup τ δ) :=
      Nat.card_congr (e₁.trans e₂).toEquiv
    rw [hc]
    have h1 : Nat.card (fixedFieldImage τ δ) = Nat.card (adjointGroup τ (fixSubfield δ)) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [← h1]
    exact Subgroup.card_dvd_of_le hJΓ
  have hk := ComponentClassification.CatLeafProof.card_fixSubfield_of_sq_pow hp he hKe δ hδ
  have h3 := ComponentClassification.CatLeafProof.three_le_pow_of_odd_prime hp hp2 he
  have hadm : StatedLieAdmissible t 0 p e := by
    rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨hp, he, rfl, h3⟩
    all_goals exact ⟨hp, he, rfl⟩
  have ht : t ∈ chevalleyExceptionalTags := by
    rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hL := ComponentClassification.CatLeafProof.lieModel_centralQuotient_of_mulEquiv_adjointGroup
    htτ hadm hk (MulEquiv.refl _)
  exact ((two_pow_six_dvd_card_of_lieModel ht hp2 hL).trans
    (Subgroup.card_quotient_dvd_card _)).trans hdvd

theorem excTwoPartInput_of_adjointGroup {t : StatedLieTag} {τ : Tag}
    (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f)) {p f k : ℕ}
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      InvolutionTwoPart (adjointGroup τ K) k) : ExcTwoPartInput t p f k := by
  intro J _ hJ
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hJ))
  exact (h F hF).of_mulEquiv e

theorem involutionTwoPart_F4_E8_G2_of_innerDiag {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8 ∨ τ = .G2)
    {K : Type} [Field K] [Finite K] {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : τ = .G2 → p ≠ 3) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hk : k ≤ 6)
    (hinner : ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) =
        (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) →
      orderOf α = 2 → 2 ^ k ∣ Nat.card (fixedSubgroup α)) :
    InvolutionTwoPart (adjointGroup τ K) k := by
  intro β hβ
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hchar := ComponentClassification.CatLeafProof.ringChar_eq_of_card hp hf hK
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hchar ▸ hp3 h⟩)
  rcases LieType.AlgebraicGroups.odd_F4_E8_G2_involution_inner_or_quadratic hτ' hKodd hβ2 with
    ⟨g, a, hβg⟩ | ⟨q, e, hq, he, hKe, δ, hδ, g, a, hβg⟩
  · exact hinner β g a hβg hβ
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    refine (pow_dvd_pow 2 hk).trans ?_
    rcases hτ with rfl | rfl | rfl
    · exact two_pow_six_dvd_card_fixed_field (t := .F4) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hq hp2 he
        hKe δ hδ hβg hβ2
    · exact two_pow_six_dvd_card_fixed_field (t := .E8)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) hq hp2 he hKe δ hδ hβg hβ2
    · exact two_pow_six_dvd_card_fixed_field (t := .G2) (Or.inl ⟨rfl, rfl⟩) hq hp2 he hKe δ hδ
        hβg hβ2

end Field

section Families

namespace FiveEx

@[expose] def bE8 : Matrix (Fin (Tag.rank .E8)) (Fin (Tag.rank .E8)) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

theorem bE8_mul_cartan : bE8 * Tag.cartan .E8 = ((1 : ℕ) : ℤ) • 1 := by
  decide +kernel

@[expose] def bE6 : Matrix (Fin (Tag.rank .E6)) (Fin (Tag.rank .E6)) ℤ :=
  !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

theorem bE6_mul_cartan : bE6 * Tag.cartan .E6 = ((3 : ℕ) : ℤ) • 1 := by
  decide +kernel

theorem one_le_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hK : Nat.card K = p ^ f) :
    1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · rw [h0, pow_zero] at hK
    exact absurd hK (Finite.one_lt_card).ne'
  · exact h0

theorem odd_card {K : Type} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Odd (Nat.card K) := by
  rw [hK]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem two_dvd_sub_one {q : ℕ} (hq : Odd q) : 2 ^ 1 ∣ q - 1 := by
  obtain ⟨r, rfl⟩ := hq
  exact ⟨r, by omega⟩

end FiveEx

open FiveEx in
theorem excTwoPartInput_G2_of_pow {p f k s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hs : 2 ^ s ∣ (p ^ f) ^ 2 - 1) (hks : k ≤ 2 * s - 1) (hk : k ≤ 6) :
    ExcTwoPartInput .G2 p f k := by
  refine excTwoPartInput_of_adjointGroup (τ := .G2) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ hK => ?_
  have hKodd := odd_card hp hp2 hK
  refine involutionTwoPart_F4_E8_G2_of_innerDiag (Or.inr (Or.inr rfl)) hp hp2 (fun _ => hp3)
    (one_le_of_card hK) hK hk fun α g a hαg hα => ?_
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα
    exact absurd hα (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    ComponentClassification.CatLeafProof.exists_toralCentralizer_equiv_of_innerDiag
      (Or.inl rfl) hKodd hαg hα2
  rw [Nat.card_congr Θ.toEquiv]
  exact (pow_dvd_pow 2 hks).trans
    (two_pow_dvd_card_toralCentralizer_G2 hKodd (hK ▸ hs) b hb (hb1 hα1))

open FiveEx in
theorem excTwoPartInput_G2 {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hk : k ≤ 5) :
    ExcTwoPartInput .G2 p f k :=
  excTwoPartInput_G2_of_pow (s := 3) hp hp2 hp3
    (eight_dvd_sq_sub_one ((hp.eq_two_or_odd'.resolve_left hp2).pow)) (by omega) (by omega)

open FiveEx in
theorem excTwoPartInput_F4 {p f k s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : 2 ^ s ∣ p ^ f - 1)
    (hks : k ≤ 4 * s) (hk : k ≤ 6) : ExcTwoPartInput .F4 p f k := by
  refine excTwoPartInput_of_adjointGroup (τ := .F4) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ hK => ?_
  have hKodd := odd_card hp hp2 hK
  refine involutionTwoPart_F4_E8_G2_of_innerDiag (Or.inl rfl) hp hp2
    (fun h => absurd h (by decide)) (one_le_of_card hK) hK hk fun α g a hαg hα => ?_
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨B, hB, -⟩ := (G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K).1
  have hB' : B * Tag.cartan .F4 = ((1 : ℕ) : ℤ) • 1 := by rw [hB]; simp
  have h := two_pow_dvd_card_fixed_innerDiag (Or.inr (Or.inl rfl)) hKodd hB' odd_one
    (hK ▸ hs) hαg hα2
  exact (pow_dvd_pow 2 (by change k ≤ s * 4; omega)).trans h

open FiveEx in
theorem excTwoPartInput_E8 {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≤ 6) :
    ExcTwoPartInput .E8 p f k := by
  refine excTwoPartInput_of_adjointGroup (τ := .E8) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ hK => ?_
  have hKodd := odd_card hp hp2 hK
  refine involutionTwoPart_F4_E8_G2_of_innerDiag (Or.inr (Or.inl rfl)) hp hp2
    (fun h => absurd h (by decide)) (one_le_of_card hK) hK hk fun α g a hαg hα => ?_
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  have h := two_pow_dvd_card_fixed_innerDiag (Or.inr (Or.inr (Or.inr rfl))) hKodd
    bE8_mul_cartan odd_one (two_dvd_sub_one hKodd) hαg hα2
  exact (pow_dvd_pow 2 (by change k ≤ 1 * 8; omega)).trans h

end Families

end CFSG.SeitzReduction.RankOne
