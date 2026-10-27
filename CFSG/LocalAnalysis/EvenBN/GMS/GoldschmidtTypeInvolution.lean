module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTypes
public import CFSG.CGT.T75M.SzOut
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open CFSG.Open CFSG.ComponentClassification.AschbacherTheorem3
open scoped MatrixGroups

theorem two_dvd_card_of_fusionBenderBorel {K : Type*} [Group K] [Finite K] {q k : ℕ}
    (hB : fusionBenderBorel K q k) (hq : 2 ∣ q) (hk : k ≠ 0) : 2 ∣ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hQ : Nat.card (Q : Subgroup K) = q ^ k := (hB Q).2.2.2.2
  exact (hq.trans (dvd_pow_self q hk)).trans (hQ ▸ Subgroup.card_subgroup_dvd_card _)

theorem card_le_of_fusionBenderBorel {K : Type} [Group K] [Finite K] {q k : ℕ}
    (hB : fusionBenderBorel K q k) (hq : 2 ≤ q) (W : Subgroup K) (hW : ∀ x ∈ W, x * x = 1) :
    Nat.card W ≤ q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 W := fun x => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hW x x.2)⟩
  obtain ⟨S, hWS⟩ := hWp.exists_le_sylow
  have hle : W ≤ (Subgroup.center (S : Subgroup K)).map (S : Subgroup K).subtype := by
    intro w hw
    refine ⟨⟨w, hWS hw⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
    have hw2 : w ^ 2 = 1 := by
      rw [pow_two]
      exact hW w hw
    exact Subtype.ext (FourEight.mem_center_of_sq_eq_one hB hq S (hWS hw) hw2 y y.2).symm
  calc Nat.card W ≤ Nat.card ((Subgroup.center (S : Subgroup K)).map (S : Subgroup K).subtype) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card (Subgroup.center (S : Subgroup K)) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    _ = q := (hB S).2.2.2.1

theorem goldschmidtSimpleType_cases {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.goldschmidtSimpleType X) :
    (∃ f : ℕ, 3 ≤ f ∧ Nonempty (X ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Nonempty (X ≃* Sz n)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (X ≃* PSU3 2 f)) ∨
    ∃ k : ℕ, Odd k ∧ (Nat.card X = 4 * k ∨ Nat.card X = 8 * k) := by
  rcases hX with hL | hS | hU | ⟨p, f, hp, hodd, hf, -, h8, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e⟩⟩
  · exact Or.inl hL
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hU))
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    obtain ⟨k, hk, hkeq⟩ := FourEight.psl2_card_two_part h8
    have h1 := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := p) (m := f) hp2
      (by omega)
    refine Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inl ?_⟩))
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p f)) = _
    rw [h1, mul_comm 2 f, pow_mul, hkeq]
  ·
    obtain ⟨k, hk, hkeq⟩ := FourEight.ordRee_two_part m
    exact Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inr (hcard.trans hkeq)⟩))
  ·
    refine Or.inr (Or.inr (Or.inr ⟨21945, by decide, Or.inr ?_⟩))
    rw [Nat.card_congr e.toEquiv, FourEight.card_goldschmidtJ1]

theorem two_dvd_card_of_goldschmidtSimpleType {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.goldschmidtSimpleType X) : 2 ∣ Nat.card X := by
  rcases goldschmidtSimpleType_cases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
      ⟨k, -, hcard | hcard⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
    exact two_dvd_card_of_fusionBenderBorel
      ((bender_psl2_borel_full f (by omega)).map_mulEquiv e.symm)
      (dvd_pow_self 2 (by omega)) one_ne_zero
  · have : Finite (Sz n) := Finite.of_equiv _ e.toEquiv
    exact two_dvd_card_of_fusionBenderBorel
      ((bender_suzuki_borel_full n hn).map_mulEquiv e.symm) (dvd_pow_self 2 (by omega))
      two_ne_zero
  · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    exact two_dvd_card_of_fusionBenderBorel
      ((bender_psu3_borel_full f hf).map_mulEquiv e.symm) (dvd_pow_self 2 (by omega))
      three_ne_zero
  · rw [hcard]
    exact Dvd.dvd.mul_right (by norm_num) k
  · rw [hcard]
    exact Dvd.dvd.mul_right (by norm_num) k

theorem statedClassicalModel_of_mulEquiv_psu3 {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f :=
  ⟨CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible f hf, GaloisField 2 (2 * f),
    inferInstance, inferInstance,
    by rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, Nat.mul_comm],
    ⟨e.trans (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm⟩⟩

theorem exists_fixed_elementary_of_psu3_outer {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) (α : MulAut X) (hαα : α * α = 1)
    (hαout : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ E : Subgroup X, (∀ x ∈ E, α x = x) ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα1 : α ≠ 1 := fun h1 => hαout ⟨1, by rw [h1, map_one]⟩
  have hαord : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hαα) hα1
  obtain ⟨K, _, _, F, -, -, -, -, hk, j, hjinj, hjfix, -⟩ :=
    even_unitary_three_outer_involution_perfect_fixed_rigidity hf
      (statedClassicalModel_of_mulEquiv_psu3 hf e) α hαord hαout
  let u := CFSG.GorensteinWalter.sl2UpperUnipotentHom
    (CFSG.ShultStronglyClosedTI.unitaryCoverFixedField F)
  have h2 : (2 : CFSG.ShultStronglyClosedTI.unitaryCoverFixedField F) = 0 := by
    have : Fintype (CFSG.ShultStronglyClosedTI.unitaryCoverFixedField F) := Fintype.ofFinite _
    have h := Nat.cast_card_eq_zero (CFSG.ShultStronglyClosedTI.unitaryCoverFixedField F)
    rw [Fintype.card_eq_nat_card, hk, Nat.cast_pow, Nat.cast_ofNat] at h
    exact (pow_eq_zero_iff (by omega)).mp h
  refine ⟨(j.comp u).range, ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact hjfix _ ⟨u s, rfl⟩
  · rintro _ ⟨s, rfl⟩
    have hs : s * s = 1 := by
      change Multiplicative.ofAdd (Multiplicative.toAdd s + Multiplicative.toAdd s) =
        Multiplicative.ofAdd 0
      rw [← two_mul, h2, zero_mul]
    rw [← map_mul, hs, map_one]
  · have hinj : Function.Injective (j.comp u) :=
      hjinj.comp CFSG.GorensteinWalter.sl2UpperUnipotentHom_injective
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hk]
    rfl

theorem exists_psl2_of_goldschmidtSimpleType_of_outer
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.goldschmidtSimpleType X) (h16 : 16 ∣ Nat.card X) {m : ℕ}
    (α : MulAut X) (hαα : α * α = 1) (hαout : α ∉ (MulAut.conj : X →* MulAut X).range)
    (hfix : ∀ E : Subgroup X, (∀ x ∈ E, α x = x) → (∀ x ∈ E, x * x = 1) → Nat.card E < m)
    (hW : ∃ W : Subgroup X, (∀ x ∈ W, x * x = 1) ∧ m ≤ Nat.card W) :
    ∃ f : ℕ, 3 ≤ f ∧ Nonempty (X ≃* PSL(2, GaloisField 2 f)) := by
  rcases goldschmidtSimpleType_cases hX with hL | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
      ⟨k, ⟨r, rfl⟩, hcard | hcard⟩
  · exact hL
  ·
    obtain ⟨g, hg⟩ := CFSG.CGT.T75M.exists_conj_of_mul_self_eq_one
      (CFSG.CGT.T75M.sz_outer_odd hn e) hαα
    exact absurd ⟨g, hg.symm⟩ hαout
  ·
    obtain ⟨E, hEfix, hE2, hEcard⟩ := exists_fixed_elementary_of_psu3_outer hf e α hαα hαout
    have hlt := hfix E hEfix hE2
    obtain ⟨W, hW2, hmW⟩ := hW
    have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    have hWle := card_le_of_fusionBenderBorel
      ((bender_psu3_borel_full f hf).map_mulEquiv e.symm)
      (le_self_pow₀ (by norm_num) (by omega)) W hW2
    omega
  · rw [hcard] at h16
    omega
  · rw [hcard] at h16
    omega

theorem sylow_facts_of_psl2 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) (Q : Sylow 2 X) :
    Nat.card (Q : Subgroup X) = 2 ^ f ∧ ∀ x ∈ (Q : Subgroup X), x * x = 1 := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
  obtain ⟨-, -, hZ2, hZcard, hQcard⟩ := (bender_psl2_borel_full f hf).map_mulEquiv e.symm Q
  rw [pow_one] at hQcard
  refine ⟨hQcard, fun x hx => ?_⟩
  have htop : Subgroup.center (Q : Subgroup X) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (hZcard.trans hQcard.symm)
  have hmem : (⟨x, hx⟩ : (Q : Subgroup X)) ∈ Subgroup.center (Q : Subgroup X) :=
    htop ▸ Subgroup.mem_top _
  have h2 := hZ2 _ hmem
  rw [pow_two] at h2
  exact congrArg Subtype.val h2

end CFSG.LocalAnalysis.EvenBN.GMS
