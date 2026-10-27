module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS7
public import CFSG.ClassicalInvolution.Asc77.AscFusionS2

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem exists_centralized_order_four_of_chart_fixed {J : Subgroup G}
    (e : (↥J ⧸ classicalInvolutionOddCore ↥J) ≃* SL(2, F)) (hodd : Odd (Nat.card F)) {z : G}
    (hz2 : z * z = 1) (hzN : z ∈ Subgroup.normalizer (J : Set G)) {g : SL(2, F)}
    (hg2 : g * g = -1) (hfix : chartAut e (J.normalizerMonoidHom ⟨z, hzN⟩) g = g) :
    ∃ x ∈ J, orderOf x = 4 ∧ z * x = x * z := by
  classical
  set σ : MulAut ↥J := J.normalizerMonoidHom ⟨z, hzN⟩ with hσ
  have hσapp : ∀ x : ↥J, ((σ x : ↥J) : G) = z * (x : G) * z⁻¹ := fun x => rfl
  have hσσ : ∀ x : ↥J, σ (σ x) = x := fun x => by
    apply Subtype.ext
    rw [hσapp, hσapp]
    calc z * (z * (x : G) * z⁻¹) * z⁻¹ = (z * z) * (x : G) * (z * z)⁻¹ := by group
      _ = x := by rw [hz2]; group
  obtain ⟨y, rfl⟩ := chartMap_surjective e g
  set φ : ↥J →* SL(2, F) := chartMap e with hφ
  have hfy : φ (σ y) = φ y := by
    rw [← chartAut_apply e σ y]
    exact hfix
  let Φ := {x : ↥J // φ x = φ y}
  have hψ : ∀ x : Φ, φ (σ x.1) = φ y := fun x => by
    rw [← chartAut_apply e σ x.1, x.2, chartAut_apply e σ y]
    exact hfy
  let ψ : Φ → Φ := fun x => ⟨σ x.1, hψ x⟩
  have hψi : Function.Involutive ψ := fun x => Subtype.ext (hσσ x.1)
  have hker : φ.ker = classicalInvolutionOddCore ↥J := by
    ext x
    rw [MonoidHom.mem_ker]
    exact chartMap_eq_one_iff e x
  have hΦodd : Odd (Nat.card Φ) := by
    have h1 : Nat.card Φ = Nat.card φ.ker := Nat.card_congr (φ.fiberEquivKer y)
    have h2 : Nat.card φ.ker = Nat.card (classicalInvolutionOddCore ↥J) := by
      rw [hker]
    rw [h1, h2]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥J
  obtain ⟨x₀, hx₀⟩ := exists_fixedPoint_of_involutive hΦodd hψi
  have hx₀σ : σ x₀.1 = x₀.1 := congrArg Subtype.val hx₀
  set N : ℕ := Nat.card (classicalInvolutionOddCore ↥J) with hN
  have hNodd : Odd N := CFSG.ComponentClassification.OddCore.odd_card ↥J
  obtain ⟨m, hm⟩ := hNodd
  have hcc : (-1 : SL(2, F)) * (-1) = 1 := by
    apply Subtype.ext
    simp
  have hneg : ∀ k : ℕ, (-1 : SL(2, F)) ^ (2 * k + 1) = -1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (-1 : SL(2, F)) ^ (2 * (k + 1) + 1) = (-1) ^ (2 * k + 1) * ((-1) * (-1)) := by
            rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, pow_two]
        _ = -1 := by rw [ih, hcc, mul_one]
  have hφx₀ : φ x₀.1 = φ y := x₀.2
  have hx4 : x₀.1 ^ 4 ∈ classicalInvolutionOddCore ↥J := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hφx₀]
    calc (φ y) ^ 4 = (φ y * φ y) * (φ y * φ y) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [hg2, hcc]
  have hx4N : (x₀.1 ^ 4) ^ N = 1 := by
    have := pow_card_eq_one' (G := classicalInvolutionOddCore ↥J) (x := ⟨x₀.1 ^ 4, hx4⟩)
    exact congrArg Subtype.val this
  set x₁ : ↥J := x₀.1 ^ N with hx₁
  have h4 : x₁ ^ 4 = 1 := by
    calc x₁ ^ 4 = (x₀.1 ^ 4) ^ N := by rw [hx₁, ← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := hx4N
  have hφx₁ : φ x₁ * φ x₁ = -1 := by
    have e1 : φ x₁ = (φ y) ^ N := by rw [hx₁, map_pow, hφx₀]
    calc φ x₁ * φ x₁ = (φ y * φ y) ^ N := by
          rw [e1, ← pow_two, ← pow_mul, mul_comm, pow_mul, pow_two]
      _ = (-1) ^ (2 * m + 1) := by rw [hg2, hm]
      _ = -1 := hneg m
  have h2 : ¬ x₁ ^ 2 ^ 1 = 1 := by
    intro h
    have h' : x₁ * x₁ = 1 := by simpa [pow_two] using h
    have := congrArg φ h'
    rw [map_mul, hφx₁, map_one] at this
    exact sl2_neg_one_ne_one hodd this
  have h4' : x₁ ^ 2 ^ (1 + 1) = 1 := by simpa using h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x₁ = 4 := by
    have := orderOf_eq_prime_pow h2 h4'
    simpa using this
  refine ⟨(x₁ : G), x₁.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hord
  · have h1 : z * (x₀.1 : G) * z⁻¹ = (x₀.1 : G) := by
      have := hx₀σ
      rw [← hσapp]
      exact congrArg Subtype.val this
    have hc : Commute z (x₀.1 : G) := by
      show z * (x₀.1 : G) = (x₀.1 : G) * z
      calc z * (x₀.1 : G) = (z * (x₀.1 : G) * z⁻¹) * z := by group
        _ = (x₀.1 : G) * z := by rw [h1]
    have hc' := hc.pow_right N
    rw [hx₁]
    exact hc'.eq

section Perfect

variable {p f : ℕ} [Fact p.Prime]

theorem perfect_trivial_of_bad (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {J : Subgroup G} {t : G}
    (hJ : IsClassicalMember p f J t) {z : G} (hz2 : z * z = 1)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hbad : ∀ x ∈ J, orderOf x = 4 → z * x = x * z → False)
    {L : Subgroup G} (hLperf : ⁅L, L⁆ = L) (hLN : L ≤ Subgroup.normalizer (J : Set G))
    (hLz : ∀ x ∈ L, z * x = x * z)
    (hinner : ∀ x ∈ L, ∃ b ∈ J, ∀ y ∈ J, x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf J) :
    ∀ x ∈ L, ∀ y ∈ J, ⁅x, y⁆ ∈ oddCoreOf J := by
  classical
  obtain ⟨e⟩ := hJ.nonempty_equiv
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  have hF : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  set ζ : MulAut SL(2, GaloisField p f) := chartAut e (J.normalizerMonoidHom ⟨z, hzN⟩) with hζ
  have hbadζ : ∀ g : SL(2, GaloisField p f), g * g = -1 → ζ g ≠ g := by
    intro g hg hfix
    obtain ⟨x, hxJ, hx4, hxz⟩ :=
      exists_centralized_order_four_of_chart_fixed e hodd hz2 hzN hg hfix
    exact hbad x hxJ hx4 hxz
  set Θ : L →* MulAut SL(2, GaloisField p f) := actSL e L hLN with hΘ
  have hcc : (-1 : SL(2, GaloisField p f)) * (-1) = 1 := by
    apply Subtype.ext
    simp
  have hrange : ∀ x : L, ∃ (b : G) (hb : b ∈ J),
      (∀ y ∈ J, (x : G) * y * (x : G)⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf J) ∧
        chartMap e ⟨b, hb⟩ ∈ signFix ζ := by
    intro x
    obtain ⟨b, hb, hbx⟩ := hinner x x.2
    refine ⟨b, hb, hbx, ?_⟩
    have hΘx : Θ x = MulAut.conj (chartMap e ⟨b, hb⟩) := actSL_eq_conj e L hLN x.2 hb hbx
    set h := chartMap e ⟨b, hb⟩ with hh
    have hcomm : Θ x * ζ = ζ * Θ x := by
      have h1 : (J.normalizerMonoidHom ⟨(x : G), hLN x.2⟩) *
          (J.normalizerMonoidHom ⟨z, hzN⟩) =
          (J.normalizerMonoidHom ⟨z, hzN⟩) * (J.normalizerMonoidHom ⟨(x : G), hLN x.2⟩) := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (hLz x x.2).symm
      have := congrArg (chartHom e) h1
      rw [map_mul, map_mul] at this
      exact this
    rw [hΘx] at hcomm
    have hc : (ζ h)⁻¹ * h ∈ Subgroup.center SL(2, GaloisField p f) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨s', rfl⟩ := ζ.surjective s
      have h1 := DFunLike.congr_fun hcomm s'
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1
      calc ζ s' * ((ζ h)⁻¹ * h) = (ζ h)⁻¹ * (ζ h * ζ s' * (ζ h)⁻¹) * h := by group
        _ = (ζ h)⁻¹ * (h * ζ s' * h⁻¹) * h := by rw [h1]
        _ = ((ζ h)⁻¹ * h) * ζ s' := by group
    rw [mem_center_sl2_iff] at hc
    rcases hc with h1 | h1
    · left
      exact inv_mul_eq_one.mp h1
    · right
      have h2 : h = ζ h * (-1) := inv_mul_eq_iff_eq_mul.mp h1
      calc ζ h = ζ h * ((-1) * (-1)) := by rw [hcc, mul_one]
        _ = (ζ h * (-1)) * (-1) := by group
        _ = h * (-1) := by rw [← h2]
        _ = (-1) * h := (sl2_neg_one_central h).symm
  set ψ : ↥(signFix ζ) →* MulAut SL(2, GaloisField p f) :=
    (MulAut.conj : SL(2, GaloisField p f) →* MulAut SL(2, GaloisField p f)).comp
      (signFix ζ).subtype with hψ
  have hsolv : Group.IsSolvable ↥(signFix ζ) := signFix_isSolvable hF ζ hbadζ
  have hsolvψ : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hle : Θ.range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, hb, hbx, hmem⟩ := hrange x
    exact ⟨⟨chartMap e ⟨b, hb⟩, hmem⟩, (actSL_eq_conj e L hLN x.2 hb hbx).symm⟩
  have hsolvΘ : Group.IsSolvable ↥Θ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
  have hperfΘ : Group.IsPerfect ↥Θ.range :=
    Group.IsPerfect.ofSurjective (f := Θ.rangeRestrict) Θ.rangeRestrict_surjective
  have hsub : Subsingleton ↥Θ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥Θ.range hsolvΘ
  intro x hx y hy
  obtain ⟨b, hb, hbx, -⟩ := hrange ⟨x, hx⟩
  have hΘ1 : Θ ⟨x, hx⟩ = 1 := by
    have : (⟨Θ ⟨x, hx⟩, ⟨_, rfl⟩⟩ : ↥Θ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have hΘx : Θ ⟨x, hx⟩ = MulAut.conj (chartMap e ⟨b, hb⟩) :=
    actSL_eq_conj e L hLN hx hb hbx
  have hcen : chartMap e ⟨b, hb⟩ ∈ Subgroup.center SL(2, GaloisField p f) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have := DFunLike.congr_fun (hΘx.symm.trans hΘ1) s
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc s * chartMap e ⟨b, hb⟩ = (chartMap e ⟨b, hb⟩ * s * (chartMap e ⟨b, hb⟩)⁻¹) *
          chartMap e ⟨b, hb⟩ := by rw [this]
      _ = chartMap e ⟨b, hb⟩ * s := by group
  have hb1 := (comm_mem_oddCoreOf_iff_central e hb).mpr hcen y hy
  have e1 : ⁅x, y⁆ = (x * y * x⁻¹ * (b * y * b⁻¹)⁻¹) * ⁅b, y⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact (oddCoreOf J).mul_mem (hbx y hy) hb1

end Perfect

end CFSG.ClassicalInvolution.Asc77.AscFusion
