module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsModel

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Defs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def StdPairImage {X : Type} [Group X] (U V : Subgroup X) : Prop :=
  (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p f) W U V) ∨
    ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W U V

@[expose] def PairKG2 {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (i : Fin D.card) : Prop :=
  ∀ R₀ ∈ compFund D i, ∀ Rβ ∈ compFund D i, ∀ a₁ a₂ : X,
    NormalizedPair (R₀.map (D.hom i)) (Rβ.map (D.hom i)) a₁ a₂ →
      StdPairImage p f (R₀.map (D.hom i)) (Rβ.map (D.hom i))

@[expose] def A2ModelKG2 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (i : Fin D.card), D.tag i ≠ .G2 → D.tag i ≠ .trialityD4 → PairKG2 p f D i

end Defs

section Lift

variable {M X : Type} [Group M] [Group X]

theorem conjSub_eq_of_map {φ : M →* X} (hker : φ.ker ≤ Subgroup.center M) {R : Subgroup M}
    (hR : R ≤ ⁅R, R⁆) {g : M} (h : conjSub (φ g) (R.map φ) = R.map φ) : conjSub g R = R := by
  have hc : conjSub g R ≤ ⁅conjSub g R, conjSub g R⁆ := by
    unfold conjSub
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hR
  have e : (conjSub g R).map φ = conjSub (φ g) (R.map φ) := by
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  exact eq_of_map_eq_of_central φ hker hc hR (e.trans h)

theorem commute_of_conjSub_map {φ : M →* X} (hker : φ.ker ≤ Subgroup.center M) {R : Subgroup M}
    (hR : R ≤ ⁅R, R⁆) {g i : M} (hi : i ∈ R) (hord : orderOf i = 2)
    (huniq : ∀ t ∈ R, orderOf t = 2 → t = i) (h : conjSub (φ g) (R.map φ) = R.map φ) :
    g * i = i * g := by
  have hN : conjSub g R = R := conjSub_eq_of_map hker hR h
  have hmem : g * i * g⁻¹ ∈ R := by
    rw [← hN]
    exact ⟨i, hi, by simp⟩
  have hord' : orderOf (g * i * g⁻¹) = 2 := by
    rw [← hord]
    exact (MulAut.conj g).orderOf_eq i
  exact mul_inv_eq_iff_eq_mul.mp (huniq _ hmem hord')

theorem lift_normalizedPair {θ : M →* X} (hker : θ.ker ≤ Subgroup.center M) {R₀ R₁ : Subgroup M}
    {i₀ i₁ : M} (h₁ : R₁ ≤ ⁅R₁, R₁⁆) (hi₁ : i₁ ∈ R₁)
    (ho₁ : orderOf i₁ = 2) (hu₀ : ∀ t ∈ R₀, orderOf t = 2 → t = i₀)
    (hu₁ : ∀ t ∈ R₁, orderOf t = 2 → t = i₁) (hinj₀ : ∀ z ∈ R₀, z ∈ θ.ker → z = 1)
    (hinj₁ : ∀ z ∈ R₁, z ∈ θ.ker → z = 1) {a₁ a₂ : X}
    (hN : NormalizedPair (R₀.map θ) (R₁.map θ) a₁ a₂) :
    a₁ = θ i₀ ∧ a₂ = θ i₁ ∧ i₀ * i₁ = i₁ * i₀ ∧ i₀ ≠ i₁ := by
  have key : ∀ {R : Subgroup M} {i : M} {a : X}, (∀ t ∈ R, orderOf t = 2 → t = i) →
      (∀ z ∈ R, z ∈ θ.ker → z = 1) → IsUniqueInvolution (R.map θ) a → a = θ i := by
    intro R i a hu hinj ha
    obtain ⟨r, hr, rfl⟩ := ha.mem
    have hrr : r * r = 1 := by
      apply hinj _ (R.mul_mem hr hr)
      rw [MonoidHom.mem_ker, map_mul]
      exact ha.sq
    have hr1 : r ≠ 1 := fun h => ha.ne_one (by rw [h, map_one])
    have : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hrr) hr1
    rw [hu r hr this]
  have e₀ : a₁ = θ i₀ := key hu₀ hinj₀ hN.uniq₁
  have e₁ : a₂ = θ i₁ := key hu₁ hinj₁ hN.uniq₂
  refine ⟨e₀, e₁, ?_, fun h => hN.ne (by rw [e₀, e₁, h])⟩
  refine commute_of_conjSub_map hker h₁ hi₁ ho₁ hu₁ ?_
  rw [← e₀]
  exact hN.norm₁

end Lift

section Reduction

variable {p f : ℕ} [Fact p.Prime]

theorem a2LocalStdPairs_of_modelKG2 (hP1 : A2P1 p f) (hN : A2NoG2D4 p f) (h : A2ModelKG2 p f) :
    A2LocalStdPairs p f := by
  intro G _ _ _ K z hb hD F _ hF A S Fr hcard8 hnc' hP1A K' hK' L' hL' hne hnc
  have hex : ExactMembers (CoreAssembly.conjClass K) := exactMembers_of_inputs hb hD hP1
  obtain ⟨x, hx, hx1⟩ := Fr.exists_ne_one_mem_axisSub_inf_axisSub hK' hL'
  obtain ⟨hxK, hxL⟩ := Subgroup.mem_inf.mp hx
  have hxA : x ∈ A := (mem_axisSub_iff.mp hxK).1
  have hP1x := hP1A x hxA hx1
  obtain ⟨D⟩ := exists_lieSystemData_branch hb hx1
  obtain ⟨i, R₀, Rβ, a₁, a₂, hR₀, hRβ, h₀, hβ, hpair⟩ :=
    exists_modelPair_of_frame hb hex Fr hP1A hP1x D hK' hL' hxK hxL hne hnc
  have htag := hN G K z hb hD F hF A S Fr hcard8 hnc' hP1A x hxA hx1 D i
  have hpair' : NormalizedPair (R₀.map (D.hom i)) (Rβ.map (D.hom i)) a₁ a₂ := by
    rw [h₀, hβ]
    exact hpair
  have key := h hb.odd hb.five D i htag.1 htag.2 R₀ hR₀ Rβ hRβ a₁ a₂ hpair'
  rw [h₀, hβ] at key
  exact ⟨x, hx, hx1, key⟩

end Reduction

end CFSG.ClassicalInvolution.ConnectedA2
