module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3U3
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem false_of_gl2_frame {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (hD : TightDatum R S t) {F : Type} [Field F] {H : Subgroup (GL (Fin 2) F)}
    {N : Subgroup Y} [N.Normal] (hRN : R ≤ N) {π : H →* Y}
    (hrange : π.range = N ⊓ Subgroup.centralizer ({t} : Set Y)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀))
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀)) : False := by
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hD hrange hk hF₀ h4 eJ
  have hval : ∀ y ∈ R, ∃ A : H, π A = y := fun y hy => by
    have : y ∈ π.range := hrange ▸ ⟨hRN hy, hD.cent hy⟩
    exact this
  have hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    obtain ⟨A, rfl⟩ := hval a ha
    obtain ⟨B, rfl⟩ := hval b hb
    obtain ⟨c, hcA⟩ := exists_scalar_of_commute hk hcs fun B' hB' =>
      (Subgroup.mem_centralizer_iff.mp (hRJ ha) (π B') ⟨B', hB', rfl⟩).symm
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcA, scalar_mul_comm]
  obtain ⟨x, -, y, -, hxy⟩ := hD.sylow_nonabelian S
  exact hxy (Subtype.ext (hab _ x.2 _ y.2))

theorem false_of_l3_ne_three {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X} (hD : TightDatum R S z) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel X .PSL 3 p f) (h3 : p ^ f ≠ 3) : False := by
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h5 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    have h3' : Nat.card K ≠ 3 := by rw [hK]; exact h3
    omega
  let e : ↥(⊤ : Subgroup X) ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    Subgroup.topEquiv.trans e₀
  obtain ⟨Q, π, hrange, hk, -, -⟩ := Q5L3.exists_frame hodd e (Subgroup.mem_top z) hD.order
  exact false_of_gl2_frame hD le_top hrange hk Q5L3.slCentScalar_top hodd h5 Q5L3.slPartTopEquiv

theorem model164U3_proved : Model164U3 := by
  intro X _ _ R S z hm _ _ p f hp hp2 h41 hL
  exfalso
  obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have h : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hq := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  let e : ↥(⊤ : Subgroup X) ≃* Assembly.LowTwoRank.StatedProj
      (Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) := Subgroup.topEquiv.trans e₀
  obtain ⟨π, hrange, hk, -⟩ := Q5U3.exists_frame h hp2 e (Subgroup.mem_top z) hm.datum.order
  obtain ⟨eJ⟩ := Q5U3.nonempty_slPart_equiv h
  exact false_of_gl2_frame hm.datum le_top hrange hk (Q5U3.slCentScalar_GU2 h)
    (by rw [hq]; exact hodd) (by rw [hq]; omega) eJ

end CFSG.ClassicalInvolution.Q3.TL4.MF164
