module

public import CFSG.ClassicalInvolution.Q3.TA3FrameBase
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Member

variable {Y : Type} [Group Y] [Finite Y] {L T : Subgroup Y}

theorem false_of_not_three_dvd [T.Normal] (hTL : T ⊔ L = ⊤) (h3 : memberIndex L T = 3)
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer T)) : False :=
  hout (three_dvd_card_outer hTL h3 hC)

end Member

variable {X : Type} [Group X]

theorem not_three_dvd_of_dvd {n : ℕ} (h : Nat.card (Outer X) ∣ n) (hn : ¬ 3 ∣ n) :
    ¬ 3 ∣ Nat.card (Outer X) := fun h3 => hn (h3.trans h)

theorem not_three_dvd_of_le_two [Finite X] (h : Nat.card (Outer X) ≤ 2) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  Quasithin.A318P.not_dvd_outer_of_card_le_two h Nat.prime_three (by norm_num)

theorem not_three_dvd_of_mulEquiv {X' : Type} [Group X'] (e : X ≃* X')
    (h : ¬ 3 ∣ Nat.card (Outer X')) : ¬ 3 ∣ Nat.card (Outer X) := by
  rwa [Nat.card_congr (equivalence e).toEquiv]

theorem card_outer_dvd_of_hom {C : Type*} [Group C] (Θ : MulAut X →* C)
    (hker : Θ.ker = ComponentClassification.OuterAutomorphisms.inner X) :
    Nat.card (Outer X) ∣ Nat.card C :=
  Subgroup.card_dvd_of_injective
    ((QuotientGroup.kerLift Θ).comp (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom)
    ((QuotientGroup.kerLift_injective Θ).comp (MulEquiv.injective _))

theorem not_three_dvd_alternating {n : ℕ} (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  Quasithin.A318P.not_dvd_outer_alternating (Or.inr hn) e Nat.prime_three (by norm_num)

theorem not_three_dvd_M11 [Finite X] (h : NativeSporadic.IsSporadic X .M11) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h; Quasithin.A318P.not_dvd_outer_M11 e Nat.prime_three (by norm_num)

theorem not_three_dvd_M12 [Finite X] (h : NativeSporadic.IsSporadic X .M12) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h; Quasithin.A318P.not_dvd_outer_M12 e Nat.prime_three (by norm_num)

theorem not_three_dvd_M22 [Finite X] (h : NativeSporadic.IsSporadic X .M22) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h; Quasithin.A318P.not_dvd_outer_M22 e Nat.prime_three (by norm_num)

theorem not_three_dvd_M23 [Finite X] (h : NativeSporadic.IsSporadic X .M23) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h; Quasithin.A318P.not_dvd_outer_M23 e Nat.prime_three (by norm_num)

theorem not_three_dvd_J1 [Finite X] (h : NativeSporadic.IsSporadic X .J1) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h; Quasithin.A318P.not_dvd_outer_J1 e Nat.prime_three (by norm_num)

theorem not_three_dvd_J2 [Finite X] (h : NativeSporadic.IsSporadic X .J2) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h; Quasithin.A318P.not_dvd_outer_J2 e Nat.prime_three (by norm_num)

theorem not_three_dvd_J3 (h : NativeSporadic.IsSporadic X .J3) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h
  not_three_dvd_of_mulEquiv (e.trans Sporadic.Schreier.j3PermEquiv)
    (not_three_dvd_of_le_two Sporadic.SmallOddCore.j3_outer_card_le)

theorem not_three_dvd_McL [Finite X] (h : NativeSporadic.IsSporadic X .McL) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨e⟩ := h
  have : Finite (NativeSporadic.Carrier .McL) := Finite.of_equiv X e.toEquiv
  exact not_three_dvd_of_mulEquiv e
    (not_three_dvd_of_le_two Sporadic.Schreier.McL_outer_card_le_two.1)

theorem not_three_dvd_Ly (h : NativeSporadic.IsSporadic X .Ly) : ¬ 3 ∣ Nat.card (Outer X) :=
  let ⟨e⟩ := h
  not_three_dvd_of_mulEquiv e (not_three_dvd_of_dvd Nobq.card_outer_Ly_dvd_two (by norm_num))

theorem not_three_dvd_psu_three_four (h : StatedClassicalModel X .PSU 3 2 2) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  rw [(LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound X 3 2 2 h).2.2.1]
  decide

theorem not_three_dvd_psl_three {n : ℕ} (hn : 3 ≤ n) (h : StatedClassicalModel X .PSL n 3 1) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  refine not_three_dvd_of_dvd
    ((LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X n 3 1 h).2.2.2.2 hn)
    fun h3 => ?_
  have h4 : 2 * 1 * Nat.gcd n (3 ^ 1 - 1) ∣ 4 := Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_right n 2)
  exact absurd (h3.trans h4) (by decide)

theorem not_three_dvd_psu_three {n : ℕ} (h : StatedClassicalModel X .PSU n 3 1) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  rw [(LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound X n 3 1 h).2.2.1]
  intro h3
  have h8 : 2 * 1 * Nat.gcd n (3 ^ 1 + 1) ∣ 8 := Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_right n 4)
  exact absurd (h3.trans h8) (by decide)

theorem not_three_dvd_psp_three {n : ℕ} (h : StatedClassicalModel X .PSp n 3 1) :
    ¬ 3 ∣ Nat.card (Outer X) :=
  not_three_dvd_of_dvd
    (LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound X n 3 1 h).2.1
    (by decide)

theorem not_three_dvd_g2_three (h : LieModel X .G2 0 3 1) : ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨-, hm⟩ :=
    Q5G2D4.chevalleyExceptionalModel_of_lieModel h (by decide) (by decide) (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hm
  have : CharP K LieType.Ree.ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      le_rfl hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    LieType.Chevalley.G2_three_exact_automorphism_normal_form le_rfl K hK
  refine not_three_dvd_of_mulEquiv e (not_three_dvd_of_dvd (card_outer_dvd_of_hom Θ hker) ?_)
  rw [show Nat.card (Multiplicative (ZMod (2 * 1))) = Nat.card (ZMod (2 * 1)) from rfl,
    Nat.card_zmod]
  decide

end CFSG.ClassicalInvolution.Q3.TA3.Frame
