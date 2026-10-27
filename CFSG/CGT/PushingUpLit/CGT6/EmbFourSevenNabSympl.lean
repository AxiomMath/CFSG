module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenArith
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenNab
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenAbel

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin
open scoped commutatorElement

theorem arithStmt_holds : ArithStmt :=
  fun _ _ _ _ _ _ _ hp hodd hj hMc hC1 hC hC2 hC3 hSe hS haS hq =>
    weil_arith hp hodd hj hMc hC1 hC hC2 hC3 hSe hS haS hq

section Assembly

variable {G : Type} [Group G] {P : Subgroup G}

theorem normConj_pow_five {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) (hx5 : x ^ 5 = 1)
    (g : ↥P) :
    normConj P x hx (normConj P x hx (normConj P x hx (normConj P x hx (normConj P x hx g)))) =
      g := by
  have hx5' : x * x * x * x * x = 1 := by simpa [pow_succ] using hx5
  apply Subtype.ext
  simp only [coe_normConj]
  calc x * (x * (x * (x * (x * (g : G) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹
      = (x * x * x * x * x) * (g : G) * (x * x * x * x * x)⁻¹ := by group
    _ = g := by rw [hx5']; simp

theorem xbar_pow_five {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) (hx5 : x ^ 5 = 1)
    (a : ↥P ⧸ Subgroup.center ↥P) :
    xbar P x hx (xbar P x hx (xbar P x hx (xbar P x hx (xbar P x hx a)))) = a := by
  induction a using QuotientGroup.induction_on with
  | H g =>
    simp only [xbar_mk]
    rw [normConj_pow_five hx hx5]

theorem card_fixPbar (x : G) (hx : x ∈ Subgroup.normalizer (P : Set G)) :
    Nat.card (fixPbar P x hx) = Nat.card {a // xbar P x hx a = a} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end Assembly

theorem nabSymplStmt_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (Y P : Subgroup (MulAut V)), Small16 Y → ∀ p : ℕ, p.Prime → Odd p → IsPGroup p P →
        (¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) →
        Y ≤ Subgroup.normalizer (P : Set (MulAut V)) →
        (∀ Q : Subgroup (MulAut V), Q < P → Y ≤ Subgroup.normalizer (Q : Set (MulAut V)) →
          Q ≤ Subgroup.centralizer (Y : Set (MulAut V))) →
        ¬ P ≤ Subgroup.centralizer (Y : Set (MulAut V)) →
        ∃ (x : MulAut V) (hx : x ∈ Subgroup.normalizer (P : Set (MulAut V))),
          x ^ 5 = 1 ∧ Nat.card (commV (Subgroup.zpowers x)) ≤ 16 ∧
          (∀ g h : ↥P, ⁅g, h⁆ ∈ Subgroup.center ↥P) ∧
          (∀ g : ↥P, g ^ p ∈ Subgroup.center ↥P) ∧
          (∀ z : ↥P, z ∈ Subgroup.center ↥P → normConj P x hx z = z) ∧
          (∀ (K : Type) [Field K] (lam : ↥(Subgroup.center ↥P) →* Kˣ),
            (∃ (g h : ↥P) (hc : ⁅g, h⁆ ∈ Subgroup.center ↥P), lam ⟨⁅g, h⁆, hc⟩ ≠ 1) →
            ∀ g : ↥P, (∀ (h : ↥P) (hc : ⁅g, h⁆ ∈ Subgroup.center ↥P), lam ⟨⁅g, h⁆, hc⟩ = 1) →
              g ∈ Subgroup.center ↥P) ∧
          (∃ j : ℕ, 2 ≤ j ∧ Nat.card (↥P ⧸ Subgroup.center ↥P) = p ^ j) ∧
          Nat.card (fixPbar P x hx) * p ≤ Nat.card (↥P ⧸ Subgroup.center ↥P) ∧
          (p ≠ 5 → Nat.card (fixPbar P x hx) * p ^ 2 ≤ Nat.card (↥P ⧸ Subgroup.center ↥P)) ∧
          (p = 3 → Nat.card (fixPbar P x hx) * 81 ≤ Nat.card (↥P ⧸ Subgroup.center ↥P)) := by
  intro V _ _ _ Y P hY p hp _ hP hnab hYP hmin hnc
  obtain ⟨hperf, S, hSY, hgen, hS⟩ := hY
  have hN : NabHyp Y P p := ⟨hp, hperf, hP, hYP, hnc, hmin, hnab⟩
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨x, hxS, g₀, hg₀, hxg⟩ := hN.exists_gen_act hgen
  have hxY : x ∈ Y := hSY hxS
  have hx : x ∈ Subgroup.normalizer (P : Set (MulAut V)) := hYP hxY
  obtain ⟨hx5, hxc⟩ := hS x hxS
  have hc := hN.commutator_mem_center
  refine ⟨x, hx, hx5, hxc, hc, hN.pow_mem_center, fun z hz => hN.normConj_center hxY hz,
    fun K _ lam hnt g hg => hN.radical_le_center lam hnt hg, ?_⟩
  have hnab' : ¬ ∀ a b : ↥P, a * b = b * a := fun hcon =>
    hnab fun a ha b hb => congrArg Subtype.val (hcon ⟨a, ha⟩ ⟨b, hb⟩)
  have hne : ∃ a : ↥P ⧸ Subgroup.center ↥P, xbar P x hx a ≠ a := by
    refine ⟨QuotientGroup.mk ⟨g₀, hg₀⟩, fun heq => hxg ?_⟩
    rw [xbar_mk] at heq
    exact mem_center_iff_mem_nabZ.mp (QuotientGroup.eq.mp heq.symm)
  have hinv : ∀ a b : ↥P ⧸ Subgroup.center ↥P,
      centerPair (xbar P x hx a) (xbar P x hx b) = centerPair a b := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H g =>
      induction b using QuotientGroup.induction_on with
      | H k =>
        simp only [xbar_mk, centerPair_mk]
        rw [← map_commutatorElement]
        exact hN.normConj_center hxY (hc g k)
  obtain ⟨hj, hfix1, hfix2, hfix3⟩ :=
    center_quot_bounds hp hP hc hnab' (xbar P x hx) (xbar_pow_five hx hx5) hne hinv
  rw [← card_fixPbar x hx] at hfix1 hfix2 hfix3
  exact ⟨hj, hfix1, hfix2, hfix3⟩

end CFSG.CGT.PushingUpLit.CGT6
