module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrVtx
public import CFSG.ClassicalInvolution.Q3.TL4OddSecGood

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.Q3NL (IsSectionMember3)
open CFSG.ClassicalInvolution.Q3.Q3CH

section Defs

variable {G : Type} [Group G]

@[expose] def ClassicalOrQuiet (c a : G) (haC : a ∈ Subgroup.centralizer ({c} : Set G)) : Prop :=
  (∃ K : Subgroup G, IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) K a) ∨
    ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y = y * oddQuotMk c ⟨a, haC⟩

theorem isInducedAut_mul_central {Q : Type} [Group Q] {L : Subgroup Q} {x e : Q}
    (he : e ∈ Subgroup.center Q) {σ : MulAut ↥L} (h : IsInducedAut L x σ) :
    IsInducedAut L (x * e) σ := by
  intro y
  rw [h y]
  have hey : e * (y : Q) = y * e := (Subgroup.mem_center_iff.mp he y).symm
  calc x * (y : Q) * x⁻¹ = x * (e * y) * (e⁻¹ * x⁻¹) := by
        rw [hey]; group
    _ = x * e * y * (x * e)⁻¹ := by group

theorem mem_normalizer_of_mem_center {Q : Type} [Group Q] {L : Subgroup Q} {e : Q}
    (he : e ∈ Subgroup.center Q) : e ∈ Subgroup.normalizer (L : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 : e * h * e⁻¹ = h := by
    rw [← (Subgroup.mem_center_iff.mp he h)]
    group
  rw [h1]

end Defs

section Vertex

variable {G : Type} [Group G] [Finite G]


theorem atMostOne_of_classicalOrQuiet (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {c a : G} (hc1 : c ≠ 1)
    {haC : a ∈ Subgroup.centralizer ({c} : Set G)} (h : ClassicalOrQuiet c a haC) :
    ∀ L₁ L₂ : Subgroup (OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) →
      (∃ y ∈ L₂, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) → L₁ = L₂ := by
  intro L₁ L₂ hL₁ hL₂ hm₁ hm₂
  rcases h with ⟨K, hK⟩ | hq
  · have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => hc1 (by
      have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton c)
      rwa [hZ, Subgroup.mem_bot] at h1)
    have hΦ := secData3_sFamily3 hK hK hK
    obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
    obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c K K K)
    have haj : oddQuotMk c ⟨a, haC⟩ ∈ secComp hΦ D j := hj (oddQuotMk_mem_modOdd hK.mem haC)
    exact (eq_secComp_of_not_commute hΦ D haj hL₁ hm₁).trans
      (eq_secComp_of_not_commute hΦ D haj hL₂ hm₂).symm
  · exfalso
    obtain ⟨y, hy, hne⟩ := hm₁
    exact hne (hq L₁ hL₁ y hy)


theorem autOddFreeOn_of_classicalOrQuiet (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {c a : G} (hc1 : c ≠ 1)
    {haC : a ∈ Subgroup.centralizer ({c} : Set G)} (h : ClassicalOrQuiet c a haC)
    (L : Subgroup (OddQuot c)) (hL : CFSG.IsComponent L)
    (hN : oddQuotMk c ⟨a, haC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)))
    (hm : ∃ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) :
    Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk c ⟨a, haC⟩)) := by
  rcases h with ⟨K, hK⟩ | hq
  · exact movedOddFree_oddQuot_of_member hBelow hZ hc1 haC hK L hL hN hm
  · exfalso
    obtain ⟨y, hy, hne⟩ := hm
    exact hne (hq L hL y hy)

theorem hyp51At_of_classical_pair (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {B : Subgroup G} (hB : IsElemAbelian 2 B) {a b c : G}
    (hgen : B = Subgroup.closure {a, b, c}) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (habC : a * b ∈ Subgroup.centralizer ({c} : Set G))
    (ha : ClassicalOrQuiet c a haC) (hb : ClassicalOrQuiet c b hbC)
    (hab : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      oddQuotMk c ⟨a * b, habC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)) →
      (∃ y ∈ L, oddQuotMk c ⟨a * b, habC⟩ * y ≠ y * oddQuotMk c ⟨a * b, habC⟩) →
      Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk c ⟨a * b, habC⟩))) :
    Hyp51At B c := by
  have haB : a ∈ B := hgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hcB : c ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  refine hyp51At_of_moved (fun x hx => (sq x).symm.trans (hB.2 x hx))
    (fun x hx x' hx' => congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨x', hx'⟩))
    ⟨oddQuotMk c ⟨a, haC⟩, oddQuotMk_mem_modOdd haB haC,
      Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC,
      atMostOne_of_classicalOrQuiet hBelow hZ hc1 ha⟩ ?_
  intro L hL hm x hx hxN hxmv
  obtain ⟨d, hd, hdC, e, he, rfl⟩ := exists_mul_central_of_mem_modOdd hB hgen hx
  have heN' : e⁻¹ ∈ Subgroup.normalizer (L : Set (OddQuot c)) :=
    mem_normalizer_of_mem_center (Subgroup.inv_mem _ he)
  have hdN : oddQuotMk c ⟨d, hdC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)) := by
    have h1 := Subgroup.mul_mem _ hxN heN'
    rwa [mul_inv_cancel_right] at h1
  have hdmv : ∃ y ∈ L, oddQuotMk c ⟨d, hdC⟩ * y ≠ y * oddQuotMk c ⟨d, hdC⟩ := by
    obtain ⟨y, hy, hne⟩ := hxmv
    refine ⟨y, hy, fun h => hne ?_⟩
    have hey : e * y = y * e := (Subgroup.mem_center_iff.mp he y).symm
    calc oddQuotMk c ⟨d, hdC⟩ * e * y = oddQuotMk c ⟨d, hdC⟩ * (e * y) := mul_assoc _ _ _
      _ = oddQuotMk c ⟨d, hdC⟩ * (y * e) := by rw [hey]
      _ = (oddQuotMk c ⟨d, hdC⟩ * y) * e := (mul_assoc _ _ _).symm
      _ = (y * oddQuotMk c ⟨d, hdC⟩) * e := by rw [h]
      _ = y * (oddQuotMk c ⟨d, hdC⟩ * e) := mul_assoc _ _ _
  suffices hsuff : Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk c ⟨d, hdC⟩)) by
    refine hsuff.mono fun σ hσ => ?_
    have h1 := isInducedAut_mul_central (Subgroup.inv_mem _ he) hσ
    rwa [mul_inv_cancel_right] at h1
  rcases hd with rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨y, hy, hne⟩ := hdmv
    apply hne
    have h1 : oddQuotMk c ⟨1, hdC⟩ = 1 := map_one _
    rw [h1, one_mul, mul_one]
  · exact autOddFreeOn_of_classicalOrQuiet hBelow hZ hc1 ha L hL hdN hdmv
  · exact autOddFreeOn_of_classicalOrQuiet hBelow hZ hc1 hb L hL hdN hdmv
  · exact hab L hL hm hdN hdmv

end Vertex

end CFSG.ClassicalInvolution.Q3.TL4
