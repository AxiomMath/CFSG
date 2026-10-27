module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open
open scoped commutatorElement

theorem commutatorElement_mul_central_left {Q : Type*} [Group Q] {a b z : Q}
    (hz : z ∈ Subgroup.center Q) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b * z⁻¹ = b := by
    have h := (Subgroup.mem_center_iff.1 hz) b
    rw [← h, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hzb]

theorem commutatorElement_mul_central_right {Q : Type*} [Group Q] {a b z : Q}
    (hz : z ∈ Subgroup.center Q) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a⁻¹ * z⁻¹ = a⁻¹ := by
    have h := (Subgroup.mem_center_iff.1 hz) a⁻¹
    rw [← h, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hza]

theorem normal_central_or_top_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  have hcomm : commutator Q = ⊤ := hQ.1
  have hsimp : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hHm : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · left
    intro x hx
    have hm : QuotientGroup.mk' (Subgroup.center Q) x ∈
        N.map (QuotientGroup.mk' (Subgroup.center Q)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hm
    exact (QuotientGroup.eq_one_iff x).1 hm
  · right
    have key : ∀ g : Q, ∃ n ∈ N, ∃ z ∈ Subgroup.center Q, g = n * z := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center Q) g ∈
          N.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.1 hg
      refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
      exact QuotientGroup.eq.1 hng
    rw [eq_top_iff, ← hcomm]
    refine Subgroup.commutator_le.2 ?_
    intro g _ k _
    obtain ⟨n, hn, z, hz, rfl⟩ := key g
    obtain ⟨m, hm, w, hw, rfl⟩ := key k
    rw [commutatorElement_mul_central_left hz, commutatorElement_mul_central_right hw]
    have e : ⁅n, m⁆ = n * (m * n⁻¹ * m⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    rw [e]
    exact N.mul_mem hn (Subgroup.Normal.conj_mem ‹N.Normal› _ (N.inv_mem hn) m)

theorem not_le_normalizer_of_isQuasisimple {G : Type*} [Group G] [Finite G] {P X : Subgroup G}
    (hQ : CFSG.Open.IsQuasisimple ↥P)
    (hsolv : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (X : Set G) →
      Group.IsSolvable ↥(H ⊓ X) → Group.IsSolvable ↥H)
    (hcard : Nat.card ↥X < Nat.card ↥P) : ¬ P ≤ Subgroup.normalizer (X : Set G) := by
  intro hPN
  have hnorm : ((P ⊓ X).subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : (n : G) ∈ P ⊓ X := hn
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact P.mul_mem (P.mul_mem g.2 (Subgroup.mem_inf.1 hn').1) (P.inv_mem g.2)
    · exact ((Subgroup.mem_normalizer_iff.1 (hPN g.2)) (n : G)).1 (Subgroup.mem_inf.1 hn').2
  haveI := hnorm
  rcases normal_central_or_top_of_isQuasisimple hQ ((P ⊓ X).subgroupOf P) with hc | ht
  · have hsolvPX : Group.IsSolvable ↥(P ⊓ X) := by
      refine Group.isSolvable_of_comm ?_
      intro a b
      have ha : (a : G) ∈ P := (Subgroup.mem_inf.1 a.2).1
      have hac : (⟨a, ha⟩ : ↥P) ∈ Subgroup.center ↥P :=
        hc (Subgroup.mem_subgroupOf.2 a.2)
      have hb : (b : G) ∈ P := (Subgroup.mem_inf.1 b.2).1
      have h := (Subgroup.mem_center_iff.1 hac) ⟨b, hb⟩
      exact Subtype.ext (congrArg Subtype.val h).symm
    have hsP : Group.IsSolvable ↥P := hsolv P hPN hsolvPX
    haveI := hsP
    have hsub : Subsingleton ↥P := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥P))) hQ.1
    have hPbot : P ≤ X := by
      intro g hg
      have h1 : (⟨g, hg⟩ : ↥P) = 1 := Subsingleton.elim _ _
      have h2 : g = 1 := congrArg Subtype.val h1
      rw [h2]
      exact X.one_mem
    exact absurd (Subgroup.card_le_of_le hPbot) (not_le.2 hcard)
  · have hPX : P ≤ X := by
      intro g hg
      have hmem : (⟨g, hg⟩ : ↥P) ∈ (P ⊓ X).subgroupOf P := by
        rw [ht]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).2
    exact absurd (Subgroup.card_le_of_le hPX) (not_le.2 hcard)

def commProd {G : Type*} [Group G] (A F : Subgroup G)
    (hc : ∀ a ∈ A, ∀ f ∈ F, a * f = f * a) : Subgroup G where
  carrier := {x | ∃ a ∈ A, ∃ f ∈ F, x = a * f}
  mul_mem' := by
    rintro _ _ ⟨a, ha, f, hf, rfl⟩ ⟨b, hb, g, hg, rfl⟩
    refine ⟨a * b, A.mul_mem ha hb, f * g, F.mul_mem hf hg, ?_⟩
    have hfb : f * b = b * f := (hc b hb f hf).symm
    calc a * f * (b * g) = a * (f * b) * g := by group
      _ = a * (b * f) * g := by rw [hfb]
      _ = a * b * (f * g) := by group
  one_mem' := ⟨1, A.one_mem, 1, F.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, ha, f, hf, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, f⁻¹, F.inv_mem hf, ?_⟩
    have hcomm : a⁻¹ * f⁻¹ = f⁻¹ * a⁻¹ := (Commute.inv_inv (hc a ha f hf)).eq
    rw [mul_inv_rev]
    exact hcomm.symm

theorem sup_eq_commProd {G : Type*} [Group G] (A F : Subgroup G)
    (hc : ∀ a ∈ A, ∀ f ∈ F, a * f = f * a) : A ⊔ F = commProd A F hc := by
  refine le_antisymm (sup_le (fun a ha => ⟨a, ha, 1, F.one_mem, by simp⟩)
    (fun f hf => ⟨1, A.one_mem, f, hf, by simp⟩)) ?_
  rintro x ⟨a, ha, f, hf, rfl⟩
  exact mul_mem ((le_sup_left : A ≤ A ⊔ F) ha) ((le_sup_right : F ≤ A ⊔ F) hf)

theorem natCard_sup_le_mul_of_commute {G : Type*} [Group G] [Finite G] {A F : Subgroup G}
    (hc : ∀ a ∈ A, ∀ f ∈ F, a * f = f * a) :
    Nat.card ↥(A ⊔ F) ≤ Nat.card ↥A * Nat.card ↥F := by
  let φ : A × F → ↥(A ⊔ F) := fun p =>
    ⟨p.1.1 * p.2.1, mul_mem ((le_sup_left : A ≤ A ⊔ F) p.1.2)
      ((le_sup_right : F ≤ A ⊔ F) p.2.2)⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [sup_eq_commProd A F hc] at hx
    obtain ⟨a, ha, f, hf, rfl⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨f, hf⟩), rfl⟩
  calc Nat.card ↥(A ⊔ F) ≤ Nat.card (A × F) := Nat.card_le_card_of_surjective φ hsurj
    _ = Nat.card ↥A * Nat.card ↥F := Nat.card_prod _ _

theorem isElemAbelian_sup_of_commute {G : Type*} [Group G] {p : ℕ} {A F : Subgroup G}
    (hA : IsElemAbelian p A) (hF : IsElemAbelian p F)
    (hc : ∀ a ∈ A, ∀ f ∈ F, a * f = f * a) : IsElemAbelian p (A ⊔ F) := by
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := fun f hf f' hf' =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨f, hf⟩ ⟨f', hf'⟩)
  rw [sup_eq_commProd A F hc]
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, f, hf, hx'⟩ := x.2
    obtain ⟨a', ha', f', hf', hy'⟩ := y.2
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [hx', hy']
    have hc1 : Commute a a' := hAc a ha a' ha'
    have hc2 : Commute a f' := hc a ha f' hf'
    have hc3 : Commute f a' := (hc a' ha' f hf).symm
    have hc4 : Commute f f' := hFc f hf f' hf'
    exact Commute.mul_left (Commute.mul_right hc1 hc2) (Commute.mul_right hc3 hc4)
  · obtain ⟨a, ha, f, hf, rfl⟩ := hx
    rw [Commute.mul_pow (hc a ha f hf), hA.2 a ha, hF.2 f hf, one_mul]

end CFSG.LieType.SeitzGeneration.ExcHigh
