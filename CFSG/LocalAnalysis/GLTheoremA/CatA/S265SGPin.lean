module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InnRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith2
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def InnLabelOf (B S : Subgroup G) (lab : GLALabel) : Prop :=
  GLAMarking S fun lab' _ _ I _ θ => lab' = lab ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
    ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ

theorem InnLabelOf.labelOf {B S : Subgroup G} {lab : GLALabel} (h : InnLabelOf B S lab) :
    LabelOf S lab :=
  rk2_marking_mono (fun _ _ _ _ _ _ h => h.1) h

variable [Finite G]

theorem rk2_inn_bound_on_pin {S : GLALabel → Prop} (hInn : Rk2InnRankOn S) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B K : Subgroup G} (k : ℕ) (hB : IsElemAbelian p B)
    (hBK : InnerDiagMarking B K) (hk : p ^ k * Nat.card ↥(B ⊓ centModSubgroup p K) ≤ Nat.card B) :
    ∃ lab : GLALabel, InnLabelOf B K lab ∧ GLAInLambda2 lab ∧
      (S lab → k ≤ rk2Mult lab (rk2Ord p lab.n)) := by
  have hall : ∀ lab, GLAInLambda2 lab → Rk2LabelAll lab (fun R [Group R] I _ => S lab →
      IsSimpleGroup R → ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsElemAbelian p E →
          Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n)) := by
    intro lab hlab Q hQ
    by_cases hS : S lab
    · exact rk2_rawDatum_mono (fun R _ I F ⟨hq, hp'⟩ => ⟨hq, fun _ => hp'⟩)
        (hInn lab hlab hS p hp hp2 Q hQ)
    · exact rk2_rawDatum_mono (fun R _ I F hq => ⟨hq, fun h => absurd h hS⟩) hQ
  have hM := rk2_marking_and_labelAll hall hBK
  obtain ⟨hKperf, lab, hlab, hraw⟩ := hM
  have hLab : InnLabelOf B K lab := ⟨hKperf, lab, hlab,
    rk2_rawDatum_mono (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, rfl, hθ.1⟩) hraw⟩
  obtain ⟨R, _, I, F, hs, -, θ, ⟨hN, hind⟩, htab⟩ := rk2_rawDatum_exists hraw
  refine ⟨lab, hLab, hlab, fun hS => ?_⟩
  choose! φ hφI hφ using hind
  have hBc : ∀ x y : ↥B, (x : G) * y = y * x := fun x y => isElemAbelian_commute hB x.2 y.2
  have hmem : ∀ (b : G), b ∈ B → ∀ l : ↥K, b⁻¹ * (l : G) * b ∈ K := by
    intro b hb l
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hN hb)) l).1 l.2
    simpa using this
  let f : ↥B → MulAut R := fun x => φ x.1
  have hf_mul : ∀ x y : ↥B, f (x * y) = f x * f y := by
    intro x y
    refine rk2_induces_unique θ (hN (B.mul_mem x.2 y.2)) (hφ _ (B.mul_mem x.2 y.2)) ?_
    intro l l' hll'
    have hl1 := hmem y y.2 l
    have hl2 := hmem x x.2 ⟨_, hl1⟩
    have e1 := hφ y.1 y.2 l ⟨_, hl1⟩ rfl
    have e2 := hφ x.1 x.2 ⟨_, hl1⟩ ⟨_, hl2⟩ rfl
    have hl' : l' = ⟨_, hl2⟩ := by
      apply Subtype.ext
      rw [hll']
      have hc : (x : G) * y = y * x := hBc x y
      rw [hc]
      simp [mul_assoc]
    show (φ x.1 * φ y.1) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
    rw [MulAut.mul_apply, e1, e2, hl']
  let ψ : ↥B →* MulAut R := MonoidHom.mk' f hf_mul
  have hψ : ∀ x : ↥B, ψ x = φ x.1 := fun x => rfl
  have hK2 : ⁅K, K⁆ = K := rk2_commutator_eq_self hKperf
  have hclaim : ∀ z ∈ ψ.ker, ∀ l : ↥K,
      (l : G)⁻¹ * (z : G)⁻¹ * l * z ∈ K ⊓ Subgroup.centralizer (K : Set G) := by
    intro z hz l
    have hz1 : φ z.1 = 1 := by rw [← hψ]; exact hz
    have hl1 := hmem z z.2 l
    have e1 := hφ z.1 z.2 l ⟨_, hl1⟩ rfl
    rw [hz1] at e1
    have e2 : (QuotientGroup.mk l : K ⧸ Subgroup.center K) = QuotientGroup.mk ⟨_, hl1⟩ := by
      apply θ.injective
      simpa using e1
    have hc : (l : ↥K)⁻¹ * ⟨_, hl1⟩ ∈ Subgroup.center ↥K := QuotientGroup.eq.1 e2
    refine ⟨?_, ?_⟩
    · have : ((l⁻¹ * ⟨_, hl1⟩ : ↥K) : G) ∈ K := (l⁻¹ * ⟨_, hl1⟩ : ↥K).2
      simpa [mul_assoc] using this
    · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨g, hg⟩)
      simpa [mul_assoc] using this
  have hker : ∀ z ∈ ψ.ker, (z : G) ∈ centModSubgroup p K := by
    intro z hz
    have hcent : (z : G) ∈ Subgroup.centralizer (K : Set G) := by
      refine rk2_mem_centralizer_of_commutator_central K hK2 z ?_
      intro l hl i
      have hzi : z ^ (-i) ∈ ψ.ker := Subgroup.zpow_mem _ hz _
      have := hclaim (z ^ (-i)) hzi ⟨l⁻¹, inv_mem hl⟩
      simpa [commutatorElement_def, mul_assoc] using this
    exact centMod_iff.1 (centMod_of_mem_centralizer hcent)
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hker_le : Nat.card ψ.ker ≤ Nat.card ↥(B ⊓ centModSubgroup p K) := by
    refine Nat.card_le_card_of_injective (fun z => ⟨(z.1 : G), z.1.2, hker z.1 z.2⟩) ?_
    intro z z' h
    have h' : (((z : ↥ψ.ker) : ↥B) : G) = (((z' : ↥ψ.ker) : ↥B) : G) := by
      simpa using congrArg (fun w : ↥(B ⊓ centModSubgroup p K) => (w : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hrange : p ^ k ≤ Nat.card ψ.range := by
    have h1 : p ^ k * Nat.card ψ.ker ≤ Nat.card ψ.ker * Nat.card ψ.range := by
      rw [hcard]
      exact (Nat.mul_le_mul_left _ hker_le).trans hk
    rw [mul_comm (Nat.card ψ.ker)] at h1
    exact Nat.le_of_mul_le_mul_right h1 hkpos
  have hEle : ψ.range ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.subset_closure (Or.inl (hφI _ x.2))
  have hEel : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      change (a : MulAut R) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hBc x y))
    · obtain ⟨x, rfl⟩ := ha
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (by simpa using hB.2 x x.2)
      rw [this, map_one]
  have hle := htab hS hs ψ.range hEle hEel
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (hrange.trans hle)

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SG

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

section Rank


theorem exists_innLabel_of_qsnl_big {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K) :
    ∃ lab : GLALabel, InnLabelOf B S lab ∧ GLAInLambda2 lab ∧ 3 ≤ rk2Mult lab (rk2Ord p lab.n) ∧
      ¬ (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
        lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) := by
  have hc := h.cfg
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hcent : Nat.card ↥(B ⊓ centModSubgroup p S) ≤ p := by
    calc Nat.card ↥(B ⊓ centModSubgroup p S) ≤ Nat.card ↥(Subgroup.zpowers x) :=
          Subgroup.card_le_of_le fun b hb => (hc.centB b hb.1).1 (centMod_iff.2 hb.2)
      _ = p := by rw [Nat.card_zpowers]; exact orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1
  have hk : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p S) ≤ Nat.card B :=
    calc p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p S) ≤ p ^ 3 * p := Nat.mul_le_mul_left _ hcent
      _ = p ^ 4 := (pow_succ p 3).symm
      _ ≤ Nat.card B := hc.big
  obtain ⟨lab, hl, hl2, h3⟩ := rk2_inn_bound_on_pin (rk2InnRank_of_kRank rk2KRank) hc.prime
    hc.odd 3 hc.elem (S10.inner_of_innDiagOn hc.comp hc.quasi hc.inn) hk
  refine ⟨lab, hl, hl2, h3 trivial, fun hs => ?_⟩
  have := rk2Mult_le_two_of_small hs (rk2Ord_pos hc.prime hc.odd lab.n)
  have := h3 trivial
  omega

end Rank

end CFSG.LocalAnalysis.GLTheoremA.S265.SG

end
