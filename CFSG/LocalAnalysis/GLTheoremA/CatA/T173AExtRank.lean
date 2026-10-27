module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem ext_image_card {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {S B : Subgroup Y}
    {x : Y} (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Y) ↔ b ∈ Subgroup.zpowers x)
    (hS : commutator ↥S = ⊤) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) (hN : B ≤ Subgroup.normalizer (S : Set Y))
    (hind : ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Y) = b⁻¹ * l * b) φ) :
    ∃ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) ∧
        IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  haveI : Fact p.Prime := ⟨hp⟩
  choose! φ hφI hφ using hind
  have hBc : ∀ u v : ↥B, (u : Y) * v = v * u := fun u v => isElemAbelian_commute hB u.2 v.2
  have hmem : ∀ (b : Y), b ∈ B → ∀ l : ↥S, b⁻¹ * (l : Y) * b ∈ S := by
    intro b hb l
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hN hb)) l).1 l.2
    simpa using this
  let f : ↥B → MulAut R := fun u => φ u.1
  have hf_mul : ∀ u v : ↥B, f (u * v) = f u * f v := by
    intro u v
    refine rk2_induces_unique θ (hN (B.mul_mem u.2 v.2)) (hφ _ (B.mul_mem u.2 v.2)) ?_
    intro l l' hll'
    have hl1 := hmem v v.2 l
    have hl2 := hmem u u.2 ⟨_, hl1⟩
    have e1 := hφ v.1 v.2 l ⟨_, hl1⟩ rfl
    have e2 := hφ u.1 u.2 ⟨_, hl1⟩ ⟨_, hl2⟩ rfl
    have hl' : l' = ⟨_, hl2⟩ := by
      apply Subtype.ext
      rw [hll']
      have hc : (u : Y) * v = v * u := hBc u v
      rw [hc]
      simp [mul_assoc]
    show (φ u.1 * φ v.1) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
    rw [MulAut.mul_apply, e1, e2, hl']
  let ψ : ↥B →* MulAut R := MonoidHom.mk' f hf_mul
  have hψ : ∀ u : ↥B, ψ u = φ u.1 := fun u => rfl
  have hS2 : ⁅S, S⁆ = S := rk2_commutator_eq_self hS
  have hclaim : ∀ z ∈ ψ.ker, ∀ l : ↥S,
      (l : Y)⁻¹ * (z : Y)⁻¹ * l * z ∈ S ⊓ Subgroup.centralizer (S : Set Y) := by
    intro z hz l
    have hz1 : φ z.1 = 1 := by rw [← hψ]; exact hz
    have hl1 := hmem z z.2 l
    have e1 := hφ z.1 z.2 l ⟨_, hl1⟩ rfl
    rw [hz1] at e1
    have e2 : (QuotientGroup.mk l : ↥S ⧸ Subgroup.center ↥S) = QuotientGroup.mk ⟨_, hl1⟩ := by
      apply θ.injective
      simpa using e1
    have hc : (l : ↥S)⁻¹ * ⟨_, hl1⟩ ∈ Subgroup.center ↥S := QuotientGroup.eq.1 e2
    refine ⟨?_, ?_⟩
    · have : ((l⁻¹ * ⟨_, hl1⟩ : ↥S) : Y) ∈ S := (l⁻¹ * ⟨_, hl1⟩ : ↥S).2
      simpa [mul_assoc] using this
    · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨g, hg⟩)
      simpa [mul_assoc] using this
  have hkerx : ∀ z ∈ ψ.ker, ((z : ↥B) : Y) ∈ Subgroup.zpowers x := by
    intro z hz
    have hc : ((z : ↥B) : Y) ∈ Subgroup.centralizer (S : Set Y) := by
      refine rk2_mem_centralizer_of_commutator_central S hS2 z ?_
      intro l hl i
      have hzi : z ^ (-i) ∈ ψ.ker := Subgroup.zpow_mem _ hz _
      have := hclaim (z ^ (-i)) hzi ⟨l⁻¹, inv_mem hl⟩
      simpa [commutatorElement_def, mul_assoc] using this
    exact (hcent _ z.2).1 hc
  have hox : orderOf x = p := orderOf_eq_prime (hB.2 x hxB) hx1
  have hkercard : Nat.card ψ.ker ≤ p := by
    rw [← hox, ← Nat.card_zpowers]
    refine Nat.card_le_card_of_injective (fun z => ⟨((z.1 : ↥B) : Y), hkerx z.1 z.2⟩) ?_
    intro z z' h
    have h' := congrArg (fun w : ↥(Subgroup.zpowers x) => (w : Y)) h
    exact Subtype.ext (Subtype.ext h')
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hrange : p ^ 3 ≤ Nat.card ψ.range := by
    have h1 : p * p ^ 3 ≤ p * Nat.card ψ.range := by
      calc p * p ^ 3 = p ^ 4 := by ring
        _ ≤ Nat.card B := hB4
        _ = Nat.card ψ.ker * Nat.card ψ.range := hcard.symm
        _ ≤ p * Nat.card ψ.range := Nat.mul_le_mul_right _ hkercard
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hEle : ψ.range ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) := by
    rintro _ ⟨u, rfl⟩
    exact Subgroup.subset_closure (Or.inl (hφI _ u.2))
  have hEel : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      apply Subtype.ext
      change (a : MulAut R) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hBc u v))
    · obtain ⟨u, rfl⟩ := ha
      rw [← map_pow]
      have : u ^ p = 1 := Subtype.ext (by simpa using hB.2 u u.2)
      rw [this, map_one]
  exact ⟨ψ.range, hEle, hEel, hrange⟩

theorem ext_split_rank (hInn : Rk2InnRank) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type}
    [Group Ω] [Finite Ω] {S B : Subgroup Ω} {x : Ω} (hB : IsElemAbelian p B)
    (hB4 : p ^ 4 ≤ Nat.card B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x)
    (hmark : SplitInnerDiagMarking16 p B S) :
    GLAMarking S fun lab _ _ I _ θ => 3 ≤ rk2Mult lab (rk2Ord p lab.n) ∧ GLASplit16 p lab ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ := by
  have hall : ∀ lab, GLAInLambda2 lab → Rk2LabelAll lab
      (fun R [Group R] I _ => IsSimpleGroup R → ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsElemAbelian p E →
          Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n)) :=
    fun lab hlab => hInn lab hlab trivial p hp hp2
  obtain ⟨hSperf, lab, hlab, hraw⟩ := rk2_marking_and_labelAll hall hmark
  refine ⟨hSperf, lab, hlab, rk2_rawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hsplit, hN, hind⟩, htab⟩
  refine ⟨hs, hna, θ, ?_, hsplit, hN, hind⟩
  obtain ⟨E, hEle, hEel, hE3⟩ := ext_image_card hp hB hB4 hxB hx1 hcent hSperf θ hN hind
  have h3 : p ^ 3 ≤ p ^ rk2Mult lab (rk2Ord p lab.n) := hE3.trans (htab hs E hEle hEel)
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h3

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
