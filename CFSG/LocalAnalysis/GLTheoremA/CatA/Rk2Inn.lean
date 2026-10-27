module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Basic
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Unique

variable {G : Type} [Group G] {K : Subgroup G} {R : Type} [Group R]

theorem rk2_induces_unique (θ : K ⧸ Subgroup.center K ≃* R) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) {φ φ' : MulAut R}
    (h : GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (h' : GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ') : φ = φ' := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hl : b⁻¹ * (l : G) * b ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hb) l).1 l.2
    simpa using this
  rw [h l ⟨_, hl⟩ rfl, h' l ⟨_, hl⟩ rfl]

end Unique

theorem rk2_mem_centralizer_of_commutator_central {G : Type} [Group G] (K : Subgroup G) (hK : ⁅K, K⁆ = K)
    (b : G) (hb : ∀ l ∈ K, ∀ i : ℤ, ⁅l, b ^ i⁆ ∈ K ⊓ Subgroup.centralizer (K : Set G)) :
    b ∈ Subgroup.centralizer (K : Set G) := by
  set C := Subgroup.zpowers b with hC
  set Z := K ⊓ Subgroup.centralizer (K : Set G) with hZ
  have hKC : ⁅K, C⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro l hl c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact hb l hl i
  have hZc : Z ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have h1 : ⁅⁅K, C⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hKC.trans hZc)
  have h2 : ⁅⁅C, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm C K]; exact h1
  have h3 : ⁅⁅K, K⁆, C⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hK] at h3
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hmem : ⁅l, b⁆ ∈ (⊥ : Subgroup G) := by
    rw [← h3]
    exact Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers b)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem rk2_commutator_eq_self {G : Type} [Group G] {K : Subgroup G} (h : commutator ↥K = ⊤) : ⁅K, K⁆ = K := by
  have h1 : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K).map K.subtype = ⁅(⊤ : Subgroup ↥K).map K.subtype,
      (⊤ : Subgroup ↥K).map K.subtype⁆ := Subgroup.map_commutator _ _ _
  have h2 : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [h2] at h1
  rw [← h1, ← commutator_def, h, Subgroup.map_top, Subgroup.range_subtype]

variable {G : Type} [Group G] [Finite G]

theorem rk2_inn_bound_on {S : GLALabel → Prop} (hInn : Rk2InnRankOn S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B K : Subgroup G} (k : ℕ) (hB : IsElemAbelian p B) (hBK : InnerDiagMarking B K)
    (hk : p ^ k * Nat.card ↥(B ⊓ centModSubgroup p K) ≤ Nat.card B) :
    ∃ lab : GLALabel, LabelOf K lab ∧ GLAInLambda2 lab ∧ (S lab → k ≤ rk2Mult lab (rk2Ord p lab.n)) := by
  have hall : ∀ lab, GLAInLambda2 lab → Rk2LabelAll lab (fun R [Group R] I _ => S lab →
      IsSimpleGroup R → ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsElemAbelian p E →
          Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n)) := by
    intro lab hlab Q hQ
    by_cases hS : S lab
    · exact rk2_rawDatum_mono (fun R _ I F ⟨hq, hp'⟩ => ⟨hq, fun _ => hp'⟩) (hInn lab hlab hS p hp hp2 Q hQ)
    · exact rk2_rawDatum_mono (fun R _ I F hq => ⟨hq, fun h => absurd h hS⟩) hQ
  have hM := rk2_marking_and_labelAll hall hBK
  obtain ⟨hKperf, lab, hlab, hraw⟩ := hM
  have hLab : LabelOf K lab :=
    ⟨hKperf, lab, hlab, rk2_rawDatum_mono (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨hN, hind⟩, htab⟩ := rk2_rawDatum_exists hraw
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
  have hclaim : ∀ z ∈ ψ.ker, ∀ l : ↥K, (l : G)⁻¹ * (z : G)⁻¹ * l * z ∈ K ⊓ Subgroup.centralizer (K : Set G) := by
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

theorem rk2_inn_bound (hInn : Rk2InnRank) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B K : Subgroup G} (k : ℕ) (hB : IsElemAbelian p B) (hBK : InnerDiagMarking B K)
    (hk : p ^ k * Nat.card ↥(B ⊓ centModSubgroup p K) ≤ Nat.card B) :
    ∃ lab : GLALabel, LabelOf K lab ∧ GLAInLambda2 lab ∧ k ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨lab, h1, h2, h3⟩ := rk2_inn_bound_on hInn hp hp2 k hB hBK hk
  exact ⟨lab, h1, h2, h3 trivial⟩

end CFSG.LocalAnalysis.GLTheoremA
