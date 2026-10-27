module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def OutPRankLE1 (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ A : Subgroup (MulAut S), IsElemAbelian p A → Nat.card A ≤ p * Nat.card ↥(A ⊓ inner S)

theorem outPRankLE1_of_cyclic {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (hcyc : IsCyclic (Outer S)) : OutPRankLE1 p S :=
  fun _ hA => card_le_prime_mul_inf_inner hp hcyc hA

@[expose] def TwoLocalRankLE1 (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ E T : Subgroup S, IsElemAbelian p E → IsPGroup 2 T → T ≠ ⊥ →
    E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ p

@[expose] def OuterFixLayer (p : ℕ) (S : Type) [Group S] [Finite S] : Prop :=
  ∀ α : MulAut S, orderOf α = p → α ∉ inner S → ∀ s : S, orderOf s = p → α s = s →
    (∃ T : Subgroup S, IsPGroup 2 T ∧ T ≠ ⊥ ∧ s ∈ Subgroup.normalizer (T : Set S)) →
      GLAPLayer p (fixSubgroup α) ≠ ⊥

section SLevel

variable {S : Type} [Group S] [Finite S]

theorem mem_normalizer_of_conj_stable {A : Subgroup (MulAut S)} {T : Subgroup S}
    (hAT : ∀ α ∈ A, T.map α.toMonoidHom = T) {s : S} (hs : MulAut.conj s ∈ A) :
    s ∈ Subgroup.normalizer (T : Set S) := by
  have hT := hAT _ hs
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have : (MulAut.conj s).toMonoidHom t ∈ T.map (MulAut.conj s).toMonoidHom :=
      Subgroup.mem_map_of_mem _ ht
    rw [hT] at this
    simpa [MulAut.conj_apply] using this
  · intro ht
    have h1 : s * t * s⁻¹ ∈ T.map (MulAut.conj s).toMonoidHom := by rw [hT]; exact ht
    obtain ⟨t', ht', htt⟩ := h1
    have : t' = t := by
      have h2 : s * t' * s⁻¹ = s * t * s⁻¹ := by simpa [MulAut.conj_apply] using htt
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← this]
    exact ht'

theorem sLevel_rankOne {p : ℕ} (hp : p.Prime) (hZ : Subgroup.center S = ⊥)
    (hout : OutPRankLE1 p S) (h2 : TwoLocalRankLE1 p S) (hfix : OuterFixLayer p S)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) (hcard : p ^ 2 ≤ Nat.card A)
    {T : Subgroup S} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) (hAT : ∀ α ∈ A, T.map α.toMonoidHom = T) :
    Nat.card A = p ^ 2 ∧ ∃ α ∈ A, α ≠ 1 ∧ GLAPLayer p (fixSubgroup α) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcjinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hZ
  obtain ⟨hel, hcardE⟩ := inner_part_elemAbelian hZ hA
  have hEN : A.comap (MulAut.conj : S →* MulAut S) ≤ Subgroup.normalizer (T : Set S) :=
    fun s hs => mem_normalizer_of_conj_stable hAT hs
  have h2' : Nat.card ↥(A ⊓ inner S) ≤ p := by
    rw [← hcardE]
    exact h2 _ T hel hT2 hT hEN
  have h1 := hout A hA
  have hAle : Nat.card A ≤ p ^ 2 := by
    calc Nat.card A ≤ p * Nat.card ↥(A ⊓ inner S) := h1
      _ ≤ p * p := Nat.mul_le_mul_left _ h2'
      _ = p ^ 2 := (sq p).symm
  have hAeq : Nat.card A = p ^ 2 := le_antisymm hAle hcard
  have hinn : Nat.card ↥(A ⊓ inner S) = p := by
    have h4 : p * p ≤ p * Nat.card ↥(A ⊓ inner S) := by rw [← sq]; exact hAeq ▸ h1
    exact le_antisymm h2' (Nat.le_of_mul_le_mul_left h4 hp.pos)
  have hpos : 1 < Nat.card ↥(A ⊓ inner S) := by rw [hinn]; exact hp.one_lt
  obtain ⟨⟨x, hxA, hxI⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A ⊓ inner S)).1
    (by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hpos
      exact lt_irrefl _ hpos)
  obtain ⟨s, rfl⟩ := hxI
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hx1 (Subtype.ext (map_one _))
  have hsp : s ^ p = 1 := by
    apply hcjinj
    rw [map_pow, map_one]
    exact hA.2 _ hxA
  have hsord : orderOf s = p := orderOf_eq_prime hsp hs1
  have hsfix : ∀ α ∈ A, α s = s := by
    intro α hα
    have hcomm : α * MulAut.conj s = MulAut.conj s * α := isElemAbelian_commute hA hα hxA
    apply hcjinj
    have h5 : MulAut.conj (α s) = α * MulAut.conj s * α⁻¹ := by
      ext y
      simp [MulAut.conj_apply]
    rw [h5, hcomm]
    group
  have houter : ∃ α ∈ A, α ∉ inner S := by
    by_contra hall
    push Not at hall
    have hsub : A ≤ inner S := hall
    rw [inf_eq_left.2 hsub] at hinn
    have : p = p ^ 2 := hinn.symm.trans hAeq
    have h6 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd this h6.ne
  obtain ⟨α, hαA, hαout⟩ := houter
  have hα1 : α ≠ 1 := fun h => hαout (h ▸ (inner S).one_mem)
  have hαp : orderOf α = p := orderOf_eq_prime (hA.2 α hαA) hα1
  exact ⟨hAeq, α, hαA, hα1,
    hfix α hαp hαout s hsord (hsfix α hαA) ⟨T, hT2, hT, mem_normalizer_of_conj_stable hAT hxA⟩⟩

end SLevel

section KLevel

variable {Y : Type} [Group Y] [Finite Y]

theorem kConcl_of_rankOne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y} (h : KHyp p K B)
    {S : Type} [Group S] [Finite S] (e : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hout : OutPRankLE1 p S) (h2 : TwoLocalRankLE1 p S) (hfix : OuterFixLayer p S)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) : KConcl p K B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBN := le_normalizer_of_normal (B := B) h.normal
  have hZ : Subgroup.center S = ⊥ := by
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.qs.2
    haveI : IsSimpleGroup S := e.symm.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h1 | h1
    · exact h1
    · exfalso
      letI : CommGroup S := { ‹Group S› with
        mul_comm := fun a b => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b)) a }
      exact false_of_quasisimple_comm_quotient h.qs e
  obtain ⟨hcard, -⟩ := card_range_ge hp h hBN e hc
  have hA := isElemAbelian_range h.elem hBN e
  obtain ⟨T', hT2, hT, hAT⟩ := exists_stable_two_subgroup hp hp2 h hBN e
  obtain ⟨hAeq, α, hαA, hα1, hgood⟩ := sLevel_rankOne hp hZ hout h2 hfix hA hcard hT2 hT hAT
  have hαp : orderOf α = p := orderOf_eq_prime (hA.2 α hαA) hα1
  exact kConcl_of_good_element hp h hBN e hc hαA hαp hAeq hgood

end KLevel

end CFSG.LocalAnalysis.GLTheoremA.HDesc
