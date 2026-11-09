module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AltSixCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

open CFSG.Permutation.FinPack
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup in
theorem alt6_o3_invol_walk : walkK 6 (fun t => !evenK 6 t ||
    !Nat.beq (mulK 6 t t) (enc (1 : Equiv.Perm (Fin 6))) || Nat.beq t (enc (1 : Equiv.Perm (Fin 6))) ||
      allK (fun c => !commLaneK 6 c t) evenOrder3Codes) 6 0 0 0 = true := by
  decide +kernel

open CFSG.Permutation.FinPack
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup in
theorem alt6_order3_not_comm_invol :
    ∀ g w : alternatingGroup (Fin 6), g ^ 3 = 1 → g ≠ 1 → w ^ 2 = 1 → w ≠ 1 → g * w ≠ w * g := by
  have hn : 6 ≤ 16 := by norm_num
  intro g w hg3 hg1 hw2 hw1 hc
  have hg3' : (g : Equiv.Perm (Fin 6)) ^ 3 = 1 := by simpa using congrArg Subtype.val hg3
  have hg1' : (g : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hg1 (Subtype.ext (by simpa using h))
  have hgs : Equiv.Perm.sign (g : Equiv.Perm (Fin 6)) = 1 := Equiv.Perm.mem_alternatingGroup.1 g.2
  have hws : Equiv.Perm.sign (w : Equiv.Perm (Fin 6)) = 1 := Equiv.Perm.mem_alternatingGroup.1 w.2
  have hw2' : (w : Equiv.Perm (Fin 6)) * w = 1 := by
    rw [← sq]; simpa using congrArg Subtype.val hw2
  have hw1' : (w : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hw1 (Subtype.ext (by simpa using h))
  have hc' : (g : Equiv.Perm (Fin 6)) * w = w * g := by simpa using congrArg Subtype.val hc
  have hg := evenOrder3Codes_complete _ hg3' hg1' hgs
  have h := walkK_sound alt6_o3_invol_walk (w : Equiv.Perm (Fin 6))
  simp only [evenK_enc_eq_decide hn, mulK_enc hn, beq_enc_eq_decide hn, hws, hw2', hw1',
    decide_true, decide_false, Bool.not_true, Bool.false_or] at h
  have h' := allK_iff.1 h _ (memK_iff.1 hg)
  rw [commLaneK_enc_eq_decide hn] at h'
  simp [hc'] at h'

theorem alt6_center_trivial :
    ∀ g : alternatingGroup (Fin 6), (∀ h : alternatingGroup (Fin 6), g * h = h * g) → g = 1 := by
  decide +kernel

private theorem conj_range_normal (S : Type) [Group S] :
    ((MulAut.conj : S →* MulAut S).range).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, ?_⟩
    ext x
    simp [MulAut.conj_apply]

abbrev A6 : Type := alternatingGroup (Fin 6)

private theorem conj_injective_a6 : Function.Injective (MulAut.conj : A6 →* MulAut A6) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  refine (Subgroup.mem_bot).2 (alt6_center_trivial g fun h => ?_)
  have := congrArg (fun φ : MulAut A6 => φ h) hg
  simpa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using this

theorem alt6_aut_three_inner (α : MulAut A6) (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : A6 →* MulAut A6).range := by
  classical
  haveI : ((MulAut.conj : A6 →* MulAut A6).range).Normal := conj_range_normal A6
  have hcardA : Nat.card A6 = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hcardH : Nat.card ((MulAut.conj : A6 →* MulAut A6).range) = 360 := by
    rw [← hcardA]
    exact (Nat.card_congr (MonoidHom.ofInjective conj_injective_a6).toEquiv).symm
  have hAut : Nat.card (MulAut A6) = 1440 :=
    CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6
  have hQ : Nat.card (MulAut A6 ⧸ (MulAut.conj : A6 →* MulAut A6).range) = 4 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAut.conj : A6 →* MulAut A6).range
    rw [hAut, hcardH] at this
    omega
  have h4 : (QuotientGroup.mk α : MulAut A6 ⧸ (MulAut.conj : A6 →* MulAut A6).range) ^ 4 = 1 := by
    rw [← hQ]
    exact pow_card_eq_one'
  have h3 : (QuotientGroup.mk α : MulAut A6 ⧸ (MulAut.conj : A6 →* MulAut A6).range) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h1 := (pow_gcd_eq_one (a := (QuotientGroup.mk α : MulAut A6 ⧸ (MulAut.conj : A6 →* MulAut A6).range))).2 ⟨h4, h3⟩
  have : Nat.gcd 4 3 = 1 := by norm_num
  rw [this, pow_one] at h1
  exact (QuotientGroup.eq_one_iff α).1 h1

theorem noInvCent_alt6 : ∀ α : MulAut A6, α ^ 3 = 1 → α ≠ 1 →
    ∀ w : A6, w ^ 2 = 1 → w ≠ 1 → α w ≠ w := by
  intro α hα3 hα1 w hw2 hw1 hfix
  obtain ⟨g, rfl⟩ := alt6_aut_three_inner α hα3
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hg3 : g ^ 3 = 1 := by
    have h : (MulAut.conj g) ^ 3 = MulAut.conj (g ^ 3) := (map_pow _ _ _).symm
    rw [h] at hα3
    exact conj_injective_a6 (hα3.trans (map_one _).symm)
  have hcomm : g * w = w * g := by
    have h := hfix
    rw [MulAut.conj_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h)
  exact alt6_order3_not_comm_invol g w hg3 hg1 hw2 hw1 hcomm

theorem kDescFam_alt6 (p : ℕ) : KDescFam p fAlt6 := by
  intro hp hp2 Y _ _ K B h hc hcB
  obtain ⟨i, hi, ⟨eK⟩⟩ := hc
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn =>
    change n = 6 at hi
    subst hi
    by_cases hp3 : p = 3
    · subst hp3
      exact (false_of_noInvCent hp hp2 h hcB eK noInvCent_alt6).elim
    · exact Or.inl (kConcl_of_alt6 hp hp2 hp3 h eK)

end CFSG.LocalAnalysis.GLTheoremA
