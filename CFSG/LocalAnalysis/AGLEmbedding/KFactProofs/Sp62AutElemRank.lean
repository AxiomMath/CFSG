module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalAut
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open KFactProofs.Sp62Local
open scoped Pointwise

namespace KFactProofs.Sp62Local

theorem T0_not_commutative :
    ∃ a ∈ T0, ∃ b ∈ T0, a * b ≠ b * a := by
  have hgenE := (tabCheck_spec tabCheck_E).2.2.2.2
  have hsgE : cSg ∈ gensE := by simp [gensE]
  have hbeE : cBeta ∈ gensE := by simp [gensE]
  refine ⟨elt cSg, E0_le_T0 (elt_mem_Hgen hsgE), elt cBeta, E0_le_T0 (elt_mem_Hgen hbeE),
    fun h => ?_⟩
  have h3 : (!(commB cSg cBeta)) = true := E0_spec.2.2.1
  have h4 := ((rep_elt (genB_isoB (hgenE _ hsgE))).comm_iff
    (rep_elt (genB_isoB (hgenE _ hbeE)))).1 h
  simp [commB, h4] at h3

theorem card_le_of_isElemAbelian_H6 {E : Subgroup H6}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H6 T0S S
  have hSeq : (S : Subgroup H6) = MulAut.conj g • T0 := by
    rw [← hg, Sylow.coe_subgroup_smul, coe_T0S]
  have hScard : Nat.card S = 3 ^ 4 := by
    have h1 := Sylow.card_eq_multiplicity S
    have h2 := Sylow.card_eq_multiplicity T0S
    rw [coe_T0S, card_T0] at h2
    rw [h1, ← h2]
  have hdvd : Nat.card E ∣ 3 ^ 4 := hScard ▸ Subgroup.card_dvd_of_le hES
  by_contra hlt
  push Not at hlt
  have h81 : Nat.card E = 3 ^ 4 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hk3 : 3 < k := by
      by_contra hk3
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hk', show k = 4 by omega]
  have hES' : E = (S : Subgroup H6) :=
    Subgroup.eq_of_le_of_card_ge hES (by rw [hScard, h81])
  obtain ⟨a, ha, b, hb, hab⟩ := T0_not_commutative
  apply hab
  have hmem : ∀ x ∈ T0, MulAut.conj g x ∈ E := fun x hx => by
    rw [hES', hSeq]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have hcomm := hE.1.is_comm.comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩
  apply (MulAut.conj g).injective
  rw [map_mul, map_mul]
  exact congrArg Subtype.val hcomm

end KFactProofs.Sp62Local

theorem kFactSp62AutElemRank : KFactSp62AutElemRank := by
  intro L _ _ d hd ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨i, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨e₂⟩ := CFSG.RankThree.PartTwo.Census.nonempty_typeBGroupEquiv_sp6 q hv hqp hqe
  let eL : L ≃* H6 := e.trans e₂
  have hsimple : IsSimpleGroup L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 q.p q.exponent
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hqp le_rfl e)
  have hcen : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, -, b, -, hab⟩ := T0_not_commutative
      apply hab
      have hmem : eL.symm a ∈ Subgroup.center L := h ▸ Subgroup.mem_top _
      have h1 := (Subgroup.mem_center_iff.mp hmem (eL.symm b)).symm
      simpa using congrArg eL h1
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hc : x ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun y => by
      have h1 := congrArg (fun f : MulAut L => f y) hx
      change x * y * x⁻¹ = y at h1
      calc y * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    rw [hcen, Subgroup.mem_bot] at hc
    exact hc
  have hall : ∀ α : MulAut L, ∃ x : L, α = MulAut.conj x := by
    intro α
    obtain ⟨g, hg⟩ := all_inner_H6 (MulAut.congr eL α)
    refine ⟨eL.symm g, (MulAut.congr eL).injective ?_⟩
    rw [hg, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj, MulEquiv.apply_symm_apply]
  have hsurj : Function.Surjective (MulAut.conj : L →* MulAut L) := fun α => (hall α).imp
    fun _ h => h.symm
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, -, hE, hk⟩
  set E' := E.comap (MulAut.conj : L →* MulAut L) with hE'
  have hmap : E'.map (MulAut.conj : L →* MulAut L) = E :=
    Subgroup.map_comap_eq_self_of_surjective hsurj E
  have hE'card : Nat.card E' = Nat.card E := by
    have := Subgroup.card_map_of_injective hinj (K := E')
    rw [hmap] at this
    exact this.symm
  have hE'e : IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  have hH6 := card_le_of_isElemAbelian_H6 (elementary_abelian_map 3 hE'e eL.toMonoidHom)
  rw [Subgroup.card_map_of_injective eL.injective, hE'card, hk] at hH6
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hH6

end CFSG.AGLEmbedding
