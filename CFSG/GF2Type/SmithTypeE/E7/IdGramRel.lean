module

public import CFSG.GF2Type.SmithTypeE.E7.IdGram
public import CFSG.GF2Type.SmithTypeE.E7.UwOrb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.GF2Type.SmithTypeE.DMod
open CFSG.SmithD6

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Distances


theorem ncard_filter_range (p : ℕ → Bool) (n : ℕ) :
    ({d : ℕ | d < n ∧ p d = true} : Set ℕ).ncard = ((List.range n).filter p).length := by
  have e : ({d : ℕ | d < n ∧ p d = true} : Set ℕ) =
      ↑((Finset.range n).filter fun d => p d = true) := by
    ext d
    simp
  rw [e, Set.ncard_coe_finset]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  apply congrArg List.length
  apply List.filter_congr
  intro x _
  simp

theorem meetCnt_eq_card {i j : ℕ} (hi : i < 75735) (hj : j < 75735) :
    meetCnt i j = Nat.card ↥(planeSub i ⊓ planeSub j) := by
  have Fi := planeFacts hi
  have Fj := planeFacts hj
  have hset : ((planeSub i ⊓ planeSub j : Submodule (ZMod 2) V12) : Set V12) =
      (fun d => dec12 (xorComb pbArr[i]! d)) ''
        {d : ℕ | d < 64 ∧ memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d) = true} := by
    ext x
    constructor
    · rintro ⟨hxi, hxj⟩
      have hxi' : x ∈ planeSpan pbArr[i]! := hxi
      have hxj' : x ∈ planeSpan pbArr[j]! := hxj
      obtain ⟨d, hd, hxd⟩ := mem_planeSpan_iff.1 hxi'
      obtain ⟨e, he, hxe⟩ := mem_planeSpan_iff.1 hxj'
      have hcode : xorComb pbArr[i]! d = xorComb pbArr[j]! e :=
        eq_of_dec12_eq (xorComb_lt Fi.lt d) (xorComb_lt Fj.lt e) (hxd.symm.trans hxe)
      have hmem : memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d) = true := by
        rw [hcode]
        exact Fj.complete e he
      exact ⟨d, ⟨hd, hmem⟩, hxd.symm⟩
    · rintro ⟨d, ⟨hd, hmem⟩, rfl⟩
      exact ⟨dec12_xorComb_mem_planeSpan _ d, dec12_mem_planeSpan_of_memR hmem⟩
  have hinj : Set.InjOn (fun d => dec12 (xorComb pbArr[i]! d))
      {d : ℕ | d < 64 ∧ memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d) = true} := by
    rintro d ⟨hd, -⟩ e ⟨he, -⟩ hde
    have hc : xorComb pbArr[i]! d = xorComb pbArr[i]! e :=
      eq_of_dec12_eq (xorComb_lt Fi.lt d) (xorComb_lt Fi.lt e) hde
    have hlt : d ^^^ e < 2 ^ 6 := Nat.xor_lt_two_pow (by norm_num; exact hd)
      (by norm_num; exact he)
    have h0 : xorComb pbArr[i]! (d ^^^ e) = 0 := by
      rw [xorComb_xor, hc, Nat.xor_self]
    rcases Fi.indep (d ^^^ e) (by norm_num at hlt; exact hlt) with h1 | h1
    · exact nat_xor_eq_zero.mp h1
    · exact absurd h0 h1
  have hcard : Nat.card ↥(planeSub i ⊓ planeSub j) =
      ((planeSub i ⊓ planeSub j : Submodule (ZMod 2) V12) : Set V12).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hset, hinj.ncard_image]
  exact (ncard_filter_range (fun d => memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d)) 64).symm

theorem meetCnt_self {i : ℕ} (hi : i < 75735) : meetCnt i i = 64 := by
  have Fi := planeFacts hi
  unfold meetCnt
  rw [List.filter_eq_self.mpr, List.length_range]
  intro d hd
  simpa using Fi.complete d (List.mem_range.mp hd)

theorem distD_self {i : ℕ} (hi : i < 75735) : distD i i = 0 := by
  unfold distD
  rw [meetCnt_self hi]
  rfl

theorem meetCnt_smul (t : TD6) (i j : Fin 75735) :
    meetCnt (t • i).val (t • j).val = meetCnt i.val j.val := by
  have hσ : Function.Injective (omegaTD6.symm t).1.toLinearMap := (omegaTD6.symm t).1.injective
  rw [meetCnt_eq_card (t • i).2 (t • j).2, meetCnt_eq_card i.2 j.2, ← map_planeSub_smul t i,
    ← map_planeSub_smul t j, ← Submodule.map_inf _ hσ]
  exact (Nat.card_congr (Submodule.equivMapOfInjective _ hσ _).toEquiv).symm

theorem distD_smul (t : TD6) (i j : Fin 75735) :
    distD (t • i).val (t • j).val = distD i.val j.val := by
  unfold distD
  rw [meetCnt_smul]

end Distances

section Relation

theorem exists_relMask
    (Γ : ℕ → ℕ → ZMod 2)
    (hconst : ∀ i j i' j' : Fin 75735, distD i j = distD i' j' → Γ i j = Γ i' j')
    (h0 : ∀ i : Fin 75735, Γ i i = 0) :
    ∃ R : ℕ, R < 16 ∧ R % 2 = 0 ∧ ∀ i j, i < 75735 → j < 75735 → Γ i j = bit (relD R i j) := by
  set r : ℕ → ZMod 2 := fun d => Classical.epsilon fun v : ZMod 2 =>
    ∃ i j : Fin 75735, distD i j = d ∧ Γ i j = v with hrdef
  have hr : ∀ i j : Fin 75735, Γ i j = r (distD i j) := by
    intro i j
    obtain ⟨i', j', hd, hv⟩ := Classical.epsilon_spec
      (p := fun v : ZMod 2 => ∃ i' j' : Fin 75735, distD i' j' = distD i j ∧ Γ i' j' = v)
      ⟨Γ i j, i, j, rfl, rfl⟩
    rw [hrdef]
    exact (hconst i j i' j' hd.symm).trans hv
  have hr0 : r 0 = 0 := by
    have h1 := hr ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
    rw [h0] at h1
    have hd : distD (⟨0, by norm_num⟩ : Fin 75735).val (⟨0, by norm_num⟩ : Fin 75735).val = 0 :=
      distD_self (by norm_num)
    rw [hd] at h1
    exact h1.symm
  have hval : ∀ a b c : ZMod 2,
      (a.val * 2 + b.val * 4 + c.val * 8 < 16 ∧ (a.val * 2 + b.val * 4 + c.val * 8) % 2 = 0) ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 0) = 0 ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 1) = a ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 2) = b ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 3) = c := by decide
  obtain ⟨⟨h16, h2⟩, b0, b1, b2, b3⟩ := hval (r 1) (r 2) (r 3)
  refine ⟨_, h16, h2, fun i j hi hj => ?_⟩
  rw [show Γ i j = r (distD i j) from hr ⟨i, hi⟩ ⟨j, hj⟩, relD]
  have hd := distD_le i j
  interval_cases h : distD i j
  · rw [b0, hr0]
  · rw [b1]
  · rw [b2]
  · rw [b3]

end Relation

section Gram


@[expose] noncomputable def gram (S : Setting G) (ψ : S.Mbar ≃* TD6) (g : G) (i j : ℕ) :
    ZMod 2 :=
  polar S.q (xcl S ψ g i) (xcl S ψ g j)

theorem gram_self (ψ : S.Mbar ≃* TD6) (g : G) (i : ℕ) : gram S ψ g i i = 0 := by
  rw [gram, polar_self]
  generalize S.q (xcl S ψ g i) = a
  revert a
  decide


theorem gram_smul [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16) (ψ : S.Mbar ≃* TD6)
    {g : G} (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (t : TD6) (i j : Fin 75735) :
    gram S ψ g (t • i).val (t • j).val = gram S ψ g i.val j.val := by
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm t)
  have ht : ψ (rhoM S m) = t := by rw [hm, MulEquiv.apply_symm_apply]
  unfold gram
  rw [← ht, ← xcl_smul I hw ψ hψ haQ hne m i, ← xcl_smul I hw ψ hψ haQ hne m j]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m).2 _ _

theorem gram_eq_of_distD_eq [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (ψ : S.Mbar ≃* TD6) {g : G}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {i j i' j' : ℕ}
    (hi : i < 75735) (hj : j < 75735) (hi' : i' < 75735) (hj' : j' < 75735)
    (h : distD i j = distD i' j') : gram S ψ g i j = gram S ψ g i' j' := by
  obtain ⟨t, ht⟩ := exists_smul_planes_eq ⟨i, hi⟩ 0
  obtain ⟨t', ht'⟩ := exists_smul_planes_eq ⟨i', hi'⟩ 0
  obtain ⟨s, hs, hsJ⟩ := exists_stab0_image_distD (j := t • (⟨j, hj⟩ : Fin 75735))
    (j' := t' • (⟨j', hj'⟩ : Fin 75735)) (by
      have d1 := distD_smul t ⟨i, hi⟩ ⟨j, hj⟩
      have d2 := distD_smul t' ⟨i', hi'⟩ ⟨j', hj'⟩
      rw [ht] at d1
      rw [ht'] at d2
      exact d1.trans (h.trans d2.symm))
  have e1 : gram S ψ g i j = gram S ψ g 0 (t • (⟨j, hj⟩ : Fin 75735)).val := by
    have := gram_smul I hw ψ hψ haQ hne t ⟨i, hi⟩ ⟨j, hj⟩
    rw [ht] at this
    exact this.symm
  have e2 : gram S ψ g i' j' = gram S ψ g 0 (t' • (⟨j', hj'⟩ : Fin 75735)).val := by
    have := gram_smul I hw ψ hψ haQ hne t' ⟨i', hi'⟩ ⟨j', hj'⟩
    rw [ht'] at this
    exact this.symm
  have e3 : gram S ψ g 0 (s • (t • (⟨j, hj⟩ : Fin 75735))).val =
      gram S ψ g 0 (t • (⟨j, hj⟩ : Fin 75735)).val := by
    have := gram_smul I hw ψ hψ haQ hne s 0 (t • (⟨j, hj⟩ : Fin 75735))
    rw [MulAction.mem_stabilizer_iff.mp hs] at this
    exact this
  rw [e1, e2, ← hsJ]
  exact e3.symm

theorem xcl_ne_zero [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16) (ψ : S.Mbar ≃* TD6)
    {g : G} (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {i : ℕ} (hi : i < 75735) :
    xcl S ψ g i ≠ 0 := by
  obtain ⟨h, hh⟩ := planeOfPsi_surj ψ ⟨i, hi⟩
  rw [xcl_eq_cl I hw ψ hψ haQ hne i (h := h) (by rw [hh])]
  obtain ⟨hbQ, hbne⟩ := mul_conj_mem h haQ hne
  exact S.cl_conj_z_ne_zero hbQ hbne

theorem gram_zero_false [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16) (ψ : S.Mbar ≃* TD6)
    {g : G} (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hz : ∀ i j : ℕ, i < 75735 → j < 75735 → polar S.q (xcl S ψ g i) (xcl S ψ g j) = 0) :
    False := by
  have hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) := ⟨ψ.trans omegaTD6.symm⟩
  have hsp : Submodule.span (ZMod 2) (Set.range fun i : Fin 75735 => xcl S ψ g i.val) = ⊤ := by
    by_contra hW
    apply irreducible I.hDW hw hO haQ hne
    refine ⟨Submodule.span (ZMod 2) (Set.range fun i : Fin 75735 => xcl S ψ g i.val), ?_, hW,
      fun m v hv => ?_⟩
    · intro hbot
      have h0 : xcl S ψ g 0 ∈ Submodule.span (ZMod 2)
          (Set.range fun i : Fin 75735 => xcl S ψ g i.val) :=
        Submodule.subset_span ⟨⟨0, by norm_num⟩, rfl⟩
      rw [hbot] at h0
      exact xcl_ne_zero I hw ψ hψ haQ hne (i := 0) (by norm_num) ((Submodule.mem_bot _).mp h0)
    · have hle : Submodule.span (ZMod 2) (Set.range fun i : Fin 75735 => xcl S ψ g i.val) ≤
          (Submodule.span (ZMod 2) (Set.range fun i : Fin 75735 => xcl S ψ g i.val)).comap
            ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap]
        show ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (xcl S ψ g i.val) ∈ _
        rw [xcl_smul I hw ψ hψ haQ hne m i]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact hle hv
  have hB : S.q.polarBilin = 0 := by
    refine LinearMap.ext_on_range hsp fun i => LinearMap.ext_on_range hsp fun j => ?_
    rw [polarBilin_apply_apply, LinearMap.zero_apply, LinearMap.zero_apply]
    exact hz i.val j.val i.2 j.2
  have hpos : 0 < Module.finrank (ZMod 2) S.Qt := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
    norm_num
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  exact hv (S.q_nondegenerate.1 v fun w => by rw [hB]; rfl)

theorem gram_eq_bit_eight [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (ψ : S.Mbar ≃* TD6) {g : G}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {i j : ℕ} (hi : i < 75735)
    (hj : j < 75735) : gram S ψ g i j = bit (relD 8 i j) := by
  obtain ⟨R, h16, h2, hR⟩ := exists_relMask (gram S ψ g)
    (fun i j i' j' h => gram_eq_of_distD_eq I hw ψ hψ haQ hne i.2 j.2 i'.2 j'.2 h)
    (fun i : Fin 75735 => gram_self ψ g i.val)
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) S.Qt ≤ 32 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  rcases rel_eq_of_gram h16 h2 hdim S.q.polarBilin (xcl S ψ g)
      (fun i j hi hj => by rw [polarBilin_apply_apply]; exact hR i j hi hj) with rfl | rfl
  · exfalso
    refine gram_zero_false I hw ψ hψ haQ hne (fun i j hi hj => ?_)
    have h0 : bit (relD 0 i j) = 0 := by simp [relD, bit]
    exact (hR i j hi hj).trans h0
  · exact hR i j hi hj

open Classical in
theorem gram_eq_opp [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (ψ : S.Mbar ≃* TD6) {g : G}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {i j : ℕ} (hi : i < 75735)
    (hj : j < 75735) :
    polar S.q (xcl S ψ g i) (xcl S ψ g j) = if Opp i j then 1 else 0 := by
  rw [← gram, gram_eq_bit_eight I hw ψ hψ haQ hne hi hj]
  by_cases h : Opp i j
  · rw [(relD_eight_iff hi hj).2 h]
    simp [h, bit]
  · have h' : relD 8 i j = false := by
      cases h' : relD 8 i j
      · rfl
      · exact absurd ((relD_eight_iff hi hj).1 h') h
    rw [h']
    simp [h, bit]

end Gram

end CFSG.GF2Type.SmithTypeE.E7
