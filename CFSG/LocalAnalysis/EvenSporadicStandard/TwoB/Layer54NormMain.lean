module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54NormComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54NormChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54NormHeis
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54NormT

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.SemisimpleComponentStructure
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem Level55.conj_t_mem_compG (d : Level55 G t z)
    (hM : (layer ↥(centZ z)).map (centZ z).subtype ⊓ centPair z t ≤ O2In (centPair z t))
    (i : ComponentIndex ↥(centZ z)) : ∀ n ∈ compG z i, t * n * t⁻¹ ∈ compG z i := by
  have htt : t * t = 1 := by rw [← pow_two, ← d.t_ord]; exact pow_orderOf_eq_one t
  have htc : t ∈ centZ z := mem_centralizer_singleton_iff.2 d.zt_comm.symm
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hY : O2In (centPair z t) ≤ centZ z := (O2In_le _).trans hKC
  let tH : ↥(centZ z) := ⟨t, htc⟩
  have htH : tH * tH = 1 := Subtype.ext htt
  let S : Subgroup ↥(centZ z) := (O2In (centPair z t)).subgroupOf (centZ z)
  have hSp : IsPGroup 2 ↥S :=
    (isPGroup_O2In (centPair z t)).of_equiv (Subgroup.subgroupOfEquivOfLe hY).symm
  have : Group.IsNilpotent ↥S := hSp.isNilpotent
  have hS : ∀ x ∈ Layer.subgroup ↥(centZ z), x * tH = tH * x → x ∈ S := by
    intro x hx hxt
    have hxE : (x : G) ∈ (layer ↥(centZ z)).map (centZ z).subtype :=
      ⟨x, by rwa [layer_eq_componentClassification], rfl⟩
    have hxK : (x : G) ∈ centPair z t :=
      mem_centPair_iff.2 ⟨(mem_centralizer_singleton_iff.1 x.2).symm,
        (congrArg Subtype.val hxt).symm⟩
    exact mem_subgroupOf.2 (hM ⟨hxE, hxK⟩)
  have hT := Layer54.map_conj_eq S htH hS i
  intro n hn
  obtain ⟨a, ha, rfl⟩ := hn
  have h1 : (MulAut.conj tH).toMonoidHom a ∈ i.val := hT ▸ Subgroup.mem_map_of_mem _ ha
  exact ⟨_, h1, by simp [tH, MulAut.conj_apply]⟩

theorem Level55.mem_normAll_of_order23 (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) (hP : Psub z = zpowers z)
    (hM : (layer ↥(centZ z)).map (centZ z).subtype ⊓ centPair z t ≤ O2In (centPair z t))
    {σ : G} (hσK : σ ∈ centPair z t) (hσ : orderOf σ = 23) : σ ∈ normAll z t := by
  rw [mem_normAll]
  refine ⟨hσK, ?_⟩
  by_contra hnot
  push Not at hnot
  obtain ⟨i0, n0, hn0, hn0'⟩ := hnot
  have htt : t * t = 1 := by rw [← pow_two, ← d.t_ord]; exact pow_orderOf_eq_one t
  have htc : t ∈ centZ z := mem_centralizer_singleton_iff.2 d.zt_comm.symm
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hnormσ : σ ∉ normalizer ((compG z i0 : Subgroup G) : Set G) := fun h =>
    hn0' ((mem_normalizer_iff.1 h n0).1 hn0)
  let Qs : ℕ → Subgroup G := fun j => (compG z i0).map (MulAut.conj (σ ^ j)).toMonoidHom
  have hQs : ∀ j, ∃ ij : ComponentIndex ↥(centZ z), compG z ij = Qs j := fun j =>
    exists_compG_conj (hKC (pow_mem hσK j)) i0
  choose iq hiq using hQs
  obtain ⟨s, hs, hsc, q0, hq0, hsq0⟩ :=
    exists_noncentral_s hodd hP htt htc i0 (d.conj_t_mem_compG hM i0)
  let sj : ℕ → G := fun j => σ ^ j * s * (σ ^ j)⁻¹
  have hsj : ∀ j, sj j ∈ compG z (iq j) := fun j => by
    rw [hiq j]
    exact ⟨s, hs, rfl⟩
  have hdist : ∀ j k : ℕ, j < k → k < 23 → compG z (iq j) ≠ compG z (iq k) := by
    intro j k hjk hk
    rw [hiq j, hiq k]
    exact map_conj_pow_ne hσ hnormσ hjk hk
  have hcomm : ∀ j < 23, ∀ k < 23, j ≠ k → ∀ x ∈ Qs j, ∀ y ∈ Qs k, x * y = y * x := by
    intro j _ k hk23 hjk x hx y hy
    rw [← hiq j] at hx
    rw [← hiq k] at hy
    rcases lt_or_gt_of_ne hjk with h | h
    · exact compG_comm (hdist j k h hk23) hx hy
    · exact (compG_comm (hdist k j h (by omega)) hy hx).symm
  have hnc : ∀ j < 23, ∃ q ∈ Qs j, sj j * q ≠ q * sj j := by
    intro j _
    refine ⟨σ ^ j * q0 * (σ ^ j)⁻¹, ⟨q0, hq0, rfl⟩, fun h => hsq0 ?_⟩
    have h' : σ ^ j * (s * q0) * (σ ^ j)⁻¹ = σ ^ j * (q0 * s) * (σ ^ j)⁻¹ := by
      calc σ ^ j * (s * q0) * (σ ^ j)⁻¹
          = sj j * (σ ^ j * q0 * (σ ^ j)⁻¹) := by simp only [sj]; group
        _ = (σ ^ j * q0 * (σ ^ j)⁻¹) * sj j := h
        _ = σ ^ j * (q0 * s) * (σ ^ j)⁻¹ := by simp only [sj]; group
    exact mul_left_cancel (mul_right_cancel h')
  have hsmem : ∀ j < 23, sj j ∈ Qs j := fun j _ => by rw [← hiq j]; exact hsj j
  have h23 := two_pow_le_card_closure_of_noncomm Qs sj 23 hsmem hcomm hnc
  have hAcomm := closure_comm_of_noncomm Qs sj 23 hsmem hcomm
  set A : Subgroup G := closure (sj '' Set.Iio 23) with hA
  have hs0 : s ∈ centZ z := compG_le_centZ i0 hs
  have hsn : s ∈ normPair z t := mem_normPair_of_comm_mem_zpowers hs0 hsc
  have hAC : A ≤ centZ z := by
    rw [hA, closure_le]
    rintro _ ⟨j, _, rfl⟩
    exact compG_le_centZ (iq j) (hsj j)
  have hAn : A ≤ normPair z t := by
    rw [hA, closure_le]
    rintro _ ⟨j, _, rfl⟩
    exact mul_mem (mul_mem (centPair_le_normPair z t (pow_mem hσK j)) hsn)
      (inv_mem (centPair_le_normPair z t (pow_mem hσK j)))
  have hAE : A ≤ (layer ↥(centZ z)).map (centZ z).subtype := by
    rw [hA, closure_le]
    rintro _ ⟨j, _, rfl⟩
    exact compG_le_layer (iq j) (hsj j)
  have hBY : centPair z t ⊓ A ≤ O2In (centPair z t) := fun b hb => hM ⟨hAE hb.2, hb.1⟩
  have hcard := d.card_le_two_mul_card_inf hAC hAn
  have hY : O2In (centPair z t) ≤ centZ z := (O2In_le _).trans hKC
  have hheis := card_sq_le_of_commutators_mem_zpowers (z := z) d.z_mul_self (O2In (centPair z t))
    (fun y hy => (mem_centPair_iff.1 (O2In_le _ hy)).1.symm)
    (fun a ha b hb => d.O2K_commutator_mem_zpowers ha hb) (centPair z t ⊓ A) hBY
    (fun a ha b hb => hAcomm a ha.2 b hb.2)
  have hZ : Nat.card (O2In (centPair z t) ⊓ centralizer ((O2In (centPair z t) : Subgroup G) :
      Set G) : Subgroup G) ≤ 4 := by
    refine (Subgroup.card_le_of_le (K := pair z t) ?_).trans
      (card_pair_le d.z_ord d.t_ord d.zt_comm)
    intro c hc
    exact d.mem_pair_of_central hc.1 fun r hr => (mem_centralizer_iff.1 hc.2 r hr).symm
  rw [d.card_O2K] at hheis
  have h22 : 2 ^ 22 ≤ Nat.card (centPair z t ⊓ A : Subgroup G) := by
    have : 2 ^ 23 ≤ 2 * Nat.card (centPair z t ⊓ A : Subgroup G) := h23.trans hcard
    omega
  generalize Nat.card (centPair z t ⊓ A : Subgroup G) = b at h22 hheis
  generalize Nat.card (O2In (centPair z t) ⊓ centralizer ((O2In (centPair z t) : Subgroup G) :
    Set G) : Subgroup G) = c at hheis hZ
  have h44 : 2 ^ 44 ≤ b ^ 2 :=
    calc 2 ^ 44 = (2 ^ 22) ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left h22 2
  omega

section Certified


theorem Level55.conj_mem_component (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) (hP : Psub z = zpowers z)
    (i : ComponentIndex ↥(centZ z)) {k : G} (hk : k ∈ centPair z t) {n : G}
    (hn : n ∈ i.val.map (centZ z).subtype) : k * n * k⁻¹ ∈ i.val.map (centZ z).subtype := by
  by_cases hKE : centPair z t ≤ (layer ↥(centZ z)).map (centZ z).subtype
  · exact conj_mem_map_component hKE i hk hn
  · have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
    have hM : (layer ↥(centZ z)).map (centZ z).subtype ⊓ centPair z t ≤ O2In (centPair z t) := by
      by_contra hnle
      have hinv : ∀ k ∈ centPair z t, ∀ m ∈ (layer ↥(centZ z)).map (centZ z).subtype ⊓
          centPair z t, k * m * k⁻¹ ∈ (layer ↥(centZ z)).map (centZ z).subtype ⊓
          centPair z t := by
        intro k hk m hm
        obtain ⟨e, he, rfl⟩ := (mem_inf.1 hm).1
        have he' : e ∈ Layer.subgroup ↥(centZ z) := by rwa [← layer_eq_componentClassification]
        have h1 := (Layer.normal ↥(centZ z)).conj_mem e he' ⟨k, hKC hk⟩
        exact mem_inf.2 ⟨⟨⟨k, hKC hk⟩ * e * ⟨k, hKC hk⟩⁻¹,
          by rwa [layer_eq_componentClassification], rfl⟩,
          mul_mem (mul_mem hk (mem_inf.1 hm).2) (inv_mem hk)⟩
      have heq := d.eq_K_of_not_le_O2K inf_le_right hinv hnle
      exact hKE (heq ▸ inf_le_left)
    obtain ⟨σ, hσK, hσ⟩ := d.exists_order23_mem_K
    have hσN := d.mem_normAll_of_order23 hodd hP hM hσK hσ
    have hσY : σ ∉ O2In (centPair z t) := by
      intro h
      obtain ⟨m, hm⟩ := isPGroup_O2In (centPair z t) ⟨σ, h⟩
      have hm' : σ ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hdvd : orderOf σ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
      rw [hσ] at hdvd
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 23) hdvd
      omega
    have heq := d.normAll_eq_of_not_le fun h => hσY (h hσN)
    exact (mem_normAll.1 (heq ▸ hk)).2 i n hn

end Certified

end CFSG.EvenSporadicStandard.TwoB
