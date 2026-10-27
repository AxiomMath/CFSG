module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.OddCorePrime
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.OddCoreBound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Burnside
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Klein

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped Pointwise

theorem five_odd_core (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hCent : FiveCentFacts a z) (hS7 : S7Facts a z) (hGam : GammaFacts a z) :
    FiveCoreFacts a z := by
  refine { hCent with odd_core := ?_ }
  intro ρ hρ h5 hshape T
  obtain ⟨z', hz'conj, haz'conj, _, hT0, hpadic⟩ := hCent.sylow ρ hρ h5 hshape T
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have ha : a * a = 1 := by simpa [pow_two] using ha2
  have hz'2ord : orderOf z' = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hz'conj
    rw [← hc]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) z).trans h.orderOf_z
  have hz' : z' * z' = 1 := by
    have : z' ^ 2 = 1 := by rw [← hz'2ord]; exact pow_orderOf_eq_one z'
    simpa [pow_two] using this
  have ha1 : a ≠ 1 := by
    intro h1
    have : orderOf a = 1 := orderOf_eq_one_iff.mpr h1
    rw [h.orderOf_a] at this
    exact (by norm_num : (2 : ℕ) ≠ 1) this
  have hz'1 : z' ≠ 1 := by
    intro h1
    have : orderOf z' = 1 := orderOf_eq_one_iff.mpr h1
    rw [hz'2ord] at this
    exact (by norm_num : (2 : ℕ) ≠ 1) this
  have hne : a ≠ z' := by
    intro h1
    exact not_isConj_of_isF5Type hI h (by rw [h1]; exact hz'conj.symm)
  have hz'cl : z' ∈ Subgroup.closure ({a, z'} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hz'Gxy : z' ∈ Gxy a ρ :=
    Subgroup.map_subtype_le (T : Subgroup ↥(Gxy a ρ)) (hT0.symm ▸ hz'cl)
  have huK : z' ∈ Gx ρ := (mem_Gxy.mp hz'Gxy).2
  have hau : a * z' = z' * a := mem_Gx.mp (mem_Gxy.mp hz'Gxy).1
  have haK : a ∈ Gx ρ := mem_Gx.mpr (mem_Gx.mp hρ).symm
  have hfix : ∀ n ∈ Gx ρ, n ∈ Subgroup.normalizer
      ((Subgroup.closure ({a, z'} : Set G) : Subgroup G) : Set G) → n * a = a * n := by
    intro n _ hnN
    have hna : n * a * n⁻¹ ∈ Subgroup.closure ({a, z'} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hnN a).mp (Subgroup.subset_closure (by simp))
    rcases (mem_closure_pair_iff_of_involutions ha hz' hau).mp hna with h1 | h2 | h3 | h4
    · exfalso
      exact ha1 (isConj_one_left.mp (isConj_iff.mpr ⟨n, h1⟩))
    · calc n * a = (n * a * n⁻¹) * n := by group
        _ = a * n := by rw [h2]
    · exfalso
      exact not_isConj_of_isF5Type hI h
        ((isConj_iff.mpr ⟨n, h3⟩ : IsConj a z').trans hz'conj.symm)
    · exfalso
      exact not_isConj_of_isF5Type hI h
        ((isConj_iff.mpr ⟨n, h4⟩ : IsConj a (a * z')).trans haz'conj.symm)
  obtain ⟨N, hNK, hNn, hodd, hNinf, hNsup⟩ :=
    exists_normal_two_complement_of_klein (K := Gx ρ) (a := a) (u := z')
      haK huK ha hz' hau ha1 hz'1 hne hpadic hfix
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Nonempty ↥N := ⟨⟨1, N.one_mem⟩⟩
  have hN5 : IsPGroup 5 ↥N := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.card ↥N).primeFactorsList.length, ?_⟩
    exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdvd =>
        five_odd_core_prime hI h hCent hS7 hGam hρ h5 hshape hNK hNn hodd hd hdvd)
  have hNconj : ∀ h k : G, h ∈ N → k ∈ Gx ρ → k * h * k⁻¹ ∈ N :=
    (Subgroup.normal_subgroupOf_iff hNK).mp hNn
  have ht2_of : ∀ t : G, t ∈ Subgroup.closure ({a, z'} : Set G) → t * t = 1 := by
    intro t ht
    rcases (mem_closure_pair_iff_of_involutions ha hz' hau).mp ht with h1 | h2 | h3 | h4
    · rw [h1]; simp
    · rw [h2]; exact ha
    · rw [h3]; exact hz'
    · rw [h4]
      have hza : z' * a = a * z' := hau.symm
      calc (a * z') * (a * z') = a * (z' * a) * z' := by group
        _ = a * (a * z') * z' := by rw [hza]
        _ = (a * a) * (z' * z') := by group
        _ = 1 := by rw [ha, hz', mul_one]
  haveI : (N.subgroupOf (Gx ρ)).Normal := hNn
  have hT0K : Subgroup.closure ({a, z'} : Set G) ≤ Gx ρ := by
    refine (Subgroup.closure_le (Gx ρ)).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact haK
    · exact huK
  have hle : Subgroup.closure ({a, z'} : Set G) ≤ Subgroup.normalizer N :=
    hT0K.trans (Subgroup.le_normalizer_of_normal_subgroupOf hNK)
  have hρmem : ρ ∈ N ⊔ Subgroup.closure ({a, z'} : Set G) := by
    rw [hNsup]
    exact self_mem_Gx ρ
  have hmemmul : ρ ∈ (N : Set G) * (Subgroup.closure ({a, z'} : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N _ hle]
    exact hρmem
  obtain ⟨n, hnN, t, htT0, hnt⟩ := Set.mem_mul.mp hmemmul
  have ht2 : t * t = 1 := ht2_of t htT0
  have htK : t ∈ Gx ρ :=
    (mem_Gxy.mp (Subgroup.map_subtype_le (T : Subgroup ↥(Gxy a ρ)) (hT0.symm ▸ htT0))).2
  have hm : t * n * t⁻¹ ∈ N := hNconj n t hnN htK
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hm' : t * n * t ∈ N := by simpa only [htinv] using hm
  have hsquare : ρ ^ 2 ∈ N := by
    rw [← hnt, pow_two]
    have hcalc : (n * t) * (n * t) = n * (t * n * t) := by group
    rw [hcalc]
    exact mul_mem hnN hm'
  have hρ5 : ρ ^ 5 = 1 := by rw [← h5]; exact pow_orderOf_eq_one ρ
  have hρ6 : ρ ^ 6 = ρ := by
    rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_succ, hρ5, one_mul]
  have hρ_eq : (ρ ^ 2) ^ 3 = ρ := by
    rw [(pow_mul ρ 2 3).symm, show 2 * 3 = 6 by norm_num, hρ6]
  have hρN : ρ ∈ N := hρ_eq ▸ pow_mem hsquare 3
  have hbound : Nat.card ↥N ≤ 5 ^ 4 :=
    five_odd_core_bound hI h hz'conj haz'conj hρ h5 hshape hz'Gxy hNK hNn hN5 hρN
  exact ⟨N, hNK, hNn, hN5, hbound, by rw [hT0]; exact hNsup, by rw [hT0]; exact hNinf⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
