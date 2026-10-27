module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

private lemma le_zpowers_of_pow_three_eq_one {Y : Type} [Group Y] {z : Y} {C E : Subgroup Y}
    (hC : ∀ c ∈ C, orderOf c = 3 → c ∈ zpowers z) (hEC : E ≤ C) (hE : ∀ x ∈ E, x ^ 3 = 1) :
    E ≤ zpowers z := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  · exact hC x (hEC hx) (orderOf_eq_prime (hE x hx) hx1)

private lemma isMulCommutative_of_orderOf_eq_three {Y : Type} [Group Y] [Finite Y] {z : Y}
    {C : Subgroup Y} (hz3 : orderOf z = 3) (hCp : IsPGroup 3 C)
    (hC : ∀ c ∈ C, orderOf c = 3 → c ∈ zpowers z) : IsMulCommutative C := by
  by_contra hcomm
  have hnc : ¬ IsCyclic C := fun h => hcomm h.isMulCommutative
  have h2 : 2 ≤ CFSG.Open.pRank 3 C :=
    two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hCp hnc
  obtain ⟨E, hEC, hE, hcard⟩ := pRank_attained 3 C (by omega)
  have hEz : E ≤ zpowers z := le_zpowers_of_pow_three_eq_one hC hEC hE.2
  have h9 : 3 ^ 2 ≤ Nat.card E := hcard ▸ Nat.pow_le_pow_right (by norm_num) h2
  have h3 : Nat.card E ≤ 3 := (card_le_of_le hEz).trans (by rw [Nat.card_zpowers, hz3])
  omega

private lemma not_forall_mul_comm_inf_of_isPerfect {Y : Type} [Group Y] [Finite Y]
    (R : Sylow 3 Y) (K : Subgroup Y) [K.Normal] {z : Y} (hK : commutator K = ⊤) (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, z * k = k * z) (hz3 : orderOf z = 3) :
    ¬ ∀ s ∈ (R : Subgroup Y) ⊓ K, ∀ s' ∈ (R : Subgroup Y) ⊓ K, s * s' = s' * s := by
  intro hcomm
  obtain ⟨S, hS⟩ := CFSG.Glauberman.sylow_inf_normal R (N := K)
  have hz1 : (⟨z, hzK⟩ : K) ≠ 1 := fun h => by
    have : z = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hz3
    omega
  have hzp : z ^ 3 = 1 := by simpa [hz3] using pow_orderOf_eq_one z
  refine not_isMulCommutative_sylow_of_isPerfect (Group.isPerfect_def.mpr hK) S
    (z := (⟨z, hzK⟩ : K)) ?_ hz1 ?_ ?_
  · rw [mem_center_iff]
    exact fun g => Subtype.ext (hzc g g.2).symm
  · exact Subtype.ext (by simpa using hzp)
  · rw [hS]
    refine IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext ?_)
    exact hcomm _ (mem_subgroupOf.1 a.2) _ (mem_subgroupOf.1 b.2)

private lemma mem_centralizer_of_conjNormal_eq_one {Y : Type} [Group Y] {K : Subgroup Y}
    [K.Normal] {g : Y} (hg : MulAut.conjNormal (H := K) g = 1) :
    g ∈ centralizer (K : Set Y) := by
  rw [mem_centralizer_iff]
  intro k hk
  have h := MulAut.conjNormal_apply (H := K) g ⟨k, hk⟩
  rw [hg, MulAut.one_apply] at h
  calc k * g = g * k * g⁻¹ * g := by rw [← h]
    _ = g * k := by group

private lemma exists_mul_eq_of_map_eq {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]
    {R A : Subgroup Y} (hAR : A ≤ R)
    (hmap : A.map (MulAut.conjNormal (H := K)) = R.map (MulAut.conjNormal (H := K))) {s : Y}
    (hs : s ∈ R) : ∃ a ∈ A, ∃ c ∈ R ⊓ centralizer (K : Set Y), s = a * c := by
  have hsmap : MulAut.conjNormal (H := K) s ∈ A.map (MulAut.conjNormal (H := K)) :=
    hmap ▸ mem_map_of_mem _ hs
  obtain ⟨a, haA, has⟩ := mem_map.1 hsmap
  have h1 : MulAut.conjNormal (H := K) (a⁻¹ * s) = 1 := by
    rw [map_mul, map_inv, has, inv_mul_cancel]
  exact ⟨a, haA, a⁻¹ * s, mem_inf.2 ⟨R.mul_mem (R.inv_mem (hAR haA)) hs,
    mem_centralizer_of_conjNormal_eq_one h1⟩, by group⟩

private lemma mul_comm_of_mul_decomp {Y : Type} [Group Y] {A C S : Subgroup Y}
    (hA : IsMulCommutative A) (hC : IsMulCommutative C)
    (hcS : ∀ c ∈ C, ∀ s ∈ S, c * s = s * c)
    (hdec : ∀ s ∈ S, ∃ a ∈ A, ∃ c ∈ C, s = a * c) {s s' : Y} (hs : s ∈ S) (hs' : s' ∈ S) :
    s * s' = s' * s := by
  obtain ⟨a, ha, c, hc, rfl⟩ := hdec s hs
  obtain ⟨a', ha', c', hc', rfl⟩ := hdec s' hs'
  have haa : a * a' = a' * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨a', ha'⟩)
  have hcc : c * c' = c' * c := congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : C) ⟨c', hc'⟩)
  have h1 := hcS c hc _ hs'
  have h2 := hcS c' hc' _ hs
  calc a * c * (a' * c') = a * (c * (a' * c')) := by rw [mul_assoc]
    _ = a * (a' * c' * c) := by rw [h1]
    _ = (a * a') * (c' * c) := by group
    _ = (a' * a) * (c * c') := by rw [haa, hcc]
    _ = a' * (a * c * c') := by group
    _ = a' * (c' * (a * c)) := by rw [← h2]
    _ = a' * c' * (a * c) := by rw [mul_assoc]

theorem false_of_small_automorphism_group {Y : Type} [Group Y] [Finite Y] (R : Sylow 3 Y)
    (K : Subgroup Y) [K.Normal] {z : Y} (hK : CFSG.Open.IsQuasisimple K) (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, z * k = k * z) (hz3 : orderOf z = 3)
    (hB : ∀ B : Subgroup (MulAut K), IsPGroup 3 B → Nat.card B ≤ 9)
    (hΩ : ∀ c ∈ (R : Subgroup Y) ⊓ centralizer (K : Set Y), orderOf c = 3 → c ∈ zpowers z)
    (hrank : 3 ≤ CFSG.Open.pRank 3 (R : Subgroup Y)) : False := by
  have hC : IsMulCommutative ↥((R : Subgroup Y) ⊓ centralizer (K : Set Y)) :=
    isMulCommutative_of_orderOf_eq_three hz3 R.isPGroup'.to_inf_left hΩ
  obtain ⟨A, hAR, hAe, hAcard⟩ := pRank_attained 3 (R : Subgroup Y) (by omega)
  have hA27 : 27 ≤ Nat.card A := by
    rw [hAcard]
    exact (Nat.pow_le_pow_right (by norm_num) hrank : 3 ^ 3 ≤ _)
  set ψ : ↥A →* MulAut K := (MulAut.conjNormal (H := K)).comp A.subtype with hψ
  have hker : Nat.card ψ.ker ≤ 3 := by
    have hle : ψ.ker.map A.subtype ≤ zpowers z := by
      refine le_zpowers_of_pow_three_eq_one hΩ ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact mem_inf.2 ⟨hAR a.2, mem_centralizer_of_conjNormal_eq_one ha⟩
      · rintro _ ⟨a, -, rfl⟩
        exact hAe.2 a a.2
    rw [← card_map_of_injective A.subtype_injective]
    exact (card_le_of_le hle).trans (by rw [Nat.card_zpowers, hz3])
  have hrange : ψ.range = A.map (MulAut.conjNormal (H := K)) := by
    rw [hψ, MonoidHom.range_comp, range_subtype]
  have hmap9 : 9 ≤ Nat.card (A.map (MulAut.conjNormal (H := K))) := by
    rw [← hrange]
    have h := card_ker_mul_card_range ψ
    by_contra hlt
    have h8 : Nat.card ψ.range ≤ 8 := by omega
    have := Nat.mul_le_mul hker h8
    omega
  have hRmap : IsPGroup 3 ((R : Subgroup Y).map (MulAut.conjNormal (H := K))) :=
    R.isPGroup'.map _
  have hmap : A.map (MulAut.conjNormal (H := K)) =
      (R : Subgroup Y).map (MulAut.conjNormal (H := K)) :=
    eq_of_le_of_card_ge (map_mono hAR) ((hB _ hRmap).trans hmap9)
  refine not_forall_mul_comm_inf_of_isPerfect R K hK.1 hzK hzc hz3 fun s hs s' hs' => ?_
  refine mul_comm_of_mul_decomp (S := (R : Subgroup Y) ⊓ K) hAe.1 hC ?_ ?_ hs hs'
  · intro c hc t ht
    exact ((mem_centralizer_iff.1 hc.2) t ht.2).symm
  · intro t ht
    obtain ⟨a, ha, c, hc, hac⟩ := exists_mul_eq_of_map_eq hAR hmap ht.1
    exact ⟨a, ha, c, hc, hac⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
