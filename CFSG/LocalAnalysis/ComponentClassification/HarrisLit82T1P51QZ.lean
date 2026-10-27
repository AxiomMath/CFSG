module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QFAt

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup

theorem fAt_of_commute_mem_zpowers {X : Type} [Group X] {z : X} (hz : orderOf z = 2)
    (h : ∀ g ∈ centralizer ({z} : Set X),
      (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
        ∀ k ∈ K, (k : X) * g = g * k) → g ∈ zpowers z) :
    FAt X z := by
  intro P hPC _ h8 hK
  exfalso
  have hle : P ≤ zpowers z := fun g hg =>
    h g (hPC hg) fun K hK₁ hK₂ k hk => hK K hK₁ hK₂ k hk g hg
  have hdvd := card_dvd_of_le hle
  rw [Nat.card_zpowers, hz, h8] at hdvd
  omega

theorem exists_zpow_mul_of_mem_sup {G : Type*} [Group G] {z : G} {N : Subgroup G}
    (hzN : ∀ n ∈ N, n * z = z * n) {g : G} (hg : g ∈ zpowers z ⊔ N) :
    ∃ k : ℤ, ∃ n ∈ N, g = z ^ k * n := by
  let S : Subgroup G :=
    { carrier := {g | ∃ k : ℤ, ∃ n ∈ N, g = z ^ k * n}
      one_mem' := ⟨0, 1, N.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k, n, hn, rfl⟩ ⟨l, m, hm, rfl⟩
        refine ⟨k + l, n * m, N.mul_mem hn hm, ?_⟩
        have hc : n * z ^ l = z ^ l * n := (Commute.zpow_right (hzN n hn) l).eq
        calc z ^ k * n * (z ^ l * m) = z ^ k * (n * z ^ l) * m := by group
          _ = z ^ k * (z ^ l * n) * m := by rw [hc]
          _ = z ^ (k + l) * (n * m) := by rw [zpow_add]; group
      inv_mem' := by
        rintro _ ⟨k, n, hn, rfl⟩
        refine ⟨-k, n⁻¹, N.inv_mem hn, ?_⟩
        rw [_root_.mul_inv_rev, zpow_neg]
        exact (Commute.zpow_right (hzN n hn) k).inv_inv.eq }
  have hle : zpowers z ⊔ N ≤ S := by
    refine sup_le (fun x hx => ?_) fun n hn => ⟨0, n, hn, by simp⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ⟨k, 1, N.one_mem, (mul_one _).symm⟩
  exact hle hg

theorem fAt_of_sup_simple {X : Type} [Group X] {z : X} (hz : orderOf z = 2) {N : Subgroup X}
    (hNC : N ≤ centralizer ({z} : Set X)) (hCN : centralizer ({z} : Set X) ≤ zpowers z ⊔ N)
    [IsSimpleGroup N] (hnab : ∃ a b : N, a * b ≠ b * a) (hev : Even (Nat.card N)) :
    FAt X z := by
  have hzN : ∀ n ∈ N, n * z = z * n := fun n hn => mem_centralizer_singleton_iff.1 (hNC hn)
  set K := N.subgroupOf (centralizer ({z} : Set X)) with hKdef
  let e : K ≃* N := subgroupOfEquivOfLe hNC
  have : IsSimpleGroup K := e.isSimpleGroup
  have hKnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hKn : K.Normal := by
    rw [hKdef, normal_subgroupOf_iff_le_normalizer hNC]
    refine hCN.trans (sup_le ?_ le_normalizer)
    have hzc : z ∈ centralizer (N : Set X) := mem_centralizer_iff.2 hzN
    rw [zpowers_le]
    exact (Subgroup.centralizer_le_normalizer _) hzc
  have hKc : IsComponent K :=
    ⟨(LocalCores.isQuasisimple_of_isSimpleGroup hKnab).1, hKn.isSubnormal⟩
  have hKe : Even (Nat.card K) := by
    rw [Nat.card_congr e.toEquiv]
    exact hev
  have hZ := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  refine fAt_of_commute_mem_zpowers hz fun g hg hcomm => ?_
  have hgN : ∀ n ∈ N, n * g = g * n := fun n hn =>
    hcomm K hKc hKe ⟨n, hNC hn⟩ (mem_subgroupOf.2 hn)
  obtain ⟨k, n, hn, rfl⟩ := exists_zpow_mul_of_mem_sup hzN (hCN hg)
  have hnZ : (⟨n, hn⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro m
    apply Subtype.ext
    change (m : X) * n = n * m
    have h1 := hgN m m.2
    have h2 : (m : X) * z ^ k = z ^ k * m := (Commute.zpow_right (hzN m m.2) k).eq
    rw [← mul_assoc, h2, mul_assoc, mul_assoc] at h1
    exact mul_left_cancel h1
  rw [hZ, mem_bot] at hnZ
  have hn1 : n = 1 := congrArg Subtype.val hnZ
  rw [hn1, mul_one]
  exact zpow_mem (mem_zpowers z) k

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
