module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12Seven
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open Subgroup

private lemma l62_isElemAbelian_zpowers3 {G : Type} [Group G] {a : G} (ha3 : a ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers a) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · show x * y = y * x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk, ← hm]
    exact (Commute.zpow_zpow_self a k m).eq
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    calc (a ^ k) ^ 3 = (a ^ 3) ^ k := by group
      _ = 1 := by rw [ha3, one_zpow]

private lemma l62_nodup_four {α : Type*} {x y z t : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxt : x ≠ t) (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t) : [x, y, z, t].Nodup := by
  simp [List.nodup_cons, hxy, hxz, hxt, hyz, hyt, hzt]

private lemma l62_pRank_two_of_commuting {G : Type} [Group G] [Finite G] {a b : G}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hbn : b ∉ Subgroup.zpowers a) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have hEa : IsElemAbelian 3 (Subgroup.zpowers a) := l62_isElemAbelian_zpowers3 ha3
  have hdc : Subgroup.zpowers a ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hab)
  obtain ⟨hE, hcard⟩ := cl_step hEa hdc hb3 hbn
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE (by rw [hcard, hza] <;> norm_num)

theorem l62_two_le_pRank_alternating (n : ℕ) (hn : 6 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) := by
  obtain ⟨q, hq⟩ : ∃ q : Fin 6 → Fin n, ∀ i j : Fin 6, i ≠ j → q i ≠ q j :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩, fun i j hij h => by
      have h' := congrArg Fin.val h
      exact hij (Fin.ext h')⟩
  obtain ⟨σa, hσa⟩ : ∃ σ : Equiv.Perm (Fin n),
      σ = Equiv.swap (q 0) (q 1) * Equiv.swap (q 0) (q 2) := ⟨_, rfl⟩
  obtain ⟨σb, hσb⟩ : ∃ σ : Equiv.Perm (Fin n),
      σ = Equiv.swap (q 3) (q 4) * Equiv.swap (q 3) (q 5) := ⟨_, rfl⟩
  have hA : σa.IsThreeCycle := by
    rw [hσa]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (hq 0 1 (by decide))
      (hq 0 2 (by decide)) (hq 1 2 (by decide))
  have hB : σb.IsThreeCycle := by
    rw [hσb]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (hq 3 4 (by decide))
      (hq 3 5 (by decide)) (hq 4 5 (by decide))
  have hAmem : σa ∈ alternatingGroup (Fin n) := hA.mem_alternatingGroup
  have hBmem : σb ∈ alternatingGroup (Fin n) := hB.mem_alternatingGroup
  have hA3 : σa ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σa
    rwa [hA.orderOf] at h
  have hB3 : σb ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σb
    rwa [hB.orderOf] at h
  have hA1 : σa ≠ 1 := hA.ne_one
  have hdisj : Equiv.Perm.Disjoint σa σb := by
    rw [hσa, hσb]
    refine Equiv.Perm.Disjoint.mul_left ?_ ?_
    · refine Equiv.Perm.Disjoint.mul_right ?_ ?_
      · exact Equiv.Perm.disjoint_swap_swap (l62_nodup_four (hq 0 1 (by decide))
          (hq 0 3 (by decide)) (hq 0 4 (by decide)) (hq 1 3 (by decide))
          (hq 1 4 (by decide)) (hq 3 4 (by decide)))
      · exact Equiv.Perm.disjoint_swap_swap (l62_nodup_four (hq 0 1 (by decide))
          (hq 0 3 (by decide)) (hq 0 5 (by decide)) (hq 1 3 (by decide))
          (hq 1 5 (by decide)) (hq 3 5 (by decide)))
    · refine Equiv.Perm.Disjoint.mul_right ?_ ?_
      · exact Equiv.Perm.disjoint_swap_swap (l62_nodup_four (hq 0 2 (by decide))
          (hq 0 3 (by decide)) (hq 0 4 (by decide)) (hq 2 3 (by decide))
          (hq 2 4 (by decide)) (hq 3 4 (by decide)))
      · exact Equiv.Perm.disjoint_swap_swap (l62_nodup_four (hq 0 2 (by decide))
          (hq 0 3 (by decide)) (hq 0 5 (by decide)) (hq 2 3 (by decide))
          (hq 2 5 (by decide)) (hq 3 5 (by decide)))
  have hcomm : σa * σb = σb * σa := hdisj.commute.eq
  have hfix : σa (q 3) = q 3 := by
    rw [hσa, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hq 3 0 (by decide)) (hq 3 2 (by decide)),
      Equiv.swap_apply_of_ne_of_ne (hq 3 0 (by decide)) (hq 3 1 (by decide))]
  have hbq : σb (q 3) = q 5 := by
    rw [hσb, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (hq 5 3 (by decide)) (hq 5 4 (by decide))]
  obtain ⟨a, ha⟩ : ∃ a : alternatingGroup (Fin n), (a : Equiv.Perm (Fin n)) = σa :=
    ⟨⟨σa, hAmem⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : alternatingGroup (Fin n), (b : Equiv.Perm (Fin n)) = σb :=
    ⟨⟨σb, hBmem⟩, rfl⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ha, Subgroup.coe_one]; exact hA3)
  have hb3 : b ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb, Subgroup.coe_one]; exact hB3)
  have ha1 : a ≠ 1 := fun h => hA1 (by rw [← ha, h, Subgroup.coe_one])
  have hab : a * b = b * a := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]
    exact hcomm)
  have hbn : b ∉ Subgroup.zpowers a := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 : σa ^ k = σb := by
      rw [← ha, ← hb, ← Subgroup.coe_zpow, hk]
    have h3 : σb (q 3) = q 3 := by
      rw [← h2]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix k
    rw [hbq] at h3
    exact hq 5 3 (by decide) h3
  exact l62_pRank_two_of_commuting ha3 hb3 ha1 hab hbn

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
