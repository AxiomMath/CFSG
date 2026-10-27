module

public import CFSG.ClassicalInvolution.Q3.TL3SecOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem subset_closure_pair_left {H : Type} [Group H] (a b : H) :
    a ∈ Subgroup.closure ({a, b} : Set H) := Subgroup.subset_closure (Set.mem_insert _ _)

theorem subset_closure_pair_right {H : Type} [Group H] (a b : H) :
    b ∈ Subgroup.closure ({a, b} : Set H) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

section Lift

variable {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]

theorem exists_odd_conj (hN : Odd (Nat.card N)) {A B : Subgroup H} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hmap : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, conjSub n A = B := by
  have key : ∀ {A B : Subgroup H}, A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N) →
      B ≤ A ⊔ N := by
    intro A B hAB b hb
    have h1 : QuotientGroup.mk' N b ∈ A.map (QuotientGroup.mk' N) :=
      hAB ▸ Subgroup.mem_map_of_mem _ hb
    obtain ⟨a, ha, hab⟩ := h1
    have hn : a⁻¹ * b ∈ N := by
      have h2 : QuotientGroup.mk' N (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv]
        have : QuotientGroup.mk' N a = QuotientGroup.mk' N b := hab
        rw [this, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h2
    have : b = a * (a⁻¹ * b) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ha hn
  have hBle : B ≤ A ⊔ N := key hmap
  have hAle : A ≤ B ⊔ N := key hmap.symm
  have hsup : B ⊔ N = A ⊔ N := le_antisymm (sup_le hBle le_sup_right) (sup_le hAle le_sup_right)
  have hAs : IsSylow2In A (A ⊔ N) := isSylow2In_sup_of_odd hN hA
  have hBs : IsSylow2In B (A ⊔ N) := by
    have := isSylow2In_sup_of_odd hN hB
    rwa [hsup] at this
  obtain ⟨m, hm, hmA⟩ := Disconnected.AschTight.Sec6Gen.exists_conjSub_eq_of_isSylow2In hAs hBs
  obtain ⟨a, ha, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hm
  have hn' : a * n * a⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem n hn a
  refine ⟨a * n * a⁻¹, hn', ?_⟩
  have e : a * n = (a * n * a⁻¹) * a := by group
  rw [e, conjSub_mul, conjSub_eq_self_of_mem ha] at hmA
  exact hmA

theorem exists_fixed_conj (hN : Odd (Nat.card N)) {A B : Subgroup H} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hmap : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N))
    {t a b x y : H} (ht2 : t * t = 1) (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ B) (hy : y ∈ B)
    (hax : QuotientGroup.mk' N a = QuotientGroup.mk' N x)
    (hby : QuotientGroup.mk' N b = QuotientGroup.mk' N y)
    (hat : a * t = t * a) (hbt : b * t = t * b) (hxt : x * t = t * x) (hyt : y * t = t * y) :
    ∃ n ∈ N, n * a * n⁻¹ = x ∧ n * b * n⁻¹ = y ∧ n * t = t * n := by
  obtain ⟨n₀, hn₀, hcn⟩ := exists_odd_conj N hN hA hB hmap
  have hBN : B ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hB le_rfl
      (hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hsame : ∀ {w z : H}, w ∈ A → z ∈ B → QuotientGroup.mk' N w = QuotientGroup.mk' N z →
      n₀ * w * n₀⁻¹ = z := by
    intro w z hw hz hwz
    have h1 : n₀ * w * n₀⁻¹ ∈ B := hcn ▸ conj_mem_conjSub hw
    have h2 : (n₀ * w * n₀⁻¹) * z⁻¹ ∈ B ⊓ N := by
      refine ⟨B.mul_mem h1 (B.inv_mem hz), ?_⟩
      have h3 : QuotientGroup.mk' N ((n₀ * w * n₀⁻¹) * z⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, map_inv]
        have : QuotientGroup.mk' N n₀ = 1 := (QuotientGroup.eq_one_iff _).mpr hn₀
        rw [this, hwz]
        group
      exact (QuotientGroup.eq_one_iff _).mp h3
    rw [hBN, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  have h₁ : n₀ * a * n₀⁻¹ = x := hsame ha hx hax
  have h₂ : n₀ * b * n₀⁻¹ = y := hsame hb hy hby
  set S : Subgroup H := N ⊓ Subgroup.centralizer ({a} : Set H) ⊓ Subgroup.centralizer ({b} : Set H)
    with hS
  set C : Set H := {c | c ∈ N ∧ c * a * c⁻¹ = x ∧ c * b * c⁻¹ = y} with hC
  have hCeq : C = (fun s => n₀ * s) '' (S : Set H) := by
    ext c
    constructor
    · rintro ⟨hcN, hca, hcb⟩
      refine ⟨n₀⁻¹ * c, ⟨⟨?_, ?_⟩, ?_⟩, by group⟩
      · exact N.mul_mem (N.inv_mem hn₀) hcN
      · show n₀⁻¹ * c ∈ Subgroup.centralizer ({a} : Set H)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : n₀⁻¹ * c * a * (n₀⁻¹ * c)⁻¹ = a := by
          calc n₀⁻¹ * c * a * (n₀⁻¹ * c)⁻¹ = n₀⁻¹ * (c * a * c⁻¹) * n₀ := by group
            _ = n₀⁻¹ * (n₀ * a * n₀⁻¹) * n₀ := by rw [hca, h₁]
            _ = a := by group
        exact mul_inv_eq_iff_eq_mul.mp this
      · show n₀⁻¹ * c ∈ Subgroup.centralizer ({b} : Set H)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : n₀⁻¹ * c * b * (n₀⁻¹ * c)⁻¹ = b := by
          calc n₀⁻¹ * c * b * (n₀⁻¹ * c)⁻¹ = n₀⁻¹ * (c * b * c⁻¹) * n₀ := by group
            _ = n₀⁻¹ * (n₀ * b * n₀⁻¹) * n₀ := by rw [hcb, h₂]
            _ = b := by group
        exact mul_inv_eq_iff_eq_mul.mp this
    · rintro ⟨s, ⟨⟨hsN, hsa⟩, hsb⟩, rfl⟩
      have hsa' : s * a = a * s := Subgroup.mem_centralizer_singleton_iff.mp hsa
      have hsb' : s * b = b * s := Subgroup.mem_centralizer_singleton_iff.mp hsb
      refine ⟨N.mul_mem hn₀ hsN, ?_, ?_⟩
      · calc n₀ * s * a * (n₀ * s)⁻¹ = n₀ * (s * a * s⁻¹) * n₀⁻¹ := by group
          _ = x := by rw [hsa', ← h₁]; group
      · calc n₀ * s * b * (n₀ * s)⁻¹ = n₀ * (s * b * s⁻¹) * n₀⁻¹ := by group
          _ = y := by rw [hsb', ← h₂]; group
  have hCodd : Odd (Nat.card C) := by
    rw [hCeq, Nat.card_image_of_injective (mul_right_injective n₀) (S : Set H)]
    exact hN.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left))
  have ht2' : IsPGroup 2 (Subgroup.zpowers t) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ht2
  have hinv : ∀ v ∈ Subgroup.zpowers t, ∀ c ∈ C, v * c * v⁻¹ ∈ C := by
    rintro v hv c ⟨hcN, hca, hcb⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hva : t ^ j * a = a * t ^ j := (Commute.zpow_left (show Commute t a from hat.symm) j).eq
    have hvb : t ^ j * b = b * t ^ j := (Commute.zpow_left (show Commute t b from hbt.symm) j).eq
    have hvx : t ^ j * x = x * t ^ j := (Commute.zpow_left (show Commute t x from hxt.symm) j).eq
    have hvy : t ^ j * y = y * t ^ j := (Commute.zpow_left (show Commute t y from hyt.symm) j).eq
    refine ⟨?_, ?_, ?_⟩
    · exact (inferInstance : N.Normal).conj_mem c hcN _
    · calc t ^ j * c * (t ^ j)⁻¹ * a * (t ^ j * c * (t ^ j)⁻¹)⁻¹
          = t ^ j * (c * ((t ^ j)⁻¹ * a * t ^ j) * c⁻¹) * (t ^ j)⁻¹ := by group
        _ = t ^ j * (c * a * c⁻¹) * (t ^ j)⁻¹ := by
            rw [show (t ^ j)⁻¹ * a * t ^ j = a by rw [mul_assoc, ← hva]; group]
        _ = x := by rw [hca, hvx]; group
    · calc t ^ j * c * (t ^ j)⁻¹ * b * (t ^ j * c * (t ^ j)⁻¹)⁻¹
          = t ^ j * (c * ((t ^ j)⁻¹ * b * t ^ j) * c⁻¹) * (t ^ j)⁻¹ := by group
        _ = t ^ j * (c * b * c⁻¹) * (t ^ j)⁻¹ := by
            rw [show (t ^ j)⁻¹ * b * t ^ j = b by rw [mul_assoc, ← hvb]; group]
        _ = y := by rw [hcb, hvy]; group
  obtain ⟨c, ⟨hcN, hca, hcb⟩, hfix⟩ :=
    Thompson.exists_fixed_mem_of_odd ht2' hinv hCodd
  refine ⟨c, hcN, hca, hcb, ?_⟩
  exact (mul_inv_eq_iff_eq_mul.mp (hfix t (Subgroup.mem_zpowers t))).symm

theorem exists_lift_fusion (hN : Odd (Nat.card N)) {A B : Subgroup H} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) {t a b x y : H} (ht2 : t * t = 1) (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ B)
    (hy : y ∈ B) (hat : a * t = t * a) (hbt : b * t = t * b) (hxt : x * t = t * x)
    (hyt : y * t = t * y) {cb : H ⧸ N}
    (hcb : cb ∈ Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (H ⧸ N)))
    (h1 : cb * QuotientGroup.mk' N a * cb⁻¹ = QuotientGroup.mk' N x)
    (h2 : cb * QuotientGroup.mk' N b * cb⁻¹ = QuotientGroup.mk' N y) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set H), c * a * c⁻¹ = x ∧ c * b * c⁻¹ = y := by
  rw [OddQ.centralizer_mk_eq hN ht2] at hcb
  obtain ⟨c₁, hc₁t, rfl⟩ := hcb
  have hc₁t' : c₁ * t = t * c₁ := Subgroup.mem_centralizer_singleton_iff.mp hc₁t
  set a' := c₁ * a * c₁⁻¹ with ha'
  set b' := c₁ * b * c₁⁻¹ with hb'
  set A' : Subgroup H := Subgroup.closure ({a', b'} : Set H) with hA'
  set B' : Subgroup H := Subgroup.closure ({x, y} : Set H) with hB'
  have hA'le : A' ≤ conjSub c₁ A := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w (rfl | rfl)
    · exact conj_mem_conjSub ha
    · exact conj_mem_conjSub hb
  have hB'le : B' ≤ B := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w (rfl | rfl)
    · exact hx
    · exact hy
  have hA'2 : IsPGroup 2 A' := (isPGroup_conjSub c₁ hA).to_le hA'le
  have hB'2 : IsPGroup 2 B' := hB.to_le hB'le
  have hax : QuotientGroup.mk' N a' = QuotientGroup.mk' N x := by
    rw [ha', map_mul, map_mul, map_inv]
    exact h1
  have hby : QuotientGroup.mk' N b' = QuotientGroup.mk' N y := by
    rw [hb', map_mul, map_mul, map_inv]
    exact h2
  have hmap : A'.map (QuotientGroup.mk' N) = B'.map (QuotientGroup.mk' N) := by
    rw [hA', hB', MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair,
      hax, hby]
  have hcomm : ∀ {w : H}, w * t = t * w → c₁ * w * c₁⁻¹ * t = t * (c₁ * w * c₁⁻¹) := by
    intro w hw
    calc c₁ * w * c₁⁻¹ * t = c₁ * w * (c₁⁻¹ * t) := by group
      _ = c₁ * w * (t * c₁⁻¹) := by
          rw [show c₁⁻¹ * t = t * c₁⁻¹ by
            calc c₁⁻¹ * t = c₁⁻¹ * (t * c₁) * c₁⁻¹ := by group
              _ = c₁⁻¹ * (c₁ * t) * c₁⁻¹ := by rw [hc₁t']
              _ = t * c₁⁻¹ := by group]
      _ = c₁ * (w * t) * c₁⁻¹ := by group
      _ = c₁ * (t * w) * c₁⁻¹ := by rw [hw]
      _ = t * (c₁ * w * c₁⁻¹) := by
          calc c₁ * (t * w) * c₁⁻¹ = (c₁ * t) * w * c₁⁻¹ := by group
            _ = (t * c₁) * w * c₁⁻¹ := by rw [hc₁t']
            _ = t * (c₁ * w * c₁⁻¹) := by group
  obtain ⟨n, hnN, hna, hnb, hnt⟩ := exists_fixed_conj N hN hA'2 hB'2 hmap ht2
    (subset_closure_pair_left a' b') (subset_closure_pair_right a' b')
    (subset_closure_pair_left x y) (subset_closure_pair_right x y) hax hby (hcomm hat)
    (hcomm hbt) hxt hyt
  refine ⟨n * c₁, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * c₁ * t = n * (c₁ * t) := by group
      _ = n * (t * c₁) := by rw [hc₁t']
      _ = (n * t) * c₁ := by group
      _ = (t * n) * c₁ := by rw [hnt]
      _ = t * (n * c₁) := by group
  · rw [show n * c₁ * a * (n * c₁)⁻¹ = n * (c₁ * a * c₁⁻¹) * n⁻¹ by group]
    exact hna
  · rw [show n * c₁ * b * (n * c₁)⁻¹ = n * (c₁ * b * c₁⁻¹) * n⁻¹ by group]
    exact hnb

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
