module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

open Subgroup

namespace CFSG.GF2Type.Widths1112

theorem mem_closure_pair_iff {G : Type*} [Group G] {a b x : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    x ∈ closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem card_closure_pair_le_four {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) : Nat.card (closure ({a, b} : Set G)) ≤ 4 := by
  have hsub : (closure ({a, b} : Set G) : Set G) ⊆ ({1, a, b, a * b} : Set G) := by
    intro x hx
    rcases (mem_closure_pair_iff ha hb hab).1 hx with h | h | h | h <;> simp [h]
  have h1 := Set.ncard_insert_le (1 : G) ({a, b, a * b} : Set G)
  have h2 := Set.ncard_insert_le a ({b, a * b} : Set G)
  have h3 := Set.ncard_insert_le b ({a * b} : Set G)
  have h4 := Set.ncard_singleton (a * b)
  calc Nat.card (closure ({a, b} : Set G))
      = Nat.card ((closure ({a, b} : Set G) : Set G)) := rfl
    _ = ((closure ({a, b} : Set G) : Set G)).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, a, b, a * b} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by omega

theorem commute_of_mem_commutator_of_comm_mem {X : Type*} [Group X] {x : X}
    {P : Subgroup X} (hxP : ∀ p ∈ P, p * x = x * p) {y : X} (hxy : y * x = x * y)
    (hy : ∀ p ∈ P, p⁻¹ * y⁻¹ * p * y ∈ zpowers x) {c : X} (hc : c ∈ ⁅P, P⁆) :
    c * y = y * c := by
  have hz : ∀ u ∈ zpowers x, ∀ p ∈ P, p * u = u * p := by
    intro u hu p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact (show Commute p x from hxP p hp).zpow_right k
  have hcomm : ∀ u ∈ zpowers x, ∀ v ∈ zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.refl x).zpow_zpow k l
  have hmul : ∀ a ∈ P, ∀ b ∈ P,
      (a * b)⁻¹ * y⁻¹ * (a * b) * y = (a⁻¹ * y⁻¹ * a * y) * (b⁻¹ * y⁻¹ * b * y) := by
    intro a ha b hb
    have hcb := hz _ (hy a ha) b⁻¹ (P.inv_mem hb)
    calc (a * b)⁻¹ * y⁻¹ * (a * b) * y
        = b⁻¹ * (a⁻¹ * y⁻¹ * a * y) * (y⁻¹ * b * y) := by group
      _ = (a⁻¹ * y⁻¹ * a * y) * b⁻¹ * (y⁻¹ * b * y) := by rw [hcb]
      _ = (a⁻¹ * y⁻¹ * a * y) * (b⁻¹ * y⁻¹ * b * y) := by simp only [mul_assoc]
  have hinv : ∀ a ∈ P, (a⁻¹)⁻¹ * y⁻¹ * a⁻¹ * y * (a⁻¹ * y⁻¹ * a * y) = 1 := by
    intro a ha
    have h := hmul a⁻¹ (P.inv_mem ha) a ha
    have h1 : (a⁻¹ * a)⁻¹ * y⁻¹ * (a⁻¹ * a) * y = (1 : X) := by group
    rw [h1] at h
    exact h.symm
  have hfour : ∀ A ∈ zpowers x, ∀ B ∈ zpowers x, ∀ A' ∈ zpowers x, ∀ B' ∈ zpowers x,
      A' * A = 1 → B' * B = 1 → A * B * A' * B' = 1 := by
    intro A hA B hB A' hA' B' hB' hAA' hBB'
    calc A * B * A' * B' = A * (B * A') * B' := by simp only [mul_assoc]
      _ = A * (A' * B) * B' := by rw [hcomm B hB A' hA']
      _ = (A * A') * B * B' := by simp only [mul_assoc]
      _ = (A' * A) * B * B' := by rw [hcomm A hA A' hA']
      _ = B * B' := by rw [hAA', one_mul]
      _ = 1 := mul_eq_one_comm.2 hBB'
  have hcc : ∀ a ∈ P, ∀ b ∈ P,
      (a * b * a⁻¹ * b⁻¹)⁻¹ * y⁻¹ * (a * b * a⁻¹ * b⁻¹) * y = 1 := by
    intro a ha b hb
    have ha' : a⁻¹ ∈ P := P.inv_mem ha
    have hb' : b⁻¹ ∈ P := P.inv_mem hb
    rw [hmul (a * b * a⁻¹) (P.mul_mem (P.mul_mem ha hb) ha') b⁻¹ hb',
      hmul (a * b) (P.mul_mem ha hb) a⁻¹ ha', hmul a ha b hb]
    exact hfour _ (hy a ha) _ (hy b hb) _ (hy a⁻¹ ha') _ (hy b⁻¹ hb') (hinv a ha) (hinv b hb)
  have key : ∀ g : X, g⁻¹ * y⁻¹ * g * y = 1 → y * g = g * y := by
    intro g hg
    have h2 : y⁻¹ * g * y = g := by
      calc y⁻¹ * g * y = g * (g⁻¹ * y⁻¹ * g * y) := by group
        _ = g := by rw [hg, mul_one]
    calc y * g = y * (y⁻¹ * g * y) := by rw [h2]
      _ = g * y := by group
  have hcen : ⁅P, P⁆ ≤ Subgroup.centralizer ({y} : Set X) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh, commutatorElement_def]
    exact key _ (hcc a ha b hb)
  exact (Subgroup.mem_centralizer_iff.1 (hcen hc) y (Set.mem_singleton y)).symm

theorem commutator_le_of_sup_central {G : Type*} [Group G] {Q Y T : Subgroup G}
    (hYQ : Y ≤ Q) (hYn : ∀ q ∈ Q, ∀ y ∈ Y, q * y * q⁻¹ ∈ Y) (hsup : Y ⊔ T = Q)
    (hT : ∀ t ∈ T, ∀ q ∈ Q, t * q = q * t) : ⁅Q, Q⁆ ≤ Y := by
  have hTQ : T ≤ Q := by
    rw [← hsup]
    exact le_sup_right
  let S : Subgroup G :=
    { carrier := {a | a ∈ Q ∧ ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Y}
      mul_mem' := by
        intro a₁ a₂ h₁ h₂
        obtain ⟨h₁Q, h₁Y⟩ := h₁
        obtain ⟨h₂Q, h₂Y⟩ := h₂
        refine ⟨Q.mul_mem h₁Q h₂Q, fun b hb => ?_⟩
        convert Y.mul_mem (hYn a₁ h₁Q _ (h₂Y b hb)) (h₁Y b hb) using 1
        group
      one_mem' := by
        refine ⟨Q.one_mem, fun b hb => ?_⟩
        convert Y.one_mem using 1
        group
      inv_mem' := by
        intro a h
        obtain ⟨hQ, hY⟩ := h
        refine ⟨Q.inv_mem hQ, fun b hb => ?_⟩
        have hba : b * a * b⁻¹ * a⁻¹ ∈ Y := by
          convert Y.inv_mem (hY b hb) using 1
          group
        convert hYn a⁻¹ (Q.inv_mem hQ) _ hba using 1
        group }
  have hSmem : ∀ a, a ∈ S ↔ (a ∈ Q ∧ ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Y) := fun a => Iff.rfl
  have hYS : Y ≤ S := by
    intro y hy
    refine (hSmem y).2 ⟨hYQ hy, fun b hb => ?_⟩
    convert Y.mul_mem hy (hYn b hb y⁻¹ (Y.inv_mem hy)) using 1
    group
  have hTS : T ≤ S := by
    intro t ht
    refine (hSmem t).2 ⟨hTQ ht, fun b hb => ?_⟩
    convert Y.one_mem using 1
    rw [hT t ht b hb]
    group
  have hQS : Q ≤ S := by
    rw [← hsup]
    exact sup_le hYS hTS
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact ((hSmem a).1 (hQS ha)).2 b hb

theorem exists_central_involution_quotient {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup 2 H) (N : Subgroup H) [N.Normal] (hne : ∃ h : H, h ∉ N) :
    ∃ c : H, c ∉ N ∧ c * c ∈ N ∧ ∀ h : H, c * h * c⁻¹ * h⁻¹ ∈ N := by
  obtain ⟨h₀, hh₀⟩ := hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (H ⧸ N) := hH.to_quotient N
  haveI : Nontrivial (H ⧸ N) :=
    ⟨⟨(h₀ : H ⧸ N), 1, fun h => hh₀ ((QuotientGroup.eq_one_iff h₀).mp h)⟩⟩
  haveI : Nontrivial (Subgroup.center (H ⧸ N)) := hQ.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center (H ⧸ N)) := hQ.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card (Subgroup.center (H ⧸ N)) := Finite.one_lt_card
    rw [hn] at h1
    norm_num at h1
  have hdvd : 2 ∣ Nat.card (Subgroup.center (H ⧸ N)) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hcQ : orderOf (c : H ⧸ N) = 2 := by
    rw [Subgroup.orderOf_coe, hc]
  have hcen : ∀ g : H ⧸ N, g * (c : H ⧸ N) = (c : H ⧸ N) * g :=
    Subgroup.mem_center_iff.mp c.2
  have hc1 : (c : H ⧸ N) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hcQ
    norm_num at hcQ
  have hsq : (c : H ⧸ N) * (c : H ⧸ N) = 1 := by
    have h := pow_orderOf_eq_one (c : H ⧸ N)
    rw [hcQ] at h
    rw [← pow_two]
    exact h
  obtain ⟨w₀, hw₀⟩ := QuotientGroup.mk_surjective (c : H ⧸ N)
  refine ⟨w₀, ?_, ?_, ?_⟩
  · intro hmem
    apply hc1
    rw [← hw₀]
    exact (QuotientGroup.eq_one_iff w₀).mpr hmem
  · apply (QuotientGroup.eq_one_iff (w₀ * w₀)).mp
    rw [QuotientGroup.mk_mul, hw₀]
    exact hsq
  · intro h
    apply (QuotientGroup.eq_one_iff (w₀ * h * w₀⁻¹ * h⁻¹)).mp
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw₀]
    rw [← hcen (h : H ⧸ N), mul_inv_cancel_right, mul_inv_cancel]

theorem exists_elem_central_mod {G : Type*} [Group G] [Finite G] {x : G} (hx2 : orderOf x = 2)
    (R : Subgroup G) (hR2 : IsPGroup 2 R) (hxR : x ∈ R) (hRx : R ≤ centralizer ({x} : Set G))
    (hne : ∃ r ∈ R, r ∉ zpowers x) :
    ∃ w ∈ R, w ∉ zpowers x ∧ w * w ∈ zpowers x ∧ ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x := by
  have hcomm : ∀ g : R, ∀ n ∈ zpowers x, (g : G) * n = n * g := by
    intro g n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hgx : Commute (g : G) x := Subgroup.mem_centralizer_singleton_iff.mp (hRx g.2)
    exact (hgx.zpow_right k).eq
  haveI hN : ((zpowers x).subgroupOf R).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcomm g _ hn, mul_inv_cancel_right]
      exact hn⟩
  have hne' : ∃ h : R, h ∉ (zpowers x).subgroupOf R := by
    obtain ⟨r, hr, hrn⟩ := hne
    exact ⟨⟨r, hr⟩, fun h => hrn (Subgroup.mem_subgroupOf.mp h)⟩
  obtain ⟨c, hc1, hc2, hc3⟩ :=
    exists_central_involution_quotient hR2 ((zpowers x).subgroupOf R) hne'
  refine ⟨(c : G), c.2, fun hmem => hc1 (Subgroup.mem_subgroupOf.mpr hmem), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hc2
  · intro r hr
    exact Subgroup.mem_subgroupOf.mp (hc3 ⟨r, hr⟩)

theorem exists_W_aux {G : Type*} [Group G] {x : G}
    (R : Subgroup G) (hRx : R ≤ centralizer ({x} : Set G))
    (hRn : ∀ h ∈ centralizer ({x} : Set G), ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hxR : x ∈ R)
    (hw : ∃ w ∈ R, w ∉ zpowers x ∧ w * w ∈ zpowers x ∧ ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x) :
    ∃ W : Subgroup G, W ≤ R ∧ x ∈ W ∧ (∃ w ∈ W, w ∉ zpowers x) ∧
      (∀ h ∈ centralizer ({x} : Set G), ∀ w ∈ W, h * w * h⁻¹ ∈ W) ∧
      (∀ w ∈ W, w * w ∈ zpowers x) ∧ (∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x) := by
  obtain ⟨w₀, hw₀R, hw₀x, hw₀sq, hw₀c⟩ := hw
  have hz : ∀ n ∈ zpowers x, ∀ g ∈ centralizer ({x} : Set G), g * n = n * g := by
    intro n hn g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg : Commute g x) k
  have hinv : ∀ a : G, (a ∈ R ∧ a * a ∈ zpowers x ∧ ∀ r ∈ R, a * r * a⁻¹ * r⁻¹ ∈ zpowers x) →
      (a⁻¹ ∈ R ∧ a⁻¹ * a⁻¹ ∈ zpowers x ∧ ∀ r ∈ R, a⁻¹ * r * (a⁻¹)⁻¹ * r⁻¹ ∈ zpowers x) := by
    rintro a ⟨haR, ha2, hac⟩
    refine ⟨inv_mem haR, ?_, ?_⟩
    · rw [← mul_inv_rev]
      exact inv_mem ha2
    · intro r hr
      have hm : (a * r * a⁻¹ * r⁻¹)⁻¹ ∈ zpowers x := inv_mem (hac r hr)
      have hc := hz _ hm a⁻¹ (inv_mem (hRx haR))
      have e : a⁻¹ * r * (a⁻¹)⁻¹ * r⁻¹ = a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * a := by group
      have e' : (a * r * a⁻¹ * r⁻¹)⁻¹ * a⁻¹ * a = (a * r * a⁻¹ * r⁻¹)⁻¹ := by group
      rw [e, hc, e']
      exact hm
  have hmul : ∀ a b : G, (a ∈ R ∧ a * a ∈ zpowers x ∧ ∀ r ∈ R, a * r * a⁻¹ * r⁻¹ ∈ zpowers x) →
      (b ∈ R ∧ b * b ∈ zpowers x ∧ ∀ r ∈ R, b * r * b⁻¹ * r⁻¹ ∈ zpowers x) →
      (a * b ∈ R ∧ a * b * (a * b) ∈ zpowers x ∧
        ∀ r ∈ R, a * b * r * (a * b)⁻¹ * r⁻¹ ∈ zpowers x) := by
    rintro a b ⟨haR, ha2, hac⟩ ⟨hbR, hb2, hbc⟩
    refine ⟨mul_mem haR hbR, ?_, ?_⟩
    · have hai := hinv a ⟨haR, ha2, hac⟩
      have e1 : a * b * (a * b) = a * a * (a⁻¹ * b * (a⁻¹)⁻¹ * b⁻¹ * (b * b)) := by group
      rw [e1]
      exact mul_mem ha2 (mul_mem (hai.2.2 b hbR) hb2)
    · intro r hr
      have e2 : a * b * r * (a * b)⁻¹ * r⁻¹ =
          a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ * (a * r * a⁻¹ * r⁻¹) := by group
      have hn : b * r * b⁻¹ * r⁻¹ ∈ zpowers x := hbc r hr
      have hcm := hz _ hn a (hRx haR)
      have e3 : a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ = b * r * b⁻¹ * r⁻¹ := by
        rw [hcm]; group
      rw [e2, e3]
      exact mul_mem hn (hac r hr)
  have hone : (1 : G) ∈ R ∧ (1 : G) * 1 ∈ zpowers x ∧
      ∀ r ∈ R, (1 : G) * r * (1 : G)⁻¹ * r⁻¹ ∈ zpowers x := by
    refine ⟨one_mem R, ?_, ?_⟩
    · rw [mul_one]; exact one_mem _
    · intro r _
      have e : (1 : G) * r * (1 : G)⁻¹ * r⁻¹ = 1 := by group
      rw [e]; exact one_mem _
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, ∀ w : G,
      w ∈ W ↔ (w ∈ R ∧ w * w ∈ zpowers x ∧ ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x) :=
    ⟨{ carrier := {w | w ∈ R ∧ w * w ∈ zpowers x ∧ ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x}
       mul_mem' := fun {a b} ha hb => hmul a b ha hb
       one_mem' := hone
       inv_mem' := fun {a} ha => hinv a ha }, fun w => Iff.rfl⟩
  refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact ((hW w).mp hw).1
  · rw [hW]
    refine ⟨hxR, mul_mem (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x), ?_⟩
    intro r hr
    have hxr : x * r = r * x := (Subgroup.mem_centralizer_singleton_iff.mp (hRx hr)).symm
    have e : x * r * x⁻¹ * r⁻¹ = 1 := by rw [hxr]; group
    rw [e]; exact one_mem _
  · exact ⟨w₀, (hW w₀).mpr ⟨hw₀R, hw₀sq, hw₀c⟩, hw₀x⟩
  · intro h hh w hwW
    obtain ⟨hwR, hwsq, hwc⟩ := (hW w).mp hwW
    rw [hW]
    refine ⟨hRn h hh w hwR, ?_, ?_⟩
    · have e : h * w * h⁻¹ * (h * w * h⁻¹) = h * (w * w) * h⁻¹ := by group
      rw [e, hz _ hwsq h hh, mul_inv_cancel_right]
      exact hwsq
    · intro r hr
      have hr' : h⁻¹ * r * (h⁻¹)⁻¹ ∈ R := hRn h⁻¹ (inv_mem hh) r hr
      have hc := hwc _ hr'
      have e : h * w * h⁻¹ * r * (h * w * h⁻¹)⁻¹ * r⁻¹ =
          h * (w * (h⁻¹ * r * (h⁻¹)⁻¹) * w⁻¹ * (h⁻¹ * r * (h⁻¹)⁻¹)⁻¹) * h⁻¹ := by group
      rw [e, hz _ hc h hh, mul_inv_cancel_right]
      exact hc
  · exact fun w hw => ((hW w).mp hw).2.1
  · exact fun w hw => ((hW w).mp hw).2.2

theorem exists_W {G : Type*} [Group G] [Finite G] {x : G} (hx2 : orderOf x = 2)
    (R : Subgroup G) (hR2 : IsPGroup 2 R) (hxR : x ∈ R) (hRx : R ≤ centralizer ({x} : Set G))
    (hRn : ∀ h ∈ centralizer ({x} : Set G), ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hne : ∃ r ∈ R, r ∉ zpowers x) :
    ∃ W : Subgroup G, W ≤ R ∧ x ∈ W ∧ (∃ w ∈ W, w ∉ zpowers x) ∧
      (∀ h ∈ centralizer ({x} : Set G), ∀ w ∈ W, h * w * h⁻¹ ∈ W) ∧
      (∀ w ∈ W, w * w ∈ zpowers x) ∧ (∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x) :=
  exists_W_aux R hRx hRn hxR (exists_elem_central_mod hx2 R hR2 hxR hRx hne)

theorem central_final {G : Type*} [Group G] {x z : G} (hx2 : orderOf x = 2) (hz2 : orderOf z = 2)
    (hxz : x * z = z * x) (hzx : z ∉ zpowers x)
    (Qx : Subgroup G) (hQxC : Qx ≤ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G))
    (hzQ : z ∈ Qx) (ha : z ∈ ⁅Qx, Qx⁆)
    (hb : ∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G),
      (∀ q ∈ Qx, q⁻¹ * c⁻¹ * q * c ∈ zpowers x) → c ∈ closure {x, z})
    (W : Subgroup G) (hWx : W ≤ centralizer ({x} : Set G)) (hxW : x ∈ W)
    (hWn : ∀ h ∈ centralizer ({x} : Set G), ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hWne : ∃ w ∈ W, w ∉ zpowers x)
    (hkey : ∀ w ∈ W, ∀ q ∈ Qx, q⁻¹ * w⁻¹ * q * w ∈ zpowers x) :
    ∀ h ∈ centralizer ({x} : Set G), h * z * h⁻¹ = z ∨ h * z * h⁻¹ = z * x := by
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx2, pow_two] at h
    exact h
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2, pow_two] at h
    exact h
  have hT : ∀ t, t ∈ closure ({x, z} : Set G) ↔ t = 1 ∨ t = x ∨ t = z ∨ t = x * z :=
    fun t => mem_closure_pair_iff hxx hzz hxz
  have hWz : ∀ w ∈ W, w ∈ centralizer ({z} : Set G) := by
    intro w hw
    have hPx : ∀ p ∈ Qx, p * x = x * p := fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hQxC hp)).1
    have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp (hWx hw)
    have hzw : z * w = w * z :=
      commute_of_mem_commutator_of_comm_mem hPx hwx (hkey w hw) ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm
  have hWT : ∀ w ∈ W, w ∈ closure ({x, z} : Set G) := by
    intro w hw
    have hwC : w ∈ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hWx hw, hWz w hw⟩
    exact hb w hwC (hkey w hw)
  have hzW : z ∈ W := by
    obtain ⟨w, hw, hwx⟩ := hWne
    rcases (hT w).mp (hWT w hw) with h1 | h1 | h1 | h1
    · exfalso
      apply hwx
      rw [h1]
      exact one_mem _
    · exfalso
      apply hwx
      rw [h1]
      exact Subgroup.mem_zpowers x
    · rw [← h1]
      exact hw
    · have hzeq : z = x * w := by
        rw [h1, ← mul_assoc, hxx, one_mul]
      rw [hzeq]
      exact mul_mem hxW hw
  intro h hh
  have hcomm : h * x = x * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hmem : h * z * h⁻¹ ∈ W := hWn h hh z hzW
  rcases (hT (h * z * h⁻¹)).mp (hWT _ hmem) with h1 | h1 | h1 | h1
  · exfalso
    apply hzx
    have hz1 : z = 1 := by
      calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
        _ = h⁻¹ * 1 * h := by rw [h1]
        _ = 1 := by group
    rw [hz1]
    exact one_mem _
  · exfalso
    apply hzx
    have hzx' : z = x := by
      calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
        _ = h⁻¹ * x * h := by rw [h1]
        _ = h⁻¹ * (x * h) := by rw [mul_assoc]
        _ = h⁻¹ * (h * x) := by rw [hcomm]
        _ = x := by group
    rw [hzx']
    exact Subgroup.mem_zpowers x
  · exact Or.inl h1
  · exact Or.inr (h1.trans hxz)

theorem hkey_caseI {G : Type*} [Group G] {x z : G} (hxz : x * z = z * x)
    (R W Qx P : Subgroup G) (hxR : x ∈ R) (hWR : W ≤ R)
    (hW : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x)
    (hRx : R ≤ centralizer ({x} : Set G))
    (hQxC : Qx ≤ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G))
    (hxQ : x ∈ Qx) (hzQ : z ∈ Qx) (ha : z ∈ ⁅Qx, Qx⁆)
    (hPR : P ≤ R) (hPQ : P ≤ Qx) (hPn : ∀ q ∈ Qx, ∀ p ∈ P, q * p * q⁻¹ ∈ P)
    (hsup : P ⊔ closure {x, z} = Qx) :
    ∀ w ∈ W, ∀ q ∈ Qx, q⁻¹ * w⁻¹ * q * w ∈ zpowers x := by
  have hxq : ∀ q ∈ Qx, x * q = q * x := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hQxC hq)).1).symm
  have hzq : ∀ q ∈ Qx, z * q = q * z := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hQxC hq)).2).symm
  have hTC : Subgroup.closure ({x, z} : Set G) ≤ Subgroup.centralizer (Qx : Set G) := by
    refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩)
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => (hxq h hh).symm
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => (hzq h hh).symm
  have hT : ∀ t ∈ Subgroup.closure ({x, z} : Set G), ∀ q ∈ Qx, t * q = q * t :=
    fun t ht q hq => (Subgroup.mem_centralizer_iff.1 (hTC ht) q hq).symm
  have hcomm : ⁅Qx, Qx⁆ ≤ P := commutator_le_of_sup_central hPQ hPn hsup hT
  have hzR : z ∈ R := hPR (hcomm ha)
  have hTR : Subgroup.closure ({x, z} : Set G) ≤ R :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxR, Set.singleton_subset_iff.2 hzR⟩)
  have hQR : Qx ≤ R := by
    rw [← hsup]
    exact sup_le hPR hTR
  intro w hw q hq
  have hqR : q ∈ R := hQR hq
  have hwi : w⁻¹ ∈ W := W.inv_mem hw
  have hn : w⁻¹ * q * (w⁻¹)⁻¹ * q⁻¹ ∈ zpowers x := hW w⁻¹ hwi q hqR
  have hqx : Commute q x := Subgroup.mem_centralizer_singleton_iff.1 (hRx hqR)
  have hconj : ∀ n ∈ zpowers x, q⁻¹ * n * q = n := by
    intro n hn'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn'
    have hc : q * x ^ k = x ^ k * q := hqx.zpow_right k
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have heq : q⁻¹ * w⁻¹ * q * w = q⁻¹ * (w⁻¹ * q * (w⁻¹)⁻¹ * q⁻¹) * q := by group
  rw [heq, hconj _ hn]
  exact hn

private lemma W1112_ncard_le_image_mul {G : Type*} [Group G] [Finite G]
    (S : Set G) (f : G → G) (H : Set G)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a⁻¹ * b ∈ H) :
    S.ncard ≤ (f '' S).ncard * H.ncard := by
  rw [← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn
    (fun a => (f a, (Function.invFunOn f S (f a))⁻¹ * a)) ?_ ?_
  · intro a ha
    have h : Function.invFunOn f S (f a) ∈ S ∧ f (Function.invFunOn f S (f a)) = f a :=
      Function.invFunOn_pos ⟨a, ha, rfl⟩
    exact ⟨Set.mem_image_of_mem f ha, hf _ h.1 a ha h.2⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨hfab, hu⟩ := hab
    rw [hfab] at hu
    exact mul_left_cancel hu

private lemma W1112_conj_eq_inv {G : Type*} [Group G] {o z : G} (hzi : z⁻¹ = z)
    (hoi : o⁻¹ = o) : z * (o * z) * z⁻¹ = (o * z)⁻¹ := by
  calc z * (o * z) * z⁻¹ = z * o := by group
    _ = z⁻¹ * o⁻¹ := by rw [hzi, hoi]
    _ = (o * z)⁻¹ := by group

private lemma W1112_orbit_ncard_le {G : Type*} [Group G] [Finite G] {x z : G}
    (W : Subgroup G) (hzi : z⁻¹ = z)
    (hzn : ∀ w ∈ W, z * w * z⁻¹ ∈ W) (hW2 : ∀ w ∈ W, w * w ∈ zpowers x) :
    ((fun w : G => w * z * w⁻¹) '' (W : Set G)).ncard ≤
      {d : G | d ∈ W ∧ z * d * z⁻¹ * d⁻¹ ∈ zpowers x}.ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun o : G => o * z) ?_ ?_
  · rintro o ⟨w, hw, rfl⟩
    have hoi : (w * z * w⁻¹)⁻¹ = w * z * w⁻¹ := by
      calc (w * z * w⁻¹)⁻¹ = w * z⁻¹ * w⁻¹ := by group
        _ = w * z * w⁻¹ := by rw [hzi]
    have hd : w * z * w⁻¹ * z = w * (z * w⁻¹ * z⁻¹) := by
      rw [hzi]; group
    have hdW : w * z * w⁻¹ * z ∈ W := by
      rw [hd]; exact W.mul_mem hw (hzn w⁻¹ (W.inv_mem hw))
    show w * z * w⁻¹ * z ∈ W ∧ z * (w * z * w⁻¹ * z) * z⁻¹ * (w * z * w⁻¹ * z)⁻¹ ∈ zpowers x
    refine ⟨hdW, ?_⟩
    rw [W1112_conj_eq_inv hzi hoi, ← mul_inv_rev]
    exact (zpowers x).inv_mem (hW2 _ hdW)
  · rintro o _ o' _ h
    exact mul_right_cancel h

private lemma W1112_card_le_orbit_mul {G : Type*} [Group G] [Finite G] {z : G}
    (W : Subgroup G) :
    (W : Set G).ncard ≤ ((fun w : G => w * z * w⁻¹) '' (W : Set G)).ncard *
      ((W ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G).ncard := by
  refine W1112_ncard_le_image_mul (W : Set G) (fun w : G => w * z * w⁻¹)
    ((W ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) ?_
  intro a ha b hb hab
  have hab' : a * z * a⁻¹ = b * z * b⁻¹ := hab
  have hc : z * (a⁻¹ * b) = a⁻¹ * b * z := by
    calc z * (a⁻¹ * b) = a⁻¹ * (a * z * a⁻¹) * b := by group
      _ = a⁻¹ * (b * z * b⁻¹) * b := by rw [hab']
      _ = a⁻¹ * b * z := by group
  rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine ⟨W.mul_mem (W.inv_mem ha) hb, fun h hh => ?_⟩
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hc

private lemma W1112_card_W0_le {G : Type*} [Group G] [Finite G] {x z : G}
    (hx2 : orderOf x = 2) (W : Subgroup G) :
    {d : G | d ∈ W ∧ z * d * z⁻¹ * d⁻¹ ∈ zpowers x}.ncard ≤
      2 * ((W ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G).ncard := by
  have hyp : ∀ a ∈ {d : G | d ∈ W ∧ z * d * z⁻¹ * d⁻¹ ∈ zpowers x},
      ∀ b ∈ {d : G | d ∈ W ∧ z * d * z⁻¹ * d⁻¹ ∈ zpowers x},
      (fun d : G => z * d * z⁻¹ * d⁻¹) a = (fun d : G => z * d * z⁻¹ * d⁻¹) b →
      a⁻¹ * b ∈ ((W ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rintro a ⟨haW, -⟩ b ⟨hbW, -⟩ hab
    have hθ : z * a * z⁻¹ * a⁻¹ = z * b * z⁻¹ * b⁻¹ := hab
    have hA : z * a * z⁻¹ = z * b * z⁻¹ * b⁻¹ * a := by
      calc z * a * z⁻¹ = z * a * z⁻¹ * a⁻¹ * a := by group
        _ = z * b * z⁻¹ * b⁻¹ * a := by rw [hθ]
    have hcomm : z * (a⁻¹ * b) * z⁻¹ = a⁻¹ * b := by
      calc z * (a⁻¹ * b) * z⁻¹ = (z * a * z⁻¹)⁻¹ * (z * b * z⁻¹) := by group
        _ = (z * b * z⁻¹ * b⁻¹ * a)⁻¹ * (z * b * z⁻¹) := by rw [hA]
        _ = a⁻¹ * b := by group
    have hc : z * (a⁻¹ * b) = a⁻¹ * b * z := by
      calc z * (a⁻¹ * b) = z * (a⁻¹ * b) * z⁻¹ * z := by group
        _ = a⁻¹ * b * z := by rw [hcomm]
    rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨W.mul_mem (W.inv_mem haW) hbW, fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hc
  have hsub : (fun d : G => z * d * z⁻¹ * d⁻¹) ''
      {d : G | d ∈ W ∧ z * d * z⁻¹ * d⁻¹ ∈ zpowers x} ⊆ (zpowers x : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hd.2
  have hN : (zpowers x : Set G).ncard = 2 := by
    rw [← hx2, ← Nat.card_zpowers]
    exact (Nat.card_coe_set_eq _).symm
  have himg : ((fun d : G => z * d * z⁻¹ * d⁻¹) ''
      {d : G | d ∈ W ∧ z * d * z⁻¹ * d⁻¹ ∈ zpowers x}).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub).trans hN.le
  exact (W1112_ncard_le_image_mul {d : G | d ∈ W ∧ z * d * z⁻¹ * d⁻¹ ∈ zpowers x}
    (fun d : G => z * d * z⁻¹ * d⁻¹) ((W ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)
    hyp).trans (Nat.mul_le_mul himg le_rfl)

private lemma W1112_arith {p q r t : ℕ} (hA : p ≤ q * t) (hB : q ≤ r) (hC : r ≤ 2 * t)
    (ht : t ≤ 4) : p ≤ 32 := by
  calc p ≤ q * t := hA
    _ ≤ r * t := Nat.mul_le_mul hB le_rfl
    _ ≤ (2 * t) * t := Nat.mul_le_mul hC le_rfl
    _ ≤ (2 * 4) * 4 := Nat.mul_le_mul (Nat.mul_le_mul le_rfl ht) ht
    _ = 32 := by norm_num

theorem card_W_le {G : Type*} [Group G] [Finite G] {x z : G} (hx2 : orderOf x = 2)
    (hz2 : orderOf z = 2)
    (W : Subgroup G) (hxW : x ∈ W) (hWx : W ≤ centralizer ({x} : Set G))
    (hzn : ∀ w ∈ W, z * w * z⁻¹ ∈ W)
    (hW2 : ∀ w ∈ W, w * w ∈ zpowers x)
    (hZ : Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 4) :
    Nat.card W ≤ 32 := by
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2, pow_two] at h
    exact h
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hZc : ((W ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G).ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hZ
  have hWc : Nat.card W = (W : Set G).ncard := Nat.card_coe_set_eq _
  rw [hWc]
  exact W1112_arith (W1112_card_le_orbit_mul (z := z) W)
    (W1112_orbit_ncard_le (x := x) W hzi hzn hW2) (W1112_card_W0_le (z := z) hx2 W) hZc

private theorem zpowers_comm_centralizer {G : Type*} [Group G] {x : G} :
    ∀ n ∈ zpowers x, ∀ c ∈ centralizer ({x} : Set G), c * n * c⁻¹ = n := by
  intro n hn c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hcx : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hc
  rw [(hcx.zpow_right k).eq, mul_inv_cancel_right]

def actKer {G : Type*} [Group G] (x : G) (W : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ centralizer ({x} : Set G) ∧ ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ zpowers x}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨mul_mem ha1 hb1, fun w hw => ?_⟩
    have h1 := hb2 w hw
    have h2 := ha2 w hw
    have key : a * b * w * (a * b)⁻¹ * w⁻¹
        = (a * (b * w * b⁻¹ * w⁻¹) * a⁻¹) * (a * w * a⁻¹ * w⁻¹) := by group
    rw [key, zpowers_comm_centralizer _ h1 a ha1]
    exact mul_mem h1 h2
  one_mem' := by
    refine ⟨one_mem _, fun w _ => ?_⟩
    simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨inv_mem hg1, fun w hw => ?_⟩
    have hm : (g * w * g⁻¹ * w⁻¹)⁻¹ ∈ zpowers x := inv_mem (hg2 w hw)
    have hc : g⁻¹ ∈ centralizer ({x} : Set G) := inv_mem hg1
    have key : g⁻¹ * w * (g⁻¹)⁻¹ * w⁻¹ = g⁻¹ * (g * w * g⁻¹ * w⁻¹)⁻¹ * (g⁻¹)⁻¹ := by
      group
    rw [key, zpowers_comm_centralizer _ hm g⁻¹ hc]
    exact hm

theorem actKer_conj_mem {G : Type*} [Group G] {x : G} (W : Subgroup G)
    (hWx : W ≤ centralizer ({x} : Set G))
    (hWn : ∀ h ∈ centralizer ({x} : Set G), ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    {c : G} (hc : c ∈ centralizer ({x} : Set G)) {g : G} (hg : g ∈ actKer x W) :
    c * g * c⁻¹ ∈ actKer x W := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨mul_mem (mul_mem hc hg1) (inv_mem hc), fun w hw => ?_⟩
  have hw' : c⁻¹ * w * c ∈ W := by
    have h := hWn c⁻¹ (inv_mem hc) w hw
    rwa [inv_inv] at h
  have hn := hg2 (c⁻¹ * w * c) hw'
  have key : c * g * c⁻¹ * w * (c * g * c⁻¹)⁻¹ * w⁻¹
      = c * (g * (c⁻¹ * w * c) * g⁻¹ * (c⁻¹ * w * c)⁻¹) * c⁻¹ := by
    group
  rw [key, zpowers_comm_centralizer _ hn c hc]
  exact hn

private theorem idx_mem_actKer {G : Type*} [Group G] {x : G} {W : Subgroup G} {g : G} :
    g ∈ actKer x W ↔ g ∈ centralizer ({x} : Set G) ∧ ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ zpowers x :=
  Iff.rfl

private theorem idx_comm_zpowers {G : Type*} [Group G] {x g : G}
    (hg : g ∈ centralizer ({x} : Set G)) {n : G} (hn : n ∈ zpowers x) : g * n = n * g := by
  have hxg : x ∈ centralizer ({g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact ((Subgroup.mem_centralizer_iff.mp hg) x (Set.mem_singleton x)).symm
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr hxg hn)) g (Set.mem_singleton g)

private theorem idx_conj_fix {G : Type*} [Group G] {x g : G}
    (hg : g ∈ centralizer ({x} : Set G)) {n : G} (hn : n ∈ zpowers x) : g * n * g⁻¹ = n := by
  rw [idx_comm_zpowers hg hn, mul_inv_cancel_right]

private theorem idx_conj_mem_iff {G : Type*} [Group G] {x g : G}
    (hg : g ∈ centralizer ({x} : Set G)) (n : G) :
    g * n * g⁻¹ ∈ zpowers x ↔ n ∈ zpowers x := by
  constructor
  · intro h
    have h2 := idx_conj_fix (inv_mem hg) h
    have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
    rw [e] at h2
    rw [h2]
    exact h
  · intro h
    rw [idx_conj_fix hg h]
    exact h

private theorem idx_card_subgroupOf {G : Type*} [Group G] {x : G} (hx2 : orderOf x = 2)
    {W : Subgroup G} (hxW : x ∈ W) : Nat.card ((zpowers x).subgroupOf W) = 2 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxW)).toEquiv,
    Nat.card_zpowers, hx2]

private theorem idx_mulAut_card_le {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a * a = 1) (hA : Nat.card A ≤ 16) :
    Nat.card (MulAut A) ≤ 20160 := by
  have hpow : ∀ a : A, a ^ 2 = 1 := fun a => by rw [pow_two]; exact hsq a
  have hp : IsPGroup 2 A := fun a => ⟨1, by simpa using hpow a⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hp
  have hd4 : d ≤ 4 := by
    by_contra hcon
    have h5 : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hd] at h5
    norm_num at h5
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hd
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2)]
  interval_cases d <;> decide

private def idxConjW {G : Type*} [Group G] (W Γ : Subgroup G)
    (hΓn : ∀ g ∈ Γ, ∀ w ∈ W, g * w * g⁻¹ ∈ W) (g : Γ) : W ≃* W where
  toFun w := ⟨(g : G) * (w : G) * (g : G)⁻¹, hΓn g g.2 w w.2⟩
  invFun w := ⟨(g : G)⁻¹ * (w : G) * (g : G), by
    have h := hΓn (g : G)⁻¹ (inv_mem g.2) w w.2
    rwa [inv_inv] at h⟩
  left_inv w := Subtype.ext (by group)
  right_inv w := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem idxConjW_val {G : Type*} [Group G] {W Γ : Subgroup G}
    (hΓn : ∀ g ∈ Γ, ∀ w ∈ W, g * w * g⁻¹ ∈ W) (g : Γ) (w : W) :
    ((idxConjW W Γ hΓn g w : W) : G) = (g : G) * (w : G) * (g : G)⁻¹ :=
  rfl

theorem index_actKer_le {G : Type*} [Group G] [Finite G] {x : G} (hx2 : orderOf x = 2)
    (W : Subgroup G) (hxW : x ∈ W) (hWx : W ≤ centralizer ({x} : Set G))
    (hW2 : ∀ w ∈ W, w * w ∈ zpowers x)
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ zpowers x)
    (hWcard : Nat.card W ≤ 32)
    (Γ : Subgroup G) (hΓx : Γ ≤ centralizer ({x} : Set G))
    (hΓn : ∀ g ∈ Γ, ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    (actKer x W).relIndex Γ ≤ 20160 := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup W, N = (zpowers x).subgroupOf W := ⟨_, rfl⟩
  have hmemN : ∀ a : W, a ∈ N ↔ (a : G) ∈ zpowers x := by
    intro a
    rw [hN, Subgroup.mem_subgroupOf]
  have hNcard : Nat.card N = 2 := by
    rw [hN]
    exact idx_card_subgroupOf hx2 hxW
  haveI hNnormal : N.Normal := ⟨fun n hn g => by
    rw [hmemN] at hn
    rw [hmemN]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [idx_conj_fix (hWx g.2) hn]
    exact hn⟩
  have hA16 : Nat.card (↥W ⧸ N) ≤ 16 := by
    have h1 : N.index * Nat.card N = Nat.card W := Subgroup.index_mul_card N
    have h2 : Nat.card (↥W ⧸ N) = N.index := rfl
    rw [hNcard] at h1
    omega
  have hAcomm : ∀ a b : ↥W ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmemN]
    have h := hWc (v : G)⁻¹ (inv_mem v.2) (u : G)⁻¹ (inv_mem u.2)
    convert h using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hAsq : ∀ a : ↥W ⧸ N, a * a = 1 := by
    intro a
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hmemN]
    simpa only [Subgroup.coe_mul] using hW2 (u : G) u.2
  have hMA : Nat.card (MulAut (↥W ⧸ N)) ≤ 20160 := idx_mulAut_card_le hAcomm hAsq hA16
  have hfix : ∀ g : Γ, ∀ z ∈ N, idxConjW W Γ hΓn g z = z := fun g z hz =>
    Subtype.ext (idx_conj_fix (hΓx g.2) ((hmemN z).mp hz))
  have hNmap : ∀ g : Γ, N.map (idxConjW W Γ hΓn g : ↥W →* ↥W) = N := by
    intro g
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show idxConjW W Γ hΓn g z ∈ N
      rw [hfix g z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, hfix g y hy⟩
  have hmul : ∀ g h : Γ,
      (QuotientGroup.congr N N (idxConjW W Γ hΓn (g * h)) (hNmap (g * h)) : MulAut (↥W ⧸ N)) =
        (QuotientGroup.congr N N (idxConjW W Γ hΓn g) (hNmap g) : MulAut (↥W ⧸ N)) *
          (QuotientGroup.congr N N (idxConjW W Γ hΓn h) (hNmap h) : MulAut (↥W ⧸ N)) := by
    intro g h
    apply MulEquiv.ext
    intro a
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    rw [MulAut.mul_apply]
    simp only [QuotientGroup.congr_mk]
    congr 1
    apply Subtype.ext
    simp only [idxConjW_val, Subgroup.coe_mul]
    group
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ →* MulAut (↥W ⧸ N), ∀ g : Γ,
      ψ g = QuotientGroup.congr N N (idxConjW W Γ hΓn g) (hNmap g) :=
    ⟨MonoidHom.mk' (fun g : Γ => QuotientGroup.congr N N (idxConjW W Γ hΓn g) (hNmap g)) hmul,
      fun g => rfl⟩
  have hkey : ∀ g : Γ, ∀ w : W,
      QuotientGroup.congr N N (idxConjW W Γ hΓn g) (hNmap g) (QuotientGroup.mk w) =
        QuotientGroup.mk w ↔ (g : G) * (w : G) * (g : G)⁻¹ * (w : G)⁻¹ ∈ zpowers x := by
    intro g w
    rw [QuotientGroup.congr_mk, QuotientGroup.eq, hmemN]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, idxConjW_val]
    have hwC : (w : G)⁻¹ ∈ centralizer ({x} : Set G) := inv_mem (hWx w.2)
    have e1 : ((g : G) * (w : G) * (g : G)⁻¹)⁻¹ * (w : G) =
        (w : G)⁻¹ * ((g : G) * (w : G) * (g : G)⁻¹ * (w : G)⁻¹)⁻¹ * (w : G)⁻¹⁻¹ := by
      group
    rw [e1, idx_conj_mem_iff hwC, Subgroup.inv_mem_iff]
  have hker : ψ.ker = (actKer x W).subgroupOf Γ := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, idx_mem_actKer]
    constructor
    · intro hg
      refine ⟨hΓx g.2, fun w hw => ?_⟩
      have h1 := DFunLike.congr_fun hg (QuotientGroup.mk (⟨w, hw⟩ : W))
      rw [MulAut.one_apply] at h1
      exact (hkey g ⟨w, hw⟩).mp h1
    · rintro ⟨-, hk⟩
      apply MulEquiv.ext
      intro a
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
      rw [MulAut.one_apply]
      exact (hkey g u).mpr (hk u u.2)
  have hrel : (actKer x W).relIndex Γ = ψ.ker.index := by
    rw [hker]
    rfl
  rw [hrel, Subgroup.index_ker]
  exact le_trans (Nat.card_le_card_of_injective _ Subtype.coe_injective) hMA

theorem hkey_caseII {G : Type*} [Group G] [Finite G] {x z : G} (hx2 : orderOf x = 2)
    (hz2 : orderOf z = 2) (hxz : x * z = z * x) (hzx : z ∉ zpowers x)
    (R W Qx : Subgroup G) (hxR : x ∈ R) (hWR : W ≤ R) (hxW : x ∈ W)
    (hWn : ∀ h ∈ centralizer ({x} : Set G), ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hW2 : ∀ w ∈ W, w * w ∈ zpowers x)
    (hW : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ zpowers x)
    (hRx : R ≤ centralizer ({x} : Set G))
    (hPT : R ⊓ centralizer ({z} : Set G) ≤ closure {x, z})
    (hQxC : Qx ≤ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G))
    (hxQ : x ∈ Qx) (hzQ : z ∈ Qx)
    (hnorm : centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (Qx : Set G))
    (ha : z ∈ ⁅Qx, Qx⁆)
    (hc : ∀ P : Subgroup G, P ≤ Qx →
      centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (P : Set G) →
      P ≤ closure {x, z} ∨ P ⊔ closure {x, z} = Qx)
    (hd : 2 ^ 17 ≤ Nat.card Qx) :
    ∀ w ∈ W, ∀ q ∈ Qx, q⁻¹ * w⁻¹ * q * w ∈ zpowers x := by
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx2, pow_two] at h
    exact h
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2, pow_two] at h
    exact h
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzC : z ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm
  have hzn : ∀ w ∈ W, z * w * z⁻¹ ∈ W := fun w hw => hWn z hzC w hw
  have hWx : W ≤ centralizer ({x} : Set G) := fun w hw => hRx (hWR hw)
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ zpowers x :=
    fun a ha' b hb => hW a ha' b (hWR hb)
  have hQxcen : Qx ≤ centralizer ({x} : Set G) :=
    fun q hq => (Subgroup.mem_inf.mp (hQxC hq)).1
  have hQxx : ∀ q ∈ Qx, q * x = x * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQxcen hq)
  have hQxz : ∀ q ∈ Qx, q * z = z * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hQxC hq)).2
  have hT4 : Nat.card (closure ({x, z} : Set G)) ≤ 4 := card_closure_pair_le_four hxx hzz hxz
  have hZT : W ⊓ centralizer ({z} : Set G) ≤ closure ({x, z} : Set G) := fun g hg =>
    hPT (Subgroup.mem_inf.mpr ⟨hWR (Subgroup.mem_inf.mp hg).1, (Subgroup.mem_inf.mp hg).2⟩)
  have hZ : Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 4 :=
    le_trans (Subgroup.card_le_of_le hZT) hT4
  have hWcard : Nat.card W ≤ 32 := card_W_le hx2 hz2 W hxW hWx hzn hW2 hZ
  have hGn : ∀ g ∈ Qx, ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw => hWn g (hQxcen hg) w hw
  have hidx : (actKer x W).relIndex Qx ≤ 20160 :=
    index_actKer_le hx2 W hxW hWx hW2 hWc hWcard Qx hQxcen hGn
  have hTC : closure ({x, z} : Set G) ≤ centralizer (Qx : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => hQxx h hh
    · rw [hg]
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => hQxz h hh
  have hTcomm : ∀ t ∈ closure ({x, z} : Set G), ∀ q ∈ Qx, t * q = q * t :=
    fun t ht q hq => (Subgroup.mem_centralizer_iff.mp (hTC ht) q hq).symm
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = Qx ⊓ actKer x W := ⟨_, rfl⟩
  have hPmem : ∀ g, g ∈ P ↔ g ∈ Qx ∧ g ∈ actKer x W := fun g => by
    rw [hP, Subgroup.mem_inf]
  have hmemK : ∀ g, g ∈ actKer x W ↔
      g ∈ centralizer ({x} : Set G) ∧ ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ zpowers x :=
    fun g => Iff.rfl
  have hPQ : P ≤ Qx := fun g hg => ((hPmem g).mp hg).1
  have hfwd : ∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G),
      ∀ h ∈ P, c * h * c⁻¹ ∈ P := by
    intro c hc' h hh
    obtain ⟨hhQ, hhK⟩ := (hPmem h).mp hh
    refine (hPmem _).mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hnorm hc') h).mp hhQ
    · exact actKer_conj_mem W hWx hWn (Subgroup.mem_inf.mp hc').1 hhK
  have hCn : centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (P : Set G) := by
    intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hfwd c hc' h hh, fun hh => ?_⟩
    have h1 := hfwd c⁻¹ (inv_mem hc') (c * h * c⁻¹) hh
    have e : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h := by group
    rw [e] at h1
    exact h1
  rcases hc P hPQ hCn with hPT' | hsupP
  · exfalso
    have h1 : Nat.card P ≤ 4 := le_trans (Subgroup.card_le_of_le hPT') hT4
    have h2 := Subgroup.relIndex_mul_card (H := actKer x W) (K := Qx)
    have h3 : Nat.card ↥(actKer x W ⊓ Qx : Subgroup G) = Nat.card P := by
      rw [hP, inf_comm]
    have h4 : (actKer x W).relIndex Qx * Nat.card ↥(actKer x W ⊓ Qx : Subgroup G) ≤ 20160 * 4 := by
      rw [h3]
      exact Nat.mul_le_mul hidx h1
    rw [h2] at h4
    norm_num at hd
    omega
  · have hcomm : ⁅Qx, Qx⁆ ≤ P :=
      commutator_le_of_sup_central hPQ (fun q hq y hy => hfwd q (hQxC hq) y hy) hsupP hTcomm
    have hzP : z ∈ P := hcomm ha
    have hzK : z ∈ actKer x W := ((hPmem z).mp hzP).2
    have hWK : ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ zpowers x := by
      intro w hw
      have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp (hWx hw)
      have e : x * w * x⁻¹ * w⁻¹ = 1 := by
        rw [← hwx]
        group
      rw [e]
      exact one_mem _
    have hxK : x ∈ actKer x W := (hmemK x).mpr ⟨hxC, hWK⟩
    have hTK : closure ({x, z} : Set G) ≤ actKer x W := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [hg]
        exact hxK
      · rw [hg]
        exact hzK
    have hQK : Qx ≤ actKer x W := by
      rw [← hsupP]
      exact sup_le (fun g hg => ((hPmem g).mp hg).2) hTK
    intro w hw q hq
    have hq' : q⁻¹ ∈ actKer x W := hQK (inv_mem hq)
    have h5 := ((hmemK q⁻¹).mp hq').2 w⁻¹ (inv_mem hw)
    simpa only [inv_inv] using h5

theorem central_lemma_R {G : Type*} [Group G] [Finite G] {x z : G}
    (R : Subgroup G) (hR2 : IsPGroup 2 R) (hRx : R ≤ centralizer ({x} : Set G))
    (hRn : ∀ h ∈ centralizer ({x} : Set G), ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hCR : ∀ y ∈ centralizer ({x} : Set G), (∀ r ∈ R, y * r = r * y) → y ∈ R)
    (hx2 : orderOf x = 2) (hz2 : orderOf z = 2) (hxz : x * z = z * x)
    (hzx : z ∉ zpowers x)
    (Qx : Subgroup G) (hQx2 : IsPGroup 2 Qx)
    (hQxC : Qx ≤ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G))
    (hxQ : x ∈ Qx) (hzQ : z ∈ Qx)
    (hnorm : centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (Qx : Set G))
    (ha : z ∈ ⁅Qx, Qx⁆)
    (hb : ∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G),
      (∀ q ∈ Qx, q⁻¹ * c⁻¹ * q * c ∈ zpowers x) → c ∈ closure {x, z})
    (hc : ∀ P : Subgroup G, P ≤ Qx →
      centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (P : Set G) →
      P ≤ closure {x, z} ∨ P ⊔ closure {x, z} = Qx)
    (hd : 2 ^ 17 ≤ Nat.card Qx)
    (he : ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) →
      centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (P : Set G) → P ≤ Qx) :
    ∀ h ∈ centralizer ({x} : Set G), h * z * h⁻¹ = z ∨ h * z * h⁻¹ = z * x := by
  have hcomm : Commute x z := hxz
  have hxX : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzX : z ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxz.symm
  have hxR : x ∈ R :=
    hCR x hxX (fun r hr => (Subgroup.mem_centralizer_singleton_iff.1 (hRx hr)).symm)
  have hne : ∃ r ∈ R, r ∉ zpowers x := by
    by_contra hcon
    have hall : ∀ r ∈ R, r ∈ zpowers x := fun r hr => by
      by_contra hr'
      exact hcon ⟨r, hr, hr'⟩
    have hzR : z ∈ R := hCR z hzX (fun r hr => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hall r hr)
      exact (hcomm.symm.zpow_right k).eq)
    exact hzx (hall z hzR)
  obtain ⟨W, hWR, hxW, hWne, hWn, hW2, hW⟩ := exists_W hx2 R hR2 hxR hRx hRn hne
  have hPp : IsPGroup 2 ((R ⊓ centralizer ({z} : Set G) : Subgroup G)) := hR2.to_inf_left
  have hPC : R ⊓ centralizer ({z} : Set G) ≤
      centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) := by
    intro p hp
    exact Subgroup.mem_inf.2 ⟨hRx (Subgroup.mem_inf.1 hp).1, (Subgroup.mem_inf.1 hp).2⟩
  have hCP : ∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G),
      ∀ p ∈ R ⊓ centralizer ({z} : Set G), c * p * c⁻¹ ∈ R ⊓ centralizer ({z} : Set G) := by
    intro c hc' p hp
    obtain ⟨hcX, hcZ⟩ := Subgroup.mem_inf.1 hc'
    obtain ⟨hpR, hpZ⟩ := Subgroup.mem_inf.1 hp
    refine Subgroup.mem_inf.2 ⟨hRn c hcX p hpR, ?_⟩
    have hcZ' : Commute c z := Subgroup.mem_centralizer_singleton_iff.1 hcZ
    have hpZ' : Commute p z := Subgroup.mem_centralizer_singleton_iff.1 hpZ
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((hcZ'.mul_left hpZ').mul_left hcZ'.inv_left).eq
  have hCnorm : centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) ≤
      normalizer ((R ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      exact hCP c hc' p hp
    · intro hp
      have h2 := hCP c⁻¹ (inv_mem hc') (c * p * c⁻¹) hp
      have e : c⁻¹ * (c * p * c⁻¹) * c⁻¹⁻¹ = p := by group
      rw [e] at h2
      exact h2
  have hPQ : R ⊓ centralizer ({z} : Set G) ≤ Qx := he _ hPp hPC hCnorm
  have hPn : ∀ q ∈ Qx, ∀ p ∈ R ⊓ centralizer ({z} : Set G),
      q * p * q⁻¹ ∈ R ⊓ centralizer ({z} : Set G) :=
    fun q hq p hp => hCP q (hQxC hq) p hp
  rcases hc (R ⊓ centralizer ({z} : Set G)) hPQ hCnorm with hPT | hsup
  ·
    have hkey := hkey_caseII hx2 hz2 hxz hzx R W Qx hxR hWR hxW hWn hW2 hW hRx hPT hQxC hxQ
      hzQ hnorm ha hc hd
    exact central_final hx2 hz2 hxz hzx Qx hQxC hzQ ha hb W (hWR.trans hRx) hxW hWn hWne hkey
  ·
    have hkey := hkey_caseI hxz R W Qx (R ⊓ centralizer ({z} : Set G)) hxR hWR hW hRx hQxC
      hxQ hzQ ha inf_le_left hPQ hPn hsup
    exact central_final hx2 hz2 hxz hzx Qx hQxC hzQ ha hb W (hWR.trans hRx) hxW hWn hWne hkey

end CFSG.GF2Type.Widths1112
