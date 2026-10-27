module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem card_comap_of_surjective' {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Surjective f) (N : Subgroup H) :
    Nat.card (N.comap f) = Nat.card f.ker * Nat.card N := by
  have h1 := Subgroup.card_mul_index (N.comap f)
  rw [Subgroup.index_comap_of_surjective _ hf] at h1
  have h2 := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h2
  have h3 := Subgroup.card_mul_index N
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, ← h2, ← h3]
  ring

theorem sec8t84_rank_lift {A : Type} [Group A] [Finite A] (N V : Subgroup A) [N.Normal]
    (hN : Odd (Nat.card N)) (hV : IsElemAb2 V 4) (hVN : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v)
    (hrk : ∀ s : A ⧸ N, orderOf s = 2 →
      CFSG.Open.pRank 2 (centralizer ({s} : Set (A ⧸ N))) = 4)
    (s : A) (hs : s * s = 1) :
    ∃ D : Subgroup A, N ≤ D ∧ s ∈ D ∧ (∀ x ∈ D, x * x ∈ N) ∧
      (∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ N) ∧ Nat.card D = 16 * Nat.card N := by
  by_cases hsN : s ∈ N
  ·
    have hcop : Nat.Coprime (Nat.card V) (Nat.card N) := by
      rw [hV.2]
      exact (Nat.coprime_pow_left_iff (n := 4) (by norm_num) 2 _).mpr
        (Nat.coprime_two_left.mpr hN)
    have hd : V ⊓ N = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
    refine ⟨V ⊔ N, le_sup_right, Subgroup.mem_sup_right hsN, ?_, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_sup_of_normal_right] at hx
      obtain ⟨v, hv, n, hn, rfl⟩ := hx
      have hcomm : v * n = n * v := hVN v hv n hn
      have hv2 : v * v = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hV.1 hv
      have hsq : (v * n) * (v * n) = n * n := by
        calc (v * n) * (v * n) = v * (n * v) * n := by group
          _ = v * (v * n) * n := by rw [← hcomm]
          _ = (v * v) * (n * n) := by group
          _ = n * n := by rw [hv2, one_mul]
      rw [hsq]
      exact N.mul_mem hn hn
    · intro x hx y hy
      rw [Subgroup.mem_sup_of_normal_right] at hx hy
      obtain ⟨v₁, hv₁, n₁, hn₁, rfl⟩ := hx
      obtain ⟨v₂, hv₂, n₂, hn₂, rfl⟩ := hy
      have hn1 : QuotientGroup.mk' N n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
      have hn2 : QuotientGroup.mk' N n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
      have hcomm : Commute (QuotientGroup.mk' N v₁) (QuotientGroup.mk' N v₂) := by
        rw [commute_iff_eq, ← map_mul, ← map_mul, CFSG.Open.IsElemAbelian.comm hV.1 hv₁ hv₂]
      have hker : QuotientGroup.mk' N
          ((v₁ * n₁) * (v₂ * n₂) * (v₁ * n₁)⁻¹ * (v₂ * n₂)⁻¹) = 1 := by
        simp only [map_mul, map_inv, hn1, hn2, mul_one]
        rw [hcomm.mul_inv_cancel, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp hker
    · rw [sec124_card_sup hVN hd, hV.2]
      norm_num
  ·
    let sbar : A ⧸ N := QuotientGroup.mk' N s
    have hsbar_sq : sbar * sbar = 1 := by
      dsimp only [sbar]
      rw [← map_mul, hs, map_one]
    have hsbar_ne : sbar ≠ 1 := by
      intro h
      exact hsN ((QuotientGroup.eq_one_iff s).mp h)
    have horder : orderOf sbar = 2 :=
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hsbar_sq) hsbar_ne
    have hC4 : CFSG.Open.pRank 2 (Subgroup.centralizer ({sbar} : Set (A ⧸ N))) = 4 :=
      hrk sbar horder
    let S : Set ℕ := {k | ∃ E : Subgroup (A ⧸ N),
      E ≤ Subgroup.centralizer ({sbar} : Set (A ⧸ N)) ∧
        CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}
    have hS4 : sSup S = 4 := hC4
    have hbdd : BddAbove S := ⟨Nat.card (A ⧸ N), fun k hk => by
      obtain ⟨E, -, -, hcard⟩ := hk
      have h1 : 2 ^ k ≤ Nat.card (A ⧸ N) := by
        rw [← hcard]
        exact Subgroup.card_le_card_group E
      have h2 : k < 2 ^ k := Nat.lt_two_pow_self
      omega⟩
    have hne : S.Nonempty := ⟨0, ⊥, bot_le, CFSG.Open.isElemAbelian_bot 2, by simp⟩
    have h4 : (4 : ℕ) ∈ S := by
      have h := Nat.sSup_mem hne hbdd
      rwa [hS4] at h
    obtain ⟨Ē, hĒle, hĒea, hĒcard⟩ := h4
    have hsbar_mem : sbar ∈ Ē := by
      by_contra hsbar_notin
      have hc : ∀ a ∈ Ē, ∀ b ∈ zpowers sbar, a * b = b * a := by
        intro a ha b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have hcomm : Commute a sbar := by
          rw [commute_iff_eq, ← Subgroup.mem_centralizer_singleton_iff]
          exact hĒle ha
        exact (hcomm.zpow_right k).eq
      have hd : Ē ⊓ zpowers sbar = ⊥ := by
        have h2 : Nat.card (zpowers sbar) = 2 := by rw [Nat.card_zpowers, horder]
        have hle : Ē ⊓ zpowers sbar ≤ zpowers sbar := inf_le_right
        have hcard_le : Nat.card ↥(Ē ⊓ zpowers sbar) ≤ 2 := h2 ▸ Subgroup.card_le_of_le hle
        have hne2 : Nat.card ↥(Ē ⊓ zpowers sbar) ≠ 2 := by
          intro hc2
          have heq : Ē ⊓ zpowers sbar = zpowers sbar :=
            Subgroup.eq_of_le_of_card_ge hle (by omega)
          have : sbar ∈ Ē ⊓ zpowers sbar := by
            rw [heq]
            exact Subgroup.mem_zpowers sbar
          exact hsbar_notin this.1
        exact Subgroup.eq_bot_of_card_le (H := Ē ⊓ zpowers sbar) (by omega)
      have hE'le : Ē ⊔ zpowers sbar ≤ Subgroup.centralizer ({sbar} : Set (A ⧸ N)) := by
        refine sup_le hĒle ?_
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have hE'ea : CFSG.Open.IsElemAbelian 2 (Ē ⊔ zpowers sbar) :=
        CFSG.Open.IsElemAbelian.sup_of_commute hĒea
          (CFSG.Open.isElemAbelian_zpowers (p := 2) (by rw [pow_two]; exact hsbar_sq)) hc
      have hE'card : Nat.card ↥(Ē ⊔ zpowers sbar) = 2 ^ 5 := by
        rw [sec124_card_sup hc hd, hĒcard, Nat.card_zpowers, horder]
        norm_num
      have h5 : (5 : ℕ) ∈ S := ⟨Ē ⊔ zpowers sbar, hE'le, hE'ea, hE'card⟩
      have := le_csSup hbdd h5
      omega
    refine ⟨Ē.comap (QuotientGroup.mk' N), ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn
      rw [Subgroup.mem_comap]
      have : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [this]
      exact Ē.one_mem
    · rw [Subgroup.mem_comap]
      exact hsbar_mem
    · intro x hx
      rw [Subgroup.mem_comap] at hx
      have : QuotientGroup.mk' N (x * x) = 1 := by
        rw [map_mul]
        exact CFSG.Open.IsElemAbelian.mul_self_eq_one hĒea hx
      exact (QuotientGroup.eq_one_iff (x * x)).mp this
    · intro x hx y hy
      rw [Subgroup.mem_comap] at hx hy
      have hcomm : Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) :=
        CFSG.Open.IsElemAbelian.comm hĒea hx hy
      have hxy : QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [hcomm.mul_inv_cancel, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp hxy
    · rw [card_comap_of_surjective' (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) Ē,
        QuotientGroup.ker_mk', hĒcard]
      ring

end CFSG.OddStandard.SmallF3.Omega
