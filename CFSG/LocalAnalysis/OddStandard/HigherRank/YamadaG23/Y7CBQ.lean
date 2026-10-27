module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBDef

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7c_X0_le_X (c : Ctx7 G L) (hb : B7Std c) : f4X0 c.s ≤ y7cX c.s := by
  have hN : f4N c.s ≤ y7cX c.s := by
    intro n hn
    rw [y7cX, Subgroup.mem_set_normalizer_iff]
    intro m
    constructor
    · intro hm
      exact y54_N_norm_M3 c.toCtx5 hb.hH n hn m hm
    · intro hm
      have hn' : n⁻¹ ∈ f4N c.s := (f4N c.s).inv_mem hn
      have h := y54_N_norm_M3 c.toCtx5 hb.hH n⁻¹ hn' (n * m * n⁻¹) hm
      rwa [show n⁻¹ * (n * m * n⁻¹) * (n⁻¹)⁻¹ = m by group] at h
  intro x hx
  obtain ⟨hxH, hxF⟩ := Subgroup.mem_inf.mp hx
  exact hN (Subgroup.mem_inf.mpr
    ⟨hxH, Subgroup.centralizer_le_normalizer (c.s.fr.F : Set G) hxF⟩)

theorem y7c_B_t_mem_Q (c : Ctx7 G L) (hb : B7Std c) : y7cTC c hb ∈ y7cQC c := by
  refine (mem_y7cImg c.s).mpr ⟨⟨c.s.t, y7c_t_mem_X c hb⟩, ?_, rfl⟩
  exact y54_P_le_X0 hb.hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))

private theorem y7cImg_mono' (s : Setting3 G L) {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    y7cImg s H₁ ≤ y7cImg s H₂ := by
  intro γ hγ
  obtain ⟨x, hx, rfl⟩ := (mem_y7cImg s).mp hγ
  exact (mem_y7cImg s).mpr ⟨x, h hx, rfl⟩

private theorem y7cImg_sup' (s : Setting3 G L) {H₁ H₂ : Subgroup G}
    (h₁ : H₁ ≤ y7cX s) (h₂ : H₂ ≤ y7cX s) :
    y7cImg s (H₁ ⊔ H₂) = y7cImg s H₁ ⊔ y7cImg s H₂ := by
  unfold y7cImg
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

private theorem y7cTC_sq' (c : Ctx7 G L) (hb : B7Std c) : y7cTC c hb ^ 2 = 1 := by
  have ht2 : c.s.t ^ 2 = 1 := y7c_t_sq c.s
  rw [show y7cTC c hb = y7cPi c.s ⟨c.s.t, y7c_t_mem_X c hb⟩ from rfl, ← map_pow]
  have h : (⟨c.s.t, y7c_t_mem_X c hb⟩ : ↥(y7cX c.s)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using ht2
  rw [h, map_one]

private theorem y7c_img_P_le_zpowers (c : Ctx7 G L) (hb : B7Std c) :
    y7cImg c.s (f4P c.s) ≤ Subgroup.zpowers (y7cTC c hb) := by
  have hFX : c.s.fr.F ≤ y7cX c.s :=
    (y54_M3_cand c.toCtx5 hb.hH).1.trans (y7c_M3_le_X c.s)
  have htX : Subgroup.zpowers c.s.t ≤ y7cX c.s :=
    Subgroup.zpowers_le.mpr (y7c_t_mem_X c hb)
  have hF : y7cImg c.s c.s.fr.F = ⊥ := by
    apply le_antisymm _ bot_le
    intro γ hγ
    obtain ⟨x, hxF, hxpi⟩ := (mem_y7cImg c.s).mp hγ
    rw [Subgroup.mem_bot, ← hxpi, y7cPi_eq_one_iff]
    exact (y54_M3_cand c.toCtx5 hb.hH).1 hxF
  have hz : y7cImg c.s (Subgroup.zpowers c.s.t) ≤ Subgroup.zpowers (y7cTC c hb) := by
    intro γ hγ
    obtain ⟨x, hx, hxpi⟩ := (mem_y7cImg c.s).mp hγ
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    rw [← hxpi]
    have hxeq : x = (⟨c.s.t, y7c_t_mem_X c hb⟩ : ↥(y7cX c.s)) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [hxeq, map_zpow]
  calc y7cImg c.s (f4P c.s)
      = y7cImg c.s (c.s.fr.F ⊔ Subgroup.zpowers c.s.t) := rfl
    _ = y7cImg c.s c.s.fr.F ⊔ y7cImg c.s (Subgroup.zpowers c.s.t) :=
        y7cImg_sup' c.s hFX htX
    _ ≤ Subgroup.zpowers (y7cTC c hb) := by rw [hF, bot_sup_eq]; exact hz

private theorem y7c_img_P_card_le (c : Ctx7 G L) (hb : B7Std c) :
    Nat.card ↥(y7cImg c.s (f4P c.s)) ≤ 2 := by
  have hle := Subgroup.card_le_of_le (y7c_img_P_le_zpowers c hb)
  rw [Nat.card_zpowers] at hle
  have hdvd : orderOf (y7cTC c hb) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (y7cTC_sq' c hb)
  have h2 : orderOf (y7cTC c hb) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem y7c_B_Q_two (c : Ctx7 G L) (hb : B7Std c) : IsPGroup 2 ↥(y7cQC c) := by
  intro q
  refine ⟨1, ?_⟩
  obtain ⟨x, hxH, hxpi⟩ := (mem_y7cImg c.s).mp q.2
  have hx2 : (x : G) ^ 2 = 1 := y54_X0_sq c.toCtx5 hb.hH (x : G) hxH
  have hx2' : x ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hx2
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
  rw [← hxpi, ← map_pow, hx2', map_one]

theorem y7c_B_Q_card (c : Ctx7 G L) (hb : B7Std c) : Nat.card ↥(y7cQC c) ≤ 4 := by
  have hA : y7cImg c.s (f4P c.s) ≤ y7cQC c := y7cImg_mono' c.s (y54_P_le_X0 hb.hH)
  by_cases hle : f4X0 c.s ≤ f4P c.s
  · calc Nat.card ↥(y7cQC c) ≤ Nat.card ↥(y7cImg c.s (f4P c.s)) :=
          Subgroup.card_le_of_le (y7cImg_mono' c.s hle)
      _ ≤ 2 := y7c_img_P_card_le c hb
      _ ≤ 4 := by norm_num
  · obtain ⟨a, haX0, haP⟩ := Set.not_subset.mp hle
    have haX : a ∈ y7cX c.s := y7c_X0_le_X c hb haX0
    let aX : ↥(y7cX c.s) := ⟨a, haX⟩
    have haQ : y7cPi c.s aX ∈ y7cQC c :=
      (mem_y7cImg c.s).mpr ⟨aX, haX0, rfl⟩
    let f : Bool × ↥(y7cImg c.s (f4P c.s)) → ↥(y7cQC c) := fun p =>
      match p.1 with
      | false => ⟨(p.2 : y7cGam c.s), hA p.2.2⟩
      | true => ⟨y7cPi c.s aX * (p.2 : y7cGam c.s), (y7cQC c).mul_mem haQ (hA p.2.2)⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨q, hq⟩
      obtain ⟨x, hxH, hxpi⟩ := (mem_y7cImg c.s).mp hq
      rcases y54_X0_cosets hb.hH a haX0 (x : G) hxH with haP' | hxP | haixP
      · exact absurd haP' haP
      · have hxP' : y7cPi c.s x ∈ y7cImg c.s (f4P c.s) :=
          (mem_y7cImg c.s).mpr ⟨x, hxP, rfl⟩
        refine ⟨(false, ⟨y7cPi c.s x, hxP'⟩), ?_⟩
        apply Subtype.ext
        simp only [f]
        exact hxpi
      · have hmemX : a⁻¹ * (x : G) ∈ y7cX c.s :=
          (y7cX c.s).mul_mem ((y7cX c.s).inv_mem haX) x.2
        have hyP : y7cPi c.s ⟨a⁻¹ * (x : G), hmemX⟩ ∈ y7cImg c.s (f4P c.s) :=
          (mem_y7cImg c.s).mpr ⟨⟨a⁻¹ * (x : G), hmemX⟩, haixP, rfl⟩
        refine ⟨(true, ⟨y7cPi c.s ⟨a⁻¹ * (x : G), hmemX⟩, hyP⟩), ?_⟩
        apply Subtype.ext
        simp only [f]
        rw [← hxpi]
        have hprod : aX * (⟨a⁻¹ * (x : G), hmemX⟩ : ↥(y7cX c.s)) = x := by
          apply Subtype.ext
          change a * (a⁻¹ * (x : G)) = (x : G)
          group
        rw [← map_mul, hprod]
    have hbound := Nat.card_le_card_of_surjective f hsurj
    have hb2 : Nat.card Bool = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [Nat.card_prod, hb2] at hbound
    have hAcard := y7c_img_P_card_le c hb
    omega

theorem y7c_B_Q_J (c : Ctx7 G L) (hb : B7Std c) :
    ∀ q ∈ y7cQC c, ∀ j ∈ y7cJC c, q * j = j * q := by
  intro q hq j hj
  obtain ⟨x, hxH, hxpi⟩ := (mem_y7cImg c.s).mp hq
  obtain ⟨y, hyJ, hypi⟩ := (mem_y7cImg c.s).mp hj
  have hyN : (y : G) ∈ normIn L c.s.fr.F :=
    Subgroup.commutator_le_self (normIn L c.s.fr.F) hyJ
  have hc : ⁅(y : G), (x : G)⁆ ∈ c.s.fr.F := y54_NL_X0 hb.hH (y : G) hyN (x : G) hxH
  have hcM : ⁅(x : G), (y : G)⁆ ∈ M3 c.s := by
    rw [← commutatorElement_inv]
    exact (M3 c.s).inv_mem ((y54_M3_cand c.toCtx5 hb.hH).1 hc)
  have hmap := map_commutatorElement (f := y7cPi c.s) (g₁ := x) (g₂ := y)
  have hcomm : ⁅y7cPi c.s x, y7cPi c.s y⁆ = 1 := by
    rw [← hmap]
    exact (y7cPi_eq_one_iff c.s ⁅x, y⁆).mpr (by
      change ⁅(x : G), (y : G)⁆ ∈ M3 c.s
      exact hcM)
  rw [← hxpi, ← hypi]
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

end CFSG.OddStandard.HigherRank.YamadaG23
