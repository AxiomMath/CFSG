module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx5

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem conjugate_card {G : Type} [Group G] (H : Subgroup G) (g : G) :
    Nat.card ↥(conjugate H g) = Nat.card ↥H := by
  rw [conjugate_eq_comap]; exact Basic.card_comap_conj H g

theorem not_comm_of_isDihedralTwoGroup {Y : Type} [Group Y] {n : ℕ} (h : IVK.IsDihedralTwoGroup Y n)
    (h8 : 8 ≤ Nat.card Y) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨-, k, hk, hk2, ⟨e⟩⟩ := h
  haveI : NeZero k := ⟨by omega⟩
  have hcard : Nat.card Y = 2 * k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hk3 : 3 ≤ k := by omega
  refine ⟨e.symm (DihedralGroup.r 1), e.symm (DihedralGroup.sr 0), ?_⟩
  intro hcomm
  have h1 := congrArg e hcomm
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
  have h2 : (0 : ZMod k) - 1 = 0 + 1 := by
    have := DihedralGroup.sr.inj h1
    exact this
  have h3 : ((2 : ℕ) : ZMod k) = 0 := by
    push_cast
    linear_combination (-1 : ZMod k) * h2
  have h4 : k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 k).1 h3
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem not_comm_of_isSemidihedralTwoGroup {Y : Type} [Group Y] {n : ℕ}
    (h : IVK.IsSemidihedralTwoGroup Y n) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨hn, ⟨e⟩⟩ := h
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ x y : Open.SemidihedralGroup n, x * y = y * x := by
    intro x y
    have h1 := hcon (e.symm x) (e.symm y)
    calc x * y = e (e.symm x * e.symm y) := by simp
      _ = e (e.symm y * e.symm x) := by rw [h1]
      _ = y * x := by simp
  have hcen : Subgroup.center (Open.SemidihedralGroup n) = ⊤ := by
    ext x
    simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
    intro y
    exact hcomm y x
  have h1 := Semidihedral.center_card n hn
  rw [hcen, Subgroup.card_top, Semidihedral.card n (by omega)] at h1
  have : 2 ^ n ≥ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn
  omega

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem nab_quot {K : Subgroup G} (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hK : K = K₁ ∨ K = K₂)
    (hQS : Qof S K ≤ S1 S K₁) (h8 : 8 * Nat.card ↥(Qof S K) ≤ Nat.card ↥(S1 S K₁)) :
    ∃ _ : ((Qof S K).subgroupOf (S1 S K₁)).Normal,
      ∃ a b : ↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁), a * b ≠ b * a := by
  have hK' : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by rcases hK with rfl | rfl <;> simp
  obtain ⟨hN, hds⟩ := hs.fused.p66.2.2.1 K hK'
  refine ⟨hN, ?_⟩
  have hXcard : Nat.card (↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁)) * Nat.card ↥(Qof S K) =
      Nat.card ↥(S1 S K₁) := by
    have h1 : Nat.card ↥((Qof S K).subgroupOf (S1 S K₁)) = Nat.card ↥(Qof S K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Qof S K).subgroupOf (S1 S K₁))
    rw [h1] at this
    exact this.symm
  have h8' : 8 ≤ Nat.card (↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁)) := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < Nat.card ↥(Qof S K) := Nat.card_pos
    have := Nat.mul_lt_mul_of_pos_right hcon hpos
    omega
  rcases hds with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact not_comm_of_isDihedralTwoGroup hn h8'
  · exact not_comm_of_isSemidihedralTwoGroup hn

theorem card_S1_eq (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Nat.card ↥(S1 S K₁) = 2 * Nat.card ↥(conjugate (Vof S K₁ W₂) h) * Nat.card ↥(Qof S K₂) := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  obtain ⟨-, hcard⟩ := hs.card_S1 hII
  have hP := hs.card_P hII
  have hV := hs.V₁h_card hII hq
  rw [← hNN] at hP
  calc Nat.card ↥(S1 S K₁) = (2 * e) * Nat.card ↥(Pz S z) := by rw [hcard, hri]
    _ = e * (2 * Nat.card ↥(Pz S z)) := by ring
    _ = e * (Nat.card ↥(Pof S K₁) * Nat.card ↥(Pof S K₁)) := by rw [← hP]
    _ = (2 * Nat.card ↥(conjugate (Vof S K₁ W₂) h)) * (e * Nat.card ↥(Pof S K₁)) := by
        rw [hV]; ring
    _ = 2 * Nat.card ↥(conjugate (Vof S K₁ W₂) h) * Nat.card ↥(Qof S K₂) := by rw [hq2]

theorem cent_le_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {x : G} (hxS : x ∈ S) (hxc : ∀ a ∈ Vof S K₁ W₂, x * a = a * x) : x ∈ S1 S K₁ := by
  by_contra hn
  obtain ⟨hx1, -⟩ := hs.swap_of_not_mem hII hxS hn
  have hle : Vof S K₁ W₂ ≤ zpowers z := by
    intro a ha
    have haK₁ : a ∈ K₁ := ha.2.2
    have hxa : x * a * x⁻¹ ∈ K₁ := by
      rw [hxc a ha]
      simpa using haK₁
    have haK₂ : a ∈ K₂ := by
      have : a ∈ conjugate K₁ x := mem_conjugate_iff.2 hxa
      rwa [hx1] at this
    have haP : a ∈ Pof S K₁ ⊓ Pof S K₂ := ⟨ha.2, ⟨ha.2.1, haK₂⟩⟩
    rwa [hs.P_inf hII] at haP
  have h1 := Subgroup.card_le_of_le hle
  have h2 := M.card_zpowers_of_sq hs.z_sq hs.z_ne
  have h3 := hs.four_le_V₁ hII hq
  omega

theorem cent_Q₂_le_W₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {x : G} (hxQ : x ∈ Qof S K₂) (hc : ∀ a ∈ Vof S K₁ W₂, x * a = a * x) : x ∈ W₂ :=
  (hs.gq_Q₂ hII).mem_of_commute hs.W₂_le_Q₂ hs.W₂_max.2.1 (hs.relIndex_W₂ hII)
    (inf_le_left : Vof S K₁ W₂ ≤ W₂) (hs.four_le_V₁ hII hq) hxQ hc

theorem V₁V_comm (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ c ∈ Vof S K₁ W₂, ∀ v ∈ conjugate (Vof S K₁ W₂) h, c * v = v * c :=
  hs.comm_V hII hq hrec (K := K₁) (X := Vof S K₁ W₂) (Or.inl rfl) inf_le_right (hs.V₁_le_W hII hq)
    (hs.V₁_normal hII)

theorem cyc_V₁_comm (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ a ∈ Vof S K₁ W₂, ∀ b ∈ Vof S K₁ W₂, a * b = b * a :=
  Basic.cyclic_comm hs.V₁_cyclic

theorem cyc_V_comm (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ a ∈ conjugate (Vof S K₁ W₂) h, ∀ b ∈ conjugate (Vof S K₁ W₂) h, a * b = b * a :=
  Basic.cyclic_comm hs.V₁h_cyclic

theorem A_comm (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ a ∈ Aof S K₁ W₂ h, ∀ b ∈ Aof S K₁ W₂ h, a * b = b * a :=
  Basic.comm_sup_of_comm hs.cyc_V₁_comm hs.cyc_V_comm (hs.V₁V_comm hII hq hrec)

theorem A_le_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : Aof S K₁ W₂ h ≤ S1 S K₁ :=
  sup_le (((inf_le_right : Vof S K₁ W₂ ≤ Pof S K₁)).trans (hs.P_le_S1 hII (Or.inl rfl)))
    (hs.V₁h_le_S1 hII hq hrec)

theorem A_le_S (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : Aof S K₁ W₂ h ≤ S :=
  (hs.A_le_S1 hII hq hrec).trans S1_le_S

theorem exists_k (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∃ k : ℕ, 2 ≤ k ∧ Nat.card ↥(Vof S K₁ W₂) = 2 ^ k := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (hs.V₁_pgroup hII)
  refine ⟨m, ?_, hm⟩
  have h4 := hs.four_le_V₁ hII hq
  by_contra hcon
  have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem W₂_card (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Nat.card ↥W₂ = e * 2 ^ k := by
  obtain ⟨e, he, -, -, -, hq2⟩ := hs.lemma82_core hII hq hrec
  refine ⟨e, he, ?_⟩
  have h1 := hs.card_W₂ hII
  have h2 := hs.card_V₁ hII hq
  have hP₁ : Nat.card ↥(Pof S K₁) = 2 * 2 ^ k := by rw [← h2, hk]
  have h3 : 2 * Nat.card ↥W₂ = 2 * (e * 2 ^ k) := by
    rw [h1, hq2, hP₁]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

theorem W₂_pow (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ w ∈ W₂, w ^ (2 ^ (k + 1)) = 1 := by
  intro w hw
  obtain ⟨e, he, hW⟩ := hs.W₂_card hII hq hrec hk
  have h1 := Basic.pow_card_of_mem hw
  have hdvd : Nat.card ↥W₂ ∣ 2 ^ (k + 1) := by
    rw [hW]
    rcases he with rfl | rfl
    · rw [one_mul]; exact pow_dvd_pow 2 (Nat.le_succ k)
    · exact ⟨1, by ring⟩
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one h1).trans hdvd)

theorem W₂_sq_mem (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ w ∈ W₂, w * w ∈ Vof S K₁ W₂ := by
  intro w hw
  refine Basic.mem_of_pow_card_eq_one (V := Vof S K₁ W₂) hs.W₂_max.2.1 inf_le_left (mul_mem hw hw) ?_
  rw [hk, ← pow_two, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
  exact hs.W₂_pow hII hq hrec hk w hw

theorem z_mem_V₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {k : ℕ} (hk2 : 2 ≤ k) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) : z ∈ Vof S K₁ W₂ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨x, hxV, hx2, hx1⟩ := Basic.exists_involution_of_cyclic hs.V₁_cyclic hk
  have hxP : x ∈ Pof S K₁ := hxV.2
  rcases (hs.gq_P hII hq (Or.inl rfl)).uniq x hxP hx2 with h' | h'
  · exact absurd h' hx1
  · rw [← h']; exact hxV

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
