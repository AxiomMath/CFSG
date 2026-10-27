module

public import CFSG.LargeExtraspecial.S111TFail
public import CFSG.LargeExtraspecial.S111TEightB
public import CFSG.LargeExtraspecial.S111AExists

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k k' : G}

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem isTIModEF_of_oddCore_eq_bot (hE : Ebar S k k' ≠ ⊥)
    (hO : CFSG.oddCore ↥(Ybar111 S k k') = ⊥) : IsTIModEF S k k' := by
  intro x hx
  have hNx : (Ebar S k k' ⊔ Ebar S k' k).map (MulAut.conj x).toMonoidHom =
      Ebar S k k' ⊔ Ebar S k' k :=
    map_conj_eq_of_mem_normalizer (P.le_normalizer_EF hx)
  by_cases hLx : (S.Lbar k).map (MulAut.conj x).toMonoidHom = S.Lbar k
  · left
    rw [Subgroup.map_sup, hLx, hNx]
  right
  intro y hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
  by_contra hyN
  obtain ⟨l, hl, n, hn, rfl⟩ := exists_mul_of_mem_sup P.Lbar_le_normalizer_EF hy2
  have hlE : l ∉ Ebar S k k' := fun hlE => hyN (mul_mem (mem_sup_left hlE) hn)
  have hlx : l ∈ (S.Lbar k).map (MulAut.conj x).toMonoidHom ⊔ (Ebar S k k' ⊔ Ebar S k' k) := by
    rw [Subgroup.map_sup, hNx] at hy1
    have := mul_mem hy1 (mem_sup_right (inv_mem hn))
    rwa [mul_inv_cancel_right] at this
  obtain ⟨w, hwY, hLw⟩ := P.exists_mem_Ybar hE hx hLx hl hlE hlx
  apply hLw
  have Z := P.zHyp hE
  refine P.map_conj_eq_of_conj_mem (Subgroup.mem_inf.mp hwY).1 fun l₁ hl₁ l₂ hl₂ => ?_
  have hc := Z.comm_mem_of_oddCore_eq_bot hO hwY hl₁
  have hl₁₂ := Lbar_comm S P.memQ hl₁ hl₂
  have hc' : (w * l₁ * w⁻¹ * l₁⁻¹) * (l₂ * (w * l₁ * w⁻¹ * l₁⁻¹)⁻¹ * l₂⁻¹) ∈
      Ebar S k k' ⊔ Ebar S k' k :=
    mul_mem hc (P.conj_mem_EF (mem_sup_left hl₂) (inv_mem hc))
  have e : w * l₁ * w⁻¹ * l₂ * (w * l₁ * w⁻¹)⁻¹ =
      (w * l₁ * w⁻¹ * l₁⁻¹) * (l₂ * (w * l₁ * w⁻¹ * l₁⁻¹)⁻¹ * l₂⁻¹) * l₂ := by
    calc w * l₁ * w⁻¹ * l₂ * (w * l₁ * w⁻¹)⁻¹ =
        (w * l₁ * w⁻¹ * l₁⁻¹) * (l₁ * l₂) * l₁⁻¹ * (w * l₁ * w⁻¹ * l₁⁻¹)⁻¹ := by group
      _ = (w * l₁ * w⁻¹ * l₁⁻¹) * (l₂ * l₁) * l₁⁻¹ * (w * l₁ * w⁻¹ * l₁⁻¹)⁻¹ := by rw [hl₁₂]
      _ = _ := by group
  rw [e]
  exact mul_mem (mem_sup_right hc') (mem_sup_left hl₂)

end Pair111

theorem Cfg111.card_eq_eight_or (C : Cfg111 S g A) : Nat.card A = 8 ∨ 16 ≤ Nat.card A := by
  have h8 := C.eight_le_card
  have hc := C.inc.card_eq
  rw [S.card_submodule] at hc
  rw [hc] at h8 ⊢
  set d := finrank (ZMod 2) (S.clSub A)
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d <;> simp_all
  · right
    calc 16 = 2 * 2 ^ 3 := by norm_num
      _ ≤ 2 * 2 ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hd)

theorem Cfg111.ord3_of_mem (C : Cfg111 S g A) (h6 : 6 ≤ S.width) (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) {F : Subgroup S.O} (hFM : F ≤ S.Mbar)
    (hodd : Odd (Nat.card F)) (hnorm : ∀ s ∈ S.Lbar k, ∀ x ∈ F, s * x * s⁻¹ ∈ F) {m : S.M}
    (hmF : S.ρ m ∈ F) (hm1 : S.ρ m ≠ 1) : Ord3 S k m := by
  have hkQ := C.inc.le_QG hk
  have hy : Hyp S k := C.hy.of_conj hkQ hkz
  have hF : F ≠ ⊥ := fun h0 => hm1 (by rw [h0] at hmF; exact (Subgroup.mem_bot).mp hmF)
  have h3 : Nat.card F = 3 := S5.timmesfeld_5_4 hy.hyp4 hy.noA2' hy.cons
    (by omega) hFM hodd hF hnorm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm := (S5.timmesfeld_5_3 hy.hyp4 hy.noA2' hy.cons hFM (isCyclic_of_prime_card h3)
    hodd hF hnorm).2
  have hdich : ∀ s ∈ S.Lbar k, s * S.ρ m * s⁻¹ = S.ρ m ∨ s * S.ρ m * s⁻¹ = (S.ρ m)⁻¹ :=
    fun s hs => S5.conj_eq_self_or_inv_of_card_eq_three hy.hyp4 h3 hnorm hmF hs
  have hw3 : S.ρ m ^ 3 = 1 := by
    have := pow_card_eq_one' (G := F) (x := ⟨S.ρ m, hmF⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have hord : orderOf (S.ρ m) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hw3) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hm1
    · exact h1
  have hzF : zpowers (S.ρ m) = F := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmF)
    (by rw [Nat.card_zpowers, hord, h3])
  refine ⟨hw3, hm1, hdich, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hcomm
  rw [commutator_eq_bot_iff_le_centralizer, ← hzF, zpowers_le, mem_centralizer_iff]
  intro s hs
  have e := (hdich s hs).resolve_right (hcon s hs)
  calc s * S.ρ m = s * S.ρ m * s⁻¹ * s := by group
    _ = S.ρ m * s := by rw [e]

theorem Pair111.oddCore_eq_bot (P : Pair111 S g A h k k') (h6 : 6 ≤ S.width)
    (hE : Ebar S k k' ≠ ⊥) : CFSG.oddCore ↥(Ybar111 S k k') = ⊥ := by
  have Z := P.zHyp hE
  set F := (CFSG.oddCore ↥(Ybar111 S k k')).map (Ybar111 S k k').subtype with hFdef
  have hFM : F ≤ S.Mbar :=
    (map_subtype_le _).trans (inf_le_left.trans (Lbar_sup_le_Mbar S k k'))
  have hodd : Odd (Nat.card F) := by
    rw [hFdef, Subgroup.card_map_of_injective (Ybar111 S k k').subtype_injective]
    exact odd_card_oddCore_of_finite _
  have hnorm : ∀ s ∈ S.Lbar k ⊔ S.Lbar k', ∀ x ∈ F, s * x * s⁻¹ ∈ F := fun s hs x hx =>
    conj_mem_oddCore (fun y hy => Z.conj_mem_cen hs hy) (fun y hy => by
      have := Z.conj_mem_cen (inv_mem hs) hy
      rwa [inv_inv] at this) hx
  rw [← Subgroup.map_eq_bot_iff_of_injective _ (Ybar111 S k k').subtype_injective]
  by_contra hF
  rcases P.cfg.card_eq_eight_or with h8 | h16
  · obtain ⟨⟨w, hwF⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
    have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (hFM hwF)
    have W := P.cfg.ord3_of_mem h6 P.mem P.ne hFM hodd (fun s hs => hnorm s (mem_sup_left hs))
      hwF hw1'
    have W' := P.swap.cfg.ord3_of_mem h6 P.mem' P.ne' hFM hodd
      (fun s hs => hnorm s (mem_sup_right hs)) hwF hw1'
    have hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n := by
      obtain ⟨y, -, hy⟩ := hwF
      intro n hn
      have hyc := mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).2 n hn
      rw [← hy]
      exact hyc
    exact P.false_of_ord3 h6 W W' hc h8 hE
  · exact hF (P.cfg.eq_bot_of_odd h6 P.mem P.ne h16 hFM hodd
      (fun s hs x hx => hnorm s (mem_sup_left hs) x hx))

theorem Pair111.isTIModEF (P : Pair111 S g A h k k') (h6 : 6 ≤ S.width)
    (hE : Ebar S k k' ≠ ⊥) : IsTIModEF S k k' :=
  P.isTIModEF_of_oddCore_eq_bot hE (P.oddCore_eq_bot h6 hE)

theorem tiClaim111 : TIClaim111 := by
  intro G _ _ _ S g A C h6 h hh hA k k' hk hkz hk' hk'z hE _
  exact (⟨C, hh, hA, hk, hkz, hk', hk'z⟩ : Pair111 S g A h k k').isTIModEF h6 hE

end CFSG.LargeExtraspecial.S11
