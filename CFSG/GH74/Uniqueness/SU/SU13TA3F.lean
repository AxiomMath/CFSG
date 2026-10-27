module

public import CFSG.GH74.Uniqueness.SU.SU13TA3Cfg
public import CFSG.GH74.Uniqueness.SU.SU13TA3PermS
public import CFSG.GH74.Uniqueness.SU.SU13TA2Cent

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 10)}

@[expose] def Fh (π : H →* alternatingGroup (Fin 10)) : Subgroup H := AS.comap π

theorem mem_Fh {x : H} : x ∈ Fh π ↔ π x ∈ AS := Iff.rfl

theorem ker_le_Fh : π.ker ≤ Fh π := fun k hk => by
  rw [mem_Fh, (MonoidHom.mem_ker.mp hk)]
  exact AS.one_mem

theorem card_Fh (hπ : TwoCover π) : Nat.card (Fh π) = 5040 := by
  rw [Fh, hπ.card_comap, card_AS]

theorem odd_orderOf_s₁ (c : Cfg π) : Odd (orderOf c.s₁) := by
  have hne : c.s₁ ≠ 1 := fun h => by
    have := c.π_s₁
    rw [h, map_one] at this
    exact ec_ne_one this.symm
  have := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₁_pow hne
  rw [this]
  decide

theorem commute_s₁_of_mem_Fh (hπ : TwoCover π) (c : Cfg π) {f : H} (hf : f ∈ Fh π) :
    Commute f c.s₁ :=
  hπ.commute_of_pow_three c.s₁_pow (by rw [c.π_s₁]; exact commute_ec_of_mem_AS hf)

theorem disjoint_zpowers_s₁_Fh (hπ : TwoCover π) (c : Cfg π) : Disjoint (zpowers c.s₁) (Fh π) := by
  rw [Subgroup.disjoint_def]
  intro x hx hxF
  have hπx : π x ∈ zpowers ec := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨k, by rw [map_zpow, c.π_s₁]⟩
  have h1 : π x = 1 := by
    exact Subgroup.disjoint_def.mp disjoint_zpowers_ec_AS hπx hxF
  have hxk : x ∈ π.ker := h1
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.s₁_pow, one_zpow]
  have h2 := hπ.sq_eq_one_of_mem_ker' hxk
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [hx3, h2, inv_one, one_mul]

theorem centralizer_s₁_eq (hπ : TwoCover π) (c : Cfg π) :
    centralizer ({c.s₁} : Set H) = zpowers c.s₁ ⊔ Fh π := by
  have := hπ.finite'
  have hle : zpowers c.s₁ ⊔ Fh π ≤ centralizer ({c.s₁} : Set H) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_s₁_of_mem_Fh hπ c hf).eq
  have hcomm : ∀ x ∈ zpowers c.s₁, ∀ y ∈ Fh π, Commute x y := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((commute_s₁_of_mem_Fh hπ c hy).symm).zpow_left k
  have hcardsup : Nat.card ↥(zpowers c.s₁ ⊔ Fh π) = 15120 := by
    rw [card_sup_of_commute hcomm (disjoint_zpowers_s₁_Fh hπ c), Nat.card_zpowers,
      card_Fh hπ, (orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₁_pow (fun h => by
        have := c.π_s₁
        rw [h, map_one] at this
        exact ec_ne_one this.symm))]
  have hcardC : Nat.card ↥(centralizer ({c.s₁} : Set H)) = 15120 := by
    rw [hπ.card_centralizer_singleton (odd_orderOf_s₁ c), c.π_s₁, card_centralizer_ec]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardsup, hcardC])).symm

theorem ker_le_of_normal_Fh (hπ : TwoCover π) {N : Subgroup H} (hN : N ≤ Fh π)
    (hnorm : ∀ f ∈ Fh π, ∀ n ∈ N, f * n * f⁻¹ ∈ N) (hne : N ≠ ⊥) : π.ker ≤ N := by
  have := hπ.finite'
  have := isSimpleGroup_AS
  set M : Subgroup (alternatingGroup (Fin 10)) := N.map π with hM
  have hnormM : (M.subgroupOf AS).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨n, hn, hnm⟩ := hm
    obtain ⟨f, hf⟩ := hπ.surj (g : alternatingGroup (Fin 10))
    have hfF : f ∈ Fh π := by rw [mem_Fh, hf]; exact g.2
    refine ⟨f * n * f⁻¹, hnorm f hfF n hn, ?_⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, hnm, hf]
  have := hnormM
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf AS) with h | h
  ·
    have hNk : N ≤ π.ker := by
      intro n hn
      have hmem : (⟨π n, hN hn⟩ : AS) ∈ M.subgroupOf AS := ⟨n, hn, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    have hcard : Nat.card π.ker ≤ Nat.card N := by
      rw [hπ.card_ker]
      have := (Subgroup.one_lt_card_iff_ne_bot N).mpr hne
      omega
    exact (Subgroup.eq_of_le_of_card_ge hNk hcard).symm.le
  ·
    have hmem : (⟨sig0, sig0_mem_AS⟩ : AS) ∈ M.subgroupOf AS := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨x, hxN, hx⟩ := hmem
    obtain ⟨hxk, hx1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by norm_num) (x := x)
      (by rw [show π x = sig0 from hx]; exact cycleType_sig0)
    intro k hk
    by_cases hk1 : k = 1
    · rw [hk1]; exact N.one_mem
    · rw [hπ.eq_of_mem_ker_ne_one' hk hxk hk1 hx1]
      exact N.pow_mem hxN 2

theorem Fh_noOdd (hπ : TwoCover π) {N : Subgroup H} (hN : N ≤ Fh π)
    (hnorm : ∀ f ∈ Fh π, ∀ n ∈ N, f * n * f⁻¹ ∈ N) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_contra hne
  have hk := ker_le_of_normal_Fh hπ hN hnorm hne
  have h2 : Nat.card π.ker ∣ Nat.card N := Subgroup.card_dvd_of_le hk
  rw [hπ.card_ker] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
