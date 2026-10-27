module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimS8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimTI

public section

namespace CFSG.QuasithinUnique.Claim2526

open Equiv CFSG.Open

section Exponent

variable {G : Type} [Group G]

theorem pow_four_centralizes {L : Subgroup G} {φ : ↥L ≃* alternatingGroup (Fin 8)} {t i : G}
    (D : S8Data L φ t i) {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G)) (hct : c * t = t * c)
    {m : ℕ} (hm : c ^ (2 ^ m) = 1) : ∀ k ∈ L, c ^ 4 * k = k * c ^ 4 := by
  have hcomm : thetaFun L φ c * Equiv.swap 0 1 = Equiv.swap 0 1 * thetaFun L φ c := by
    rw [← thetaFun_t D, ← thetaFun_mul hc D.t_mem, ← thetaFun_mul D.t_mem hc, hct]
  have hpow : (thetaFun L φ c) ^ (2 ^ m) = 1 := by
    rw [← thetaFun_pow hc, hm, thetaFun_one]
  have h4 : (thetaFun L φ c) ^ 4 = 1 := perm_pow_four_of_commute_swap (by decide) hcomm hpow
  have hc4 : c ^ 4 ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hc 4
  have h4' : thetaFun L φ (c ^ 4) = 1 := by rw [thetaFun_pow hc, h4]
  rw [thetaFun_of_mem hc4] at h4'
  exact (theta_eq_one_iff L φ ⟨c ^ 4, hc4⟩).mp h4'

theorem pow_four_eq_one {L : Subgroup G} {φ : ↥L ≃* alternatingGroup (Fin 8)} {t i : G}
    (D : S8Data L φ t i) {S SC SCx : Subgroup G} (hS2 : IsPGroup 2 S) (hSCx : SCx ≤ S)
    (hN : ∀ c ∈ SCx, c ∈ Subgroup.normalizer (L : Set G) ∧ c * t = t * c)
    (hSC : ∀ c ∈ S, (∀ k ∈ L, c * k = k * c) → c ∈ SC) (hcap : SC ⊓ SCx = ⊥) :
    ∀ c ∈ SCx, c ^ 4 = 1 := by
  intro c hc
  obtain ⟨hcN, hct⟩ := hN c hc
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hS2 ⟨c, hSCx hc⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hcent := pow_four_centralizes D hcN hct hm
  have hc4S : c ^ 4 ∈ S := S.pow_mem (hSCx hc) 4
  have hc4SC : c ^ 4 ∈ SC := hSC _ hc4S hcent
  have hc4X : c ^ 4 ∈ SCx := SCx.pow_mem hc 4
  have hmem : c ^ 4 ∈ SC ⊓ SCx := ⟨hc4SC, hc4X⟩
  rw [hcap, Subgroup.mem_bot] at hmem
  exact hmem

theorem pow_four_of_conj {SC : Subgroup G} {x : G} (h : ∀ c ∈ CFSG.conjugate SC x, c ^ 4 = 1) :
    ∀ s ∈ SC, s ^ 4 = 1 := by
  intro s hs
  have hmem : x⁻¹ * s * x ∈ CFSG.conjugate SC x := by
    rw [BenderBranch.mem_conjugate_iff]
    have : x * (x⁻¹ * s * x) * x⁻¹ = s := by group
    rw [this]
    exact hs
  have h1 := h _ hmem
  rw [conj_pow_inv] at h1
  calc s ^ 4 = x * (x⁻¹ * s ^ 4 * x) * x⁻¹ := by group
    _ = 1 := by rw [h1]; group

end Exponent

section Dihedral

variable {G : Type} [Group G] [Finite G]

theorem sc_dihedral_four {SC U : Subgroup G} (hSC2 : IsPGroup 2 SC) (hUSC : U ≤ SC)
    (hU4 : Nat.card U = 4) (hUexp : ∀ u ∈ U, u ^ 2 = 1)
    (hC : SC ⊓ Subgroup.centralizer (U : Set G) ≤ U) (hne : U ≠ SC)
    (hexp : ∀ s ∈ SC, s ^ 4 = 1) : Nonempty (↥SC ≃* DihedralGroup 4) := by
  rcases suzuki_selfCentralizing_four hSC2 hUSC hU4 hUexp hC hne with
    ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hord : orderOf (e.symm (DihedralGroup.r 1)) = 2 ^ k := by
      rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have h4 : (e.symm (DihedralGroup.r 1)) ^ 4 = 1 :=
      Subtype.ext (by simpa using hexp _ (e.symm (DihedralGroup.r 1)).2)
    have hdvd : 2 ^ k ∣ 2 ^ 2 := by
      rw [← hord]
      simpa using orderOf_dvd_of_pow_eq_one h4
    have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    obtain rfl : k = 2 := by omega
    exact ⟨e⟩
  · exfalso
    have hord : orderOf (e.symm (CFSG.Semidihedral.r n)) = 2 ^ (n - 1) := by
      rw [MulEquiv.orderOf_eq]
      exact CFSG.Semidihedral.orderOf_r n (by omega)
    have h4 : (e.symm (CFSG.Semidihedral.r n)) ^ 4 = 1 :=
      Subtype.ext (by simpa using hexp _ (e.symm (CFSG.Semidihedral.r n)).2)
    have hdvd : 2 ^ (n - 1) ∣ 4 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one h4
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h8 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem d4_center : ∀ a : DihedralGroup 4, (∀ b : DihedralGroup 4, a * b = b * a) → a * a = 1 →
    a ≠ 1 → a = DihedralGroup.r 2 := by
  decide

theorem d4_cent : ∀ b : DihedralGroup 4, b * DihedralGroup.r 1 = DihedralGroup.r 1 * b →
    b = 1 ∨ b = DihedralGroup.r 1 ∨ b = DihedralGroup.r 1 ^ 2 ∨ b = DihedralGroup.r 1 ^ 3 := by
  decide

theorem d4_sqrt : ∀ b : DihedralGroup 4, b * b = DihedralGroup.r 2 →
    b = DihedralGroup.r 1 ∨ b = DihedralGroup.r 1 ^ 3 := by
  decide

theorem d4_r1_sq : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 = DihedralGroup.r 2 := by decide

theorem d4_r1_four : (DihedralGroup.r 1 : DihedralGroup 4) ^ 4 = 1 := by decide

omit [Finite G] in
theorem exists_V {SC : Subgroup G} (e : ↥SC ≃* DihedralGroup 4) {t : G} (htSC : t ∈ SC) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (htc : ∀ s ∈ SC, t * s = s * t) :
    ∃ v ∈ SC, v ^ 2 = t ∧ v ^ 4 = 1 ∧
      (∀ s ∈ SC, (∀ y ∈ Subgroup.zpowers v, s * y = y * s) → s ∈ Subgroup.zpowers v) ∧
      (∀ x ∈ SC, x ^ 2 = t → x ∈ Subgroup.zpowers v) := by
  set tt : ↥SC := ⟨t, htSC⟩ with htt
  have hcent : ∀ b : DihedralGroup 4, e tt * b = b * e tt := by
    intro b
    obtain ⟨s, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (htc s s.2))
  have hsq : e tt * e tt = 1 := by
    have : tt * tt = 1 := Subtype.ext (by simpa [sq] using ht2)
    rw [← map_mul, this, map_one]
  have hne : e tt ≠ 1 := by
    intro h
    apply ht1
    exact congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
  have ha : e tt = DihedralGroup.r 2 := d4_center _ hcent hsq hne
  set v₀ : ↥SC := e.symm (DihedralGroup.r 1) with hv₀
  have hev : e v₀ = DihedralGroup.r 1 := by rw [hv₀, MulEquiv.apply_symm_apply]
  have hv2 : v₀ ^ 2 = tt := by
    apply e.injective
    rw [map_pow, hev, d4_r1_sq, ha]
  have hv4 : v₀ ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, hev, d4_r1_four, map_one]
  have hzp : ∀ n : ℕ, ((v₀ ^ n : ↥SC) : G) ∈ Subgroup.zpowers (v₀ : G) := fun n => by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n
  have hpow : ∀ b : ↥SC, (e b = 1 ∨ e b = DihedralGroup.r 1 ∨ e b = DihedralGroup.r 1 ^ 2 ∨
      e b = DihedralGroup.r 1 ^ 3) → (b : G) ∈ Subgroup.zpowers (v₀ : G) := by
    intro b hb
    have hb' : b = 1 ∨ b = v₀ ∨ b = v₀ ^ 2 ∨ b = v₀ ^ 3 := by
      rcases hb with h | h | h | h
      · left; exact e.injective (h.trans (map_one e).symm)
      · right; left; exact e.injective (h.trans hev.symm)
      · right; right; left
        apply e.injective
        rw [map_pow, hev]
        exact h
      · right; right; right
        apply e.injective
        rw [map_pow, hev]
        exact h
    rcases hb' with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact hzp 2
    · rw [h]; exact hzp 3
  refine ⟨v₀, v₀.2, congrArg Subtype.val hv2, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hv4
    simpa using this
  · intro s hs hcomm
    have hv : (s : G) * (v₀ : G) = (v₀ : G) * s := hcomm _ (Subgroup.mem_zpowers _)
    have h1 : (⟨s, hs⟩ : ↥SC) * v₀ = v₀ * ⟨s, hs⟩ := Subtype.ext hv
    have h2 := congrArg e h1
    rw [map_mul, map_mul, hev] at h2
    exact hpow ⟨s, hs⟩ (d4_cent _ h2)
  · intro x hx hx2
    have h1 : (⟨x, hx⟩ : ↥SC) * ⟨x, hx⟩ = tt := Subtype.ext (by simpa [sq] using hx2)
    have h2 := congrArg e h1
    rw [map_mul, ha] at h2
    rcases d4_sqrt _ h2 with h | h
    · exact hpow ⟨x, hx⟩ (Or.inr (Or.inl h))
    · exact hpow ⟨x, hx⟩ (Or.inr (Or.inr (Or.inr h)))

end Dihedral

end CFSG.QuasithinUnique.Claim2526
