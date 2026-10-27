module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

section Gen

variable {Γ : Type*} [Group Γ]

theorem actFun_zpow (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) (n : ℤ) :
    actFun S (g ^ n) = actFun S g ^ n := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact actFun_pow S hg m
  | negSucc m =>
    rw [zpow_negSucc, zpow_negSucc, actFun_inv S (pow_mem hg _), actFun_pow S hg]

theorem imgIn_zpowers (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) :
    imgIn S (zpowers g) = zpowers (actFun S g) := by
  ext a
  rw [mem_imgIn_iff]
  constructor
  · rintro ⟨h, ⟨n, rfl⟩, hN, rfl⟩
    exact ⟨n, (actFun_zpow S hg n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨g ^ n, ⟨n, rfl⟩, zpow_mem hg n, actFun_zpow S hg n⟩

theorem isElemAbelian_imgIn_of_comm_sq {p : ℕ} (S : Subgroup Γ) {K : Subgroup Γ}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ centralizer (S : Set Γ))
    (hpow : ∀ a ∈ K, a ^ p ∈ centralizer (S : Set Γ)) : IsElemAbelian p (imgIn S K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨g, hgK, hgN, ha⟩ := (mem_imgIn_iff S K).1 a.2
    obtain ⟨h, hhK, hhN, hb⟩ := (mem_imgIn_iff S K).1 b.2
    apply Subtype.ext
    show (a : MulAut ↥S) * b = b * a
    rw [← ha, ← hb, ← actFun_mul S hgN hhN, ← actFun_mul S hhN hgN,
      actFun_eq_iff S (mul_mem hgN hhN) (mul_mem hhN hgN)]
    have := hcomm h⁻¹ (inv_mem hhK) g⁻¹ (inv_mem hgK)
    simpa [mul_assoc] using this
  · obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff S K).1 hx
    rw [← actFun_pow S hgN, (actFun_eq_one_iff S (pow_mem hgN p)).2 (hpow g hgK)]

theorem actFun_mem_normalizer_imgIn (S K : Subgroup Γ) {g : Γ} (hgS : g ∈ normalizer (S : Set Γ))
    (hgK : g ∈ normalizer (K : Set Γ)) :
    actFun S g ∈ normalizer ((imgIn S K : Subgroup (MulAut ↥S)) : Set (MulAut ↥S)) := by
  have h1 := imgIn_map_conj S K hgS
  have h2 : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.1 hgK
  rw [h2] at h1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h1.symm

theorem imgIn_le_stabilizer (S K : Subgroup Γ) (v : ↥S)
    (h : ∀ g ∈ K, g ∈ normalizer (S : Set Γ) → g * (v : Γ) = (v : Γ) * g) :
    imgIn S K ≤ MulAction.stabilizer (MulAut ↥S) v := by
  intro x hx
  obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff S K).1 hx
  exact (actFun_fixes_iff S hgN v).2 (h g hgK hgN)

theorem eq_one_or_of_mem_zpowers {t a : Γ} (ht : t * t = 1) (ha : a ∈ zpowers t) :
    a = 1 ∨ a = t := by
  obtain ⟨n, rfl⟩ := ha
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    show t ^ (2 * k) = 1
    rw [zpow_mul, h2, one_zpow]
  · right
    show t ^ (2 * k + 1) = t
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

end Gen

end CFSG.LocalAnalysis.EvenBN.Tits.N
