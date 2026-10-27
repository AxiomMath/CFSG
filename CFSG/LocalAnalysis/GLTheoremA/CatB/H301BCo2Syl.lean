module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Syl

open scoped Pointwise

private theorem isPGroup_zpowers_three {G : Type*} [Group G] {a : G} (ha : a ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers a) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ha)

private theorem exists_commute_conj {G : Type*} [Group G] [Finite G] (h25 : ¬ 25 ∣ Nat.card G)
    {x0 x y : G} (hx0 : orderOf x0 = 5) (hx5 : orderOf x = 5) (hxy : Commute x y) :
    ∃ g : G, Commute x0 (g * y * g⁻¹) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h1 : 5 ^ 1 ∣ Nat.card G := by
    rw [pow_one, ← hx0]
    exact orderOf_dvd_natCard x0
  have h2 : ¬ 5 ^ 2 ∣ Nat.card G := h25
  rw [Nat.prime_five.pow_dvd_iff_le_factorization hn] at h1 h2
  have hf : (Nat.card G).factorization 5 = 1 := by omega
  let P0 : Sylow 5 G :=
    Sylow.ofCard (Subgroup.zpowers x0) (by rw [Nat.card_zpowers, hx0, hf, pow_one])
  let P : Sylow 5 G :=
    Sylow.ofCard (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx5, hf, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P0
  have hgP : MulAut.conj g • Subgroup.zpowers x = Subgroup.zpowers x0 :=
    congrArg (fun S : Sylow 5 G => (S : Subgroup G)) hg
  have hmem : (MulAut.conj g)⁻¹ • x0 ∈ Subgroup.zpowers x := by
    rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hgP]
    exact Subgroup.mem_zpowers x0
  rw [MulAut.smul_def, MulAut.conj_inv_apply] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hc : Commute (g⁻¹ * x0 * g) y := hk ▸ hxy.zpow_left k
  refine ⟨g, ?_⟩
  show x0 * (g * y * g⁻¹) = g * y * g⁻¹ * x0
  calc x0 * (g * y * g⁻¹) = g * (g⁻¹ * x0 * g * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * x0 * g)) * g⁻¹ := by rw [hc.eq]
    _ = g * y * g⁻¹ * x0 := by group

private theorem exists_conj_pow {G H : Type*} [Group G] [Finite G] [Group H] (φ : G →* H)
    (hN : IsPGroup 2 φ.ker) {d y : G} (hd3 : d ^ 3 = 1) (hy3 : y ^ 3 = 1) {e : ℕ}
    (he : φ y = φ d ^ e) : ∃ c : G, c * y * c⁻¹ = d ^ e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := (Subgroup.zpowers (φ d)).comap φ
  have hyK : y ∈ K := Subgroup.mem_comap.2 (by
    rw [he]
    exact pow_mem (Subgroup.mem_zpowers _) e)
  have hdK : d ∈ K := Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)
  obtain ⟨P, hP⟩ :=
    (isPGroup_zpowers_three (a := (⟨y, hyK⟩ : K)) (Subtype.ext hy3)).exists_le_sylow
  obtain ⟨Q, hQ⟩ :=
    (isPGroup_zpowers_three (a := (⟨d, hdK⟩ : K)) (Subtype.ext hd3)).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq K P Q
  have hhP : MulAut.conj h • (P : Subgroup K) = Q :=
    congrArg (fun S : Sylow 3 K => (S : Subgroup K)) hh
  have h1 : (h : G) * y * (h : G)⁻¹ ∈ (Q : Subgroup K).map K.subtype := by
    refine ⟨h * ⟨y, hyK⟩ * h⁻¹, ?_, rfl⟩
    rw [← hhP]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj h) _ (hP (Subgroup.mem_zpowers _))
  have h2 : d ^ e ∈ (Q : Subgroup K).map K.subtype :=
    ⟨⟨d, hdK⟩ ^ e, pow_mem (hQ (Subgroup.mem_zpowers _)) e, rfl⟩
  have hφh : φ ((h : G) * y * (h : G)⁻¹) = φ d ^ e := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 h.2)
    rw [map_mul, map_mul, map_inv, ← hk, he,
      (((Commute.refl (φ d)).zpow_left k).pow_right e).eq, mul_inv_cancel_right]
  have hdisj : Disjoint ((Q : Subgroup K).map K.subtype) φ.ker :=
    IsPGroup.disjoint_of_coprime (Q.isPGroup'.map K.subtype) hN (by decide)
  have hz : ((h : G) * y * (h : G)⁻¹)⁻¹ * d ^ e = 1 := by
    refine Subgroup.disjoint_def.1 hdisj (mul_mem (inv_mem h1) h2) ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφh, map_pow, inv_mul_cancel]
  exact ⟨h, inv_mul_eq_one.1 hz⟩

theorem exists_conj_five_three {G H : Type*} [Group G] [Finite G] [Group H] (φ : G →* H)
    (hN : IsPGroup 2 φ.ker) (h25 : ¬ 25 ∣ Nat.card G) {x0 d : G} (hx0 : orderOf x0 = 5)
    (hd3 : d ^ 3 = 1)
    (hsix : ∀ c : G, c ^ 3 = 1 → φ c ≠ 1 → Commute (φ c) (φ x0) → φ c = φ d ∨ φ c = φ d ^ 2)
    {y x : G} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hx5 : orderOf x = 5) (hxy : Commute x y) :
    ∃ c : G, c * y * c⁻¹ = d ∨ c * y * c⁻¹ = d ^ 2 := by
  obtain ⟨g, hg⟩ := exists_commute_conj h25 hx0 hx5 hxy
  have hy13 : (g * y * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hφ : φ (g * y * g⁻¹) ≠ 1 := fun h => hy1 (conj_eq_one_iff.1
    (Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_coprime (isPGroup_zpowers_three hy13) hN
      (by decide)) (Subgroup.mem_zpowers _) (MonoidHom.mem_ker.2 h)))
  have hconj : ∀ c : G, c * (g * y * g⁻¹) * c⁻¹ = c * g * y * (c * g)⁻¹ := fun c => by group
  rcases hsix _ hy13 hφ (hg.map φ).symm with hc | hc
  · obtain ⟨c, hc'⟩ := exists_conj_pow φ hN hd3 hy13 (e := 1) (by rw [pow_one]; exact hc)
    exact ⟨c * g, Or.inl (by rw [← hconj, hc', pow_one])⟩
  · obtain ⟨c, hc'⟩ := exists_conj_pow φ hN hd3 hy13 (e := 2) hc
    exact ⟨c * g, Or.inr (by rw [← hconj, hc'])⟩

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Syl

end
