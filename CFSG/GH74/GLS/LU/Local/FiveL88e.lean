module

public import CFSG.GH74.GLS.LU.Local.FiveL88d

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L88e

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.isConj_of_invol (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {i : G} (hi : orderOf i = 2) :
    IsConj z i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(zpowers i) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hi]; norm_num)
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hmem : g * i * g⁻¹ ∈ (S : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul i (MulAut.conj g) (P : Subgroup G)
      (hP' (mem_zpowers i))
    simpa using this
  have hord : orderOf (g * i * g⁻¹) = 2 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective i
    have e : (MulAut.conj g).toMonoidHom i = g * i * g⁻¹ := by simp
    rw [e] at h
    rw [h, hi]
  have h1 := c.ctx.extra.fusion _ hmem hord
  exact h1.trans (isConj_iff.mpr ⟨g, rfl⟩).symm

theorem Cfg8.C_E (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    centralizer ((EE v t w₁ X₁ : Subgroup G) : Set G) = EE v t w₁ X₁ := by
  set E := EE v t w₁ X₁ with hE
  have hCN : centralizer (E : Set G) ≤ normalizer (E : Set G) :=
    le_normalizer_of_commute (fun a ha b hb => ((Subgroup.mem_centralizer_iff.mp ha) b hb).symm)
  have hnormC : ∀ n ∈ normalizer (E : Set G), ∀ y ∈ centralizer (E : Set G),
      n * y * n⁻¹ ∈ centralizer (E : Set G) := by
    intro n hn y hy
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : n⁻¹ * e * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) e).mp he
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp hy) _ he'
    calc e * (n * y * n⁻¹) = n * ((n⁻¹ * e * n) * y) * n⁻¹ := by group
      _ = n * (y * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
      _ = (n * y * n⁻¹) * e := by group
  have hnorm : ((centralizer (E : Set G)).subgroupOf (normalizer (E : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCN]
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hnormC n hn y
    · intro hy
      have h2 := hnormC n⁻¹ (inv_mem hn) _ hy
      have e : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
      rwa [e] at h2
  have hodd : Odd (Nat.card ↥(centralizer (E : Set G))) := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥(centralizer (E : Set G)) := by
      rcases Nat.even_or_odd (Nat.card ↥(centralizer (E : Set G))) with h | h
      · exact even_iff_two_dvd.mp h
      · exact absurd h hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hi : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (c.isConj_of_invol hi)
    have hle : cjL g⁻¹ E ≤ centralizer ({z} : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      have hex : e * (x : G) = (x : G) * e := (Subgroup.mem_centralizer_iff.mp x.2) e he
      have hg' : (MulAut.conj g⁻¹).toMonoidHom e = g⁻¹ * e * g := by simp
      rw [hg']
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [← hg] at hex
      calc g⁻¹ * e * g * z = g⁻¹ * (e * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * e) * g := by rw [hex]
        _ = z * (g⁻¹ * e * g) := by group
    have hcard : Nat.card ↥(cjL g⁻¹ E) = 125 := by rw [card_cjL, c.E_card c.b86]; norm_num
    have h3 := Subgroup.card_dvd_of_le hle
    rw [hcard, c.b82.card_C] at h3
    norm_num at h3
  have hle := le_QQ_of_normal hCN hnorm hodd
  rw [c.QQ_eq] at hle
  exact le_antisymm hle
    (fun e he => Subgroup.mem_centralizer_iff.mpr (fun h hh => c.E_comm c.b86 h hh e he))

theorem Cfg2.card_K1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥K₁ = 120 := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcardq : Nat.card (ZMod 5) = p ^ f := by rw [c.ctx.pf, Nat.card_zmod]
  obtain ⟨e⟩ := exists_mulEquiv_SL2 c.hc.sl₁ (ZMod 5) hcardq
  exact sl2_five_card e

theorem Cfg2.card_HK1_le (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    Nat.card ↥(H ⊔ K₁ : Subgroup G) ≤ 480 := by
  have hHK : H ≤ normalizer (K₁ : Set G) := fun h hh =>
    mem_normalizer_of_cjL_eq (c.b66.H_normK h hh).1
  have h := card_sup_mul_card_inf' hHK
  rw [c.H_card, c.card_K1] at h
  have h4 : 4 ≤ Nat.card ↥(H ⊓ K₁ : Subgroup G) := by
    rw [← c.card_CK1u]
    apply Subgroup.card_le_of_le
    intro x hx
    exact ⟨c.K1_inf_cent_le_H hx, hx.1⟩
  have h5 : Nat.card ↥(H ⊔ K₁ : Subgroup G) * 4 ≤ Nat.card ↥(H ⊔ K₁ : Subgroup G) *
      Nat.card ↥(H ⊓ K₁ : Subgroup G) := Nat.mul_le_mul_left _ h4
  omega

theorem Cfg3.card_NX2_le (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    Nat.card ↥(normalizer ((XB t X₁ : Subgroup G) : Set G)) ≤ 1500000 := by
  have hN : normalizer ((XB t X₁ : Subgroup G) : Set G) = (H ⊔ K₁) ⊔ RR t X₁ := by
    rw [c.N_X2_eq]; ac_rfl
  have hnormR : (H ⊔ K₁) ≤ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
    sup_le (c.H_le_normalizer_X2.trans (normalizer_le_normalizer_RR t X₁)) c.K1_le_normalizer_RR
  have h := card_sup_mul_card_inf' hnormR
  rw [c.R_card] at h
  have hpos := Nat.card_pos (α := ↥((H ⊔ K₁) ⊓ RR t X₁))
  have h1 : Nat.card ↥((H ⊔ K₁) ⊔ RR t X₁ : Subgroup G) ≤
      Nat.card ↥((H ⊔ K₁) ⊔ RR t X₁ : Subgroup G) * Nat.card ↥((H ⊔ K₁) ⊓ RR t X₁ : Subgroup G) :=
    Nat.le_mul_of_pos_right _ hpos
  have h2 := Nat.mul_le_mul_right (5 ^ 5) c.card_HK1_le
  rw [hN]
  omega

end L88e

end CFSG.GH74.GLS.LU.Local.Five
