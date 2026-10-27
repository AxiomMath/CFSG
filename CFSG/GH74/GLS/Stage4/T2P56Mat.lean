module

public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.LU.Local.SL2Pure
public import CFSG.GH74.Generic.S3.Rank5

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Center

variable {F : Type} [Field F]

theorem sl2s_center {c : SL2 F} (hc : ∀ g : SL2 F, g * c = c * g) :
    c = 1 ∨ c = specialLinearGroupEquivStatedSL 2 F (-1) := by
  set ε := specialLinearGroupEquivStatedSL 2 F with hε
  have hcen : ε.symm c ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply ε.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc (ε g)
  rcases CFSG.GH74.Generic.S3.sl2_center_eq hcen with h | h
  · left
    have := congrArg ε h
    simpa using this
  · right
    have := congrArg ε h
    simpa using this

end Center

section Torus

variable {F : Type} [Field F] [Finite F]

theorem sl2s_cent_torus (hF : L2Field F) (D : Subgroup (SL2 F)) (hDc : IsCyclic ↥D)
    (hD : Nat.card ↥D = Nat.card F - 1) :
    ∀ c : SL2 F, (∀ x ∈ D, c * x = x * c) → c ∈ D := by
  classical
  obtain ⟨w, hN, hwD, hw2c, hw21, hwinv⟩ := ivk_1_3abc F hF D hDc hD
  obtain ⟨hodd, h3⟩ := hF
  set ε := specialLinearGroupEquivStatedSL 2 F with hε
  have h2 : (2 : F) ≠ 0 := by
    refine Ring.two_ne_zero fun h => ?_
    have := Fintype.ofFinite F
    have h1 : Fintype.card F % 2 = 0 := FiniteField.even_card_of_char_two h
    rw [← Nat.card_eq_fintype_card] at h1
    have := Nat.odd_iff.mp hodd
    omega
  have hw2 : w ^ 2 = ε (-1) := by
    rcases sl2s_center (fun g => ((Subgroup.mem_center_iff.1 hw2c) g)) with h | h
    · exact absurd h hw21
    · exact h
  have hevenD : 2 ∣ Nat.card ↥D := by
    rw [hD]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hι⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 hevenD
  have hι2 : (ι : SL2 F) * ι = 1 := by
    have := pow_orderOf_eq_one ι
    rw [hι, pow_two] at this
    exact congrArg Subtype.val this
  have hι1 : (ι : SL2 F) ≠ 1 := by
    intro h
    have : ι = 1 := Subtype.ext h
    rw [this, orderOf_one] at hι
    omega
  have hιc : ∀ g : SL2 F, g * (ι : SL2 F) = (ι : SL2 F) * g := by
    intro g
    have hsq : ε.symm (ι : SL2 F) * ε.symm (ι : SL2 F) = 1 := by
      rw [← map_mul, hι2, map_one]
    have hcen := LU.Local.sl2_involution_central h2 hsq
    have := Subgroup.mem_center_iff.1 hcen (ε.symm g)
    apply ε.symm.injective
    rw [map_mul, map_mul]
    exact this
  have hιeq : (ι : SL2 F) = ε (-1) := by
    rcases sl2s_center hιc with h | h
    · exact absurd h hι1
    · exact h
  have hw2D : w ^ 2 ∈ D := by rw [hw2, ← hιeq]; exact ι.2
  have hwN : w ∈ Subgroup.normalizer (D : Set (SL2 F)) := by
    rw [hN]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwiN : w⁻¹ ∈ Subgroup.normalizer (D : Set (SL2 F)) := Subgroup.inv_mem _ hwN
  have hwinv' : ∀ x ∈ D, w⁻¹ * x * w = x⁻¹ := by
    intro x hx
    have hx' : w⁻¹ * x * w ∈ D := by
      have := (Subgroup.mem_normalizer_iff.1 hwiN x).1 hx
      simpa using this
    have h1 := hwinv _ hx'
    have h2 : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
    rw [h2] at h1
    have h3 : (w⁻¹ * x * w) = x⁻¹ := by
      have := congrArg (fun t => t⁻¹) h1
      simpa using this.symm
    exact h3
  have hpow : ∀ k : ℤ, w ^ k ∈ D ∨ ∃ x₀ ∈ D, w ^ k = x₀ * w := by
    intro k
    induction k using Int.induction_on with
    | zero => exact Or.inl (by simp)
    | succ k ih =>
      rcases ih with h | ⟨x₀, hx₀, h⟩
      · exact Or.inr ⟨w ^ (k : ℤ), h, by rw [zpow_add_one]⟩
      · left
        rw [zpow_add_one, h, mul_assoc, ← pow_two]
        exact D.mul_mem hx₀ hw2D
    | pred k ih =>
      rcases ih with h | ⟨x₀, hx₀, h⟩
      · right
        refine ⟨(-(k : ℤ) : ℤ) |> fun _ => w ^ (-(k : ℤ)) * (w ^ 2)⁻¹, D.mul_mem h (D.inv_mem hw2D), ?_⟩
        rw [zpow_sub_one]
        group
      · left
        rw [zpow_sub_one, h]
        simpa using hx₀
  have hform : ∀ x ∈ D ⊔ Subgroup.zpowers w, x ∈ D ∨ ∃ x₀ ∈ D, x = x₀ * w := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact Or.inl hy
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact hpow k
    | one => exact Or.inl D.one_mem
    | mul a b _ _ ha hb =>
      rcases ha with ha | ⟨x₀, hx₀, rfl⟩ <;> rcases hb with hb | ⟨x₁, hx₁, rfl⟩
      · exact Or.inl (D.mul_mem ha hb)
      · exact Or.inr ⟨a * x₁, D.mul_mem ha hx₁, by group⟩
      · refine Or.inr ⟨x₀ * b⁻¹, D.mul_mem hx₀ (D.inv_mem hb), ?_⟩
        have := hwinv b hb
        calc x₀ * w * b = x₀ * (w * b * w⁻¹) * w := by group
          _ = x₀ * b⁻¹ * w := by rw [this]
      · left
        have := hwinv x₁ hx₁
        have e : x₀ * w * (x₁ * w) = x₀ * x₁⁻¹ * w ^ 2 := by
          calc x₀ * w * (x₁ * w) = x₀ * (w * x₁ * w⁻¹) * (w ^ 2) := by group
            _ = x₀ * x₁⁻¹ * w ^ 2 := by rw [this]
        rw [e]
        exact D.mul_mem (D.mul_mem hx₀ (D.inv_mem hx₁)) hw2D
    | inv a _ ha =>
      rcases ha with ha | ⟨x₀, hx₀, rfl⟩
      · exact Or.inl (D.inv_mem ha)
      · refine Or.inr ⟨x₀ * (w ^ 2)⁻¹, D.mul_mem hx₀ (D.inv_mem hw2D), ?_⟩
        have h1 := hwinv' x₀⁻¹ (D.inv_mem hx₀)
        rw [inv_inv] at h1
        calc (x₀ * w)⁻¹ = (w⁻¹ * x₀⁻¹ * w) * w⁻¹ := by group
          _ = x₀ * w⁻¹ := by rw [h1]
          _ = x₀ * (w ^ 2)⁻¹ * w := by group
  intro c hc
  have hcN : c ∈ Subgroup.normalizer (D : Set (SL2 F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : c * h * c⁻¹ = h := by rw [hc h hh]; group
      rw [this]; exact hh
    · intro hh
      have h1 := hc _ hh
      have : h = c * h * c⁻¹ := by
        calc h = c⁻¹ * ((c * h * c⁻¹) * c) := by group
          _ = c⁻¹ * (c * (c * h * c⁻¹)) := by rw [← h1]
          _ = c * h * c⁻¹ := by group
      rw [this]; exact hh
  rw [hN] at hcN
  rcases hform c hcN with h | ⟨x₀, hx₀, rfl⟩
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := hDc.exists_generator
    have hgord : orderOf (g : SL2 F) = Nat.card ↥D := by
      rw [Subgroup.orderOf_coe]; exact orderOf_eq_card_of_forall_mem_zpowers hg
    have hg2 : (g : SL2 F) * g ≠ 1 := by
      intro h1
      have h2 : orderOf (g : SL2 F) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
      rw [hgord, hD] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hgD : (g : SL2 F) ∈ D := g.2
    have h1 := hc _ hgD
    have hcomm : ∀ a b : SL2 F, a ∈ D → b ∈ D → a * b = b * a := by
      intro a b ha hb
      have hC : IsMulCommutative ↥D := hDc.isMulCommutative
      exact congrArg Subtype.val (hC.is_comm.comm (⟨a, ha⟩ : ↥D) ⟨b, hb⟩)
    have h2 : x₀ * w * (g : SL2 F) * (x₀ * w)⁻¹ = (g : SL2 F)⁻¹ := by
      calc x₀ * w * (g : SL2 F) * (x₀ * w)⁻¹ = x₀ * (w * (g : SL2 F) * w⁻¹) * x₀⁻¹ := by group
        _ = x₀ * (g : SL2 F)⁻¹ * x₀⁻¹ := by rw [hwinv _ hgD]
        _ = (g : SL2 F)⁻¹ := by
            have := hcomm x₀ _ hx₀ (D.inv_mem hgD)
            calc x₀ * (g : SL2 F)⁻¹ * x₀⁻¹ = ((g : SL2 F)⁻¹ * x₀) * x₀⁻¹ := by rw [this]
              _ = (g : SL2 F)⁻¹ := by group
    have h3 : x₀ * w * (g : SL2 F) * (x₀ * w)⁻¹ = (g : SL2 F) := by rw [h1]; group
    rw [h3] at h2
    exact hg2 (mul_eq_one_iff_eq_inv.2 h2)

theorem sl2s_centralizer_le (hF : L2Field F) (D : Subgroup (SL2 F)) (hDc : IsCyclic ↥D)
    (hD : Nat.card ↥D = Nat.card F - 1) {y : SL2 F} (hy : y ∈ D) (hy2 : y * y ≠ 1) :
    ∀ d : SL2 F, d * y = y * d → d ∈ D := by
  intro d hd
  apply sl2s_cent_torus hF D hDc hD d
  intro x hx
  set ε := specialLinearGroupEquivStatedSL 2 F with hε
  have hxy : x * y = y * x := by
    have hC : IsMulCommutative ↥D := hDc.isMulCommutative
    exact congrArg Subtype.val (hC.is_comm.comm (⟨x, hx⟩ : ↥D) ⟨y, hy⟩)
  have hg : ε.symm y ∉ Subgroup.center SL(2, F) := by
    intro hc
    apply hy2
    rcases CFSG.GH74.Generic.S3.sl2_center_eq hc with h | h
    · have : y = 1 := by simpa using congrArg ε h
      rw [this]; group
    · have h' : y = ε (-1) := by simpa using congrArg ε h
      rw [h', ← map_mul]
      simp
  have ha : ε.symm d * ε.symm y = ε.symm y * ε.symm d := by rw [← map_mul, ← map_mul, hd]
  have hb : ε.symm x * ε.symm y = ε.symm y * ε.symm x := by rw [← map_mul, ← map_mul, hxy]
  have := LU.Local.sl2_commute_of_centralizer hg ha hb
  apply ε.symm.injective
  rw [map_mul, map_mul]
  exact this

theorem cent_le_torus {G : Type} [Group G] (hF : L2Field F) {K : Subgroup G} (e : ↥K ≃* SL2 F)
    {D : Subgroup G} (hDK : D ≤ K) (hDc : IsCyclic ↥D) (hD : Nat.card ↥D = Nat.card F - 1)
    {y : G} (hy : y ∈ D) (hy2 : y * y ≠ 1) : ∀ d ∈ K, d * y = y * d → d ∈ D := by
  set D' : Subgroup (SL2 F) := (D.subgroupOf K).map e.toMonoidHom with hD'
  have hDe : ↥(D.subgroupOf K) ≃* ↥D := (Subgroup.subgroupOfEquivOfLe hDK)
  have hD'e : ↥(D.subgroupOf K) ≃* ↥D' := Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  have hcyc : IsCyclic ↥D' := hD'e.symm.isCyclic.2 (hDe.isCyclic.2 hDc)
  have hcard : Nat.card ↥D' = Nat.card F - 1 := by
    rw [← hD, Nat.card_congr hD'e.symm.toEquiv, Nat.card_congr hDe.toEquiv]
  have hyK : y ∈ K := hDK hy
  have hy' : e ⟨y, hyK⟩ ∈ D' := ⟨⟨y, hyK⟩, hy, rfl⟩
  have hy2' : e ⟨y, hyK⟩ * e ⟨y, hyK⟩ ≠ 1 := by
    intro h
    apply hy2
    have : (⟨y, hyK⟩ : ↥K) * ⟨y, hyK⟩ = 1 := e.injective (by rw [map_mul, h, map_one])
    simpa using congrArg Subtype.val this
  intro d hdK hd
  have hd' : e ⟨d, hdK⟩ * e ⟨y, hyK⟩ = e ⟨y, hyK⟩ * e ⟨d, hdK⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hd
  have := sl2s_centralizer_le hF D' hcyc hcard hy' hy2' _ hd'
  obtain ⟨x, hx, hxe⟩ := this
  have : x = ⟨d, hdK⟩ := e.injective hxe
  rw [this] at hx
  exact hx

end Torus

end CFSG.GH74.GLS.Stage4.Rest
