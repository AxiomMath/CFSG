module

public import CFSG.LocalAnalysis.EvenBN.U4.CenterUTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  card_sup_mul_card_inf_eq)
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)


variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

theorem RG_le_U_sup_W2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) :
    miyamotoRG h L η t Q ≤ 𝓤 ⊔ (𝓦 ⊓ prodFactorTwo ψ) := by
  intro r hr
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
  rw [← (hS.W_eq_sup (ψ := ψ) hk).1] at hw
  have hle : (𝓦 ⊓ prodFactorOne ψ) ⊔ (𝓦 ⊓ prodFactorTwo ψ) ≤ 𝓤 ⊔ (𝓦 ⊓ prodFactorTwo ψ) :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hw' : w ∈ 𝓤 ⊔ (𝓦 ⊓ prodFactorTwo ψ) := hle hw
  exact mul_mem hw' (mem_sup_left (mem_sup_left hy))

theorem centerIn_U_inf_centralizer_W2_le_E [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {z : G} (hz : z ∈ CFSG.centerIn 𝓤)
    (hzW : z ∈ centralizer ((𝓦 ⊓ prodFactorTwo ψ : Subgroup G) : Set G)) :
    z ∈ miyamotoEG h L η Q := by
  rw [← hS.centerIn_RG]
  refine mem_inf.2 ⟨hS.U_le_RG (mem_inf.1 hz).1, ?_⟩
  have hC : 𝓤 ⊔ (𝓦 ⊓ prodFactorTwo ψ) ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun u hu => ?_) (fun w hw => ?_)
    · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hz).2 u hu)
    · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzW w hw)
  exact mem_centralizer_iff.2 fun r hr =>
    (mem_centralizer_singleton_iff.1 (hC (hS.RG_le_U_sup_W2 hk hr)))

theorem R1G_mem_M1 (hS : Setting h L η t Q T) : miyamotoR1G h L η ∈ miyamotoM1G h L η t :=
  hS.sec3_12_one.2.2.1 hS.R1G_mem_N1

theorem centerIn_U_inf_r1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) (hZF : CFSG.centerIn 𝓤 ≤ miyamotoFG h L η t Q) :
    CFSG.centerIn 𝓤 ⊓ (CFSG.centerIn 𝓤).map (MulAut.conj (miyamotoR1G h L η)).toMonoidHom =
      ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := CFSG.centerIn 𝓤 with hZdef
  set r := miyamotoR1G h L η with hrdef
  have hrr : r * r = 1 := hS.R1G_mul_self
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  set V := Z ⊓ Z.map (MulAut.conj r).toMonoidHom with hV
  have hV2 : IsPGroup 2 V := hS.isPGroup_RG.to_le (inf_le_left.trans (inf_le_left.trans
    hS.U_le_RG))
  have hX2Z : prodFactorTwo ψ ≤ normalizer (Z : Set G) := fun x hx =>
    normalizer_le_normalizer_centerIn _ (hS.X2_le_normalizer_U hx)
  have hrX2 : r ∈ normalizer (prodFactorTwo ψ : Set G) :=
    Common.le_normalizer_prodFactorTwo ψ hS.R1G_mem_M1
  have hX2Zr : prodFactorTwo ψ ≤
      normalizer ((Z.map (MulAut.conj r).toMonoidHom : Subgroup G) : Set G) := by
    intro x hx
    have hx' : r⁻¹ * x * r ∈ prodFactorTwo ψ := by
      have := (mem_normalizer_iff.1 (inv_mem hrX2) x).1 hx
      rwa [inv_inv] at this
    have key : ∀ y ∈ prodFactorTwo ψ, ∀ z ∈ Z.map (MulAut.conj r).toMonoidHom,
        y * z * y⁻¹ ∈ Z.map (MulAut.conj r).toMonoidHom := by
      intro y hy z hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hy' : r⁻¹ * y * r ∈ prodFactorTwo ψ := by
        have := (mem_normalizer_iff.1 (inv_mem hrX2) y).1 hy
        rwa [inv_inv] at this
      refine ⟨(r⁻¹ * y * r) * z' * (r⁻¹ * y * r)⁻¹,
        (mem_normalizer_iff.1 (hX2Z hy') z').1 hz', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [mem_normalizer_iff]
    intro z
    refine ⟨key x hx z, fun hz => ?_⟩
    have := key x⁻¹ (inv_mem hx) _ hz
    rwa [inv_inv, show x⁻¹ * (x * z * x⁻¹) * x = z by group] at this
  have hWV : 𝓦 ⊓ prodFactorTwo ψ ≤ normalizer (V : Set G) := fun w hw =>
    mem_normalizer_inf (hX2Z (mem_inf.1 hw).2) (hX2Zr (mem_inf.1 hw).2)
  by_contra hne
  have hW2 : IsPGroup 2 (𝓦 ⊓ prodFactorTwo ψ : Subgroup G) :=
    hS.isPGroup_RG.to_le (inf_le_left.trans inf_le_left)
  have hfix := U5.Prelim.inf_centralizer_ne_bot_of_pow_mem hV2 hne hWV fun w hw => by
    obtain ⟨n, hn⟩ := hW2 ⟨w, hw⟩
    exact ⟨n, by rw [show w ^ 2 ^ n = 1 from congrArg Subtype.val hn]; exact one_mem _⟩
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hfix
  obtain ⟨heV, heC⟩ := mem_inf.1 he
  obtain ⟨heZ, heZr⟩ := mem_inf.1 heV
  have heE : (e : G) ∈ miyamotoEG h L η Q :=
    hS.centerIn_U_inf_centralizer_W2_le_E hk heZ heC
  obtain ⟨z, hz, hze⟩ := heZr
  have hzF : z ∈ miyamotoFG h L η t Q := hZF hz
  have hmem : z ∈ (miyamotoEG h L η Q).map (MulAut.conj r⁻¹).toMonoidHom ⊓
      miyamotoFG h L η t Q := by
    refine mem_inf.2 ⟨⟨e, heE, ?_⟩, hzF⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hze ⊢
    rw [← hze]
    group
  rw [hS.E_r1_inf_F, mem_bot] at hmem
  have he' : e = 1 := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hze
    rw [← hze, hmem, mul_one, mul_inv_cancel]
  exact he1 (Subtype.ext he')

theorem F1_eq_centerIn_U_sup_r1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZF : CFSG.centerIn 𝓤 ≤ miyamotoFG h L η t Q) :
    Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4 ∧
      miyamotoF1G h L η t = CFSG.centerIn 𝓤 ⊔
        (CFSG.centerIn 𝓤).map (MulAut.conj (miyamotoR1G h L η)).toMonoidHom := by
  set Z := CFSG.centerIn 𝓤 with hZdef
  set r := miyamotoR1G h L η with hrdef
  set Zr := Z.map (MulAut.conj r).toMonoidHom with hZr
  have hZF1 : Z ≤ miyamotoF1G h L η t := hS.centerIn_U_le_F1
  have hrF1 : r ∈ normalizer (miyamotoF1G h L η t : Set G) := hS.M1_le_normalizer_F1 hS.R1G_mem_M1
  have hZrF1 : Zr ≤ miyamotoF1G h L η t := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.1 hrF1 z).1 (hZF1 hz)
  have hcardZr : Nat.card Zr = Nat.card Z :=
    card_map_of_injective (MulAut.conj r).injective
  have hN : Zr ≤ normalizer (Z : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [hS.F1_comm (hZrF1 hx) (hZF1 hz), mul_inv_cancel_right]
      exact hz
    · intro hz
      have hz' : x * z * x⁻¹ ∈ miyamotoF1G h L η t := hZF1 hz
      have hzF1 : z ∈ miyamotoF1G h L η t := by
        have := mul_mem (mul_mem (inv_mem (hZrF1 hx)) hz') (hZrF1 hx)
        rwa [show x⁻¹ * (x * z * x⁻¹) * x = z by group] at this
      rwa [hS.F1_comm (hZrF1 hx) hzF1, mul_inv_cancel_right] at hz
  have h1 := card_sup_mul_card_inf_eq hN
  rw [hS.centerIn_U_inf_r1 hk hZF, card_bot, mul_one, hcardZr] at h1
  have hle : Z ⊔ Zr ≤ miyamotoF1G h L η t := sup_le hZF1 hZrF1
  have hcardle := Subgroup.card_le_of_le hle
  rw [h1, hS.card_F1] at hcardle
  have hge := hS.card_centerIn_U_ge (ψ := ψ) hk hψt
  have hZ4 : Nat.card Z = (2 ^ f) ^ 4 := by
    refine le_antisymm ?_ hge
    by_contra hlt
    push Not at hlt
    have : (2 ^ f) ^ 4 * (2 ^ f) ^ 4 < Nat.card Z * Nat.card Z :=
      Nat.mul_lt_mul_of_lt_of_le hlt hlt.le Nat.card_pos
    have h8 : (2 ^ f) ^ 8 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
    omega
  refine ⟨hZ4, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [h1, hZ4, hS.card_F1]
  ring_nf
  exact le_rfl

theorem centerIn_U_inf_t [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    CFSG.centerIn 𝓤 ⊓ (CFSG.centerIn 𝓤).map (MulAut.conj t).toMonoidHom =
      miyamotoEG h L η Q := by
  set Z := CFSG.centerIn 𝓤 with hZdef
  have htE : t ∈ normalizer (miyamotoEG h L η Q : Set G) :=
    hS.normalizer_P1_le_normalizer_E hS.t_mem_normalizer_P1
  refine le_antisymm (fun x hx => ?_) (le_inf hS.E_le_centerIn_U fun e he => ?_)
  · obtain ⟨hxZ, z, hz, rfl⟩ := mem_inf.1 hx
    refine hS.centerIn_U_inf_centralizer_W2_le_E hk hxZ (mem_centralizer_iff.2 fun w hw => ?_)
    have hw' := hS.t_conj_mem_W1 hψt hw
    have hc := mem_centralizer_iff.1 (mem_inf.1 hz).2 _ (mem_sup_right hw')
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc w * (t * z * t⁻¹) = t * ((t⁻¹ * w * t) * z) * t⁻¹ := by group
      _ = t * (z * (t⁻¹ * w * t)) * t⁻¹ := by rw [hc]
      _ = t * z * t⁻¹ * w := by group
  · have he' : t⁻¹ * e * t ∈ miyamotoEG h L η Q := by
      have := (mem_normalizer_iff.1 (inv_mem htE) e).1 he
      rwa [inv_inv] at this
    refine ⟨t⁻¹ * e * t, hS.E_le_centerIn_U he', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem F_eq_centerIn_U_sup_t [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZF : CFSG.centerIn 𝓤 ≤ miyamotoFG h L η t Q) :
    miyamotoFG h L η t Q =
      CFSG.centerIn 𝓤 ⊔ (CFSG.centerIn 𝓤).map (MulAut.conj t).toMonoidHom := by
  set Z := CFSG.centerIn 𝓤 with hZdef
  set Zt := Z.map (MulAut.conj t).toMonoidHom with hZt
  have htF : t ∈ normalizer (miyamotoFG h L η t Q : Set G) :=
    hS.normalizer_P1_le_normalizer_F hS.t_mem_normalizer_P1
  have hZtF : Zt ≤ miyamotoFG h L η t Q := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.1 htF z).1 (hZF hz)
  have hZF1 : Z ≤ miyamotoF1G h L η t := hS.centerIn_U_le_F1
  have hN : Zt ≤ normalizer (Z : Set G) := by
    intro x hx
    have hxF1 := hS.F_le_F1 (hZtF hx)
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [hS.F1_comm hxF1 (hZF1 hz), mul_inv_cancel_right]
      exact hz
    · intro hz
      have hz' : x * z * x⁻¹ ∈ miyamotoF1G h L η t := hZF1 hz
      have hzF1 : z ∈ miyamotoF1G h L η t := by
        have := mul_mem (mul_mem (inv_mem hxF1) hz') hxF1
        rwa [show x⁻¹ * (x * z * x⁻¹) * x = z by group] at this
      rwa [hS.F1_comm hxF1 hzF1, mul_inv_cancel_right] at hz
  have hcardZt : Nat.card Zt = Nat.card Z :=
    card_map_of_injective (MulAut.conj t).injective
  have h1 := card_sup_mul_card_inf_eq hN
  rw [hS.centerIn_U_inf_t hk hψt, hcardZt, (hS.F1_eq_centerIn_U_sup_r1 hk hψt hZF).1,
    hS.card_E] at h1
  have hle : Z ⊔ Zt ≤ miyamotoFG h L η t Q := sup_le hZF hZtF
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hS.card_F]
  have h8 : (2 ^ f) ^ 4 * (2 ^ f) ^ 4 = (2 ^ f) ^ 6 * (2 ^ f) ^ 2 := by ring
  rw [h8] at h1
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) h1).symm.le

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
