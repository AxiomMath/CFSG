module

public import CFSG.LocalAnalysis.EvenBN.U5.LinBasic
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBDiagonal
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin_Bt_eq : c.Bt = (d.F ⊔ c.Kt) ⊓ d.D := by
  unfold CaseBData.Bt CaseBData.Bc
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective, Subgroup.map_sup,
    lin_map_conj_t_F hl k c, lin_map_conj_t_D hl k c]
  rfl

theorem lin_s12 : (d.F ⊔ c.Kc) ⊔ (d.F ⊔ c.Kt) = d.L₁ ∧ (d.F ⊔ c.Kc) ⊓ (d.F ⊔ c.Kt) = d.F ∧
    IsNaturalSection (d.M₁ ⊓ c.Kc) c.Bc d.F c.k :=
  k.s12 c.k inferInstance inferInstance c.card_k c.ψ

theorem lin_L₁_le_normalizer_FK : d.L₁ ≤ normalizer ((d.F ⊔ c.Kc : Subgroup G) : Set G) :=
  fun _ hg => Common.mem_normalizer_sup (lin_L₁_le_normalizer_F hl k c hg)
    (lin_L₁_le_normalizer_Kc hl k c hg)

theorem lin_L₁_le_normalizer_FKt : d.L₁ ≤ normalizer ((d.F ⊔ c.Kt : Subgroup G) : Set G) :=
  fun _ hg => Common.mem_normalizer_sup (lin_L₁_le_normalizer_F hl k c hg)
    (lin_L₁_le_normalizer_Kt hl k c hg)

theorem lin_D_le_L₁ : d.D ≤ d.L₁ := (lin_L₁_eq hl k c) ▸ le_sup_left

theorem lin_L₁_le_normalizer_Bc : d.L₁ ≤ normalizer (c.Bc : Set G) :=
  fun _ hg => Common.mem_normalizer_inf (lin_L₁_le_normalizer_FK hl k c hg)
    (lin_L₁_le_normalizer_D hl k c hg)

theorem lin_F_le_Bc : d.F ≤ c.Bc := le_inf le_sup_left (lin_F_le_D hl k c)

theorem lin_Bc_le_D : c.Bc ≤ d.D := inf_le_right

theorem lin_Bc_le_FK : c.Bc ≤ d.F ⊔ c.Kc := inf_le_left

theorem lin_Bt_le_D : c.Bt ≤ d.D := by
  rw [lin_Bt_eq hl k c]
  exact inf_le_right

theorem lin_F_le_Bt : d.F ≤ c.Bt := by
  rw [lin_Bt_eq hl k c]
  exact le_inf le_sup_left (lin_F_le_D hl k c)

theorem lin_comm_Bc_Y {b y : G} (hb : b ∈ c.Bc) (hy : y ∈ c.Y) : y * b * y⁻¹ * b⁻¹ ∈ d.F := by
  obtain ⟨-, hinf, -⟩ := lin_s12 hl k c
  have hyL : y ∈ d.L₁ := lin_Y_le_L₁ hl k c hy
  have hbL : b ∈ d.L₁ := lin_D_le_L₁ hl k c (lin_Bc_le_D hl k c hb)
  have hyKt : y ∈ d.F ⊔ c.Kt := mem_sup_right (lin_Y_le_Kt hl k c hy)
  have h1 : y * b * y⁻¹ * b⁻¹ ∈ d.F ⊔ c.Kc :=
    mul_mem ((mem_normalizer_iff.1 (lin_L₁_le_normalizer_FK hl k c hyL) b).1
      (lin_Bc_le_FK hl k c hb)) (inv_mem (lin_Bc_le_FK hl k c hb))
  have h2 : y * b * y⁻¹ * b⁻¹ ∈ d.F ⊔ c.Kt := by
    have hbyb : b * y⁻¹ * b⁻¹ ∈ d.F ⊔ c.Kt :=
      (mem_normalizer_iff.1 (lin_L₁_le_normalizer_FKt hl k c hbL) y⁻¹).1 (inv_mem hyKt)
    have := mul_mem hyKt hbyb
    simpa [mul_assoc] using this
  have := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rwa [hinf] at this

theorem lin_exists_odd_Y : ∃ y ∈ c.Y, y ≠ 1 ∧ Odd (orderOf y) := by
  have hf2 := hl.hyp.two_le
  have hkm : Nat.card c.k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, c.card_k, ← pow_mul, mul_comm]
  have hsyl : IsSylowOf 2 (c.Y ⊓ c.S) c.Y :=
    s313a_isSylowOf_Y_inf_S hl.toCaseHyp k c.S_syl c.P_le_S c.ψ
  obtain ⟨J, hJY, -, hJcard⟩ := s313a_exists_J hkm (by omega : 1 ≤ 2 * f) c.φY hsyl
  have hodd : Odd (Nat.card J) := by
    rw [hJcard, hkm]
    have h4 : 2 ≤ 2 ^ (2 * f) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : Even (2 ^ (2 * f)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    rcases h5 with ⟨m, hm⟩
    rw [hm]
    refine ⟨m - 1, ?_⟩
    omega
  have hgt : 1 < Nat.card J := by
    rw [hJcard, hkm]
    have h4 : 2 ^ 2 ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI : Nontrivial J := Finite.one_lt_card_iff_nontrivial.1 hgt
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : J)
  have hy1' : y ≠ 1 := fun e => hy1 (Subtype.ext e)
  refine ⟨y, hJY hy, hy1', ?_⟩
  exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard J hy)

theorem lin_Bc_inf_Bt : c.Bc ⊓ c.Bt = d.F := by
  obtain ⟨-, hinf, -⟩ := lin_s12 hl k c
  apply le_antisymm
  · rintro x ⟨hxB, hxBt⟩
    rw [lin_Bt_eq hl k c] at hxBt
    have := Subgroup.mem_inf.2 ⟨lin_Bc_le_FK hl k c hxB, hxBt.1⟩
    rwa [hinf] at this
  · exact le_inf (lin_F_le_Bc hl k c) (lin_F_le_Bt hl k c)

theorem lin_card_Bc : Nat.card c.Bc = (2 ^ f) ^ 12 := by
  obtain ⟨-, -, hnat⟩ := lin_s12 hl k c
  have h1 := IsNaturalSection.card_eq hnat (lin_F_le_Bc hl k c)
  rw [h1, lin_card_F hl k c, Nat.card_eq_fintype_card (α := c.k), c.card_k]
  ring

theorem lin_card_Bt : Nat.card c.Bt = (2 ^ f) ^ 12 := by
  unfold CaseBData.Bt
  rw [Subgroup.card_map_of_injective (MulAut.conj d.t).injective, lin_card_Bc hl k c]

theorem lin_Bc_sup_Bt : c.Bc ⊔ c.Bt = d.D := by
  have hBt := lin_Bt_le_D hl k c
  have hle : c.Bc ⊔ c.Bt ≤ d.D := sup_le (lin_Bc_le_D hl k c) hBt
  have hnorm : c.Bt ≤ normalizer (c.Bc : Set G) :=
    hBt.trans ((lin_D_le_L₁ hl k c).trans (lin_L₁_le_normalizer_Bc hl k c))
  have hcard := Common.card_sup_mul_card_inf_eq hnorm
  rw [lin_Bc_inf_Bt hl k c, lin_card_F hl k c, lin_card_Bc hl k c, lin_card_Bt hl k c] at hcard
  have hD : Nat.card d.D = (2 ^ f) ^ 16 := k.s9e.card_D
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hD]
  have hpos : 0 < (2 ^ f) ^ 8 := by positivity
  have : Nat.card (c.Bc ⊔ c.Bt : Subgroup G) = (2 ^ f) ^ 16 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hcard]
    ring
  exact this.ge

theorem lin_Bc_elem (h41 : c.Sec41) : IsElemAbelian 2 c.Bc := by
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀odd⟩ := lin_exists_odd_Y hl k c
  have hfree := h41.free y₀ hy₀Y hy₀odd hy₀1
  have hFB := lin_F_le_Bc hl k c
  have hBD := lin_Bc_le_D hl k c
  have hS2 : IsPGroup 2 c.S := c.S_syl.isPGroup
  have hB2 : IsPGroup 2 c.Bc := hS2.to_le (hBD.trans (lin_D_le_S hl k c))
  have hz_le : zpowers y₀ ≤ c.Y := zpowers_le.2 hy₀Y
  have hdec : ∀ b ∈ c.Bc, ∃ z ∈ c.Bc ⊓ centralizer ((zpowers y₀ : Subgroup G) : Set G),
      ∃ f₀ ∈ d.F, b = z * f₀ := by
    intro b hb
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hB2
    haveI : Group.IsNilpotent c.Bc := IsPGroup.isNilpotent hB2
    have hsolv : Group.IsSolvable c.Bc := inferInstance
    have hcop : (Nat.card (zpowers y₀)).Coprime (Nat.card c.Bc) := by
      rw [Nat.card_zpowers, hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hy₀odd)
    have hMN : c.Bc ≤ normalizer (d.F : Set G) :=
      hBD.trans ((lin_D_le_L₁ hl k c).trans (lin_L₁_le_normalizer_F hl k c))
    have hSM : zpowers y₀ ≤ normalizer (c.Bc : Set G) :=
      hz_le.trans ((lin_Y_le_L₁ hl k c).trans (lin_L₁_le_normalizer_Bc hl k c))
    have hSN : zpowers y₀ ≤ normalizer (d.F : Set G) :=
      hz_le.trans ((lin_Y_le_L₁ hl k c).trans (lin_L₁_le_normalizer_F hl k c))
    have hfix : ∀ s ∈ zpowers y₀, b⁻¹ * (s * b * s⁻¹) ∈ d.F := by
      intro s hs
      have hx := lin_comm_Bc_Y hl k c hb (hz_le hs)
      have hcomm := mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c (hBD hb)) _ hx
      have e : b⁻¹ * (s * b * s⁻¹) = s * b * s⁻¹ * b⁻¹ := by
        have h2 : s * b * s⁻¹ * b⁻¹ * b = b * (s * b * s⁻¹ * b⁻¹) := hcomm
        calc b⁻¹ * (s * b * s⁻¹) = b⁻¹ * (s * b * s⁻¹ * b⁻¹ * b) := by group
          _ = b⁻¹ * (b * (s * b * s⁻¹ * b⁻¹)) := by rw [h2]
          _ = s * b * s⁻¹ * b⁻¹ := by group
      rw [e]
      exact hx
    exact Common.exists_mem_inf_centralizer_mul_of_coprime hFB hMN hSM hSN hsolv hcop hb hfix
  set C := c.Bc ⊓ centralizer ((zpowers y₀ : Subgroup G) : Set G) with hC
  have hCB : C ≤ c.Bc := inf_le_left
  have hCfix : ∀ z ∈ C, y₀ * z * y₀⁻¹ = z := by
    intro z hz
    have := mem_centralizer_iff.1 hz.2 y₀ (mem_zpowers y₀)
    rw [this]
    group
  have hCF : ∀ z ∈ C, z ∈ d.F → z = 1 := fun z hz hzF => hfree z hzF (hCfix z hz)
  have hFcomm : ∀ {v w : G}, v ∈ d.F → w ∈ d.F → v * w = w * v := fun {v w} hv hw =>
    Prelim.mul_comm_of_mem (lin_isElementaryAbelian_F hl k c) hv hw
  have hFsq : ∀ v ∈ d.F, v * v = 1 := fun v hv => by
    haveI := lin_isElementaryAbelian_F hl k c
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.F) v hv
    simpa [sq] using this
  have hCsq : ∀ z ∈ C, z * z = 1 := fun z hz =>
    hCF _ (mul_mem hz hz) (lin_mul_self_mem_F hl k c z (hBD (hCB hz)))
  have hCcomm : ∀ z ∈ C, ∀ w ∈ C, z * w = w * z := by
    intro z hz w hw
    have h1 : z * w * z⁻¹ * w⁻¹ ∈ d.F :=
      lin_commutator_mem_F hl k c (hBD (hCB hz)) (hBD (hCB hw))
    have h2 : z * w * z⁻¹ * w⁻¹ ∈ C := mul_mem (mul_mem (mul_mem hz hw) (inv_mem hz)) (inv_mem hw)
    have h3 := hCF _ h2 h1
    calc z * w = z * w * z⁻¹ * w⁻¹ * w * z := by group
      _ = w * z := by rw [h3]; group
  have hFcent : ∀ v ∈ d.F, ∀ x ∈ d.D, v * x = x * v := fun v hv x hx =>
    mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hx) v hv
  refine LinearThree.isElemAbelian_of_forall ?_ ?_
  · intro b hb b' hb'
    obtain ⟨z, hz, f₀, hf₀, rfl⟩ := hdec b hb
    obtain ⟨z', hz', f₀', hf₀', rfl⟩ := hdec b' hb'
    have hzD : z ∈ d.D := hBD (hCB hz)
    have hz'D : z' ∈ d.D := hBD (hCB hz')
    have e1 : z * f₀ * (z' * f₀') = z * z' * (f₀ * f₀') := by
      calc z * f₀ * (z' * f₀') = z * (f₀ * z') * f₀' := by group
        _ = z * (z' * f₀) * f₀' := by rw [hFcent f₀ hf₀ z' hz'D]
        _ = z * z' * (f₀ * f₀') := by group
    have e2 : z' * f₀' * (z * f₀) = z' * z * (f₀' * f₀) := by
      calc z' * f₀' * (z * f₀) = z' * (f₀' * z) * f₀ := by group
        _ = z' * (z * f₀') * f₀ := by rw [hFcent f₀' hf₀' z hzD]
        _ = z' * z * (f₀' * f₀) := by group
    rw [e1, e2, hCcomm z hz z' hz', hFcomm hf₀ hf₀']
  · intro b hb
    obtain ⟨z, hz, f₀, hf₀, rfl⟩ := hdec b hb
    have hzD : z ∈ d.D := hBD (hCB hz)
    have e : (z * f₀) ^ 2 = z * z * (f₀ * f₀) := by
      calc (z * f₀) ^ 2 = z * (f₀ * z) * f₀ := by rw [sq]; group
        _ = z * (z * f₀) * f₀ := by rw [hFcent f₀ hf₀ z hzD]
        _ = z * z * (f₀ * f₀) := by group
    rw [e, hCsq z hz, hFsq f₀ hf₀, one_mul]

theorem lin_sec42_basic (h41 : c.Sec41) :
    IsElemAbelian 2 c.Bc ∧ Nat.card c.Bc = (2 ^ f) ^ 12 ∧ c.Bc ⊓ c.Bt = d.F ∧
      c.Bc ⊔ c.Bt = d.D :=
  ⟨lin_Bc_elem hl k c h41, lin_card_Bc hl k c, lin_Bc_inf_Bt hl k c, lin_Bc_sup_Bt hl k c⟩

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
