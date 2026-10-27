module

public import CFSG.LocalAnalysis.EvenBN.U5.LinSec42E
public import CFSG.LocalAnalysis.EvenBN.U5.LinNaturalSection

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K}  {d : Data G h}

namespace CaseBData

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin_comm_Bc_Kt {b y : G} (hb : b ∈ c.Bc) (hy : y ∈ c.Kt) :
    y * b * y⁻¹ * b⁻¹ ∈ d.F := by
  obtain ⟨-, hinf, -⟩ := lin_s12 hl k c
  have hyL : y ∈ d.L₁ := lin_Kt_le_L₁ hl k c hy
  have hbL : b ∈ d.L₁ := lin_D_le_L₁ hl k c (lin_Bc_le_D hl k c hb)
  have hyKt : y ∈ d.F ⊔ c.Kt := mem_sup_right hy
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

theorem lin_map_conj_t_M₁ : d.M₁.map (MulAut.conj d.t).toMonoidHom = d.M₁ :=
  map_conj_eq_of_mem_normalizer hl.hyp.t_mem_normalizer_M₁

theorem lin_natural_Bt : IsNaturalSection (d.M₁ ⊓ c.Kt) c.Bt d.F c.k := by
  obtain ⟨-, -, hnat⟩ := lin_s12 hl k c
  have h0 := LinCase.natural_section_map_conj hnat d.t
  have h1 : (d.M₁ ⊓ c.Kc).map (MulAut.conj d.t).toMonoidHom = d.M₁ ⊓ c.Kt := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective, lin_map_conj_t_M₁ hl k c]
    rfl
  rw [h1, lin_map_conj_t_F hl k c] at h0
  exact h0

theorem lin_inf_centralizer_Bc (h42 : c.Sec42) {b : G} (hb : b ∈ c.Bc) (hbt : b ∉ c.Bt) :
    d.D ⊓ centralizer ({b} : Set G) = c.Bc := by
  have hBD := lin_Bc_le_D hl k c
  have hBtD := lin_Bt_le_D hl k c
  have hFcent : ∀ f₀ ∈ d.F, ∀ x ∈ d.D, f₀ * x = x * f₀ := fun f₀ hf₀ x hx =>
    mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hx) f₀ hf₀
  have hBcomm : ∀ x ∈ c.Bc, ∀ y ∈ c.Bc, x * y = y * x := fun x hx y hy =>
    LinearThree.comm_of_isElemAbelian (CFSG.Open.isElemAbelian_of_isElementaryAbelian
      (h := h42.elem)) hx hy
  apply le_antisymm
  · rintro x ⟨hxD, hxc⟩
    have hxsup : x ∈ c.Bc ⊔ c.Bt := by rw [h42.sup]; exact hxD
    have hnorm : c.Bt ≤ normalizer (c.Bc : Set G) :=
      hBtD.trans ((lin_D_le_L₁ hl k c).trans (lin_L₁_le_normalizer_Bc hl k c))
    obtain ⟨a, ha, b', hb', rfl⟩ := Common.exists_mul_of_le_normalizer hnorm x hxsup
    have hb'c : b' ∈ c.Bt ⊓ centralizer ({b} : Set G) := by
      refine ⟨hb', mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : a * b' * b = b * (a * b') := mem_centralizer_singleton_iff.1 hxc
      have h2 : a * b = b * a := hBcomm a ha b hb
      have : a * (b' * b) = a * (b * b') := by
        calc a * (b' * b) = a * b' * b := by group
          _ = b * (a * b') := h1
          _ = (b * a) * b' := by group
          _ = (a * b) * b' := by rw [h2]
          _ = a * (b * b') := by group
      exact mul_left_cancel this
    set Z : Subgroup G := c.Bt ⊓ centralizer ({b} : Set G) with hZ
    have hFZ : d.F ≤ Z := fun f₀ hf₀ =>
      ⟨lin_F_le_Bt hl k c hf₀, mem_centralizer_singleton_iff.2
        (hFcent f₀ hf₀ b (hBD hb))⟩
    have hinv : ∀ y ∈ d.M₁ ⊓ c.Kt, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z := by
      intro y hy z hz
      have hyL : y ∈ d.L₁ := lin_Kt_le_L₁ hl k c hy.2
      have hzBt : y * z * y⁻¹ ∈ c.Bt :=
        (mem_normalizer_iff.1 (lin_L₁_le_normalizer_Bt hl k c hyL) z).1 hz.1
      refine ⟨hzBt, mem_centralizer_singleton_iff.2 ?_⟩
      have hu := lin_comm_Bc_Kt hl k c hb hy.2
      have hzb : z * b = b * z := mem_centralizer_singleton_iff.1 hz.2
      set u : G := y * b * y⁻¹ * b⁻¹ with hu_def
      have hyb : y * b * y⁻¹ = u * b := by rw [hu_def]; group
      have hzD : y * z * y⁻¹ ∈ d.D := hBtD hzBt
      have h1 : (y * z * y⁻¹) * (y * b * y⁻¹) = (y * b * y⁻¹) * (y * z * y⁻¹) := by
        calc (y * z * y⁻¹) * (y * b * y⁻¹) = y * (z * b) * y⁻¹ := by group
          _ = y * (b * z) * y⁻¹ := by rw [hzb]
          _ = (y * b * y⁻¹) * (y * z * y⁻¹) := by group
      rw [hyb] at h1
      have h2 : (y * z * y⁻¹) * u = u * (y * z * y⁻¹) :=
        (hFcent u hu _ hzD).symm
      have hw_u : Commute (y * z * y⁻¹) u := h2
      have hw_ub : Commute (y * z * y⁻¹) (u * b) := h1
      have hw_b : Commute (y * z * y⁻¹) b := by
        have := (hw_u.inv_right).mul_right hw_ub
        simpa using this
      exact hw_b.eq
    rcases LinCase.natural_section_eq_of_invariant (lin_natural_Bt hl k c) hFZ inf_le_left hinv with
      hZF | hZBt
    ·
      have hb'F : b' ∈ d.F := by
        have : b' ∈ Z := hb'c
        rw [hZF] at this
        exact this
      exact mul_mem ha (lin_F_le_Bc hl k c hb'F)
    ·
      exfalso
      apply hbt
      have hbcen : b ∈ CFSG.centerIn d.D := by
        refine ⟨hBD hb, mem_centralizer_iff.2 fun w hw => ?_⟩
        have hwsup : w ∈ c.Bc ⊔ c.Bt := by rw [h42.sup]; exact hw
        obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := Common.exists_mul_of_le_normalizer hnorm w hwsup
        have h1 : b * b₁ = b₁ * b := by
          have : b₁ ∈ Z := by rw [hZBt]; exact hb₁
          exact (mem_centralizer_singleton_iff.1 this.2).symm
        have h2 : a₁ * b = b * a₁ := hBcomm a₁ ha₁ b hb
        calc a₁ * b₁ * b = a₁ * (b₁ * b) := by group
          _ = a₁ * (b * b₁) := by rw [h1]
          _ = (a₁ * b) * b₁ := by group
          _ = (b * a₁) * b₁ := by rw [h2]
          _ = b * (a₁ * b₁) := by group
      rw [lin_centerIn_D hl k c] at hbcen
      exact lin_F_le_Bt hl k c hbcen
  · intro x hx
    exact ⟨hBD hx, mem_centralizer_singleton_iff.2 (hBcomm x hx b hb)⟩

theorem lin_sec43_one (h42 : c.Sec42) :
    ∀ Y : Subgroup G, Y ≤ d.D → CFSG.IsElementaryAbelian 2 Y → Y ≤ c.Bc ∨ Y ≤ c.Bt := by
  intro Y hY hYel
  have hf2 := hl.hyp.two_le
  have hBD := lin_Bc_le_D hl k c
  have hBtD := lin_Bt_le_D hl k c
  have hnorm : c.Bt ≤ normalizer (c.Bc : Set G) :=
    hBtD.trans ((lin_D_le_L₁ hl k c).trans (lin_L₁_le_normalizer_Bc hl k c))
  have hBtel : CFSG.IsElementaryAbelian 2 c.Bt :=
    (CFSG.Open.IsElemAbelian.map (CFSG.Open.isElemAbelian_of_isElementaryAbelian
      (h := h42.elem)) (MulAut.conj d.t).toMonoidHom).isElementaryAbelian
  have h4 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hFlt : Nat.card d.F < Nat.card c.Bc := by
    rw [lin_card_F hl k c, h42.card]
    exact Nat.pow_lt_pow_right h4 (by norm_num)
  obtain ⟨b, hb, hbt⟩ : ∃ b ∈ c.Bc, b ∉ c.Bt := by
    by_contra hcon
    push_neg at hcon
    have hle : c.Bc ≤ c.Bt := hcon
    have h1 := inf_eq_left.2 hle
    rw [h42.inf] at h1
    rw [← h1] at hFlt
    exact lt_irrefl _ hFlt
  obtain ⟨b', hb', hb'B⟩ : ∃ b' ∈ c.Bt, b' ∉ c.Bc := by
    by_contra hcon
    push_neg at hcon
    have hle : c.Bt ≤ c.Bc := hcon
    have h1 := inf_eq_right.2 hle
    rw [h42.inf] at h1
    have hFlt' : Nat.card d.F < Nat.card c.Bt := by
      rw [lin_card_F hl k c, lin_card_Bt hl k c]
      exact Nat.pow_lt_pow_right h4 (by norm_num)
    rw [← h1] at hFlt'
    exact lt_irrefl _ hFlt'
  have hprod : Common.TwoElementaryProduct d.D c.Bc c.Bt :=
    { le_left := hBD
      le_right := hBtD
      exists_mul := fun s hs =>
        Common.exists_mul_of_le_normalizer hnorm s (by rw [h42.sup]; exact hs)
      isElementaryAbelian_left := h42.elem
      isElementaryAbelian_right := hBtel
      exists_mul_ne := ⟨b, hBD hb, b', hBtD hb', fun hcomm => hb'B (by
        have : b' ∈ d.D ⊓ centralizer ({b} : Set G) :=
          ⟨hBtD hb', mem_centralizer_singleton_iff.2 hcomm.symm⟩
        rwa [lin_inf_centralizer_Bc hl k c h42 hb hbt] at this)⟩
      inf_centralizer_left := fun a ha hat => lin_inf_centralizer_Bc hl k c h42 ha hat }
  haveI := hYel
  exact hprod.le_or_le hY

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
