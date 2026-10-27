module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Field
public import CFSG.CGT.PushingUpLit.T2KR.MMAct

public section

namespace CFSG.CGT.PushingUpLit.T2KR.MData

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

theorem conj_vec {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) :
    m * H.vec w * m⁻¹ = H.vec (H.act m w) :=
  (H.vec_ψe (H.conj_vec_mem hm w)).symm

theorem vec_injective : Function.Injective H.vec := fun w w' h => by
  rw [← H.ψe_vec w, ← H.ψe_vec w', h]

theorem act_smul_L {l : G} (hl : l ∈ L) (c : Fq n) (w : Fin 2 → Fq n) :
    H.act l (c • w) = c • H.act l w := by
  rw [H.act_L hl, H.act_L hl, Matrix.mulVec_smul]

theorem act_zero {m : G} (hm : m ∈ M) : H.act m 0 = 0 := by
  have := H.act_add hm 0 0
  simpa using this

theorem act_involution {m : G} (hm : m ∈ M) (hm2 : m * m = 1) (w : Fin 2 → Fq n) :
    H.act m (H.act m w) = w := by
  rw [← H.act_mul hm, hm2, H.act_one]

theorem act_conj {a h : G} (haM : a ∈ M) (hhM : h ∈ M) (w : Fin 2 → Fq n) :
    H.act (h * a * h⁻¹) w = H.act h (H.act a (H.act h⁻¹ w)) := by
  rw [H.act_mul (M.inv_mem hhM), H.act_mul haM]

theorem sq_mul_vec {a : G} (ha : a ∈ M) (ha2 : a * a = 1) (w : Fin 2 → Fq n) :
    (a * H.vec w) * (a * H.vec w) = H.vec (H.act a w + w) := by
  have h1 := H.conj_vec ha w
  calc (a * H.vec w) * (a * H.vec w) = (a * H.vec w * a⁻¹) * (a * a) * H.vec w := by group
    _ = H.vec (H.act a w + w) := by rw [h1, ha2, mul_one, H.vec_add]

end CFSG.CGT.PushingUpLit.T2KR.MData

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

structure IsTv (e₁ e₂ : Fin 2 → Fq n) (a : G) (s : Fq n) : Prop where
  fix : H.act a e₁ = e₁
  shift : H.act a e₂ = e₂ + s • e₁

variable {H}

theorem IsTv.act_coord {e₁ e₂ : Fin 2 → Fq n} {a : G} {s : Fq n} (h : IsTv H e₁ e₂ a s)
    (ha : a ∈ L) (α β : Fq n) :
    H.act a (α • e₁ + β • e₂) = (α + s * β) • e₁ + β • e₂ := by
  rw [H.act_add (H.le ha), H.act_smul_L ha, H.act_smul_L ha, h.fix, h.shift]
  module

theorem act_inv_diag {h : G} {e₁ e₂ : Fin 2 → Fq n} {lam : Fq n} (hhL : h ∈ L) (hlam : lam ≠ 0)
    (hh1 : H.act h e₁ = lam • e₁) (hh2 : H.act h e₂ = lam⁻¹ • e₂) :
    H.act h⁻¹ e₁ = lam⁻¹ • e₁ ∧ H.act h⁻¹ e₂ = lam • e₂ := by
  have hhM : h ∈ M := H.le hhL
  constructor
  · have h1 : H.act h (lam⁻¹ • e₁) = e₁ := by
      rw [H.act_smul_L hhL, hh1, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    have := H.act_inv_act hhM (lam⁻¹ • e₁)
    rwa [h1] at this
  · have h1 : H.act h (lam • e₂) = e₂ := by
      rw [H.act_smul_L hhL, hh2, smul_smul, mul_inv_cancel₀ hlam, one_smul]
    have := H.act_inv_act hhM (lam • e₂)
    rwa [h1] at this

theorem IsTv.conj_torus {e₁ e₂ : Fin 2 → Fq n} {a h : G} {s lam : Fq n}
    (hs : IsTv H e₁ e₂ a s) (haL : a ∈ L) (hhL : h ∈ L) (hlam : lam ≠ 0)
    (hh1 : H.act h e₁ = lam • e₁) (hh2 : H.act h e₂ = lam⁻¹ • e₂) :
    IsTv H e₁ e₂ (h * a * h⁻¹) (lam ^ 2 * s) := by
  have hhM : h ∈ M := H.le hhL
  have hMa : a ∈ M := H.le haL
  obtain ⟨hinv1, hinv2⟩ := act_inv_diag hhL hlam hh1 hh2
  constructor
  · rw [H.act_conj hMa hhM, hinv1, H.act_smul_L haL, hs.fix, H.act_smul_L hhL, hh1, smul_smul,
      inv_mul_cancel₀ hlam, one_smul]
  · rw [H.act_conj hMa hhM, hinv2, H.act_smul_L haL, hs.shift, smul_add, smul_smul, H.act_add hhM,
      H.act_smul_L hhL, H.act_smul_L hhL, hh1, hh2, smul_smul, smul_smul,
      mul_inv_cancel₀ hlam, one_smul]
    module

theorem e13_core {e₁ e₂ : Fin 2 → Fq n}
    (hspan : ∀ w : Fin 2 → Fq n, ∃ α β : Fq n, w = α • e₁ + β • e₂) (he₁ : e₁ ≠ 0) {lam : Fq n}
    (hlam : lam ^ 2 + lam + 1 = 0) {r h : G} (hrL : r ∈ L) (hr2 : r * r = 1)
    (hr : IsTv H e₁ e₂ r 1) (hhL : h ∈ L) (hh1 : H.act h e₁ = lam • e₁)
    (hh2 : H.act h e₂ = lam⁻¹ • e₂) (hO : oTwoIn L = blockU L) :
    r * (h * r * h⁻¹) = (h * r * h⁻¹) * r := by
  have hlam0 : lam ≠ 0 := root_ne_zero hlam
  have h2 : (2 : Fq n) = 0 := two_eq_zero
  have h3 : ∀ x : Fin 2 → Fq n, (2 : Fq n) • x = 0 := fun x => by rw [h2, zero_smul]
  have hhM : h ∈ M := H.le hhL
  have hrM : r ∈ M := H.le hrL
  set a₁ := h * r * h⁻¹ with ha₁
  set a₂ := h * a₁ * h⁻¹ with ha₂
  have ha₁L : a₁ ∈ L := L.mul_mem (L.mul_mem hhL hrL) (L.inv_mem hhL)
  have ha₂L : a₂ ∈ L := L.mul_mem (L.mul_mem hhL ha₁L) (L.inv_mem hhL)
  have ha₁M : a₁ ∈ M := H.le ha₁L
  have ha₂M : a₂ ∈ M := H.le ha₂L
  have ha₁2 : a₁ * a₁ = 1 := by
    calc a₁ * a₁ = h * (r * r) * h⁻¹ := by simp only [ha₁]; group
      _ = 1 := by rw [hr2]; group
  have ha₂2 : a₂ * a₂ = 1 := by
    calc a₂ * a₂ = h * (a₁ * a₁) * h⁻¹ := by simp only [ha₂]; group
      _ = 1 := by rw [ha₁2]; group
  have htv₁ : IsTv H e₁ e₂ a₁ (lam ^ 2 * 1) := hr.conj_torus hrL hhL hlam0 hh1 hh2
  have htv₂ : IsTv H e₁ e₂ a₂ (lam ^ 2 * (lam ^ 2 * 1)) := htv₁.conj_torus ha₁L hhL hlam0 hh1 hh2
  have hl4 : lam ^ 2 * (lam ^ 2 * 1) = lam := by
    linear_combination lam * root_cube hlam
  rw [hl4] at htv₂
  rw [mul_one] at htv₁
  set y := a₂ * (r * a₁) with hy
  have hyL : y ∈ L := L.mul_mem ha₂L (L.mul_mem hrL ha₁L)
  have hyM : y ∈ M := H.le hyL
  have hyact : ∀ w, H.act y w = w := by
    intro w
    obtain ⟨α, β, rfl⟩ := hspan w
    rw [hy, H.act_mul (M.mul_mem hrM ha₁M), H.act_mul ha₁M, htv₁.act_coord ha₁L,
      hr.act_coord hrL, htv₂.act_coord ha₂L]
    have : lam ^ 2 + 1 + lam = 0 := by linear_combination hlam
    have e : α + lam ^ 2 * β + 1 * β + lam * β = α := by linear_combination β * hlam
    rw [e]
  have hyV : y ∈ blockU L := by
    rw [← hO]
    refine NatData.mem_oTwoIn_of_centralizes H.D hyL fun v hv => ?_
    have h1 := H.conj_vec hyM (H.D.ψe v)
    rw [H.vec_ψe hv, hyact] at h1
    rw [h1, H.vec_ψe hv]
  obtain ⟨α, β, hw⟩ := hspan (H.D.ψe y)
  set W : Fin 2 → Fq n := α • e₁ + β • e₂ with hW
  have hyvec : y = H.vec W := by rw [← hw, H.vec_ψe hyV]
  have hr₁ : a₂ * y = r * a₁ := by
    simp only [hy]
    calc a₂ * (a₂ * (r * a₁)) = (a₂ * a₂) * (r * a₁) := by group
      _ = r * a₁ := by rw [ha₂2, one_mul]
  have hr₂ : r * a₂ * y = a₁ := by
    simp only [hy]
    calc r * a₂ * (a₂ * (r * a₁)) = r * (a₂ * a₂) * (r * a₁) := by group
      _ = (r * r) * a₁ := by rw [ha₂2]; group
      _ = a₁ := by rw [hr2, one_mul]
  have hinv2 : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right ha₂2
  have hActW : H.act a₂ W = (α + lam * β) • e₁ + β • e₂ := htv₂.act_coord ha₂L α β
  have hc01 : (r * a₁) * (r * a₁) = H.vec ((lam * β) • e₁) := by
    rw [← hr₁, hyvec, H.sq_mul_vec ha₂M ha₂2]
    congr 1
    rw [hActW]
    linear_combination (norm := module) h3 W
  have hc12 : (a₁ * a₂) * (a₁ * a₂) = H.vec (β • e₁) := by
    have e1 : a₁ * a₂ = r * H.vec (H.act a₂ W) := by
      rw [← hr₂, hyvec, ← H.conj_vec ha₂M, hinv2]
      group
    rw [e1, H.sq_mul_vec hrM hr2]
    congr 1
    rw [hActW, hr.act_coord hrL]
    linear_combination (norm := module) h3 ((α + lam * β) • e₁ + β • e₂)
  have htor : h * ((r * a₁) * (r * a₁)) * h⁻¹ = (a₁ * a₂) * (a₁ * a₂) := by
    calc h * ((r * a₁) * (r * a₁)) * h⁻¹
        = (h * r * h⁻¹) * (h * a₁ * h⁻¹) * ((h * r * h⁻¹) * (h * a₁ * h⁻¹)) := by group
      _ = (a₁ * a₂) * (a₁ * a₂) := rfl
  rw [hc01, hc12, H.conj_vec hhM, H.act_smul_L hhL, hh1] at htor
  have hinj := H.vec_injective htor.symm
  have hβ : β • e₁ = (lam * β * lam) • e₁ := by
    rw [hinj, smul_smul]
  have hβ' : (β - lam * β * lam) • e₁ = 0 := by rw [sub_smul, hβ, sub_self]
  have hβ'' : β - lam * β * lam = 0 := (smul_eq_zero.1 hβ').resolve_right he₁
  have hlb : lam * β = 0 := by linear_combination hβ'' + β * hlam - β * h2
  have hβ0 : β = 0 := (mul_eq_zero.1 hlb).resolve_left hlam0
  have hone : (r * a₁) * (r * a₁) = 1 := by
    rw [hc01, hβ0, mul_zero, zero_smul, H.vec_zero]
  have ha₀inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have ha₁inv : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right ha₁2
  have hX : (r * a₁)⁻¹ = r * a₁ := inv_eq_of_mul_eq_one_right hone
  rw [mul_inv_rev, ha₀inv, ha₁inv] at hX
  exact hX.symm

end CFSG.CGT.PushingUpLit.T2KR.P613
