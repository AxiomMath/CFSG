module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductCommon
public import CFSG.LocalAnalysis.EvenBN.Sp4.ProductModelGen
public import CFSG.LocalAnalysis.EvenBN.Sp4.ProductModelRadical
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProduct

open Subgroup

section RootTrick

variable {G : Type*} [Group G]

@[expose] def rtDl (t x : G) : G := x * (t * x * t⁻¹)

theorem rtDl_conj {t g : G} (hg : t * g = g * t) (x : G) :
    rtDl t (g * x * g⁻¹) = g * rtDl t x * g⁻¹ := by
  have hg' : t * g * t⁻¹ = g := mul_inv_eq_iff_eq_mul.2 hg
  unfold rtDl
  calc g * x * g⁻¹ * (t * (g * x * g⁻¹) * t⁻¹)
      = g * x * g⁻¹ * ((t * g * t⁻¹) * (t * x * t⁻¹) * (t * g * t⁻¹)⁻¹) := by group
    _ = g * (x * (t * x * t⁻¹)) * g⁻¹ := by rw [hg']; group

structure RtPair (t : G) (P : Subgroup G) : Prop where
  t_sq : t * t = 1
  comm : ∀ x ∈ P, ∀ y ∈ P, x * (t * y * t⁻¹) = (t * y * t⁻¹) * x
  inf : ∀ x ∈ P, t * x * t⁻¹ ∈ P → x = 1

theorem RtPair.of_subgroups {t : G} {P : Subgroup G} (ht : t * t = 1)
    (hc : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hi : P ⊓ P.map (MulAut.conj t).toMonoidHom = ⊥) : RtPair t P := by
  refine ⟨ht, fun x hx y hy => ?_, fun x hx hx' => ?_⟩
  · have h1 := commutator_eq_bot_iff_le_centralizer.1 hc hx
    have h2 : t * y * t⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom := ⟨y, hy, rfl⟩
    exact (mem_centralizer_iff.1 h1 _ h2).symm
  · have h1 : x ∈ P.map (MulAut.conj t).toMonoidHom := by
      refine ⟨t * x * t⁻¹, hx', ?_⟩
      show t * (t * x * t⁻¹) * t⁻¹ = x
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [ht]; group
    have h2 : x ∈ P ⊓ P.map (MulAut.conj t).toMonoidHom := mem_inf.2 ⟨hx, h1⟩
    rw [hi] at h2
    exact mem_bot.1 h2

namespace RtPair

variable {t : G} {P : Subgroup G} (hP : RtPair t P)
include hP

theorem dl_mul {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    rtDl t (x * y) = rtDl t x * rtDl t y := by
  unfold rtDl
  have h := hP.comm y hy x hx
  calc x * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
    _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [h]
    _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group

theorem dl_one : rtDl t (1 : G) = 1 := by simp [rtDl]

theorem dl_inv {x : G} (hx : x ∈ P) : rtDl t x⁻¹ = (rtDl t x)⁻¹ := by
  have h := hP.dl_mul hx (inv_mem hx)
  rw [mul_inv_cancel, hP.dl_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem dl_inj {x y : G} (hx : x ∈ P) (hy : y ∈ P) (h : rtDl t x = rtDl t y) : x = y := by
  have hz : y⁻¹ * x ∈ P := mul_mem (inv_mem hy) hx
  have e : y⁻¹ * x = t * (y * x⁻¹) * t⁻¹ := by
    unfold rtDl at h
    calc y⁻¹ * x = y⁻¹ * (x * (t * x * t⁻¹)) * (t * x * t⁻¹)⁻¹ := by group
      _ = y⁻¹ * (y * (t * y * t⁻¹)) * (t * x * t⁻¹)⁻¹ := by rw [h]
      _ = t * (y * x⁻¹) * t⁻¹ := by group
  have e2 : t * (y⁻¹ * x) * t⁻¹ = y * x⁻¹ := by
    calc t * (y⁻¹ * x) * t⁻¹ = t * (t * (y * x⁻¹) * t⁻¹) * t⁻¹ := by rw [← e]
      _ = (t * t) * (y * x⁻¹) * (t * t)⁻¹ := by group
      _ = y * x⁻¹ := by rw [hP.t_sq]; group
  have h1 : y⁻¹ * x = 1 := hP.inf _ hz (by rw [e2]; exact mul_mem hy (inv_mem hx))
  exact (inv_mul_eq_one.1 h1).symm

theorem conj_dl {p x : G} (hp : p ∈ P) (hx : x ∈ P) :
    rtDl t p * x * (rtDl t p)⁻¹ = p * x * p⁻¹ := by
  unfold rtDl
  have hc : (t * p * t⁻¹) * x = x * (t * p * t⁻¹) := (hP.comm x hx p hp).symm
  calc p * (t * p * t⁻¹) * x * (p * (t * p * t⁻¹))⁻¹
      = p * ((t * p * t⁻¹) * x * (t * p * t⁻¹)⁻¹) * p⁻¹ := by group
    _ = p * x * p⁻¹ := by rw [hc]; group

theorem dl_comm {x : G} (hx : x ∈ P) : t * rtDl t x = rtDl t x * t := by
  unfold rtDl
  have hc := hP.comm x hx x hx
  have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [hP.t_sq]; group
  calc t * (x * (t * x * t⁻¹)) = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) * t := by group
    _ = (t * x * t⁻¹) * x * t := by rw [e]
    _ = (x * (t * x * t⁻¹)) * t := by rw [hc]

end RtPair

def rtDelta {t : G} {P : Subgroup G} (hP : RtPair t P) : P →* G :=
  MonoidHom.mk' (fun x => rtDl t (x : G)) fun x y => hP.dl_mul x.2 y.2

theorem rt_gen {t r : G} {P Q B : Subgroup G} (hP : RtPair t P) (htr : t * r = r * t)
    (hrP : ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hQP : Q ≤ P)
    (hB : ∀ u ∈ B, ∃ x ∈ Q, rtDl t x = u) {x : G} (hx : x ∈ P)
    (hxB : rtDl t x ∈ B ⊔ B.map (MulAut.conj r).toMonoidHom) :
    x ∈ Q ⊔ Q.map (MulAut.conj r).toMonoidHom := by
  set H := Q ⊔ Q.map (MulAut.conj r).toMonoidHom
  set D : Subgroup G := (H.subgroupOf P).map (rtDelta hP)
  have hmem : ∀ z : G, z ∈ D ↔ ∃ y : G, y ∈ P ∧ y ∈ H ∧ rtDl t y = z := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, y.2, hy, rfl⟩
    · rintro ⟨y, hyP, hyH, rfl⟩
      exact ⟨⟨y, hyP⟩, hyH, rfl⟩
  have hBD : B ≤ D := by
    intro u hu
    obtain ⟨y, hyQ, rfl⟩ := hB u hu
    exact (hmem _).2 ⟨y, hQP hyQ, mem_sup_left hyQ, rfl⟩
  have hcBD : B.map (MulAut.conj r).toMonoidHom ≤ D := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨y, hyQ, rfl⟩ := hB u hu
    refine (hmem _).2 ⟨r * y * r⁻¹, hrP y (hQP hyQ), mem_sup_right ⟨y, hyQ, rfl⟩, ?_⟩
    exact rtDl_conj htr y
  obtain ⟨y, hyP, hyH, hy⟩ := (hmem _).1 (sup_le hBD hcBD hxB)
  rw [← hP.dl_inj hyP hx hy]
  exact hyH

def rtPre {t : G} {P : Subgroup G} (hP : RtPair t P) (R A : Subgroup G) (hRP : R ≤ P) :
    Subgroup G where
  carrier := {x | x ∈ R ∧ rtDl t x ∈ A}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [hP.dl_mul (hRP hx.1) (hRP hy.1)]; exact mul_mem hx.2 hy.2⟩
  one_mem' := ⟨one_mem R, by rw [hP.dl_one]; exact one_mem A⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    rw [hP.dl_inv (hRP hx.1)]; exact inv_mem hx.2⟩

theorem rt_cox {r₁ r₂ : G} (h₁ : r₁ * r₁ = 1) (h₂ : r₂ * r₂ = 1) (h4 : (r₁ * r₂) ^ 4 = 1) :
    r₁ * r₂ * r₁ = (r₂ * r₁ * r₂) * r₁ * r₂ := by
  have i₁ : r₁⁻¹ = r₁ := inv_eq_of_mul_eq_one_right h₁
  have i₂ : r₂⁻¹ = r₂ := inv_eq_of_mul_eq_one_right h₂
  have h5 : (r₁ * r₂ * r₁ * r₂) * (r₁ * r₂ * r₁ * r₂) = 1 := by
    rw [← h4]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h6 : r₁ * r₂ * r₁ * r₂ = (r₁ * r₂ * r₁ * r₂)⁻¹ := eq_inv_of_mul_eq_one_left h5
  have h7 : (r₁ * r₂ * r₁ * r₂)⁻¹ = r₂ * r₁ * r₂ * r₁ := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, i₁, i₂]; group
  rw [h7] at h6
  calc r₁ * r₂ * r₁ = (r₁ * r₂ * r₁ * r₂) * r₂ := by
        rw [mul_assoc (r₁ * r₂ * r₁) r₂ r₂, h₂, mul_one]
    _ = (r₂ * r₁ * r₂ * r₁) * r₂ := by rw [h6]
    _ = (r₂ * r₁ * r₂) * r₁ * r₂ := by group

theorem rt_conj_comm {m p q : G} (h : p * q = q * p) :
    m * p * m⁻¹ * (m * q * m⁻¹) = m * q * m⁻¹ * (m * p * m⁻¹) := by
  calc m * p * m⁻¹ * (m * q * m⁻¹) = m * (p * q) * m⁻¹ := by group
    _ = m * (q * p) * m⁻¹ := by rw [h]
    _ = m * q * m⁻¹ * (m * p * m⁻¹) := by group

structure RtRoot (t r₁ r₂ : G) (P₁ P₂ R U A : Subgroup G) (a : G) : Prop where
  pair₁ : RtPair t P₁
  pair₂ : RtPair t P₂
  r₁_sq : r₁ * r₁ = 1
  r₂_sq : r₂ * r₂ = 1
  tr₁ : t * r₁ = r₁ * t
  tr₂ : t * r₂ = r₂ * t
  pow4 : (r₁ * r₂) ^ 4 = 1
  R_le₁ : R ≤ P₁
  R_le₂ : R ≤ P₂
  R_dl : ∀ x ∈ R, rtDl t x ∈ U
  U_dl : ∀ u ∈ U, ∃ x ∈ R, rtDl t x = u
  s₁ : ∃ s ∈ P₁, rtDl t s = r₁
  s₂ : ∃ s ∈ P₂, rtDl t s = r₂
  gen₁ : ∀ x ∈ P₁, rtDl t x ∈ U ⊔ U.map (MulAut.conj r₁).toMonoidHom
  gen₂ : ∀ x ∈ P₂, rtDl t x ∈ U ⊔ U.map (MulAut.conj r₂).toMonoidHom
  A_le : A ≤ U
  A_r₂ : ∀ x ∈ A, r₂ * x * r₂⁻¹ ∈ A
  U_le : U ≤ A ⊔ A.map (MulAut.conj r₁).toMonoidHom
  a_mem : a ∈ A
  a_mem' : a ∈ A.map (MulAut.conj (r₂ * r₁)).toMonoidHom
  y_mem₁ : a * r₁ * a⁻¹ ∈ A.map (MulAut.conj r₁).toMonoidHom
  y_mem₂ : a * r₁ * a⁻¹ ∈ A.map (MulAut.conj (r₁ * r₂ * r₁)).toMonoidHom

namespace RtRoot

def W {t r₁ r₂ : G} {P₁ P₂ R U A : Subgroup G} {a : G}
    (d : RtRoot t r₁ r₂ P₁ P₂ R U A a) : Subgroup G := rtPre d.pair₁ R A d.R_le₁

variable {t r₁ r₂ : G} {P₁ P₂ R U A : Subgroup G} {a : G}
  (d : RtRoot t r₁ r₂ P₁ P₂ R U A a)
include d

theorem r₂_inv : r₂⁻¹ = r₂ := inv_eq_of_mul_eq_one_right d.r₂_sq

theorem norm₁ {x : G} (hx : x ∈ P₁) : r₁ * x * r₁⁻¹ ∈ P₁ := by
  obtain ⟨s, hs, hsr⟩ := d.s₁
  rw [← hsr, d.pair₁.conj_dl hs hx]
  exact mul_mem (mul_mem hs hx) (inv_mem hs)

theorem norm₂ {x : G} (hx : x ∈ P₂) : r₂ * x * r₂⁻¹ ∈ P₂ := by
  obtain ⟨s, hs, hsr⟩ := d.s₂
  rw [← hsr, d.pair₂.conj_dl hs hx]
  exact mul_mem (mul_mem hs hx) (inv_mem hs)

theorem conj₁ {s : G} (hs : s ∈ P₁) (hsr : rtDl t s = r₁) {x : G} (hx : x ∈ P₁) :
    r₁ * x * r₁⁻¹ = s * x * s⁻¹ := by
  rw [← hsr]
  exact d.pair₁.conj_dl hs hx

theorem mem_R₁ {x : G} (hx : x ∈ P₁) (hxU : rtDl t x ∈ U) : x ∈ R := by
  obtain ⟨y, hyR, hy⟩ := d.U_dl _ hxU
  exact (d.pair₁.dl_inj (d.R_le₁ hyR) hx hy) ▸ hyR

theorem mem_R₂ {x : G} (hx : x ∈ P₂) (hxU : rtDl t x ∈ U) : x ∈ R := by
  obtain ⟨y, hyR, hy⟩ := d.U_dl _ hxU
  exact (d.pair₂.dl_inj (d.R_le₂ hyR) hx hy) ▸ hyR

theorem W_le_R : d.W ≤ R := fun _ hx => hx.1

theorem mem_W_of₁ {x : G} (hx : x ∈ P₁) (hxA : rtDl t x ∈ A) : x ∈ d.W :=
  ⟨d.mem_R₁ hx (d.A_le hxA), hxA⟩

theorem mem_W_of₂ {x : G} (hx : x ∈ P₂) (hxA : rtDl t x ∈ A) : x ∈ d.W :=
  ⟨d.mem_R₂ hx (d.A_le hxA), hxA⟩

theorem exists_W {u : G} (hu : u ∈ A) : ∃ x ∈ d.W, rtDl t x = u := by
  obtain ⟨x, hxR, hx⟩ := d.U_dl u (d.A_le hu)
  exact ⟨x, ⟨hxR, hx ▸ hu⟩, hx⟩

theorem conj₂_W {x : G} (hx : x ∈ d.W) : r₂ * x * r₂⁻¹ ∈ d.W := by
  have hxP : x ∈ P₂ := d.R_le₂ hx.1
  refine d.mem_W_of₂ (d.norm₂ hxP) ?_
  rw [rtDl_conj d.tr₂]
  exact d.A_r₂ _ hx.2

theorem R_le_sup {x : G} (hx : x ∈ R) : x ∈ d.W ⊔ d.W.map (MulAut.conj r₁).toMonoidHom :=
  rt_gen d.pair₁ d.tr₁ (fun y hy => d.norm₁ hy) (d.W_le_R.trans d.R_le₁)
    (fun u hu => d.exists_W hu) (d.R_le₁ hx) (d.U_le (d.R_dl x hx))

theorem P₁_le_sup {x : G} (hx : x ∈ P₁) : x ∈ R ⊔ R.map (MulAut.conj r₁).toMonoidHom :=
  rt_gen d.pair₁ d.tr₁ (fun y hy => d.norm₁ hy) d.R_le₁ d.U_dl hx (d.gen₁ x hx)

theorem P₂_le_sup {x : G} (hx : x ∈ P₂) : x ∈ R ⊔ R.map (MulAut.conj r₂).toMonoidHom :=
  rt_gen d.pair₂ d.tr₂ (fun y hy => d.norm₂ hy) d.R_le₂ d.U_dl hx (d.gen₂ x hx)

theorem key {s ã : G} (hs : s ∈ P₁) (hsr : rtDl t s = r₁) (hã : ã ∈ d.W)
    (hãa : rtDl t ã = a) :
    (∃ w ∈ d.W, ã * s * ã⁻¹ = (r₁ * r₂ * r₁) * w * (r₁ * r₂ * r₁)⁻¹) ∧
      ∃ w ∈ d.W, ã = (r₂ * r₁) * w * (r₂ * r₁)⁻¹ := by
  have hãP : ã ∈ P₁ := d.R_le₁ hã.1
  have hy₁P : ã * s * ã⁻¹ ∈ P₁ := mul_mem (mul_mem hãP hs) (inv_mem hãP)
  have hy₁δ : rtDl t (ã * s * ã⁻¹) = a * r₁ * a⁻¹ := by
    rw [d.pair₁.dl_mul (mul_mem hãP hs) (inv_mem hãP), d.pair₁.dl_mul hãP hs,
      d.pair₁.dl_inv hãP, hãa, hsr]
  refine ⟨?_, ?_⟩
  · obtain ⟨u₂, hu₂A, hu₂⟩ := d.y_mem₂
    obtain ⟨u₁, hu₁A, hu₁⟩ := d.y_mem₁
    change (r₁ * r₂ * r₁) * u₂ * (r₁ * r₂ * r₁)⁻¹ = a * r₁ * a⁻¹ at hu₂
    change r₁ * u₁ * r₁⁻¹ = a * r₁ * a⁻¹ at hu₁
    have e₂ : u₂ = (r₁ * r₂ * r₁)⁻¹ * (a * r₁ * a⁻¹) * (r₁ * r₂ * r₁) := by
      rw [← hu₂]; group
    obtain ⟨w₀, hw₀, hw₀δ⟩ := d.exists_W hu₂A
    have hw₁P : r₁ * w₀ * r₁⁻¹ ∈ P₁ := d.norm₁ (d.R_le₁ hw₀.1)
    have hw₁δ : rtDl t (r₁ * w₀ * r₁⁻¹) = r₂⁻¹ * u₁ * r₂ := by
      rw [rtDl_conj d.tr₁, hw₀δ, e₂, ← hu₁]; group
    have hw₁A : rtDl t (r₁ * w₀ * r₁⁻¹) ∈ A := by
      rw [hw₁δ, d.r₂_inv]
      have := d.A_r₂ u₁ hu₁A
      rwa [d.r₂_inv] at this
    have hw₁W : r₁ * w₀ * r₁⁻¹ ∈ d.W := d.mem_W_of₁ hw₁P hw₁A
    have hw₂W := d.conj₂_W hw₁W
    have hw₃P : r₁ * (r₂ * (r₁ * w₀ * r₁⁻¹) * r₂⁻¹) * r₁⁻¹ ∈ P₁ :=
      d.norm₁ (d.R_le₁ hw₂W.1)
    have hw₃δ : rtDl t (r₁ * (r₂ * (r₁ * w₀ * r₁⁻¹) * r₂⁻¹) * r₁⁻¹) = a * r₁ * a⁻¹ := by
      rw [rtDl_conj d.tr₁, rtDl_conj d.tr₂, rtDl_conj d.tr₁, hw₀δ, ← hu₂]; group
    have hy : ã * s * ã⁻¹ = r₁ * (r₂ * (r₁ * w₀ * r₁⁻¹) * r₂⁻¹) * r₁⁻¹ :=
      d.pair₁.dl_inj hy₁P hw₃P (hy₁δ.trans hw₃δ.symm)
    exact ⟨w₀, hw₀, by rw [hy]; group⟩
  · obtain ⟨a₁, ha₁A, ha₁⟩ := d.a_mem'
    change (r₂ * r₁) * a₁ * (r₂ * r₁)⁻¹ = a at ha₁
    obtain ⟨w₃, hw₃, hw₃δ⟩ := d.exists_W ha₁A
    have hw'P : r₁ * w₃ * r₁⁻¹ ∈ P₁ := d.norm₁ (d.R_le₁ hw₃.1)
    have hw'δ : rtDl t (r₁ * w₃ * r₁⁻¹) = r₂⁻¹ * a * r₂ := by
      rw [rtDl_conj d.tr₁, hw₃δ, ← ha₁]; group
    have hw'A : rtDl t (r₁ * w₃ * r₁⁻¹) ∈ A := by
      rw [hw'δ, d.r₂_inv]
      have := d.A_r₂ a d.a_mem
      rwa [d.r₂_inv] at this
    have hw'W : r₁ * w₃ * r₁⁻¹ ∈ d.W := d.mem_W_of₁ hw'P hw'A
    have hw''W := d.conj₂_W hw'W
    have hw''δ : rtDl t (r₂ * (r₁ * w₃ * r₁⁻¹) * r₂⁻¹) = a := by
      rw [rtDl_conj d.tr₂, rtDl_conj d.tr₁, hw₃δ, ← ha₁]; group
    have hw''eq : r₂ * (r₁ * w₃ * r₁⁻¹) * r₂⁻¹ = ã :=
      d.pair₁.dl_inj (d.R_le₁ hw''W.1) hãP (hw''δ.trans hãa.symm)
    exact ⟨w₃, hw₃, by rw [← hw''eq]; group⟩

theorem s_comm {s ã : G} (hs : s ∈ P₁) (hsr : rtDl t s = r₁) (hã : ã ∈ d.W)
    (hãa : rtDl t ã = a) {w : G} (hw : w ∈ d.W) :
    s * ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) =
      ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) * s := by
  obtain ⟨⟨w₀, hw₀, hy₁⟩, ⟨w₃, hw₃, hã_eq⟩⟩ := d.key hs hsr hã hãa
  have hwP : w ∈ P₁ := d.R_le₁ hw.1
  have hcom1 : ã * ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) =
      ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) * ã := by
    rw [hã_eq]
    exact rt_conj_comm (d.pair₁.comm w₃ (d.R_le₁ hw₃.1) w hwP)
  have hcom2 : (ã * s * ã⁻¹) * ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) =
      ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) * (ã * s * ã⁻¹) := by
    have hcox := rt_cox d.r₁_sq d.r₂_sq d.pow4
    have hI2 : r₂ * r₁ = (r₂ * r₁ * r₂) * r₂ := by
      rw [mul_assoc (r₂ * r₁) r₂ r₂, d.r₂_sq, mul_one]
    have hw'W := d.conj₂_W hw
    have hw₀'W := d.conj₂_W hw₀
    have hp : r₁ * (r₂ * w₀ * r₂⁻¹) * r₁⁻¹ ∈ P₁ := d.norm₁ (d.R_le₁ hw₀'W.1)
    have hc := d.pair₁.comm _ hp _ (d.R_le₁ hw'W.1)
    have hy_eq : ã * s * ã⁻¹ =
        (r₂ * r₁ * r₂) * (r₁ * (r₂ * w₀ * r₂⁻¹) * r₁⁻¹) * (r₂ * r₁ * r₂)⁻¹ := by
      rw [hy₁, hcox]; group
    have hv_eq : (r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹ =
        (r₂ * r₁ * r₂) * (t * (r₂ * w * r₂⁻¹) * t⁻¹) * (r₂ * r₁ * r₂)⁻¹ := by
      have e : t * (r₂ * w * r₂⁻¹) * t⁻¹ = r₂ * (t * w * t⁻¹) * r₂⁻¹ := by
        have hr₂' : t * r₂ * t⁻¹ = r₂ := mul_inv_eq_iff_eq_mul.2 d.tr₂
        calc t * (r₂ * w * r₂⁻¹) * t⁻¹
            = (t * r₂ * t⁻¹) * (t * w * t⁻¹) * (t * r₂ * t⁻¹)⁻¹ := by group
          _ = r₂ * (t * w * t⁻¹) * r₂⁻¹ := by rw [hr₂']
      rw [e]
      calc (r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹
          = ((r₂ * r₁ * r₂) * r₂) * (t * w * t⁻¹) * ((r₂ * r₁ * r₂) * r₂)⁻¹ := by rw [← hI2]
        _ = _ := by group
    rw [hy_eq, hv_eq]
    exact rt_conj_comm hc
  have hs_eq : s = ã⁻¹ * (ã * s * ã⁻¹) * ã := by group
  have c1 : Commute ã ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) := hcom1
  have c2 : Commute (ã * s * ã⁻¹) ((r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹) := hcom2
  have c3 := (c1.inv_left.mul_left c2).mul_left c1
  rw [← hs_eq] at c3
  exact c3.eq

theorem comm_cross : ⁅P₁, P₂.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  obtain ⟨s, hs, hsr⟩ := d.s₁
  obtain ⟨ã, hã, hãa⟩ := d.exists_W d.a_mem
  rw [commutator_eq_bot_iff_le_centralizer]
  have h10 : ∀ x ∈ R, s * (t * (r₂ * x * r₂⁻¹) * t⁻¹) = (t * (r₂ * x * r₂⁻¹) * t⁻¹) * s := by
    intro x hx
    let Z : Subgroup G := (centralizer ({s} : Set G)).comap (MulAut.conj (t * r₂)).toMonoidHom
    have hmemZ : ∀ z : G, z ∈ Z ↔
        (t * (r₂ * z * r₂⁻¹) * t⁻¹) * s = s * (t * (r₂ * z * r₂⁻¹) * t⁻¹) := by
      intro z
      have e : (t * r₂) * z * (t * r₂)⁻¹ = t * (r₂ * z * r₂⁻¹) * t⁻¹ := by group
      rw [Subgroup.mem_comap, mem_centralizer_singleton_iff]
      change (t * r₂) * z * (t * r₂)⁻¹ * s = s * ((t * r₂) * z * (t * r₂)⁻¹) ↔ _
      rw [e]
    have hWZ : d.W ≤ Z := by
      intro w hw
      have hw' := d.conj₂_W hw
      exact (hmemZ w).2 (d.pair₁.comm s hs _ (d.R_le₁ hw'.1)).symm
    have hcWZ : d.W.map (MulAut.conj r₁).toMonoidHom ≤ Z := by
      rintro _ ⟨w, hw, rfl⟩
      have e : t * (r₂ * (r₁ * w * r₁⁻¹) * r₂⁻¹) * t⁻¹ =
          (r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹ := by
        have hr₁' : t * r₁ * t⁻¹ = r₁ := mul_inv_eq_iff_eq_mul.2 d.tr₁
        have hr₂' : t * r₂ * t⁻¹ = r₂ := mul_inv_eq_iff_eq_mul.2 d.tr₂
        calc t * (r₂ * (r₁ * w * r₁⁻¹) * r₂⁻¹) * t⁻¹
            = (t * r₂ * t⁻¹) * ((t * r₁ * t⁻¹) * (t * w * t⁻¹) * (t * r₁ * t⁻¹)⁻¹) *
                (t * r₂ * t⁻¹)⁻¹ := by group
          _ = r₂ * (r₁ * (t * w * t⁻¹) * r₁⁻¹) * r₂⁻¹ := by rw [hr₁', hr₂']
          _ = (r₂ * r₁) * (t * w * t⁻¹) * (r₂ * r₁)⁻¹ := by group
      refine (hmemZ _).2 ?_
      change t * (r₂ * (r₁ * w * r₁⁻¹) * r₂⁻¹) * t⁻¹ * s =
        s * (t * (r₂ * (r₁ * w * r₁⁻¹) * r₂⁻¹) * t⁻¹)
      rw [e]
      exact (d.s_comm hs hsr hã hãa hw).symm
    have hRZ : R ≤ Z := fun x hx => sup_le hWZ hcWZ (d.R_le_sup hx)
    exact ((hmemZ x).1 (hRZ hx)).symm
  intro x hx
  have hx' := d.P₁_le_sup hx
  have hRc : R ≤ centralizer ((P₂.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    intro y hy
    rw [mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact (d.pair₂.comm y (d.R_le₂ hy) z hz).symm
  have hcRc : R.map (MulAut.conj r₁).toMonoidHom ≤
      centralizer ((P₂.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have e := d.conj₁ hs hsr (d.R_le₁ hx₀)
    change (t * z * t⁻¹) * (r₁ * x₀ * r₁⁻¹) = (r₁ * x₀ * r₁⁻¹) * (t * z * t⁻¹)
    rw [e]
    have he : s * x₀ * s⁻¹ ∈ P₁ := mul_mem (mul_mem hs (d.R_le₁ hx₀)) (inv_mem hs)
    let Z₄ : Subgroup G :=
      (centralizer ({s * x₀ * s⁻¹} : Set G)).comap (MulAut.conj t).toMonoidHom
    have hmem4 : ∀ z : G, z ∈ Z₄ ↔
        (t * z * t⁻¹) * (s * x₀ * s⁻¹) = (s * x₀ * s⁻¹) * (t * z * t⁻¹) := by
      intro z
      rw [Subgroup.mem_comap, mem_centralizer_singleton_iff]
      rfl
    have hR4 : R ≤ Z₄ := fun z hz => (hmem4 z).2 (d.pair₁.comm _ he z (d.R_le₁ hz)).symm
    have hR4' : R.map (MulAut.conj r₂).toMonoidHom ≤ Z₄ := by
      rintro _ ⟨x', hx', rfl⟩
      refine (hmem4 _).2 ?_
      have h1 : Commute s (t * (r₂ * x' * r₂⁻¹) * t⁻¹) := h10 x' hx'
      have h2 : Commute x₀ (t * (r₂ * x' * r₂⁻¹) * t⁻¹) :=
        d.pair₂.comm x₀ (d.R_le₂ hx₀) (r₂ * x' * r₂⁻¹) (d.norm₂ (d.R_le₂ hx'))
      exact ((h1.mul_left h2).mul_left h1.inv_left).eq.symm
    exact (hmem4 z).1 (sup_le hR4 hR4' (d.P₂_le_sup hz))
  exact sup_le hRc hcRc hx'

end RtRoot

theorem rt_card_inf_ge [Finite G] {t : G} {P S : Subgroup G} (hP : RtPair t P)
    (hSP : S ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom) (hS2 : IsPGroup 2 S) {N : ℕ}
    (hS : Nat.card S = N * N)
    (hbound : ∀ T : Subgroup G, T ≤ P → IsPGroup 2 T → Nat.card T ≤ N) :
    N ≤ Nat.card (S ⊓ P : Subgroup G) := by
  classical
  let ψ : P × P →* G := MonoidHom.mk' (fun xy => (xy.1 : G) * (t * (xy.2 : G) * t⁻¹)) (by
    intro xy xy'
    have h := hP.comm xy'.1 xy'.1.2 xy.2 xy.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (xy.1 : G) * xy'.1 * (t * ((xy.2 : G) * xy'.2) * t⁻¹)
        = (xy.1 : G) * ((xy'.1 : G) * (t * (xy.2 : G) * t⁻¹)) * (t * (xy'.2 : G) * t⁻¹) := by
          group
      _ = (xy.1 : G) * ((t * (xy.2 : G) * t⁻¹) * (xy'.1 : G)) * (t * (xy'.2 : G) * t⁻¹) := by
          rw [h]
      _ = ((xy.1 : G) * (t * (xy.2 : G) * t⁻¹)) * ((xy'.1 : G) * (t * (xy'.2 : G) * t⁻¹)) := by
          group)
  have hψ : ∀ xy : P × P, ψ xy = (xy.1 : G) * (t * (xy.2 : G) * t⁻¹) := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    rw [hψ] at hxy
    simp only at hxy
    have h1 : (x : G) = (t * (y : G) * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have h2 : t * (x : G) * t⁻¹ = (y : G)⁻¹ := by
      rw [h1]
      calc t * (t * (y : G) * t⁻¹)⁻¹ * t⁻¹ = (t * t) * (y : G)⁻¹ * (t * t)⁻¹ := by group
        _ = (y : G)⁻¹ := by rw [hP.t_sq]; group
    have hx1 : (x : G) = 1 := hP.inf (x : G) x.2 (by rw [h2]; exact inv_mem y.2)
    have hy1 : (y : G) = 1 := by
      rw [hx1, one_mul] at hxy
      calc (y : G) = t⁻¹ * (t * (y : G) * t⁻¹) * t := by group
        _ = 1 := by rw [hxy]; group
    exact Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)
  have hcomm : ∀ a ∈ P, ∀ b ∈ P.map (MulAut.conj t).toMonoidHom, a * b = b * a := by
    rintro a ha _ ⟨y, hy, rfl⟩
    exact hP.comm a ha y hy
  have hrange : S ≤ ψ.range := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := diag_exists_mul_of_mem_sup hcomm (hSP hg)
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨(⟨a, ha⟩, ⟨y, hy⟩), rfl⟩
  let S' : Subgroup (P × P) := S.comap ψ
  have hS'card : Nat.card S' = N * N := by
    have h1 : S'.map ψ = S := by
      rw [Subgroup.map_comap_eq, inf_of_le_right hrange]
    calc Nat.card S' = Nat.card (S'.map ψ) := (Subgroup.card_map_of_injective hψinj).symm
      _ = Nat.card S := by rw [h1]
      _ = N * N := hS
  have hS'2 : IsPGroup 2 S' := hS2.comap_of_injective ψ hψinj
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, mul_zero] at hS
      exact absurd hS Nat.card_pos.ne'
    · exact h0
  set A : Subgroup P := S'.map (MonoidHom.fst P P)
  set B : Subgroup P := S'.map (MonoidHom.snd P P)
  have hAN : Nat.card A ≤ N := by
    have h2 : IsPGroup 2 (A.map P.subtype) := (hS'2.map (MonoidHom.fst P P)).map P.subtype
    have h3 := hbound _ (Subgroup.map_subtype_le A) h2
    rwa [Subgroup.card_map_of_injective P.subtype_injective] at h3
  have hBN : Nat.card B ≤ N := by
    have h2 : IsPGroup 2 (B.map P.subtype) := (hS'2.map (MonoidHom.snd P P)).map P.subtype
    have h3 := hbound _ (Subgroup.map_subtype_le B) h2
    rwa [Subgroup.card_map_of_injective P.subtype_injective] at h3
  have hS'le : S' ≤ A.prod B := fun z hz =>
    Subgroup.mem_prod.2 ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  have hprod : Nat.card (A.prod B : Subgroup (P × P)) = Nat.card A * Nat.card B := by
    rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]
  have hle := Subgroup.card_le_of_le hS'le
  rw [hS'card, hprod] at hle
  have hAeq : Nat.card A = N := by
    refine le_antisymm hAN ?_
    refine Nat.le_of_mul_le_mul_right (c := N) ?_ hNpos
    exact hle.trans (Nat.mul_le_mul_left _ hBN)
  have hBeq : Nat.card B = N := by
    refine le_antisymm hBN ?_
    refine Nat.le_of_mul_le_mul_left (a := N) ?_ hNpos
    calc N * N ≤ Nat.card A * Nat.card B := hle
      _ = N * Nat.card B := by rw [hAeq]
  have hS'eq : S' = A.prod B :=
    Subgroup.eq_of_le_of_card_ge hS'le (by rw [hS'card, hprod, hAeq, hBeq])
  have hsub : A.map P.subtype ≤ S ⊓ P := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_inf.2 ⟨?_, a.2⟩
    have h1 : ((a, (1 : P)) : P × P) ∈ A.prod B :=
      Subgroup.mem_prod.2 ⟨ha, one_mem B⟩
    rw [← hS'eq] at h1
    have h2 : ψ (a, 1) ∈ S := h1
    rw [hψ] at h2
    simpa using h2
  calc N = Nat.card A := hAeq.symm
    _ = Nat.card (A.map P.subtype) := (Subgroup.card_map_of_injective P.subtype_injective).symm
    _ ≤ Nat.card (S ⊓ P : Subgroup G) := Subgroup.card_le_of_le hsub

theorem rt_card_le [Finite G] {t : G} {P L : Subgroup G} (hP : RtPair t P)
    (hL : ∀ x ∈ P, rtDl t x ∈ L) {N m : ℕ} (hN : 0 < N) (hLcard : Nat.card L = N * m)
    (hm : ¬ 2 ∣ m) : ∀ T : Subgroup G, T ≤ P → IsPGroup 2 T → Nat.card T ≤ N := by
  intro T hTP hT2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (rtDelta hP) := fun x y h =>
    Subtype.ext (hP.dl_inj x.2 y.2 h)
  let T' : Subgroup G := (T.subgroupOf P).map (rtDelta hP)
  have hTP' : IsPGroup 2 (T.subgroupOf P) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm
  have hT'2 : IsPGroup 2 T' := hTP'.map (rtDelta hP)
  have hT'card : Nat.card T' = Nat.card T := by
    rw [Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv
  have hT'L : T' ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact hL y y.2
  have hdvd : Nat.card T' ∣ Nat.card L := Subgroup.card_dvd_of_le hT'L
  obtain ⟨k, hk⟩ := hT'2.exists_card_eq
  rw [hk, hLcard] at hdvd
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
  have h2 : 2 ^ k ∣ N := hcop.dvd_of_dvd_mul_right hdvd
  rw [← hT'card, hk]
  exact Nat.le_of_dvd hN h2

theorem rt_main [Finite G] {t r₁ r₂ : G} {P₁ P₂ S U A C₁ C₂ L₀ : Subgroup G} {a : G}
    {N m : ℕ} (hP₁ : RtPair t P₁) (hP₂ : RtPair t P₂)
    (hd₁ : ∀ x ∈ P₁, rtDl t x ∈ C₁) (hs₁ : ∀ y ∈ C₁, ∃ x ∈ P₁, rtDl t x = y)
    (hd₂ : ∀ x ∈ P₂, rtDl t x ∈ C₂) (hs₂ : ∀ y ∈ C₂, ∃ x ∈ P₂, rtDl t x = y)
    (hsylow : S ⊓ P₁ = S ⊓ P₂)
    (hSP : S ≤ P₁ ⊔ P₁.map (MulAut.conj t).toMonoidHom)
    (hSτ : ∀ x ∈ S, t * x * t⁻¹ ∈ S) (hSC : ∀ x ∈ S, t * x = x * t → x ∈ U)
    (hS2 : IsPGroup 2 S) (hS : Nat.card S = N * N) (hU : Nat.card U = N)
    (hC₁ : C₁ ≤ L₀) (hL₀ : Nat.card L₀ = N * m) (hm : ¬ 2 ∣ m)
    (hr₁C : r₁ ∈ C₁) (hr₂C : r₂ ∈ C₂) (hr₁ : r₁ * r₁ = 1) (hr₂ : r₂ * r₂ = 1)
    (htr₁ : t * r₁ = r₁ * t) (htr₂ : t * r₂ = r₂ * t) (hpow4 : (r₁ * r₂) ^ 4 = 1)
    (hgen₁ : C₁ ≤ U ⊔ U.map (MulAut.conj r₁).toMonoidHom)
    (hgen₂ : C₂ ≤ U ⊔ U.map (MulAut.conj r₂).toMonoidHom)
    (hAU : A ≤ U) (hAr₂ : ∀ x ∈ A, r₂ * x * r₂⁻¹ ∈ A)
    (hUA : U ≤ A ⊔ A.map (MulAut.conj r₁).toMonoidHom)
    (ha : a ∈ A) (ha' : a ∈ A.map (MulAut.conj (r₂ * r₁)).toMonoidHom)
    (hy₁ : a * r₁ * a⁻¹ ∈ A.map (MulAut.conj r₁).toMonoidHom)
    (hy₂ : a * r₁ * a⁻¹ ∈ A.map (MulAut.conj (r₁ * r₂ * r₁)).toMonoidHom) :
    ⁅P₁, P₂.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, mul_zero] at hS
      exact absurd hS Nat.card_pos.ne'
    · exact h0
  have hbound := rt_card_le hP₁ (fun x hx => hC₁ (hd₁ x hx)) hN hL₀ hm
  have hge := rt_card_inf_ge hP₁ hSP hS2 hS hbound
  have hRU : ∀ x ∈ S ⊓ P₁, rtDl t x ∈ U := fun x hx =>
    hSC _ (mul_mem hx.1 (hSτ x hx.1)) (hP₁.dl_comm hx.2)
  have hUdl : ∀ u ∈ U, ∃ x ∈ S ⊓ P₁, rtDl t x = u := by
    have hcard : Nat.card U ≤ Nat.card (S ⊓ P₁ : Subgroup G) := hU ▸ hge
    let f : ↥(S ⊓ P₁) → ↥U := fun x => ⟨rtDl t x, hRU x x.2⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (hP₁.dl_inj x.2.2 y.2.2 (congrArg Subtype.val hxy))
    have hbij := hf.bijective_of_nat_card_le hcard
    intro u hu
    obtain ⟨x, hx⟩ := hbij.2 ⟨u, hu⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  exact RtRoot.comm_cross
    ⟨hP₁, hP₂, hr₁, hr₂, htr₁, htr₂, hpow4, inf_le_right,
      fun x hx => (inf_le_right : S ⊓ P₂ ≤ P₂) (hsylow ▸ hx), hRU, hUdl, hs₁ r₁ hr₁C,
      hs₂ r₂ hr₂C, fun x hx => hgen₁ (hd₁ x hx), fun x hx => hgen₂ (hd₂ x hx), hAU, hAr₂, hUA,
      ha, ha', hy₁, hy₂⟩

theorem rt_comm_swap {t : G} {P Q : Subgroup G} (ht : t * t = 1)
    (h : ⁅Q, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥) :
    ⁅P, Q.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer] at h ⊢
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have h1 := mem_centralizer_iff.1 (h hy) (t * x * t⁻¹) ⟨x, hx, rfl⟩
  have h2 : t * ((t * x * t⁻¹) * y) * t⁻¹ = t * (y * (t * x * t⁻¹)) * t⁻¹ := by rw [h1]
  have e1 : t * ((t * x * t⁻¹) * y) * t⁻¹ = x * (t * y * t⁻¹) := by
    calc t * ((t * x * t⁻¹) * y) * t⁻¹ = ((t * t) * x * (t * t)⁻¹) * (t * y * t⁻¹) := by group
      _ = x * (t * y * t⁻¹) := by rw [ht]; group
  have e2 : t * (y * (t * x * t⁻¹)) * t⁻¹ = (t * y * t⁻¹) * x := by
    calc t * (y * (t * x * t⁻¹)) * t⁻¹ = (t * y * t⁻¹) * ((t * t) * x * (t * t)⁻¹) := by group
      _ = (t * y * t⁻¹) * x := by rw [ht]; group
  rw [e1, e2] at h2
  exact h2.symm

end RootTrick

section Transport

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ]

theorem rt_map_conj (ι : Γ →* G) (H : Subgroup Γ) (g : Γ) :
    (H.map (MulAut.conj g).toMonoidHom).map ι =
      (H.map ι).map (MulAut.conj (ι g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem rt_map_le_sup_conj (ι : Γ →* G) {H₁ H₂ H₃ : Subgroup Γ} {g : Γ}
    (h : H₁ ≤ H₂ ⊔ H₃.map (MulAut.conj g).toMonoidHom) :
    H₁.map ι ≤ H₂.map ι ⊔ (H₃.map ι).map (MulAut.conj (ι g)).toMonoidHom := by
  calc H₁.map ι ≤ (H₂ ⊔ H₃.map (MulAut.conj g).toMonoidHom).map ι := Subgroup.map_mono h
    _ = H₂.map ι ⊔ (H₃.map (MulAut.conj g).toMonoidHom).map ι := Subgroup.map_sup _ _ _
    _ = H₂.map ι ⊔ (H₃.map ι).map (MulAut.conj (ι g)).toMonoidHom := by rw [rt_map_conj]

theorem rt_mem_map_conj_of_mem (ι : Γ →* G) {H : Subgroup Γ} {g x : Γ}
    (h : x ∈ H.map (MulAut.conj g).toMonoidHom) :
    ι x ∈ (H.map ι).map (MulAut.conj (ι g)).toMonoidHom := by
  rw [← rt_map_conj]
  exact Subgroup.mem_map_of_mem ι h

end Transport

open CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rt_weyl_pow_four (i : Axis) : (weylElt K i * weylElt K i.swap) ^ 4 = 1 := by
  cases i
  · exact ProductModel.weylElt_mul_weylElt_pow_four
  · have h := ProductModel.weylElt_mul_weylElt_pow_four (K := K)
    have e : weylElt K Axis.two * weylElt K Axis.one =
        (weylElt K Axis.one * weylElt K Axis.two)⁻¹ := by
      rw [mul_inv_rev, weylElt_inv, weylElt_inv]
    show (weylElt K Axis.two * weylElt K Axis.one) ^ 4 = 1
    rw [e, inv_pow, h, inv_one]

theorem rt_card_antiSp : ∃ m : ℕ, Nat.card (antiSp K) = Nat.card K ^ 4 * m ∧ ¬ 2 ∣ m := by
  refine ⟨(antiUnipotent K).index, ?_, ?_⟩
  · rw [← (card_and_isSylowTwoOf_antiUnipotent (K := K)).1]
    exact (Subgroup.card_mul_index _).symm
  · obtain ⟨-, -, hodd⟩ := (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
    rwa [show ((antiUnipotent K).subgroupOf ⊤).index = (antiUnipotent K).index from
      Subgroup.relIndex_top_right _] at hodd

end Model

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}

theorem cross_aux (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) {Pi Pj : Subgroup G}
    (hPi : RtPair t Pi) (hPj : RtPair t Pj)
    (hdi : ∀ x ∈ Pi, x * (t * x * t⁻¹) ∈ L ⊓ centralizer (𝐔[i] : Set G))
    (hsi : ∀ y ∈ L ⊓ centralizer (𝐔[i] : Set G), ∃ x ∈ Pi, x * (t * x * t⁻¹) = y)
    (hdj : ∀ x ∈ Pj, x * (t * x * t⁻¹) ∈ L ⊓ centralizer (𝐔[i.swap] : Set G))
    (hsj : ∀ y ∈ L ⊓ centralizer (𝐔[i.swap] : Set G), ∃ x ∈ Pj, x * (t * x * t⁻¹) = y)
    (hsylow : 𝐒 ⊓ Pi = 𝐒 ⊓ Pj)
    (hSP : 𝐒 ≤ Pi ⊔ Pi.map (MulAut.conj t).toMonoidHom)
    (hU : antiUnipotent K = rootA K i.swap ⊔
        (rootA K i ⊓ (rootA K i.swap).map (MulAut.conj (weylElt K i)).toMonoidHom))
    {a₀ : antiSp K} (ha₀ : a₀ ∈ rootA K i.swap ⊓ (rootA K i.swap).map
        (MulAut.conj (weylElt K i.swap * weylElt K i)).toMonoidHom)
    (hy₀ : a₀ * weylElt K i * a₀⁻¹ ∈
        (rootA K i.swap).map (MulAut.conj (weylElt K i)).toMonoidHom ⊓
          (rootA K i.swap).map
            (MulAut.conj (weylElt K i * weylElt K i.swap * weylElt K i)).toMonoidHom) :
    ⁅Pi, Pj.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  obtain ⟨m, hm, hm2⟩ := rt_card_antiSp (K := K)
  let ι : antiSp K →* G := L.subtype.comp φ.symm.toMonoidHom
  have pullι : ∀ H : Subgroup (antiSp K), pull φ H = H.map ι := fun H => diag_pull_eq_map φ H
  have hwi : ∀ j : Axis, 𝐰[j] = ι (weylElt K j) := fun _ => rfl
  have hwC : ∀ j : Axis, 𝐰[j] ∈ L ⊓ centralizer (𝐔[j] : Set G) := fun j =>
    mem_inf.2 ⟨w_mem_L j, mem_centralizer_iff.2 (w_facts h j).2.2.2.2.2⟩
  refine rt_main (S := 𝐒) (U := pull φ (antiUnipotent K)) (A := 𝐀[i.swap])
    (L₀ := L) (r₁ := 𝐰[i]) (r₂ := 𝐰[i.swap]) (a := ι a₀) (N := Nat.card K ^ 4) (m := m)
    hPi hPj hdi hsi hdj hsj hsylow hSP
    (fun x hx => (mem_normalizer_iff.1 (T_le_normalizer_S h hbt (t_mem_T h)) x).1 hx)
    (fun x hx hxt => (BothTrivialSlice.S_inf_C h hbt).le
      ⟨hx, mem_centralizer_singleton_iff.2 hxt.symm⟩)
    (IsPGroup.of_card (n := 8 * n) (by rw [card_S h hbt, h.setup.card_K]; ring))
    (by rw [card_S h hbt]; ring)
    ((card_pull φ _).trans (card_antiUnipotent rfl))
    inf_le_left ((Nat.card_congr φ.toEquiv).trans hm) hm2
    (hwC i) (hwC i.swap) (w_mul_self i) (w_mul_self i.swap)
    (mem_centralizer_singleton_iff.1 (w_facts h i).1).symm
    (mem_centralizer_singleton_iff.1 (w_facts h i.swap).1).symm
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hwi i, hwi i.swap, ← map_mul, ← map_pow, rt_weyl_pow_four, map_one]
  · rw [CU_eq i, pullι, pullι, hwi]
    exact rt_map_le_sup_conj ι (ProductModel.rootC_le_antiUnipotent_sup i)
  · rw [CU_eq i.swap, pullι, pullι, hwi]
    exact rt_map_le_sup_conj ι (ProductModel.rootC_le_antiUnipotent_sup i.swap)
  · exact pull_mono φ (ProductModel.rootA_le_antiUnipotent i.swap)
  · exact fun x hx => (mem_normalizer_iff.1 (w_facts h i.swap).2.1 x).1 hx
  · rw [pullι, pullι, hwi]
    exact rt_map_le_sup_conj ι (hU.le.trans (sup_le_sup_left inf_le_right _))
  · exact symm_mem_pull.mpr ha₀.1
  · have := rt_mem_map_conj_of_mem ι ha₀.2
    rw [map_mul] at this
    rw [pullι, hwi, hwi]
    exact this
  · have := rt_mem_map_conj_of_mem ι hy₀.1
    simp only [map_mul, map_inv] at this
    rw [pullι, hwi]
    exact this
  · have := rt_mem_map_conj_of_mem ι hy₀.2
    have e : ι (a₀ * weylElt K i * a₀⁻¹) = ι a₀ * ι (weylElt K i) * (ι a₀)⁻¹ := by
      simp only [map_mul, map_inv]
    have e2 : ι (weylElt K i * weylElt K i.swap * weylElt K i) =
        ι (weylElt K i) * ι (weylElt K i.swap) * ι (weylElt K i) := by simp only [map_mul]
    rw [e, e2] at this
    rw [pullι, hwi, hwi]
    exact this

structure CrossData (h : FCHyp L K n φ t) where
  P₁ : Subgroup G
  P₂ : Subgroup G
  perfect₁ : ⁅P₁, P₁⁆ = P₁
  perfect₂ : ⁅P₂, P₂⁆ = P₂
  comm₁ : ⁅P₁, P₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  comm₂ : ⁅P₂, P₂.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  inf₁ : P₁ ⊓ P₁.map (MulAut.conj t).toMonoidHom = ⊥
  inf₂ : P₂ ⊓ P₂.map (MulAut.conj t).toMonoidHom = ⊥
  sup₁ : P₁ ⊔ P₁.map (MulAut.conj t).toMonoidHom = 𝐍𝐂[Axis.one]
  sup₂ : P₂ ⊔ P₂.map (MulAut.conj t).toMonoidHom = 𝐍𝐂[Axis.two]
  diag₁ : ∀ x ∈ P₁, x * (t * x * t⁻¹) ∈ L ⊓ centralizer (𝐔[Axis.one] : Set G)
  diag_surj₁ : ∀ y ∈ L ⊓ centralizer (𝐔[Axis.one] : Set G), ∃ x ∈ P₁, x * (t * x * t⁻¹) = y
  diag₂ : ∀ x ∈ P₂, x * (t * x * t⁻¹) ∈ L ⊓ centralizer (𝐔[Axis.two] : Set G)
  diag_surj₂ : ∀ y ∈ L ⊓ centralizer (𝐔[Axis.two] : Set G), ∃ x ∈ P₂, x * (t * x * t⁻¹) = y
  sylow : 𝐒 ⊓ P₁ = 𝐒 ⊓ P₂

theorem commutator_cross_eq_bot (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (c : CrossData h) :
    ⁅c.P₁, c.P₂.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  have ht := h.setup.t_mul_t
  have hP₁ : RtPair t c.P₁ := RtPair.of_subgroups ht c.comm₁ c.inf₁
  have hP₂ : RtPair t c.P₂ := RtPair.of_subgroups ht c.comm₂ c.inf₂
  obtain ⟨i, hU, a₀, ha₀, hy₀⟩ := ProductModel.exists_root_trick_axis (K := K)
  cases i
  · exact cross_aux h hbt Axis.one hP₁ hP₂ c.diag₁ c.diag_surj₁ c.diag₂ c.diag_surj₂ c.sylow
      ((S_le_NC h hbt Axis.one).trans c.sup₁.ge) hU ha₀ hy₀
  · exact rt_comm_swap ht (cross_aux h hbt Axis.two hP₂ hP₁ c.diag₂ c.diag_surj₂ c.diag₁
      c.diag_surj₁ c.sylow.symm ((S_le_NC h hbt Axis.two).trans c.sup₂.ge) hU ha₀ hy₀)

end Setting

end BothTrivialProduct

end CFSG.LocalAnalysis.EvenBN.Sp4
