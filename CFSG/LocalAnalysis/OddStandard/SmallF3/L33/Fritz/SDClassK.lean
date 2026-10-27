module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDComm

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup CFSG.ComponentClassification.HSFLit

private lemma isConj_not_inner {L : Type*} [Group L] {φ ψ : MulAut L}
    (hφ : ¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹) (h : IsConj φ ψ) :
    ¬ ∃ a : L, ∀ u : L, ψ u = a * u * a⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  rintro ⟨a, ha⟩
  apply hφ
  refine ⟨c⁻¹ a, fun u => ?_⟩
  have h1 := ha (c u)
  simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h1
  calc φ u = c⁻¹ (c (φ u)) := by simp
    _ = c⁻¹ (a * c u * a⁻¹) := by rw [h1]
    _ = c⁻¹ a * u * (c⁻¹ a)⁻¹ := by simp [map_mul, map_inv, MulAut.inv_apply_self]

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

private theorem actX_conj {g b : X} (hg : g ∈ centralizer ({t} : Set X))
    (hb : b ∈ centralizer ({t} : Set X)) :
    ctx.actX (g * b * g⁻¹) = ctx.actX g * ctx.actX b * (ctx.actX g)⁻¹ := by
  rw [ctx.actX_mul (mul_mem hg hb) (inv_mem hg), ctx.actX_mul hg hb, ctx.actX_inv hg]

theorem not_conj_k_tk : ∀ g ∈ centralizer ({t} : Set X), g * ctx.C.k * g⁻¹ ≠ t * ctx.C.k := by
  intro g hg h
  have hkC : ctx.C.k ∈ centralizer ({t} : Set X) := ctx.k_mem_centralizer
  have htC : t ∈ centralizer ({t} : Set X) := by rw [mem_centralizer_singleton_iff]
  have ht1 : ctx.actX t = 1 := (ctx.actX_eq_one_iff htC).2 (Or.inr rfl)
  have htk : ctx.actX (t * ctx.C.k) = ctx.actX ctx.C.k := by
    rw [ctx.actX_mul htC hkC, ht1, one_mul]
  have h1 : ctx.actX g * ctx.actX ctx.C.k * (ctx.actX g)⁻¹ = ctx.actX ctx.C.k := by
    rw [← actX_conj ctx hg hkC, h, htk]
  have hcomm : ctx.actX g * ctx.actX ctx.C.k = ctx.actX ctx.C.k * ctx.actX g := by
    calc ctx.actX g * ctx.actX ctx.C.k
        = (ctx.actX g * ctx.actX ctx.C.k * (ctx.actX g)⁻¹) * ctx.actX g := by group
      _ = ctx.actX ctx.C.k * ctx.actX g := by rw [h1]
  have hcommg : g * ctx.C.k = ctx.C.k * g := ctx.comm_outer (Or.inl rfl) hg hcomm
  have hk : g * ctx.C.k * g⁻¹ = ctx.C.k := by rw [hcommg]; group
  have htk_eq : ctx.C.k = t * ctx.C.k := hk.symm.trans h
  have ht_eq_one : t = 1 := by
    have h2 : t * ctx.C.k = 1 * ctx.C.k := by rw [htk_eq.symm, one_mul]
    exact mul_right_cancel h2
  have hord := ctx.A.orderOf_t
  rw [ht_eq_one, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem ncard_conj_k :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * ctx.C.k * g⁻¹ = b}.ncard = 234 := by
  classical
  let S : Set X := {b | ∃ g ∈ centralizer ({t} : Set X), g * ctx.C.k * g⁻¹ = b}
  let O : Set (MulAut ↥L) :=
    {φ | φ ^ 2 = 1 ∧ ¬ ∃ a : ↥L, ∀ u : ↥L, φ u = a * u * a⁻¹}
  change S.ncard = 234
  have hmemS : ∀ b, b ∈ S ↔ ∃ g ∈ centralizer ({t} : Set X), g * ctx.C.k * g⁻¹ = b :=
    fun _ => Iff.rfl
  have hSsub : S ⊆ centralizer ({t} : Set X) := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := (hmemS b).1 hb
    exact mul_mem (mul_mem hg ctx.k_mem_centralizer) (inv_mem hg)
  have hinj : Set.InjOn ctx.actX S := by
    intro b₁ hb₁ b₂ hb₂ hab
    obtain ⟨g₁, hg₁, hg₁b⟩ := (hmemS b₁).1 hb₁
    obtain ⟨g₂, hg₂, hg₂b⟩ := (hmemS b₂).1 hb₂
    have hb₁C : b₁ ∈ centralizer ({t} : Set X) := hSsub hb₁
    have hb₂C : b₂ ∈ centralizer ({t} : Set X) := hSsub hb₂
    have hmulC : b₂ * b₁⁻¹ ∈ centralizer ({t} : Set X) := mul_mem hb₂C (inv_mem hb₁C)
    have hact : ctx.actX (b₂ * b₁⁻¹) = 1 := by
      rw [ctx.actX_mul hb₂C (inv_mem hb₁C), ctx.actX_inv hb₁C, hab]
      group
    rcases (ctx.actX_eq_one_iff hmulC).1 hact with h1 | ht
    · exact (mul_inv_eq_one.mp h1).symm
    · exfalso
      have hb2 : b₂ = t * b₁ := mul_inv_eq_iff_eq_mul.mp ht
      have htb : g₁⁻¹ * t * g₁ = t := by
        have htinv : t * g₁⁻¹ = g₁⁻¹ * t :=
          mem_centralizer_iff.mp (inv_mem hg₁) t (by simp)
        rw [← htinv]
        group
      have hkey : g₁⁻¹ * b₂ * g₁ = t * ctx.C.k := by
        calc g₁⁻¹ * b₂ * g₁ = g₁⁻¹ * (t * (g₁ * ctx.C.k * g₁⁻¹)) * g₁ := by
              rw [hb2, hg₁b.symm]
          _ = (g₁⁻¹ * t * g₁) * ctx.C.k := by group
          _ = t * ctx.C.k := by rw [htb]
      have hg12C : g₁⁻¹ * g₂ ∈ centralizer ({t} : Set X) := mul_mem (inv_mem hg₁) hg₂
      have hconj : (g₁⁻¹ * g₂) * ctx.C.k * (g₁⁻¹ * g₂)⁻¹ = t * ctx.C.k := by
        calc (g₁⁻¹ * g₂) * ctx.C.k * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * b₂ * g₁ := by
              rw [hg₂b.symm]; group
          _ = t * ctx.C.k := hkey
      exact (not_conj_k_tk ctx (g₁⁻¹ * g₂) hg12C) hconj
  have himg : ctx.actX '' S = O := by
    ext φ
    constructor
    · rintro ⟨b, hb, hbφ⟩
      rw [← hbφ]
      obtain ⟨g, hg, hgb⟩ := (hmemS b).1 hb
      rw [← hgb, actX_conj ctx hg ctx.k_mem_centralizer, ctx.actX_k]
      change (ctx.actX g * ctx.M.F.k * (ctx.actX g)⁻¹) ^ 2 = 1 ∧
        ¬ ∃ a : ↥L, ∀ u : ↥L,
          (ctx.actX g * ctx.M.F.k * (ctx.actX g)⁻¹) u = a * u * a⁻¹
      refine ⟨?_, ?_⟩
      · rw [conj_pow, ctx.M.F.k_sq]
        group
      · exact isConj_not_inner ctx.M.F.k_outer (isConj_iff.2 ⟨ctx.actX g, rfl⟩)
    · intro hφ
      change φ ^ 2 = 1 ∧ ¬ ∃ a : ↥L, ∀ u : ↥L, φ u = a * u * a⁻¹ at hφ
      obtain ⟨c, hc⟩ := isConj_iff.1
        (ctx.M.outer_involutions_conj ctx.M.F.k_sq ctx.M.F.k_outer hφ.1 hφ.2)
      obtain ⟨g, hg, hgk⟩ := ctx.exists_actX_eq c
      refine ⟨g * ctx.C.k * g⁻¹, (hmemS _).2 ⟨g, hg, rfl⟩, ?_⟩
      rw [actX_conj ctx hg ctx.k_mem_centralizer, ctx.actX_k, hgk]
      exact hc
  have hOcard : O.ncard = 234 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {φ : MulAut ↥L // φ ^ 2 = 1 ∧
      ¬ ∃ a : ↥L, ∀ u : ↥L, φ u = a * u * a⁻¹} = 234
    exact ctx.M.card_outer_involutions
  rw [← hinj.ncard_image, himg]
  exact hOcard

theorem card_conj_k :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * ctx.C.k * g⁻¹ = b}.ncard ≡ 2 [MOD 4] := by
  rw [ctx.ncard_conj_k]
  decide

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx
