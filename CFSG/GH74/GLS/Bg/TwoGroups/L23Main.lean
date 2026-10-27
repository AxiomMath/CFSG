module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23V
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Class

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L23

open A44

section ExtT

variable {T : Type} [Group T] (A : Subgroup T) [A.Normal] (θ : A ≃* Z4Z4)

theorem mem_A_of_rho_eq_one (hC : Subgroup.centralizer (A : Set T) = A) {t : T}
    (ht : rhoHom A θ t = 1) : t ∈ A :=
  (SetLike.ext_iff.mp (ker_rho A θ hC) t).mp (MonoidHom.mem_ker.mpr ht)

theorem exists_extData (hC : Subgroup.centralizer (A : Set T) = A) (p q : T)
    (hp : (rhoHom A θ p).1 = Pm) (hq : (rhoHom A θ q).1 = Qm) :
    ∃ D : ExtData PP QQ T, D.emb = embT A θ ∧ D.p = p ∧ D.q = q := by
  have hpe : ∀ v, p * embT A θ v = embT A θ (PP v) * p := by
    intro v
    have h := conj_embT A θ p v
    rw [hp] at h
    calc p * embT A θ v = (p * embT A θ v * p⁻¹) * p := by group
      _ = embT A θ (PP v) * p := by rw [show PP v = Pm.act v from rfl, h]
  have hqe : ∀ v, q * embT A θ v = embT A θ (QQ v) * q := by
    intro v
    have h := conj_embT A θ q v
    rw [hq] at h
    calc q * embT A θ v = (q * embT A θ v * q⁻¹) * q := by group
      _ = embT A θ (QQ v) * q := by rw [show QQ v = Qm.act v from rfl, h]
  have hPP : rhoHom A θ (p * p) = 1 := by
    rw [map_mul]
    apply Subtype.ext
    show M4.mul (rhoHom A θ p).1 (rhoHom A θ p).1 = M4.one
    rw [hp]; decide
  have hQQ : rhoHom A θ (q * q) = 1 := by
    rw [map_mul]
    apply Subtype.ext
    show M4.mul (rhoHom A θ q).1 (rhoHom A θ q).1 = M4.one
    rw [hq]; decide
  have hPQ : rhoHom A θ p * rhoHom A θ q = rhoHom A θ q * rhoHom A θ p := by
    apply Subtype.ext
    show M4.mul (rhoHom A θ p).1 (rhoHom A θ q).1 = M4.mul (rhoHom A θ q).1 (rhoHom A θ p).1
    rw [hp, hq]; decide
  have hG : rhoHom A θ ((p * q)⁻¹ * (q * p)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hPQ, inv_mul_cancel]
  obtain ⟨α, hα⟩ := exists_embT A θ (mem_A_of_rho_eq_one A θ hC hPP)
  obtain ⟨β, hβ⟩ := exists_embT A θ (mem_A_of_rho_eq_one A θ hC hQQ)
  obtain ⟨γ, hγ⟩ := exists_embT A θ (mem_A_of_rho_eq_one A θ hC hG)
  refine ⟨{ emb := embT A θ
            emb_add := embT_add A θ
            emb_inj := embT_inj A θ
            p := p
            q := q
            α := α
            β := β
            γ := γ
            hp := hpe
            hq := hqe
            hpp := hα
            hqq := hβ
            hqp := ?_ }, rfl, rfl, rfl⟩
  calc q * p = (p * q) * ((p * q)⁻¹ * (q * p)) := by group
    _ = p * q * embT A θ γ := by rw [hγ]

end ExtT

section Classify

variable {T : Type} [Group T] [Finite T] (A : Subgroup T) [A.Normal] (θ : A ≃* Z4Z4)
  (x : MulAut T) (hA : ∀ a ∈ A, x a ∈ A)

include θ hA

theorem classify_T (hx : x ^ 3 = 1) (hfix : ∀ g : T, x g = g → g = 1)
    (hC : Subgroup.centralizer (A : Set T) = A) (hT : Nat.card T = 64) (hA16 : Nat.card A = 16) :
    (Nonempty (T ≃* SylSL3_4) ∧ Nat.card (Invs T) = 27) ∨
      (Nonempty (T ≃* SylSU3_4) ∧ Nat.card (Invs T) = 3) := by
  obtain ⟨p, hp⟩ := V4list_subset_range A θ x hA hx hfix hC hT hA16 Pm (by decide)
  obtain ⟨q, hq⟩ := V4list_subset_range A θ x hA hx hfix hC hT hA16 Qm (by decide)
  obtain ⟨D, hDe, hDp, hDq⟩ := exists_extData A θ hC p q hp hq
  have hnf := ExtData.nf_bijective D hT hdistPQ
  have hinj := ExtData.nf_injective D hdistPQ
  have hxe : ∀ v, x (D.emb v) = D.emb ((xi A θ x hA).1.act v) := by
    intro v; rw [hDe]; exact x_embT A θ x hA v
  have hp' : ∀ w, p * D.emb w = D.emb (PP w) * p := by
    intro w; have := D.hp w; rwa [hDp] at this
  have hq' : ∀ w, q * D.emb w = D.emb (QQ w) * q := by
    intro w; have := D.hq w; rwa [hDq] at this
  have hpp : p * p = D.emb D.α := by have := D.hpp; rwa [hDp] at this
  have hqq : q * q = D.emb D.β := by have := D.hqq; rwa [hDq] at this
  have hqp : q * p = p * q * D.emb D.γ := by have := D.hqp; rwa [hDp, hDq] at this
  have hnf0 : ∀ t : Vec, D.nf (t, false, false) = D.emb t := by
    intro t; simp [ExtData.nf, pw]
  obtain ⟨⟨a₁, i₁, j₁⟩, h1⟩ := hnf.2 (x p)
  obtain ⟨⟨a₂, i₂, j₂⟩, h2⟩ := hnf.2 (x q)
  have hassoc : Assoc8 D.α D.β D.γ := by
    intro a _ b _ c _
    apply hinj
    rw [← ExtData.nf_mul, ← ExtData.nf_mul, ← ExtData.nf_mul, ← ExtData.nf_mul, mul_assoc]
  have hπ := assoc8_valid D.α D.β D.γ hassoc
  have hActP : ActP (xi A θ x hA).1 i₁ j₁ := by
    intro w
    have e1 := ExtData.nf_conj D (a₁, i₁, j₁) ((xi A θ x hA).1.act w)
    rw [h1] at e1
    have e2 : x p * D.emb ((xi A θ x hA).1.act w) =
        D.emb ((xi A θ x hA).1.act (PP w)) * x p := by
      rw [← hxe, ← map_mul, hp', map_mul, hxe]
    have e3 : D.emb (Mop PP QQ i₁ j₁ ((xi A θ x hA).1.act w)) * x p =
        D.emb ((xi A θ x hA).1.act (PP w)) * x p := by
      rw [← e1, e2]
    exact D.emb_inj (mul_right_cancel e3)
  have hActQ : ActQ (xi A θ x hA).1 i₂ j₂ := by
    intro w
    have e1 := ExtData.nf_conj D (a₂, i₂, j₂) ((xi A θ x hA).1.act w)
    rw [h2] at e1
    have e2 : x q * D.emb ((xi A θ x hA).1.act w) =
        D.emb ((xi A θ x hA).1.act (QQ w)) * x q := by
      rw [← hxe, ← map_mul, hq', map_mul, hxe]
    have e3 : D.emb (Mop PP QQ i₂ j₂ ((xi A θ x hA).1.act w)) * x q =
        D.emb ((xi A θ x hA).1.act (QQ w)) * x q := by
      rw [← e1, e2]
    exact D.emb_inj (mul_right_cancel e3)
  have hSq1 : SqEq (D.α, D.β, D.γ) (a₁, i₁, j₁) ((xi A θ x hA).1.act D.α) := by
    apply hinj
    show D.nf (mulC PP QQ D.α D.β D.γ (a₁, i₁, j₁) (a₁, i₁, j₁)) =
      D.nf ((xi A θ x hA).1.act D.α, false, false)
    rw [← ExtData.nf_mul, h1, hnf0, ← hxe, ← hpp, map_mul]
  have hSq2 : SqEq (D.α, D.β, D.γ) (a₂, i₂, j₂) ((xi A θ x hA).1.act D.β) := by
    apply hinj
    show D.nf (mulC PP QQ D.α D.β D.γ (a₂, i₂, j₂) (a₂, i₂, j₂)) =
      D.nf ((xi A θ x hA).1.act D.β, false, false)
    rw [← ExtData.nf_mul, h2, hnf0, ← hxe, ← hqq, map_mul]
  have hComm : CommEq (D.α, D.β, D.γ) (a₁, i₁, j₁) (a₂, i₂, j₂) ((xi A θ x hA).1.act D.γ) := by
    apply hinj
    show D.nf (mulC PP QQ D.α D.β D.γ (a₂, i₂, j₂) (a₁, i₁, j₁)) =
      D.nf (mulC PP QQ D.α D.β D.γ (mulC PP QQ D.α D.β D.γ (a₁, i₁, j₁) (a₂, i₂, j₂))
        ((xi A θ x hA).1.act D.γ, false, false))
    rw [← ExtData.nf_mul, ← ExtData.nf_mul, ← ExtData.nf_mul, h1, h2, hnf0, ← hxe]
    rw [← map_mul, ← map_mul, ← map_mul, ← hqp]
  have hπ16 : (D.α, D.β, D.γ) ∈ S16 :=
    x_classify (D.α, D.β, D.γ) hπ (xi A θ x hA).1 (xi_mem_ord3 A θ x hA hx hfix) i₁ j₁ hActP a₁
      hSq1 i₂ j₂ hActQ a₂ hSq2 hComm
  exact classify_models hT D hπ16

end Classify

end L23

end CFSG.GH74.GLS.Bg.TwoGroups
