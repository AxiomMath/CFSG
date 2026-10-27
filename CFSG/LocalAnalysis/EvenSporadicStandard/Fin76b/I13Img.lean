module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Rho

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

section Conv

variable {G : Type*} [Group G] {E : Subgroup G}

@[expose] noncomputable def convN (ℓ : normalizer (E : Set G)) : MulAut ↥E :=
  E.normalizerMonoidHom ℓ

theorem convN_coe (ℓ : normalizer (E : Set G)) (e : ↥E) :
    ((convN ℓ e : ↥E) : G) = ℓ * e * (ℓ : G)⁻¹ := rfl

theorem convN_mul (ℓ ℓ' : normalizer (E : Set G)) : convN (ℓ * ℓ') = convN ℓ * convN ℓ' :=
  map_mul _ _ _

theorem theta_conj_of_comm {z n : G} (hnz : n * z = z * n) (w : G) :
    (n * w * n⁻¹) * (z * (n * w * n⁻¹) * z⁻¹) = n * (w * (z * w * z⁻¹)) * n⁻¹ := by
  have key : z * (n * w * n⁻¹) * z⁻¹ = n * (z * w * z⁻¹) * n⁻¹ := by
    calc z * (n * w * n⁻¹) * z⁻¹ = (z * n) * w * (z * n)⁻¹ := by group
      _ = (n * z) * w * (n * z)⁻¹ := by rw [hnz]
      _ = n * (z * w * z⁻¹) * n⁻¹ := by group
  rw [key]
  group

end Conv

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem rho1_W1 (w : ↥c.W1) :
    c.rho1 ⟨w, c.Qs_le_N1 (c.W1_le_Qs w.2)⟩ = MulAut.conj (c.thetaHom w) := by
  refine MulEquiv.ext fun e => ?_
  obtain ⟨w', rfl⟩ := c.thetaHom_surjective e
  rw [rho1_theta, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem rho1_W2 (w : ↥c.W2) : c.rho1 ⟨w, c.Qs_le_N1 (c.W2_le_Qs w.2)⟩ = 1 := by
  refine MulEquiv.ext fun e => ?_
  obtain ⟨w', rfl⟩ := c.thetaHom_surjective e
  rw [rho1_theta]
  show c.thetaHom (c.conjW1 _ w') = c.thetaHom w'
  congr 1
  apply Subtype.ext
  show (w : G) * w' * (w : G)⁻¹ = w'
  rw [← c.W1_comm_W2 w'.2 w.2]
  group

theorem rho_W1 (w : ↥c.W1) :
    c.rho ⟨w, c.Qs_le_N1 (c.W1_le_Qs w.2)⟩ = (MulAut.conj (c.thetaHom w), 1) := by
  refine Prod.ext (c.rho1_W1 w) ?_
  show c.rho1 (c.zconjN1 _) = 1
  have : c.zconjN1 ⟨w, c.Qs_le_N1 (c.W1_le_Qs w.2)⟩ =
      ⟨z * w * z⁻¹, c.Qs_le_N1 (c.W2_le_Qs (c.z_conj_W1 w.2))⟩ := rfl
  rw [this]
  exact c.rho1_W2 ⟨z * w * z⁻¹, c.z_conj_W1 w.2⟩

theorem rho_W2 (w : ↥c.W2) :
    c.rho ⟨w, c.Qs_le_N1 (c.W2_le_Qs w.2)⟩ =
      (1, MulAut.conj (c.thetaHom ⟨z * w * z⁻¹, c.z_conj_W2 w.2⟩)) := by
  refine Prod.ext (c.rho1_W2 w) ?_
  show c.rho1 (c.zconjN1 _) = _
  exact c.rho1_W1 ⟨z * w * z⁻¹, c.z_conj_W2 w.2⟩

theorem rho_Qs_mem {q : G} (hq : q ∈ c.Qs) :
    ∃ e₁ e₂ : ↥E, c.rho ⟨q, c.Qs_le_N1 hq⟩ = (MulAut.conj e₁, MulAut.conj e₂) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq hq
  have h := map_mul c.rho (⟨w₁, c.Qs_le_N1 (c.W1_le_Qs hw₁)⟩ : ↥c.N1)
    ⟨w₂, c.Qs_le_N1 (c.W2_le_Qs hw₂)⟩
  have e : (⟨w₁ * w₂, c.Qs_le_N1 hq⟩ : ↥c.N1) =
      ⟨w₁, c.Qs_le_N1 (c.W1_le_Qs hw₁)⟩ * ⟨w₂, c.Qs_le_N1 (c.W2_le_Qs hw₂)⟩ := rfl
  rw [e, h, rho_W1 c ⟨w₁, hw₁⟩, rho_W2 c ⟨w₂, hw₂⟩]
  exact ⟨c.thetaHom ⟨w₁, hw₁⟩, c.thetaHom ⟨z * w₂ * z⁻¹, c.z_conj_W2 hw₂⟩, by simp⟩

theorem exists_rho_Qs (e₁ e₂ : ↥E) :
    ∃ q : G, ∃ hq : q ∈ c.Qs, c.rho ⟨q, c.Qs_le_N1 hq⟩ = (MulAut.conj e₁, MulAut.conj e₂) := by
  obtain ⟨w₁, rfl⟩ := c.thetaHom_surjective e₁
  obtain ⟨w₂, rfl⟩ := c.thetaHom_surjective e₂
  have hw₂ : z * (w₂ : G) * z⁻¹ ∈ c.W2 := c.z_conj_W1 w₂.2
  have hmem : (w₁ : G) * (z * (w₂ : G) * z⁻¹) ∈ c.Qs :=
    mul_mem (c.W1_le_Qs w₁.2) (c.W2_le_Qs hw₂)
  refine ⟨_, hmem, ?_⟩
  have h := map_mul c.rho (⟨w₁, c.Qs_le_N1 (c.W1_le_Qs w₁.2)⟩ : ↥c.N1)
    ⟨z * (w₂ : G) * z⁻¹, c.Qs_le_N1 (c.W2_le_Qs hw₂)⟩
  have e : (⟨(w₁ : G) * (z * (w₂ : G) * z⁻¹), c.Qs_le_N1 hmem⟩ : ↥c.N1) =
      ⟨w₁, c.Qs_le_N1 (c.W1_le_Qs w₁.2)⟩ * ⟨z * (w₂ : G) * z⁻¹, c.Qs_le_N1 (c.W2_le_Qs hw₂)⟩ :=
    rfl
  rw [e, h, rho_W1 c w₁, rho_W2 c ⟨z * (w₂ : G) * z⁻¹, hw₂⟩]
  have : (⟨z * (z * (w₂ : G) * z⁻¹) * z⁻¹, c.z_conj_W2 hw₂⟩ : ↥c.W1) = w₂ :=
    Subtype.ext (c.z_conj_conj _)
  rw [this]
  simp

theorem rho_Zs {a : G} (ha : a ∈ c.Zs) : c.rho ⟨a, c.Zs_le_N1 ha⟩ = 1 := by
  refine Prod.ext (c.rho1_W2 ⟨a, c.Zs_le_W2 ha⟩) ?_
  show c.rho1 (c.zconjN1 _) = 1
  have hza : z * a * z⁻¹ ∈ c.Zs := by
    rcases c.mem_Zs.1 ha with h1 | h1 | h1 | h1
    · rw [h1]; simp
    · rw [h1, c.h.z_conj_t]; exact c.t_mem_Zs
    · rw [h1, c.h.z_conj_alpha c.hα]; exact c.alpha_t_mem_Zs
    · rw [h1]
      have : z * (α * t) * z⁻¹ = α := by
        calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
          _ = α * t * t := by rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t]
          _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
      rw [this]; exact c.alpha_mem_Zs
  exact c.rho1_W2 ⟨z * a * z⁻¹, c.Zs_le_W2 hza⟩

theorem W_le_normE : L ⊓ centralizer ({t} : Set G) ≤ normalizer (E : Set G) :=
  CFSG.EvenSporadicStandard.Fin76b.W_le_normalizer c.h.wf

theorem rho1_conv (n : ↥c.N1) (hnz : (n : G) * z = z * n) (hn : (n : G) ∈ normalizer (E : Set G)) :
    c.rho1 n = convN ⟨(n : G), hn⟩ := by
  refine MulEquiv.ext fun e => ?_
  obtain ⟨w, rfl⟩ := c.thetaHom_surjective e
  rw [rho1_theta]
  apply Subtype.ext
  show (n : G) * w * (n : G)⁻¹ * (z * ((n : G) * w * (n : G)⁻¹) * z⁻¹) =
    (n : G) * ((w : G) * (z * w * z⁻¹)) * (n : G)⁻¹
  exact theta_conj_of_comm hnz w

theorem rho_conv (n : ↥c.N1) (hnz : (n : G) * z = z * n)
    (hn : (n : G) ∈ normalizer (E : Set G)) :
    c.rho n = (convN ⟨(n : G), hn⟩, convN ⟨(n : G), hn⟩) := by
  have hz : c.zconjN1 n = n := by
    apply Subtype.ext
    show z * (n : G) * z⁻¹ = n
    rw [← hnz]; group
  refine Prod.ext (c.rho1_conv n hnz hn) ?_
  show c.rho1 (c.zconjN1 n) = _
  rw [hz]
  exact c.rho1_conv n hnz hn

theorem exists_eq_mul_of_mem_W {ℓ : G} (hℓ : ℓ ∈ L ⊓ centralizer ({t} : Set G)) :
    ∃ e ∈ E, ∃ b ∈ B, ℓ = e * b := by
  classical
  have hEB : ∀ (p : ↥E × ↥B), (p.1 : G) * p.2 ∈ L ⊓ centralizer ({t} : Set G) := fun p =>
    mul_mem (c.h.E_le_W p.1.2) (c.h.B_le_W p.2.2)
  let φ : ↥E × ↥B → ↥(L ⊓ centralizer ({t} : Set G)) := fun p => ⟨p.1 * p.2, hEB p⟩
  have hinj : Function.Injective φ := by
    rintro ⟨e, b⟩ ⟨e', b'⟩ hφ
    have h1 : (e : G) * b = e' * b' := congrArg Subtype.val hφ
    have h2 : ((e' : G)⁻¹ * e : G) = b' * (b : G)⁻¹ := by
      calc (e' : G)⁻¹ * e = (e' : G)⁻¹ * (e * b) * (b : G)⁻¹ := by group
        _ = (e' : G)⁻¹ * (e' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hbB : (b' : G) * (b : G)⁻¹ ∈ B := mul_mem b'.2 (inv_mem b.2)
    have hbE : (b' : G) * (b : G)⁻¹ ∈ E := by
      rw [← h2]; exact mul_mem (inv_mem e'.2) e.2
    have h3 := c.h.E_inf_B hbE hbB
    have hb : (b' : G) = b := by
      calc (b' : G) = (b' * (b : G)⁻¹) * b := by group
        _ = b := by rw [h3, one_mul]
    have he : (e : G) = e' := by
      calc (e : G) = e' * ((e' : G)⁻¹ * e) := by group
        _ = e' := by rw [h2, h3, mul_one]
    rw [Subtype.ext he, Subtype.ext hb.symm]
  have hcard : Nat.card ↥(L ⊓ centralizer ({t} : Set G)) ≤ Nat.card (↥E × ↥B) := by
    rw [Nat.card_prod, c.h.wf.card_cent, c.h.wf.card_E, c.h.B_card]
  obtain ⟨⟨e, b⟩, hfb⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨ℓ, hℓ⟩
  exact ⟨e, e.2, b, b.2, (congrArg Subtype.val hfb).symm⟩

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
