module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx51
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic14
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx50

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Basic

theorem cyc_comm {G : Type*} [Group G] {W : Subgroup G} (hc : IsCyclic ↥W) :
    ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  intro a ha b hb
  have := (hc.isMulCommutative).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

end Basic

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G} {t w : G}

theorem S1_le_normalizer_Q (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : S1 S K₁ ≤ normalizer (Qof S K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hs.Q_conj_mem hII hK hg hy
  · intro hy
    have h1 := hs.Q_conj_mem hII hK (inv_mem hg) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h1

theorem card_cent_w_le32 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) :
    Nat.card ↥(S ⊓ centralizer ({w} : Set G)) ≤ 32 := by
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  have hV4 : Nat.card ↥(Vof S K₁ W₂) = 4 := by norm_num at hk; exact hk
  obtain ⟨hQ₁16, hQ₂16, hS1eq, hS1i⟩ := hs.case3 hII hq hrec hP8 cfg.hS256
  have hwS : w ∈ S := Nh_le_S cfg.hwD
  have hAV₁ : Vof S K₁ W₂ ≤ Aof S K₁ W₂ h := le_sup_left
  have hAV₂ : Vof S K₂ W₁ ≤ Aof S K₁ W₂ h := hs.V₂_le_A hII hq hrec hk
  have hinv₁ : ∀ x ∈ Vof S K₁ W₂, w * x * w⁻¹ = x⁻¹ := fun x hx => cfg.hinvA x (hAV₁ hx)
  have hinv₂ : ∀ x ∈ Vof S K₂ W₁, w * x * w⁻¹ = x⁻¹ := fun x hx => cfg.hinvA x (hAV₂ hx)
  have hwS1 : w ∈ S1 S K₁ := hs.w_mem_S1 hII hV4 hwS hinv₁
  have hmemS1 : ∀ g ∈ Qof S K₁ ⊔ Qof S K₂, g ∈ S1 S K₁ := fun g hg => by
    rw [hS1eq]
    exact hg
  have hQ₁N : Qof S K₁ ≤ normalizer (Qof S K₂ : Set G) := fun g hg =>
    hs.S1_le_normalizer_Q hII (Or.inr rfl) (hs.Q₁_le_S1 hg)
  have hwQ : w ∈ Qof S K₁ ⊔ Qof S K₂ := by
    rw [← hS1eq]
    exact hwS1
  obtain ⟨w₁, hw₁, w₂, hw₂, hww⟩ := Basic.mem_sup_of_le_normalizer' hQ₁N hwQ
  obtain ⟨M₁, hM₁Q, hM₁c, hzM₁, -, hM₁i, hM₁out⟩ := (hs.gq_Q₁ hII).ex
  obtain ⟨M₂, hM₂Q, hM₂c, hzM₂, -, hM₂i, hM₂out⟩ := (hs.gq_Q₂ hII).ex
  have hM₁8 : Nat.card ↥M₁ = 8 := by
    have := Basic.card_mul_relIndex_of_le hM₁Q
    rw [hM₁i, hQ₁16] at this
    omega
  have hM₂8 : Nat.card ↥M₂ = 8 := by
    have := Basic.card_mul_relIndex_of_le hM₂Q
    rw [hM₂i, hQ₂16] at this
    omega
  have hW₁8 : Nat.card ↥W₁ = 8 := by
    have := hs.card_W₁ hII
    omega
  have hW₂8 : Nat.card ↥W₂ = 8 := by
    have := hs.card_W₂ hII
    omega
  have hzz := hs.z_sq
  have hz1 : z ≠ 1 := hs.z_ne
  have hW₁M : W₁ = M₁ := Basic.W_eq_M (Q := Qof S K₁) (z := z) hs.W₁_le_Q₁ hs.W₁_max.2.1 hW₁8 hM₁8
    (fun x hx hxM => (hM₁out x hx hxM).1) hzz
  have hW₂M : W₂ = M₂ := Basic.W_eq_M (Q := Qof S K₂) (z := z) hs.W₂_le_Q₂ hs.W₂_max.2.1 hW₂8 hM₂8
    (fun x hx hxM => (hM₂out x hx hxM).1) hzz
  obtain ⟨v₁, hv₁, v₂, hv₂, -, hv₁sq, hv₂sq⟩ := hs.u_decomp hII hq
  have hv₁W₂ : v₁ ∈ W₂ := hv₁.1
  have hv₂W₁ : v₂ ∈ W₁ := hv₂.1
  have hv₁P : v₁ ∈ Pof S K₁ := hv₁.2
  have hv₂P : v₂ ∈ Pof S K₂ := hv₂.2
  have hQc₂ := hs.Q_comm_P hII (K := K₂) (Or.inr rfl)
  have hQc₁ := hs.Q_comm_P hII (K := K₁) (Or.inl rfl)
  have hw₁M : w₁ ∉ M₁ := by
    intro hw₁M
    have hw₁W : w₁ ∈ W₁ := by rw [hW₁M]; exact hw₁M
    have c1 : w₁ * v₂ = v₂ * w₁ := Basic.cyc_comm hs.W₁_max.2.1 w₁ hw₁W v₂ hv₂W₁
    have c2 : w₂ * v₂ = v₂ * w₂ := hQc₂ w₂ hw₂ v₂ hv₂P
    have h1 : w * v₂ * w⁻¹ = v₂ := by
      rw [hww]
      calc w₁ * w₂ * v₂ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * v₂ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * v₂ * w₁⁻¹ := by rw [c2]; group
        _ = v₂ := by rw [c1]; group
    have h2 := hinv₂ v₂ hv₂
    rw [h1] at h2
    have h3 : v₂ * v₂ = 1 := by
      calc v₂ * v₂ = v₂ * v₂⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel v₂
    rw [hv₂sq] at h3
    exact hz1 h3
  have hw₂M : w₂ ∉ M₂ := by
    intro hw₂M
    have hw₂W : w₂ ∈ W₂ := by rw [hW₂M]; exact hw₂M
    have c1 : w₂ * v₁ = v₁ * w₂ := Basic.cyc_comm hs.W₂_max.2.1 w₂ hw₂W v₁ hv₁W₂
    have c2 : w₁ * v₁ = v₁ * w₁ := hQc₁ w₁ hw₁ v₁ hv₁P
    have h1 : w * v₁ * w⁻¹ = v₁ := by
      rw [hww]
      calc w₁ * w₂ * v₁ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * v₁ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * v₁ * w₁⁻¹ := by rw [c1]; group
        _ = v₁ := by rw [c2]; group
    have h2 := hinv₁ v₁ hv₁
    rw [h1] at h2
    have h3 : v₁ * v₁ = 1 := by
      calc v₁ * v₁ = v₁ * v₁⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel v₁
    rw [hv₁sq] at h3
    exact hz1 h3
  have hm₁Q : v₂ ∈ M₁ := by rw [← hW₁M]; exact hv₂W₁
  have hm₁c : ∀ y ∈ Qof S K₂, v₂ * y = y * v₂ := fun y hy => (hQc₂ y hy v₂ hv₂P).symm
  have hbound := Basic.card_cent_le_sixteen (Q₁ := Qof S K₁) (Q₂ := Qof S K₂) (M₁ := M₁) (M₂ := M₂)
    (z := z) (w₁ := w₁) (w₂ := w₂) (m₁ := v₂) hzz hz1
    (fun g hg => hs.z_comm hII (S1_le_S (hmemS1 g hg)))
    (fun g hg y hy => hs.Q_conj_mem hII (Or.inl rfl) (hmemS1 g hg) hy)
    (fun g hg y hy => hs.Q_conj_mem hII (Or.inr rfl) (hmemS1 g hg) hy)
    (hs.Q_inf_Q hII) hM₁Q hM₂Q hM₁c hM₂c hQ₁16 hQ₂16 hM₁8 hM₂8 hzM₁ hzM₂ hM₁out hM₂out hw₁ hw₁M
    hw₂ hw₂M hm₁Q hv₂sq hm₁c
  rw [← hww, ← hS1eq] at hbound
  have h2 := Basic.card_le_two_mul_inf (C := S ⊓ centralizer ({w} : Set G)) (S := S) (S₁ := S1 S K₁)
    inf_le_left hS1i.le
  have heq : S1 S K₁ ⊓ (S ⊓ centralizer ({w} : Set G)) = S1 S K₁ ⊓ centralizer ({w} : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, S1_le_S hx.1, hx.2⟩
  rw [heq] at h2
  omega

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
