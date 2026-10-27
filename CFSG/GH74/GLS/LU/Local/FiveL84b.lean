module

public import CFSG.GH74.GLS.LU.Local.FiveL85a

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L84b

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.sup_eq_K1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {P Q : Subgroup G} (hP : P ≤ K₁)
    (hQ : Q ≤ K₁) (hPc : Nat.card ↥P = 5) (hQc : Nat.card ↥Q = 5) (hne : P ≠ Q) : P ⊔ Q = K₁ := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcardq : Nat.card (ZMod 5) = p ^ f := by rw [c.ctx.pf, Nat.card_zmod]
  obtain ⟨e⟩ := exists_mulEquiv_SL2 c.hc.sl₁ (ZMod 5) hcardq
  have hP' : Nat.card ↥(P.subgroupOf K₁) = 5 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv).trans hPc
  have hQ' : Nat.card ↥(Q.subgroupOf K₁) = 5 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv).trans hQc
  have hne' : P.subgroupOf K₁ ≠ Q.subgroupOf K₁ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hP, ← Subgroup.map_subgroupOf_eq_of_le hQ, h]
  have h := sl2_five_sylow_gen e hP' hQ' hne'
  have h2 : (P.subgroupOf K₁ ⊔ Q.subgroupOf K₁).map K₁.subtype = P ⊔ Q := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hP, Subgroup.map_subgroupOf_eq_of_le hQ]
  rw [← h2, h, Subgroup.map_top, Subgroup.range_subtype]

theorem Cfg2.invSyl_K2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {D : Subgroup G} (hD : D ≤ K₂)
    (hcard : Nat.card ↥D = 5) (hH : HInv H D) :
    D = XB t X₁ ∨ D = cjL (t * w₁ * t⁻¹) (XB t X₁) := by
  have ht2 : t * t = 1 := c.hs.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hK21 : cjL t K₂ = K₁ := by
    have h1 : cjL t K₁ = K₂ := c.hs.t_swap
    rw [← h1, cjL_cjL, ht2, cjL_one]
  have hD1 : cjL t D ≤ K₁ := by
    have := cjL_mono t hD
    rwa [hK21] at this
  have hH1 : HInv H (cjL t D) := hH.conj c.b66.t_normH
  have hcard1 : Nat.card ↥(cjL t D) = 5 := by rw [card_cjL]; exact hcard
  have hback : D = cjL t (cjL t D) := by rw [cjL_cjL, ht2, cjL_one]
  rcases c.invSyl_K1 hD1 hcard1 hH1 with h | h
  · left
    rw [hback, h]
  · right
    rw [hback, h]
    show cjL t (cjL w₁ X₁) = cjL (t * w₁ * t⁻¹) (cjL t X₁)
    rw [cjL_cjL, cjL_cjL]
    congr 1
    group

theorem Cfg2.isSylowIn_C (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {R : Subgroup G}
    (hR : R ≤ centralizer ({z} : Set G)) (hcard : Nat.card ↥R = 25) :
    IsSylowIn 5 R (centralizer ({z} : Set G)) := by
  refine ⟨hR, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), ?_⟩
  have h1 := Subgroup.index_mul_card (R.subgroupOf (centralizer ({z} : Set G)))
  have h2 : Nat.card ↥(R.subgroupOf (centralizer ({z} : Set G))) = 25 := by
    rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  rw [h2, c.b82.card_C] at h1
  intro h5
  omega

theorem Cfg2.zu_ne_one (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : z * u ≠ 1 := by
  intro h
  apply c.hs.u_ne
  have h2 : u = z⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h2]
  exact inv_eq_of_mul_eq_one_right c.hs.z_sq

omit [Finite G] in
theorem zu_mem_UU (z u : G) : z * u ∈ UU z u :=
  mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers u))

theorem Cfg2.exists_b (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ∃ b ∈ NN z u, b * z * b⁻¹ = z * u :=
  c.b66.N_trans z (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) c.z_ne_one (z * u)
    (zu_mem_UU z u) c.zu_ne_one

theorem Cfg2.W_comm_z (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ w ∈ zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹), w * z = z * w := by
  intro w hw
  have hle : zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹) ≤ centralizer ({z} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (c.hc.cz₁ c.b66.w₁_mem)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (c.hc.cz₂ c.w₂_mem)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem Cfg3.exists_v0 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∃ v₀ ∈ NN z u, v₀ * z * v₀⁻¹ = z * u ∧ cjL v₀ (XX t X₁) = Y := by
  obtain ⟨b, hbN, hb⟩ := c.exists_b
  have hbinv : b⁻¹ ∈ NN z u := inv_mem hbN
  have hYC : cjL b⁻¹ Y ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (MulAut.conj b⁻¹).toMonoidHom y = b⁻¹ * y * b := by simp
    rw [hy']
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h1 : y * (z * u) = (z * u) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (c.b83.Y_syl.1 hy)
    have h2 : b⁻¹ * (z * u) * b = z := by rw [← hb]; group
    calc b⁻¹ * y * b * z = b⁻¹ * y * b * (b⁻¹ * (z * u) * b) := by rw [h2]
      _ = b⁻¹ * (y * (z * u)) * b := by group
      _ = b⁻¹ * ((z * u) * y) * b := by rw [h1]
      _ = (b⁻¹ * (z * u) * b) * (b⁻¹ * y * b) := by group
      _ = z * (b⁻¹ * y * b) := by rw [h2]
  have hcard : Nat.card ↥(cjL b⁻¹ Y) = 25 := by rw [card_cjL]; exact c.b83.Y_card
  have hSyl := c.isSylowIn_C hYC hcard
  have hH : HInv H (cjL b⁻¹ Y) := c.hinv_Y.conj (c.cjL_H hbinv)
  obtain ⟨w, hw, hR⟩ := c.b82.syl_inv _ hSyl hH
  refine ⟨b * w, mul_mem hbN (c.W_le_NN hw), ?_, ?_⟩
  · have hwz : w * z * w⁻¹ = z := by
      have := c.W_comm_z w hw
      calc w * z * w⁻¹ = (z * w) * w⁻¹ := by rw [this]
        _ = z := by group
    calc b * w * z * (b * w)⁻¹ = b * (w * z * w⁻¹) * b⁻¹ := by group
      _ = z * u := by rw [hwz, hb]
  · rw [← cjL_cjL, ← hR, cjL_cjL, mul_inv_cancel, cjL_one]

end L84b

end CFSG.GH74.GLS.LU.Local.Five
