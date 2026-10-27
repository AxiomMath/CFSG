module

public import CFSG.GH74.GLS.LU.Local.FiveW
public import CFSG.GH74.GLS.LU.Local.FiveCfg2

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

structure Cfg2W (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G)
    (K₁ K₂ : Subgroup G) (t u : G) (H : Subgroup G) (w₁ : G) (X₁ : Subgroup G) : Prop where
  ctx : FiveCtx G p f z S K₁ K₂ t u
  b66 : Five66W z t u K₁ K₂ H w₁
  b82 : Five82W z t u K₁ K₂ H w₁ X₁

section CfgW

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2W.hc (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : LUComps G (p ^ f) z K₁ K₂ := c.ctx.hyp.1

theorem Cfg2W.hs (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : LUSyl G z S K₁ K₂ t u := c.ctx.hyp.2.1

theorem Cfg2W.t_sq (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : t * t = 1 := c.hs.t_sq

theorem Cfg2W.z_sq (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : z * z = 1 := c.hs.z_sq

theorem Cfg2W.hinv_X1 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : HInv H X₁ := c.b82.H_normX₁

theorem Cfg2W.hinv_X2 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : HInv H (XB t X₁) :=
  c.hinv_X1.conj c.b66.t_normH

theorem Cfg2W.hinv_XX (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : HInv H (XX t X₁) :=
  c.hinv_X1.sup c.hinv_X2

theorem Cfg2W.card_X1 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥X₁ = 5 := c.b82.X₁_card

theorem Cfg2W.card_X2 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥(XB t X₁) = 5 :=
  (card_cjL t X₁).trans c.card_X1

theorem Cfg2W.X2_le_K2 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : XB t X₁ ≤ K₂ := by
  have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) c.b82.X₁_syl.1
  rwa [c.hs.t_swap] at this

theorem Cfg2W.t_XX (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : cjL t (XX t X₁) = XX t X₁ := by
  have h : cjL t (cjL t X₁) = X₁ := by rw [cjL_cjL, c.t_sq, cjL_one]
  rw [XX, cjL_sup, h, sup_comm]

theorem Cfg2W.zu_conj (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : IsConj z (z * u) := by
  have h := c.hs.uz_conj
  rwa [show u * z = z * u from c.hs.zu_comm.symm] at h

theorem Cfg2W.z_ne_one (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : z ≠ 1 := by
  intro h
  have := c.hs.z_inv
  rw [h, orderOf_one] at this
  omega

theorem Cfg2W.card_cent_of_conj (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) {a : G} (ha : IsConj z a) :
    Nat.card ↥(centralizer ({a} : Set G)) = 28800 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  have : cjL g (centralizer ({z} : Set G)) = centralizer ({a} : Set G) := by
    ext x
    rw [mem_cjL, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← hg]
    constructor
    · intro h
      calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
        _ = (g * z * g⁻¹) * x := by group
    · intro h
      calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
        _ = z * (g⁻¹ * x * g) := by group
  rw [← this, card_cjL]
  exact c.b82.card_C

theorem Cfg2W.K1_inf_K2_sq (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ x ∈ K₁ ⊓ K₂, x * x = 1 := by
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (c.hc.comm g g.2 x hx.2)
  have hz : x ∈ zpowers z := by
    rw [← c.hc.cen₁]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  rcases mem_zpowers_of_sq_eq_one c.z_sq hz with h | h
  · rw [h]; simp
  · rw [h]; exact c.z_sq

theorem Cfg2W.five_inf_K2 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) {A : Subgroup G} (hA : A ≤ K₁)
    (hcard : Nat.card ↥A = 5) : A ⊓ K₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx5 : x ^ 5 = 1 := pow_five_of_card hcard hx.1
  have hxx : x * x = 1 := c.K1_inf_K2_sq x ⟨hA hx.1, hx.2⟩
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hxx
  have : x = 1 := by
    calc x = x ^ 5 * (x ^ 2)⁻¹ * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx5, hx2]; simp
  rw [this]; exact Subgroup.one_mem _

theorem Cfg2W.isConj_of_invol (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) {i : G} (hi : orderOf i = 2) :
    IsConj z i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(zpowers i) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hi]; norm_num)
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hmem : g * i * g⁻¹ ∈ (S : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul i (MulAut.conj g) (P : Subgroup G)
      (hP' (mem_zpowers i))
    simpa using this
  have hord : orderOf (g * i * g⁻¹) = 2 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective i
    have e : (MulAut.conj g).toMonoidHom i = g * i * g⁻¹ := by simp
    rw [e] at h
    rw [h, hi]
  have h1 := c.ctx.extra.fusion _ hmem hord
  exact h1.trans (isConj_iff.mpr ⟨g, rfl⟩).symm

end CfgW

end CFSG.GH74.GLS.LU.Local.Five
