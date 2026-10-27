module

public import CFSG.GH74.GLS.LU.Local.FiveL88g
public import CFSG.GH74.GLS.LU.Local.FiveE31
public import CFSG.GH74.GLS.LU.Local.FiveGasch
public import CFSG.GH74.GLS.LU.Local.FiveL88f

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L88

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg8.card_N_le (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    Nat.card ↥(normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) ≤ 125 * 372000 := by
  have hE : Nat.card ↥(EE v t w₁ X₁) = 125 := by rw [c.E_card c.b86]; norm_num
  have h := card_le_mul_normalizer_of_five (normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G))
    (EE v t w₁ X₁) (XB t X₁) le_rfl hE (c.E_pow c.b86) c.X2_le_E c.card_X2
  rw [inf_eq_right.mpr c.NG_X2_le_N] at h
  have h2 := c.card_NX2_le
  omega

theorem Cfg8.exists_L' (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    ∃ L' : Subgroup G, Five88 z t u K₁ K₂ w₁ X₁ v L' := by
  obtain ⟨phi, hsurj, hker⟩ := c.exists_phi c.card_N_le
  have hE : Nat.card ↥(EE v t w₁ X₁) = 125 := by rw [c.E_card c.b86]; norm_num
  have hN : Nat.card ↥(normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) = 125 * 372000 := by
    have h1 := Subgroup.index_ker phi
    have h2 := Subgroup.index_mul_card phi.ker
    have hk : phi.ker = (EE v t w₁ X₁).subgroupOf (normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) := by
      ext m
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hker m
    have hkcard : Nat.card ↥phi.ker = 125 := by
      rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hE]
    have hrcard : Nat.card ↥phi.range = 372000 := by
      rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, card_sl3_five]
    rw [h1, hkcard, hrcard] at h2
    omega
  have hUH : UU z u ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr c.b66.z_mem) (Subgroup.zpowers_le.mpr c.b66.u_mem)
  have hUN : UU z u ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) :=
    hUH.trans c.H_N
  have hcopU : Nat.Coprime (Nat.card ↥(EE v t w₁ X₁)) (Nat.card ↥(UU z u)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (c.H_two.to_le hUH)
    rw [hE, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hm : Nat.card ↥(normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) =
      2976 * Nat.card ↥(EE v t w₁ X₁ ⊔ DD v w₁ X₁) := by
    rw [hN, c.b87.ED_card]; norm_num
  obtain ⟨L, hLN, hEL, hELN, hUL⟩ := exists_complement_containing_coprime
    (normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) (EE v t w₁ X₁) (DD v w₁ X₁) (UU z u)
    le_rfl Subgroup.le_normalizer (c.E_comm c.b86) c.D_le_N (c.ED_disj c.b86) 2976 hm
    (by rw [hE]; norm_num) hUN hcopU
  refine ⟨L, c.C_E, hLN, hEL, hELN, ?_, hUL, c.K1_N, c.L_N⟩
  let ψ : ↥L →* SL(3, ZMod 5) := phi.comp (Subgroup.inclusion hLN)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : ((Subgroup.inclusion hLN a : ↥(normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G))) : G) ∈
        EE v t w₁ X₁ := (hker _).mp ha
    have hmem' : (a : G) ∈ EE v t w₁ X₁ ⊓ L := ⟨hmem, a.2⟩
    rw [hEL] at hmem'
    exact Subtype.ext (Subgroup.mem_bot.mp hmem')
  have hψsurj : Function.Surjective ψ := by
    intro s
    obtain ⟨m, hm⟩ := hsurj s
    obtain ⟨e, he, l, hl, hel⟩ := exists_mul_of_mem_sup (N := normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G))
      le_rfl Subgroup.le_normalizer hLN hELN m.2
    have he' : e ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := Subgroup.le_normalizer he
    have hl' : l ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := hLN hl
    have hmeq : m = ⟨e, he'⟩ * ⟨l, hl'⟩ := Subtype.ext hel.symm
    refine ⟨⟨l, hl⟩, ?_⟩
    have h1 : phi ⟨e, he'⟩ = 1 := (hker _).mpr he
    show phi (Subgroup.inclusion hLN ⟨l, hl⟩) = s
    rw [← hm, hmeq, map_mul, h1, one_mul]
    rfl
  exact ⟨(MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).symm⟩

theorem leaf88 : Leaf88 := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85 b86 b87
  have c0 : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v := ⟨⟨⟨⟨ctx, b66, b82⟩, b83⟩, b84⟩, b85⟩
  exact (⟨c0, b86, b87⟩ : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v).exists_L'

end L88

end CFSG.GH74.GLS.LU.Local.Five
