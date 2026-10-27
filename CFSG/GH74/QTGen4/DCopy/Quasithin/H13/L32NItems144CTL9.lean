module

public import CFSG.Quasithin.H13.L32NItems144CTL9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem mem_M_of_conj_F4 (h331 : Stmt3_3_1_F4) (h13322 : Stmt13_3_2_two_F4) {h : G}
    (hT : T ≤ Subgroup.normalizer ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)) :
    h ∈ Subgroup.normalizer (L : Set G) := by
  have hT'N : T.map (MulAut.conj h⁻¹).toMonoidHom ≤ Subgroup.normalizer (V : Set G) := by
    have := conj_T_le_normalizer hT h⁻¹
    rwa [map_conj_inv_map_conj] at this
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans S.normV
  have hidx : (T.map (MulAut.conj h⁻¹).toMonoidHom).index = T.index := by
    have h1 := Subgroup.card_mul_index (T.map (MulAut.conj h⁻¹).toMonoidHom)
    rw [card_map_conj] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans (Subgroup.card_mul_index T).symm)
  have hT'syl : quasithinIsSylowTwo (T.map (MulAut.conj h⁻¹).toMonoidHom) :=
    ⟨S.hyp.fsu.sylow.1.map _, by rw [hidx]; exact S.hyp.fsu.sylow.2⟩
  obtain ⟨n, hn, hconj⟩ := A4.exists_conj_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTN)
    (isSylowTwoOf_of_quasithinIsSylowTwo hT'syl hT'N)
  have hmem : ∀ x, x ∈ T ↔ h⁻¹ * x * h ∈ T.map (MulAut.conj h⁻¹).toMonoidHom := fun x => by
    constructor
    · intro hx
      exact ⟨x, hx, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hyx
      exact (by simpa using hyx : y = x) ▸ hy

  have hNT : n⁻¹ * h⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [show n⁻¹ * h⁻¹ * x * (n⁻¹ * h⁻¹)⁻¹ = n⁻¹ * (h⁻¹ * x * h) * n by group, hmem x]
    exact hconj _
  have hNTM : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hL13 := h13322 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful
    exact (h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow).1 _ L
      hL13.2.2.1 hL13.1 S.hyp.fsu.maximal Subgroup.le_normalizer S.hyp.fsu.quasisimple
  have h2 := (Subgroup.normalizer (L : Set G)).mul_mem (S.normVL hn) (hNTM hNT)
  rw [show n * (n⁻¹ * h⁻¹) = h⁻¹ by group] at h2
  simpa using (Subgroup.normalizer (L : Set G)).inv_mem h2

end Setup

end L1444CTL

end CFSG.Quasithin.H13
