module

public import CFSG.Quasithin.MS93.S33Trans
public import CFSG.GH74.SectionalRank
public import CFSG.Quasithin.MS93.S34DAsm
public import CFSG.Quasithin.MS93.S45M0

public section

namespace CFSG.GH74.QTGen4.ThmE

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.GH74 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93.S45 CFSG.Quasithin.MS93.S34D
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem card_Xq_le (hG : Gen4 G) (h : PUHyp M T L) : Nat.card (Xq M) ≤ 2 ^ 4 :=
  SectionalTwoRankLE.card_le_of_elementary hG (Xq M) h.isElemAbelian_Xq

theorem card_Uq_le (hG : Gen4 G) (h : PUHyp M T L) : Nat.card (Uq M T L) ≤ 2 ^ 4 :=
  (Subgroup.card_le_of_le h.Uq_le_Xq).trans (card_Xq_le hG h)

theorem sl3Full_of_sl3U_gen4 (hG : Gen4 G) (h : PUHyp M T L) (hU : IsSL3U M T L) :
    IsSL3Full M T L := by
  obtain ⟨hX, hZU, n, F, _, _, α, hcard, hα, hLV, -, β, hβ, hβker, hβα⟩ := hU
  have hbot : T ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  by_cases hn : 2 ≤ n
  · exfalso
    have hinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    have hcardU : Nat.card (Uq M T L) = Fintype.card F ^ 3 := by
      rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβ⟩), Nat.card_eq_fintype_card]
      simp
    have := card_Uq_le hG h
    rw [hcardU, hcard, ← pow_mul] at this
    have h8 : 2 ^ 4 < 2 ^ (n * 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact S34R.sl3Full_of_le_linPart h hcard hα hX hZU hβ hβker hβα
      (S34R.le_linPart_of_card_two h (S34R.card_eq_two_of_lt hcard (by omega)) hβ hβker hbot)

theorem sp4Full_of_sp4U_gen4 (hG : Gen4 G) (h : PUHyp M T L) (hU : IsSp4U M T L) :
    IsSp4Full M T L := by
  rcases hU with ⟨k, F, _, _, α, hk, hcard, hα, hLV, hZV, β, hβ, hβker, hβα⟩ | ⟨α, hα, hnat⟩
  · exfalso
    have hle : Fintype.card F ^ 4 ≤ Nat.card (Uq M T L) := by
      have := Nat.card_le_card_of_surjective β hβ
      simpa [Nat.card_eq_fintype_card] using this
    have := card_Uq_le hG h
    rw [hcard, ← pow_mul] at hle
    have h8 : 2 ^ 4 < 2 ^ (k * 4) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact ⟨1, ZMod 2, inferInstance, inferInstance, α, le_rfl, by simp, hα, hnat⟩

theorem card_zloc (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    Nat.card (Zloc h.le L δ) = Nat.card (Zq M L) := by
  obtain ⟨g, rfl⟩ := (PU.isMVtx_iff _).1 hδ
  rw [zloc_smul h, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have : Zloc h.le L (baseA (puAmalgam h.le)) = imM h.le (Zq M L) :=
    puTrans_baseA h.le (S4A.Zq_normal h)
  rw [this, S33.card_imM h.le Zq_le]

theorem card_Zq_mul_card_Uq_le (h : PUHyp M T L) (hX : Xq M = Zq M L ⊔ Uq M T L)
    (hZU : Zq M L ⊓ Uq M T L = ⊥) :
    Nat.card (Zq M L) * Nat.card (Uq M T L) ≤ Nat.card (Xq M) := by
  have hnorm : Uq M T L ≤ Subgroup.normalizer (Zq M L : Set G) :=
    (Uq_le h.L_le).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer Zq_le).1
      (S4A.Zq_normal h))
  have := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (Zq M L) (Uq M T L)
    hnorm (disjoint_iff.mpr hZU)
  rw [← this, ← hX]

variable {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}

theorem false_of_ctx_gen4 (hG : Gen4 G) (c : Ctx M T L φ)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) (hN : 16 ≤ N) :
    False := by
  have h := c.hyp
  obtain ⟨⟨n, hn⟩, hφ, hX, hZU, hnat⟩ := c.via
  obtain ⟨hMV, -, β, hβ, hβker, hβφ⟩ := hnat
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hcardU : Nat.card (Uq M T L) = Fintype.card F ^ 3 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβ⟩), Nat.card_eq_fintype_card]
    simp
  have h1 := card_Zq_mul_card_Uq_le h hX hZU
  have h2 := card_Xq_le hG h
  have hM : IsMVtx (puAmalgam h.le) (p (4 + 6)) :=
    c.isMVtx_of_isGoodPath hp (k := 4 + 6) (by omega) (by decide)
  have hH := c.card_hloc hp (x := 4) (by decide) le_rfl (by omega)
  have hHZ : Hloc h.le L (p (4 + 6)) ≤ Zloc h.le L (p (4 + 6)) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv (p (4 + 6))) le_rfl).trans
      (c.commutator_vv_qv_le_zloc hM)
  have : Finite (Zloc h.le L (p (4 + 6))) :=
    Nat.finite_of_card_ne_zero (by rw [card_zloc h hM]; exact Nat.card_pos.ne')
  have h3 := Subgroup.card_le_of_le hHZ
  rw [hH, card_zloc h hM] at h3
  have hF2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [hcardU] at h1
  have h4 : Fintype.card F ^ 2 * Fintype.card F ^ 3 ≤ Nat.card (Zq M L) * Fintype.card F ^ 3 :=
    Nat.mul_le_mul_right _ h3
  have h5 : 2 ^ 5 ≤ Fintype.card F ^ 2 * Fintype.card F ^ 3 := by
    rw [← pow_add]
    exact Nat.pow_le_pow_left hF2 5
  omega

end CFSG.GH74.QTGen4.ThmE
