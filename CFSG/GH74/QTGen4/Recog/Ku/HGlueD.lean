module

public import CFSG.GH74.QTGen4.Recog.Ku.HGlue
public import CFSG.GH74.QTGen4.Recog.Ku.S5Abelian

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem card_pCore_M_inf_pCore_H_le [KuLeaf LeafEqKuAOfElemAbelian]
    (h : KuHyp G T M H P z) :
    Nat.card ↥(pCoreOf 2 M ⊓ pCoreOf 2 H) ≤ 8 := by
  have hd : Nat.card ↥(pCoreOf 2 M ⊓ pCoreOf 2 H) ∣ 16 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : pCoreOf 2 M ⊓ pCoreOf 2 H ≤ pCoreOf 2 M)
    rwa [h.vCard] at this
  by_contra hc
  have hle16 : Nat.card ↥(pCoreOf 2 M ⊓ pCoreOf 2 H) ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  have h16 : Nat.card ↥(pCoreOf 2 M ⊓ pCoreOf 2 H) = 16 := by
    have key16 : ∀ n < 17, n ∣ 16 → 8 < n → n = 16 := by decide
    exact key16 _ (by omega) hd (by omega)
  have hVQ' : pCoreOf 2 M ⊓ pCoreOf 2 H = pCoreOf 2 M :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by have := h.vCard; omega)
  apply h.not_pCore_M_le_pCore_H
  calc pCoreOf 2 M = pCoreOf 2 M ⊓ pCoreOf 2 H := hVQ'.symm
    _ ≤ pCoreOf 2 H := inf_le_right

omit [Finite G] in
theorem card_P (h : KuHyp G T M H P z) : Nat.card ↥P = 32 := by
  have hc := h.pExtra.2.1
  norm_num at hc
  exact hc

theorem card_pCore_M_inf_P [KuLeaf LeafEqKuAOfElemAbelian]
    (h : KuHyp G T M H P z) :
    Nat.card ↥(pCoreOf 2 M ⊓ P) = 8 := by
  have hPM : P ≤ M := h.P_le_T.trans h.tM
  obtain ⟨φ, -, hφker⟩ := h.mQuot
  let ψ : ↥P →* Equiv.Perm (Fin 5) := φ.comp (Subgroup.inclusion hPM)
  have hzV : z ∈ pCoreOf 2 M := h.z_mem_pCoreOf
  have hkerV : ∀ x : ↥M, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 M := by
    intro x
    rw [← MonoidHom.mem_ker, hφker, Subgroup.mem_subgroupOf]
  have hψ_ker : ∀ p : ↥P, ψ p = 1 ↔ (p : G) ∈ pCoreOf 2 M :=
    fun p => hkerV (Subgroup.inclusion hPM p)
  have hmap : ψ.ker.map P.subtype = pCoreOf 2 M ⊓ P := by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(hψ_ker p).mp (MonoidHom.mem_ker.mp hp), p.2⟩
    · rintro ⟨hV, hP⟩
      exact ⟨⟨g, hP⟩, MonoidHom.mem_ker.mpr ((hψ_ker ⟨g, hP⟩).mpr hV), rfl⟩
  have hcardmap : Nat.card ↥(ψ.ker.map P.subtype) = Nat.card ψ.ker :=
    Subgroup.card_map_of_injective (f := P.subtype) Subtype.val_injective
  rw [hmap] at hcardmap
  have hidx_range : ψ.ker.index = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hidx : Nat.card ψ.ker * Nat.card ψ.range = 32 := by
    have := Subgroup.card_mul_index ψ.ker
    rw [hidx_range, h.card_P] at this
    exact this
  have hnk : Nat.card ↥(pCoreOf 2 M ⊓ P) * Nat.card ψ.range = 32 := by
    rw [hcardmap]
    exact hidx
  have hk120 : Nat.card ψ.range ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [card_perm_fin5] at this
  have hk32 : Nat.card ψ.range ∣ 32 := Dvd.intro_left _ hnk
  have hk33 : Nat.card ψ.range < 33 := by
    have := Nat.le_of_dvd (by norm_num) hk32
    omega
  have hcomm : ∀ p q : ↥P, ψ p * ψ q = ψ q * ψ p := by
    intro p q
    have e : (QuotientGroup.mk p : ↥P ⧸ Subgroup.center ↥P) * QuotientGroup.mk q
        = QuotientGroup.mk q * QuotientGroup.mk p := h.quot_P_comm _ _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at e
    have hmem : (p * q)⁻¹ * (q * p) ∈ Subgroup.center ↥P := QuotientGroup.eq.mp e
    rw [h.center_P_eq] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hw : ψ (⟨z, h.zP_mem⟩ : ↥P) = 1 := (hψ_ker (⟨z, h.zP_mem⟩ : ↥P)).mpr hzV
    have h1 : ψ ((p * q)⁻¹ * (q * p)) = 1 := by
      rw [← hk, map_zpow, hw, one_zpow]
    simp only [map_mul, map_inv] at h1
    exact inv_mul_eq_one.mp h1
  have hKcomm : IsMulCommutative ψ.range := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp b.2
    show (a : Equiv.Perm (Fin 5)) * (b : Equiv.Perm (Fin 5))
        = (b : Equiv.Perm (Fin 5)) * (a : Equiv.Perm (Fin 5))
    rw [← hp, ← hq]
    exact hcomm p q
  have hle8 : Nat.card ↥(pCoreOf 2 M ⊓ P) ≤ 8 := by
    have hsub : pCoreOf 2 M ⊓ P ≤ pCoreOf 2 M ⊓ pCoreOf 2 H :=
      inf_le_inf_left _ h.P_le_pCore_H
    have := Subgroup.card_le_of_le hsub
    have h8 := h.card_pCore_M_inf_pCore_H_le
    omega
  have hn9 : Nat.card ↥(pCoreOf 2 M ⊓ P) < 9 := by omega
  have key : ∀ n < 9, ∀ k < 33, n * k = 32 → k ∣ 120 → n = 8 ∨ n = 4 := by decide
  rcases key _ hn9 _ hk33 hnk hk120 with h8 | h4
  · exact h8
  · exfalso
    have hk8 : Nat.card ψ.range = 8 := by
      rw [h4] at hnk
      omega
    exact not_isMulCommutative_of_card_eq_eight_perm5 ψ.range hk8 hKcomm

end KuHyp

end CFSG.GH74.QTGen4.Ku
