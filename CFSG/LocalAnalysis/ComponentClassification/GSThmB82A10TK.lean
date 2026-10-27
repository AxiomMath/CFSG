module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TNC
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCases

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

abbrev fixR : Finset (Fin 10) := {0, 1, 2, 3, 4, 5, 6, 7}

private theorem mem_fixR_of_r0 : ∀ i : Fin 10, r0 i = i → i ∈ fixR := by
  decide

private theorem r0_of_mem_fixR : ∀ i : Fin 10, i ∈ fixR → r0 i = i := by
  decide

private theorem card_fusionZStar_conjugate (M : Subgroup X) (g : X) :
    Nat.card (↥(conjugate M g) ⧸ Open.fusionZStar ↥(conjugate M g)) =
      Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
  (Nat.card_congr (Sol78.fusionZStarQuotCongr (M.equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)).toEquiv).symm

private theorem card_of_isRep {N Y : Subgroup X} {φ : ↥N →* Perm (Fin 10)}
    (h : IsRep φ Y (altOn fixR)) : Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = 20160 := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have h8 : 4 ≤ Nat.card ↥fixR := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  have hZ : center (↥Y ⧸ pPrimeCore 2 ↥Y) = ⊥ := by
    let e' := e.trans (altOnEquiv fixR).symm
    have h1 := Subgroup.map_center_eq e'
    rw [alternatingGroup.center_eq_bot h8] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1
  rw [fusionZStar_eq_of_center_eq_bot hZ, Nat.card_congr e.toEquiv, card_altOn _ (by decide)]
  decide

namespace Ctx

variable (c : Ctx X)

structure CaseIIIp where
  d : c.PropBData
  hw : c.φ ⟨d.z', d.z'_mem_secSub⟩ = r0
  ha : c.φ ⟨d.a', d.a'_mem_secSub⟩ = sigmaTwo * z0 * r0
  A8 : Subgroup X
  A8_le : A8 ≤ Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.z'} : Set X)
  isPComponent_A8 : IsPComponent 2 (A8.subgroupOf
    (centralizer ({d.z'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X)))
  isRep_A8 : IsRep c.φ A8 (altOn fixR)
  K : Subgroup X
  K_le : K ≤ centralizer ({d.z'} : Set X)
  isPComponent_K : IsPComponent 2 (K.subgroupOf (centralizer ({d.z'} : Set X)))
  A8_le_K : A8 ≤ K

variable {c} in
private theorem secB0_le_centralizer_z' (d : c.PropBData) :
    c.s.h.secB0 c.s.y ≤ centralizer ({d.z'} : Set X) := fun b hb =>
  mem_centralizer_singleton_iff.mpr (d.comm_S0 _ (Set.mem_insert_of_mem _ rfl) b
    (mem_inf.mpr ⟨c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hb), le_normalizer hb⟩))

variable {c} in
private theorem isPGroup_zpowers_z' (d : c.PropBData) : IsPGroup 2 (zpowers d.z') :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact d.z'_mul_self))

variable {c} in
private theorem conjugate_centralizer_z' (d : c.PropBData) :
    conjugate (centralizer ({d.z'} : Set X)) d.g⁻¹ = centralizer ({c.Z.z} : Set X) := by
  have h : d.g⁻¹⁻¹ * d.z' * d.g⁻¹ = c.Z.z := by
    show d.g⁻¹⁻¹ * (d.g⁻¹ * c.Z.z * d.g) * d.g⁻¹ = c.Z.z
    group
  rw [conjugate_centralizer_singleton, h]

variable {c} in
private theorem Lay_inf_le (d : c.PropBData) :
    Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.z'} : Set X) ≤
      centralizer ({d.z'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) :=
  le_inf inf_le_right (inf_le_left.trans (Seven.Lay_le_centralizer_secB0 _ _))

variable {c} in
private theorem exists_natural (d : c.PropBData) (hw : c.φ ⟨d.z', d.z'_mem_secSub⟩ = r0) :
    ∃ Y : Subgroup X, Y ≤ Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.z'} : Set X) ∧
      IsPComponent 2 (Y.subgroupOf (Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.z'} : Set X))) ∧
      IsRep c.φ Y (altOn fixR) ∧
      (∀ Y' : Subgroup X, Y' ≤ Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.z'} : Set X) →
        IsPComponent 2 (Y'.subgroupOf (Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.z'} : Set X))) →
          Y' = Y) ∧
      ∀ u ∈ c.s.h.secSub c.s.y, u ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) →
        u ∈ centralizer ({d.z'} : Set X) → u ∈ normalizer (Y : Set X) := by
  have hzL : d.z' ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) :=
    Seven.secG0_le_normalizer_Lay _ _ (mem_inf.mp d.z'_mem_S0).2
  have hEN : zpowers d.z' ≤ c.s.h.secSub c.s.y := zpowers_le.mpr d.z'_mem_secSub
  have hφpow : ∀ k : ℤ, c.φ ⟨d.z' ^ k, hEN (zpow_mem (mem_zpowers _) k)⟩ = r0 ^ k := by
    intro k
    rw [← hw, ← map_zpow]
    rfl
  have hΔ : ∀ i, (∀ e (he : e ∈ zpowers d.z'), c.φ ⟨e, hEN he⟩ i = i) ↔ i ∈ fixR := by
    intro i
    constructor
    · intro h
      have h1 := h d.z' (mem_zpowers _)
      rw [hw] at h1
      exact mem_fixR_of_r0 i h1
    · intro hi e he
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
      rw [hφpow k]
      exact zpow_apply_eq_self_of_apply_eq_self (r0_of_mem_fixR i hi) k
  obtain ⟨Y, hYC, hYpc, hYrep, -, huniq, hYN⟩ := exists_natural_component c.isRep_Lay hEN
    (zpowers_le.mpr hzL) (isPGroup_zpowers_z' d) hΔ (by decide)
  rw [UnbalancedLayer.centralizer_zpowers_eq] at hYC hYpc huniq
  refine ⟨Y, hYC, hYpc, hYrep, huniq, fun u huH huL huw => hYN ?_⟩
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨huH, huL⟩, centralizer_le_normalizer _ ?_⟩
  rw [UnbalancedLayer.centralizer_zpowers_eq]
  exact huw

variable {c} in
theorem PropBData.exists_caseIIIp
    (d : c.PropBData) (hw : c.φ ⟨d.z', d.z'_mem_secSub⟩ = r0)
    (ha : c.φ ⟨d.a', d.a'_mem_secSub⟩ = sigmaTwo * z0 * r0) :
    ∃ e : c.CaseIIIp, e.d = d := by
  have hG0L : c.s.h.secG0 c.s.y ≤ normalizer (Seven.Lay c.s.h c.s.y : Set X) :=
    Seven.secG0_le_normalizer_Lay _ _
  obtain ⟨Y, hYC, hYpc, hYrep, -, -⟩ := exists_natural d hw
  have hUV := Lay_inf_le d
  have hUn : ((Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.z'} : Set X)).subgroupOf
      (centralizer ({d.z'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X))).Normal := by
    rw [normal_subgroupOf_iff hUV]
    intro h k hh hk
    obtain ⟨hhL, hha⟩ := mem_inf.mp hh
    obtain ⟨hka, hkB⟩ := mem_inf.mp hk
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hG0L (centralizer_le_normalizer _ hkB)) h).mp hhL,
      mul_mem (mul_mem hka hha) (inv_mem hka)⟩
  have hY := isPComponent_of_le_of_subnormal hYC hUV hUn.isSubnormal hYpc
  have hYC' := hYC.trans hUV
  have hYlay : Y ≤ layerIn (centralizer ({d.z'} : Set X)) :=
    le_layerIn_of_isPComponent_inf_centralizer (c.s.h.isPGroup_secB0 c.s.y)
      ((secB0_le_centralizer_z' d).trans le_normalizer) hYC' hY
  have hYz : conjugate Y d.g⁻¹ ≤ layerIn (centralizer ({c.Z.z} : Set X)) := by
    rw [← conjugate_centralizer_z' d, ← B5a.conjugate_layerIn_eq]
    exact map_mono hYlay
  obtain ⟨hYg, hYgpc⟩ := Six.isPComponent_conjugate hYC' hY d.g⁻¹
  have h64 : 64 ∣ Nat.card (↥(conjugate Y d.g⁻¹) ⧸ Open.fusionZStar ↥(conjugate Y d.g⁻¹)) := by
    rw [card_fusionZStar_conjugate, card_of_isRep hYrep]
    norm_num
  obtain ⟨Js, hJsC, hJs, -, hYJs, -, -⟩ := c.exists_Jstar hYz
    (isPerfect_of_isPComponent hYg hYgpc) (isQuasisimple_of_isPComponent hYg hYgpc) h64
  obtain ⟨hK1, hK2⟩ := Six.isPComponent_conjugate hJsC hJs d.g
  rw [conjugate_centralizer_singleton] at hK1 hK2
  refine ⟨⟨d, hw, ha, Y, hYC, hY, hYrep, conjugate Js d.g, hK1, hK2, ?_⟩, rfl⟩
  calc Y = conjugate (conjugate Y d.g⁻¹) d.g := by
        rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
    _ ≤ conjugate Js d.g := map_mono hYJs

namespace CaseIIIp

variable {c} (e : c.CaseIIIp)

abbrev w : X := e.d.z'

theorem kGroup_centralizer_w : SectionRank.IsKGroupCat ↥(centralizer ({e.w} : Set X)) := by
  have hw1 : e.d.z' ≠ 1 := fun h => c.Z.hz1 (by
    have h1 : c.Z.z = e.d.g * e.d.z' * e.d.g⁻¹ := by
      show c.Z.z = e.d.g * (e.d.g⁻¹ * c.Z.z * e.d.g) * e.d.g⁻¹
      group
    rw [h1, h, mul_one, mul_inv_cancel])
  have h := c.kGroup_centralizer (F := zpowers e.d.z') (by rwa [Ne, zpowers_eq_bot])
    (isPGroup_zpowers_z' e.d)
  rwa [UnbalancedLayer.centralizer_zpowers_eq] at h

theorem secB0_le_centralizer_w : c.s.h.secB0 c.s.y ≤ centralizer ({e.w} : Set X) :=
  secB0_le_centralizer_z' e.d

private theorem isPComponent_A8_Lay : IsPComponent 2 (e.A8.subgroupOf
    (Seven.Lay c.s.h c.s.y ⊓ centralizer ({e.d.z'} : Set X))) :=
  isPComponent_of_le_of_le e.A8_le (Lay_inf_le e.d) e.isPComponent_A8

theorem mem_normalizer_K {u : X} (huw : u ∈ centralizer ({e.w} : Set X))
    (huA : u ∈ normalizer (e.A8 : Set X)) : u ∈ normalizer (e.K : Set X) := by
  obtain ⟨h1, h2⟩ := A10T.isPComponent_conjugate (le_normalizer huw) e.K_le e.isPComponent_K
  have hA : e.A8 ≤ conjugate e.K u :=
    calc e.A8 = conjugate e.A8 u := (conjugate_eq_of_mem_normalizer huA).symm
      _ ≤ conjugate e.K u := map_mono e.A8_le_K
  have hns : ¬ Group.IsSolvable ↥e.A8 := not_isSolvable_of_isQuasisimple
    (isQuasisimple_of_isPComponent (e.A8_le.trans (Lay_inf_le e.d)) e.isPComponent_A8)
  exact mem_normalizer_of_conjugate_eq
    (eq_of_le_of_le_of_not_isSolvable h1 e.K_le h2 e.isPComponent_K hA e.A8_le_K hns)

theorem mem_normalizer_A8 {u : X} (huH : u ∈ c.s.h.secSub c.s.y)
    (huL : u ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X))
    (huw : u ∈ centralizer ({e.w} : Set X)) : u ∈ normalizer (e.A8 : Set X) := by
  obtain ⟨Y₀, -, -, -, huniq, hN⟩ := exists_natural e.d e.hw
  rw [huniq e.A8 e.A8_le e.isPComponent_A8_Lay]
  exact hN u huH huL huw

theorem secB0_le_normalizer_K : c.s.h.secB0 c.s.y ≤ normalizer (e.K : Set X) := fun b hb =>
  e.mem_normalizer_K (e.secB0_le_centralizer_w hb)
    (e.mem_normalizer_A8 (c.s.h.secB0_le_secSub c.s.y hb)
      (Seven.secG0_le_normalizer_Lay _ _ (le_normalizer hb)) (e.secB0_le_centralizer_w hb))

theorem card_A8 : Nat.card (↥e.A8 ⧸ Open.fusionZStar ↥e.A8) = 20160 :=
  card_of_isRep e.isRep_A8

theorem nonempty_pPrimeCore_equiv_of_fusionZStar {m : ℕ} (hm : 8 ≤ m)
    (eK : ↥e.K ⧸ Open.fusionZStar ↥e.K ≃* alternatingGroup (Fin m)) :
    Nonempty (↥e.K ⧸ pPrimeCore 2 ↥e.K ≃* alternatingGroup (Fin m)) := by
  obtain ⟨eA⟩ := e.isRep_A8.nonempty_equiv
  have h8 : Fintype.card ↥fixR = 8 := by
    rw [Fintype.card_coe]
    decide
  exact nonempty_pPrimeCore_equiv_alt_of_fixed' e.K_le e.isPComponent_K e.secB0_le_centralizer_w
    (c.s.h.isPGroup_secB0 c.s.y) e.secB0_le_normalizer_K e.A8_le_K
    (e.A8_le.trans (inf_le_left.trans (Seven.Lay_le_centralizer_secB0 _ _))) e.isPComponent_A8
    (by norm_num) ((eA.trans (altOnEquiv fixR).symm).trans
      (Fintype.equivFinOfCardEq h8).altCongrHom) hm eK

theorem jstarData {m : ℕ}
    (hm : 7 ≤ m) (eK : ↥e.K ⧸ pPrimeCore 2 ↥e.K ≃* alternatingGroup (Fin m)) :
    Nonempty c.JstarData := by
  obtain ⟨hJsC, hJs⟩ := Six.isPComponent_conjugate e.K_le e.isPComponent_K e.d.g⁻¹
  rw [conjugate_centralizer_z' e.d] at hJsC hJs
  obtain ⟨hYg, hYgpc⟩ := Six.isPComponent_conjugate (e.A8_le.trans (Lay_inf_le e.d))
    e.isPComponent_A8 e.d.g⁻¹
  have hYJs : conjugate e.A8 e.d.g⁻¹ ≤ conjugate e.K e.d.g⁻¹ := map_mono e.A8_le_K
  have h64 : 64 ∣ Nat.card (↥(conjugate e.A8 e.d.g⁻¹) ⧸
      Open.fusionZStar ↥(conjugate e.A8 e.d.g⁻¹)) := by
    rw [card_fusionZStar_conjugate, e.card_A8]
    norm_num
  have hYq := isQuasisimple_of_isPComponent hYg hYgpc
  obtain ⟨Js', hJs'C, hJs', hJ0, hYJs', hx, -⟩ :=
    c.exists_Jstar (hYJs.trans (le_layerIn_of_isPComponent hJsC hJs))
      (isPerfect_of_isPComponent hYg hYgpc) hYq h64
  have heq : conjugate e.K e.d.g⁻¹ = Js' := eq_of_le_of_le_of_not_isSolvable hJsC hJs'C hJs hJs'
    hYJs hYJs' (not_isSolvable_of_isQuasisimple hYq)
  rw [← heq] at hJ0 hx
  let ψ : ↥e.K ≃* ↥(conjugate e.K e.d.g⁻¹) := e.K.equivMapOfInjective
    (MulAut.conj e.d.g⁻¹⁻¹).toMonoidHom (MulAut.conj e.d.g⁻¹⁻¹).injective
  exact ⟨⟨conjugate e.K e.d.g⁻¹, hJsC, hJs, hJ0, hx, m, hm,
    ⟨(Sol78.coreQuotCongr ψ).symm.trans eK⟩⟩⟩

end CaseIIIp

end Ctx

end CFSG.ComponentClassification.GSThmB.A10T
