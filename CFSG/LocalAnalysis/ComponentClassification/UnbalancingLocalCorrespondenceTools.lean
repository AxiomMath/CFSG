module

public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace Correspondence

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem card_quotient_pPrimeCore_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (X ⧸ pPrimeCore p X) = Nat.card (Y ⧸ pPrimeCore p Y) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (pPrimeCore_map_iso p e)).toEquiv

@[expose] def quotientPPrimeCoreCongr {X Y : Type*} [Group X] [Group Y] (p : ℕ) (e : X ≃* Y) :
    X ⧸ pPrimeCore p X ≃* Y ⧸ pPrimeCore p Y :=
  QuotientGroup.congr _ _ e (pPrimeCore_map_iso p e)

omit [Fact p.Prime] in
theorem quotientPPrimeCoreCongr_mk {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    quotientPPrimeCoreCongr p e (x : X ⧸ pPrimeCore p X) = ((e x : Y) : Y ⧸ pPrimeCore p Y) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem map_pLayer_of_coprime_kernel {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker) :
    (pLayer X p).map f = pLayer Y p := by
  obtain ⟨hbij, -, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hf hker
  rw [pLayer, pLayer, (gc_map_comap f).l_sSup]
  apply le_antisymm
  · exact iSup₂_le fun L hL => le_sSup (hbij.mapsTo hL)
  · refine sSup_le fun M hM => ?_
    obtain ⟨L, hL, rfl⟩ := hbij.surjOn hM
    exact le_iSup₂_of_le L hL le_rfl

theorem exists_quotient_equiv_of_coprime_kernel {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] (f : X →* Y) (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker)
    (hY : pPrimeCore p Y = ⊥) :
    pPrimeCore p X = f.ker ∧ ∃ e : X ⧸ pPrimeCore p X ≃* Y, ∀ x : X, e x = f x := by
  have h := (prime_complement_kernel_core_preimage f hf hker).1
  rw [hY, MonoidHom.comap_bot] at h
  exact ⟨h.symm, (QuotientGroup.quotientMulEquivOfEq h.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), fun x => rfl⟩

theorem card_gsFixedLayer_quotient {G : Type*} [Group G] [Finite G] {a b : G}
    {J L : Subgroup G} (h : GSCorr a J b L) :
    Nat.card (gsFixedLayer J b ⧸ pPrimeCore 2 (gsFixedLayer J b)) =
      Nat.card (J ⧸ pPrimeCore 2 J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hbo, -, hJa, hJcomp, -, -, hbN, hcomm, -⟩ := h
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJcomp).2.2
  have hbb : b * b = 1 := by rw [← sq, ← hbo, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hzp : ∀ c ∈ zpowers b, c = 1 ∨ c = b := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hbb, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hbb, one_zpow, one_mul, zpow_one]
  have hBN : zpowers b ≤ normalizer (J : Set G) := zpowers_le.mpr hbN
  let α : zpowers b →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (c : zpowers b) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => Subgroup.normalizerMonoidHom_apply_apply_coe J _ j
  have hB2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have htriv : ∀ (c : zpowers b) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rcases hzp c c.2 with hc | hc
    · have hc1 : c = 1 := Subtype.ext hc
      rw [hc1, map_one]
      rfl
    · rw [eq_comm, QuotientGroup.eq]
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp (hcomm (j : G) j.2)
      have hoe : o = j⁻¹ * α c j := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, hc, hbinv]
        rw [hbinv] at hoeq
        change J.subtype o = _
        rw [hoeq]
        group
      rwa [hoe] at ho
  have hCmem : ∀ j : J, j ∈ (centralizer ({b} : Set G)).subgroupOf J ↔ ∀ c : zpowers b,
      α c j = j := by
    intro j
    rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h c
      apply Subtype.ext
      rw [hα]
      rcases hzp c c.2 with hc | hc
      · rw [hc]
        group
      · rw [hc, ← h, mul_inv_cancel_right]
    · intro h
      have h1 := congrArg Subtype.val (h ⟨b, mem_zpowers b⟩)
      rw [hα] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  set CJ := (centralizer ({b} : Set G)).subgroupOf J with hCJ
  set TJ := (pLayer CJ 2).map CJ.subtype with hTJ
  obtain ⟨-, -, e, -⟩ := fixed_prime_layer_covers_core_quotient 2 hB2 α hJq htriv CJ hCmem TJ hTJ
  have hTb : TJ.map J.subtype = gsFixedLayer J b := by
    rw [hTJ, Subgroup.map_map, gsFixedLayer]
    let φ : CJ ≃* (J ⊓ centralizer ({b} : Set G) : Subgroup G) :=
      { toFun := fun x => ⟨x, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    have hcomp : J.subtype.comp CJ.subtype =
        (J ⊓ centralizer ({b} : Set G)).subtype.comp φ.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, FixedLayerPComponent.map_pLayer_mulEquiv 2 φ]
  have eT : TJ ≃* gsFixedLayer J b :=
    (TJ.equivMapOfInjective J.subtype J.subtype_injective).trans (MulEquiv.subgroupCongr hTb)
  rw [← card_quotient_pPrimeCore_congr eT]
  exact Nat.card_congr e.toEquiv

end Correspondence

end CFSG.ComponentClassification.UnbalancingLocal
