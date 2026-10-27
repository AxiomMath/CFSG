module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51
public import CFSG.LocalAnalysis.ComponentClassification.GSLitSylowGood

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

namespace Six

variable {G : Type*} [Group G]

theorem conjugate_layerIn [Finite G] (Y : Subgroup G) (c : G) :
    conjugate (layerIn Y) c = layerIn (conjugate Y c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : G ≃* G := MulAut.conj c⁻¹ with hφ
  let ψ : ↥Y ≃* ↥(conjugate Y c) := Y.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomm : φ.toMonoidHom.comp Y.subtype = (conjugate Y c).subtype.comp ψ.toMonoidHom := by
    ext y
    rfl
  change ((pLayer Y 2).map Y.subtype).map φ.toMonoidHom =
    (pLayer (conjugate Y c) 2).map (conjugate Y c).subtype
  rw [map_map, hcomm, ← map_map, UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 ψ]

theorem conjugate_oddCoreIn (L : Subgroup G) (c : G) :
    conjugate (oddCoreIn L) c = oddCoreIn (conjugate L c) :=
  GSLit.conjugate_map_pPrimeCore L c

theorem isPComponent_conjugate {L X : Subgroup G} (hLX : L ≤ X)
    (hL : IsPComponent 2 (L.subgroupOf X)) (c : G) :
    conjugate L c ≤ conjugate X c ∧
      IsPComponent 2 ((conjugate L c).subgroupOf (conjugate X c)) := by
  set φ : G ≃* G := MulAut.conj c⁻¹ with hφ
  refine ⟨map_mono hLX, ?_⟩
  let ψ : ↥X ≃* ↥(conjugate X c) := X.equivMapOfInjective φ.toMonoidHom φ.injective
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 ψ hL
  convert h using 1
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj, hjy⟩ := mem_map.mp (mem_subgroupOf.mp hy)
    exact ⟨⟨j, hLX hj⟩, mem_subgroupOf.mpr hj, Subtype.ext hjy⟩
  · rintro ⟨w, hw, rfl⟩
    exact mem_subgroupOf.mpr ⟨w, mem_subgroupOf.mp hw, rfl⟩

theorem isoCorrSub_conjugate [Finite G] {a c : G} {J E L : Subgroup G}
    (hca : c ∈ centralizer ({a} : Set G)) (hcJ : c ∈ normalizer (J : Set G))
    (h : IsoCorrSub a J E L) : IsoCorrSub a J (conjugate E c) (conjugate L c) := by
  obtain ⟨hLN, hLc, hLa, hsup, hfix⟩ := h
  have hJc : conjugate J c = J := conjugate_eq_of_mem_normalizer hcJ
  have hNc : conjugate (normalizer (E : Set G)) c = normalizer (conjugate E c : Set G) :=
    map_equiv_normalizer_eq E (MulAut.conj c⁻¹)
  have hCa : conjugate (centralizer ({a} : Set G)) c = centralizer ({a} : Set G) :=
    conjugate_eq_of_mem_normalizer (le_normalizer hca)
  have hfixc : GSLit.fixedLayer J (conjugate E c) = conjugate (GSLit.fixedLayer J E) c := by
    rw [GSLit.conjugate_fixedLayer, hJc]
  have hac : c * a = a * c := mem_centralizer_singleton_iff.mp hca
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hNc]
    exact map_mono hLN
  · have := (isPComponent_conjugate hLN hLc c).2
    rwa [hNc] at this
  · rw [conjugate_conjugate, hac, ← conjugate_conjugate, hLa]
  · rw [hfixc]
    exact GSLit.conjugate_sup_pPrimeCore hsup c
  · rw [hfixc, hfix, conjugate_layerIn]
    congr 1
    calc conjugate (L ⊓ centralizer ({a} : Set G)) c
        = conjugate L c ⊓ conjugate (centralizer ({a} : Set G)) c :=
          Subgroup.map_inf _ _ _ (MulAut.conj c⁻¹).injective
      _ = conjugate L c ⊓ centralizer ({a} : Set G) := by rw [hCa]

theorem sylow_conjugate_of_mem {X S : Subgroup G} (hSX : S ≤ X)
    (hS : ∃ R : Sylow 2 ↥X, (R : Subgroup ↥X) = S.subgroupOf X) {c : G} (hc : c ∈ X) :
    conjugate S c ≤ X ∧ ∃ R : Sylow 2 ↥X, (R : Subgroup ↥X) = (conjugate S c).subgroupOf X := by
  have hle : conjugate S c ≤ X := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have := mul_mem (mul_mem (inv_mem hc) (hSX hy)) hc
    rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at this
  refine ⟨hle, ?_⟩
  obtain ⟨R, hR⟩ := hS
  refine ⟨(⟨c, hc⟩ : X)⁻¹ • R, ?_⟩
  rw [Sylow.coe_subgroup_smul, hR]
  ext y
  rw [mem_pointwise_smul_iff_inv_smul_mem, mem_subgroupOf, mem_subgroupOf, mem_conjugate_iff,
    MulAut.smul_def, ← map_inv, inv_inv, MulAut.conj_apply]
  rfl

theorem map_upperCentralSeries_conjugate (S : Subgroup G) (c : G) (i : ℕ) :
    (Subgroup.upperCentralSeries (conjugate S c) i).map (conjugate S c).subtype =
      conjugate ((Subgroup.upperCentralSeries S i).map S.subtype) c := by
  set φ : G ≃* G := MulAut.conj c⁻¹ with hφ
  let ψ : ↥S ≃* ↥(conjugate S c) := S.equivMapOfInjective φ.toMonoidHom φ.injective
  have hU : Subgroup.upperCentralSeries (conjugate S c) i =
      (Subgroup.upperCentralSeries S i).map ψ.toMonoidHom := by
    rw [← Subgroup.comap_upperCentralSeries ψ.symm i]
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_map_equiv]
    rfl
  rw [hU, map_map]
  change _ = ((Subgroup.upperCentralSeries S i).map S.subtype).map φ.toMonoidHom
  rw [map_map]
  rfl

theorem index_centralizer_conjugate (S : Subgroup G) {b c : G} (hbc : c * b = b * c) :
    ((centralizer ({b} : Set G)).subgroupOf (conjugate S c)).index =
      ((centralizer ({b} : Set G)).subgroupOf S).index := by
  set φ : G ≃* G := MulAut.conj c⁻¹ with hφ
  let ψ : ↥S ≃* ↥(conjugate S c) := S.equivMapOfInjective φ.toMonoidHom φ.injective
  have heq : (centralizer ({b} : Set G)).subgroupOf (conjugate S c) =
      ((centralizer ({b} : Set G)).subgroupOf S).comap ψ.symm.toMonoidHom := by
    ext y
    obtain ⟨s, rfl⟩ := ψ.surjective y
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, mem_subgroupOf,
      mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    change (c⁻¹ * ↑s * c⁻¹⁻¹) * b = b * (c⁻¹ * ↑s * c⁻¹⁻¹) ↔ ↑s * b = b * ↑s
    have hbc' : c⁻¹ * b = b * c⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hbc, mul_assoc, mul_inv_cancel, mul_one]
    constructor
    · intro h1
      calc ↑s * b = c * (c⁻¹ * ↑s * c⁻¹⁻¹) * (c⁻¹ * b) := by group
        _ = c * (c⁻¹ * ↑s * c⁻¹⁻¹) * (b * c⁻¹) := by rw [hbc']
        _ = c * ((c⁻¹ * ↑s * c⁻¹⁻¹) * b) * c⁻¹ := by group
        _ = c * (b * (c⁻¹ * ↑s * c⁻¹⁻¹)) * c⁻¹ := by rw [h1]
        _ = (c * b) * (c⁻¹ * ↑s * c⁻¹⁻¹) * c⁻¹ := by group
        _ = (b * c) * (c⁻¹ * ↑s * c⁻¹⁻¹) * c⁻¹ := by rw [hbc]
        _ = b * ↑s := by group
    · intro h1
      calc (c⁻¹ * ↑s * c⁻¹⁻¹) * b = c⁻¹ * ↑s * (c * b) := by group
        _ = c⁻¹ * ↑s * (b * c) := by rw [hbc]
        _ = c⁻¹ * (↑s * b) * c := by group
        _ = c⁻¹ * (b * ↑s) * c := by rw [h1]
        _ = (c⁻¹ * b) * ↑s * c := by group
        _ = (b * c⁻¹) * ↑s * c := by rw [hbc']
        _ = b * (c⁻¹ * ↑s * c⁻¹⁻¹) := by group
  rw [heq]
  exact index_comap_of_surjective _ ψ.symm.surjective

end Six

variable {H : Type} [Group H] [Finite H]

namespace Hyp52

theorem not_isoCorrSub_B (h : Hyp52 H) (L : Subgroup H) : ¬ IsoCorrSub h.a h.J h.B L := by
  rintro ⟨hLN, hLc, hLa, hsup, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJq : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.J _ h.J_le).1 h.isPComponent_J).2.2
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := by
    obtain ⟨R, hR⟩ := h.S_sylow
    have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set H) ⊓
        normalizer (h.J : Set H))) := hR ▸ R.isPGroup'
    have h2 := h1.map (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)).subtype
    rw [map_subgroupOf_eq_of_le h.S_le] at h2
    exact h2.to_le (h.B_le.trans inf_le_left)
  have hJBL : GSLit.fixedLayer h.J h.B ≤ L := by
    rw [← hsup]
    exact le_sup_left
  have hEN : layerIn (normalizer (h.B : Set H)) ≤ normalizer (L : Set H) :=
    UGSChain.map_pLayer_le_normalizer hLN hLc
  have hVL : layerIn (normalizer (h.B : Set H)) ≤ L := by
    rw [← h.conjClosure_eq]
    refine iSup₂_le fun v hv => ?_
    have hvN : v ∈ normalizer (L : Set H) := hEN hv
    calc conjugate (GSLit.fixedLayer h.J h.B) v ≤ conjugate L v := map_mono hJBL
      _ = L := conjugate_eq_of_mem_normalizer hvN
  have haL : h.a ∈ normalizer (L : Set H) := mem_normalizer_of_conjugate_eq hLa
  have hTa : GSLit.fixedLayer h.J h.B ≤ centralizer ({h.a} : Set H) :=
    (GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_left.trans h.J_le)
  have hLO : ⁅L, zpowers h.a⁆ ≤ oddCoreIn L := commutator_le_oddCoreIn haL hJBL hTa hsup
  have hVO : layerIn (normalizer (h.B : Set H)) ≤ oddCoreIn L := by
    rw [← h.commutator_eq]
    exact (commutator_mono hVL le_rfl).trans hLO
  have hJBV : GSLit.fixedLayer h.J h.B ≤ layerIn (normalizer (h.B : Set H)) := by
    rw [← h.conjClosure_eq]
    refine le_trans ?_ (le_iSup₂_of_le (1 : H) (one_mem _) le_rfl)
    intro z hz
    refine ⟨z, hz, ?_⟩
    simp
  have hJBO : GSLit.fixedLayer h.J h.B ≤ oddCoreIn L := hJBV.trans hVO
  have hodd : Odd (Nat.card (oddCoreIn L)) := by
    rw [oddCoreIn, card_map_of_injective L.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (pPrimeCore_coprime_card (p := 2)
        (G := L)) h2)
  have hJBbot : GSLit.fixedLayer h.J h.B = ⊥ := by
    rw [GSLit.fixedLayer_eq_closure hJq hBJ hB2, closure_eq_bot_iff]
    rintro z ⟨hz, k, hk⟩
    have hzJB : z ∈ GSLit.fixedLayer h.J h.B := by
      rw [GSLit.fixedLayer_eq_closure hJq hBJ hB2]
      exact subset_closure ⟨hz, k, hk⟩
    have hdvd : orderOf z ∣ Nat.card (oddCoreIn L) :=
      Subgroup.orderOf_dvd_natCard _ (hJBO hzJB)
    rw [hk] at hdvd
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exfalso
      have h2 : 2 ∣ Nat.card (oddCoreIn L) := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hsupJ := (GSLit.fixedLayer_sup_pPrimeCore hJq hBJ hB2).1
  rw [hJBbot, bot_sup_eq] at hsupJ
  have htop : ∀ j : h.J, j ∈ pPrimeCore 2 h.J := by
    intro j
    have hj : (j : H) ∈ (pPrimeCore 2 h.J).map h.J.subtype := by
      rw [hsupJ]
      exact j.2
    obtain ⟨o, ho, hoj⟩ := mem_map.mp hj
    rwa [show o = j from Subtype.ext hoj] at ho
  obtain ⟨u, v, huv⟩ := hJq.2.2
  apply huv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  have hu : ((u : h.J ⧸ pPrimeCore 2 h.J) :
      (h.J ⧸ pPrimeCore 2 h.J) ⧸ center (h.J ⧸ pPrimeCore 2 h.J)) = 1 := by
    rw [(QuotientGroup.eq_one_iff (N := pPrimeCore 2 h.J) u).mpr (htop u)]
    rfl
  rw [hu, one_mul, mul_one]

end Hyp52

end CFSG.ComponentClassification.GSThmB
