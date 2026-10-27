module

import CFSG.CGT.A8S.TopSylow
public import CFSG.CGT.T75P.Aut
public import CFSG.CGT.T75P.NatTrans
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public section

namespace CFSG.CGT.A8S

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {G : Type} [Group G] {T H : Subgroup G}

theorem exists_linearization3 (hN : NaturalSL T H 3 1) :
    ∃ (φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)) (ρ : ↥H →* SL(3, GaloisField 2 1)),
      Function.Surjective ρ ∧ (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ T) ∧
      ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
        Multiplicative.toAdd (φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩) =
          ρ h • Multiplicative.toAdd (φ t) := by
  obtain ⟨hn, e, φ, hc⟩ := hN
  refine ⟨φ, e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun h => ?_, fun h t hmem => ?_⟩
  · simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  · rw [hc h t hmem, toAdd_ofAdd]
    rfl

theorem card_T_of_naturalSL3 (hN : NaturalSL T H 3 1) : Nat.card T = 8 := by
  obtain ⟨-, -, φ, -⟩ := hN
  have hF : Nat.card (GaloisField 2 1) = 2 := by simpa using GaloisField.card 2 1 one_ne_zero
  rw [Nat.card_congr φ.toEquiv]
  change Nat.card (Fin 3 → GaloisField 2 1) = 8
  rw [Nat.card_fun, hF, Nat.card_fin]
  rfl

theorem relIndex_T_H_of_naturalSL3 (hN : NaturalSL T H 3 1) : T.relIndex H = 168 := by
  obtain ⟨hn, e, -, -⟩ := hN
  let : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    rw [Nat.card_eq_fintype_card] at this
    simpa using this
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr e.toEquiv, Matrix.card_SL_field 3]
  simp [hF, Fin.prod_univ_three]

theorem card_H_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) : Nat.card H = 1344 := by
  have h := Subgroup.card_mul_index (T.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, card_T_of_naturalSL3 hN,
    ← Subgroup.relIndex, relIndex_T_H_of_naturalSL3 hN] at h
  omega

theorem le_normalizer_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) :
    H ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨hn, -, -, -⟩ := hN
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTH).1 hn

theorem inf_centralizer_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) :
    H ⊓ Subgroup.centralizer (T : Set G) = T :=
  CFSG.CGT.T75P.inf_centralizer_eq_of_natural hTH (le_normalizer_of_naturalSL3 hTH hN) hN

theorem normalizer_eq_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) :
    Subgroup.normalizer (T : Set G) = H ⊔ Subgroup.centralizer (T : Set G) := by
  have hHN := le_normalizer_of_naturalSL3 hTH hN
  refine le_antisymm (fun g hg => ?_)
    (sup_le hHN (Subgroup.centralizer_le_normalizer _))
  obtain ⟨h, hh, c, hc, rfl⟩ := CFSG.CGT.T75P.exists_mul_of_natural hHN hN hg
  exact Subgroup.mul_mem_sup hh hc

theorem le_centralizer_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) :
    T ≤ Subgroup.centralizer (T : Set G) :=
  (inf_centralizer_of_naturalSL3 hTH hN).ge.trans inf_le_right

theorem relIndex_centralizer_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) :
    T.relIndex (Subgroup.centralizer (T : Set G)) =
      H.relIndex (Subgroup.normalizer (T : Set G)) := by
  set C := Subgroup.centralizer (T : Set G)
  set N := Subgroup.normalizer (T : Set G)
  have hHN : H ≤ N := le_normalizer_of_naturalSL3 hTH hN
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have h1 : C.relIndex N = T.relIndex H := by
    have hsup : H.subgroupOf N ⊔ C.subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hHN hCN, ← normalizer_eq_of_naturalSL3 hTH hN,
        Subgroup.subgroupOf_self]
    have h := Subgroup.relIndex_sup_right (H.subgroupOf N) (C.subgroupOf N)
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hHN] at h
    rw [Subgroup.relIndex, h, ← Subgroup.inf_relIndex_left,
      inf_centralizer_of_naturalSL3 hTH hN]
  have h2 := Subgroup.relIndex_mul_relIndex T C N (le_centralizer_of_naturalSL3 hTH hN) hCN
  have h3 := Subgroup.relIndex_mul_relIndex T H N hTH hHN
  rw [h1, ← h3, relIndex_T_H_of_naturalSL3 hN, mul_comm] at h2
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

theorem mk_eq_mk_iff_of_galoisField_two3 {v w : Fin 3 → GaloisField 2 1} (hv : v ≠ 0)
    (hw : w ≠ 0) :
    Projectivization.mk (GaloisField 2 1) v hv = Projectivization.mk (GaloisField 2 1) w hw ↔
      v = w :=
  CFSG.CGT.A8S.TopSylow.mk_eq_mk_iff hv hw

theorem card_projectivization_galoisField_two3 :
    Nat.card (Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)) = 7 :=
  CFSG.CGT.A8S.TopSylow.card_projectivization

theorem index_stabilizer_SL3 {v : Fin 3 → GaloisField 2 1} (hv : v ≠ 0) :
    (MulAction.stabilizer SL(3, GaloisField 2 1)
      (Projectivization.mk (GaloisField 2 1) v hv)).index = 7 := by
  have := MulAction.isPretransitive_of_is_two_pretransitive (G := SL(3, GaloisField 2 1))
    (α := Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1))
  rw [MulAction.index_stabilizer_of_transitive, card_projectivization_galoisField_two3]

theorem index_fixingSubgroup_SL3 {v w : Fin 3 → GaloisField 2 1} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : v ≠ w) :
    (fixingSubgroup SL(3, GaloisField 2 1) ({Projectivization.mk (GaloisField 2 1) v hv,
      Projectivization.mk (GaloisField 2 1) w hw} :
        Set (Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)))).index = 42 := by
  have hne : Projectivization.mk (GaloisField 2 1) v hv ≠
      Projectivization.mk (GaloisField 2 1) w hw := by
    rwa [Ne, mk_eq_mk_iff_of_galoisField_two3]
  have h2 := Set.ncard_pair hne
  rw [MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq _ (by rw [h2]; infer_instance),
    h2, card_projectivization_galoisField_two3]
  rfl

private theorem toAdd_ne_zero (φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)) {t : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) : Multiplicative.toAdd (φ ⟨t, ht⟩) ≠ 0 := by
  intro h
  rw [toAdd_eq_zero, MulEquiv.map_eq_one_iff] at h
  exact ht1 (congrArg Subtype.val h)

private theorem toAdd_injective (φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)) {s t : G}
    (hs : s ∈ T) (ht : t ∈ T) (hst : s ≠ t) :
    Multiplicative.toAdd (φ ⟨s, hs⟩) ≠ Multiplicative.toAdd (φ ⟨t, ht⟩) := fun h =>
  hst (congrArg Subtype.val (φ.injective (Multiplicative.toAdd.injective h)))

private theorem mem_centralizer_iff_smul_eq {φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)}
    {ρ : ↥H →* SL(3, GaloisField 2 1)} (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hc : ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
      Multiplicative.toAdd (φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩) =
        ρ h • Multiplicative.toAdd (φ t))
    (h : ↥H) {t : G} (ht : t ∈ T) :
    (h : G) ∈ Subgroup.centralizer ({t} : Set G) ↔
      ρ h • Multiplicative.toAdd (φ ⟨t, ht⟩) = Multiplicative.toAdd (φ ⟨t, ht⟩) := by
  rw [Subgroup.mem_centralizer_singleton_iff,
    ← hc h ⟨t, ht⟩ (conj_mem_of_mem_normalizer (hHN h.2) ht), EmbeddingLike.apply_eq_iff_eq,
    EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, mul_inv_eq_iff_eq_mul]

theorem transitive_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y :=
  CFSG.CGT.T75P.natural_trans (le_normalizer_of_naturalSL3 hTH hN) hN

theorem card_inf_centralizer_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1) {v : G}
    (hv : v ∈ T) (hv1 : v ≠ 1) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({v} : Set G)) = 192 := by
  obtain ⟨φ, ρ, hρ, -, hc⟩ := exists_linearization3 hN
  have hHN := le_normalizer_of_naturalSL3 hTH hN
  have hv0 := toAdd_ne_zero φ hv hv1
  have hsub : (H ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf H =
      (MulAction.stabilizer SL(3, GaloisField 2 1)
        (Projectivization.mk (GaloisField 2 1) _ hv0)).comap ρ := by
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      MulAction.mem_stabilizer_iff, Projectivization.smul_mk, mk_eq_mk_iff_of_galoisField_two3,
      ← mem_centralizer_iff_smul_eq hHN hc h hv]
    exact and_iff_right h.2
  have hidx : ((H ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf H).index = 7 := by
    rw [hsub, Subgroup.index_comap_of_surjective _ hρ, index_stabilizer_SL3]
  have h1 := Subgroup.card_mul_index ((H ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf H)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    card_H_of_naturalSL3 hTH hN] at h1
  omega

theorem card_inf_centralizer_pair_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1)
    {v w : G} (hv : v ∈ T) (hv1 : v ≠ 1) (hw : w ∈ T) (hw1 : w ≠ 1) (hvw : v ≠ w) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({v} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G)) = 32 := by
  obtain ⟨φ, ρ, hρ, -, hc⟩ := exists_linearization3 hN
  have hHN := le_normalizer_of_naturalSL3 hTH hN
  have hv0 := toAdd_ne_zero φ hv hv1
  have hw0 := toAdd_ne_zero φ hw hw1
  set X := H ⊓ Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) with hX
  have hsub : X.subgroupOf H = (fixingSubgroup SL(3, GaloisField 2 1)
      ({Projectivization.mk (GaloisField 2 1) _ hv0, Projectivization.mk (GaloisField 2 1) _ hw0} :
        Set (Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)))).comap ρ := by
    ext h
    simp only [hX, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      mem_fixingSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq]
    rw [Projectivization.smul_mk, Projectivization.smul_mk, mk_eq_mk_iff_of_galoisField_two3,
      mk_eq_mk_iff_of_galoisField_two3, ← mem_centralizer_iff_smul_eq hHN hc h hv,
      ← mem_centralizer_iff_smul_eq hHN hc h hw]
    exact ⟨fun h' => ⟨h'.1.2, h'.2⟩, fun h' => ⟨⟨h.2, h'.1⟩, h'.2⟩⟩
  have hidx : (X.subgroupOf H).index = 42 := by
    rw [hsub, Subgroup.index_comap_of_surjective _ hρ,
      index_fixingSubgroup_SL3 hv0 hw0 (toAdd_injective φ hv hw hvw)]
  have h1 := Subgroup.card_mul_index (X.subgroupOf H)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv,
    card_H_of_naturalSL3 hTH hN] at h1
  rw [hX]
  omega

end CFSG.CGT.A8S
