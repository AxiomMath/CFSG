module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverDiag
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (swapDiagHom swapDiagHom_apply)

local instance e6PilotSwapCoverCTNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Generic

variable {G : Type*} [Group G] {t : G}

theorem swap_map_conj_map_conj (htt : t * t = 1) (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.id_apply]
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [htt]; group

theorem swap_iSup_le_centralizer {ι : Type*} {F : ι → Subgroup G}
    (hc : ∀ i j, (F j).map (MulAut.conj t).toMonoidHom ≤ centralizer (F i : Set G)) :
    (⨆ i, F i).map (MulAut.conj t).toMonoidHom ≤ centralizer ((⨆ i, F i : Subgroup G) : Set G) := by
  rw [Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  rw [← le_centralizer_iff]
  exact iSup_le fun i => le_centralizer_iff.1 (hc i j)

variable [Finite G]

theorem nonempty_quotient_center_mulEquiv_of_swapDiag {ι : Type*} {F R : ι → Subgroup G}
    {L : Subgroup G}
    (hc : ∀ i j, (F j).map (MulAut.conj t).toMonoidHom ≤ centralizer (F i : Set G))
    (hFL : ∀ i, ∀ x ∈ F i, x * (t * x * t⁻¹) ∈ L)
    (hRF : ∀ i, ∀ y ∈ R i, ∃ x ∈ F i, x * (t * x * t⁻¹) = y) (hLR : L ≤ ⨆ i, R i)
    (hZ : center L = ⊥) :
    Nonempty ((⨆ i, F i : Subgroup G) ⧸ center (⨆ i, F i : Subgroup G) ≃* L) := by
  set G₁ : Subgroup G := ⨆ i, F i with hG₁
  have hcomm := swap_iSup_le_centralizer hc
  set δ := swapDiagHom hcomm with hδ
  have hFG : ∀ i, F i ≤ G₁ := fun i => le_iSup F i
  have hrange : δ.range = L := by
    refine le_antisymm ?_ (hLR.trans (iSup_le fun i y hy => ?_))
    · have hle : G₁ ≤ (L.comap δ).map G₁.subtype :=
        iSup_le fun i x hx => ⟨⟨x, hFG i hx⟩, hFL i x hx, rfl⟩
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hle x.2
      rw [show x = y from Subtype.ext hyx.symm]
      exact hy
    · obtain ⟨x, hx, rfl⟩ := hRF i y hy
      exact ⟨⟨x, hFG i hx⟩, rfl⟩
  have hker : center G₁ = δ.ker := by
    refine le_antisymm (fun z hz => ?_) fun x hx => ?_
    · have hzL : δ z ∈ L := hrange ▸ ⟨z, rfl⟩
      have hzc : (⟨δ z, hzL⟩ : L) ∈ center L := by
        rw [mem_center_iff]
        rintro ⟨y, hy⟩
        rw [← hrange] at hy
        obtain ⟨g, rfl⟩ := hy
        apply Subtype.ext
        change δ g * δ z = δ z * δ g
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hz g)]
      rw [hZ, mem_bot] at hzc
      exact congrArg Subtype.val hzc
    · rw [MonoidHom.mem_ker, swapDiagHom_apply] at hx
      have hxt : (x : G) ∈ G₁.map (MulAut.conj t).toMonoidHom := by
        refine ⟨(x : G)⁻¹, inv_mem x.2, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc t * (x : G)⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
          _ = x := (eq_inv_of_mul_eq_one_left hx).symm
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 (hcomm hxt) g g.2)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange δ)).trans (MulEquiv.subgroupCongr hrange)⟩

end Generic

section Flip


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 K} {t : G}

@[expose] noncomputable def SwapFactorCover.flip {N : E6Neighbour} (h : SwapFactorCover e t N)
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) : SwapFactorCover e t N where
  Kc := h.Kc.map (MulAut.conj t).toMonoidHom
  perfect := by rw [← map_commutator, h.perfect]
  le_centralizer := by
    rw [swap_map_conj_map_conj htt]
    exact le_centralizer_iff.1 h.le_centralizer
  sup_eq := by rw [swap_map_conj_map_conj htt, sup_comm, h.sup_eq]
  odd_card_inf := by rw [swap_map_conj_map_conj htt, inf_comm]; exact h.odd_card_inf
  normalizer_le := by
    intro s hs hso
    have hts : ∀ τ ∈ modelToG e (N.torus K), τ * t = t * τ := fun τ hτ =>
      mem_centralizer_iff.1 htL τ (modelToG_le e _ hτ)
    have hs' : t⁻¹ * s * t ∈ centralizer (modelToG e (N.torus K) : Set G) := by
      rw [mem_centralizer_iff] at hs ⊢
      intro τ hτ
      have h1 := hs τ hτ
      have h2 := hts τ hτ
      have h3 : τ * t⁻¹ = t⁻¹ * τ := by
        calc τ * t⁻¹ = t⁻¹ * (t * τ) * t⁻¹ := by group
          _ = t⁻¹ * (τ * t) * t⁻¹ := by rw [h2]
          _ = t⁻¹ * τ := by group
      calc τ * (t⁻¹ * s * t) = t⁻¹ * (τ * s) * t := by rw [← mul_assoc, ← mul_assoc, h3]; group
        _ = t⁻¹ * (s * τ) * t := by rw [h1]
        _ = t⁻¹ * s * (τ * t) := by group
        _ = t⁻¹ * s * t * τ := by rw [h2]; group
    have hso' : Odd (orderOf (t⁻¹ * s * t)) := by
      have h1 := MulEquiv.orderOf_eq (MulAut.conj t⁻¹) s
      rw [MulAut.conj_apply, inv_inv] at h1
      rw [h1]
      exact hso
    have h1 := conj_mem_normalizer_map_conj t (h.normalizer_le _ hs' hso')
    rwa [show t * (t⁻¹ * s * t) * t⁻¹ = s by group] at h1
  ε := h.ε.comp (h.Kc.equivMapOfInjective _ (swapConj_injective t)).symm.toMonoidHom
  surjective := h.surjective.comp (MulEquiv.surjective _)
  eq_one_iff := by
    intro x
    obtain ⟨k, rfl⟩ := (h.Kc.equivMapOfInjective _ (swapConj_injective t)).surjective x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    rw [h.eq_one_iff, coe_equivMapOfInjective_apply]
    exact (Subgroup.mem_map_iff_mem (f := (MulAut.conj t).toMonoidHom)
      (swapConj_injective t) (K := h.Kc.map (MulAut.conj t).toMonoidHom) (x := (k : G))).symm
  diag := by
    intro x
    obtain ⟨k, rfl⟩ := (h.Kc.equivMapOfInjective _ (swapConj_injective t)).surjective x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    rw [coe_equivMapOfInjective_apply, ← h.diag k]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc : (k : G) * (t * k * t⁻¹) = t * k * t⁻¹ * k :=
      mem_centralizer_iff.1 (h.le_centralizer ⟨k, k.2, rfl⟩) k k.2
    calc t * (k : G) * t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) =
          t * k * t⁻¹ * ((t * t) * k * (t * t)⁻¹) := by group
      _ = t * k * t⁻¹ * k := by rw [htt]; group
      _ = (k : G) * (t * k * t⁻¹) := hc.symm

theorem SwapFactorCover.flip_Kc {N : E6Neighbour} (h : SwapFactorCover e t N)
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) :
    (h.flip htL htt).Kc = h.Kc.map (MulAut.conj t).toMonoidHom :=
  rfl

theorem SwapFactorCover.piece_flip [Finite G] {N : E6Neighbour} (h : SwapFactorCover e t N)
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) (J : Finset (Fin (Tag.rank .E6))) :
    (h.flip htL htt).piece J = (h.piece J).map (MulAut.conj t).toMonoidHom := by
  have hT : (modelToG e (leviTorus K J)).map (MulAut.conj t).toMonoidHom =
      modelToG e (leviTorus K J) := by
    refine le_antisymm ?_ fun τ hτ => ⟨τ, hτ, ?_⟩
    · rintro _ ⟨τ, hτ, rfl⟩
      have hτt : τ * t = t * τ := mem_centralizer_iff.1 htL τ (modelToG_le e _ hτ)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hτt, mul_inv_cancel_right]
      exact hτ
    · have hτt : τ * t = t * τ := mem_centralizer_iff.1 htL τ (modelToG_le e _ hτ)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hτt, mul_inv_cancel_right]
  rw [SwapFactorCover.piece, SwapFactorCover.piece, CFSG.Quasithin.map_perfectCore,
    Subgroup.map_inf_eq _ _ _ (swapConj_injective t), F4Pilot.map_centralizer_mulEquiv, hT,
    h.flip_Kc]

end Flip

section Assembly


variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 K} {t : G}

theorem SwapFactorCover.pieceCore_le_centralizer_pieceCore {N : E6Neighbour}
    (h : SwapFactorCover e t N) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1)
    {I J : Finset (Fin (Tag.rank .E6))} (hI : I.card ≤ 2) (hJ : J.card ≤ 2) (hIN : I ⊆ N.nodes)
    (hJN : J ⊆ N.nodes)
    (hc : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      centralizer (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I :
        Set (adjointGroup .E6 K))) :
    pieceCore e J ≤ centralizer (pieceCore e I : Set G) := by
  rw [h.pieceCore_eq_piece_sup htL htt hf hK hIN, h.pieceCore_eq_piece_sup htL htt hf hK hJN]
  have h1 : h.piece J ≤ centralizer (h.piece I : Set G) :=
    h.piece_le_centralizer_piece hq htL hI hJ hc
  have h2 : (h.piece J).map (MulAut.conj t).toMonoidHom ≤ centralizer (h.piece I : Set G) :=
    (map_mono (h.piece_le J)).trans (h.map_le_centralizer_piece I)
  have h3 : h.piece J ≤
      centralizer ((h.piece I).map (MulAut.conj t).toMonoidHom : Set G) :=
    le_centralizer_iff.1 ((map_mono (h.piece_le I)).trans (h.map_le_centralizer_piece J))
  have h4 : (h.piece J).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((h.piece I).map (MulAut.conj t).toMonoidHom : Set G) :=
    F4Pilot.map_le_centralizer_map _ h1
  refine sup_le ?_ ?_ <;>
    refine (le_inf ?_ ?_).trans F4Pilot.centralizer_inf_centralizer_le_centralizer_sup
  exacts [h1, h3, h2, h4]

theorem SwapFactorCover.mul_conj_mem_map_levi {N : E6Neighbour} (h : SwapFactorCover e t N)
    (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G)) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J.card ≤ 2) {x : G} (hx : x ∈ h.piece J) :
    x * (t * x * t⁻¹) ∈ (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J).map
      (L.subtype.comp e.symm.toMonoidHom) :=
  ⟨h.epsC ⟨x, h.piece_le J hx⟩, h.epsC_mem_levi hq htL hJ hx, (h.mul_conj_eq ⟨x, _⟩).symm⟩

theorem SwapFactorCover.exists_mem_piece_mul_conj_eq {N : E6Neighbour}
    (h : SwapFactorCover e t N) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G)) {J : Finset (Fin (Tag.rank .E6))}
    (hJN : J ⊆ N.nodes) {y : adjointGroup .E6 K}
    (hy : y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    ∃ x ∈ h.piece J, x * (t * x * t⁻¹) = (L.subtype.comp e.symm.toMonoidHom) y := by
  obtain ⟨k, hk, rfl⟩ := h.exists_epsC_eq hf hK hq htL hJN hy
  exact ⟨k, hk, h.mul_conj_eq k⟩

theorem exists_aligned_six {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) (hX : SwapFactorCover e t .high)
    (hY : SwapFactorCover e t .six) :
    ∃ hY' : SwapFactorCover e t .six, hY'.piece {3} = hX.piece {3} := by
  rcases hX.piece_eq_or_eq_conj hY hf hK hq htL htt (j := 3) (by decide) (by decide) with h3 | h3
  · exact ⟨hY, h3⟩
  · refine ⟨hY.flip htL htt, ?_⟩
    rw [hY.piece_flip htL htt, h3, swap_map_conj_map_conj htt]

theorem exists_swapFactor_of_swapFactorCover {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1)
    (hcov : ∀ N : E6Neighbour, Nonempty (SwapFactorCover e t N)) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      Nonempty (G₁ ⧸ center G₁ ≃* adjointGroup .E6 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, pieceCore e J.1 := by
  obtain ⟨hX⟩ := hcov .high
  obtain ⟨hY₀⟩ := hcov .six
  obtain ⟨hZ⟩ := hcov .three
  obtain ⟨hY, hY3⟩ := exists_aligned_six hf hK hq htL htt hX hY₀
  set φ : adjointGroup .E6 K →* G := L.subtype.comp e.symm.toMonoidHom with hφ
  set F : Fin (Tag.rank .E6) → Subgroup G :=
    fun i => if i = 1 then hY.piece {i} else hX.piece {i} with hF
  have hF1 : F 1 = hY.piece {1} := ite_eq_left rfl
  have hFi : ∀ i, i ≠ 1 → F i = hX.piece {i} := fun i hi => ite_eq_right hi
  have hcard : ∀ i : Fin (Tag.rank .E6), ({i} : Finset (Fin (Tag.rank .E6))).card ≤ 2 :=
    fun i => by simp
  have hXn : ∀ i : Fin (Tag.rank .E6), i ≠ 1 →
      ({i} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.high.nodes :=
    fun i hi => Finset.singleton_subset_iff.2 (mem_nodes_high_of_ne hi)
  have hY1 : ({1} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.six.nodes := by decide
  have hM : ∀ i, pieceCore e {i} = F i ⊔ (F i).map (MulAut.conj t).toMonoidHom := by
    intro i
    by_cases hi : i = 1
    · subst hi
      rw [hF1]
      exact hY.pieceCore_eq_piece_sup htL htt hf hK hY1
    · rw [hFi i hi]
      exact hX.pieceCore_eq_piece_sup htL htt hf hK (hXn i hi)
  have hFM : ∀ i, F i ≤ pieceCore e {i} := fun i => le_sup_left.trans (hM i).ge
  have hFtM : ∀ i, (F i).map (MulAut.conj t).toMonoidHom ≤ pieceCore e {i} :=
    fun i => le_sup_right.trans (hM i).ge
  have hp : ∀ i, ⁅F i, F i⁆ = F i := by
    intro i
    by_cases hi : i = 1
    · subst hi
      rw [hF1]
      exact hY.commutator_piece _
    · rw [hFi i hi]
      exact hX.commutator_piece _
  have hFL : ∀ i, ∀ x ∈ F i, x * (t * x * t⁻¹) ∈
      (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i}).map φ := by
    intro i x hx
    by_cases hi : i = 1
    · subst hi
      rw [hF1] at hx
      exact hY.mul_conj_mem_map_levi hq htL (hcard 1) hx
    · rw [hFi i hi] at hx
      exact hX.mul_conj_mem_map_levi hq htL (hcard i) hx
  have hRF : ∀ i, ∀ y ∈ (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i}).map φ,
      ∃ x ∈ F i, x * (t * x * t⁻¹) = y := by
    rintro i _ ⟨y, hy, rfl⟩
    by_cases hi : i = 1
    · subst hi
      rw [hF1]
      exact hY.exists_mem_piece_mul_conj_eq hf hK hq htL hY1 hy
    · rw [hFi i hi]
      exact hX.exists_mem_piece_mul_conj_eq hf hK hq htL (hXn i hi) hy
  have hM1 : ∀ j : Fin (Tag.rank .E6), (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) →
      pieceCore e {j} ≤ centralizer (pieceCore e {1} : Set G) := by
    intro j hj
    have hc := levi_one_le_centralizer_levi_E6 (K := K) hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact hY.pieceCore_le_centralizer_pieceCore hf hK hq htL htt (hcard 1) (hcard 0) hY1
        (by decide) hc
    · exact hY.pieceCore_le_centralizer_pieceCore hf hK hq htL htt (hcard 1) (hcard 2) hY1
        (by decide) hc
    · exact hZ.pieceCore_le_centralizer_pieceCore hf hK hq htL htt (hcard 1) (hcard 4)
        (by decide) (by decide) hc
    · exact hZ.pieceCore_le_centralizer_pieceCore hf hK hq htL htt (hcard 1) (hcard 5)
        (by decide) (by decide) hc
  have hc : ∀ i j, (F j).map (MulAut.conj t).toMonoidHom ≤ centralizer (F i : Set G) := by
    intro i j
    by_cases hi : i = 1 <;> by_cases hj : j = 1
    · subst hi
      subst hj
      rw [hF1]
      exact (map_mono (hY.piece_le _)).trans (hY.map_le_centralizer_piece _)
    · subst hi
      by_cases hj3 : j = 3
      · subst hj3
        rw [hF1, hFi 3 hj, ← hY3]
        exact (map_mono (hY.piece_le _)).trans (hY.map_le_centralizer_piece _)
      · have hj' : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5 := by revert hj hj3; revert j; decide
        exact (hFtM j).trans ((hM1 j hj').trans
          (centralizer_le (SetLike.coe_subset_coe.2 (hFM 1))))
    · subst hj
      by_cases hi3 : i = 3
      · subst hi3
        rw [hF1, hFi 3 hi, ← hY3]
        exact (map_mono (hY.piece_le _)).trans (hY.map_le_centralizer_piece _)
      · have hi' : i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 5 := by revert hi hi3; revert i; decide
        exact (hFtM 1).trans ((le_centralizer_iff.1 (hM1 i hi')).trans
          (centralizer_le (SetLike.coe_subset_coe.2 (hFM i))))
    · rw [hFi i hi, hFi j hj]
      exact (map_mono (hX.piece_le _)).trans (hX.map_le_centralizer_piece _)
  set G₁ : Subgroup G := ⨆ i, F i with hG₁
  have hcomm : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) :=
    swap_iSup_le_centralizer hc
  have hperf : ⁅G₁, G₁⁆ = G₁ := CFSG.Quasithin.A3.commutator_iSup_eq_of_perfect F hp
  have hZL : center L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ center (adjointGroup .E6 K) := (MulEquivClass.apply_mem_center_iff e).2 hx
    rw [center_adjointGroup_eq_bot_field, mem_bot, MulEquiv.map_eq_one_iff] at h1
    exact mem_bot.2 h1
  have hLR : L ≤ ⨆ i, (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i}).map φ := by
    intro l hl
    have htop : ⊤ ≤ (⨆ i, (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i}).map
        φ).comap φ :=
      top_le_of_forall_levi_singleton_le_E6 fun i y hy =>
        le_iSup (fun i => (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i}).map φ) i
          ⟨y, hy, rfl⟩
    have h1 := htop (mem_top (e ⟨l, hl⟩))
    rw [mem_comap] at h1
    have h2 : φ (e ⟨l, hl⟩) = l := by simp [hφ]
    rwa [h2] at h1
  have hFL' : ∀ i, ∀ x ∈ F i, x * (t * x * t⁻¹) ∈ L := fun i x hx => by
    obtain ⟨y, -, hy⟩ := hFL i x hx
    rw [← hy]
    exact (e.symm y).2
  obtain ⟨eG⟩ := nonempty_quotient_center_mulEquiv_of_swapDiag hc hFL' hRF hLR hZL
  have hsimple : IsSimpleGroup (G₁ ⧸ center G₁) := by
    have := isSimpleGroup_adjointGroup_E6 (K := K)
    exact (eG.trans e).isSimpleGroup
  refine ⟨G₁, ⟨(isPerfect_iff.2 hperf).commutator_eq_top, hsimple⟩, ⟨eG.trans e⟩, hcomm, ?_⟩
  have hle_sup : ∀ i, pieceCore e {i} ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := fun i => by
    rw [hM i]
    exact sup_le_sup (le_iSup F i) (map_mono (le_iSup F i))
  have hpS : ∀ i, pieceCore e {i} ≤
      ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, pieceCore e J.1 := fun i =>
    le_iSup (fun J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} => pieceCore e J.1)
      ⟨{i}, hcard i⟩
  apply le_antisymm
  · refine sup_le (iSup_le fun i => (hFM i).trans (hpS i)) ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun i => (hFtM i).trans (hpS i)
  · refine iSup_le fun J => ?_
    obtain ⟨hN⟩ := hcov (amalgamPlacement J.1)
    have hJN := subset_nodes_amalgamPlacement J.2
    rw [hN.pieceCore_eq_piece_sup htL htt hf hK hJN]
    have hle : hN.piece J.1 ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
      refine (hN.piece_le_iSup_piece hf hK hq htL J.2 hJN).trans (iSup₂_le fun j hj => ?_)
      have h1 := hN.pieceCore_eq_piece_sup htL htt hf hK (Finset.singleton_subset_iff.2 (hJN hj))
      exact (le_sup_left.trans h1.ge).trans (hle_sup j)
    refine sup_le hle ?_
    calc (hN.piece J.1).map (MulAut.conj t).toMonoidHom ≤
        (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom := map_mono hle
      _ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
        rw [Subgroup.map_sup, swap_map_conj_map_conj htt, sup_comm]

end Assembly

section Input


theorem e6SwapCoverCTInput_holds : E6SwapCoverCTInput := by
  intro G _ _ L K₂ _ _ _ σ h4 e t htL htt hcov
  have : Fintype (fixSubfield σ) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (fixSubfield σ) 2
  have hK : Nat.card (fixSubfield σ) = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  exact exists_swapFactor_of_swapFactorCover n.pos hK h4 htL htt hcov

theorem e6SwapRowCTInput_holds : E6SwapRowCTInput :=
  e6SwapRowCTInput_of_swapCoverCT e6SwapCoverCTInput_holds

end Input

end CFSG.SeitzReduction.E6Pilot
