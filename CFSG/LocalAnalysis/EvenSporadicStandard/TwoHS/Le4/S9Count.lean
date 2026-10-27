module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Orbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HIndex
public import Certificates.Certificate26753

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier
  Matrix

section Model

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : G}


structure ModelData (G : Type) [Group G] (L : Subgroup G) (y : G) where
  hΛ : HSCtx
  ι : L ≃* HSCover
  y₁ : G
  mem : y₁ ∈ L ⊔ zpowers y
  not_mem : y₁ ∉ L
  sq : y₁ * y₁ = 1
  conj : ∀ x : L, y₁ * (x : G) * y₁⁻¹ = (ι.symm (hΛ.sigma (ι x)) : G)

namespace ModelData

variable {y : G}

theorem conj_bL (M : ModelData G L y) (w : HSCover) :
    M.y₁ * bL M.ι w * M.y₁⁻¹ = bL M.ι (M.hΛ.sigma w) := by
  have := M.conj (M.ι.symm w)
  simpa [bL] using this

theorem conj0 (M : ModelData G L y) (l w : HSCover) :
    bL M.ι l * bL M.ι w * (bL M.ι l)⁻¹ = bL M.ι (l * w * l⁻¹) := by
  simp [bL_mul, bL_inv]

theorem conj1 (M : ModelData G L y) (l w : HSCover) :
    (bL M.ι l * M.y₁) * bL M.ι w * (bL M.ι l * M.y₁)⁻¹ =
      bL M.ι (l * M.hΛ.sigma w * l⁻¹) := by
  rw [bL_mul, bL_mul, bL_inv, ← M.conj_bL]
  group

theorem normalizer_of_basis (hF : FourHyp G L f) (M : ModelData G L y) {x : G}
    (hx : ∀ j : Fin 4, x * bas M.ι f j * x⁻¹ ∈ (basisCoord M.hΛ hF M.ι).E) :
    x ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) := by
  have hE : (basisCoord M.hΛ hF M.ι).E = closure (Set.range (bas M.ι f)) :=
    ECoord.ofBasis_E _ _ _ _
  apply mem_normalizer_of_conj_mem
  rw [hE] at hx ⊢
  intro g hg
  refine conj_mem_of_closure (fun s hs => ?_) g hg
  obtain ⟨j, rfl⟩ := hs
  exact hx j

theorem elt_fVec (hF : FourHyp G L f) (M : ModelData G L y) :
    (basisCoord M.hΛ hF M.ι).elt fVec = f := by
  rw [← vec_f M.hΛ hF M.ι]
  exact (basisCoord M.hΛ hF M.ι).elt_vec (f_mem_E M.hΛ hF M.ι)

theorem elt_neg_fVec (hF : FourHyp G L f) (M : ModelData G L y) :
    (basisCoord M.hΛ hF M.ι).elt (vecOfList [0, 0, 3, 0]) = f⁻¹ := by
  have : vecOfList [0, 0, 3, 0] = -fVec := by
    funext i
    fin_cases i <;> decide
  rw [this, ECoord.elt_neg, elt_fVec hF M]

theorem elt_single (hF : FourHyp G L f) (M : ModelData G L y) (j : Fin 4) :
    (basisCoord M.hΛ hF M.ι).elt (Pi.single j 1) = bas M.ι f j := by
  rw [basisCoord_elt]
  exact basisElt_single _ _

theorem gamma1Data_lt : ∀ x ∈ gamma1Data, x < 4 := by decide

theorem gamma2Data_lt : ∀ x ∈ gamma2Data, x < 4 := by decide

theorem hx1 (hF : FourHyp G L f) (M : ModelData G L y) (j : Fin 4) :
    bL M.ι gamma1L * bas M.ι f j * (bL M.ι gamma1L)⁻¹ =
      (basisCoord M.hΛ hF M.ι).elt (vecOfList (colOf gamma1Data j.val)) := by
  fin_cases j
  · show bL M.ι gamma1L * bL M.ι (bet 0) * (bL M.ι gamma1L)⁻¹ = _
    rw [M.conj0, M.hΛ.real1 (by norm_num : 0 < 3)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt gamma1Data_lt _ i) (by decide)
  · show bL M.ι gamma1L * bL M.ι (bet 1) * (bL M.ι gamma1L)⁻¹ = _
    rw [M.conj0, M.hΛ.real1 (by norm_num : 1 < 3)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt gamma1Data_lt _ i) (by decide)
  · show bL M.ι gamma1L * f * (bL M.ι gamma1L)⁻¹ = _
    have h : colOf gamma1Data 2 = [0, 0, 1, 0] := by decide
    simp only [h]
    rw [show vecOfList [0, 0, 1, 0] = fVec from rfl, elt_fVec hF M, bL_comm_f hF M.ι]
    group
  · show bL M.ι gamma1L * bL M.ι (bet 2) * (bL M.ι gamma1L)⁻¹ = _
    rw [M.conj0, M.hΛ.real1 (by norm_num : 2 < 3)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt gamma1Data_lt _ i) (by decide)

theorem hx2 (hF : FourHyp G L f) (hyy : y * y = 1) (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) (M : ModelData G L y)
    (j : Fin 4) :
    (bL M.ι gamma2L * M.y₁) * bas M.ι f j * (bL M.ι gamma2L * M.y₁)⁻¹ =
      (basisCoord M.hΛ hF M.ι).elt (vecOfList (colOf gamma2Data j.val)) := by
  fin_cases j
  · show (bL M.ι gamma2L * M.y₁) * bL M.ι (bet 0) * (bL M.ι gamma2L * M.y₁)⁻¹ = _
    rw [M.conj1, M.hΛ.real2 (by norm_num : 0 < 3)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt gamma2Data_lt _ i) (by decide)
  · show (bL M.ι gamma2L * M.y₁) * bL M.ι (bet 1) * (bL M.ι gamma2L * M.y₁)⁻¹ = _
    rw [M.conj1, M.hΛ.real2 (by norm_num : 1 < 3)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt gamma2Data_lt _ i) (by decide)
  · show (bL M.ι gamma2L * M.y₁) * f * (bL M.ι gamma2L * M.y₁)⁻¹ = _
    have h : colOf gamma2Data 2 = [0, 0, 3, 0] := by decide
    simp only [h]
    rw [elt_neg_fVec hF M]
    have hy₁f : M.y₁ * f * M.y₁⁻¹ = f⁻¹ := H1_conj_f_of_not_mem hF hyy hyf hN M.mem M.not_mem
    calc bL M.ι gamma2L * M.y₁ * f * (bL M.ι gamma2L * M.y₁)⁻¹
        = bL M.ι gamma2L * (M.y₁ * f * M.y₁⁻¹) * (bL M.ι gamma2L)⁻¹ := by group
      _ = bL M.ι gamma2L * f⁻¹ * (bL M.ι gamma2L)⁻¹ := by rw [hy₁f]
      _ = f⁻¹ := by
        have := bL_comm_f hF M.ι gamma2L
        calc bL M.ι gamma2L * f⁻¹ * (bL M.ι gamma2L)⁻¹
            = (bL M.ι gamma2L * f * (bL M.ι gamma2L)⁻¹)⁻¹ := by group
          _ = f⁻¹ := by rw [this]; group
  · show (bL M.ι gamma2L * M.y₁) * bL M.ι (bet 2) * (bL M.ι gamma2L * M.y₁)⁻¹ = _
    rw [M.conj1, M.hΛ.real2 (by norm_num : 2 < 3)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt gamma2Data_lt _ i) (by decide)

theorem basisElt_eq (hF : FourHyp G L f) (M : ModelData G L y) (v : V4) :
    basisElt (bas M.ι f) v =
      bL M.ι (bet 0 ^ (v 0).val * bet 1 ^ (v 1).val * bet 2 ^ (v 3).val) * f ^ (v 2).val := by
  have hc : f ^ (v 2).val * bL M.ι (bet 2) ^ (v 3).val =
      bL M.ι (bet 2) ^ (v 3).val * f ^ (v 2).val :=
    ((((show Commute (bL M.ι (bet 2)) f from bL_comm_f hF M.ι _).pow_left (v 3).val).pow_right
      (v 2).val)).eq.symm
  simp only [basisElt, bas, bL_mul, bL_pow]
  calc bL M.ι (bet 0) ^ (v 0).val * bL M.ι (bet 1) ^ (v 1).val * f ^ (v 2).val *
        bL M.ι (bet 2) ^ (v 3).val
      = bL M.ι (bet 0) ^ (v 0).val * bL M.ι (bet 1) ^ (v 1).val *
          (f ^ (v 2).val * bL M.ι (bet 2) ^ (v 3).val) := by rw [mul_assoc _ (f ^ _)]
    _ = bL M.ι (bet 0) ^ (v 0).val * bL M.ι (bet 1) ^ (v 1).val *
          (bL M.ι (bet 2) ^ (v 3).val * f ^ (v 2).val) := by rw [hc]
    _ = _ := by rw [← mul_assoc]

theorem inter_mem_E1L (hF : FourHyp G L f) (M : ModelData G L y) {e : G}
    (he : e ∈ (basisCoord M.hΛ hF M.ι).E) (heL : e ∈ L) : M.ι ⟨e, heL⟩ ∈ E1L := by
  set C := basisCoord M.hΛ hF M.ι
  have hev : e = basisElt (bas M.ι f) (C.vec e) := by
    rw [← basisCoord_elt M.hΛ hF M.ι, C.elt_vec he]
  rw [basisElt_eq hF M] at hev
  set v := C.vec e
  set X := bet 0 ^ (v 0).val * bet 1 ^ (v 1).val * bet 2 ^ (v 3).val with hX
  have hfd : f ^ (v 2).val ∈ L := by
    have : f ^ (v 2).val = (bL M.ι X)⁻¹ * e := by
      rw [hev]; group
    rw [this]
    exact L.mul_mem (L.inv_mem (bL_mem M.ι X)) heL
  have hd4 : (v 2).val < 4 := ZMod.val_lt _
  have heven : (v 2).val % 2 = 0 := by
    by_contra hodd
    apply f_not_mem_L hF
    obtain ⟨m, hm⟩ : ∃ m, (v 2).val = 2 * m + 1 := ⟨(v 2).val / 2, by omega⟩
    rw [hm] at hfd
    have h1 : f ^ (2 * m + 1) * ((f ^ 2) ^ m)⁻¹ = f := by
      rw [pow_succ', pow_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [← h1]
    exact L.mul_mem hfd (L.inv_mem (L.pow_mem hF.sq_mem m))
  have hfd2 : f ^ (v 2).val = bL M.ι (tL ^ ((v 2).val / 2)) := by
    rw [bL_pow, bL_tL M.hΛ hF M.ι, ← pow_mul]
    congr 1
    omega
  have he2 : e = bL M.ι (X * tL ^ ((v 2).val / 2)) := by
    rw [bL_mul, ← hfd2]
    exact hev
  have h3 : M.ι ⟨e, heL⟩ = X * tL ^ ((v 2).val / 2) := by
    have : (⟨e, heL⟩ : L) = M.ι.symm (X * tL ^ ((v 2).val / 2)) := Subtype.ext he2
    rw [this, MulEquiv.apply_symm_apply]
  rw [h3]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _)
    (Subgroup.pow_mem _ ?_ _)) (Subgroup.pow_mem _ ?_ _)) (Subgroup.pow_mem _ ?_ _) <;>
    exact Subgroup.subset_closure (by simp)

theorem normalizes_E1L (hF : FourHyp G L f) (M : ModelData G L y) {x : G} (hxL : x ∈ L)
    (hxt : x * f ^ 2 = f ^ 2 * x)
    (hxN : x ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G)) :
    M.ι ⟨x, hxL⟩ ∈ normalizer (E1L : Set HSCover) := by
  have := M.hΛ.finite
  apply mem_normalizer_of_conj_mem
  intro w hw
  refine conj_mem_of_closure (S := ({bet 0, bet 1, bet 2, tL} : Set HSCover)) (fun s hs => ?_) w hw
  have hconj : ∀ g : L, (g : G) ∈ (basisCoord M.hΛ hF M.ι).E →
      M.ι ⟨x, hxL⟩ * M.ι g * (M.ι ⟨x, hxL⟩)⁻¹ ∈ E1L := by
    intro g hg
    have h1 : x * (g : G) * x⁻¹ ∈ (basisCoord M.hΛ hF M.ι).E :=
      (mem_normalizer_iff.1 hxN g).1 hg
    have h2 : x * (g : G) * x⁻¹ ∈ L := L.mul_mem (L.mul_mem hxL g.2) (L.inv_mem hxL)
    have := inter_mem_E1L hF M h1 h2
    have e : (⟨x * (g : G) * x⁻¹, h2⟩ : L) = ⟨x, hxL⟩ * g * ⟨x, hxL⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at this
    exact this
  rcases hs with rfl | rfl | rfl | rfl
  · have := hconj (M.ι.symm (bet 0)) (bas_mem M.hΛ hF M.ι 0)
    rwa [MulEquiv.apply_symm_apply] at this
  · have := hconj (M.ι.symm (bet 1)) (bas_mem M.hΛ hF M.ι 1)
    rwa [MulEquiv.apply_symm_apply] at this
  · have := hconj (M.ι.symm (bet 2)) (bas_mem M.hΛ hF M.ι 3)
    rwa [MulEquiv.apply_symm_apply] at this
  · have hg : (M.ι.symm tL : G) = f ^ 2 := bL_tL M.hΛ hF M.ι
    have h1 : x * (M.ι.symm tL : G) * x⁻¹ = (M.ι.symm tL : G) := by
      rw [hg, hxt]
      group
    have e : (⟨x, hxL⟩ : L) * M.ι.symm tL * ⟨x, hxL⟩⁻¹ = M.ι.symm tL := Subtype.ext h1
    have : M.ι ⟨x, hxL⟩ * tL * (M.ι ⟨x, hxL⟩)⁻¹ = tL := by
      have := congrArg M.ι e
      simpa [map_mul, map_inv] using this
    rw [this]
    exact Subgroup.subset_closure (by simp)

section Bound


theorem card_L_inf_le (hF : FourHyp G L f) (M : ModelData G L y) :
    Nat.card ↥(L ⊓ (centralizer ({f ^ 2} : Set G) ⊓
      normalizer ((basisCoord M.hΛ hF M.ι).E : Set G))) ≤ 21504 := by
  have := M.hΛ.finite
  let T : Subgroup G := L ⊓ (centralizer ({f ^ 2} : Set G) ⊓
      normalizer ((basisCoord M.hΛ hF M.ι).E : Set G))
  let φ : T → ↥(normalizer (E1L : Set HSCover)) := fun x =>
    ⟨M.ι ⟨(x : G), x.2.1⟩, normalizes_E1L hF M x.2.1
      (mem_centralizer_singleton_iff.1 x.2.2.1) x.2.2.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    have h2 := M.ι.injective h1
    exact Subtype.ext (Subtype.mk.inj h2)
  calc Nat.card T ≤ Nat.card ↥(normalizer (E1L : Set HSCover)) :=
        Nat.card_le_card_of_injective φ hinj
    _ ≤ 21504 := card_normalizer_E1L_le M.hΛ

theorem card_NE_le (hF : FourHyp G L f) (hyy : y * y = 1) (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) (M : ModelData G L y) :
    Nat.card ↥(centralizer ({f ^ 2} : Set G) ⊓
      normalizer ((basisCoord M.hΛ hF M.ι).E : Set G)) ≤ 86016 := by
  set 𝒩 : Subgroup G := centralizer ({f ^ 2} : Set G) ⊓
    normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) with h𝒩
  have hLc : L ≤ centralizer ({f ^ 2} : Set G) := by
    intro l hl
    rw [mem_centralizer_singleton_iff]
    exact ((show Commute l f from comm_f_of_mem hF hl).pow_right 2).eq
  have hidx : L.relIndex (centralizer ({f ^ 2} : Set G)) ≤ 4 :=
    relindex_le_four_of_inv hLc (fun l hl => comm_f_of_mem hF hl) hF.sq_mem hyy
      (y_mem_normalizer hF hN) hN hyf
  have hne : L.relIndex (centralizer ({f ^ 2} : Set G)) ≠ 0 := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := centralizer ({f ^ 2} : Set G))
    intro h0
    rw [h0, zero_mul] at h
    have : 0 < Nat.card (centralizer ({f ^ 2} : Set G)) := Nat.card_pos
    omega
  have h1 : L.relIndex 𝒩 ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left hne).trans hidx
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := 𝒩)
  have h3 : Nat.card ↥(L ⊓ 𝒩) ≤ 21504 := card_L_inf_le hF M
  calc Nat.card 𝒩 = L.relIndex 𝒩 * Nat.card ↥(L ⊓ 𝒩) := h2.symm
    _ ≤ 4 * 21504 := Nat.mul_le_mul h1 h3
    _ = 86016 := by norm_num

end Bound

section Realization


theorem real1_ex (hF : FourHyp G L f) (M : ModelData G L y) :
    ∃ x : G, x * f ^ 2 = f ^ 2 * x ∧ x ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) ∧
      (basisCoord M.hΛ hF M.ι).mat x = gamma1Mat := by
  have hN : bL M.ι gamma1L ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) :=
    normalizer_of_basis hF M fun j => by
      rw [hx1 hF M j]
      exact (basisCoord M.hΛ hF M.ι).elt_mem _
  refine ⟨bL M.ι gamma1L, ?_, hN, ?_⟩
  · exact ((show Commute (bL M.ι gamma1L) f from bL_comm_f hF M.ι _).pow_right 2).eq
  · exact mat_eq_of_conj_basis fun j => by rw [elt_single hF M j]; exact hx1 hF M j

theorem real2_ex (hF : FourHyp G L f) (hyy : y * y = 1) (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) (M : ModelData G L y) :
    ∃ x : G, x * f ^ 2 = f ^ 2 * x ∧ x ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) ∧
      (basisCoord M.hΛ hF M.ι).mat x = gamma2Mat := by
  have hnorm : bL M.ι gamma2L * M.y₁ ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) :=
    normalizer_of_basis hF M fun j => by
      rw [hx2 hF hyy hyf hN M j]
      exact (basisCoord M.hΛ hF M.ι).elt_mem _
  refine ⟨bL M.ι gamma2L * M.y₁, ?_, hnorm, ?_⟩
  · have hy₁f : M.y₁ * f * M.y₁⁻¹ = f⁻¹ := H1_conj_f_of_not_mem hF hyy hyf hN M.mem M.not_mem
    have hsq : M.y₁ * f ^ 2 * M.y₁⁻¹ = f ^ 2 := by
      have e : M.y₁ * f ^ 2 * M.y₁⁻¹ = (M.y₁ * f * M.y₁⁻¹) ^ 2 := conj_pow.symm
      rw [e, hy₁f]
      have h2 : f ^ 2 * f ^ 2 = 1 := by rw [← pow_add]; exact hF.pow_four
      calc f⁻¹ ^ 2 = (f ^ 2)⁻¹ := by group
        _ = f ^ 2 := inv_eq_of_mul_eq_one_right h2
    have hy₁c : M.y₁ * f ^ 2 = f ^ 2 * M.y₁ := by
      calc M.y₁ * f ^ 2 = (M.y₁ * f ^ 2 * M.y₁⁻¹) * M.y₁ := by group
        _ = f ^ 2 * M.y₁ := by rw [hsq]
    have hbc : bL M.ι gamma2L * f ^ 2 = f ^ 2 * bL M.ι gamma2L :=
      ((show Commute (bL M.ι gamma2L) f from bL_comm_f hF M.ι _).pow_right 2).eq
    calc bL M.ι gamma2L * M.y₁ * f ^ 2 = bL M.ι gamma2L * (M.y₁ * f ^ 2) := by rw [mul_assoc]
      _ = bL M.ι gamma2L * (f ^ 2 * M.y₁) := by rw [hy₁c]
      _ = (bL M.ι gamma2L * f ^ 2) * M.y₁ := by rw [mul_assoc]
      _ = f ^ 2 * (bL M.ι gamma2L * M.y₁) := by rw [hbc, mul_assoc]
  · exact mat_eq_of_conj_basis fun j => by rw [elt_single hF M j]; exact hx2 hF hyy hyf hN M j

theorem real_q0 (hF : FourHyp G L f) (hyy : y * y = 1) (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) (M : ModelData G L y) :
    ∀ A ∈ q0List, ∃ x : G, x * f ^ 2 = f ^ 2 * x ∧
      x ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) ∧
      (basisCoord M.hΛ hF M.ι).mat x = A := by
  set C := basisCoord M.hΛ hF M.ι
  have hLF : ListFacts := Certificates.certificate26753
  refine hLF.closure {A | ∃ x : G, x * f ^ 2 = f ^ 2 * x ∧ x ∈ normalizer (C.E : Set G) ∧
      C.mat x = A} ?_ ?_ ?_ ?_
  · rintro A ⟨x, hxt, hxN, rfl⟩ B ⟨x', hxt', hxN', rfl⟩
    refine ⟨x * x', ?_, Subgroup.mul_mem _ hxN hxN', C.mat_mul hxN hxN'⟩
    calc x * x' * f ^ 2 = x * (x' * f ^ 2) := by rw [mul_assoc]
      _ = x * (f ^ 2 * x') := by rw [hxt']
      _ = (x * f ^ 2) * x' := by rw [mul_assoc]
      _ = f ^ 2 * (x * x') := by rw [hxt, mul_assoc]
  · exact ⟨1, by simp, Subgroup.one_mem _, C.mat_one⟩
  · exact real1_ex hF M
  · exact real2_ex hF hyy hyf hN M

theorem count_core (hF : FourHyp G L f) (hyy : y * y = 1) (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) (M : ModelData G L y) :
    (∀ x : G, x * f ^ 2 = f ^ 2 * x → x ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) →
      (basisCoord M.hΛ hF M.ι).mat x ∈ q0List) ∧
    (∀ x : G, x * f ^ 2 = f ^ 2 * x → (∀ e ∈ (basisCoord M.hΛ hF M.ι).E, x * e = e * x) →
      x ∈ (basisCoord M.hΛ hF M.ι).E) := by
  have hLF : ListFacts := Certificates.certificate26753
  have hb := card_NE_le hF hyy hyf hN M
  refine (basisCoord M.hΛ hF M.ι).count_normalizer (t := f ^ 2)
    (pow_mem (f_mem_E M.hΛ hF M.ι) 2) q0List hLF.q0_nodup (real_q0 hF hyy hyf hN M) ?_
  rw [hLF.q0_len]
  exact hb

end Realization

end ModelData

end Model

end CFSG.EvenSporadicStandard.TwoHS
