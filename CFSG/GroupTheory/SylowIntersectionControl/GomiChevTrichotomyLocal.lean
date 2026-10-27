module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
public import CFSG.Open.LocalVocabulary

import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.LieType.BorelTits.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem exists_isSylowOf_normalized_ctl {K Q : Subgroup G} (hQ : IsPGroup p Q)
    (hQK : Q ≤ normalizer (K : Set G)) :
    ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ normalizer (P : Set G) := by
  classical
  let : MulAction Q (Sylow p K) := MulAction.compHom (Sylow p K) (Subgroup.inclusion hQK)
  have : Finite (Sylow p K) := Sylow.finite_of_finiteIndex (Classical.choice (Sylow.nonempty))
  obtain ⟨P₀, hP₀fix⟩ :=
    hQ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p K)
      (not_dvd_card_sylow (p := p) (G := K))
  refine ⟨(P₀ : Subgroup K).map K.subtype, ⟨P₀, rfl⟩, ?_⟩
  have hforward : ∀ q : Q, ∀ x ∈ (P₀ : Subgroup K).map K.subtype,
      (q : G) * x * (q : G)⁻¹ ∈ (P₀ : Subgroup K).map K.subtype := by
    intro q x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix : (Subgroup.inclusion hQK q) • P₀ = P₀ := by
      simpa only [MulAction.compHom_smul_def] using MulAction.mem_fixedPoints.mp hP₀fix q
    have hsm : (Subgroup.inclusion hQK q) • (P₀ : Subgroup K) = (P₀ : Subgroup K) := by
      rw [← Sylow.pointwise_smul_def, hfix]
    have hmem : (Subgroup.inclusion hQK q) • k ∈ (P₀ : Subgroup K) := by
      have h := Subgroup.smul_mem_pointwise_smul k (Subgroup.inclusion hQK q) (P₀ : Subgroup K) hk
      rwa [hsm] at h
    have hmemG : (((Subgroup.inclusion hQK q) • k : K) : G) ∈ (P₀ : Subgroup K).map K.subtype :=
      Subgroup.mem_map_of_mem K.subtype hmem
    have hcoe : (((Subgroup.inclusion hQK q) • k : K) : G) = (q : G) * (k : G) * (q : G)⁻¹ := rfl
    rwa [hcoe] at hmemG
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward ⟨q, hq⟩ x
  · intro hx
    have h := hforward (⟨q, hq⟩ : Q)⁻¹ (q * x * q⁻¹) hx
    simpa [mul_assoc] using h

private theorem dvd_relIndex_of_lt_of_isPGroup_ctl {A B : Subgroup G} (hA : IsPGroup p A)
    (hBA : B < A) : p ∣ B.relIndex A := by
  have hne : B.subgroupOf A ≠ ⊤ := fun h =>
    hBA.ne (le_antisymm hBA.le (Subgroup.subgroupOf_eq_top.mp h))
  have hlt : 1 < (B.subgroupOf A).index := Subgroup.one_lt_index_of_ne_top hne
  obtain ⟨n, hn⟩ := hA.index (B.subgroupOf A)
  rw [Subgroup.relIndex, hn]
  exact dvd_pow_self p (fun h0 => by rw [h0, pow_zero] at hn; omega)

omit [Finite G] in
private theorem relIndex_sup_of_le_normalizer_ctl {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) : A.relIndex (B ⊔ A) = A.relIndex B := by
  have hN : (A.subgroupOf (B ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hB le_normalizer)
  have h1 := Subgroup.relIndex_sup_right (B.subgroupOf (B ⊔ A)) (A.subgroupOf (B ⊔ A))
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.relIndex_subgroupOf (le_refl (B ⊔ A)), Subgroup.relIndex_subgroupOf le_sup_left] at h1
  exact h1

private theorem relIndex_sup_eq_relIndex_inf_ctl {N B : Subgroup G}
    (hB : B ≤ normalizer (N : Set G)) : B.relIndex (N ⊔ B) = (N ⊓ B).relIndex N := by
  have h1 : (B ⊓ N).relIndex B * B.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
  have h2 : (B ⊓ N).relIndex N * N.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left
  have h3 : N.relIndex (N ⊔ B) = (B ⊓ N).relIndex B := by
    rw [sup_comm, relIndex_sup_of_le_normalizer_ctl hB, Subgroup.inf_relIndex_left]
  have h4 : 0 < (B ⊓ N).relIndex B :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (B ⊓ N).subgroupOf B))
  have h5 : B.relIndex (N ⊔ B) = (B ⊓ N).relIndex N :=
    Nat.eq_of_mul_eq_mul_left h4 (by rw [h1, ← h2, h3, mul_comm])
  rw [h5, inf_comm]

private theorem relIndex_dvd_relIndex_of_le_right_ctl {H A B : Subgroup G} (hAB : A ≤ B)
    (hNA : H ⊓ B ≤ normalizer (A : Set G)) : H.relIndex A ∣ H.relIndex B := by
  have h1 : (H ⊓ B).relIndex (A ⊔ (H ⊓ B)) = H.relIndex A := by
    rw [relIndex_sup_eq_relIndex_inf_ctl hNA]
    rw [show A ⊓ (H ⊓ B) = H ⊓ A by
      rw [← inf_assoc, inf_comm A H, inf_assoc, inf_eq_left.mpr hAB], Subgroup.inf_relIndex_right]
  exact ⟨(A ⊔ (H ⊓ B)).relIndex B, by
    rw [← Subgroup.inf_relIndex_right H B, ← h1]
    exact (Subgroup.relIndex_mul_relIndex (H ⊓ B) (A ⊔ (H ⊓ B)) B le_sup_right
      (sup_le hAB inf_le_right)).symm⟩

theorem exists_sylow_sup_le_inf_eq {L U W : Subgroup G} (hL : L.Normal) (hU : IsSylowOf p U L)
    (hW : IsPGroup p W) (hWU : W ≤ normalizer (U : Set G)) :
    ∃ T : Sylow p G, U ⊔ W ≤ (T : Subgroup G) ∧ (T : Subgroup G) ⊓ L = U := by
  have hUWp : IsPGroup p (U ⊔ W : Subgroup G) := hU.isPGroup.to_sup_of_normal_left' hW hWU
  obtain ⟨T, hTle⟩ := hUWp.exists_le_sylow
  have hTsyl : IsSylowOf p (T : Subgroup G) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, T.isPGroup', by rw [Subgroup.relIndex_top_right]; exact T.not_dvd_index⟩
  have hTLsyl : IsSylowOf p ((T : Subgroup G) ⊓ L) L :=
    hTsyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top L])
  exact ⟨T, hTle, hU.eq_of_le (le_inf (le_sup_left.trans hTle) hU.le) inf_le_right
    hTLsyl.isPGroup⟩

omit [Finite G] [Fact p.Prime] in
private theorem normalizer_map_conj_ctl {U₀ U : Subgroup G} {y : G}
    (h : U = U₀.map (MulAut.conj y).toMonoidHom) :
    normalizer (U : Set G) = (normalizer (U₀ : Set G)).map (MulAut.conj y).toMonoidHom := by
  rw [h, ← Subgroup.map_equiv_normalizer_eq U₀ (MulAut.conj y)]

omit [Finite G] [Fact p.Prime] in
private theorem inf_normalizer_map_conj_ctl {L U₀ U : Subgroup G} {y : G} (hyL : y ∈ L)
    (h : U = U₀.map (MulAut.conj y).toMonoidHom) :
    L ⊓ normalizer (U : Set G) =
      (L ⊓ normalizer (U₀ : Set G)).map (MulAut.conj y).toMonoidHom := by
  rw [normalizer_map_conj_ctl h, Subgroup.map_inf L (normalizer (U₀ : Set G))
    (MulAut.conj y).toMonoidHom (MulAut.conj y).injective,
    show L.map (MulAut.conj y).toMonoidHom = L from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer hyL)]

theorem exists_isSylowOf_le_normalizer {L P U₀ H : Subgroup G} (hPL : P ≤ L)
    (hU₀ : IsSylowOf p U₀ L) (hU₀P : L ⊓ normalizer (U₀ : Set G) ≤ P) (hH : IsPGroup p H)
    (hHP : H ≤ normalizer (P : Set G)) :
    ∃ U : Subgroup G, IsSylowOf p U L ∧ U ≤ P ∧ H ≤ normalizer (U : Set G) ∧
      L ⊓ normalizer (U : Set G) ≤ P := by
  obtain ⟨U, hUP', hHU⟩ := exists_isSylowOf_normalized_ctl (K := P) hH hHP
  have hUP : U ≤ P := hUP'.le
  have hU₀P' : U₀ ≤ P := (le_inf hU₀.le le_normalizer).trans hU₀P
  have hU₀P'' : IsSylowOf p U₀ P := hU₀.of_le hU₀P' hPL
  have hUL : U ≤ L := hUP.trans hPL
  have hcard : Nat.card U = Nat.card U₀ := by
    rw [IsSylowOf.card_eq hUP', IsSylowOf.card_eq hU₀P'']
  have hUsyl : IsSylowOf p U L := by
    refine isSylowOf_of_card hUL ?_
    rw [hcard, IsSylowOf.card_eq hU₀]
  obtain ⟨y, hyP, hy⟩ := hU₀P''.exists_mem_conj hUP'
  have hUeq : U = U₀.map (MulAut.conj y).toMonoidHom := by
    ext x
    rw [hy x]
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨y⁻¹ * x * y, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨z, hz, hzx⟩
      have hz' : y⁻¹ * x * y = z := by
        rw [← hzx]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [hz']
  have hfin := inf_normalizer_map_conj_ctl (L := L) (hPL hyP) hUeq
  refine ⟨U, hUsyl, hUP, hHU, ?_⟩
  rw [hfin]
  rintro x ⟨z, hz, hzx⟩
  have hzP : z ∈ P := hU₀P hz
  have hxP : x = y * z * y⁻¹ := by
    rw [← hzx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hxP]
  exact P.mul_mem (P.mul_mem hyP hzP) (P.inv_mem hyP)

theorem pCoreOf_inf_normalizer_inf_eq {L X H : Subgroup G} (hL : L.Normal) (hLX : L ≤ X)
    (hH : IsPGroup p H) (hHX : H ≤ X) (h : IsPIsolatedOver p (normalizer (H : Set G) ⊓ X) H) :
    pCoreOf p (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L := by
  refine le_antisymm ?_ ?_
  · have hQle : pCoreOf p (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ≤
        L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) := pCoreOf_le p _
    have hQL : pCoreOf p (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ≤ L :=
      hQle.trans inf_le_left
    have hQp : IsPGroup p (pCoreOf p (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))) :=
      pCoreOf_isPGroup p _
    have hN0L : normalizer (H : Set G) ≤ normalizer (L : Set G) := by
      rw [Subgroup.normalizer_eq_top L]
      exact le_top
    have hN0I : normalizer (H : Set G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
      (le_inf le_rfl hN0L).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hN0NI : normalizer (H : Set G) ≤
        normalizer (normalizer ((H ⊓ L : Subgroup G) : Set G) : Set G) :=
      hN0I.trans Subgroup.le_normalizer
    have hN0QI : normalizer (H : Set G) ≤
        normalizer (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) : Set G) :=
      (le_inf hN0L hN0NI).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hXN : normalizer (H : Set G) ⊓ X ≤
        normalizer (pCoreOf p (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) : Set G) :=
      (inf_le_left.trans hN0QI).trans
        (normalizer_le_normalizer_pCoreOf p (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)))
    have hQH := IsPIsolatedOver.le_of_inf_normalizer_le (K := X) h hH hHX hQp
      (hQL.trans hLX) hXN
    exact le_inf hQH hQL
  · exact le_pCoreOf_of_le_normalizer (r := p) (N := H ⊓ L)
      (le_inf inf_le_right le_normalizer) inf_le_right hH.to_inf_left

theorem IsPIsolatedOver.dvd_relIndex {H K : Subgroup G} (h : IsPIsolatedOver p K H)
    (hH : IsPGroup p H) (hHK : H ≤ K) (hKN : K ≤ normalizer (H : Set G)) :
    p ∣ H.relIndex K := by
  by_contra hp
  have hHsyl : IsSylowOf p H K := isSylowOf_iff.mpr ⟨hHK, hH, hp⟩
  obtain ⟨S, T, hS, hT, hne⟩ := h
  have key : ∀ A : Subgroup G, IsSylowOf p A K → A = H := by
    intro A hA
    refine hHsyl.eq_of_le ?_ hA.le hA.isPGroup
    have hinf : IsSylowOf p (A ⊓ H) H := hA.inf_of_le_normalizer hHK hKN
    have heq : H = A ⊓ H := IsSylowOf.eq_of_le hinf inf_le_right le_rfl hH
    rw [heq]
    exact inf_le_left
  exact hne (by rw [key S hS, key T hT]; exact Relation.EqvGen.refl _)

theorem dvd_relIndex_inf_normalizer {L H U : Subgroup G} (hH : IsPGroup p H)
    (hU : IsPGroup p U) (hUL : U ≤ L) (hHU : H ≤ normalizer (U : Set G)) (hUH : ¬ U ≤ H) :
    p ∣ H.relIndex (L ⊓ normalizer (H : Set G)) := by
  have hWp : IsPGroup p (U ⊔ H : Subgroup G) := hU.to_sup_of_normal_left' hH hHU
  have hHW : H < U ⊔ H :=
    lt_of_le_of_ne le_sup_right (fun heq => hUH (le_sup_left.trans (le_of_eq heq.symm)))
  have hHlt : H < (U ⊔ H) ⊓ normalizer (H : Set G) := lt_inf_normalizer_of_isPGroup hWp hHW
  obtain ⟨x, hx, hxH⟩ := SetLike.exists_of_lt hHlt
  obtain ⟨hxW, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxW' : x ∈ (U : Set G) * (H : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U H hHU]
    exact hxW
  obtain ⟨u, hu, h, hh, hux⟩ := hxW'
  have hu_eq : u = x * h⁻¹ := by rw [← hux]; group
  have huN : u ∈ normalizer (H : Set G) := by
    rw [hu_eq]
    exact (normalizer (H : Set G)).mul_mem hxN
      ((normalizer (H : Set G)).inv_mem (le_normalizer hh))
  have huH : u ∉ H := fun huH => hxH (by rw [← hux]; exact H.mul_mem huH hh)
  set A : Subgroup G := U ⊓ normalizer (H : Set G) with hA
  have hAp : IsPGroup p A := hU.to_inf_left
  have huA : u ∈ A := ⟨hu, huN⟩
  have hnot : ¬ A ≤ H := fun hle => huH (hle huA)
  have hltA : H ⊓ A < A :=
    lt_of_le_of_ne inf_le_right (fun heq => hnot (heq ▸ inf_le_left))
  have hdvdA : p ∣ H.relIndex A := by
    have hd := dvd_relIndex_of_lt_of_isPGroup_ctl hAp hltA
    rwa [Subgroup.inf_relIndex_right] at hd
  have hNA : H ⊓ (L ⊓ normalizer (H : Set G)) ≤ normalizer (A : Set G) := by
    have hC1 : H ⊓ (L ⊓ normalizer (H : Set G)) ≤ normalizer (U : Set G) :=
      (inf_le_left : H ⊓ (L ⊓ normalizer (H : Set G)) ≤ H).trans hHU
    have hC2 : H ⊓ (L ⊓ normalizer (H : Set G)) ≤
        normalizer (normalizer (H : Set G) : Set G) :=
      ((inf_le_right : H ⊓ (L ⊓ normalizer (H : Set G)) ≤ L ⊓ normalizer (H : Set G)).trans
        inf_le_right).trans le_normalizer
    rw [hA]
    exact (le_inf hC1 hC2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAB : A ≤ L ⊓ normalizer (H : Set G) := le_inf (inf_le_left.trans hUL) inf_le_right
  exact hdvdA.trans (relIndex_dvd_relIndex_of_le_right_ctl hAB hNA)

omit [Finite G] in
private theorem sup_inf_normalizer_le_ctl {L X H : Subgroup G} (hLX : L ≤ X)
    (hHX : H ≤ X) :
    (L ⊓ normalizer (H : Set G)) ⊔ H ≤ normalizer (H : Set G) ⊓ X :=
  le_inf (sup_le inf_le_right le_normalizer) (sup_le (inf_le_left.trans hLX) hHX)

omit [Finite G] in
private theorem sup_inf_normalizer_normal_ctl {L X H : Subgroup G} (hL : L.Normal)
    (hLX : L ≤ X) (hHX : H ≤ X) :
    (((L ⊓ normalizer (H : Set G)) ⊔ H).subgroupOf (normalizer (H : Set G) ⊓ X)).Normal := by
  have hle := sup_inf_normalizer_le_ctl hLX hHX
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_
  have hN0L : normalizer (H : Set G) ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top L]
    exact le_top
  have hN0A : normalizer (H : Set G) ≤ normalizer (L ⊓ normalizer (H : Set G) : Set G) :=
    (le_inf hN0L le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  refine (le_inf (inf_le_left.trans hN0A) inf_le_left).trans ?_
  exact Subgroup.inf_normalizer_le_normalizer_sup (L ⊓ normalizer (H : Set G)) H

private theorem relIndex_sup_inf_normalizer_ctl {L H : Subgroup G} (hL : L.Normal) :
    H.relIndex ((L ⊓ normalizer (H : Set G)) ⊔ H) =
      H.relIndex (L ⊓ normalizer (H : Set G)) := by
  set N0 := normalizer (H : Set G) with hN0
  set A := L ⊓ N0 with hA
  have hA_le : A ≤ N0 := inf_le_right
  have hH_le : H ≤ N0 := le_normalizer
  have hN0L : N0 ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top L]
    exact le_top
  have hN0A : N0 ≤ normalizer (A : Set G) := by
    rw [hA]
    exact (le_inf hN0L le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAnorm : (A.subgroupOf N0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le).mpr hN0A
  have hsup_le : A ⊔ H ≤ N0 := sup_le hA_le hH_le
  rw [← Subgroup.relIndex_subgroupOf hsup_le, Subgroup.subgroupOf_sup hA_le hH_le,
    relIndex_sup_eq_relIndex_of_normal, Subgroup.relIndex_subgroupOf hA_le]

theorem isPIsolatedOver_inf_normalizer {L X H : Subgroup G} (hL : L.Normal) (hLX : L ≤ X)
    (hH : IsPGroup p H) (hHX : H ≤ X) (h : IsPIsolatedOver p (normalizer (H : Set G) ⊓ X) H)
    (hp : p ∣ H.relIndex (L ⊓ normalizer (H : Set G))) :
    IsPIsolatedOver p (L ⊓ normalizer (H : Set G)) (H ⊓ L) := by
  set Y := (L ⊓ normalizer (H : Set G)) ⊔ H with hY
  have hYle : Y ≤ normalizer (H : Set G) ⊓ X := sup_inf_normalizer_le_ctl hLX hHX
  have hYnorm : (Y.subgroupOf (normalizer (H : Set G) ⊓ X)).Normal :=
    sup_inf_normalizer_normal_ctl hL hLX hHX
  have hrel : H.relIndex Y = H.relIndex (L ⊓ normalizer (H : Set G)) :=
    relIndex_sup_inf_normalizer_ctl hL
  have hYiso : IsPIsolatedOver p Y H :=
    h.of_isSubnormal_le_over hH inf_le_left le_sup_right le_rfl hYle hYnorm.isSubnormal
      (by rw [hrel]; exact hp)
  have hsup := (isPIsolatedOver_sup_iff hH (inf_le_right : L ⊓ normalizer (H : Set G) ≤
    normalizer (H : Set G))).mp hYiso
  simpa [hY, inf_assoc, inf_comm, inf_left_comm, inf_eq_left.mpr le_normalizer] using hsup

omit [Finite G] [Fact p.Prime] in
private theorem card_fixedPoints_eq_centralizer_ctl {L H : Subgroup G} [MulAction H L]
    (hsmul : ∀ (h : H) (x : L), ((h • x : L) : G) = (h : G) * (x : G) * (h : G)⁻¹) :
    Nat.card (MulAction.fixedPoints H L) = Nat.card ↥(L ⊓ centralizer (H : Set G)) := by
  have hset : ((L ⊓ centralizer (H : Set G)).subgroupOf L : Set L) =
      MulAction.fixedPoints H L := by
    ext x
    change x ∈ (L ⊓ centralizer (H : Set G)).subgroupOf L ↔ x ∈ MulAction.fixedPoints H L
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_fixedPoints]
    constructor
    · rintro ⟨-, hxC⟩ h
      refine Subtype.ext ?_
      rw [hsmul h x]
      rw [(Subgroup.mem_centralizer_iff.mp hxC) (h : G) h.2]
      group
    · intro hfixx
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 := congrArg (fun y : L => (y : G)) (hfixx ⟨h, hh⟩)
      rw [hsmul ⟨h, hh⟩ x] at h1
      calc h * (x : G) = (h * (x : G) * (h : G)⁻¹) * h := by group
        _ = (x : G) * h := by rw [h1]
  rw [← hset]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (H := L ⊓ centralizer (H : Set G)) (K := L) inf_le_left).toEquiv

omit [Finite G] [Fact p.Prime] in
private theorem inf_normalizer_eq_inf_centralizer_ctl {L H : Subgroup G} (hL : L.Normal)
    (hHL : H ⊓ L = ⊥) :
    L ⊓ normalizer (H : Set G) = L ⊓ centralizer (H : Set G) := by
  refine le_antisymm ?_ (inf_le_inf_left L (Subgroup.centralizer_le_normalizer (H : Set G)))
  intro x hx
  obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hconjH : x * h * x⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hxN h).mp hh
  have hcommH : x * h * x⁻¹ * h⁻¹ ∈ H := H.mul_mem hconjH (H.inv_mem hh)
  have hcommL : x * h * x⁻¹ * h⁻¹ ∈ L := by
    have hhL : h * x⁻¹ * h⁻¹ ∈ L := hL.conj_mem x⁻¹ (L.inv_mem hxL) h
    have heq : x * h * x⁻¹ * h⁻¹ = x * (h * x⁻¹ * h⁻¹) := by group
    rw [heq]
    exact L.mul_mem hxL hhL
  have hcomm1 : x * h * x⁻¹ * h⁻¹ = 1 :=
    Subgroup.mem_bot.mp (hHL ▸ Subgroup.mem_inf.mpr ⟨hcommH, hcommL⟩)
  have hxh : x * h * x⁻¹ = h := by
    have := congrArg (fun y => y * h) hcomm1
    simpa [mul_assoc] using this
  calc h * x = (x * h * x⁻¹) * x := by rw [hxh]
    _ = x * h := by group

theorem isPIsolatedOver_inf_centralizer {L X H : Subgroup G} (hL : L.Normal)
    (hpL : p ∣ Nat.card L) (hLX : L ≤ X) (hH : IsPGroup p H) (hHX : H ≤ X)
    (h : IsPIsolatedOver p (normalizer (H : Set G) ⊓ X) H) (hHL : H ⊓ L = ⊥) :
    IsPIsolatedOver p (L ⊓ centralizer (H : Set G)) ⊥ := by
  have hHLnorm : H ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top L]
    exact le_top
  let φ : H →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hHLnorm)
  let : MulAction H L := MulAction.compHom L φ
  have happly : ∀ (h : H) (x : L), ((h • x : L) : G) = (h : G) * (x : G) * (h : G)⁻¹ :=
    fun h x => Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hHLnorm h) x
  have hfix := card_fixedPoints_eq_centralizer_ctl happly
  have hfixedvd : p ∣ Nat.card (MulAction.fixedPoints H L) :=
    (Nat.modEq_zero_iff_dvd).mp
      ((hH.card_modEq_card_fixedPoints L).symm.trans (Nat.modEq_zero_iff_dvd.mpr hpL))
  have hNL := inf_normalizer_eq_inf_centralizer_ctl hL hHL
  have hAN : H.relIndex (L ⊓ normalizer (H : Set G)) =
      Nat.card ↥(L ⊓ normalizer (H : Set G)) := by
    rw [← Subgroup.inf_relIndex_right H (L ⊓ normalizer (H : Set G))]
    have hbot : H ⊓ (L ⊓ normalizer (H : Set G)) = ⊥ := by
      rw [← inf_assoc, hHL, bot_inf_eq]
    rw [hbot, Subgroup.relIndex_bot_left]
  have hpc : p ∣ H.relIndex (L ⊓ normalizer (H : Set G)) := by
    rw [hAN, hNL]
    rwa [hfix] at hfixedvd
  have h6 := isPIsolatedOver_inf_normalizer hL hLX hH hHX h hpc
  rw [hHL] at h6
  rwa [hNL] at h6

omit [Fact p.Prime] in
theorem exists_le_of_inf_normalizer_le {L X H Y : Subgroup G} (hL : L.Normal) (hLX : L ≤ X)
    (hHX : H ≤ X) (hp : p ∣ H.relIndex (L ⊓ normalizer (H : Set G)))
    (hLY : L ⊓ normalizer (H : Set G) ≤ Y) (hHY : H ≤ Y) :
    ∃ K : Subgroup G, H ≤ K ∧ K ≤ normalizer (H : Set G) ⊓ X ∧
      (K.subgroupOf (normalizer (H : Set G) ⊓ X)).IsSubnormal ∧ p ∣ H.relIndex K ∧ K ≤ Y := by
  refine ⟨(L ⊓ normalizer (H : Set G)) ⊔ H, le_sup_right, ?_, ?_, ?_, sup_le hLY hHY⟩
  · exact sup_inf_normalizer_le_ctl hLX hHX
  · exact (sup_inf_normalizer_normal_ctl hL hLX hHX).isSubnormal
  · rw [relIndex_sup_inf_normalizer_ctl hL]
    exact hp

end CFSG.GroupTheory
