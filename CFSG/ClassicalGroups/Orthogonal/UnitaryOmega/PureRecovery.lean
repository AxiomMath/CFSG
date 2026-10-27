module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureCharts
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureStd
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeFar

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.PhanDn CFSG.GroupTheory

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem pureBlock_le_range_normDel {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1))
    (T : Finset (Fin (m + 1))) (hc : c ∉ T) :
    normPureBlock E (m + 1) T ≤ (normDel E hm c).range := by
  rw [range_normDel]
  apply (normPureBlock_le_normBlock E (m + 1) T).trans
  apply normBlock_mono E (m + 1)
  intro i hi
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  intro he
  subst i
  exact hc hi

private theorem recovery_cast {H : Type*} [Group H]
    (J : DΩ E 3 →* normOmega E 4) (hJ : Function.Injective J)
    (hJcomp : J.comp (qnExtΩ E (Fin.succEmb 3)) =
      (normOmegaCast E (Nat.le_succ 3)).comp
        (pureEmb E (Function.Embedding.refl (Fin 3))))
    (φ : DΩ E 3 →* H) (a : normOmega E 3 →* H)
    (h3 : φ.comp (qnExtΩ E (Fin.succEmb 3)) =
      a.comp (pureEmb E (Function.Embedding.refl (Fin 3))))
    (S : Finset (Fin 3)) :
    ((normPureBlock E 4 (S.map Fin.castSuccEmb)).comap J).map φ =
      ((normPureBlock E 4 (S.map Fin.castSuccEmb)).comap
        (normDel E (by norm_num : 2 ≤ 3) 3)).map a := by
  have hX : normPureBlock E 3 S ≤
      (pureEmb E (Function.Embedding.refl (Fin 3))).range := by
    rw [range_pureEmb, Finset.map_refl]
    exact normPureBlock_mono E 3 (Finset.subset_univ S)
  have hemb : Fin.castLEEmb (Nat.le_succ 3) = Fin.castSuccEmb := by
    ext i
    rfl
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, normDel_last,
    ← hemb, ← map_normPureBlock_normOmegaCast E (Nat.le_succ 3),
    Subgroup.comap_map_eq_self_of_injective (normOmegaCast_injective E (Nat.le_succ 3))]
  have hmap : (normPureBlock E 3 S).map (normOmegaCast E (Nat.le_succ 3)) =
      (((normPureBlock E 3 S).comap (pureEmb E (Function.Embedding.refl (Fin 3)))).map
        (qnExtΩ E (Fin.succEmb 3))).map J := by
    rw [Subgroup.map_map, hJcomp, ← Subgroup.map_map, Subgroup.map_comap_eq_self hX]
  rw [hmap, Subgroup.comap_map_eq_self_of_injective hJ, Subgroup.map_map, h3,
    ← Subgroup.map_map, Subgroup.map_comap_eq_self hX]

private theorem recovery_singleton_of_pairs {L H : Type*} [Group L] [Group H]
    (J : L →* normOmega E 4) (φ : L →* H) (hφ : Function.Injective φ)
    (a : Fin 4 → (normOmega E 3 →* H)) (ha : ∀ c, Function.Injective (a c))
    (hpair : ∀ i j : Fin 4, i ≠ j → ∀ c : Fin 4, c ∉ ({i,j} : Finset (Fin 4)) →
      transport J φ (normPureBlock E 4 {i,j}) =
        transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 {i,j}))
    (i c : Fin 4) (hc : c ≠ i) :
    transport J φ (normPureBlock E 4 {i}) =
      transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 {i}) := by
  have choose : ∀ i c : Fin 4, c ≠ i → ∃ j k : Fin 4,
      c ≠ j ∧ c ≠ k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide +kernel
  obtain ⟨j,k,hcj,hck,hij,hik,hjk⟩ := choose i c hc
  rw [← normPureBlock_pair_inf_pair E hij hik hjk,
    transport_inf hφ, transport_inf (ha c),
    hpair i j hij c (by simp [hc,hcj]), hpair i k hik c (by simp [hc,hck])]

private theorem recovery_of_pairs {L H : Type*} [Group L] [Group H]
    (J : L →* normOmega E 4) (hJrange : J.range = normPureBlock E 4 Finset.univ)
    (φ : L →* H) (hφ : Function.Injective φ)
    (a : Fin 4 → (normOmega E 3 →* H)) (ha : ∀ c, Function.Injective (a c))
    (hsup : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      normPureBlock E 4 {i,j} ⊔ normPureBlock E 4 {i,k} = normPureBlock E 4 {i,j,k})
    (hpair : ∀ i j : Fin 4, i ≠ j → ∀ c : Fin 4, c ∉ ({i,j} : Finset (Fin 4)) →
      transport J φ (normPureBlock E 4 {i,j}) =
        transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 {i,j}))
    (T : Finset (Fin 4)) (hT : T.Nonempty) (hT3 : T.card ≤ 3) (c : Fin 4) (hc : c ∉ T) :
    transport J φ (normPureBlock E 4 T) =
      transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 T) := by
  have hpos : 0 < T.card := hT.card_pos
  have hcards : T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  rcases hcards with hcard | hcard | hcard
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hcard
    exact recovery_singleton_of_pairs E J φ hφ a ha hpair i c (by simpa using hc)
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hcard
    exact hpair i j hij c hc
  · obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp hcard
    have hcij : c ∉ ({i,j} : Finset (Fin 4)) := fun h => hc ((by simp :
      ({i,j} : Finset (Fin 4)) ⊆ {i,j,k}) h)
    have hcik : c ∉ ({i,k} : Finset (Fin 4)) := fun h => hc ((by simp :
      ({i,k} : Finset (Fin 4)) ⊆ {i,j,k}) h)
    have hJpair (S : Finset (Fin 4)) : normPureBlock E 4 S ≤ J.range := by
      rw [hJrange]
      exact normPureBlock_mono E 4 (Finset.subset_univ S)
    rw [← hsup i j k hij hik hjk,
      transport_sup (hJpair {i,j}) (hJpair {i,k}),
      transport_sup (pureBlock_le_range_normDel E (by norm_num : 2 ≤ 3) c {i,j} hcij)
        (pureBlock_le_range_normDel E (by norm_num : 2 ≤ 3) c {i,k} hcik),
      hpair i j hij c hcij, hpair i k hik c hcik]

private theorem transported_pair_centralizer {L H : Type*} [Group L] [Group H]
    (J : L →* normOmega E 4) (hJ : Function.Injective J)
    (φ : L →* H) (hφ : Function.Injective φ) (i j k : Fin 4)
    (hC : ⁅Subgroup.centralizer (normPureBlock E 4 {i} : Set (normOmega E 4)) ⊓
        normPureBlock E 4 {i,j,k},
      Subgroup.centralizer (normPureBlock E 4 {i} : Set (normOmega E 4)) ⊓
        normPureBlock E 4 {i,j,k}⁆ = normPureBlock E 4 {j,k})
    (hi : normPureBlock E 4 {i} ≤ J.range)
    (hT : normPureBlock E 4 {i,j,k} ≤ J.range) :
    transport J φ (normPureBlock E 4 {j,k}) =
      ⁅Subgroup.centralizer (transport J φ (normPureBlock E 4 {i}) : Set H) ⊓
          transport J φ (normPureBlock E 4 {i,j,k}),
        Subgroup.centralizer (transport J φ (normPureBlock E 4 {i}) : Set H) ⊓
          transport J φ (normPureBlock E 4 {i,j,k})⁆ := by
  have hS : Subgroup.centralizer (normPureBlock E 4 {i} : Set (normOmega E 4)) ⊓
      normPureBlock E 4 {i,j,k} ≤ J.range := inf_le_right.trans hT
  rw [← hC, transport_commutator hJ hS hS, transport_centralizer_inf hJ hφ hi]

private theorem recovery_of_native_formulas {H : Type*} [Group H]
    (J : DΩ E 3 →* normOmega E 4) (hJ : Function.Injective J)
    (hJrange : J.range = normPureBlock E 4 Finset.univ)
    (hJcomp : J.comp (qnExtΩ E (Fin.succEmb 3)) =
      (normOmegaCast E (Nat.le_succ 3)).comp
        (pureEmb E (Function.Embedding.refl (Fin 3))))
    (a : Fin 4 → (normOmega E 3 →* H)) (ha : ∀ c, Function.Injective (a c))
    (R : Finset (Fin 4) → Subgroup H)
    (hR : ∀ (c : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a c) = R (S.image c.succAbove))
    (N : Subgroup (normOmega E 4))
    (hNsup : N ⊔ normPureBlock E 4 {0,1} = normPureBlock E 4 {0,1,3})
    (hC : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      ⁅Subgroup.centralizer (normPureBlock E 4 {i} : Set (normOmega E 4)) ⊓
          normPureBlock E 4 {i,j,k},
        Subgroup.centralizer (normPureBlock E 4 {i} : Set (normOmega E 4)) ⊓
          normPureBlock E 4 {i,j,k}⁆ = normPureBlock E 4 {j,k})
    (hPerf : Group.IsPerfect (normPureBlock E 4 {0,3}))
    (hsup : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      normPureBlock E 4 {i,j} ⊔ normPureBlock E 4 {i,k} = normPureBlock E 4 {i,j,k})
    (hIndependent : ∀ i j : Fin 4, i ≠ j → ∀ c d : Fin 4,
      c ∉ ({i,j} : Finset (Fin 4)) → d ∉ ({i,j} : Finset (Fin 4)) →
      transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 {i,j}) =
        transport (normDel E (by norm_num : 2 ≤ 3) d) (a d) (normPureBlock E 4 {i,j}))
    (hFar : ∀ z ∈ transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2)
        (normPureBlock E 4 {0,3}), ∀ y ∈ R {1,2}, Commute z y)
    (φ : DΩ E 3 →* H) (hφ : Function.Injective φ)
    (h3 : φ.comp (qnExtΩ E (Fin.succEmb 3)) =
      (a 3).comp (pureEmb E (Function.Embedding.refl (Fin 3))))
    (h0 : transport J φ N = transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2) N)
    (T : Finset (Fin 4)) (hT : T.Nonempty) (hT3 : T.card ≤ 3) (c : Fin 4) (hc : c ∉ T) :
    transport J φ (normPureBlock E 4 T) =
      transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 T) := by
  classical
  letI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have jr (S : Finset (Fin 4)) : normPureBlock E 4 S ≤ J.range := by
    rw [hJrange]
    exact normPureBlock_mono E 4 (Finset.subset_univ S)
  have dr (d : Fin 4) (S : Finset (Fin 4)) (hd : d ∉ S) :
      normPureBlock E 4 S ≤ (normDel E (by norm_num : 2 ≤ 3) d).range :=
    pureBlock_le_range_normDel E (by norm_num : 2 ≤ 3) d S hd
  have b3 (S : Finset (Fin 3)) :
      transport J φ (normPureBlock E 4 (S.map Fin.castSuccEmb)) =
        transport (normDel E (by norm_num : 2 ≤ 3) 3) (a 3)
          (normPureBlock E 4 (S.map Fin.castSuccEmb)) :=
    recovery_cast E J hJ hJcomp φ (a 3) h3 S
  have b01 := b3 ({0,1} : Finset (Fin 3))
  have b02 := b3 ({0,2} : Finset (Fin 3))
  have b12 := b3 ({1,2} : Finset (Fin 3))
  simp only [show ({0,1} : Finset (Fin 3)).map Fin.castSuccEmb = {0,1} by decide +kernel] at b01
  simp only [show ({0,2} : Finset (Fin 3)).map Fin.castSuccEmb = {0,2} by decide +kernel] at b02
  simp only [show ({1,2} : Finset (Fin 3)).map Fin.castSuccEmb = {1,2} by decide +kernel] at b12
  have b01two := b01.trans (hIndependent 0 1 (by decide) 3 2 (by decide) (by decide))
  have hNP : N ≤ normPureBlock E 4 {0,1,3} := le_sup_left.trans hNsup.le
  have b013 : transport J φ (normPureBlock E 4 {0,1,3}) =
      transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2)
        (normPureBlock E 4 {0,1,3}) := by
    rw [← hNsup, transport_sup (hNP.trans (jr {0,1,3})) (jr {0,1}),
      transport_sup (hNP.trans (dr 2 {0,1,3} (by decide))) (dr 2 {0,1} (by decide)),
      h0, b01two]
  have p1three : transport (normDel E (by norm_num : 2 ≤ 3) 3) (a 3)
      (normPureBlock E 4 {1}) = (normPureBlock E 3 {1}).map (a 3) := by
    have hcast : (normPureBlock E 3 {1}).map (normOmegaCast E (Nat.le_succ 3)) =
        normPureBlock E 4 {1} := by
      simpa only [show ({1} : Finset (Fin 3)).map (Fin.castLEEmb (Nat.le_succ 3)) = {1}
        by decide +kernel] using map_normPureBlock_normOmegaCast E (Nat.le_succ 3)
          ({1} : Finset (Fin 3))
    change ((normPureBlock E 4 {1}).comap (normDel E (by norm_num : 2 ≤ 3) 3)).map (a 3) = _
    rw [show normDel E (by norm_num : 2 ≤ 3) (3 : Fin 4) =
      normOmegaCast E (Nat.le_succ 3) from normDel_last E (by norm_num), ← hcast,
      Subgroup.comap_map_eq_self_of_injective (normOmegaCast_injective E (Nat.le_succ 3))]
  have p1 := b3 ({1} : Finset (Fin 3))
  simp only [show ({1} : Finset (Fin 3)).map Fin.castSuccEmb = {1} by decide +kernel] at p1
  have p1R : transport J φ (normPureBlock E 4 {1}) ≤ R {1,2} := by
    have mark := hR 3 ({1,2} : Finset (Fin 3)) (by simp) (by decide)
    simp only [show ({1,2} : Finset (Fin 3)).image (3 : Fin 4).succAbove = {1,2}
      by decide +kernel] at mark
    rw [p1, p1three, ← mark]
    exact Subgroup.map_mono ((normPureBlock_le_normBlock E 3 {1}).trans
      (normBlock_mono E 3 (by simp)))
  have b03 : transport J φ (normPureBlock E 4 {0,3}) =
      transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2)
        (normPureBlock E 4 {0,3}) := by
    let Z := transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2) (normPureBlock E 4 {0,3})
    let Y := transport J φ (normPureBlock E 4 {0,3})
    have yform := transported_pair_centralizer E J hJ φ hφ 1 0 3
      (hC 1 0 3 (by decide) (by decide) (by decide)) (jr {1}) (jr {1,0,3})
    simp only [show ({1,0,3} : Finset (Fin 4)) = {0,1,3} by decide +kernel] at yform
    have zp : ⁅Z,Z⁆ = Z := by
      letI := hPerf
      change ⁅transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2) (normPureBlock E 4 {0,3}),
        transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2) (normPureBlock E 4 {0,3})⁆ = _
      rw [← transport_commutator (normDel_injective E (by norm_num : 2 ≤ 3) 2)
        (dr 2 {0,3} (by decide)) (dr 2 {0,3} (by decide)), Subgroup.commutator_eq_self]
    have zT : Z ≤ transport J φ (normPureBlock E 4 {0,1,3}) := by
      rw [b013]
      exact Subgroup.map_mono (Subgroup.comap_mono (normPureBlock_mono E 4 (by simp)))
    have zC : Z ≤ Subgroup.centralizer (transport J φ (normPureBlock E 4 {1}) : Set H) := by
      intro z hz
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hFar z hz y (p1R hy)).eq.symm)
    have zY : Z ≤ Y := by
      calc
        Z = ⁅Z,Z⁆ := zp.symm
        _ ≤ ⁅Subgroup.centralizer (transport J φ (normPureBlock E 4 {1}) : Set H) ⊓
            transport J φ (normPureBlock E 4 {0,1,3}),
          Subgroup.centralizer (transport J φ (normPureBlock E 4 {1}) : Set H) ⊓
            transport J φ (normPureBlock E 4 {0,1,3})⁆ :=
          Subgroup.commutator_mono (le_inf zC zT) (le_inf zC zT)
        _ = Y := yform.symm
    have zcard : Nat.card Z = Nat.card (normPureBlock E 4 {0,3}) :=
      card_transport (normDel_injective E (by norm_num : 2 ≤ 3) 2) (ha 2)
        (dr 2 {0,3} (by decide))
    have ycard : Nat.card Y = Nat.card (normPureBlock E 4 {0,3}) :=
      card_transport hJ hφ (jr {0,3})
    letI : Finite Y := Finite.of_equiv ((normPureBlock E 4 {0,3}).comap J)
      (Subgroup.equivMapOfInjective ((normPureBlock E 4 {0,3}).comap J) φ hφ).toEquiv
    exact (Subgroup.eq_of_le_of_card_ge zY (by rw [ycard,zcard])).symm
  have b0two : transport J φ (normPureBlock E 4 {0}) =
      transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2) (normPureBlock E 4 {0}) := by
    rw [← normPureBlock_pair_inf_pair E (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 3), transport_inf hφ, transport_inf (ha 2), b01two, b03]
  have b13 : transport J φ (normPureBlock E 4 {1,3}) =
      transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2) (normPureBlock E 4 {1,3}) := by
    rw [transported_pair_centralizer E J hJ φ hφ 0 1 3
      (hC 0 1 3 (by decide) (by decide) (by decide)) (jr {0}) (jr {0,1,3}),
      transported_pair_centralizer E _ (normDel_injective E (by norm_num : 2 ≤ 3) 2) _ (ha 2) 0 1 3
        (hC 0 1 3 (by decide) (by decide) (by decide))
        (dr 2 {0} (by decide)) (dr 2 {0,1,3} (by decide)), b0two, b013]
  have b12zero := b12.trans (hIndependent 1 2 (by decide) 3 0 (by decide) (by decide))
  have b13zero := b13.trans (hIndependent 1 3 (by decide) 2 0 (by decide) (by decide))
  have b123 : transport J φ (normPureBlock E 4 {1,2,3}) =
      transport (normDel E (by norm_num : 2 ≤ 3) 0) (a 0) (normPureBlock E 4 {1,2,3}) := by
    rw [← hsup 1 2 3 (by decide) (by decide) (by decide),
      transport_sup (jr {1,2}) (jr {1,3}),
      transport_sup (dr 0 {1,2} (by decide)) (dr 0 {1,3} (by decide)), b12zero, b13zero]
  have b1zero : transport J φ (normPureBlock E 4 {1}) =
      transport (normDel E (by norm_num : 2 ≤ 3) 0) (a 0) (normPureBlock E 4 {1}) := by
    rw [← normPureBlock_pair_inf_pair E (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)
      (by decide : (2 : Fin 4) ≠ 3), transport_inf hφ, transport_inf (ha 0), b12zero, b13zero]
  have b23 : transport J φ (normPureBlock E 4 {2,3}) =
      transport (normDel E (by norm_num : 2 ≤ 3) 0) (a 0) (normPureBlock E 4 {2,3}) := by
    rw [transported_pair_centralizer E J hJ φ hφ 1 2 3
      (hC 1 2 3 (by decide) (by decide) (by decide)) (jr {1}) (jr {1,2,3}),
      transported_pair_centralizer E _ (normDel_injective E (by norm_num : 2 ≤ 3) 0) _ (ha 0) 1 2 3
        (hC 1 2 3 (by decide) (by decide) (by decide))
        (dr 0 {1} (by decide)) (dr 0 {1,2,3} (by decide)), b1zero, b123]
  have bases : ∀ i j : Fin 4, i ≠ j → ∃ d : Fin 4, d ∉ ({i,j} : Finset (Fin 4)) ∧
      transport J φ (normPureBlock E 4 {i,j}) =
        transport (normDel E (by norm_num : 2 ≤ 3) d) (a d) (normPureBlock E 4 {i,j}) := by
    intro i j hij
    have six : ∀ i j : Fin 4, i ≠ j →
        ({i,j} : Finset (Fin 4)) = {0,1} ∨ ({i,j} : Finset (Fin 4)) = {0,2} ∨
        ({i,j} : Finset (Fin 4)) = {1,2} ∨ ({i,j} : Finset (Fin 4)) = {0,3} ∨
        ({i,j} : Finset (Fin 4)) = {1,3} ∨ ({i,j} : Finset (Fin 4)) = {2,3} := by decide +kernel
    rcases six i j hij with h | h | h | h | h | h
    · rw [h]
      exact ⟨3, by decide, b01⟩
    · rw [h]
      exact ⟨3, by decide, b02⟩
    · rw [h]
      exact ⟨3, by decide, b12⟩
    · rw [h]
      exact ⟨2, by decide, b03⟩
    · rw [h]
      exact ⟨2, by decide, b13⟩
    · rw [h]
      exact ⟨0, by decide, b23⟩
  have pairs : ∀ i j : Fin 4, i ≠ j → ∀ d : Fin 4, d ∉ ({i,j} : Finset (Fin 4)) →
      transport J φ (normPureBlock E 4 {i,j}) =
        transport (normDel E (by norm_num : 2 ≤ 3) d) (a d) (normPureBlock E 4 {i,j}) := by
    intro i j hij d hd
    obtain ⟨e,he,hb⟩ := bases i j hij
    exact hb.trans (hIndependent i j hij e d he hd)
  exact recovery_of_pairs E J hJrange φ hφ a ha hsup pairs T hT hT3 c hc

private theorem transport_pair_eq_rangePurePair (hq : 4 ≤ Nat.card F)
    {G : Type} [Group G] {a : Fin 4 → (normOmega E 3 →* G)}
    (ha : ∀ c, Function.Injective (a c)) {R : Finset (Fin 4) → Subgroup G}
    (hR : ∀ (c : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a c) = R (S.image c.succAbove))
    {i j c : Fin 4} (hij : i ≠ j) (hc : c ∉ ({i,j} : Finset (Fin 4))) :
    transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 {i,j}) =
      rangePurePair R i j := by
  have hn : c ≠ i ∧ c ≠ j := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hc
  obtain ⟨i',hi'⟩ := Fin.exists_succAbove_eq hn.1.symm
  obtain ⟨j',hj'⟩ := Fin.exists_succAbove_eq hn.2.symm
  have hcomap := comap_normPureBlock_normDel E (by norm_num : 2 ≤ 3) c
    ({i',j'} : Finset (Fin 3))
  simp only [Finset.map_insert, Finset.map_singleton] at hcomap
  change (normPureBlock E 4 {c.succAbove i',c.succAbove j'}).comap
    (normDel E (by norm_num : 2 ≤ 3) c) = normPureBlock E 3 {i',j'} at hcomap
  rw [hi',hj'] at hcomap
  change ((normPureBlock E 4 {i,j}).comap (normDel E (by norm_num : 2 ≤ 3) c)).map (a c) = _
  rw [hcomap]
  exact (rangePurePair_eq_map (E := E) hq ha hR hij hn.1.symm hn.2.symm hi' hj').symm

theorem pureD4_recovery (hq : 4 ≤ 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {G : Type} [Group G] {a : Fin 4 → (normOmega E 3 →* G)}
    (ha : ∀ i, Function.Injective (a i)) {R : Finset (Fin 4) → Subgroup G}
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {φ : DΩ E 3 →* G} (hφ : Function.Injective φ)
    (h3 : φ.comp (qnExtΩ E (Fin.succEmb 3)) =
      (a 3).comp (pureEmb E (Function.Embedding.refl (Fin 3))))
    (h0 : ((stdNode E hK hq 0).comap (stdEmb E)).map φ =
      ((stdNode E hK hq 0).comap (normDel E (by norm_num : 2 ≤ 3) 2)).map (a 2))
    (T : Finset (Fin 4)) (hT : T.Nonempty) (hT3 : T.card ≤ 3) (c : Fin 4) (hc : c ∉ T) :
    ((normPureBlock E 4 T).comap (stdEmb E)).map φ =
      ((normPureBlock E 4 T).comap (normDel E (by norm_num : 2 ≤ 3) c)).map (a c) := by
  classical
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hcard : Nat.card K = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), E.finrank_eq]
  have hbase : Nat.card F = 2 ^ f := by
    apply Nat.mul_self_inj.mp
    simpa only [pow_two] using hcard.symm.trans hK
  have hqF : 4 ≤ Nat.card F := by rw [hbase]; exact hq
  have hsup : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      normPureBlock E 4 {i,j} ⊔ normPureBlock E 4 {i,k} = normPureBlock E 4 {i,j,k} := by
    intro i j k hij hik hjk
    have h := normPureBlock_pair_sup_pair E (by omega : 2 < Nat.card F)
      (i := j) (j := i) (k := k) hij.symm hjk hik
    rw [Finset.pair_comm j i, Finset.insert_comm j i] at h
    exact h
  have hIndependent : ∀ i j : Fin 4, i ≠ j → ∀ c d : Fin 4,
      c ∉ ({i,j} : Finset (Fin 4)) → d ∉ ({i,j} : Finset (Fin 4)) →
      transport (normDel E (by norm_num : 2 ≤ 3) c) (a c) (normPureBlock E 4 {i,j}) =
        transport (normDel E (by norm_num : 2 ≤ 3) d) (a d) (normPureBlock E 4 {i,j}) := by
    intro i j hij c d hc hd
    exact (transport_pair_eq_rangePurePair E hqF ha hR hij hc).trans
      (transport_pair_eq_rangePurePair E hqF ha hR hij hd).symm
  have hFar : ∀ z ∈ transport (normDel E (by norm_num : 2 ≤ 3) 2) (a 2)
      (normPureBlock E 4 {0,3}), ∀ y ∈ R {1,2}, Commute z y := by
    intro z hz y hy
    have hz' : z ∈ rangePurePair R 0 3 := by
      rw [← transport_pair_eq_rangePurePair E hqF ha hR (by decide : (0 : Fin 4) ≠ 3)
        (by decide : (2 : Fin 4) ∉ ({0,3} : Finset (Fin 4)))]
      exact hz
    exact commute_of_mem_rangePurePair_of_mem_pair (E := E) hqF ha hR
      (i := 0) (j := 3) (k := 1) (l := 2) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hz' hy
  exact recovery_of_native_formulas E (stdEmb E) (stdEmb_injective E) (range_stdEmb E)
    (stdEmb_comp_qnExtΩ_succ E) a ha R hR (stdNode E hK hq 0) (stdNode_zero_sup E hK hq)
    (fun i j k hij hik hjk =>
      commutator_centralizer_normPureBlock_singleton_inf_triple E hqF hij hik hjk)
    (isPerfect_normPureBlock_pair E (by decide : (0 : Fin 4) ≠ 3) hqF)
    hsup hIndependent hFar φ hφ h3 h0 T hT hT3 c hc

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end

