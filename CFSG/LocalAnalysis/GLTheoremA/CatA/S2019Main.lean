module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs62
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Ambient

variable {G : Type} [Group G]

theorem subgroupOf_inf_centralizer_subgroup {H K D : Subgroup G} (hDH : D ≤ H) :
    (K ⊓ Subgroup.centralizer (D : Set G)).subgroupOf H =
      K.subgroupOf H ⊓ Subgroup.centralizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr Iff.rfl ⟨fun h d hd => Subtype.ext (h d hd), fun h d hd => ?_⟩
  exact congrArg Subtype.val (h ⟨d, hDH hd⟩ hd)

end Ambient

section Main

theorem i2019At_of_full (hFull : S2019Full) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I2019At G p := by
  classical
  intro hp hp2 q hq hq2 hqp B D K J hB hBK hQ hChev hC hDB hCD hrel hD hJ hBJ hcm T hTK hT2 hJT
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := hB.1
  have hBcard : Nat.card B = p ^ GLATwoLocalRank p G := hB.2.1
  set H : Subgroup G := K ⊔ B with hH
  have hKH : K ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hDH : D ≤ H := hDB.trans hBH
  have hJK : J ≤ K := (hJ.1).trans inf_le_left
  have hJH : J ≤ H := hJK.trans hKH
  have hTH : T ≤ H := hTK.trans hKH
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hBK
  have hinj : Function.Injective H.subtype := H.subtype_injective
  have hker : ¬ p ∣ Nat.card H.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff H.subtype).2 hinj, Subgroup.card_bot]
    exact hp.not_dvd_one
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  set B' : Subgroup ↥H := B.subgroupOf H with hB'
  set D' : Subgroup ↥H := D.subgroupOf H with hD'
  set J' : Subgroup ↥H := J.subgroupOf H with hJ'
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  have hKm : K'.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  have hBm : B'.map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
  have hDm : D'.map H.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDH
  have hJm : J'.map H.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJH
  have hTm : T'.map H.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTH
  haveI hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  have hBK' : B' ≤ Subgroup.normalizer (K' : Set ↥H) := by
    intro g _
    rw [Subgroup.normalizer_eq_top_iff.2 hK'n]
    exact Subgroup.mem_top _
  have hBel' : IsElemAbelian p B' := isElemAbelian_subgroupOf hBel H
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hBel
  have hcB' : Nat.card B' = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hcD' : Nat.card D' = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
  have hKB' : K' ⊔ B' = ⊤ := by
    have h1 : (K' ⊔ B').map H.subtype = H := by
      rw [Subgroup.map_sup, hKm, hBm]
    apply Subgroup.map_injective hinj
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  have hrank' : p ^ GLATwoLocalRank p ↥H ≤ Nat.card B' := by
    rw [hcB', hBcard]
    exact pow_le_pow_right₀ hp.one_lt.le (S11.twoLocalRank_le_top hp H)
  obtain ⟨e⟩ := nonempty_pQuot_equiv_subgroupOf p hKH
  have hQ' : CFSG.Open.IsQuasisimple (PQuot p K') := hQ.of_mulEquiv e
  let eKS : PSimple p K' ≃* PSimple p K := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hChev' : IsChevSimple q (PSimple p K') := chev_isChevSimple_of_mulEquiv eKS hChev
  have hmapcm : (B' ⊓ centModSubgroup p K').map H.subtype = B ⊓ centModSubgroup p K := by
    have hh := map_inf_centModSubgroup hp H.subtype hker hBK'
    rw [hh, hKm, hBm]
  have hcC' : Nat.card ↥(B' ⊓ centModSubgroup p K') = Nat.card ↥(B ⊓ centModSubgroup p K) := by
    rw [← hmapcm]
    exact (Subgroup.card_map_of_injective hinj).symm
  have hC' : B' ⊓ centModSubgroup p K' ≠ ⊥ := by
    intro h
    apply hC
    rw [h, Subgroup.card_bot] at hcC'
    exact Subgroup.eq_bot_of_card_eq _ hcC'.symm
  have hDB' : D' ≤ B' := fun x hx => hDB hx
  have hCD' : B' ⊓ centModSubgroup p K' ≤ D' := fun x hx =>
    hCD (by rw [← hmapcm]; exact ⟨x, hx, rfl⟩)
  have hrel' : (B' ⊓ centModSubgroup p K').relIndex D' ≤ p := by
    rw [relIndex_eq_of_card hCD hCD' hcC' hcD']
    exact hrel
  have hD'' : p ^ 2 * Nat.card D' ≤ Nat.card B' := by
    rw [hcD', hcB']; exact hD
  have hJ'' : GLAPComponent p (K' ⊓ Subgroup.centralizer (D' : Set ↥H)) J' := by
    have h1 := glaPComponent_subgroupOf hp (H := H) (X := K ⊓ Subgroup.centralizer (D : Set G))
      (inf_le_left.trans hKH) hJ
    rwa [subgroupOf_inf_centralizer_subgroup hDH] at h1
  have hBJ' : B' ≤ Subgroup.normalizer (J' : Set ↥H) := by
    intro b hb
    have h1 : H.subtype b ∈ Subgroup.normalizer (J : Set G) := hBJ hb
    rw [← hJm] at h1
    exact (mem_normalizer_map_iff_inj H.subtype hinj).1 h1
  have hcm' : ∀ b ∈ B', CentMod p J' b ↔ b ∈ D' := by
    intro b hb
    have h2 : b ∈ centModSubgroup p J' ↔ (b : G) ∈ centModSubgroup p J := by
      have := mem_centModSubgroup_map_iff_inj hp H.subtype hinj (J := J') (b := b)
      rwa [hJm] at this
    rw [centMod_iff, h2, ← centMod_iff, hcm (b : G) hb]
    exact Iff.rfl
  have hTK' : T' ≤ K' := fun x hx => hTK hx
  have hT2' : IsPGroup 2 T' := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hJT' : J' ≤ Subgroup.normalizer ((T' ⊔ GLAPPrimeCoreOf p K' : Subgroup ↥H) : Set ↥H) := by
    intro j hj
    have h1 : H.subtype j ∈ Subgroup.normalizer ((T ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G) :=
      hJT hj
    have h2 : (T' ⊔ GLAPPrimeCoreOf p K').map H.subtype = T ⊔ GLAPPrimeCoreOf p K := by
      rw [Subgroup.map_sup, hTm, map_subtype_glaPPrimeCoreOf_subgroupOf p hKH]
    rw [← h2] at h1
    exact (mem_normalizer_map_iff_inj H.subtype hinj).1 h1
  have key := s2019_A hFull hp hp2 hq hq2 hqp hBel' hKB' hrank' hBK' hQ' hChev' hC' hDB' hCD' hrel'
    hD'' hJ'' hBJ' hcm' hTK' hT2' hJT'
  have key2 := Subgroup.map_mono (f := H.subtype) key
  rw [Subgroup.map_commutator, hTm, hJm, map_subtype_glaPPrimeCoreOf_subgroupOf p hKH] at key2
  exact key2

theorem i2019At_of_facts_amb (hCl : S2019FactClassical) (hA1 : S2019FactA1)
    (hEx : S2019FactExceptional) (hAm : S2019FactAmbiguous) (G : Type) [Group G] [Finite G]
    (p : ℕ) : I2019At G p :=
  i2019At_of_full (s2019Full_of_facts hCl hA1 hEx hAm) G p

end Main

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
