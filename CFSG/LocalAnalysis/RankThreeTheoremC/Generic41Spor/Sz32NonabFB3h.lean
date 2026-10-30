module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB1
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y} {L : Subgroup Y} {z : Y}

theorem nf5_B_inf_L (hc : NF5Cfg F Γ B R₀ x L z)
    (hcyc : Nat.card ((F ⊓ L : Subgroup Y)) = 25 ∧ IsCyclic ((F ⊓ L : Subgroup Y))) :
    ∀ b ∈ B, b ∈ L → b ∈ Subgroup.zpowers z := by
  intro b hb hbL
  obtain ⟨hbF, hb5⟩ := (hc.data.hB b).1 hb
  haveI : IsCyclic (F ⊓ L : Subgroup Y) := hcyc.2
  obtain ⟨z', hzz⟩ : ∃ z' : (F ⊓ L : Subgroup Y), (z' : Y) = z :=
    ⟨⟨z, Subgroup.mem_inf.2 ⟨hc.zgen.mem, hc.zL⟩⟩, rfl⟩
  obtain ⟨b', hbb⟩ : ∃ b' : (F ⊓ L : Subgroup Y), (b' : Y) = b :=
    ⟨⟨b, Subgroup.mem_inf.2 ⟨hbF, hbL⟩⟩, rfl⟩
  have hz' : orderOf z' = 5 := by
    rw [← Subgroup.orderOf_coe, hzz]
    exact hc.zgen.order
  have hb' : orderOf b' ∣ 5 := by
    rw [← Subgroup.orderOf_coe, hbb]
    exact orderOf_dvd_of_pow_eq_one hb5
  have hle : Subgroup.zpowers b' ≤ Subgroup.zpowers z' := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hz']
    exact hb'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hle (Subgroup.mem_zpowers b'))
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [← hzz, ← hbb, ← Subgroup.coe_zpow, hk]

theorem nf5_sylow_cyclic (hc : NF5Cfg F Γ B R₀ x L z) (hcyc : IsCyclic ((F ⊓ L : Subgroup Y))) :
    ∀ S : Sylow 5 ↥L, IsCyclic (S : Subgroup ↥L) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := hc.normal
  obtain ⟨hFp, hFidx⟩ : IsPGroup 5 F ∧ ¬ 5 ∣ F.index := by
    obtain ⟨_, hFp, hFdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hc.data.sylow
    exact ⟨hFp, by rwa [Subgroup.relIndex_top_right] at hFdvd⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 5 Y, (Q : Subgroup Y) = F := ⟨IsPGroup.toSylow hFp hFidx, rfl⟩
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q
    (Subgroup.Normal.isSubnormal (H := L) hc.normal)
  rw [hQ] at hP
  have e : (P : Subgroup ↥L) ≃* (F ⊓ L : Subgroup Y) :=
    (Subgroup.equivMapOfInjective (P : Subgroup ↥L) L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  have hPcyc : IsCyclic (P : Subgroup ↥L) :=
    isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  intro S
  exact isCyclic_of_surjective (Sylow.equiv P S).toMonoidHom (Sylow.equiv P S).surjective

theorem nf5_generation (h10 : KFactFieldGeneration5) (hc : NF5Cfg F Γ B R₀ x L z)
    (hI : (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ), ℓ ≠ 5 ∧
        CFSG.Blueprint.LieModel ↥L t n ℓ f) ∧
      (Nat.card ((F ⊓ L : Subgroup Y)) = 25 ∧ IsCyclic ((F ⊓ L : Subgroup Y))))
    (hnS : ¬ IsoLie ↥L (.suzuki 2)) :
    L ≤ ⨆ b ∈ {b : Y | b ∈ B ∧ b ∉ L}, Subgroup.centralizer ({b} : Set Y) := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc.cen).trans QuotientGroup.quotientBot
  have hsimp : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr e).1 hq.2
  have hnonab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hbot : commutator ↥L = ⊥ := (commutator_eq_bot_iff _).2 (isMulCommutative_iff.2 hcomm)
    have htop : (⊤ : Subgroup ↥L) = ⊥ := hq.1.symm.trans hbot
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥L
    have ha : a = 1 := by
      have h : a ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top a
      rw [htop, Subgroup.mem_bot] at h
      exact h
    have hb : b = 1 := by
      have h : b ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top b
      rw [htop, Subgroup.mem_bot] at h
      exact h
    exact hab (ha.trans hb.symm)
  have hnq : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h' := congrArg e h
    simpa using h'
  have hcat : IsCatalogGroup ↥L :=
    isCatalogGroup_isoInvariant e.symm
      (hc.data.catalog L (Subgroup.center ↥L) inferInstance hq.2 hnq)
  have hzB : z ∈ B := nf5_z_mem_B hc.data hc.zgen
  have hz1 : z ≠ 1 := by
    intro h
    have h5 := hc.zgen.order
    rw [h, orderOf_one] at h5
    norm_num at h5
  exact h10 Y L hc.normal hsimp hnonab hcat hc.cent hnS hI.1 (nf5_sylow_cyclic hc hI.2.2) B z
    hc.data.Belem hc.data.Bcard hzB hc.zL hz1 (nf5_B_inf_L hc hI.2)

theorem nf5_L_le_Γ (hc : NF5Cfg F Γ B R₀ x L z)
    (hgen : L ≤ ⨆ b ∈ {b : Y | b ∈ B ∧ b ∉ L}, Subgroup.centralizer ({b} : Set Y)) : L ≤ Γ := by
  refine hgen.trans (iSup₂_le fun b hb => ?_)
  obtain ⟨hbB, hbL⟩ := hb
  refine hc.data.hC b hbB fun hbx => hbL ?_
  have hbF : b ∈ F := ((hc.data.hB b).1 hbB).1
  exact Subgroup.zpowers_le.2 hc.zL (nf5_mem_zpowers_of_mem_x hc.data hc.zgen hbF hbx)

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
