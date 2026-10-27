module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamGen
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4M22
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4M23
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4J3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4McL
public import CFSG.RankThree.PartOne.SPOR.OuterLy

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45 CFSG.OddStandard CFSG.ClassicalInvolution CFSG.Sporadic.Ly
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

theorem lem711_m22 :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  refine lem711_empty_of_cent_card (P := fun X _ => NativeSporadic.IsSporadic X .M22) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M22 := e
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact IVK.GHInv.card_outer_le_of_card_mulAut_le (Sporadic.Schreier.m22_center_eq_bot')
      (by simpa using Sporadic.Schreier.m22_mulAut_card)
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M22 := e
    have hcent : ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
        Nat.card (centralizerIn NativeSporadic.M22 u) = 384 :=
      IVK.mathieu_inv_centralizer_card
        (OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial.2.2.1)
    have hord : orderOf (e' y) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    have hcardC : Nat.card ↥(centralizer ({y} : Set L)) = 384 := by
      have h1 := IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M22 e' y
      rw [h1]
      exact hcent _ (e' y).2 (by rw [Subgroup.orderOf_coe]; exact hord)
    rw [hcardC]
    norm_num

theorem lem711_m23 :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  refine lem711_empty_of_cent_card (P := fun X _ => NativeSporadic.IsSporadic X .M23) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M23 := e
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact Sporadic.Schreier.at_m23_schreier.1
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M23 := e
    have hord : orderOf ((e' y : NativeSporadic.M23) : Equiv.Perm (Fin 23)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    obtain ⟨-, hcard⟩ := IVK.m23_inv_centralizer_data _ (e' y).2 hord
    rw [IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M23 e' y, hcard]
    norm_num


theorem lem711_j3 :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  refine lem711_empty_of_cent_card (P := fun X _ => NativeSporadic.IsSporadic X .J3) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥j3P := e.trans j3PermEquiv
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact j3_outer_card_le
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥j3P := e.trans j3PermEquiv
    have hord : orderOf ((e' y : ↥j3P) : Equiv.Perm (Fin 6156)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    obtain ⟨-, hcard⟩ := IVK.j3_inner_centralizer_data _ (e' y).2 hord
    rw [IVK.GHInv.card_centralizer_eq_centralizerIn j3P e' y, hcard]
    norm_num


theorem lem711_mcl :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .McL) := by
  refine lem711_empty_of_comp_top (P := fun X _ => NativeSporadic.IsSporadic X .McL) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥mclP := e.trans mclPermEquiv
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact mcl_outer_card_le
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥mclP := e.trans mclPermEquiv
    have hord : orderOf ((e' y : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' y).2 hord
    exact ⟨↥mclCt, inferInstance, inferInstance, IVK.GHInv.centralizerEquivConj mclP e' y hg hgt,
      fun K hK => IVK.mclCt_isComponent_top hK⟩

theorem lem711_ly :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) := by
  obtain ⟨hkey, hq, -, -⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  have hperf : Group.IsPerfect ↥LyProof.KJ := Group.isPerfect_def.2 hq.1
  refine lem711_empty_of_comp_top (P := fun X _ => NativeSporadic.IsSporadic X .Ly) ?_ ?_
  · intro L _ _ hL
    exact Nat.le_of_dvd two_pos (RankThree.PartOne.SPOR.outer_order_divides_two' hL).1
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥J := e.trans lyEquivJ
    have hy2' : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    have hord : orderOf (e' y) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hy2'
    have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
      intro s hs hso
      have hss : s * s = 1 := by
        have := pow_orderOf_eq_one s
        rwa [hso, pow_two] at this
      have hs1 : s ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hso
        exact absurd hso (by norm_num)
      obtain ⟨C, hC⟩ := hcover s hs hss hs1
      exact ⟨C, Subgroup.mem_top C, hC⟩
    obtain ⟨c, -, hc⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' y)
      (Subgroup.mem_top _) hord
    refine ⟨↥LyProof.KJ, inferInstance, inferInstance, ?_, fun K hK => ?_⟩
    · exact (IVK.GHInv.centralizerEquivConj (J : Subgroup (GL (Fin 111) (ZMod 5))) e' y
        (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5))) (g := (c : GL (Fin 111) (ZMod 5))) c.2
        (by rw [hc]; simp)).trans
        ((IVK.GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans (MulEquiv.subgroupCongr hkey))
    · exact IVK.GHInv.isComponent_eq_top_of_perfect hperf (QuotientGroup.mk' (center ↥LyProof.KJ))
        (QuotientGroup.mk'_surjective _) hq.2 (by rw [QuotientGroup.ker_mk']) hK

theorem m12_inv_centralizer_card :
    ∀ u ∈ NativeSporadic.M12, orderOf u = 2 →
      Nat.card ↥(centralizerIn NativeSporadic.M12 u) = 192 ∨
        Nat.card ↥(centralizerIn NativeSporadic.M12 u) = 240 := by
  obtain ⟨hrecs, -, hcover⟩ := m12_innerRecordsValid
  intro u hu hu2
  obtain ⟨r, hr, hur⟩ := hcover u hu hu2
  rw [IVK.GHInv.card_centralizerIn_eq_of_mem_conjClass NativeSporadic.M12 hur,
    (hrecs r hr).2.2.2.1]
  simp only [m12Records, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left; rfl
  · right; rfl


theorem j2_inner_centralizer_card :
    ∀ t ∈ j2P, orderOf t = 2 →
      Nat.card ↥(centralizerIn j2P t) = 240 ∨ Nat.card ↥(centralizerIn j2P t) = 1920 := by
  obtain ⟨hSR, -, -, hrows, hcover, -, hshape, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  intro t htP ht2
  have htR : t ∈ j2R := Subgroup.mem_sup_left htP
  obtain ⟨r, hr, g, hg, htg⟩ := hcover t htR ht2
  obtain ⟨-, -, hrouter, hCr, hcard, -⟩ := hrows r hr
  have hrP : tp 315 r.rep ∈ j2P := by
    have : tp 315 r.rep = g⁻¹ * t * g := by rw [htg]; group
    rw [this]
    exact j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) htP) hg
  have hrout : r.outer = false := by
    by_contra hne
    exact (hrouter.1 (by simpa using hne)) hrP
  have hr0 : r.centOrder = 240 ∨ r.centOrder = 1920 := by
    have hm : (r.outer, r.classSize, r.centOrder) ∈
        j2Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) := List.mem_map_of_mem hr
    rw [hshape] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨h, -, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · rw [hrout] at h
      exact absurd h (by decide)
    · exact Or.inl h
    · exact Or.inr h
  have hcls : t ∈ CFSG.Sporadic.Schreier.conjClass j2P (tp 315 r.rep) := ⟨g, hg, htg⟩
  rw [IVK.GHInv.card_centralizerIn_eq_of_mem_conjClass j2P hcls]
  rcases hr0 with h0 | h0
  · exact Or.inl (hcard.trans h0)
  · exact Or.inr (hcard.trans h0)


theorem lem711_j2 :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .J2) := by
  refine lem711_empty_of_cent_card (P := fun X _ => NativeSporadic.IsSporadic X .J2) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥j2P := e.trans j2PermEquiv
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact j2_outer_card_le
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥j2P := e.trans j2PermEquiv
    have hord : orderOf ((e' y : ↥j2P) : Equiv.Perm (Fin 315)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    have hc := j2_inner_centralizer_card _ (e' y).2 hord
    rw [IVK.GHInv.card_centralizer_eq_centralizerIn j2P e' y]
    rcases hc with hc | hc <;> rw [hc] <;> norm_num

theorem lem711_m12 :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  refine lem711_empty_of_cent_card_comm (P := fun X _ => NativeSporadic.IsSporadic X .M12) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M12 := e
    exact isMulCommutative_of_mulEquiv'
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e') Sporadic.Schreier.at_m12_schreier.2.1
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M12 := e
    have hord : orderOf ((e' y : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    have hc := m12_inv_centralizer_card _ (e' y).2 hord
    rw [IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M12 e' y]
    rcases hc with hc | hc <;> rw [hc] <;> norm_num

end CFSG.GH74.GLS
