module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4OuterBound
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Eta
public import CFSG.Milestones.ASVolI.F411.aG2Core

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Spin


theorem mem_of_odd_index_centralizer {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) (hirr : X1.IsIrrOn L) {e : MulAut V}
    (heN : e ∈ Subgroup.normalizer (L : Set (MulAut V))) (he2 : e * e = 1)
    (hodd : Odd ((Subgroup.centralizer {e}).subgroupOf L).index) : e ∈ L := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup L := (Subgroup.centralizer ({e} : Set (MulAut V))).subgroupOf L
  have hoddC : Odd C.index := hodd
  let P : Sylow 2 C := Classical.choice Sylow.nonempty
  let T : Subgroup L := (P : Subgroup C).map C.subtype
  have hTp : IsPGroup 2 T := P.isPGroup'.map C.subtype
  have hTindex : ¬ 2 ∣ T.index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two P.not_dvd_index hoddC.not_two_dvd_nat
  let S : Sylow 2 L := hTp.toSylow hTindex
  have hcomm : ∀ s ∈ (S : Subgroup L), ((s : L) : MulAut V) * e = e * ((s : L) : MulAut V) := by
    intro s hs
    have hsT : s ∈ T := by
      simpa only [S, IsPGroup.toSylow_coe] using hs
    rcases Subgroup.mem_map.mp hsT with ⟨c, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 c.2)
  have hfixS : ∀ s ∈ (S : Subgroup L), X1.conjAut L heN s = s := by
    intro s hs
    apply Subtype.ext
    rw [X1.coe_conjAut]
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    rw [hei, mul_assoc, hcomm s hs, ← mul_assoc, he2, one_mul]
  let χ : L ≃* CFSG.Blueprint.Chevalley.adjointGroup .D4 K := θ.trans (eta K).symm
  let α : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .D4 K) :=
    MulAut.congr χ (X1.conjAut L heN)
  let S' : Sylow 2 (CFSG.Blueprint.Chevalley.adjointGroup .D4 K) :=
    Sylow.mapSurjective (f := χ.toMonoidHom) χ.surjective S
  have hfix : ∀ s ∈ (S' : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .D4 K)), α s = s := by
    intro s hs
    have hcoe := Sylow.coe_mapSurjective (f := χ.toMonoidHom) χ.surjective S
    have hsm : s ∈ (S : Subgroup L).map χ.toMonoidHom := by
      rw [← hcoe]
      exact hs
    rcases Subgroup.mem_map.mp hsm with ⟨t, ht, rfl⟩
    change MulAut.congr χ (X1.conjAut L heN) (χ t) = χ t
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hfixS t ht]
  obtain ⟨g, hg⟩ :=
    CFSG.ASVolI.burnsideF411a_chev_inner_of_fix_sylow .D4 K 2 α S' hfix
  refine mem_of_conjAut_eq_conj hV hirr heN he2 (χ.symm g) ?_
  intro x
  apply χ.injective
  calc χ (X1.conjAut L heN x) = α (χ x) := by
        change χ (X1.conjAut L heN x) = MulAut.congr χ (X1.conjAut L heN) (χ x)
        conv_rhs => rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
    _ = g * χ x * g⁻¹ := by rw [hg, MulAut.conj_apply]
    _ = χ (χ.symm g * x * (χ.symm g)⁻¹) := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
