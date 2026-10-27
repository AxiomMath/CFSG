module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3312A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312B

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped Pointwise

namespace L3312

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Hyp3312

variable {T M L D Y : Subgroup G} (H : Hyp3312 G T M L D Y)

include H

theorem mem_normalizer_of_mk_F4 (h14 : Stmt3_3_14_F4) (h37 : A37ForSQTK) (h128 : Lemma128One)
    {h : G} (hh : h ∈ Y ⊔ T ⊔ D)
    (hN : (QuotientGroup.mk ⟨h, hh⟩ : ↥(Y ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(Y ⊔ T ⊔ D)) ∈
      Subgroup.normalizer (modO2Image (Y ⊔ T ⊔ D) Y : Set (↥(Y ⊔ T ⊔ D) ⧸
        CFSG.pCore 2 ↥(Y ⊔ T ⊔ D)))) :
    h ∈ Subgroup.normalizer (Y : Set G) := by
  set X := Y ⊔ T ⊔ D with hX
  have hYX : Y ≤ X := le_sup_left.trans le_sup_left
  have h1 : (⟨h, hh⟩ : ↥X) ∈ Subgroup.normalizer
      ((Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X : Subgroup ↥X) : Set ↥X) := by
    have hc : (modO2Image X Y).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) =
        Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X := by
      unfold modO2Image
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    have hmem : (⟨h, hh⟩ : ↥X) ∈ (Subgroup.normalizer (modO2Image X Y : Set _)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := hN
    rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _), hc] at hmem
    exact hmem
  have h2 : h ∈ Subgroup.normalizer
      (((Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X).map X.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map X.subtype ⟨_, h1, rfl⟩
  have h3 : (Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X).map X.subtype = Y ⊔ pCoreOf 2 X := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYX, pCoreOf]
  rw [h3] at h2
  exact normalizer_sup_le H.perfect_Y (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf H.isSylowTwoOf_H).trans
      (H.le_normalizer_Y_F4 h14 h37 h128)) h2

theorem le_normalizer_D_of_oddNorm_F4 (h14 : Stmt3_3_14_F4) (h37 : A37ForSQTK) (h128 : Lemma128One)
    {K : Subgroup G} (hKH : K ≤ Y ⊔ T ⊔ D) (hYK : Y ≤ K)
    (hHK : Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G))
    (hON : OddNorm ↥(modO2Image (Y ⊔ T ⊔ D) K)
      ((modO2Image (Y ⊔ T ⊔ D) Y).subgroupOf (modO2Image (Y ⊔ T ⊔ D) K))) :
    D ≤ Subgroup.normalizer (Y : Set G) := by
  set X := Y ⊔ T ⊔ D with hX
  have : (modO2Image X K).Normal := modO2Image_normal hKH hHK
  let ψ : (↥X ⧸ CFSG.pCore 2 ↥X) →* MulAut ↥(modO2Image X K) := MulAut.conjNormal
  have hInn : (MulAut.conj : ↥(modO2Image X K) →* MulAut ↥(modO2Image X K)).range ≤ ψ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, MulAut.conjNormal_val⟩
  have hS := isSylowTwoOf_map_range ψ H.isSylowTwoOf_modO2Image_T
  have hYK' : modO2Image X Y ≤ modO2Image X K :=
    Subgroup.map_mono fun y hy => hYK hy
  have hSB : (modO2Image X T).map ψ ≤ MulAction.stabilizer (MulAut ↥(modO2Image X K))
      ((modO2Image X Y).subgroupOf (modO2Image X K)) := by
    rintro _ ⟨tb, htb, rfl⟩
    obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb
    refine (conjNormal_mem_stabilizer_iff hYK' _).mpr ?_
    exact mk_mem_normalizer_modO2Image htX (H.le_normalizer_Y_F4 h14 h37 h128 ht)
  intro d hd
  have hdX : d ∈ X := Subgroup.mem_sup_right hd
  apply H.mem_normalizer_of_mk_F4 h14 h37 h128 hdX
  refine (conjNormal_mem_stabilizer_iff hYK' _).mp ?_
  refine hON ψ.range _ hInn hS hSB _ ⟨?_, ⟨_, rfl⟩⟩ ?_
  · exact Subgroup.le_normalizer_map ψ ⟨_, mk_mem_normalizer_modO2Image hdX (H.DN hd), rfl⟩
  · refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ψ _)
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) _)
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat H.Dodd h1

end Hyp3312

end L3312

end CFSG.Quasithin.H13
