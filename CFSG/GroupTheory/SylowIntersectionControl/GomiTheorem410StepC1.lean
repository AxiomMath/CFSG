module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Lift
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SylowIntersectionControl.Regular
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import TauCeti.GroupTheory.Elementary
import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.GroupTheory.SylowIntersectionControl.CharPair
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open scoped Pointwise commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω} {hyp : Subgroup Ω → Prop}
  {G : Subgroup Ω}

omit [Finite Ω] in
private theorem le_of_normal_isSylowTwoOf_s4c1 {H P Q : Subgroup Ω} (hQ : IsSylowTwoOf Q H)
    (hQn : (Q.subgroupOf H).Normal) (hP : IsPGroup 2 P) (hPH : P ≤ H) : P ≤ Q := by
  have hQ'2 : IsPGroup 2 (Q.subgroupOf H) := hQ.2.1.comap_subtype (K := H)
  have hQ'idx : ¬ 2 ∣ (Q.subgroupOf H).index := hQ.2.2
  let Qs : Sylow 2 ↥H := hQ'2.toSylow hQ'idx
  have hQse : (Qs : Subgroup ↥H) = Q.subgroupOf H := rfl
  have hQsn : (Qs : Subgroup ↥H).Normal := by rw [hQse]; exact hQn
  have := hQsn
  have hP'2 : IsPGroup 2 (P.subgroupOf H) := hP.comap_subtype (K := H)
  have hkey : P.subgroupOf H ≤ (Qs : Subgroup ↥H) := by
    have h := IsPGroup.inf_normalizer_sylow hP'2 Qs
    change P.subgroupOf H ⊓ Subgroup.normalizer ((Qs : Subgroup ↥H) : Set ↥H) =
      P.subgroupOf H ⊓ (Qs : Subgroup ↥H) at h
    rw [Subgroup.normalizer_eq_top_iff.mpr hQsn, inf_top_eq] at h
    exact inf_eq_left.mp h.symm
  intro x hx
  have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  have hx'' : (⟨x, hPH hx⟩ : ↥H) ∈ (Qs : Subgroup ↥H) := hkey hx'
  rw [hQse] at hx''
  exact Subgroup.mem_subgroupOf.mp hx''

omit [Finite Ω] in
private theorem gomi410c1_block_le_normal_s4c1 {N S : Subgroup Ω} (hNG : N ≤ G)
    (hN : G ≤ normalizer (N : Set Ω)) (hS : IsSylowTwoOf S G) {B₀ : Subgroup ↥(N ⊔ S)}
    (hres : oResidualTwo ↥B₀ = ⊤) : B₀.map (N ⊔ S).subtype ≤ N := by
  have hNH : N ≤ N ⊔ S := le_sup_left
  have hSH : S ≤ N ⊔ S := le_sup_right
  have hHG : N ⊔ S ≤ G := sup_le hNG hS.1
  have hN'norm : (N.subgroupOf (N ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr (hHG.trans hN)
  have := hN'norm
  have hS'H : IsPGroup 2 (S.subgroupOf (N ⊔ S)) := hS.2.1.comap_subtype (K := N ⊔ S)
  have hsup : (N.subgroupOf (N ⊔ S)) ⊔ (S.subgroupOf (N ⊔ S)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hSH, Subgroup.subgroupOf_self]
  have hker : (N.subgroupOf (N ⊔ S)).map (QuotientGroup.mk' (N.subgroupOf (N ⊔ S))) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' (N := N.subgroupOf (N ⊔ S))).symm
  have hmap : (S.subgroupOf (N ⊔ S)).map (QuotientGroup.mk' (N.subgroupOf (N ⊔ S))) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' (N.subgroupOf (N ⊔ S)))) hsup
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      hker, bot_sup_eq] at h
    exact h
  have hquotH : IsPGroup 2 (↥(N ⊔ S) ⧸ N.subgroupOf (N ⊔ S)) := by
    have h2 := hS'H.map (QuotientGroup.mk' (N.subgroupOf (N ⊔ S)))
    rw [hmap] at h2
    exact h2.of_equiv Subgroup.topEquiv
  have hquotB : IsPGroup 2 (↥B₀ ⧸ (N.subgroupOf (N ⊔ S)).subgroupOf B₀) := by
    refine TauCeti.isPGroup_quotient_of_forall_exists_pow_mem fun x => ?_
    obtain ⟨k, hk⟩ := (CFSG.CGT.PushingUpLit.isPGroup_two_quotient_iff _).mp hquotH x
    exact ⟨k, by rw [Subgroup.mem_subgroupOf]; simpa using hk⟩
  have htop : oResidualTwo ↥B₀ ≤ (N.subgroupOf (N ⊔ S)).subgroupOf B₀ :=
    sInf_le ⟨inferInstance, hquotB⟩
  rw [hres] at htop
  have hBleN' : B₀ ≤ N.subgroupOf (N ⊔ S) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mp (htop (Subgroup.mem_top (⟨x, hx⟩ : ↥B₀)))
  calc B₀.map (N ⊔ S).subtype ≤ (N.subgroupOf (N ⊔ S)).map (N ⊔ S).subtype :=
        Subgroup.map_mono hBleN'
    _ = N := Subgroup.map_subgroupOf_eq_of_le hNH

omit [Finite Ω] in
private theorem gomi410c1_block_subnormal_s4c1 {N S : Subgroup Ω} (hNG : N ≤ G)
    (hN : G ≤ normalizer (N : Set Ω)) (hS : IsSylowTwoOf S G)
    {B₀ : Subgroup ↥(N ⊔ S)} (hsub : B₀.IsSubnormal)
    (hBN : B₀.map (N ⊔ S).subtype ≤ N) :
    ((B₀.map (N ⊔ S).subtype).subgroupOf G).IsSubnormal := by
  have hNH : N ≤ N ⊔ S := le_sup_left
  have hHG : N ⊔ S ≤ G := sup_le hNG hS.1
  have hNnormalG : (N.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).mpr hN
  have hBsubH : ((B₀.map (N ⊔ S).subtype).subgroupOf (N ⊔ S)).IsSubnormal := by
    rw [show (B₀.map (N ⊔ S).subtype).subgroupOf (N ⊔ S) = B₀ from
      Subgroup.comap_map_eq_self_of_injective (f := (N ⊔ S).subtype)
        (N ⊔ S).subtype_injective B₀]
    exact hsub
  have hBsubN : ((B₀.map (N ⊔ S).subtype).subgroupOf N).IsSubnormal :=
    isSubnormal_subgroupOf_of_le hNH hBsubH
  exact isSubnormal_subgroupOf_trans hBN hNG hBsubN hNnormalG.isSubnormal

theorem isSylowTwoOf_inf_sup_pCoreOf {N S : Subgroup Ω} (hNG : N ≤ G)
    (hN : G ≤ normalizer (N : Set Ω)) (hS : IsSylowTwoOf S G) :
    IsSylowTwoOf (S ⊓ (N ⊔ pCoreOf 2 G)) (N ⊔ pCoreOf 2 G) := by
  have hQleG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hHleG : N ⊔ pCoreOf 2 G ≤ G := sup_le hNG hQleG
  have hHnorm : G ≤ normalizer ((N ⊔ pCoreOf 2 G : Subgroup Ω) : Set Ω) :=
    (le_inf hN (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup N (pCoreOf 2 G))
  have hinf :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp hS).inf_of_le_normalizer
      hHleG hHnorm
  exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hinf

theorem Gomi410Cex.isRegular_sup_of_normal (h : Gomi410Cex f hyp G) (hchar : CharTwo G)
    (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {N S : Subgroup Ω} (hNG : N ≤ G) (hN : G ≤ normalizer (N : Set Ω))
    (hS : IsSylowTwoOf S G) (hne : N ⊔ S ≠ G) : f.IsRegular (N ⊔ S) := by
  by_contra hnotreg
  have hHG : N ⊔ S ≤ G := sup_le hNG hS.1
  have hHltG : N ⊔ S < G := lt_of_le_of_ne hHG hne
  have hQH : pCoreOf 2 G ≤ N ⊔ S :=
    (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hS).trans le_sup_right
  obtain ⟨B₀, hB₀⟩ := h.minimal (N ⊔ S) hHltG hQH (hmono (N ⊔ S) hHG hQH) hnotreg
  have hBN : B₀.map (N ⊔ S).subtype ≤ N :=
    gomi410c1_block_le_normal_s4c1 hNG hN hS hB₀.residual
  have hBsub : ((B₀.map (N ⊔ S).subtype).subgroupOf G).IsSubnormal :=
    gomi410c1_block_subnormal_s4c1 hNG hN hS hB₀.subnormal hBN
  have hQBV : ⁅pCoreOf 2 G, B₀.map (N ⊔ S).subtype⁆ ≤ gomiV G := by
    have hQn : ((pCoreOf 2 G).subgroupOf (N ⊔ S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr
        (hHG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
    have hQlePCH : pCoreOf 2 G ≤ pCoreOf 2 (N ⊔ S) :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 hQH hQn
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G)
    calc ⁅pCoreOf 2 G, B₀.map (N ⊔ S).subtype⁆
        ≤ ⁅pCoreOf 2 (N ⊔ S), B₀.map (N ⊔ S).subtype⁆ :=
          Subgroup.commutator_mono hQlePCH le_rfl
      _ ≤ gomiV (N ⊔ S) := IsAschbacherBlockGomi.commutator_map_le_gomiV hB₀
      _ ≤ gomiV G := gomiV_le_gomiV_of_pCoreOf_le hchar hHG hQH
  exact h.not_block (hasGomiBlock_of_isSubnormal hHG hB₀ hBsub hQBV)

theorem Gomi410Cex.not_isRegular_inf_normalizer (h : Gomi410Cex f hyp G)
    {N S : Subgroup Ω} (hNG : N ≤ G) (hN : G ≤ normalizer (N : Set Ω))
    (hS : IsSylowTwoOf S G) (hreg : f.IsRegular (N ⊔ S)) :
    ¬ f.IsRegular (G ⊓ normalizer ((S ⊓ (N ⊔ pCoreOf 2 G) : Subgroup Ω) : Set Ω)) := by
  intro hregH
  set T : Subgroup Ω := S ⊓ (N ⊔ pCoreOf 2 G) with hT
  set H : Subgroup Ω := G ⊓ normalizer (T : Set Ω) with hH
  have hQleG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hNQleG : N ⊔ pCoreOf 2 G ≤ G := sup_le hNG hQleG
  have hNQnorm : G ≤ normalizer ((N ⊔ pCoreOf 2 G : Subgroup Ω) : Set Ω) :=
    (le_inf hN (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup N (pCoreOf 2 G))
  have hTsyl : IsSylowTwoOf T (N ⊔ pCoreOf 2 G) := by
    rw [hT]; exact isSylowTwoOf_inf_sup_pCoreOf hNG hN hS
  have hfrattini : G = (N ⊔ pCoreOf 2 G) ⊔ H := by
    rw [hH]
    exact le_antisymm
      (CFSG.Quasithin.B6.frattini_two hNQleG hNQnorm hTsyl)
      (sup_le (sup_le hNG (CFSG.LieType.BorelTits.pCoreOf_le 2 G)) inf_le_left)
  have hQT : pCoreOf 2 G ≤ T := by
    rw [hT]; exact le_inf (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hS) le_sup_right
  have hTH : T ≤ H := by
    rw [hH]; exact le_inf (hTsyl.1.trans hNQleG) Subgroup.le_normalizer
  have hQH : pCoreOf 2 G ≤ H := hQT.trans hTH
  have hGNH : G = N ⊔ H := by
    rw [hfrattini, sup_assoc, sup_eq_right.mpr hQH]
  have hSH : S ≤ H := by
    rw [hH]
    refine le_inf hS.1 ?_
    calc S ≤ Subgroup.normalizer (S : Set Ω) ⊓
          Subgroup.normalizer ((N ⊔ pCoreOf 2 G : Subgroup Ω) : Set Ω) :=
          le_inf Subgroup.le_normalizer (hS.1.trans hNQnorm)
      _ ≤ Subgroup.normalizer (S ⊓ (N ⊔ pCoreOf 2 G) : Subgroup Ω) :=
          Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := N ⊔ pCoreOf 2 G)
      _ = Subgroup.normalizer (T : Set Ω) := by rw [hT]
  have hHN : H ≤ normalizer (N : Set Ω) := (hH.le.trans inf_le_left).trans hN
  have hmul : (H : Set Ω) * ((N ⊔ S : Subgroup Ω) : Set Ω) = (G : Set Ω) :=
    mul_eq_of_eq_sup hGNH hHN le_sup_left (sup_le hNG hS.1)
  exact h.singular (PSubgroupSelection.IsRegular.of_mul_eq
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp hS) hSH le_sup_right hmul
    hregH hreg)

theorem inf_sup_pCoreOf_not_le {N S B : Subgroup Ω} (hNG : N ≤ G)
    (hN : G ≤ normalizer (N : Set Ω)) (hS : IsSylowTwoOf S G) (hBN : B ≤ N)
    (heven : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B))) :
    ¬ S ⊓ (N ⊔ pCoreOf 2 G) ≤ pCoreOf 2 G := by
  intro hle
  have hQleG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hNQleG : N ⊔ pCoreOf 2 G ≤ G := sup_le hNG hQleG
  have hTsyl : IsSylowTwoOf (S ⊓ (N ⊔ pCoreOf 2 G)) (N ⊔ pCoreOf 2 G) :=
    isSylowTwoOf_inf_sup_pCoreOf hNG hN hS
  have hQT : pCoreOf 2 G ≤ S ⊓ (N ⊔ pCoreOf 2 G) :=
    le_inf (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hS) le_sup_right
  have hTQ : S ⊓ (N ⊔ pCoreOf 2 G) = pCoreOf 2 G := le_antisymm hle hQT
  have hQsyl : IsSylowTwoOf (pCoreOf 2 G) (N ⊔ pCoreOf 2 G) := by
    have := hTsyl
    rw [hTQ] at this
    exact this
  have hQn : ((pCoreOf 2 G).subgroupOf (N ⊔ pCoreOf 2 G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (hNQleG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf B
  have hPH0 : P ≤ N ⊔ pCoreOf 2 G := hP.1.trans (hBN.trans le_sup_left)
  have hPQ : P ≤ pCoreOf 2 G := le_of_normal_isSylowTwoOf_s4c1 hQsyl hQn hP.2.1 hPH0
  have hPK : P.subgroupOf B ≤ (B ⊓ pCoreOf 2 G).subgroupOf B := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hPQ (Subgroup.mem_subgroupOf.mp hx)⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hBQn : ((B ⊓ pCoreOf 2 G).subgroupOf B).Normal := by
    have hBnormQ : B ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
      (hBN.trans le_sup_left).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp hQn)
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    exact (le_inf Subgroup.le_normalizer hBnormQ).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := pCoreOf 2 G))
  have hQ2' : IsPGroup 2 ((B ⊓ pCoreOf 2 G).subgroupOf B) :=
    (hQ2.to_le inf_le_right).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hKleC : (B ⊓ pCoreOf 2 G).subgroupOf B ≤ CFSG.pCore 2 ↥B :=
    CFSG.LieType.BorelTits.le_pCore 2 hBQn hQ2'
  have hoddP : Odd ((P.subgroupOf B).index) :=
    Nat.not_even_iff_odd.mp fun h => hP.2.2 (even_iff_two_dvd.mp h)
  have hoddK : Odd ((B ⊓ pCoreOf 2 G).subgroupOf B).index :=
    Odd.of_dvd_nat hoddP (Subgroup.index_dvd_of_le hPK)
  have hoddC : Odd (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)) := by
    rw [← Subgroup.index_eq_card]
    exact Odd.of_dvd_nat hoddK (Subgroup.index_dvd_of_le hKleC)
  exact (Nat.not_even_iff_odd.mpr hoddC) heven

end CFSG.GroupTheory
