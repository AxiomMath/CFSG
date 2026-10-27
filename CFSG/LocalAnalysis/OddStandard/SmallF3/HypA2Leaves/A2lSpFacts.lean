module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FStarFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuotAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open CFSG.OddStandard.SmallF3.HypA2 (TypU isSLTwoOver_of_mulEquiv)
open CFSG.Open.StatedAPI (scalar_mem_statedSp_iff)
open scoped MatrixGroups

section Datum

theorem a2lDatum_of_subgroup_component_of_le {G : Type} [Group G] (H : Subgroup G) [Finite H]
    {z : G} (hzH : z ∈ H) (hz : z * z = 1) (hz1 : z ≠ 1) {Q N : Subgroup G} {q₀ : ℕ}
    (hodd : Odd q₀) (h5 : 5 ≤ q₀)
    (hQc : CFSG.Assembly.IsComponentOf Q (H ⊓ centralizer ({z} : Set G))) (hNQ : N ≤ Q)
    (hzN : z ∈ N) (hN : HarrisLit.IsSLTwoOver q₀ ↥N) (hTU : TypU ↥Q) : a2lDatum ↥H := by
  obtain ⟨hQle, hQs, hQq⟩ := hQc
  have hQH : Q ≤ H := hQle.trans inf_le_left
  have hNH : N ≤ H := hNQ.trans hQH
  let t : H := ⟨z, hzH⟩
  let eJ : ↥(Q.subgroupOf H) ≃* ↥Q := subgroupOfEquivOfLe hQH
  let eN : ↥(N.subgroupOf H) ≃* ↥N := subgroupOfEquivOfLe hNH
  have hcent : (H ⊓ centralizer ({z} : Set G)).subgroupOf H = centralizer ({t} : Set H) := by
    ext g
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨g.2, congrArg Subtype.val h⟩⟩
  have hsub : CFSG.Assembly.IsSubnormal (Q.subgroupOf H) (centralizer ({t} : Set H)) := by
    rw [← hcent]
    exact hQs.comap H.subtype
  refine a2lDatum_of_block (P := H) (MonoidHom.id H) Function.surjective_id ?_ hodd h5 (t := t)
    (J := Q.subgroupOf H) (N := N.subgroupOf H) (Subtype.ext hz) ?_
    (fun x hx => mem_subgroupOf.2 (hNQ (mem_subgroupOf.1 hx))) hzN ?_ hsub ?_
    (fun x _ hx => hx) (isSLTwoOver_of_mulEquiv eN.symm hN) (a2l_typU_of_mulEquiv eJ.symm hTU)
  · intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
    rw [hx]
    exact one_mem _
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · intro x hx
    have hxQ : (x : G) ∈ centralizer ({z} : Set G) := (hQle (mem_subgroupOf.1 hx)).2
    rw [mem_centralizer_singleton_iff] at hxQ ⊢
    exact Subtype.ext hxQ
  · exact (AssemblyBPredicates.isQuasisimple_iff_native _).1 hQq |> fun h =>
      CFSG.IsQuasisimple.of_mulEquiv eJ h

end Datum

section TypU

theorem a2l_typU_of_chev3 {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) (hS : HarrisLit.IsSimpleChevalleyOver 3 (K ⧸ center K))
    (hI : ¬ GH74.GLS.InChev2 (K ⧸ center K)) : TypU K := by
  have hO : pPrimeCore 2 K = ⊥ := HypA2.pPrimeCore_eq_bot_of_isQuasisimple hq hZ
  have hZs : Open.fusionZStar K = center K := HypA2.fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  let e : K ⧸ Open.fusionZStar K ≃* K ⧸ center K := QuotientGroup.quotientMulEquivOfEq hZs
  refine Or.inr (Or.inl ⟨3, Nat.prime_three, by norm_num, ?_, ?_⟩)
  · exact (HypA2.isSimpleChevalleyOver_congr 3 e).2 hS
  · rw [HypA2.inChev2_congr e]
    exact hI

theorem a2l_not_inChev2_of_card (hC : HypA2.ChevOddInChev2) {S : Type} [Group S] [Finite S]
    (hS : HarrisLit.IsSimpleChevalleyOver 3 S)
    (hne : Nat.card S ∉ ({60, 168, 6048, 360, 25920} : Finset ℕ)) : ¬ GH74.GLS.InChev2 S := by
  intro hI
  rcases hC S 3 Nat.prime_three (by norm_num) hS hI with h | h | h
  · exact hne (by simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; omega)
  · have h1 := GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 3) (f := 2) (by norm_num) h
    exact hne (by rw [h1]; decide)
  · have h1 := GH74.card_of_lieModel_PSp (G := S) (n := 2) (p := 3) (f := 1) (by norm_num)
      (by norm_num) h
    exact hne (by rw [h1]; decide)

theorem a2l_typU_of_psp_three (hC : HypA2.ChevOddInChev2) {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) (hZ : IsPGroup 2 ↥(center K))
    (hm : LieModel (K ⧸ center K) .PSp 3 3 1) : TypU K := by
  refine a2l_typU_of_chev3 hq hZ ⟨.PSp, 3, 1, hm⟩
    (a2l_not_inChev2_of_card hC ⟨.PSp, 3, 1, hm⟩ ?_)
  rw [GH74.card_of_lieModel_PSp (n := 3) (p := 3) (f := 1) (by norm_num) (by norm_num) hm]
  decide

end TypU

section Center

variable {n : ℕ} {F : Type} [Field F]

theorem a2l_center_statedSp_cases (hn : 1 ≤ n) {s : StatedSp n F}
    (hs : s ∈ center (StatedSp n F)) :
    (s : GL (Fin n ⊕ Fin n) F) = 1 ∨
      (s : GL (Fin n ⊕ Fin n) F) =
        Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Fˣ) := by
  rw [LieType.Universal.Symplectic.center_eq] at hs
  obtain ⟨c, hc⟩ := mem_subgroupOf.1 hs
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n F := by
    rw [hc]
    exact s.2
  have hc2 : ((c : F) * c) = 1 := by
    have := congrArg Units.val ((scalar_mem_statedSp_iff hn c).1 hmem)
    rwa [Units.val_pow_eq_pow_val, Units.val_one, sq] at this
  rcases mul_self_eq_one_iff.1 hc2 with h | h
  · left
    rw [← hc, show c = 1 from Units.ext h, map_one]
  · right
    rw [← hc, show c = -1 from Units.ext (by rw [h]; simp)]

theorem a2l_mul_self_eq_one_of_mem_center (hn : 1 ≤ n) {s : StatedSp n F}
    (hs : s ∈ center (StatedSp n F)) : s * s = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  rcases a2l_center_statedSp_cases hn hs with h | h
  · rw [h, mul_one]
  · rw [h, ← map_mul]
    simp

theorem a2l_map_neg_one_eq_of_central (hn : 1 ≤ n) {L : Type} [Group L]
    (hP : Group.IsPerfect (StatedSp n F)) (ψ : StatedSp n F →* L) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (StatedSp n F)) {z : L} (hz : z ∈ center L) (hz1 : z ≠ 1)
    {g : StatedSp n F}
    (hg : (g : GL (Fin n ⊕ Fin n) F) =
      Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Fˣ)) : ψ g = z := by
  obtain ⟨s, rfl⟩ := hψ z
  have hsc : s ∈ center (StatedSp n F) := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hP ψ hψ hker]
    exact hz
  rcases a2l_center_statedSp_cases hn hsc with h | h
  · exact absurd (by rw [show s = 1 from Subtype.ext h, map_one]) hz1
  · rw [show g = s from Subtype.ext (hg.trans h.symm)]

theorem a2l_injective_of_central_kernel (hn : 1 ≤ n) {L : Type} [Group L]
    (ψ : StatedSp n F →* L) (hker : ψ.ker ≤ center (StatedSp n F)) {g₀ : StatedSp n F}
    (hg₀ : (g₀ : GL (Fin n ⊕ Fin n) F) =
      Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Fˣ)) (h1 : ψ g₀ ≠ 1) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases a2l_center_statedSp_cases hn (hker (MonoidHom.mem_ker.2 hg)) with h | h
  · exact Subtype.ext h
  · rw [show g = g₀ from Subtype.ext (h.trans hg₀.symm)] at hg
    exact absurd hg h1

theorem a2l_isPGroup_two_center_of_cover (hn : 1 ≤ n) {L : Type} [Group L]
    (hP : Group.IsPerfect (StatedSp n F)) (ψ : StatedSp n F →* L) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (StatedSp n F)) : IsPGroup 2 ↥(center L) := by
  intro y
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨s, hs⟩ := hψ (y : L)
  have hsc : s ∈ center (StatedSp n F) := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hP ψ hψ hker, mem_comap, hs]
    exact y.2
  have h := a2l_mul_self_eq_one_of_mem_center hn hsc
  rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one, ← hs, ← map_mul, h, map_one]

end Center

end CFSG.OddStandard.SmallF3.HypA2Leaves
