module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialSlice
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialSwap
import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisNormalizer
import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGW
import CFSG.CharacterTheory.Blocks.BrauerInduction
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialField

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)
open scoped MatrixGroups

section Outer

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem mem_of_conjNormal_mem_inner {N O W V : Subgroup M} [N.Normal] (hNO : N ⊓ O = ⊥)
    (hC : centralizer (N : Set M) = O) (hO : Odd (Nat.card O)) (hW : IsPGroup 2 W)
    (hWN : W ⊓ N = V) {w : M} (hw : w ∈ W)
    (hinn : (MulAut.conjNormal w : MulAut N) ∈ inner N) : w ∈ V := by
  obtain ⟨m, hm⟩ := hinn
  have hcC : (m : M)⁻¹ * w ∈ centralizer (N : Set M) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun f : MulAut N => ((f ⟨x, hx⟩ : N) : M)) hm
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc x * ((m : M)⁻¹ * w) = (m : M)⁻¹ * ((m : M) * x * (m : M)⁻¹) * w := by group
      _ = (m : M)⁻¹ * (w * x * w⁻¹) * w := by rw [h1]
      _ = (m : M)⁻¹ * w * x := by group
  set c := (m : M)⁻¹ * w with hcdef
  have hcO : c ∈ O := hC ▸ hcC
  have hcomm : Commute (m : M) c := mem_centralizer_iff.mp hcC (m : M) m.2
  have hwmc : w = m * c := by rw [hcdef]; group
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hck : c ^ 2 ^ k = 1 := by
    have h1 : (m : M) ^ 2 ^ k * c ^ 2 ^ k = 1 := by rw [← hcomm.mul_pow, ← hwmc, hwk]
    have h2 : c ^ 2 ^ k ∈ N ⊓ O := by
      refine mem_inf.mpr ⟨?_, pow_mem hcO _⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (pow_mem m.2 _)
    rw [hNO] at h2
    exact mem_bot.mp h2
  have hc1 : c = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hck)
    have hodd : Odd (orderOf c) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hcO)
    rw [hj] at hodd
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hj0⟩)
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  rw [← hWN]
  exact ⟨hw, by rw [hwmc, hc1, mul_one]; exact m.2⟩

theorem mem_or_mul_mem_of_isCyclic_outer {N O W V : Subgroup M} [N.Normal] (hNO : N ⊓ O = ⊥)
    (hC : centralizer (N : Set M) = O) (hO : Odd (Nat.card O)) (hcyc : IsCyclic (Outer N))
    (hW : IsPGroup 2 W) (hWN : W ⊓ N = V) {τ y : M} (hτW : τ ∈ W) (hτ : τ * τ = 1)
    (hτV : τ ∉ V) (hyW : y ∈ W) (hy : y * y = 1) : y ∈ V ∨ y * τ ∈ V := by
  let ψ : M →* Outer N := (QuotientGroup.mk' (inner N)).comp MulAut.conjNormal
  have hker : ∀ w ∈ W, ψ w = 1 → w ∈ V := fun w hw h1 =>
    mem_of_conjNormal_mem_inner hNO hC hO hW hWN hw ((QuotientGroup.eq_one_iff _).mp h1)
  have hτ1 : ψ τ ≠ 1 := fun h1 => hτV (hker τ hτW h1)
  have hτ2 : orderOf (ψ τ) = 2 := orderOf_eq_prime (by rw [sq, ← map_mul, hτ, map_one]) hτ1
  by_cases hy1 : ψ y = 1
  · exact Or.inl (hker y hyW hy1)
  · have hy2 : orderOf (ψ y) = 2 := orderOf_eq_prime (by rw [sq, ← map_mul, hy, map_one]) hy1
    have e := CFSG.ABGLocalTools.eq_of_orderOf_eq_two_of_isCyclic hy2 hτ2
    refine Or.inr (hker _ (mul_mem hyW hτW) ?_)
    rw [map_mul, e, ← map_mul, hτ, map_one]

theorem isCyclic_outer_of_mulEquiv_sl2 {N : Type*} [Group N] {k₂ : Type} [Field k₂]
    [Fintype k₂] {n : ℕ} (hn : 1 ≤ n) (hk₂ : Fintype.card k₂ = (2 ^ n) ^ 2)
    (ψ : N ≃* SL(2, k₂)) : IsCyclic (Outer N) := by
  have hk : Nat.card k₂ = 2 ^ (2 * n) := by
    rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
  have := (even_SL2_full_automorphism_semilinear_model (by omega) hk).2.2.1
  exact isCyclic_of_surjective (equivalence ψ).symm (equivalence ψ).symm.surjective

end Outer

section Bar

variable {G' : Type*} [Group G'] [Finite G']

theorem mem_or_mul_mem_of_isCyclic_outer_bar {X S T : Subgroup G'} {t y : G'} (hXS : X ≤ S)
    (hST : S ≤ T) (hT : IsPGroup 2 T) (htT : t ∈ T) (htS : t ∉ S) (ht2 : t * t = 1)
    (hTX : T ≤ normalizer (X : Set G')) (hyX : y ∈ normalizer (X : Set G'))
    (hyT : y ∈ normalizer (T : Set G')) (hy2 : y * y = 1) {N : Subgroup (BarM X)} [N.Normal]
    (hNO : N ⊓ CFSG.Open.standardComponentOddCore (BarM X) = ⊥)
    (hC : centralizer (N : Set (BarM X)) = CFSG.Open.standardComponentOddCore (BarM X))
    (hcyc : IsCyclic (Outer N)) (hSN : barSub X S ≤ N)
    (hSyl : ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = barSub X S) :
    y ∈ S ∨ y * t ∈ S := by
  have hyp : IsPGroup 2 (zpowers y) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hy2) : orderOf y ∣ 2 ^ 1)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hW : IsPGroup 2 (T ⊔ zpowers y : Subgroup G') :=
    hT.to_sup_of_normal_left' hyp (zpowers_le.mpr hyT)
  have hW' : IsPGroup 2 (barSub X (T ⊔ zpowers y)) :=
    (hW.comap_subtype : IsPGroup 2 ((T ⊔ zpowers y).subgroupOf (normalizer (X : Set G')))).map _
  have hVW : barSub X S ≤ barSub X (T ⊔ zpowers y) :=
    map_mono fun z hz => mem_subgroupOf.mpr (mem_sup_left (hST (mem_subgroupOf.mp hz)))
  have hWN : barSub X (T ⊔ zpowers y) ⊓ N = barSub X S :=
    eq_of_le_of_sylow_map hSyl (hW'.to_le inf_le_left) (le_inf hVW hSN) inf_le_right
  have htX : t ∈ normalizer (X : Set G') := hTX htT
  have hτW : barMap X ⟨t, htX⟩ ∈ barSub X (T ⊔ zpowers y) :=
    ⟨⟨t, htX⟩, mem_subgroupOf.mpr (mem_sup_left htT), rfl⟩
  have hyW : barMap X ⟨y, hyX⟩ ∈ barSub X (T ⊔ zpowers y) :=
    ⟨⟨y, hyX⟩, mem_subgroupOf.mpr (mem_sup_right (mem_zpowers y)), rfl⟩
  have hτ : barMap X ⟨t, htX⟩ * barMap X ⟨t, htX⟩ = 1 := by
    rw [← map_mul, barMap_eq_one_iff]
    change t * t ∈ X
    rw [ht2]
    exact one_mem _
  have hy : barMap X ⟨y, hyX⟩ * barMap X ⟨y, hyX⟩ = 1 := by
    rw [← map_mul, barMap_eq_one_iff]
    change y * y ∈ X
    rw [hy2]
    exact one_mem _
  have hτV : barMap X ⟨t, htX⟩ ∉ barSub X S := fun h => htS ((mem_barSub_iff hXS _).mp h)
  rcases mem_or_mul_mem_of_isCyclic_outer hNO hC
      (GMSK.odd_card_standardComponentOddCore (BarM X)) hcyc hW' hWN hτW hτ hτV hyW hy with
    h1 | h1
  · exact Or.inl ((mem_barSub_iff hXS _).mp h1)
  · rw [← map_mul] at h1
    exact Or.inr ((mem_barSub_iff hXS _).mp h1)

end Bar

section Quot

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

theorem mem_Q_of_inner (hS : Setup L K n φ (zpowers t) t) {W : Subgroup G} (hW : IsPGroup 2 W)
    (hQW : pull φ (antiUnipotent K) ⊔ zpowers t ≤ W) {x : G} (hxW : x ∈ W)
    (hxC : x ∈ centralizer ({t} : Set G))
    (hinn : normAct φ ⟨x, hS.cent_le hxC⟩ ∈ inner (antiSp K)) :
    x ∈ pull φ (antiUnipotent K) ⊔ zpowers t := by
  obtain ⟨a, ha⟩ := hinn
  set l : G := ((φ.symm a : L) : G)
  have hlL : l ∈ L := (φ.symm a).2
  have h0 : l⁻¹ * x ∈ centralizer (L : Set G) :=
    inv_mul_mem_centralizer φ _ (φ.symm a) (by rw [MulEquiv.apply_symm_apply]; exact ha.symm)
  have hc : l⁻¹ * x ∈ zpowers t := hS.mem_T h0 (mul_mem (inv_mem (hS.L_le hlL)) hxC)
  have hcW : l⁻¹ * x ∈ W := hQW (mem_sup_right hc)
  have hlW : l ∈ W := by simpa using mul_mem hxW (inv_mem hcW)
  obtain ⟨R, hR⟩ := exists_sylow_pull (G := G) φ
  have hWL : W ⊓ L = pull φ (antiUnipotent K) := eq_of_le_of_sylow_map ⟨R, hR⟩
    hW.to_inf_left (le_inf (le_sup_left.trans hQW) (pull_le φ _)) inf_le_right
  have hlP : l ∈ pull φ (antiUnipotent K) := hWL ▸ mem_inf.mpr ⟨hlW, hlL⟩
  simpa using mul_mem (mem_sup_left hlP : l ∈ pull φ (antiUnipotent K) ⊔ zpowers t)
    (mem_sup_right hc)

theorem comm_mem_P (hS : Setup L K n φ (zpowers t) t) {W : Subgroup G} (hW : IsPGroup 2 W)
    (hQW : pull φ (antiUnipotent K) ⊔ zpowers t ≤ W) {x y : G}
    (hx : x ∈ W ⊓ centralizer ({t} : Set G)) (hy : y ∈ W ⊓ centralizer ({t} : Set G)) :
    (x * y)⁻¹ * (y * x) ∈ pull φ (antiUnipotent K) := by
  set H : Subgroup G := W ⊓ centralizer ({t} : Set G) with hH
  set P : Subgroup G := pull φ (antiUnipotent K) with hP
  have hHN : H ≤ normalizer (L : Set G) := inf_le_right.trans hS.cent_le
  obtain ⟨R, hR⟩ := exists_sylow_pull (G := G) φ
  have hWL : W ⊓ L = P := eq_of_le_of_sylow_map ⟨R, hR⟩ hW.to_inf_left
    (le_inf (le_sup_left.trans hQW) (pull_le φ _)) inf_le_right
  have hnorm : (P.subgroupOf H).Normal := by
    refine ⟨fun p hp g => ?_⟩
    rw [mem_subgroupOf] at hp ⊢
    rw [← hWL] at hp ⊢
    obtain ⟨hpW, hpL⟩ := mem_inf.mp hp
    obtain ⟨hgW, hgC⟩ := mem_inf.mp g.2
    exact mem_inf.mpr ⟨mul_mem (mul_mem hgW hpW) (inv_mem hgW),
      (mem_normalizer_iff.mp (hS.cent_le hgC) _).mp hpL⟩
  have := isCyclic_outer_antiSp (K := K) (by have := hS.two_le; omega) hS.card_K
  let ψ : H →* Outer (antiSp K) := (QuotientGroup.mk' (inner (antiSp K))).comp (subAct φ hHN)
  have hker : P.subgroupOf H ≤ ψ.ker := by
    intro p hp
    rw [mem_subgroupOf] at hp
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, subAct_of_eq φ hHN (l := ⟨p, pull_le φ _ hp⟩) rfl]
    exact ⟨_, rfl⟩
  let f := QuotientGroup.lift (P.subgroupOf H) ψ hker
  have hf : f.ker ≤ center (H ⧸ P.subgroupOf H) := by
    intro q hq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hq
    obtain ⟨hzW, hzC⟩ := mem_inf.mp z.2
    have hzQ := mem_Q_of_inner hS hW hQW hzW hzC hq
    obtain ⟨p, hp, c, hc, hpc⟩ := hS.mem_Q.mp hzQ
    have hcH : c ∈ H := mem_inf.mpr ⟨hQW (mem_sup_right hc), hS.T_le_C hc⟩
    have hzc : (QuotientGroup.mk z : H ⧸ P.subgroupOf H) = QuotientGroup.mk ⟨c, hcH⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      have hpc' : p * c = c * p := hS.comm_L_T (pull_le φ _ hp) hc
      have e : ((z⁻¹ * ⟨c, hcH⟩ : H) : G) = p⁻¹ := by
        rw [coe_mul, coe_inv, ← hpc, hpc']
        group
      rw [e]
      exact inv_mem hp
    rw [hzc, mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨j, rfl⟩ := hc
    have hg't : Commute (g' : G) t := mem_centralizer_singleton_iff.mp (mem_inf.mp g'.2).2
    exact (hg't.zpow_right j).eq
  have hcomm := f.isMulCommutative_of_isCyclic_of_ker_le_center hf
  have e := hcomm.is_comm.comm (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at e
  simpa using e

theorem isMulCommutative_quot (hS : Setup L K n φ (zpowers t) t) {S T W : Subgroup G}
    (hfr : ∀ g ∈ normalizer (T : Set G), ∃ s ∈ S, g * s⁻¹ ∈ centralizer ({t} : Set G))
    (hSn : normalizer (T : Set G) ≤ normalizer (S : Set G)) (hST : S ≤ T)
    (hPS : pull φ (antiUnipotent K) ≤ S) (hQT : pull φ (antiUnipotent K) ⊔ zpowers t ≤ T)
    (hW : IsPGroup 2 W) (hTW : T ≤ W) (hWN : W ≤ normalizer (T : Set G)) :
    ∃ _ : (S.subgroupOf W).Normal, IsMulCommutative (W ⧸ S.subgroupOf W) := by
  have hSW : S ≤ W := hST.trans hTW
  have hn : (S.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSW).mpr (hWN.trans hSn)
  refine ⟨hn, ⟨⟨fun a b => ?_⟩⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have key : ∀ z : W, ∃ c ∈ W ⊓ centralizer ({t} : Set G), ∃ hc : c ∈ W,
      (QuotientGroup.mk z : W ⧸ S.subgroupOf W) = QuotientGroup.mk ⟨c, hc⟩ := by
    intro z
    obtain ⟨v, hv, hzv⟩ := hfr _ (hWN z.2)
    have hc : (z : G) * v⁻¹ ∈ W := mul_mem z.2 (inv_mem (hSW hv))
    refine ⟨_, mem_inf.mpr ⟨hc, hzv⟩, hc, ?_⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using inv_mem hv
  obtain ⟨c₁, hc₁, hc₁W, e₁⟩ := key x
  obtain ⟨c₂, hc₂, hc₂W, e₂⟩ := key y
  rw [e₁, e₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
  have hP := comm_mem_P hS hW (hQT.trans hTW) hc₁ hc₂
  exact hPS (by simpa using hP)

end Quot

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀" => (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))

theorem map_X_eq (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {g : G}
    {j k : Axis} (hk : 𝐁[j].map (MulAut.conj g).toMonoidHom = 𝐁[k]) :
    𝐗[j].map (MulAut.conj g).toMonoidHom = 𝐗[k] := by
  have hE : (𝐄[j]).map (MulAut.conj g).toMonoidHom = 𝐄[k] := by
    rw [pCore_normalizer_map_conj g 𝐁[j]]
    exact pCore_map_subtype_congr (congrArg (fun B : Subgroup G => normalizer (B : Set G)) hk)
  have hle : 𝐗[j].map (MulAut.conj g).toMonoidHom ≤ 𝐄[k] :=
    (map_mono (X_le_E h j)).trans_eq hE
  have hW2 : ∀ w ∈ 𝐗[j].map (MulAut.conj g).toMonoidHom, w * w = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, X_mul_self h hbt j hx]
    group
  have hcard : Nat.card (𝐗[j].map (MulAut.conj g).toMonoidHom) = Nat.card K ^ 6 := by
    rw [card_map_of_injective (MulAut.conj g).injective, card_X h j]
  rcases subgroup_le_of_subset_union (fun w hw => mem_X_or_B h hbt k (hle hw) (hW2 w hw)) with
    h1 | h1
  · exact eq_of_le_of_card_ge h1 (by rw [hcard, card_X h k])
  · exfalso
    have h2 := card_le_of_le h1
    rw [hcard, h.card_B k] at h2
    have := two_mul_pow_three_lt h
    omega

theorem normalizer_Q_le_normalizer_S (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    normalizer (𝐐 : Set G) ≤ normalizer (𝐒 : Set G) := by
  intro g hg
  have hX : ∀ j : Axis, ∀ x ∈ 𝐗[j], g * x * g⁻¹ ∈ 𝐒 := by
    intro j x hx
    have hx' : g * x * g⁻¹ ∈ 𝐗[j].map (MulAut.conj g).toMonoidHom := ⟨x, hx, by simp⟩
    rcases h.map_B hg j with hk | hk
    · rw [map_X_eq h hbt hk] at hx'
      exact mem_sup_left hx'
    · rw [map_X_eq h hbt hk] at hx'
      exact mem_sup_right hx'
  exact mem_normalizer_of_conj_le fun x hx => conj_mem_of_sup (hX Axis.one) (hX Axis.two) hx

theorem centralizer_inf_normalizer_le (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    𝐂 ⊓ normalizer (𝐓₀ : Set G) ≤ normalizer (𝐐 : Set G) := by
  rintro c ⟨hcC, hcN⟩
  refine mem_normalizer_of_conj_le fun q hq => ?_
  have hqT : q ∈ 𝐓₀ ⊓ 𝐂 := (T_inf_C h hbt).ge hq
  rw [← T_inf_C h hbt]
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hcN q).mp (mem_inf.mp hqT).1,
    mul_mem (mul_mem hcC (mem_inf.mp hqT).2) (inv_mem hcC)⟩

theorem exists_conj_of_conj_mem_T (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {g : G} (hg : g⁻¹ * t * g ∈ 𝐓₀) :
    ∃ s ∈ 𝐒, g⁻¹ * t * g = s⁻¹ * t * s := by
  have hgS := conj_not_mem_S h hbt g
  have htN : t ∈ normalizer (𝐒 : Set G) := T_le_normalizer_S h hbt (t_mem_T h)
  have hord : orderOf (g⁻¹ * t * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rwa [MulAut.conj_apply, inv_inv, h.setup.order_t] at this
  rw [← SetLike.mem_coe, ← S_mul_t h hbt] at hg
  obtain ⟨s, hs, c, hc, hsc⟩ := Set.mem_mul.mp hg
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
  rcases zpow_eq_one_or_eq h.setup.t_mul_t j with h1 | h1
  · rw [h1, mul_one] at hsc
    rw [← hsc] at hgS
    exact absurd hs hgS
  · rw [h1] at hsc
    refine exists_conj_of_mem_coset h hbt ⟨t⁻¹ * s * t, ?_, ?_⟩ hord
    · have := (mem_normalizer_iff.mp (inv_mem htN) s).mp hs
      rwa [inv_inv] at this
    · rw [← hsc]
      group

theorem exists_mul_inv_mem_C (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {g : G}
    (hg : g ∈ normalizer (𝐓₀ : Set G)) : ∃ s ∈ 𝐒, g * s⁻¹ ∈ 𝐂 := by
  obtain ⟨s, hs, hgs⟩ :=
    exists_conj_of_conj_mem_T h hbt ((mem_normalizer_iff''.mp hg t).mp (t_mem_T h))
  refine ⟨s, hs, mem_centralizer_singleton_iff.mpr ?_⟩
  calc g * s⁻¹ * t = g * (s⁻¹ * t * s) * s⁻¹ := by group
    _ = g * (g⁻¹ * t * g) * s⁻¹ := by rw [hgs]
    _ = t * (g * s⁻¹) := by group

theorem normalizer_T_le_normalizer_S (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    normalizer (𝐓₀ : Set G) ≤ normalizer (𝐒 : Set G) := by
  intro g hg
  obtain ⟨s, hs, hgs⟩ := exists_mul_inv_mem_C h hbt hg
  have hsT : s ∈ normalizer (𝐓₀ : Set G) := le_normalizer (S_le_T h hs)
  have hu : g * s⁻¹ ∈ normalizer (𝐒 : Set G) :=
    normalizer_Q_le_normalizer_S h hbt (centralizer_inf_normalizer_le h hbt
      (mem_inf.mpr ⟨hgs, mul_mem hg (inv_mem hsT)⟩))
  have := mul_mem hu (le_normalizer hs)
  rwa [inv_mul_cancel_right] at this

theorem isPGroup_T (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    IsPGroup 2 𝐓₀ :=
  IsPGroup.of_card (by rw [card_T h hbt, h.setup.card_K, ← pow_mul, ← pow_succ'])

omit [Finite G] [Finite K] in
theorem isPerfect [IsSimpleGroup G] (φ : L ≃* antiSp K) : Group.IsPerfect G := by
  refine Group.isPerfect_def.2 ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
  · exfalso
    have hab : ∀ a b : G, a * b = b * a := fun a b => by
      rw [← commutatorElement_eq_one_iff_mul_comm, ← mem_bot, ← hc, commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    have hx : uElt (1 : K) 0 0 0 = 1 := by
      refine eq_one_of_forall_commute fun z => φ.symm.injective (Subtype.ext ?_)
      rw [map_mul, map_mul, coe_mul, coe_mul, hab]
    rw [← uElt_zero_eq_one] at hx
    exact one_ne_zero (uElt_inj hx).1
  · exact hc

end BothTrivialField

end CFSG.LocalAnalysis.EvenBN.Sp4
