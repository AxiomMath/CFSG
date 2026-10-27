module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43H
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem false_of_normal_index_two (hG : IsSimpleGroup G) (hnc : ∃ a b : G, a * b ≠ b * a)
    (N : Subgroup G) [N.Normal] (hN : N.index = 2) : False := by
  rcases hG.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.index_bot] at hN
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card hN
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    let _ : CommGroup G := IsCyclic.commGroup
    exact mul_comm a b
  · rw [h, Subgroup.index_top] at hN
    omega

omit [Finite G] in
theorem withKernel_conj_mem {K : Subgroup G} {n y : G} (hn : n ∈ normalizer (K : Set G))
    (hy : y ∈ withKernel K) : n * y * n⁻¹ ∈ withKernel K := by
  have hle : (withKernel K).map (MulAut.conj n).toMonoidHom ≤ withKernel K := by
    rw [withKernel, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact (mem_normalizer_iff.mp hn k).mp hk
    · rintro _ ⟨q, hq, rfl⟩
      exact UnbalancedLayer.conj_mem_coreActionKernel hn hq
  exact hle ⟨y, hy, rfl⟩

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34Lemma43HeldStep_of_inputs
    (hAut : L34Lemma43HeldAutStep) (h64 : HeldSylowElementarySixtyFour)
    (hZc : HeldSylowCenterTwo) (hOut : HeldOuterInvolutionRank) : L34Lemma43HeldStep := by
  intro G _ _ a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc he hJK
  obtain ⟨hKN, hxK⟩ := hAut G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc he hJK
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, -, -, hS, -, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, -, -, -, hLB, -, -⟩ := hbase
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hSK : S ≤ normalizer (K : Set G) := (hS.1.trans hNJ).trans hKN
  obtain ⟨T, hT, hST⟩ := GrS4.exists_isSylowTwoIn_le' hSK hS2
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hT
  have h3T : IsThreeConnected T := isThreeConnected_sylow e h64 hZc hOut hT
  obtain ⟨hAW, hA8, -⟩ := hrun
  obtain ⟨c, -, hc⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn (GrS4.isSylowTwoIn_withKernel hS) hAW
    hA8.1.isPGroup
  set E₀ : Subgroup G := A.map (MulAut.conj c⁻¹).toMonoidHom with hE₀def
  have hE₀S₁ : E₀ ≤ S ⊓ withKernel J := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hc y hy
    have h2 : S ⊓ J ⊔ S ⊓ coreActionKernel J ≤ S ⊓ withKernel J :=
      sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    simpa [MulAut.conj_apply] using h2 h1
  have hE₀ : IsAbelianTwoOfRank 3 E₀ := (hA8.1.map_conj c⁻¹).isAbelianTwoOfRank (by
    rw [card_map_of_injective (MulAut.conj c⁻¹).injective, hA8.2])
  have hWE₀ : wGroup E₀ = W := hWB E₀ hE₀S₁ hE₀
  have hE₀T : E₀ ≤ T := (hE₀S₁.trans inf_le_left).trans hST
  have hWT : ∀ F : Subgroup G, F ≤ T → IsAbelianTwoOfRank 3 F → wGroup F = W :=
    fun F hFT hF => (wGroup_eq_of_le_threeConnected hGW h3T hE₀T hE₀ hFT hF).trans hWE₀
  have hTM : T ≤ M := fun t ht => GrS4.mem_normalizer_of_map_le' hWT hE₀T hE₀ (by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem ht (hE₀T hy)) (inv_mem ht))
  have hTSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = T := by
    obtain ⟨Q, hTQ⟩ := hT2.exists_le_sylow
    refine ⟨Q, le_antisymm ?_ hTQ⟩
    by_contra hQT
    have hlt : T.subgroupOf Q < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hQT fun q hq => ?_
      have : (⟨q, hq⟩ : Q) ∈ T.subgroupOf Q := by rw [htop]; exact mem_top _
      exact mem_subgroupOf.mp this
    have hnil : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
    obtain ⟨y, hyN, hyT⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hyM : (y : G) ∈ M := by
      refine GrS4.mem_normalizer_of_map_le' hWT hE₀T hE₀ ?_
      rintro _ ⟨z, hz, rfl⟩
      have hzQ : z ∈ Q := hTQ (hE₀T hz)
      have hz' : (⟨z, hzQ⟩ : Q) ∈ T.subgroupOf Q := mem_subgroupOf.mpr (hE₀T hz)
      have := (mem_normalizer_iff.mp hyN _).mp hz'
      exact mem_subgroupOf.mp this
    have hQ' : IsPGroup 2 ↥(T ⊔ zpowers (y : G)) :=
      Q.isPGroup'.to_le (sup_le hTQ (zpowers_le.mpr y.2))
    have heq := hT.eq_of_le le_sup_left (sup_le hT.1 (zpowers_le.mpr (hKN hyM))) hQ'
    have hyT' : (y : G) ∈ T ⊔ zpowers (y : G) :=
      (le_sup_right : zpowers (y : G) ≤ T ⊔ zpowers (y : G)) (mem_zpowers (y : G))
    rw [heq] at hyT'
    exact hyT (mem_subgroupOf.mpr hyT')
  obtain ⟨P, hPT⟩ := hTSyl
  set U : Subgroup G := T ⊓ withKernel K with hU
  have hxT : x ∈ T := hST hxS
  have hxU : x ∉ U := fun h => hxK (mem_inf.mp h).2
  have hUidx : U.relIndex T = 2 := by
    have hUT : U ≤ T := inf_le_left
    have h1 : U.relIndex T * Nat.card U = Nat.card T := by
      have h := relIndex_mul_card U T
      rwa [inf_eq_left.mpr hUT] at h
    have h2 : Nat.card T ≤ 2 * Nat.card U := card_le_two_mul_card_inf e hT.1
    have hne1 : U.relIndex T ≠ 1 := by
      rw [Ne, relIndex_eq_one]
      exact fun h => hxU (h hxT)
    have hpos : 0 < Nat.card U := Nat.card_pos
    have hle2 : U.relIndex T ≤ 2 := by
      by_contra hgt
      have hgt' : 3 ≤ U.relIndex T := by omega
      have h3 : 3 * Nat.card U ≤ U.relIndex T * Nat.card U := Nat.mul_le_mul_right _ hgt'
      omega
    have hne0 : U.relIndex T ≠ 0 := by
      intro h
      rw [h, zero_mul] at h1
      exact (Nat.card_pos (α := T)).ne' h1.symm
    omega
  have hxx : x * x = 1 := by rw [← pow_two, ← hU3.2.1, pow_orderOf_eq_one]
  have hTidx : ¬ 2 ∣ T.index := by rw [← hPT]; exact P.not_dvd_index
  obtain ⟨g, hgU⟩ : ∃ g : G, g⁻¹ * x * g ∈ U := by
    by_contra hcon
    obtain ⟨N, hN, hidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hT2 hTidx
      inf_le_left hUidx hxT hxU (fun y hyT hyU => by
        rw [hU3.2.1]
        have hy1 : y ≠ 1 := fun h => hyU (h ▸ one_mem _)
        have hpos := orderOf_pos y
        have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
        omega) (fun g hg => hcon ⟨g, hg⟩)
    exact GrS4.false_of_normal_index_two hsimple hnab N hidx
  obtain ⟨h₀, hx₀⟩ := exists_extremal_conj ⟨P, hPT⟩ hxT
  have hgT : g⁻¹ * x * g ∈ T := (mem_inf.mp hgU).1
  have hgg : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
    rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group, hxx]
    group
  obtain ⟨m₁, hm₁M, hm₁⟩ := GrS4.exists_mem_normalizer_of_extremal hWT hx₀ (y := x)
    (k := h₀⁻¹) (by group) (GrS4.three_le_pRank_of_held e h64 hOut hT hxT hxx)
  obtain ⟨m₂, hm₂M, hm₂⟩ := GrS4.exists_mem_normalizer_of_extremal hWT hx₀
    (y := g⁻¹ * x * g) (k := h₀⁻¹ * g) (by group)
    (GrS4.three_le_pRank_of_held e h64 hOut hT hgT hgg)
  have hconj : g⁻¹ * x * g = (m₁⁻¹ * m₂)⁻¹ * x * (m₁⁻¹ * m₂) := by
    have hx₀' : h₀⁻¹ * x * h₀ = m₁ * x * m₁⁻¹ :=
      calc h₀⁻¹ * x * h₀ = m₁ * (m₁⁻¹ * (h₀⁻¹ * x * h₀) * m₁) * m₁⁻¹ := by group
        _ = m₁ * x * m₁⁻¹ := by rw [← hm₁]
    rw [hm₂, hx₀']
    group
  have h1 : (m₁⁻¹ * m₂)⁻¹ * x * (m₁⁻¹ * m₂) ∈ withKernel K := hconj ▸ (mem_inf.mp hgU).2
  have hn : m₁⁻¹ * m₂ ∈ normalizer (K : Set G) := hKN (mul_mem (inv_mem hm₁M) hm₂M)
  apply hxK
  have h2 := GrS4.withKernel_conj_mem hn h1
  rwa [show m₁⁻¹ * m₂ * ((m₁⁻¹ * m₂)⁻¹ * x * (m₁⁻¹ * m₂)) * (m₁⁻¹ * m₂)⁻¹ = x by group] at h2

end CFSG.ComponentClassification.GrSLit
