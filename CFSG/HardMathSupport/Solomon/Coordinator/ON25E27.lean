module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Local
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

section


theorem on25_isE27_of_commute {g x : GM} (hg3 : g ^ 3 = 1) (hgZ : g ∉ center GM)
    (hx3 : x ^ 3 = 1) (hxg : x * g = g * x) (hxY : x ∉ zpowers g ⊔ center GM) :
    CFSG.RankThree.PartTwo.Late.IsE27 (zpowers x ⊔ (zpowers g ⊔ center GM)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := on25_card_center_GM
  have hZz : center GM = zpowers zG := center_GM
  set Y := zpowers g ⊔ center GM with hY
  have hY9 : Nat.card Y = 9 := by
    rw [hY, hZz, sup_comm]
    refine CFSG.RankThree.PartTwo.Sec4.card_zpowers_sup_zpowers hg3
      (orderOf_eq_prime relG.xcube relG.x1) (fun h => hgZ (hZz ▸ h)) ?_
    exact (Subgroup.mem_center_iff.mp (hZz ▸ mem_zpowers zG) g)
  have hY3 : ∀ s ∈ Y, s ^ 3 = 1 := by
    intro s hs
    have h := pow_card_eq_one' (G := Y) (x := ⟨s, hs⟩)
    rw [hY9] at h
    exact CFSG.RankThree.PartTwo.Sec13.ON134.pow_three_eq_one (MulEquiv.refl GM) (k := 2)
      (by simpa using congrArg Subtype.val h)
  have hxC : Y ≤ Subgroup.centralizer ({x} : Set GM) := by
    refine sup_le (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hxg.symm)) ?_
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hw x).symm
  exact CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers_sup_of_card_nine hx3 hxY le_rfl hY9 hY3
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hxC hy)).symm

theorem on25_exists_E27 {U : Subgroup GM} (hU : Nat.card U = 81) :
    ∃ A ≤ U, CFSG.RankThree.PartTwo.Late.IsE27 A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := on25_card_center_GM
  have hZz : center GM = zpowers zG := center_GM
  have hU3 : IsPGroup 3 U := IsPGroup.of_card (n := 4) (by rw [hU]; norm_num)
  have hUcube : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hU3 ⟨u, hu⟩
    exact CFSG.RankThree.PartTwo.Sec13.ON134.pow_three_eq_one (MulEquiv.refl GM) (k := k)
      (congrArg Subtype.val hk)
  obtain ⟨P, hUP⟩ := hU3.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  have hr := relG_conj g
  have hz' : MulAut.conj g zG = zG := conj_zG g
  have hUQ : U ≤ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := hg ▸ hUP
  have hnab : ∃ a ∈ U, ∃ b ∈ U, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have hab : ∀ a ∈ U.subgroupOf (threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i))),
        ∀ b ∈ U.subgroupOf (threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i))),
        a * b = b * a := by
      intro a ha b hb
      exact Subtype.ext (hall a (Subgroup.mem_subgroupOf.1 ha) b (Subgroup.mem_subgroupOf.1 hb))
    have := hr.card_le_of_abelian _ hab
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv, hU] at this
    omega
  have hcomm_mem : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ zpowers zG := by
    intro a ha b hb
    have := hr.comm_mem (hUQ ha) (hUQ hb)
    rwa [hz'] at this
  obtain ⟨g₁, hg₁U, u₁, hu₁U, hne⟩ := hnab
  have hcU : ⁅g₁, u₁⁆ ∈ U := by
    rw [commutatorElement_def]
    exact U.mul_mem (U.mul_mem (U.mul_mem hg₁U hu₁U) (U.inv_mem hg₁U)) (U.inv_mem hu₁U)
  have hc1 : ⁅g₁, u₁⁆ ≠ 1 := fun h => hne (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hzU : zG ∈ U := by
    haveI : Fact (Nat.card (zpowers zG)).Prime := ⟨by rw [on25_card_zG]; exact Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
        ((zpowers ⁅g₁, u₁⁆).subgroupOf (zpowers zG)) with h | h
    · exfalso
      have hm : (⟨⁅g₁, u₁⁆, hcomm_mem g₁ hg₁U u₁ hu₁U⟩ : ↥(zpowers zG)) ∈
          (zpowers ⁅g₁, u₁⁆).subgroupOf (zpowers zG) :=
        Subgroup.mem_subgroupOf.2 (mem_zpowers _)
      rw [h, Subgroup.mem_bot] at hm
      exact hc1 (congrArg Subtype.val hm)
    · have hm : (⟨zG, mem_zpowers zG⟩ : ↥(zpowers zG)) ∈
          (zpowers ⁅g₁, u₁⁆).subgroupOf (zpowers zG) := by rw [h]; trivial
      exact (Subgroup.zpowers_le.2 hcU) (Subgroup.mem_subgroupOf.1 hm)
  have hZU : center GM ≤ U := by rw [hZz]; exact Subgroup.zpowers_le.2 hzU
  have hg₁Z : g₁ ∉ center GM := fun h => hne (Subgroup.mem_center_iff.1 h u₁).symm
  have hZc : ∀ u ∈ U, ⁅g₁, u⁆ ∈ center GM := fun u hu => hZz ▸ hcomm_mem g₁ hg₁U u hu
  let φ : ↥U →* GM :=
    { toFun := fun u => ⁅g₁, (u : GM)⁆
      map_one' := by simp
      map_mul' := fun u v => by
        have hv := Subgroup.mem_center_iff.mp (hZc v v.2)
        simp only [commutatorElement_def] at hv
        simp only [Subgroup.coe_mul, commutatorElement_def]
        have key : g₁ * ((u : GM) * v) * g₁⁻¹ * ((u : GM) * v)⁻¹ =
            g₁ * u * g₁⁻¹ * ((g₁ * v * g₁⁻¹ * (v : GM)⁻¹) * (u : GM)⁻¹) := by group
        rw [key, ← hv (u : GM)⁻¹]
        group }
  have hφ : ∀ u : ↥U, φ u = ⁅g₁, (u : GM)⁆ := fun _ => rfl
  have hrange : φ.range ≤ center GM := by
    rintro _ ⟨u, rfl⟩
    exact hZc u u.2
  have hker : 27 ≤ Nat.card φ.ker := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hU] at h1
    have h2 : Nat.card φ.range ≤ 3 := hZ ▸ Subgroup.card_le_of_le hrange
    have h3 : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 3 :=
      Nat.mul_le_mul_left _ h2
    omega
  set C := φ.ker.map U.subtype with hC
  have hCcard : Nat.card C = Nat.card φ.ker := Subgroup.card_map_of_injective U.subtype_injective
  have hY9 : Nat.card (zpowers g₁ ⊔ center GM : Subgroup GM) = 9 := by
    rw [hZz, sup_comm]
    refine CFSG.RankThree.PartTwo.Sec4.card_zpowers_sup_zpowers (hUcube g₁ hg₁U)
      (orderOf_eq_prime relG.xcube relG.x1) (fun h => hg₁Z (hZz ▸ h)) ?_
    exact (Subgroup.mem_center_iff.mp (hZz ▸ mem_zpowers zG) g₁)
  obtain ⟨g₂, hg₂C, hg₂⟩ : ∃ g₂ ∈ C, g₂ ∉ zpowers g₁ ⊔ center GM := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show C ≤ zpowers g₁ ⊔ center GM from hall)
    rw [hY9, hCcard] at h1
    omega
  obtain ⟨u, hu, rfl⟩ := hg₂C
  set g₂ : GM := (u : GM) with hg₂def
  have hg₂g₁ : g₂ * g₁ = g₁ * g₂ := by
    have := (MonoidHom.mem_ker.1 hu)
    rw [hφ] at this
    exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  have hE27 := on25_isE27_of_commute (hUcube g₁ hg₁U) hg₁Z (hUcube g₂ u.2) hg₂g₁ hg₂
  refine ⟨_, sup_le (Subgroup.zpowers_le.mpr u.2) (sup_le (Subgroup.zpowers_le.mpr hg₁U) hZU),
    hE27⟩

end

end CFSG.HardMathSupport.Solomon.Coordinator
