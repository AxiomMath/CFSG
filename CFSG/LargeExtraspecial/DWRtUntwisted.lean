module

public import CFSG.LargeExtraspecial.DWRtAbstract
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.LargeExtraspecial.DW

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem parabolicPosRoots_singleton (i : Fin τ.rank) :
    parabolicPosRoots τ {i} = {Pi.single i 1} := by
  ext α
  constructor
  · rintro ⟨⟨hr, hsupp⟩, -, hpos⟩
    have hα : α = (α i) • (Pi.single i 1 : Fin τ.rank → ℤ) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hsupp j hj, hj]
    rcases (isRoot_smul_single_iff i (α i)).1 (hα ▸ hr) with h | h
    · rw [Set.mem_singleton_iff, hα, h, one_smul]
    · rw [hα, h, neg_one_smul, height_neg, height_single] at hpos
      norm_num at hpos
  · rintro rfl
    refine ⟨⟨isRoot_single τ i, fun j hj => ?_⟩, isRoot_single τ i, ?_⟩
    · rw [Set.mem_singleton_iff] at hj
      simp [hj]
    · rw [height_single]
      exact one_pos

theorem parabolicLeviUnipotent_singleton_le
    (i : Fin τ.rank) :
    parabolicLeviUnipotent τ K {i} ≤
      Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) := by
  rw [parabolicLeviUnipotent, rootSpan, parabolicPosRoots_singleton]
  refine iSup₂_le fun α hα => ?_
  rw [Set.mem_singleton_iff] at hα
  subst hα
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [pinnedX_single]
  exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem closure_xUnit_yUnit_le_adjointGroup
    (i : Fin τ.rank) :
    Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) ≤ adjointGroup τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact xUnit_mem_adjointGroup i c
  · exact yUnit_mem_adjointGroup i c

theorem closure_xUnit_yUnit_le_parabolicLevi
    (i : Fin τ.rank) :
    Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) ≤
      parabolicLevi τ K {i} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact xUnit_mem_parabolicLevi (Set.mem_singleton i) c
  · exact yUnit_mem_parabolicLevi (Set.mem_singleton i) c

theorem exists_rankOne_injective
    [CharP K 2] (i : Fin τ.rank) :
    ∃ ρ : SL2 K →* ModGL τ K, (∀ c, ρ (uSL c) = xUnit τ K i c) ∧
      ρ.range = Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) ∧
      Function.Injective ρ := by
  obtain ⟨ρ, hu, -, -, -, hrange, hker, -, -⟩ := exceptional_ordinary_rank_one_central_image τ K i
  exact ⟨ρ, hu, hrange, injective_of_ker_scalar ρ hker⟩

theorem not_isTransClass34_adjointGroup
    [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (D : Set (adjointGroup τ K)) :
    ¬ IsTransClass34 D := by
  intro hD
  have hfin : Finite (ModGL τ K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨⟨S, hS⟩, -, hUV, -⟩ := exceptional_ordinary_Sylow_opposition τ K 2 w₀ hw₀
  let C := adjointGroup τ K
  let U : Subgroup C := (posUnipotent τ K).subgroupOf C
  have hDU : ∃ d ∈ D, d ∈ U := by
    obtain ⟨d₀, hd₀, -⟩ := hD.2.1
    obtain ⟨hne, hsq⟩ := hD.2.2.1 d₀ hd₀
    have h2 : IsPGroup 2 (Subgroup.zpowers d₀) := by
      rintro ⟨g, hg⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      refine ⟨1, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, sq, hsq, one_zpow]
    obtain ⟨T, hT⟩ := h2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C T S
    refine ⟨g * d₀ * g⁻¹, hD.conj_mem g hd₀, ?_⟩
    have hmem : g * d₀ * g⁻¹ ∈ ((g • T : Sylow 2 C) : Subgroup C) := by
      rw [coe_smul_sylow_eq_map]
      exact ⟨d₀, hT (Subgroup.mem_zpowers d₀), by simp [MulAut.conj_apply]⟩
    rw [hg, hS] at hmem
    exact hmem
  have hU : U ≠ ⊤ := by
    intro htop
    let i₀ : Fin τ.rank := ⟨0, by cases τ <;> decide⟩
    have hy : (⟨yUnit τ K i₀ 1, yUnit_mem_adjointGroup i₀ 1⟩ : C) ∈ U :=
      htop ▸ Subgroup.mem_top _
    have hy' : yUnit τ K i₀ 1 ∈ posUnipotent τ K ⊓ negUnipotent τ K :=
      ⟨hy, yUnit_mem_negUnipotent i₀ 1⟩
    rw [hUV, Subgroup.mem_bot, ← yUnit_zero i₀] at hy'
    obtain ⟨-, -, -, -, -, -, -, -, hyinj⟩ := exceptional_ordinary_rank_one_central_image τ K i₀
    exact one_ne_zero (hyinj hy')
  choose ρ hρu hρrange hρinj using fun i : Fin τ.rank => exists_rankOne_injective (K := K) i
  have hρC : ∀ i g, ρ i g ∈ C := fun i g =>
    closure_xUnit_yUnit_le_adjointGroup i (hρrange i ▸ ⟨g, rfl⟩)
  have hρM : ∀ i g, ρ i g ∈ parabolicLevi τ K {i} := fun i g =>
    closure_xUnit_yUnit_le_parabolicLevi i (hρrange i ▸ ⟨g, rfl⟩)
  let φ : ∀ i : Fin τ.rank, SL2 K →* C := fun i => (ρ i).codRestrict C (hρC i)
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_four_le hK
  refine false_of_parabolic_family hD U hDU hU
    (fun i => (parabolicSubgroup τ K {i}).subgroupOf C)
    (fun i => (parabolicRadical τ K {i}).subgroupOf C)
    (fun i => (parabolicLevi τ K {i}).subgroupOf C) ?_ ?_ ?_ ?_ ?_ (fun _ => K) (fun _ => s)
    (fun _ => hs0) (fun _ => hs1) φ ?_ ?_ ?_
  ·
    intro i x hx
    exact parabolicRadical_le_posUnipotent {i} hx
  ·
    intro i p hp x hx
    have hn := parabolicSubgroup_le_normalizer_parabolicRadical (K := K) {i} hp
    have := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
    simpa [Subgroup.mem_subgroupOf] using this
  ·
    intro i x hx
    exact parabolicLevi_le_parabolicSubgroup {i} hx
  ·
    intro i
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : (x : ModGL τ K) ∈ parabolicRadical τ K {i} ⊓ parabolicLevi τ K {i} :=
      ⟨hx.1, hx.2⟩
    rw [parabolicRadical_inf_parabolicLevi, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  ·
    rw [eq_top_iff]
    intro g _
    have hle : C ≤ (⨆ i, (parabolicSubgroup τ K {i}).subgroupOf C).map C.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨i, c, hx | hx⟩
      · have hx' : x = xUnit τ K i c := Units.ext hx
        subst hx'
        exact ⟨⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩, Subgroup.mem_iSup_of_mem i
          (posUnipotent_le_parabolicSubgroup {i} (xUnit_mem_posUnipotent i c)), rfl⟩
      · have hx' : x = yUnit τ K i c := Units.ext hx
        subst hx'
        exact ⟨⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩, Subgroup.mem_iSup_of_mem i
          (parabolicLevi_le_parabolicSubgroup {i}
            (yUnit_mem_parabolicLevi (Set.mem_singleton i) c)), rfl⟩
    obtain ⟨y, hy, hyg⟩ := hle g.2
    rwa [show y = g from Subtype.ext hyg] at hy
  ·
    intro i a b h
    exact hρinj i (congrArg Subtype.val h)
  ·
    rintro i _ ⟨g, rfl⟩
    exact hρM i g
  ·
    intro i u hu
    have hu' : (u : ModGL τ K) ∈ ((parabolicRadical τ K {i} : Set (ModGL τ K)) *
        (parabolicLeviUnipotent τ K {i} : Set (ModGL τ K))) := by
      rw [← posUnipotent_eq_mul_parabolic {i}]
      exact hu
    obtain ⟨q, hq, v, hv, hqv⟩ := hu'
    obtain ⟨g, hg⟩ : ∃ g, ρ i g = v := by
      have hv' := parabolicLeviUnipotent_singleton_le (K := K) i hv
      rw [← hρrange i] at hv'
      exact hv'
    have hqC : q ∈ C := by
      have : q = (u : ModGL τ K) * (ρ i g)⁻¹ := by rw [hg, ← hqv]; group
      rw [this]
      exact C.mul_mem u.2 (C.inv_mem (hρC i g))
    refine ⟨⟨q, hqC⟩, hq, g, Subtype.ext ?_⟩
    change (u : ModGL τ K) = q * ρ i g
    rw [hg]
    exact hqv.symm

end CFSG.LargeExtraspecial.DW
