module

public import CFSG.Goldschmidt.Steps.G312Comp
public import CFSG.Goldschmidt.Steps.G312Lin
import CFSG.Goldschmidt.Steps.Balance
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.Goldschmidt.G312

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_two_pow_mem
    {H A : Subgroup G} (hS : IsSStarIn H A) {𝔐 : Type*} [Group 𝔐]
    [Finite 𝔐] (φ : H →* 𝔐) {ζ₀ : 𝔐} (hζ₀ : ζ₀ ∈ Subgroup.center 𝔐)
    (hUI : ∀ y ∈ commutator 𝔐, y ^ 2 = 1 → y = 1 ∨ y = ζ₀) (h : H)
    (hh : (h : G) ∈ normalClosureIn H A ⊔ oddCoreOf H) :
    ∃ m : ℕ, φ h ^ 2 ^ m ∈ ((oddCoreOf H).subgroupOf H).map φ := by
  classical
  obtain ⟨-, -, T, -, -, -, hlayer, -, -, htypes⟩ := hS
  set K := normalClosureIn H A with hK
  set O := oddCoreOf H with hO
  set X := φ.range with hX
  have hOsub : O.subgroupOf H = goldschmidtOddCore H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hOn : (O.subgroupOf H).Normal := by rw [hOsub]; infer_instance
  have hOodd : Odd (Nat.card (O.subgroupOf H)) := by
    rw [hOsub]
    have := Balance.odd_card_oddCoreOf H
    rwa [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective] at this
  set X₁ : Subgroup X := (O.subgroupOf H).map φ.rangeRestrict with hX₁
  have hX₁n : X₁.Normal := hOn.map φ.rangeRestrict φ.rangeRestrict_surjective
  have hX₁odd : Odd (Nat.card X₁) := Odd.of_dvd_nat hOodd (Subgroup.card_map_dvd _ _)
  obtain ⟨ζ, hζc, hUIX⟩ : ∃ ζ : X, ζ ∈ Subgroup.center X ∧
      ∀ y ∈ commutator X, y ^ 2 = 1 → y = 1 ∨ y = ζ := by
    have hcomm : ∀ y ∈ commutator X, (y : 𝔐) ∈ commutator 𝔐 := by
      intro y hy
      have h1 := Subgroup.mem_map_of_mem X.subtype hy
      rw [Subgroup.map_subtype_commutator] at h1
      exact Subgroup.commutator_mono le_top le_top h1
    by_cases hmem : ζ₀ ∈ X
    · refine ⟨⟨ζ₀, hmem⟩, ?_, fun y hy hy2 => ?_⟩
      · rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.mp hζ₀ g)
      · rcases hUI _ (hcomm y hy) (by rw [← Subgroup.coe_pow, hy2, Subgroup.coe_one]) with
          h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
    · refine ⟨1, Subgroup.one_mem _, fun y hy hy2 => Or.inl ?_⟩
      rcases hUI _ (hcomm y hy) (by rw [← Subgroup.coe_pow, hy2, Subgroup.coe_one]) with
        h1 | h1
      · exact Subtype.ext h1
      · exact absurd (h1 ▸ y.2) hmem
  set Ψ : H →* X ⧸ X₁ := (QuotientGroup.mk' X₁).comp φ.rangeRestrict with hΨ
  have hΨO : ∀ o : H, (o : G) ∈ O → Ψ o = 1 := by
    intro o ho
    rw [hΨ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨o, ho, rfl⟩
  have hΨmem : ∀ g : H, ∀ m : ℕ, Ψ g ^ m = 1 → φ g ^ m ∈ (O.subgroupOf H).map φ := by
    intro g m hg
    rw [← map_pow, hΨ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hg
    obtain ⟨o, ho, hoe⟩ := hg
    refine ⟨o, ho, ?_⟩
    have := congrArg Subtype.val hoe
    rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, map_pow] at this
    exact this
  have hKH : K ≤ H := Sec8.normalClosureIn_le_self H A
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
      (Sec8.le_normalizer_normalClosureIn H A)
  set ΨK : K →* X ⧸ X₁ := Ψ.comp (Subgroup.inclusion hKH) with hΨK
  have hOK : goldschmidtOddCore K ≤ ΨK.ker := by
    intro o ho
    rw [MonoidHom.mem_ker]
    exact hΨO _ (Balance.oddCoreOf_le_of_normal hKH hKn ⟨o, ho, rfl⟩)
  set Ψbar := QuotientGroup.lift (goldschmidtOddCore K) ΨK hOK with hΨbar
  have hcomp : ∀ L : Subgroup (K ⧸ goldschmidtOddCore K), IsComponentOf L ⊤ →
      L ≤ Ψbar.ker := by
    intro L hL
    have hLq : CFSG.Open.IsQuasisimple L := hL.2.2
    set ψ : L →* X ⧸ X₁ := Ψbar.comp L.subtype with hψ
    have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hLq.1]
    have hζc' : ∀ x ∈ ψ.range, x * (ζ : X ⧸ X₁) = (ζ : X ⧸ X₁) * x := by
      intro x _
      refine QuotientGroup.induction_on x fun g => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hζc g]
    have hrange := range_eq_bot_of_unique_involution hLq (htypes L hL) ψ hζc'
      (eq_one_or_eq_of_isPerfect X₁ hX₁odd hUIX ψ.range hperf)
    intro l hl
    rw [MonoidHom.mem_ker]
    have : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨⟨l, hl⟩, rfl⟩
    rw [hrange, Subgroup.mem_bot] at this
    exact this
  have hlay : goldschmidtLayer (K ⧸ goldschmidtOddCore K) ≤ Ψbar.ker :=
    sSup_le fun L hL => hcomp L hL
  have hK2 : ∀ k : K, ∃ m : ℕ, ΨK k ^ 2 ^ m = 1 := by
    intro k
    have hx : (k : K ⧸ goldschmidtOddCore K) ∈
        CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) ⊔ Ψbar.ker := by
      have : (k : K ⧸ goldschmidtOddCore K) ∈ (⊤ : Subgroup (K ⧸ goldschmidtOddCore K)) :=
        Subgroup.mem_top _
      rw [← hlayer] at this
      exact (sup_le_sup_left hlay _) this
    obtain ⟨c, hc, z, hz, hcz⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨m, hm⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2 ⟨c, hc⟩
    refine ⟨m, ?_⟩
    have h1 : ΨK k = Ψbar c := by
      rw [← QuotientGroup.lift_mk (goldschmidtOddCore K) hOK k, ← hΨbar, ← hcz, map_mul,
        MonoidHom.mem_ker.mp hz, mul_one]
    have hc1 : c ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [h1, ← map_pow, hc1, map_one]
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hh' : h ∈ K.subgroupOf H ⊔ O.subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup hKH hOH]
    exact hh
  obtain ⟨k, hk, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh'
  obtain ⟨m, hm⟩ := hK2 ⟨k, hk⟩
  refine ⟨m, hΨmem _ (2 ^ m) ?_⟩
  rw [map_mul, hΨO o ho, mul_one]
  exact hm

end CFSG.Goldschmidt.G312
