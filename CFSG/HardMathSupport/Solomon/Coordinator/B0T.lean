module

public import CFSG.HardMathSupport.Solomon.Coordinator.B0TKey
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TSuzuki
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

section Certified


theorem suzSections_of_isKGroup {Δ : Type} [Group Δ] [Finite Δ] (hK : CFSG.IsKGroup Δ)
    (h3 : ¬ 3 ∣ Nat.card Δ) : SuzSections Δ := by
  intro P S _ _ _ f hf hnab
  have hcat : CFSG.Assembly.InCatalog S :=
    CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK P S f hf
  have h3S : ¬ 3 ∣ Nat.card S := by
    intro h
    apply h3
    have h2 : Nat.card S ∣ Nat.card P := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    exact h.trans (h2.trans (Subgroup.card_subgroup_dvd_card P))
  obtain ⟨e, he⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd S hnab hcat h3S
  exact suzLike_of_suzukiModel hnab he

theorem inputB0T_holds : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputB0T := by
  intro G _ _ B Δ hBel hBΔ hcop hKΔ hEven
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card Δ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  have hKΔ' : CFSG.IsKGroup ↥Δ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.s1t_isKGroup_of_open hKΔ
  have hSzΔ : SuzSections ↥Δ := suzSections_of_isKGroup hKΔ' h3
  have hB3 : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hBel.2 g g.2)⟩
  have hEΔ : ⁅Δ, B⁆ ≤ Δ := (Subgroup.le_normalizer_iff_commutator_le_left).1 hBΔ
  have hBE : B ≤ Subgroup.normalizer (⁅Δ, B⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_right Δ B
  have hcardE : ¬ 3 ∣ Nat.card (⁅Δ, B⁆ : Subgroup G) :=
    fun h => h3 (h.trans (Subgroup.card_dvd_of_le hEΔ))
  have hEK : ⁅Δ, B⁆ ≤ Δ ⊔ B := hEΔ.trans le_sup_left
  have hBK : B ≤ Δ ⊔ B := le_sup_right
  obtain ⟨P, hP⟩ := exists_sylow_fixed_of_pGroup (p := 2) hB3 hBE hcardE
  set T : Subgroup G := (P : Subgroup (⁅Δ, B⁆ : Subgroup G)).map (⁅Δ, B⁆ : Subgroup G).subtype
    with hT
  have hTE : T ≤ ⁅Δ, B⁆ := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := P.isPGroup'.map _
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := fun b hb =>
    Subgroup.mem_normalizer_fintype fun n hn => by
      obtain ⟨x, hx, rfl⟩ := hn
      exact hP b hb x hx
  refine ⟨T, hTE.trans hEΔ, hT2, hBT, fun hTB => ?_⟩
  have hcomm : ∀ x ∈ T, ∀ b ∈ B, x * b = b * x := by
    intro x hx b hb
    have : ⁅x, b⁆ ∈ ⁅T, B⁆ := Subgroup.commutator_mem_commutator hx hb
    rw [hTB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hDn : (⁅Δ, B⁆.subgroupOf (Δ ⊔ B)).Normal := inferInstance
  have hB3' : IsPGroup 3 (B.subgroupOf (Δ ⊔ B)) := hB3.comap_subtype
  let eD : ↥(⁅Δ, B⁆.subgroupOf (Δ ⊔ B)) ≃* ↥(⁅Δ, B⁆ : Subgroup G) :=
    Subgroup.subgroupOfEquivOfLe hEK
  have hcardD : Nat.card ↥(⁅Δ, B⁆.subgroupOf (Δ ⊔ B)) = Nat.card (⁅Δ, B⁆ : Subgroup G) :=
    Nat.card_congr eD.toEquiv
  have h3D : ¬ 3 ∣ Nat.card ↥(⁅Δ, B⁆.subgroupOf (Δ ⊔ B)) := by
    rw [hcardD]
    exact hcardE
  have hSzD : SuzSections ↥(⁅Δ, B⁆.subgroupOf (Δ ⊔ B)) :=
    hSzΔ.of_injective ((Subgroup.inclusion hEΔ).comp eD.toMonoidHom)
      ((Subgroup.inclusion_injective hEΔ).comp eD.injective)
  have hcopBΔ : Nat.Coprime (Nat.card B) (Nat.card Δ) := by
    obtain ⟨m, hm⟩ := hB3.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_left m hcop
  have hcommD : ⁅⁅Δ, B⁆.subgroupOf (Δ ⊔ B), B.subgroupOf (Δ ⊔ B)⁆ =
      ⁅Δ, B⁆.subgroupOf (Δ ⊔ B) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (Δ ⊔ B))
    have hmapD : (⁅Δ, B⁆.subgroupOf (Δ ⊔ B)).map (Δ ⊔ B).subtype = ⁅Δ, B⁆ := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 hEK
    have hmapB : (B.subgroupOf (Δ ⊔ B)).map (Δ ⊔ B).subtype = B := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 hBK
    rw [Subgroup.map_commutator, hmapD, hmapB]
    exact BenderSuzuki.ig1114_commutator_idempotent_of_coprime Δ B hcopBΔ hBΔ
  obtain ⟨P', hP'⟩ : ∃ P' : Sylow 2 ↥(⁅Δ, B⁆.subgroupOf (Δ ⊔ B)),
      ∀ x ∈ (P' : Subgroup ↥(⁅Δ, B⁆.subgroupOf (Δ ⊔ B))), ∀ b ∈ B.subgroupOf (Δ ⊔ B),
        ((x : ↥(Δ ⊔ B)) * b = b * x) := by
    refine ⟨Sylow.mapSurjective (f := eD.symm.toMonoidHom) eD.symm.surjective P, fun x hx b hb => ?_⟩
    change x ∈ Subgroup.map eD.symm.toMonoidHom (P : Subgroup ↥(⁅Δ, B⁆ : Subgroup G)) at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subtype.ext (hcomm (y : G) ⟨y, hy, rfl⟩ (b : G) hb)
  have hkey := odd_card_of_centralizes_sylow _ (Y := ↥(Δ ⊔ B)) (⁅Δ, B⁆.subgroupOf (Δ ⊔ B))
    (B.subgroupOf (Δ ⊔ B)) rfl hDn hB3' h3D hSzD hcommD ⟨P', hP'⟩
  rw [hcardD] at hkey
  exact (Nat.not_even_iff_odd.2 hkey) hEven

end Certified

end CFSG.HardMathSupport.Solomon.Coordinator
