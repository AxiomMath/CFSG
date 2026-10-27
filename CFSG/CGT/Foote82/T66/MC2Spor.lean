module

public import CFSG.CGT.Foote82.FPrimeDefs
import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallModels
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
public import CFSG.CGT.Foote82.T66.CitedMC2
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.Blueprint.NativeSporadic

@[expose] def FSurj (Y : Type*) [Group Y] : Prop :=
  (∃ n : ℕ, 6 ≤ n ∧ ∃ α : Y →* alternatingGroup (Fin n), Function.Surjective α) ∨
    (∃ α : Y →* ↥(omegaMinusTwo 2), Function.Surjective α) ∨
    (∃ α : Y →* ↥(omegaMinusTwo 3), Function.Surjective α)

theorem IsFPrimeModule.fSurj {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {L : Subgroup (GLV V)} (h : IsFPrimeModule L) : FSurj ↥L := by
  rcases h with ⟨n, hn, α, hα, -⟩ | ⟨⟨α, hα⟩, -⟩ | ⟨α, hα, -⟩ | ⟨α, hα, -⟩ | ⟨α, hα, -⟩ |
    ⟨⟨α, hα⟩, -⟩
  · exact Or.inl ⟨n, hn, α, hα⟩
  · exact Or.inl ⟨7, by norm_num, α, hα⟩
  · obtain ⟨φ, -, -⟩ := CFSG.RankThree.PartTwo.Sec19.SimsItem316Small.omegaPlusTwo_three_model
    exact Or.inl ⟨8, by norm_num, φ.toMonoidHom.comp α, φ.surjective.comp hα⟩
  · exact Or.inr (Or.inl ⟨α, hα⟩)
  · exact Or.inr (Or.inr ⟨α, hα⟩)
  · exact Or.inl ⟨6, le_rfl, α, hα⟩

theorem fSurj_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') (h : FSurj Y') :
    FSurj Y := by
  rcases h with ⟨n, hn, α, hα⟩ | ⟨α, hα⟩ | ⟨α, hα⟩
  · exact Or.inl ⟨n, hn, α.comp e.toMonoidHom, hα.comp e.surjective⟩
  · exact Or.inr (Or.inl ⟨α.comp e.toMonoidHom, hα.comp e.surjective⟩)
  · exact Or.inr (Or.inr ⟨α.comp e.toMonoidHom, hα.comp e.surjective⟩)

theorem center_eq_bot_of_simple {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    (h : ¬ (Nat.card T).Prime) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h0 | h0
  · exact h0
  · exfalso
    have : IsMulCommutative T :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a)⟩⟩
    exact h (Group.is_simple_iff_prime_card.1 inferInstance)

theorem center_omegaMinusTwo {m : ℕ} (hm : 2 ≤ m) : Subgroup.center ↥(omegaMinusTwo m) = ⊥ := by
  have : IsSimpleGroup ↥(omegaMinusTwo m) :=
    CFSG.ComponentClassification.RankTwoClassical.ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le
      (K := ZMod 2) (m := m + 1) (by omega)
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one
  refine center_eq_bot_of_simple ?_
  obtain ⟨s, -, hs⟩ := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.exists_card_omegaMinusTwo hm
  refine CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.not_prime_of_four_dvd ?_
  rw [hs]
  refine Dvd.dvd.mul_right ?_ s
  have h6 := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.two_le_succ_mul hm
  have := pow_dvd_pow 2 (show 2 ≤ (m + 1) * m by omega)
  simpa using this

theorem exists_surjective_lift {A B T : Type*} [Group A] [Group B] [Group T] (p : A →* B)
    (hp : Function.Surjective p) (hker : p.ker ≤ Subgroup.center A) (α : A →* T)
    (hα : Function.Surjective α) (hT : Subgroup.center T = ⊥) :
    ∃ β : B →* T, Function.Surjective β := by
  have hle : p.ker ≤ α.ker := by
    intro a ha
    have hac := hker ha
    have : α a ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun t => by
      obtain ⟨b, rfl⟩ := hα t
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hac b)]
    rw [hT, Subgroup.mem_bot] at this
    exact this
  refine ⟨p.liftOfSurjective hp ⟨α, hle⟩, fun t => ?_⟩
  obtain ⟨a, rfl⟩ := hα t
  exact ⟨p a, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a⟩

theorem fSurj_map {Γ Γ' : Type*} [Group Γ] [Group Γ'] (π : Γ →* Γ')
    (hker : π.ker ≤ Subgroup.center Γ) {A : Subgroup Γ} (h : FSurj ↥A) : FSurj ↥(A.map π) := by
  have hp : Function.Surjective (π.subgroupMap A) := π.subgroupMap_surjective A
  have hpker : (π.subgroupMap A).ker ≤ Subgroup.center ↥A := by
    intro a ha
    have hπ : π a = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 ha)
      simpa using this
    have hc : (a : Γ) ∈ Subgroup.center Γ := hker hπ
    exact Subgroup.mem_center_iff.2 fun b => Subtype.ext (Subgroup.mem_center_iff.1 hc b)
  rcases h with ⟨n, hn, α, hα⟩ | ⟨α, hα⟩ | ⟨α, hα⟩
  · obtain ⟨β, hβ⟩ := exists_surjective_lift _ hp hpker α hα
      (alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))
    exact Or.inl ⟨n, hn, β, hβ⟩
  · obtain ⟨β, hβ⟩ := exists_surjective_lift _ hp hpker α hα (center_omegaMinusTwo le_rfl)
    exact Or.inr (Or.inl ⟨β, hβ⟩)
  · obtain ⟨β, hβ⟩ := exists_surjective_lift _ hp hpker α hα (center_omegaMinusTwo (by norm_num))
    exact Or.inr (Or.inr ⟨β, hβ⟩)

theorem sporadic_false (hG5 : SporadicNoFComponent) {X : Type} [Group X] [Finite X]
    (hX : IsSporadic X .J2 ∨ IsSporadic X .Suz ∨ IsSporadic X .He ∨ IsSporadic X .Ru ∨
      IsSporadic X .Co1)
    {Y : Subgroup X} (hY : standardComponentIsStandard Y) (hS : FSurj ↥Y) : False := by
  obtain ⟨t, htC, ht2⟩ := CFSG.StandardSubgroupAPI.exists_mem_orderOf_eq_two_of_even hY.2.1
  have hYt : Y ≤ Subgroup.centralizer ({t} : Set X) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 htC y hy)
  have hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (Y : Set X) := fun g hg =>
    hY.2.2.2.1 ▸ CFSG.StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hY.2.2.1 htC ht2
      (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hnormal : (Y.subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYt).2 hN
  have hcomp : IsComponentOf Y (Subgroup.centralizer ({t} : Set X)) :=
    ⟨hYt, CFSG.Open.IsSubnormal.step hYt hnormal (CFSG.Open.IsSubnormal.refl _), hY.1⟩
  obtain ⟨h1, h2, h3⟩ := hG5 X hX t ht2 Y hcomp
  rcases hS with ⟨n, hn, α, hα⟩ | ⟨α, hα⟩ | ⟨α, hα⟩
  · exact h1 n hn α hα
  · exact h2 α hα
  · exact h3 α hα

end MC2

end CFSG.CGT.Foote82
