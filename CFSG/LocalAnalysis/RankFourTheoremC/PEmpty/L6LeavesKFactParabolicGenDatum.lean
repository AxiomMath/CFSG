module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenCore
public import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.ASVolI.ChIJK Subgroup

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem posUnipotentExcept_ne_bot (hext : SteinbergExtras D n H) (hrank : 2 ≤ D.rank)
    (i : Fin D.rank) : posUnipotentExcept D i ≠ ⊥ := by
  haveI : Nontrivial (Fin D.rank) := Fin.nontrivial_iff_two_le.mpr hrank
  obtain ⟨j, hji⟩ := exists_ne i
  intro hbot
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈
      (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j) hji (by simp)
  have hle := rootGroup_le_posUnipotentExcept (D := D) hα
  rw [hbot, le_bot_iff] at hle
  exact hext.ne_bot _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j) hle

theorem torus_le_normalizer_posUnipotentExcept
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (i : Fin D.rank) :
    (⨆ k, H k) ≤ normalizer (posUnipotentExcept D i : Set K) := by
  refine iSup_le fun k => le_normalizer_iSup₂ fun x hx γ hγ y hy => ?_
  exact rootGroup_le_posUnipotentExcept hγ
    (hct.H_conj_mem k γ hγ.1.1 x hx y hy)

theorem borel_le_normalizer_posUnipotentExcept (hext : SteinbergExtras D n H)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (i : Fin D.rank) :
    borel D H ≤ normalizer (posUnipotentExcept D i : Set K) := by
  refine sup_le (torus_le_normalizer_posUnipotentExcept hct i) ?_
  rw [posUnipotent_eq_sup hext i]
  exact sup_le Subgroup.le_normalizer (rootGroup_single_le_normalizer hext i)

theorem n_mem_normalizer_posUnipotentExcept [Finite K]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (i : Fin D.rank) :
    n i ∈ normalizer (posUnipotentExcept D i : Set K) := by
  have hle : (posUnipotentExcept D i).map (MulAut.conj (n i)).toMonoidHom ≤
      posUnipotentExcept D i := by
    rintro _ ⟨u, hu, rfl⟩
    exact conj_n_mem_posUnipotentExcept hct i hu
  have hcard : Nat.card (posUnipotentExcept D i) ≤
      Nat.card ((posUnipotentExcept D i).map (MulAut.conj (n i)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (n i)).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem hasParGen_of_datum [Finite K]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBN : IsSplitBNPair 2 (borel D H) (weylN n H))
    (hU : IsPGroup 2 (posUnipotent D)) (hrank : 2 ≤ D.rank) : HasParGen K := by
  haveI : Nonempty (Fin D.rank) := ⟨⟨0, by omega⟩⟩
  refine hasParGen_of_bn_family (B := borel D H) (hBN.exists_sylow_normalizer Nat.prime_two) n
    (fun i => posUnipotentExcept D i) ?_ (fun i => hU.to_le (posUnipotentExcept_le_posUnipotent i))
    (posUnipotentExcept_ne_bot hext hrank)
    (fun i => (posUnipotentExcept_le_posUnipotent i).trans posUnipotent_le_borel)
    (borel_le_normalizer_posUnipotentExcept hext hct)
    (n_mem_normalizer_posUnipotentExcept hct)
  have hle : weylN n H ≤ borel D H ⊔ ⨆ i, zpowers (n i) := by
    refine sup_le (iSup_le_borel.trans le_sup_left) ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i (Subgroup.mem_zpowers (n i)))
  rw [eq_top_iff, ← hBN.gen]
  exact sup_le le_sup_left hle

theorem center_odd_of_datum [Finite K]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBN : IsSplitBNPair 2 (borel D H) (weylN n H))
    (hT : ¬ 2 ∣ Nat.card (⨆ i, H i : Subgroup K)) : ∀ x ∈ center K, Odd (orderOf x) := by
  intro x hx
  have hxT : x ∈ (⨆ i, H i : Subgroup K) := by
    rw [← borel_inf_weylN hct hext]
    exact burnsideI2BN_center_le hBN hx
  have hdvd : orderOf (⟨x, hxT⟩ : (⨆ i, H i : Subgroup K)) ∣
      Nat.card (⨆ i, H i : Subgroup K) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  exact hT ((even_iff_two_dvd.mp hne).trans hdvd)

theorem parGen_of_datum_pkg [Finite K]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBE : BruhatExtras D H)
    (hU : IsPGroup 2 (posUnipotent D)) (hT : ¬ 2 ∣ Nat.card (⨆ i, H i : Subgroup K))
    (hrank : 2 ≤ D.rank) : HasParGen K ∧ ∀ x ∈ center K, Odd (orderOf x) := by
  have hBN := burnsideI2BN_of_datum Nat.prime_two hct hext hBE hU hT
  exact ⟨hasParGen_of_datum hct hext hBN hU hrank, center_odd_of_datum hct hext hBN hT⟩

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
