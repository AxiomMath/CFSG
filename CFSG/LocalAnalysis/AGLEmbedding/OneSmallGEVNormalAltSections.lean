module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltConfig
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem exists_barM_hom (hc : D1SmallAltConfig p P M H R Rbar K z) :
    ∃ θ : ↥(barM M (H ⊓ M)) →* H ⧸ primeComplementCore (G := H) p,
      p.Coprime (Nat.card θ.ker) ∧ ∀ (m : ↥M) (hmH : (m : G) ∈ H)
        (hm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ barM M (H ⊓ M)),
        θ ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hm⟩ =
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨m, hmH⟩ := by
  set A := H ⊓ M
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set α : ↥A →* ↥(barM M A) := (mkM.comp (Subgroup.inclusion inf_le_right)).codRestrict
    (barM M A) fun a => ⟨Subgroup.inclusion inf_le_right a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  set β : ↥A →* H ⧸ primeComplementCore (G := H) p := π.comp (Subgroup.inclusion inf_le_left)
  have hsurj : Function.Surjective α := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  have hker : α.ker ≤ β.ker := by
    intro a ha
    have h1 : mkM (Subgroup.inclusion inf_le_right a) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).mp ha)
    have h2 := hc.twoCore_le_primeCore (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
    exact (MonoidHom.mem_ker).mpr ((mk'_primeComplementCore_eq_one_iff p _).mpr h2)
  set θ := (α.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj))
    ⟨β, hker⟩
  have hθ : ∀ a : ↥A, θ (α a) = β a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  refine ⟨θ, ?_, fun m hmH hm => ?_⟩
  ·
    have hle : θ.ker ≤ β.ker.map α := by
      intro x hx
      obtain ⟨a, rfl⟩ := hsurj x
      exact ⟨a, (MonoidHom.mem_ker).mpr (by rw [← hθ]; exact (MonoidHom.mem_ker).mp hx), rfl⟩
    have hβ : β.ker.map A.subtype ≤ GLBPrimeCore p H := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mk'_primeComplementCore_eq_one_iff p _).mp ((MonoidHom.mem_ker).mp ha)
    have h1 : Nat.card β.ker ∣ Nat.card (GLBPrimeCore p H) := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective]
      exact Subgroup.card_dvd_of_le hβ
    exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le hle).trans
      ((Subgroup.card_map_dvd _ _).trans h1)) (glbPrimeCore_coprime p H)
  · have hmA : (m : G) ∈ A := ⟨hmH, m.2⟩
    have h1 : α ⟨m, hmA⟩ = ⟨mkM m, hm⟩ := rfl
    rw [← h1, hθ]
    rfl

theorem perfectSectionsAltSq_of_le (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hΓ : KFactAltTwoPGamma) {J : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hJ : J ≤ barM M (H ⊓ M)) : PerfectSectionsAltSq p J := by
  intro V hVJ hVp
  set B := barM M (H ⊓ M)
  obtain ⟨θ, hθk, hθ⟩ := hc.exists_barM_hom
  have hVB : V ≤ B := hVJ.trans hJ
  set V' := V.subgroupOf B
  set U := V'.map θ
  have hV'p : ⁅V', V'⁆ = V' := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVB, hVp]
  have hUp : ⁅U, U⁆ = U := by rw [← Subgroup.map_commutator, hV'p]
  have hUX : U ≤ d1X0 p M H := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨m, hm, hmx⟩ := x.2
    have hmA := Subgroup.mem_subgroupOf.mp hm
    have hx : x = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmx ▸ x.2⟩ := Subtype.ext hmx.symm
    rw [hx, hθ m hmA.1]
    exact ⟨⟨m, hmA.1⟩, Subgroup.mem_subgroupOf.mpr hmA, rfl⟩
  obtain ⟨f₁, hf₁⟩ := hc.exists_injective_of_perfect hΓ hUX hUp
  set e : ↥V ≃* ↥V' := (Subgroup.subgroupOfEquivOfLe hVB).symm
  set F := f₁.comp ((θ.subgroupMap V').comp e.toMonoidHom)
  refine ⟨F.ker.map V.subtype, Subgroup.map_subtype_le _, ?_, ?_, F, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective V.subtype_injective]
    infer_instance
  · rw [Subgroup.card_map_of_injective V.subtype_injective]
    have hle : F.ker.map (V'.subtype.comp e.toMonoidHom) ≤ θ.ker := by
      rintro _ ⟨v, hv, rfl⟩
      have h1 : f₁ (θ.subgroupMap V' (e v)) = 1 := hv
      have h2 : θ.subgroupMap V' (e v) = 1 := hf₁ (h1.trans (map_one f₁).symm)
      exact (MonoidHom.mem_ker).mpr (congrArg Subtype.val h2)
    have hinj : Function.Injective (V'.subtype.comp e.toMonoidHom) :=
      V'.subtype_injective.comp e.injective
    rw [← Subgroup.card_map_of_injective hinj]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) hθk
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective V.subtype_injective]

theorem perfectSectionsAltSq_block (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hΓ : KFactAltTwoPGamma) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    PerfectSectionsAltSq p (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) := by
  refine hc.perfectSectionsAltSq_of_le hΓ (barM_mono ?_)
  rw [hc.phase.normalizer_twoCore_H]
  exact inf_le_inf_left H hL.le

end D1SmallAltConfig

end CFSG.AGLEmbedding
