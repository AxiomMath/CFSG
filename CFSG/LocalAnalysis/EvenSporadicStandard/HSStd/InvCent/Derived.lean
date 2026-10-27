module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Setting

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.EvenSporadicStandard.SolomonRed

variable {G B : Type*} [Group G] [Group B]

theorem bot_prod_map_inr (B₀ : Subgroup B) :
    (⊥ : Subgroup (Multiplicative (ZMod 2))).prod B₀
      = B₀.map (MonoidHom.inr (Multiplicative (ZMod 2)) B) := by
  ext x
  constructor
  · intro hx
    exact ⟨x.2, hx.2, Prod.ext (Subgroup.mem_bot.mp hx.1).symm rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Subgroup.one_mem _, hb⟩

theorem commutator_zmod_two_prod :
    commutator (Multiplicative (ZMod 2) × B)
      = (⊥ : Subgroup (Multiplicative (ZMod 2))).prod (commutator B) := by
  haveI : IsMulCommutative (Multiplicative (ZMod 2)) :=
    IsMulCommutative.of_comm fun a b => mul_comm a b
  change ⁅(⊤ : Subgroup (Multiplicative (ZMod 2) × B)), ⊤⁆
      = (⊥ : Subgroup (Multiplicative (ZMod 2))).prod (commutator B)
  rw [← Subgroup.top_prod_top (G := Multiplicative (ZMod 2)) (N := B),
    Subgroup.commutator_prod_prod,
    ← _root_.commutator_def (Multiplicative (ZMod 2)), ← _root_.commutator_def B,
    commutator_eq_bot]

theorem centralizerDerived_eq_map {t : G}
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) :
    centralizerDerived t = (commutator B).map (embA ζ) := by
  have h1 : (commutator (Multiplicative (ZMod 2) × B)).map ζ.symm.toMonoidHom
      = commutator ↥(centralizer ({t} : Set G)) := by
    change Subgroup.map ζ.symm.toMonoidHom
        ⁅(⊤ : Subgroup (Multiplicative (ZMod 2) × B)), ⊤⁆
      = ⁅(⊤ : Subgroup ↥(centralizer ({t} : Set G))), ⊤⁆
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ζ.symm.toMonoidHom ζ.symm.surjective]
  rw [centralizerDerived, ← h1, Subgroup.map_map, commutator_zmod_two_prod,
    bot_prod_map_inr, Subgroup.map_map]
  refine congrArg (fun f : B →* G => (commutator B).map f) ?_
  ext x
  simp only [MonoidHom.comp_apply, embA]

theorem map_embA_normal_of_central {t : G} (ht : t ∈ Subgroup.center G)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) {B₀ : Subgroup B}
    (hB₀ : B₀.Normal) : (B₀.map (embA ζ)).Normal :=
  ⟨fun b hb d =>
    conj_mem_map_embA ζ hB₀
      (mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp ht d)) hb⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent
