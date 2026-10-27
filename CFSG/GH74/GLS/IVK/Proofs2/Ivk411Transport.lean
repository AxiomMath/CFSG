module

import CFSG.GH74.GLS.Stage2.Final.ModelIVK410
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFId

public section

namespace CFSG.GH74.Ivk411

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT (Data411)
open scoped commutatorElement

theorem Fstar_map_gen {K G : Type} [Group K] [Group G] (Φ : K ≃* G) (H : Subgroup K)
    (H' : Subgroup G) (hH : H.map Φ.toMonoidHom = H') :
    (generalizedFitting ↥H').map H'.subtype =
      ((generalizedFitting ↥H).map H.subtype).map Φ.toMonoidHom := by
  subst hH
  exact CFSG.QuasithinUnique.Setup.Layer.Actor.map_ambient (fun K _ => generalizedFitting K)
    (fun e => CFSG.QuasithinUnique.Setup.Layer.Actor.generalizedFitting_map e) Φ H

theorem Z_map {K G : Type} [Group K] [Group G] (Φ : K ≃* G) (x : K) :
    (Subgroup.centralizer ({x} : Set K) ⊓
        Subgroup.centralizer ((IVK.Ez x : Subgroup K) : Set K)).map Φ.toMonoidHom =
      Subgroup.centralizer ({Φ x} : Set G) ⊓
        Subgroup.centralizer ((IVK.Ez (Φ x) : Subgroup G) : Set G) := by
  rw [← ModelBlock.Ez_map_equiv Φ x]
  ext y
  constructor
  · rintro ⟨y', ⟨hy1, hy2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 := Subgroup.mem_centralizer_singleton_iff.1 hy1
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      show Φ y' * Φ x = Φ x * Φ y'
      rw [← map_mul, ← map_mul, h1]
    · show Φ y' ∈ Subgroup.centralizer (((IVK.Ez x).map Φ.toMonoidHom : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨e, he, rfl⟩
      show Φ e * Φ y' = Φ y' * Φ e
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hy2 e he]
  · rintro ⟨hy1, hy2⟩
    obtain ⟨y', rfl⟩ := Φ.surjective y
    refine ⟨y', ⟨?_, ?_⟩, rfl⟩
    · have h1 := Subgroup.mem_centralizer_singleton_iff.1 hy1
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      apply Φ.injective
      rw [map_mul, map_mul]
      exact h1
    · show y' ∈ Subgroup.centralizer ((IVK.Ez x : Subgroup K) : Set K)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      apply Φ.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.1 hy2 (Φ e) ⟨e, he, rfl⟩

theorem data411_map_equiv {K G : Type} [Group K] [Group G] (Φ : K ≃* G) {x : K} {q : ℕ}
    {I₁ I₂ : Subgroup K} (h : Data411 x q I₁ I₂) :
    Data411 (Φ x) q (I₁.map Φ.toMonoidHom) (I₂.map Φ.toMonoidHom) := by
  have hEz := ModelBlock.Ez_map_equiv Φ x
  have hC : (Subgroup.centralizer ({x} : Set K)).map Φ.toMonoidHom =
      Subgroup.centralizer ({Φ x} : Set G) := ModelLT.centralizer_map_equiv Φ x
  have hF := Fstar_map_gen Φ (Subgroup.centralizer ({x} : Set K))
    (Subgroup.centralizer ({Φ x} : Set G)) hC
  have hZ := Z_map Φ x
  refine ⟨?_, ModelLUT.hasSL2Model_of_equiv (ModelLUT.subEquiv Φ I₁) h.sl₁,
    ModelLUT.hasSL2Model_of_equiv (ModelLUT.subEquiv Φ I₂) h.sl₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hEz, h.sup, Subgroup.map_sup]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.comm a ha b hb]
  · rw [← Subgroup.map_inf_eq _ _ Φ.toMonoidHom Φ.injective, h.inf, MonoidHom.map_zpowers]
    rfl
  · intro a ha b hb
    rw [← hC] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [hF, ← map_commutatorElement]
    exact Subgroup.mem_map_of_mem _ (h.derived a' ha' b' hb')
  · rw [hF, h.Fs, Subgroup.map_sup, hEz, hZ]
  · intro a ha b hb
    rw [← hZ] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    show Φ a' * Φ b' = Φ b' * Φ a'
    rw [← map_mul, ← map_mul, h.Zabel a' ha' b' hb']

end CFSG.GH74.Ivk411
