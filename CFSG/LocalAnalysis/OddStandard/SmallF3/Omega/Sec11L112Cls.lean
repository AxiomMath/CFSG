module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem map_add_one (h : Sec11Perm A M Alt φ) (v : Fin 6 → ZMod 2) :
    φ (v + (fun _ => 1)) = φ v := by
  rw [h.mul, (h.ker _).2 (Or.inr rfl), mul_one]

theorem map_cls (h : Sec11Perm A M Alt φ) (v : Fin 6 → ZMod 2) : φ (sec11Cls v) = φ v := by
  unfold sec11Cls
  split_ifs
  · exact h.map_add_one v
  · rfl

end Sec11Perm

theorem sec11_vec_eq_of_add_eq_zero {x y : Fin 6 → ZMod 2} (h : x + y = 0) : x = y := by
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  funext i
  exact key _ _ (congrFun h i)

theorem sec11_cls_of_card [Finite G] {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))}
    {φ : (Fin 6 → ZMod 2) → G} (hm : Sec11Perm A M Alt φ)
    (hAlt : Alt = alternatingGroup (Fin 6) ∨ Alt = ⊤) {t : G} (ht : t ∈ A) (ht1 : t ≠ 1)
    (hcard : (conjClassIn M t).ncard = 6) : ∃ a : Fin 6, t = φ (Pi.single a 1) := by
  classical
  obtain ⟨v, rfl⟩ := hm.surj t ht
  by_contra hcon
  push Not at hcon
  have hone : φ (fun _ => 1) = 1 := (hm.ker _).2 (Or.inr rfl)
  have hv0 : v ≠ 0 := fun h => ht1 (by rw [h, hm.map_zero])
  have hv1 : v ≠ (fun _ => 1) := fun h => ht1 (by rw [h, hone])
  have hva : ∀ a, v ≠ Pi.single a 1 ∧ v ≠ Pi.single a 1 + (fun _ => 1) := by
    intro a
    refine ⟨fun h => hcon a (by rw [h]), fun h => hcon a ?_⟩
    rw [h, hm.map_add_one]
  have h7 := sec11_orbit_ge7 v hv0 hv1 hva
  set S : Finset (Fin 6 → ZMod 2) := sec11L3.image fun σ => sec11Cls (permVec σ v) with hS
  set F : Finset G := sec11L3.image fun σ => φ (permVec σ v) with hF
  have hFeq : F = S.image φ := by
    rw [hS, hF, Finset.image_image]
    exact Finset.image_congr fun σ _ => (hm.map_cls _).symm
  have hinj : Set.InjOn φ (S : Set (Fin 6 → ZMod 2)) := by
    intro x hx y hy hxy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨σ', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    rcases (hm.eq_iff _ _).mp hxy with h0 | h1
    · exact sec11_vec_eq_of_add_eq_zero h0
    · exfalso
      have := congrFun h1 0
      simp only [Pi.add_apply, sec11_cls_zero] at this
      exact absurd this (by decide)
  have hFcard : 7 ≤ F.card := by
    rw [hFeq, Finset.card_image_of_injOn hinj]
    exact h7
  have hFsub : (↑F : Set G) ⊆ conjClassIn M (φ v) := by
    intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    have hσA : σ ∈ Alt := by
      have hsign : Equiv.Perm.sign σ = 1 := (Finset.mem_filter.mp hσ).2.1
      rcases hAlt with rfl | rfl
      · exact Equiv.Perm.mem_alternatingGroup.mpr hsign
      · exact Subgroup.mem_top _
    obtain ⟨m, hm', hact⟩ := hm.act_surj σ hσA
    exact ⟨m, hm', (hact v).symm⟩
  have hle := Set.ncard_le_ncard hFsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at hle
  omega

end CFSG.OddStandard.SmallF3.Omega
