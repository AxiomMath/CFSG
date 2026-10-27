module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LCore
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LInst
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LLift

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.Open
open scoped Pointwise

theorem y2l_two_part_10752 : 2 ^ (10752 : ℕ).factorization 2 = 512 := by
  rw [show (10752 : ℕ) = 2 ^ 9 * 21 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21)]
  norm_num

theorem y2l_lift_comp {G H : Type} [Group G] [Group H] (f : G →* H) (x : Fin 5 → G)
    (y : FreeGroup (Fin 5)) : FreeGroup.lift (fun i => f (x i)) y = f (FreeGroup.lift x y) := by
  have h : FreeGroup.lift (fun i => f (x i)) = f.comp (FreeGroup.lift x) :=
    FreeGroup.ext_hom _ _ fun i => by simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply]
  rw [h, MonoidHom.comp_apply]

theorem y2l_map_conj {X : Type} [Group X] (M : Subgroup X) [hM : M.Normal] (g : X) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr fun m hm => ?_) fun m hm => ?_
  · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hM.conj_mem m hm g
  · refine ⟨g⁻¹ * m * g, by simpa using hM.conj_mem m hm g⁻¹, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem y2l_sylow_transport {X : Type} [Group X] [Finite X]
    (hX : 2 ^ (Nat.card X).factorization 2 = 512) {M : Subgroup X} [M.Normal] {e : Bool}
    {x : Fin 5 → X} (hrel : ∀ y ∈ rels26 2 e, FreeGroup.lift x y = 1)
    (h7 : ∀ y ∈ y2l_ws7 2, FreeGroup.lift x (FreeGroup.mk y) ≠ 1)
    (hM : closure ({x 0, x 1, x 2} : Set X) = M) (P : Sylow 2 X) :
    ∃ u v w r s : ↥P, IsPres26 2 e ↥P u v w r s ∧
      closure ({(u : X), (v : X), (w : X)} : Set X) = M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 X) :=
    Finite.of_injective (fun T : Sylow 2 X => (T : Set X)) SetLike.coe_injective
  have hx : (![x 0, x 1, x 2, x 3, x 4] : Fin 5 → X) = x := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨-, hcard⟩ := y2l_isPres26_two (e := e) (u := x 0) (v := x 1) (w := x 2) (r := x 3)
    (s := x 4) (by rw [hx]; exact hrel) (by rw [hx]; exact h7)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X
    (Sylow.ofCard (closure ({x 0, x 1, x 2, x 3, x 4} : Set X)) (by rw [hcard, hX])) P
  set f : X →* X := (MulAut.conj g).toMonoidHom with hf
  have hx' : (![f (x 0), f (x 1), f (x 2), f (x 3), f (x 4)] : Fin 5 → X) = fun i => f (x i) := by
    funext i
    fin_cases i <;> rfl
  have hrel' : ∀ y ∈ rels26 2 e, FreeGroup.lift (fun i => f (x i)) y = 1 := fun y hy => by
    rw [y2l_lift_comp, hrel y hy, map_one]
  have h7' : ∀ y ∈ y2l_ws7 2, FreeGroup.lift (fun i => f (x i)) (FreeGroup.mk y) ≠ 1 :=
    fun y hy h => h7 y hy (by
      rwa [y2l_lift_comp, map_eq_one_iff f fun a b hab => (MulAut.conj g).injective hab] at h)
  obtain ⟨hP, hcard'⟩ := y2l_isPres26_two (e := e) (u := f (x 0)) (v := f (x 1)) (w := f (x 2))
    (r := f (x 3)) (s := f (x 4)) (by rw [hx']; exact hrel') (by rw [hx']; exact h7')
  have hle : closure ({f (x 0), f (x 1), f (x 2), f (x 3), f (x 4)} : Set X) ≤ P := by
    have hmem : ∀ i, f (x i) ∈ (P : Subgroup X) := fun i => by
      rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
      exact Subgroup.smul_mem_pointwise_smul (x i) (MulAut.conj g) _
        (subset_closure (by fin_cases i <;> simp))
    rw [closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact hmem _
  have heq : closure ({f (x 0), f (x 1), f (x 2), f (x 3), f (x 4)} : Set X) = P :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcard']
      exact ((Sylow.card_eq_multiplicity P).trans hX).le)
  have hM' : closure ({f (x 0), f (x 1), f (x 2)} : Set X) = M := by
    rw [show ({f (x 0), f (x 1), f (x 2)} : Set X) = f '' {x 0, x 1, x 2} by
      simp only [Set.image_insert_eq, Set.image_singleton], ← MonoidHom.map_closure, hM, hf]
    exact y2l_map_conj M g
  have key : ∀ K : Subgroup X,
      closure ({f (x 0), f (x 1), f (x 2), f (x 3), f (x 4)} : Set X) = K →
      ∃ u v w r s : ↥K, IsPres26 2 e ↥K u v w r s ∧
        closure ({(u : X), (v : X), (w : X)} : Set X) = M := by
    rintro K rfl
    exact ⟨_, _, _, _, _, hP, hM'⟩
  exact key P heq

theorem lemma26Pres2_holds :
    Lemma26Pres2 := by
  intro X _ _ hX P
  obtain ⟨⟨eM⟩, ⟨hN, ⟨eQ⟩⟩, hC⟩ := hX
  haveI : (pCoreOf 2 (⊤ : Subgroup X)).Normal := ⟨fun m hm g => Subgroup.mem_subgroupOf.mp
    (hN.conj_mem ⟨m, mem_top m⟩ (Subgroup.mem_subgroupOf.mpr hm) ⟨g, mem_top g⟩)⟩
  have hidx : (pCoreOf 2 (⊤ : Subgroup X)).index = 168 := by
    rw [← Subgroup.relIndex_top_right]
    exact (Nat.card_congr eQ.toEquiv).trans CFSG.ComponentClassification.GHarris.card_GL32_gh
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at eM
  let τ : ↥(pCoreOf 2 (⊤ : Subgroup X)) ≃* Multiplicative (Fin 3 → ZMod 4) :=
    eM.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 4)).symm
  let ψ : X →* GL (Fin 3) (ZMod 2) := eQ.toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).toMonoidHom)
  have hψ : Function.Surjective ψ := fun q => by
    obtain ⟨y, rfl⟩ := eQ.surjective q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(z : X), rfl⟩
  have hker : ψ.ker = pCoreOf 2 (⊤ : Subgroup X) := by
    ext x
    rw [MonoidHom.mem_ker]
    change eQ (QuotientGroup.mk (Subgroup.topEquiv.symm x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  obtain ⟨τ', xa, xb, ha, hb⟩ := y2l_exists_lift τ hC ψ hψ hker hidx
  obtain ⟨e, r, s, hR⟩ := y2l_exists_rels τ' hC ha hb
  have hcard : Nat.card X = 10752 := by
    rw [← Subgroup.card_mul_index (pCoreOf 2 (⊤ : Subgroup X)), hidx, Nat.card_congr τ'.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  obtain ⟨u, v, w, r', s', hP, hM⟩ := y2l_sylow_transport (by rw [hcard, y2l_two_part_10752])
    (y2l_rels_iff.mpr hR) (y2l_seven τ' r s) (y2l_closure_el τ') P
  exact ⟨e, u, v, w, r', s', hP, hM⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec2
