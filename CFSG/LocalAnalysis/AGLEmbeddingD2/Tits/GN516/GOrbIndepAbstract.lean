module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbIndepGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Indep

open scoped commutatorElement
open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.GN516.Perf

theorem indep_abstract {S ι : Type*} [Group S] [Finite S] [Finite ι]
    (𝒜 : Subgroup (MulAut S)) (σ : ↥𝒜 →* Equiv.Perm ι) (i : ι) (J : Set ι)
    (hJ : J = Set.range fun a : ↥𝒜 => σ a i) (L Nn : ι → Subgroup S) (V T Wg : Subgroup S)
    (hW : Wg = V ⊔ ⨆ j ∈ J, L j) (hVT : V ≤ T) (hT2 : IsPGroup 2 ↥T)
    (hTa : ∀ a : ↥𝒜, T.map a.1.toMonoidHom = T)
    (hWV : Wg ≤ Subgroup.normalizer (V : Set S))
    (hWa : ∀ a : ↥𝒜, Wg.map a.1.toMonoidHom = Wg)
    (hcomm : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → L j ≤ Subgroup.centralizer (L k : Set S))
    (hNa : ∀ (a : ↥𝒜) (j : ι), (Nn j).map a.1.toMonoidHom = Nn (σ a j))
    (hLN : ∀ j, L j ≤ Nn j) (hP : ∀ j ∈ J, perfRad (Nn j) ≤ V ⊔ L j)
    (hL2 : ∀ j ∈ J, ∀ X : Subgroup S, L j ≤ X → L j ≤ pElementSubgroup 2 X)
    (hdich : (∀ j ∈ J, Group.IsSolvable ↥(L j)) ∨ ∀ j ∈ J, ⁅L j, L j⁆ = L j) :
    Group.IsSolvable ↥Wg ∨
    ∃ C : Subgroup S, C ≤ pElementSubgroup 2 C ∧ C ≤ Wg ∧ Wg ≤ Subgroup.normalizer (C : Set S) ∧
      Wg ≤ ⨆ a : ↥𝒜, C.map a.1.toMonoidHom ∧
      ∀ a : ↥𝒜, σ a i ≠ i → ⁅C, C.map a.1.toMonoidHom⁆ ≤ pCoreOf 2 Wg := by
  have hi : i ∈ J := hJ ▸ ⟨1, by simp⟩
  have hσJ : ∀ a : ↥𝒜, σ a i ∈ J := fun a => hJ ▸ ⟨a, rfl⟩
  have hLW : ∀ j ∈ J, L j ≤ Wg := fun j hj => hW ▸ le_sup_of_le_right
    (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => L j) j hj le_rfl)
  have hVW : V ≤ Wg := hW ▸ le_sup_left
  rcases hdich with hsolv | hperf
  · left
    have hV : Group.IsSolvable ↥V := by
      have := (hT2.to_le hVT).isNilpotent
      infer_instance
    have hfin : J.Finite := Set.toFinite J
    have key := isSolvable_sup_iSup hV (L := L) hfin.toFinset
      (fun j hj => hsolv j (hfin.mem_toFinset.1 hj))
      (fun j hj => (hLW j (hfin.mem_toFinset.1 hj)).trans hWV)
      (fun j hj k hk hjk => hcomm j (hfin.mem_toFinset.1 hj) k (hfin.mem_toFinset.1 hk) hjk)
    have e : (⨆ j ∈ hfin.toFinset, L j) = ⨆ j ∈ J, L j := by simp
    rw [e] at key
    rw [hW]
    exact key
  · right
    have hQ : ∀ j ∈ J, L j ≤ perfRad (Nn j) := fun j hj => le_perfRad (hLN j) (hperf j hj)
    have hmap_mul : ∀ (a b : ↥𝒜) (X : Subgroup S),
        (X.map b.1.toMonoidHom).map a.1.toMonoidHom = X.map (a * b).1.toMonoidHom := by
      intro a b X
      rw [Subgroup.map_map]
      rfl
    have hmap_one : ∀ X : Subgroup S, X.map (1 : ↥𝒜).1.toMonoidHom = X := by
      intro X
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    set Vt : Subgroup S := ⨆ a : ↥𝒜, V.map a.1.toMonoidHom with hVt
    have hVVt : V ≤ Vt := fun x hx => Subgroup.mem_iSup_of_mem (1 : ↥𝒜) ⟨x, hx, rfl⟩
    have hVta : ∀ a : ↥𝒜, Vt.map a.1.toMonoidHom = Vt := by
      intro a
      apply le_antisymm
      · rw [hVt, Subgroup.map_iSup]
        refine iSup_le fun b => ?_
        rw [hmap_mul]
        exact le_iSup (fun c : ↥𝒜 => V.map c.1.toMonoidHom) (a * b)
      · refine iSup_le fun b => ?_
        have : V.map b.1.toMonoidHom = (V.map (a⁻¹ * b).1.toMonoidHom).map a.1.toMonoidHom := by
          rw [hmap_mul]
          simp
        rw [this]
        exact Subgroup.map_mono (le_iSup (fun c : ↥𝒜 => V.map c.1.toMonoidHom) (a⁻¹ * b))
    have hVtT : Vt ≤ T := iSup_le fun a => (Subgroup.map_mono hVT).trans (hTa a).le
    have hVt2 : IsPGroup 2 ↥Vt := hT2.to_le hVtT
    have hVtW : Vt ≤ Wg := iSup_le fun a => (Subgroup.map_mono hVW).trans (hWa a).le
    have hWVt : Wg ≤ Subgroup.normalizer (Vt : Set S) := by
      refine CFSG.LieType.Steinberg.le_normalizer_iSup fun a => ?_
      calc Wg = Wg.map a.1.toMonoidHom := (hWa a).symm
        _ ≤ (Subgroup.normalizer (V : Set S)).map a.1.toMonoidHom := Subgroup.map_mono hWV
        _ ≤ Subgroup.normalizer ((V.map a.1.toMonoidHom : Subgroup S) : Set S) :=
          Subgroup.le_normalizer_map _
    have hKey1 : ∀ a : ↥𝒜, (L i).map a.1.toMonoidHom ≤ V ⊔ L (σ a i) := by
      intro a
      calc (L i).map a.1.toMonoidHom ≤ (perfRad (Nn i)).map a.1.toMonoidHom :=
            Subgroup.map_mono (hQ i hi)
        _ = perfRad ((Nn i).map a.1.toMonoidHom) := map_perfRad a.1 (Nn i)
        _ = perfRad (Nn (σ a i)) := by rw [hNa a i]
        _ ≤ V ⊔ L (σ a i) := hP _ (hσJ a)
    have hKey2 : ∀ a : ↥𝒜, L (σ a i) ≤ (V ⊔ L i).map a.1.toMonoidHom := by
      intro a
      calc L (σ a i) ≤ perfRad (Nn (σ a i)) := hQ _ (hσJ a)
        _ = perfRad ((Nn i).map a.1.toMonoidHom) := by rw [hNa a i]
        _ = (perfRad (Nn i)).map a.1.toMonoidHom := (map_perfRad a.1 (Nn i)).symm
        _ ≤ (V ⊔ L i).map a.1.toMonoidHom := Subgroup.map_mono (hP i hi)
    refine ⟨Vt ⊔ L i, ?_, ?_, ?_, ?_, ?_⟩
    · exact sup_le (le_pElementSubgroup_two_of_isPGroup le_sup_left hVt2)
        (hL2 i hi _ le_sup_right)
    · exact sup_le hVtW (hLW i hi)
    · refine hW.le.trans (sup_le ?_ (iSup₂_le fun j hj => ?_))
      · exact hVVt.trans (le_sup_left.trans Subgroup.le_normalizer)
      · by_cases hji : j = i
        · subst hji
          exact le_sup_right.trans Subgroup.le_normalizer
        · exact CFSG.LieType.Steinberg.le_normalizer_sup ((hLW j hj).trans hWVt)
            (le_normalizer_of_le_centralizer (hcomm j hj i hi hji))
    · refine hW.le.trans (sup_le ?_ (iSup₂_le fun j hj => ?_))
      · refine hVVt.trans ?_
        calc Vt = Vt.map (1 : ↥𝒜).1.toMonoidHom := (hmap_one Vt).symm
          _ ≤ (Vt ⊔ L i).map (1 : ↥𝒜).1.toMonoidHom := Subgroup.map_mono le_sup_left
          _ ≤ _ := le_iSup (fun a : ↥𝒜 => (Vt ⊔ L i).map a.1.toMonoidHom) 1
      · obtain ⟨a, rfl⟩ : ∃ a : ↥𝒜, σ a i = j := by
          rw [hJ] at hj
          exact hj
        calc L (σ a i) ≤ (V ⊔ L i).map a.1.toMonoidHom := hKey2 a
          _ ≤ (Vt ⊔ L i).map a.1.toMonoidHom :=
            Subgroup.map_mono (sup_le_sup_right hVVt _)
          _ ≤ _ := le_iSup (fun a : ↥𝒜 => (Vt ⊔ L i).map a.1.toMonoidHom) a
    · intro a hne
      have hC : (Vt ⊔ L i).map a.1.toMonoidHom ≤ Vt ⊔ L (σ a i) := by
        rw [Subgroup.map_sup, hVta a]
        exact sup_le le_sup_left ((hKey1 a).trans (sup_le_sup_right hVVt _))
      calc ⁅Vt ⊔ L i, (Vt ⊔ L i).map a.1.toMonoidHom⁆ ≤ ⁅Vt ⊔ L i, Vt ⊔ L (σ a i)⁆ :=
            Subgroup.commutator_mono le_rfl hC
        _ ≤ Vt := commutator_sup_sup_le ((hLW i hi).trans hWVt) ((hLW _ (hσJ a)).trans hWVt)
            (hcomm i hi _ (hσJ a) (Ne.symm hne))
        _ ≤ pCoreOf 2 Wg := le_pCoreOf_two hVtW hWVt hVt2

end CFSG.AGLEmbeddingD2.Tits.GN516.Indep
