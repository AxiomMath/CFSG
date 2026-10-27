module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Two

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExcTwo


@[expose] def frameM8 : Fin 8 → Fin Tag.E8.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 0, -1],
    ![-1, 0, 0, 0, 0, 1, 0, -1],
    ![-1, 0, 0, 1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, -1, 2, -1],
    ![0, 0, 0, -1, 2, -1, 0, 0],
    ![-1, 0, 2, -1, 0, 0, 0, 0],
    ![0, 2, 0, -1, 0, 0, 0, 0]]

@[expose] def frameN8 : Fin Tag.E8.rank → Fin 8 → ℤ :=
  ![![2, 2, 0, 0, 0, 0, 0, 0],
    ![3, 2, 1, 1, 0, 0, 0, 1],
    ![4, 3, 1, 1, 0, 0, 1, 0],
    ![6, 4, 2, 2, 0, 0, 0, 0],
    ![5, 3, 2, 1, 0, 1, 0, 0],
    ![4, 2, 2, 0, 0, 0, 0, 0],
    ![3, 1, 1, 0, 1, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0]]

theorem iform_frame_single8 : ∀ (i : Fin 8) (k : Fin Tag.E8.rank),
    iform (frameE8Root i) (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = frameM8 i k := by
  decide +kernel

theorem frameN8_mul_frameM8 : ∀ j k : Fin Tag.E8.rank,
    ∑ i, frameN8 j i * frameM8 i k = if j = k then 2 else 0 := by
  decide +kernel

theorem iform_self_of_isRoot_E8Fr {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot .E8 β) :
    iform β β = 2 := by
  have h : ∀ σ ∈ rootFinset .E8, iform σ σ = 2 := by decide +kernel
  exact h β (mem_rootFinset.2 hβ)

theorem zpow_finsetSum_frame8 {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

section Torus

variable {L : Type} [Field L]

theorem rootTorusSL2_eq_rootDiagUnit_E8 {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β)
    (c : Lˣ) :
    rootTorusSL2 Tag.E8 L β c =
      rootDiagUnit Tag.E8 (fun k => c ^ iform β (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport Tag.E8 L hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single Tag.E8 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit Tag.E8 a : ModGL Tag.E8 L) : Module.End L (RootModule Tag.E8 L))
      (rootVec Tag.E8 L (Pi.single i 1))) =
        ((a i : Lˣ) : L) • rootVec Tag.E8 L (Pi.single i 1) := by
    change rootDiag a (rootVec Tag.E8 L (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank Tag.E8) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single Tag.E8 i), hs]
  rw [h2] at h1
  have hne : rootVec Tag.E8 L (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single Tag.E8 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective L hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_of_isRoot_E8Fr hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3

@[expose] def frameSpan8 (L : Type) [Field L] : Subgroup (ModGL Tag.E8 L) :=
  ⨆ i : Fin 8, (rootSL2 Tag.E8 L (frameE8Root i)).range

theorem rootSL2_mem_frameSpan8 (i : Fin 8) (A : SL2 L) :
    rootSL2 Tag.E8 L (frameE8Root i) A ∈ frameSpan8 L :=
  le_iSup (fun j : Fin 8 => (rootSL2 Tag.E8 L (frameE8Root j)).range) i ⟨A, rfl⟩

@[expose] def rootDiagHomE8 (L : Type) [Field L] : (Fin Tag.E8.rank → Lˣ) →* ModGL Tag.E8 L where
  toFun := rootDiagUnit Tag.E8
  map_one' := rootDiagUnit_one
  map_mul' a b := rootDiagUnit_mul a b

theorem torusGroup_le_frameSpan8 (hsq : ∀ x : L, ∃ z : L, z ^ 2 = x) :
    torusGroup Tag.E8 L ≤ frameSpan8 L := by
  intro t ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hs : ∀ k : Fin Tag.E8.rank, ∃ s : Lˣ, s ^ 2 = b k := by
    intro k
    obtain ⟨z, hz⟩ := hsq (b k : L)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (b k).ne_zero (by rw [← hz]; ring)
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  choose s hs using hs
  let c : Fin 8 → Lˣ := fun i => ∏ j : Fin Tag.E8.rank, s j ^ frameN8 j i
  let v : Fin 8 → Fin Tag.E8.rank → Lˣ := fun i k => c i ^ frameM8 i k
  have hv : ∀ i, rootDiagHomE8 L (v i) ∈ frameSpan8 L := by
    intro i
    have h := rootTorusSL2_eq_rootDiagUnit_E8 (L := L) (e8Frame_isRoot i) (c i)
    have hv' : rootDiagHomE8 L (v i) = rootTorusSL2 Tag.E8 L (frameE8Root i) (c i) := by
      rw [h]
      show rootDiagUnit Tag.E8 _ = rootDiagUnit Tag.E8 _
      congr 1
      funext k
      show c i ^ frameM8 i k = _
      rw [iform_frame_single8]
    rw [hv']
    exact rootSL2_mem_frameSpan8 i (HSL (c i))
  have hb : b = ∏ i : Fin 8, v i := by
    funext k
    rw [Finset.prod_apply]
    have hexp : ∀ i : Fin 8, v i k = ∏ j : Fin Tag.E8.rank, s j ^ (frameN8 j i * frameM8 i k) := by
      intro i
      simp only [v, c, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_congr rfl fun i _ => hexp i, Finset.prod_comm]
    have hcol : ∀ j : Fin Tag.E8.rank, ∏ i : Fin 8, s j ^ (frameN8 j i * frameM8 i k) =
        s j ^ (if j = k then (2 : ℤ) else 0) := by
      intro j
      rw [← frameN8_mul_frameM8 j k, zpow_finsetSum_frame8]
    rw [Finset.prod_congr rfl fun j _ => hcol j]
    rw [Finset.prod_eq_single k (fun j _ hj => by rw [if_neg hj, zpow_zero])
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
    rw [zpow_two, ← pow_two, hs k]
  have hmem : b ∈ (frameSpan8 L).comap (rootDiagHomE8 L) := by
    rw [hb]
    exact Subgroup.prod_mem _ fun i _ => hv i
  exact hmem

end Torus

end CFSG.LieType.SeitzGeneration.ExcHigh
