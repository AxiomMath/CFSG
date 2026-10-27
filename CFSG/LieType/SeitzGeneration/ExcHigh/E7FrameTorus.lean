module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Two

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExcTwo


@[expose] def frameM : Fin 7 → Fin Tag.E7.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 1, 0], ![-1, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, -1, 2], ![0, 0, 0, -1, 2, -1, 0], ![-1, 0, 2, -1, 0, 0, 0],
    ![0, 2, 0, -1, 0, 0, 0]]

@[expose] def frameN : Fin Tag.E7.rank → Fin 7 → ℤ :=
  ![![2, 0, 0, 0, 0, 0, 0], ![2, 1, 1, 0, 0, 0, 1], ![3, 1, 1, 0, 0, 1, 0],
    ![4, 2, 2, 0, 0, 0, 0], ![3, 2, 1, 0, 1, 0, 0], ![2, 2, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0]]

theorem iform_frame_single : ∀ (i : Fin 7) (k : Fin Tag.E7.rank),
    iform (frameE7Root i) (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = frameM i k := by
  decide +kernel

theorem frameN_mul_frameM : ∀ j k : Fin Tag.E7.rank,
    ∑ i, frameN j i * frameM i k = if j = k then 2 else 0 := by
  decide +kernel

theorem iform_self_of_isRoot_E7' {β : Fin Tag.E7.rank → ℤ} (hβ : IsRoot .E7 β) :
    iform β β = 2 := by
  have h : ∀ σ ∈ rootFinset .E7, iform σ σ = 2 := by decide +kernel
  exact h β (mem_rootFinset.2 hβ)

theorem zpow_finsetSum_frame {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

section Torus

variable {L : Type} [Field L]

theorem rootTorusSL2_eq_rootDiagUnit_E7 {β : Fin Tag.E7.rank → ℤ} (hβ : IsRoot Tag.E7 β)
    (c : Lˣ) :
    rootTorusSL2 Tag.E7 L β c =
      rootDiagUnit Tag.E7 (fun k => c ^ iform β (Pi.single k 1 : Fin Tag.E7.rank → ℤ)) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport Tag.E7 L hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single Tag.E7 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit Tag.E7 a : ModGL Tag.E7 L) : Module.End L (RootModule Tag.E7 L))
      (rootVec Tag.E7 L (Pi.single i 1))) = ((a i : Lˣ) : L) • rootVec Tag.E7 L (Pi.single i 1) := by
    change rootDiag a (rootVec Tag.E7 L (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank Tag.E7) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single Tag.E7 i), hs]
  rw [h2] at h1
  have hne : rootVec Tag.E7 L (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single Tag.E7 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective L hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_of_isRoot_E7' hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3

@[expose] def frameSpan (L : Type) [Field L] : Subgroup (ModGL Tag.E7 L) :=
  ⨆ i : Fin 7, (rootSL2 Tag.E7 L (frameE7Root i)).range

theorem rootSL2_mem_frameSpan (i : Fin 7) (A : SL2 L) :
    rootSL2 Tag.E7 L (frameE7Root i) A ∈ frameSpan L :=
  le_iSup (fun j : Fin 7 => (rootSL2 Tag.E7 L (frameE7Root j)).range) i ⟨A, rfl⟩

@[expose] def rootDiagHomE7 (L : Type) [Field L] : (Fin Tag.E7.rank → Lˣ) →* ModGL Tag.E7 L where
  toFun := rootDiagUnit Tag.E7
  map_one' := rootDiagUnit_one
  map_mul' a b := rootDiagUnit_mul a b

theorem torusGroup_le_frameSpan (hsq : ∀ x : L, ∃ z : L, z ^ 2 = x) :
    torusGroup Tag.E7 L ≤ frameSpan L := by
  intro t ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hs : ∀ k : Fin Tag.E7.rank, ∃ s : Lˣ, s ^ 2 = b k := by
    intro k
    obtain ⟨z, hz⟩ := hsq (b k : L)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (b k).ne_zero (by rw [← hz]; ring)
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  choose s hs using hs
  let c : Fin 7 → Lˣ := fun i => ∏ j : Fin Tag.E7.rank, s j ^ frameN j i
  let v : Fin 7 → Fin Tag.E7.rank → Lˣ := fun i k => c i ^ frameM i k
  have hv : ∀ i, rootDiagHomE7 L (v i) ∈ frameSpan L := by
    intro i
    have h := rootTorusSL2_eq_rootDiagUnit_E7 (L := L) (e7Frame_isRoot i) (c i)
    have hv' : rootDiagHomE7 L (v i) = rootTorusSL2 Tag.E7 L (frameE7Root i) (c i) := by
      rw [h]
      show rootDiagUnit Tag.E7 _ = rootDiagUnit Tag.E7 _
      congr 1
      funext k
      show c i ^ frameM i k = _
      rw [iform_frame_single]
    rw [hv']
    exact rootSL2_mem_frameSpan i (HSL (c i))
  have hb : b = ∏ i : Fin 7, v i := by
    funext k
    rw [Finset.prod_apply]
    have hexp : ∀ i : Fin 7, v i k = ∏ j : Fin Tag.E7.rank, s j ^ (frameN j i * frameM i k) := by
      intro i
      simp only [v, c, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_congr rfl fun i _ => hexp i, Finset.prod_comm]
    have hcol : ∀ j : Fin Tag.E7.rank, ∏ i : Fin 7, s j ^ (frameN j i * frameM i k) =
        s j ^ (if j = k then (2 : ℤ) else 0) := by
      intro j
      rw [← frameN_mul_frameM j k, zpow_finsetSum_frame]
    rw [Finset.prod_congr rfl fun j _ => hcol j]
    rw [Finset.prod_eq_single k (fun j _ hj => by rw [if_neg hj, zpow_zero])
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
    rw [zpow_two, ← pow_two, hs k]
  have hmem : b ∈ (frameSpan L).comap (rootDiagHomE7 L) := by
    rw [hb]
    exact Subgroup.prod_mem _ fun i _ => hv i
  exact hmem

end Torus

end CFSG.LieType.SeitzGeneration.ExcHigh
