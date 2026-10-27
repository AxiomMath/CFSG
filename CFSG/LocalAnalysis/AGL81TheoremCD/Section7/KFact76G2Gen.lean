module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Roots

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
open scoped commutatorElement

theorem sA_u : sA • gU = gR := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)

theorem sRA_u : (sR * sA) • gU = -gR := by
  rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)

theorem sRA_v : (sR * sA) • gV = gU := by
  rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)

abbrev sRARA : WeylGroup .G2 := sR * sA * sR * sA

theorem sRARA_a : sRARA • gA = -gC := by
  rw [mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem sRARA_b : sRARA • gB = gA := by
  rw [mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem sRARA_c : sRARA • gC = -gB := by
  rw [mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

variable
  {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem Xnb_mem_of (H : Subgroup (ModGL .G2 K)) (hCm : ∀ t : K, X (-gC) t ∈ H)
    (hA : ∀ t : K, X gA t ∈ H) (t : K) : X (-gB) t ∈ H := by
  obtain ⟨εf, hε, h⟩ := commutatorElement_pinnedX_signed (τ := .G2)
    (r := (7, 10, 12, [(1, 1, 11, 1)])) (by decide) sRARA
  have key := @h K _ (-gC) gA (by rw [pos7]; exact sRARA_a) (by rw [pos10]; exact sRARA_b) 1
    (((εf (1, 1, 11, 1) : ℤ) : K) * t)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pos11,
    sRARA_c] at key
  have hm : ⁅X (-gC) 1, X gA (((εf (1, 1, 11, 1) : ℤ) : K) * t)⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hCm 1) (hA _)) (H.inv_mem (hCm 1))) (H.inv_mem (hA _))
  rw [key] at hm
  convert hm using 2
  rcases hε (1, 1, 11, 1) with he | he <;> simp [he]

theorem Xr_mem_of (H : Subgroup (ModGL .G2 K)) (hQ : Qg K ≤ H) (hNA : ∀ t : K, X (-gA) t ∈ H)
    (t : K) : X gR t ∈ H := by
  obtain ⟨εf, hε, h⟩ := commutatorElement_pinnedX_signed (τ := .G2)
    (r := (7, 6, 12, [(1, 1, 8, 1), (1, 2, 9, -1), (1, 3, 10, -1), (2, 3, 11, 1)])) (by decide) sA
  have key := @h K _ (-gA) gU (by rw [pos7]; exact sA_a) (by rw [pos6]; exact sA_r) 1
    (((εf (1, 1, 8, 1) : ℤ) : K) * t)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pos8, pos9,
    pos10, pos11, sA_u, sA_v, sA_b, sA_c] at key
  have hm : ⁅X (-gA) 1, X gU (((εf (1, 1, 8, 1) : ℤ) : K) * t)⁆ ∈ H := by
    rw [commutatorElement_def]
    have hu := hQ (X_mem_Qg (K := K) isQRoot_u (((εf (1, 1, 8, 1) : ℤ) : K) * t))
    exact H.mul_mem (H.mul_mem (H.mul_mem (hNA 1) hu) (H.inv_mem (hNA 1))) (H.inv_mem hu)
  rw [key] at hm
  have hm' := (H.mul_mem_cancel_right (H.mul_mem (hQ (X_mem_Qg isQRoot_v _))
    (H.mul_mem (hQ (X_mem_Qg isQRoot_c _)) (hQ (X_mem_Qg isQRoot_b _))))).1 hm
  convert hm' using 2
  rcases hε (1, 1, 8, 1) with he | he <;> simp [he]

theorem Xnr_mem_of (H : Subgroup (ModGL .G2 K)) (hQ : Qg K ≤ H) (hNB : ∀ t : K, X (-gB) t ∈ H)
    (t : K) : X (-gR) t ∈ H := by
  obtain ⟨εf, hε, h⟩ := commutatorElement_pinnedX_signed (τ := .G2)
    (r := (7, 6, 12, [(1, 1, 8, 1), (1, 2, 9, -1), (1, 3, 10, -1), (2, 3, 11, 1)])) (by decide)
    (sR * sA)
  have key := @h K _ (-gB) gV (by rw [pos7]; exact sRA_a) (by rw [pos6]; exact sRA_r) 1
    (((εf (1, 1, 8, 1) : ℤ) : K) * t)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pos8, pos9,
    pos10, pos11, sRA_u, sRA_v, sRA_b, sRA_c] at key
  have hm : ⁅X (-gB) 1, X gV (((εf (1, 1, 8, 1) : ℤ) : K) * t)⁆ ∈ H := by
    rw [commutatorElement_def]
    have hv := hQ (X_mem_Qg (K := K) isQRoot_v (((εf (1, 1, 8, 1) : ℤ) : K) * t))
    exact H.mul_mem (H.mul_mem (H.mul_mem (hNB 1) hv) (H.inv_mem (hNB 1))) (H.inv_mem hv)
  rw [key] at hm
  have hm' := (H.mul_mem_cancel_right (H.mul_mem (hQ (X_mem_Qg isQRoot_u _))
    (H.mul_mem (hQ (X_mem_Qg isQRoot_c _)) (hQ (X_mem_Qg isQRoot_a _))))).1 hm
  convert hm' using 2
  rcases hε (1, 1, 8, 1) with he | he <;> simp [he]

theorem adjointGroup_le_of_rootGroups (H : Subgroup (ModGL .G2 K)) (hA : ∀ t : K, X gA t ∈ H)
    (hNA : ∀ t : K, X (-gA) t ∈ H) (hR : ∀ t : K, X gR t ∈ H) (hNR : ∀ t : K, X (-gR) t ∈ H) :
    adjointGroup .G2 K ≤ H := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg⟩
  fin_cases i
  · rcases hg with hg | hg
    · have : g = xUnit .G2 K iA c := Units.ext hg
      rw [this, xUnit_iA]; exact hA c
    · have : g = yUnit .G2 K iA c := Units.ext hg
      rw [this, yUnit_iA]; exact hNA c
  · rcases hg with hg | hg
    · have : g = xUnit .G2 K iR c := Units.ext hg
      rw [this, xUnit_iR]; exact hR c
    · have : g = yUnit .G2 K iR c := Units.ext hg
      rw [this, yUnit_iR]; exact hNR c

theorem adjointGroup_le_of_Qg_le (H : Subgroup (ModGL .G2 K)) (hQ : Qg K ≤ H)
    (hCm : ∀ t : K, X (-gC) t ∈ H) : adjointGroup .G2 K ≤ H := by
  have hA : ∀ t : K, X gA t ∈ H := fun t => hQ (X_mem_Qg isQRoot_a t)
  have hNA := Xna_mem_of H hCm fun t => hQ (X_mem_Qg isQRoot_b t)
  exact adjointGroup_le_of_rootGroups H hA hNA (Xr_mem_of H hQ hNA)
    (Xnr_mem_of H hQ (Xnb_mem_of H hCm hA))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max
