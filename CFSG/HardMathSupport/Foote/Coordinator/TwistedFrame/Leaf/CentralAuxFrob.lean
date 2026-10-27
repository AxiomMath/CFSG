module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false

section Fixed

open Polynomial in
theorem exists_algebraMap_of_pow_card_eq {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (c : L) (hc : c ^ Nat.card K = c) : ∃ k : K, algebraMap K L k = c := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hc
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  set P : L[X] := X ^ Fintype.card K - X with hP
  have hdeg : P.natDegree = Fintype.card K := FiniteField.X_pow_card_sub_X_natDegree_eq L hq1
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  set S : Finset L := Finset.univ.image (algebraMap K L) with hS
  have hSc : S.card = Fintype.card K := by
    rw [hS, Finset.card_image_of_injective _ (algebraMap K L).injective, Finset.card_univ]
  have hSsub : S ⊆ P.roots.toFinset := by
    intro s hs
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hs
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp only [eval_sub, eval_pow, eval_X]
    rw [← map_pow, FiniteField.pow_card, sub_self]
  have hle : P.roots.toFinset.card ≤ S.card := by
    calc P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ = S.card := by rw [hdeg, hSc]
  have hEq := Finset.eq_of_subset_of_card_le hSsub hle
  have hcm : c ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp only [eval_sub, eval_pow, eval_X]
    rw [hc, sub_self]
  rw [← hEq] at hcm
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hcm
  exact ⟨k, hk⟩

end Fixed

section Frobenius


variable {τ : Tag} {L : Type} [Field L]

@[expose] def Fm (ψ : L →+* L) : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom ψ)

theorem Fm_pinnedX (ψ : L →+* L) (γ : Fin τ.rank → ℤ) (c : L) :
    Fm ψ (pinnedX τ L γ c) = pinnedX τ L γ (ψ c) :=
  Units.ext (by
    rw [Fm, Units.coe_map]
    exact entrywise_pinnedX ψ γ c)

theorem Fm_prodX (ψ : L →+* L) (l : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → L) :
    Fm ψ (CoordAux.prodX l c) = CoordAux.prodX l (fun α => ψ (c α)) := by
  induction l with
  | nil => rw [CoordAux.prodX_nil, CoordAux.prodX_nil, map_one]
  | cons α l ih => rw [CoordAux.prodX_cons, CoordAux.prodX_cons, map_mul, Fm_pinnedX, ih]

theorem baseChangeGL_prodX {K : Type} [Field K] (f : K →+* L) (l : List (Fin τ.rank → ℤ))
    (c : (Fin τ.rank → ℤ) → K) :
    baseChangeGL f (CoordAux.prodX l c) = CoordAux.prodX l (fun α => f (c α)) := by
  induction l with
  | nil => rw [CoordAux.prodX_nil, CoordAux.prodX_nil, map_one]
  | cons α l ih =>
    rw [CoordAux.prodX_cons, CoordAux.prodX_cons, map_mul, baseChangeGL_pinnedX, ih]

variable {K : Type} [Field K] [Algebra K L]

theorem exists_rational_of_fixed [Finite K] (ψ : L →+* L) (hψ : ∀ c, ψ c = c ^ Nat.card K)
    {y : ModGL τ L} (hy : y ∈ Qθ τ L) (hF : Fm ψ y = y) :
    ∃ y₀ ∈ Qθ τ K, baseChangeGL (algebraMap K L) y₀ = y := by
  classical
  have hspec := heisCoord_spec τ L
  obtain ⟨L₁, hnd, hmem⟩ := CoordAux.exists_list_Deg1 (τ := τ)
  have hD : ∀ β ∈ L₁, β ∈ Deg1 τ := fun β hβ => (hmem β).1 hβ
  have hsupp : ∀ ν, ν ∉ L₁ → heisCoord τ L y ν = 0 :=
    fun ν hν => hspec.support y hy ν (fun h => hν ((hmem ν).2 h))
  obtain ⟨u, hu, hyu⟩ := exists_prodX_of_support hnd hD hy hsupp
  generalize hc : heisCoord τ L y = c at hyu
  obtain ⟨z, rfl⟩ := mem_rootSubgroup.1 hu
  have hQ := heisCoord_prodX hnd hD (fun α => ψ (c α))
  have hFy : Fm ψ y = pinnedX τ L (highRoot τ) (ψ z) *
      CoordAux.prodX L₁ (fun α => ψ (c α)) := by
    rw [hyu, map_mul, Fm_pinnedX, Fm_prodX]
  have hcoordF : ∀ β ∈ L₁, c β = ψ (c β) := by
    intro β hβ
    have h1 : heisCoord τ L (Fm ψ y) β = ψ (c β) := by
      rw [hFy, hspec.mul _ (Uθ_le_Qθ (mem_rootSubgroup.2 ⟨ψ z, rfl⟩)) _ hQ.1,
        hspec.pinnedX_highRoot, Pi.add_apply, hQ.2 β, if_pos hβ]
      simp
    rw [hF, hc] at h1
    exact h1
  have hrat : ∀ β, ∃ k : K, β ∈ L₁ → algebraMap K L k = c β := by
    intro β
    by_cases hβ : β ∈ L₁
    · have h := hcoordF β hβ
      rw [hψ] at h
      obtain ⟨k, hk⟩ := exists_algebraMap_of_pow_card_eq (K := K) (c β) h.symm
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose c₀ hc₀ using hrat
  have hy₁ : CoordAux.prodX L₁ c =
      baseChangeGL (algebraMap K L) (CoordAux.prodX L₁ c₀) := by
    rw [baseChangeGL_prodX]
    exact CoordAux.prodX_congr fun α hα => (hc₀ α hα).symm
  have hFy₁ : Fm ψ (CoordAux.prodX L₁ c) = CoordAux.prodX L₁ c := by
    rw [Fm_prodX]
    exact CoordAux.prodX_congr fun α hα => (hcoordF α hα).symm
  have hz : ψ z = z := by
    have hu' : pinnedX τ L (highRoot τ) z = y * (CoordAux.prodX L₁ c)⁻¹ := by
      rw [hyu]; group
    have h1 : pinnedX τ L (highRoot τ) (ψ z) = pinnedX τ L (highRoot τ) z := by
      have := congrArg (Fm ψ) hu'
      rw [map_mul, map_inv, hF, hFy₁, Fm_pinnedX] at this
      rw [this, hu']
    exact pinnedX_injective τ L (highRoot τ) h1
  obtain ⟨z₀, hz₀⟩ := exists_algebraMap_of_pow_card_eq (K := K) z ((hψ z).symm.trans hz)
  refine ⟨pinnedX τ K (highRoot τ) z₀ * CoordAux.prodX L₁ c₀,
    mul_mem (Uθ_le_Qθ (mem_rootSubgroup.2 ⟨z₀, rfl⟩)) (heisCoord_prodX hnd hD c₀).1, ?_⟩
  rw [map_mul, baseChangeGL_pinnedX, hz₀, ← hy₁, ← hyu]

end Frobenius

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
