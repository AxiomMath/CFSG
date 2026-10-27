module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Coord

public section

namespace CFSG.SeitzReduction.EPilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

variable {τ : Tag} {K : Type} [Field K]

theorem exists_add_single_mem_rootFinset_of_deg_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ μ ∈ rootFinset τ, μ (iθ τ) = 1 → μ ≠ highRoot τ - Pi.single (iθ τ) 1 →
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ μ + Pi.single j 1 ∈ rootFinset τ := by
  rcases hτ with rfl | rfl | rfl <;> decide +kernel

theorem exists_sub_single_mem_rootFinset_of_deg_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ μ ∈ rootFinset τ, μ (iθ τ) = 1 → μ ≠ Pi.single (iθ τ) 1 →
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ μ - Pi.single j 1 ∈ rootFinset τ := by
  rcases hτ with rfl | rfl | rfl <;> decide +kernel


theorem heisCoord_conj_pinnedX_of_deg_zero [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ0 : γ (iθ τ) = 0) (s : K) {q : ModGL τ K}
    (hq : q ∈ Qθ τ K) :
    pinnedX τ K γ s * q * (pinnedX τ K γ s)⁻¹ ∈ Qθ τ K ∧
      ∀ ν, heisCoord τ K (pinnedX τ K γ s * q * (pinnedX τ K γ s)⁻¹) ν =
        heisCoord τ K q ν + if ν ∈ rootFinset τ then s * heisCoord τ K q (ν - γ) else 0 := by
  classical
  have hs := heisCoord_spec τ K
  have hg := CFSG.StandardType.LieKnownR2.Coord.pinnedX_mem_Pθ hγ hγ0 s
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    hτ.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr h)
  refine ⟨CFSG.StandardType.LieKnownR2.Coord.conj_mem_Qθ hg hq, fun ν => ?_⟩
  rw [CFSG.StandardType.LieKnownR2.Coord.heisCoord_conj_param hτ' hγ hγ0 hq s ν]
  congr 1
  by_cases h2 : IsRoot τ ν
  · by_cases h1 : ν - γ ∈ Deg1 τ
    · rw [if_pos ⟨h1, h2⟩, if_pos (mem_rootFinset.2 h2)]
    · rw [if_neg (fun h => h1 h.1), if_pos (mem_rootFinset.2 h2),
        hs.support q hq (ν - γ) h1, mul_zero]
  · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 (mem_rootFinset.1 h))]

theorem heisCoord_eq_zero_of_forall_conj_single [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {q : ModGL τ K} (hq : q ∈ Qθ τ K)
    (hfix : ∀ j : Fin τ.rank, j ≠ iθ τ →
      heisCoord τ K (pinnedX τ K (Pi.single j 1) 1 * q * (pinnedX τ K (Pi.single j 1) 1)⁻¹) =
        heisCoord τ K q)
    {μ : Fin τ.rank → ℤ} (hμ : μ ≠ highRoot τ - Pi.single (iθ τ) 1) :
    heisCoord τ K q μ = 0 := by
  by_cases hμD : μ ∈ Deg1 τ
  · obtain ⟨hμr, hμ1⟩ := CoordAux.mem_Deg1.1 hμD
    obtain ⟨j, hj, hjr⟩ :=
      exists_add_single_mem_rootFinset_of_deg_one hτ μ (mem_rootFinset.2 hμr) hμ1 hμ
    have h1 := (heisCoord_conj_pinnedX_of_deg_zero hτ (isRoot_single τ j)
      (by simp [Ne.symm hj]) 1 hq).2 (μ + Pi.single j 1)
    rw [hfix j hj, if_pos hjr, one_mul, add_sub_cancel_right] at h1
    exact left_eq_add.1 h1
  · exact (heisCoord_spec τ K).support q hq μ hμD

theorem heisCoord_eq_zero_of_forall_conj_neg_single [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {q : ModGL τ K} (hq : q ∈ Qθ τ K)
    (hfix : ∀ j : Fin τ.rank, j ≠ iθ τ →
      heisCoord τ K (pinnedX τ K (-Pi.single j 1) 1 * q * (pinnedX τ K (-Pi.single j 1) 1)⁻¹) =
        heisCoord τ K q)
    {μ : Fin τ.rank → ℤ} (hμ : μ ≠ Pi.single (iθ τ) 1) :
    heisCoord τ K q μ = 0 := by
  by_cases hμD : μ ∈ Deg1 τ
  · obtain ⟨hμr, hμ1⟩ := CoordAux.mem_Deg1.1 hμD
    obtain ⟨j, hj, hjr⟩ :=
      exists_sub_single_mem_rootFinset_of_deg_one hτ μ (mem_rootFinset.2 hμr) hμ1 hμ
    have h1 := (heisCoord_conj_pinnedX_of_deg_zero hτ
      (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single τ j))
      (by simp [Ne.symm hj]) 1 hq).2 (μ - Pi.single j 1)
    rw [hfix j hj, if_pos hjr, one_mul, sub_neg_eq_add, sub_add_cancel] at h1
    exact left_eq_add.1 h1
  · exact (heisCoord_spec τ K).support q hq μ hμD

private theorem isRoot_highRoot_sub_single (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    IsRoot τ (highRoot τ - Pi.single (iθ τ) 1) := by
  rcases hτ with rfl | rfl | rfl <;> exact RootOps.isRootB_iff.1 (by decide +kernel)

private theorem mem_Deg1_highRoot_sub_single (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRoot τ - Pi.single (iθ τ) 1 ∈ Deg1 τ := by
  refine CoordAux.mem_Deg1.2 ⟨isRoot_highRoot_sub_single hτ, ?_⟩
  simp [CoordAux.highRoot_degree]

private theorem ne_highRoot_sub_single (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRoot τ - Pi.single (iθ τ) 1 ≠ Pi.single (iθ τ) 1 := by
  rcases hτ with rfl | rfl | rfl <;> decide +kernel

private theorem ne_neg_highRoot_sub_single (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRoot τ - Pi.single (iθ τ) 1 ≠ -Pi.single (iθ τ) 1 := by
  rcases hτ with rfl | rfl | rfl <;> decide +kernel

private theorem exists_mul_pinnedX_coord_ne_zero {η : Fin τ.rank → ℤ} (hη : η ∈ Deg1 τ)
    {q : ModGL τ K} (hq : q ∈ Qθ τ K) (hqU : q ∉ Uθ τ K)
    (hηs : ∀ μ, μ ≠ η → heisCoord τ K q μ = 0) :
    ∃ u ∈ Uθ τ K, q = u * pinnedX τ K η (heisCoord τ K q η) ∧
      heisCoord τ K q η ≠ 0 := by
  obtain ⟨u, hu, h⟩ := exists_prodX_of_support (L := [η]) (by simp) (by simpa using hη) hq
    (fun ν hν => hηs ν (by simpa using hν))
  rw [CoordAux.prodX_singleton] at h
  refine ⟨u, hu, h, ?_⟩
  intro h0
  apply hqU
  rw [h, h0, pinnedX_zero, mul_one]
  exact hu

private theorem commute_of_mem_Uθ_mul_mem_posUnipotent {u u' x y : ModGL τ K}
    (hu : u ∈ Uθ τ K) (hu' : u' ∈ Uθ τ K) (hx : x ∈ posUnipotent τ K)
    (hy : y ∈ posUnipotent τ K)
    (h : (u * x) * (u' * y) = (u' * y) * (u * x)) : x * y = y * x := by
  have hux : Commute u x := CoordAux.Uθ_comm hu hx
  have huy : Commute u y := CoordAux.Uθ_comm hu hy
  have hu'x : Commute u' x := CoordAux.Uθ_comm hu' hx
  have hu'y : Commute u' y := CoordAux.Uθ_comm hu' hy
  have huP : u ∈ posUnipotent τ K :=
    parabolicRadical_le_posUnipotent (Jθ τ) (Uθ_le_Qθ hu)
  have huu' : Commute u' u := CoordAux.Uθ_comm hu' huP
  have h1 : (u * x) * (u' * y) = (u * u') * (x * y) :=
    Commute.mul_mul_mul_comm hu'x.symm u y
  have h2 : (u' * y) * (u * x) = (u * u') * (y * x) := by
    calc (u' * y) * (u * x) = (u' * u) * (y * x) :=
          Commute.mul_mul_mul_comm huy.symm u' x
      _ = (u * u') * (y * x) := by rw [huu'.eq]
  rw [h1, h2] at h
  exact mul_left_cancel h

private theorem commutator_pinnedX_highRoot_sub_single [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (s s' : K) :
    pinnedX τ K (highRoot τ - Pi.single (iθ τ) 1) s *
        pinnedX τ K (Pi.single (iθ τ) 1) s' *
        (pinnedX τ K (highRoot τ - Pi.single (iθ τ) 1) s)⁻¹ *
        (pinnedX τ K (Pi.single (iθ τ) 1) s')⁻¹ =
      pinnedX τ K (highRoot τ) (s * s') := by
  have hsum : highRoot τ - Pi.single (iθ τ) 1 + Pi.single (iθ τ) 1 = highRoot τ := by
    simp
  have hcomm := commutatorElement_pinnedX_of_oddDerivLaced (R := K)
    (CharP.cast_eq_zero K 2) (oddDerivLacedCheck_of_simplyLaced (Or.inr hτ))
    (isRoot_highRoot_sub_single hτ) (isRoot_single τ (iθ τ))
    (ne_highRoot_sub_single hτ) (ne_neg_highRoot_sub_single hτ)
    (by rw [hsum]; exact isRoot_highRoot τ) s s'
  rw [hsum, commutatorElement_def] at hcomm
  exact hcomm

theorem mul_ne_mul_of_heisCoord_support [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {v v' : ModGL τ K} (hv : v ∈ Qθ τ K) (hv' : v' ∈ Qθ τ K)
    (hsv : ∀ μ, μ ≠ highRoot τ - Pi.single (iθ τ) 1 → heisCoord τ K v μ = 0)
    (hsv' : ∀ μ, μ ≠ Pi.single (iθ τ) 1 → heisCoord τ K v' μ = 0)
    (hvU : v ∉ Uθ τ K) (hv'U : v' ∉ Uθ τ K) : v * v' ≠ v' * v := by
  have hβD : highRoot τ - Pi.single (iθ τ) 1 ∈ Deg1 τ := mem_Deg1_highRoot_sub_single hτ
  have hαD : Pi.single (iθ τ) 1 ∈ Deg1 τ :=
    CoordAux.mem_Deg1.2 ⟨isRoot_single τ (iθ τ), by simp⟩
  obtain ⟨u, hu, hvu, hs⟩ := exists_mul_pinnedX_coord_ne_zero hβD hv hvU hsv
  obtain ⟨u', hu', hv'u', hs'⟩ := exists_mul_pinnedX_coord_ne_zero hαD hv' hv'U hsv'
  let s : K := heisCoord τ K v (highRoot τ - Pi.single (iθ τ) 1)
  let s' : K := heisCoord τ K v' (Pi.single (iθ τ) 1)
  have hxP : pinnedX τ K (highRoot τ - Pi.single (iθ τ) 1) s ∈ posUnipotent τ K :=
    CoordAux.pinnedX_mem_pos hβD s
  have hyP : pinnedX τ K (Pi.single (iθ τ) 1) s' ∈ posUnipotent τ K :=
    CoordAux.pinnedX_mem_pos hαD s'
  intro h
  rw [hvu, hv'u'] at h
  have hxy : pinnedX τ K (highRoot τ - Pi.single (iθ τ) 1) s *
      pinnedX τ K (Pi.single (iθ τ) 1) s' =
      pinnedX τ K (Pi.single (iθ τ) 1) s' *
        pinnedX τ K (highRoot τ - Pi.single (iθ τ) 1) s :=
    commute_of_mem_Uθ_mul_mem_posUnipotent hu hu' hxP hyP h
  have hone : pinnedX τ K (highRoot τ - Pi.single (iθ τ) 1) s *
        pinnedX τ K (Pi.single (iθ τ) 1) s' *
        (pinnedX τ K (highRoot τ - Pi.single (iθ τ) 1) s)⁻¹ *
        (pinnedX τ K (Pi.single (iθ τ) 1) s')⁻¹ = 1 := by
    rw [hxy]
    group
  have hss' : s * s' = 0 := by
    refine pinnedX_injective τ K (highRoot τ) ?_
    rw [pinnedX_zero]
    exact (commutator_pinnedX_highRoot_sub_single hτ s s').symm.trans hone
  exact (mul_ne_zero hs hs') hss'

end CFSG.SeitzReduction.EPilot
