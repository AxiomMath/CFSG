module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Basic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Generic

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section Close

variable {K : Type} [Field K] [Finite K] {σ η : K ≃+* K} {p : ℕ}

private noncomputable abbrev twE6_w (i : Fin Tag.E6.rank) : ↥(adjointGroup Tag.E6 K) :=
  CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ)

private abbrev twE6_thetaConjMv (g : ↥(adjointGroup Tag.E6 K)) (β δ : Fin Tag.E6.rank → ℤ) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ u : K, g * xE6 β u * g⁻¹ = xE6 δ ((ε : K) * u)

private theorem twE6_thetaConj_comp {g h : ↥(adjointGroup Tag.E6 K)} {β δ γ : Fin Tag.E6.rank → ℤ}
    (hg : twE6_thetaConjMv g β δ) (hh : twE6_thetaConjMv h δ γ) :
    twE6_thetaConjMv (h * g) β γ := by
  obtain ⟨ε, hε, hg'⟩ := hg
  obtain ⟨ε', hε', hh'⟩ := hh
  refine ⟨ε' * ε, ?_, fun u => ?_⟩
  · rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num
  · calc h * g * xE6 β u * (h * g)⁻¹ = h * (g * xE6 β u * g⁻¹) * h⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = h * xE6 δ ((ε : K) * u) * h⁻¹ := by rw [hg' u]
      _ = xE6 γ ((ε' : K) * ((ε : K) * u)) := hh' _
      _ = xE6 γ (((ε' * ε : ℤ) : K) * u) := by congr 1; push_cast; ring

private theorem twE6_thetaConj_weyl (i : Fin Tag.E6.rank) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) :
    twE6_thetaConjMv (twE6_w (K := K) i) β (reflect Tag.E6 i β) := by
  obtain ⟨ε, hε, h⟩ := weylElement_xPar_conj (F := rootOperatorFamily Tag.E6) (K := K) i hβ
  refine ⟨ε, hε, fun u => ?_⟩
  have h1 := h 1 u
  have hrefl : CFSG.LieType.RootSystem.reflection Tag.E6.cartan i β = reflect Tag.E6 i β := by
    rw [CFSG.LieType.RootSystem.reflection_apply]
    rfl
  rw [hrefl] at h1
  simp only [Units.val_one, one_zpow, mul_one] at h1
  exact h1

private theorem twE6_thetaConj_step (i : Fin Tag.E6.rank) {β β' : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (h : reflect Tag.E6 i β = β') :
    twE6_thetaConjMv (twE6_w (K := K) i) β β' ∧ IsRoot Tag.E6 β' := by
  subst h
  exact ⟨twE6_thetaConj_weyl i hβ, IsRoot.reflect i hβ⟩

private abbrev twE6_vec (a0 a1 a2 a3 a4 a5 : ℤ) : Fin Tag.E6.rank → ℤ :=
  ![a0, a1, a2, a3, a4, a5]

private theorem twE6_thetaConj_top {t : Fin Tag.E6.rank → ℤ} (ht : t ∈ rootFinset Tag.E6)
    (hmax : ∀ γ ∈ rootFinset Tag.E6, height (τ := Tag.E6) γ ≤ height (τ := Tag.E6) t) :
    t = twE6_vec 1 2 2 3 2 1 := by
  have hval : ∀ s ∈ rootFinset Tag.E6, 11 ≤ height (τ := Tag.E6) s → s = twE6_vec 1 2 2 3 2 1 := by
    decide +kernel
  have h0 : twE6_vec 1 2 2 3 2 1 ∈ rootFinset Tag.E6 := by
    decide +kernel
  have h11 : height (τ := Tag.E6) (twE6_vec 1 2 2 3 2 1) = 11 := by
    decide +kernel
  have hle : 11 ≤ height t := by
    have := hmax _ h0
    rw [h11] at this
    exact this
  exact hval t ht hle

private theorem twE6_not_isRoot_of_not_mem {v : Fin Tag.E6.rank → ℤ} (h : v ∉ rootFinset Tag.E6) :
    ¬IsRoot Tag.E6 v := fun hv => h (mem_rootFinset.2 hv)

private theorem twE6_thetaConj_w_eq (i : Fin Tag.E6.rank) :
    twE6_w (K := K) i =
      xE6 (Pi.single i 1) 1 * xE6 (-Pi.single i 1) (-1) * xE6 (Pi.single i 1) 1 := by
  simp only [twE6_w, CFSG.LieType.Steinberg.weylElement, inv_one, Units.val_one, Units.val_neg]

private theorem twE6_thetaConj_grp_id {G : Type*} [Group G] (A A' B B' : G)
    (hBA : B * A = A * B) (hBA' : B * A' = A' * B) (hB'A : B' * A = A * B') :
    A * B * (A' * B') * (A * B) = A * A' * A * (B * B' * B) := by
  calc A * B * (A' * B') * (A * B) = A * (B * A') * B' * (A * B) := by simp only [mul_assoc]
    _ = A * (A' * B) * B' * (A * B) := by rw [hBA']
    _ = A * A' * B * (B' * A) * B := by simp only [mul_assoc]
    _ = A * A' * B * (A * B') * B := by rw [hB'A]
    _ = A * A' * (B * A) * B' * B := by simp only [mul_assoc]
    _ = A * A' * (A * B) * B' * B := by rw [hBA]
    _ = A * A' * A * (B * B' * B) := by simp only [mul_assoc]

private theorem twE6_thetaConj_orbit (i j : Fin Tag.E6.rank)
    (hr1 : ¬IsRoot Tag.E6 ((Pi.single j 1 : Fin Tag.E6.rank → ℤ) + Pi.single i 1))
    (hn1 : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + Pi.single i 1 ≠ 0)
    (hr2 : ¬IsRoot Tag.E6 ((Pi.single j 1 : Fin Tag.E6.rank → ℤ) + -Pi.single i 1))
    (hn2 : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + -Pi.single i 1 ≠ 0)
    (hr3 : ¬IsRoot Tag.E6 ((-Pi.single j 1 : Fin Tag.E6.rank → ℤ) + Pi.single i 1))
    (hn3 : (-Pi.single j 1 : Fin Tag.E6.rank → ℤ) + Pi.single i 1 ≠ 0) :
    twE6_w (K := K) i * twE6_w (K := K) j =
      xE6 (Pi.single i 1) (1 : K) * xE6 (Pi.single j 1) (1 : K) *
        (xE6 (-Pi.single i 1) (-1 : K) * xE6 (-Pi.single j 1) (-1 : K)) *
        (xE6 (Pi.single i 1) (1 : K) * xE6 (Pi.single j 1) (1 : K)) := by
  have hBA : xE6 (Pi.single j 1) (1 : K) * xE6 (Pi.single i 1) (1 : K) =
      xE6 (Pi.single i 1) (1 : K) * xE6 (Pi.single j 1) (1 : K) :=
    (commute_xPar (F := rootOperatorFamily Tag.E6) e6AdjData_valid noG2_E6
      (isRoot_single Tag.E6 j) (isRoot_single Tag.E6 i) hn1 hr1 1 1).eq
  have hBA' : xE6 (Pi.single j 1) (1 : K) * xE6 (-Pi.single i 1) (-1 : K) =
      xE6 (-Pi.single i 1) (-1 : K) * xE6 (Pi.single j 1) (1 : K) :=
    (commute_xPar (F := rootOperatorFamily Tag.E6) e6AdjData_valid noG2_E6
      (isRoot_single Tag.E6 j) (isRoot_neg_single Tag.E6 i) hn2 hr2 1 (-1)).eq
  have hB'A : xE6 (-Pi.single j 1) (-1 : K) * xE6 (Pi.single i 1) (1 : K) =
      xE6 (Pi.single i 1) (1 : K) * xE6 (-Pi.single j 1) (-1 : K) :=
    (commute_xPar (F := rootOperatorFamily Tag.E6) e6AdjData_valid noG2_E6
      (isRoot_neg_single Tag.E6 j) (isRoot_single Tag.E6 i) hn3 hr3 (-1) 1).eq
  rw [twE6_thetaConj_w_eq i, twE6_thetaConj_w_eq j]
  exact (twE6_thetaConj_grp_id _ _ _ _ hBA hBA' hB'A).symm

theorem twE6_theta_conj_simple (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) :
    ∃ n ∈ twR σ η, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      twIncl σ n * xE6 θ c * (twIncl σ n)⁻¹ = xE6 (Pi.single 3 1) ((ε : K) * c) := by
  obtain ⟨hθr, hθmax⟩ := hθ
  have hθeq : θ = twE6_vec 1 2 2 3 2 1 :=
    twE6_thetaConj_top (mem_rootFinset.2 hθr) (fun γ hγ => hθmax γ (mem_rootFinset.1 hγ))
  subst hθeq
  have hgen : TwGens σ η (twRP σ η) := twR_gens hS
  have hWfix : ∀ i ∈ ({1, 3} : Finset (Fin 6)), twE6_w (K := K) i ∈ twRP σ η := by
    intro i hi
    rw [twE6_thetaConj_w_eq i]
    exact (twRP σ η).mul_mem ((twRP σ η).mul_mem (hgen.fixedX i hi 1 (by simp) (by simp))
      (hgen.fixedY i hi (-1) (by simp) (by simp))) (hgen.fixedX i hi 1 (by simp) (by simp))
  have hW1 : twE6_w (K := K) 1 ∈ twRP σ η := hWfix 1 (by decide)
  have hW3 : twE6_w (K := K) 3 ∈ twRP σ η := hWfix 3 (by decide)
  have hX24 : xE6 (Pi.single 2 1) 1 * xE6 (Pi.single 4 1) 1 ∈ twRP σ η := by
    have h := hgen.orbX (2, 4) (by decide) 1 (map_one η)
    rw [map_one σ] at h
    exact h
  have hY24 : xE6 (-Pi.single 2 1) (-1) * xE6 (-Pi.single 4 1) (-1) ∈ twRP σ η := by
    have h := hgen.orbY (2, 4) (by decide) (-1) (by simp)
    rw [map_neg, map_one] at h
    exact h
  have hX05 : xE6 (Pi.single 0 1) 1 * xE6 (Pi.single 5 1) 1 ∈ twRP σ η := by
    have h := hgen.orbX (0, 5) (by decide) 1 (map_one η)
    rw [map_one σ] at h
    exact h
  have hY05 : xE6 (-Pi.single 0 1) (-1) * xE6 (-Pi.single 5 1) (-1) ∈ twRP σ η := by
    have h := hgen.orbY (0, 5) (by decide) (-1) (by simp)
    rw [map_neg, map_one] at h
    exact h
  have hW24 : twE6_w (K := K) 2 * twE6_w (K := K) 4 ∈ twRP σ η := by
    rw [twE6_thetaConj_orbit 2 4 (twE6_not_isRoot_of_not_mem (by decide +kernel))
      (by decide +kernel) (twE6_not_isRoot_of_not_mem (by decide +kernel)) (by decide +kernel)
      (twE6_not_isRoot_of_not_mem (by decide +kernel)) (by decide +kernel)]
    exact (twRP σ η).mul_mem ((twRP σ η).mul_mem hX24 hY24) hX24
  have hW05 : twE6_w (K := K) 0 * twE6_w (K := K) 5 ∈ twRP σ η := by
    rw [twE6_thetaConj_orbit 0 5 (twE6_not_isRoot_of_not_mem (by decide +kernel))
      (by decide +kernel) (twE6_not_isRoot_of_not_mem (by decide +kernel)) (by decide +kernel)
      (twE6_not_isRoot_of_not_mem (by decide +kernel)) (by decide +kernel)]
    exact (twRP σ η).mul_mem ((twRP σ η).mul_mem hX05 hY05) hX05
  have hGP : twE6_w (K := K) 1 * (twE6_w (K := K) 2 * twE6_w (K := K) 4 *
      (twE6_w (K := K) 3 * (twE6_w (K := K) 0 * twE6_w (K := K) 5 *
        (twE6_w (K := K) 2 * twE6_w (K := K) 4 * (twE6_w (K := K) 3 * twE6_w (K := K) 1)))))
      ∈ twRP σ η :=
    (twRP σ η).mul_mem hW1 ((twRP σ η).mul_mem hW24 ((twRP σ η).mul_mem hW3
      ((twRP σ η).mul_mem hW05 ((twRP σ η).mul_mem hW24 ((twRP σ η).mul_mem hW3 hW1)))))
  obtain ⟨M1, r1⟩ := twE6_thetaConj_step (K := K) 1 hθr
    (β' := twE6_vec 1 1 2 3 2 1) (by decide +kernel)
  obtain ⟨M2, r2⟩ := twE6_thetaConj_step (K := K) 3 r1
    (β' := twE6_vec 1 1 2 2 2 1) (by decide +kernel)
  obtain ⟨M3a, r3⟩ := twE6_thetaConj_step (K := K) 4 r2
    (β' := twE6_vec 1 1 2 2 1 1) (by decide +kernel)
  obtain ⟨M3b, r4⟩ := twE6_thetaConj_step (K := K) 2 r3
    (β' := twE6_vec 1 1 1 2 1 1) (by decide +kernel)
  obtain ⟨M4a, r5⟩ := twE6_thetaConj_step (K := K) 5 r4
    (β' := twE6_vec 1 1 1 2 1 0) (by decide +kernel)
  obtain ⟨M4b, r6⟩ := twE6_thetaConj_step (K := K) 0 r5
    (β' := twE6_vec 0 1 1 2 1 0) (by decide +kernel)
  obtain ⟨M5, r7⟩ := twE6_thetaConj_step (K := K) 3 r6
    (β' := twE6_vec 0 1 1 1 1 0) (by decide +kernel)
  obtain ⟨M6a, r8⟩ := twE6_thetaConj_step (K := K) 4 r7
    (β' := twE6_vec 0 1 1 1 0 0) (by decide +kernel)
  obtain ⟨M6b, r9⟩ := twE6_thetaConj_step (K := K) 2 r8
    (β' := twE6_vec 0 1 0 1 0 0) (by decide +kernel)
  obtain ⟨M7, -⟩ := twE6_thetaConj_step (K := K) 1 r9
    (β' := Pi.single 3 1) (by decide +kernel)
  have A1 := twE6_thetaConj_comp M3a M3b
  have A2 := twE6_thetaConj_comp M4a M4b
  have A3 := twE6_thetaConj_comp M6a M6b
  have C := twE6_thetaConj_comp (twE6_thetaConj_comp (twE6_thetaConj_comp
    (twE6_thetaConj_comp (twE6_thetaConj_comp (twE6_thetaConj_comp M1 M2) A1) A2) M5) A3) M7
  obtain ⟨ε, hε, hG⟩ := C
  obtain ⟨n, hn, hnG⟩ := Subgroup.mem_map.mp hGP
  refine ⟨n, hn, ε, hε, fun c => ?_⟩
  rw [hnG]
  exact hG c

private theorem twE6_mem_reflect_node (P : Subgroup ↥(adjointGroup Tag.E6 K)) {i : Fin Tag.E6.rank}
    (hwi : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) ∈ P)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (u : K) :
    xPar (rootOperatorFamily Tag.E6) β u ∈ P ↔
      xPar (rootOperatorFamily Tag.E6) (reflect Tag.E6 i β) u ∈ P := by
  have key : ∀ {β : Fin Tag.E6.rank → ℤ}, IsRoot Tag.E6 β → ∀ u : K,
      xPar (rootOperatorFamily Tag.E6) β u ∈ P →
        xPar (rootOperatorFamily Tag.E6) (reflect Tag.E6 i β) u ∈ P := by
    intro β hβ u hu
    obtain ⟨ε, hε, h⟩ := weylElement_xPar_conj (F := rootOperatorFamily Tag.E6) (K := K) i hβ
    have h1 := P.mul_mem (P.mul_mem hwi hu) (P.inv_mem hwi)
    rw [h 1 u] at h1
    have hrefl : CFSG.LieType.RootSystem.reflection Tag.E6.cartan i β = reflect Tag.E6 i β := by
      rw [CFSG.LieType.RootSystem.reflection_apply]
      rfl
    rw [hrefl] at h1
    simp only [Units.val_one, one_zpow, mul_one] at h1
    rcases hε with rfl | rfl
    · simpa using h1
    · have h2 := P.inv_mem h1
      rw [xPar_neg] at h2
      simpa using h2
  refine ⟨key hβ u, fun h => ?_⟩
  have := key (IsRoot.reflect i hβ) u h
  rwa [reflect_reflect] at this

private theorem twE6_reflect_self (i : Fin Tag.E6.rank) :
    reflect Tag.E6 i (Pi.single i 1) = -Pi.single i 1 := by
  have hcart : ∀ j : Fin Tag.E6.rank, Tag.E6.cartan j j = 2 := by decide
  rw [reflect_single, hcart i, two_zsmul]
  abel

private theorem twE6_mem_e13_iff (P : Subgroup ↥(adjointGroup Tag.E6 K))
    (hw1 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 1 (1 : Kˣ) ∈ P)
    (u : K) :
    xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) u ∈ P ↔
      xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1 + Pi.single 1 1) u ∈ P := by
  have hr1 : reflect Tag.E6 1 (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single 3 1 + Pi.single 1 1 := by decide
  have h := twE6_mem_reflect_node P hw1 (isRoot_single Tag.E6 3) u
  rwa [hr1] at h

private theorem twE6_mem_e1_iff (P : Subgroup ↥(adjointGroup Tag.E6 K))
    (hw3 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 3 (1 : Kˣ) ∈ P)
    (h13 : Tag.E6.cartan 1 3 = -1) (u : K) :
    xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1 + Pi.single 1 1) u ∈ P ↔
      xPar (rootOperatorFamily Tag.E6) (Pi.single 1 1) u ∈ P := by
  have hr2 : reflect Tag.E6 3 (Pi.single 3 1 + Pi.single 1 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single 1 1 := by decide
  have hroot : IsRoot Tag.E6 (Pi.single 3 1 + Pi.single 1 1 : Fin Tag.E6.rank → ℤ) :=
    isRoot_single_add_single h13
  have h := twE6_mem_reflect_node P hw3 hroot u
  rwa [hr2] at h

private theorem twE6_neighbour_one_three (P : Subgroup ↥(adjointGroup Tag.E6 K))
    (hw1 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 1 (1 : Kˣ) ∈ P)
    (hw3 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 3 (1 : Kˣ) ∈ P)
    (u : K) :
    xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) u ∈ P ↔
      xPar (rootOperatorFamily Tag.E6) (Pi.single 1 1) u ∈ P :=
  (twE6_mem_e13_iff P hw1 u).trans (twE6_mem_e1_iff P hw3 (by decide) u)

theorem twE6_long_full (hS : TwE6Setup K σ η p) (H : Subgroup ↥(twistedE6RootGroup K σ))
    (hRH : twR σ η ≤ H) {t : K} (hσt : σ t = t) (hηt : η t ≠ t)
    (hmem : xE6 (Pi.single 3 1) t ∈ H.map (twIncl σ)) :
    ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c →
      xE6 (Pi.single i 1) c ∈ H.map (twIncl σ) ∧ xE6 (-Pi.single i 1) c ∈ H.map (twIncl σ) := by
  have hgen : TwGens σ η (twRP σ η) := twR_gens hS
  have hRHP : twRP σ η ≤ H.map (twIncl σ) := Subgroup.map_mono hRH
  have hfixX : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → η c = c →
      xE6 (Pi.single i 1) c ∈ H.map (twIncl σ) :=
    fun i hi c h1 h2 => hRHP (hgen.fixedX i hi c h1 h2)
  have hfixY : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → η c = c →
      xE6 (-Pi.single i 1) c ∈ H.map (twIncl σ) :=
    fun i hi c h1 h2 => hRHP (hgen.fixedY i hi c h1 h2)
  have hw : ∀ i ∈ ({1, 3} : Finset (Fin 6)),
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) ∈
        H.map (twIncl σ) := by
    intro i hi
    unfold CFSG.LieType.Steinberg.weylElement
    simp only [inv_one, Units.val_one]
    exact (H.map (twIncl σ)).mul_mem
      ((H.map (twIncl σ)).mul_mem (hfixX i hi 1 (by simp) (by simp))
        (hfixY i hi (-1) (by simp) (by simp)))
      (hfixX i hi 1 (by simp) (by simp))
  have hw1 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6))
      (1 : Fin Tag.E6.rank) (1 : Kˣ) ∈ H.map (twIncl σ) := hw 1 (by decide)
  have hw3 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6))
      (3 : Fin Tag.E6.rank) (1 : Kˣ) ∈ H.map (twIncl σ) := hw 3 (by decide)
  have h13 : Tag.E6.cartan 1 3 = -1 := by decide
  have h31 : Tag.E6.cartan 3 1 = -1 := by decide
  obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_neighbour (K := K) (D := e6AdjData)
    e6AdjData_valid noG2_E6 h31 h13
  let A : Subring ↥(fixSubfield σ) :=
    { carrier := {u | xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ)}
      mul_mem' := fun {u v} hu hv => by
        have hu' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ) := hu
        have hv' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (v : K) ∈ H.map (twIncl σ) := hv
        have ha := (twE6_neighbour_one_three (H.map (twIncl σ)) hw1 hw3 (u : K)).mp hu'
        have hm := xPar_mul_mem_of_commutator (H.map (twIncl σ)) hε hcomm ha hv'
        rw [add_comm] at hm
        exact (twE6_mem_e13_iff (H.map (twIncl σ)) hw1 ((u : K) * (v : K))).mpr hm
      one_mem' := by
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((1 : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [OneMemClass.coe_one]
        exact hfixX 3 (by decide) 1 (by simp) (by simp)
      add_mem' := fun {u v} hu hv => by
        have hu' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ) := hu
        have hv' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (v : K) ∈ H.map (twIncl σ) := hv
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((u + v : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [AddMemClass.coe_add, xPar_add]
        exact (H.map (twIncl σ)).mul_mem hu' hv'
      zero_mem' := by
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((0 : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [ZeroMemClass.coe_zero, xPar_zero]
        exact (H.map (twIncl σ)).one_mem
      neg_mem' := fun {u} hu => by
        have hu' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ) := hu
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((-u : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [NegMemClass.coe_neg, ← xPar_neg]
        exact (H.map (twIncl σ)).inv_mem hu' }
  have htF : t ∈ fixSubfield σ := hσt
  have hk : ∀ F' : Subfield ↥(fixSubfield σ), fixSubfield (fixSubfieldRestrict η σ) ≤ F' →
      F' = fixSubfield (fixSubfieldRestrict η σ) ∨ F' = ⊤ :=
    fun F' hF' => subfield_eq_or_top (fixSubfieldRestrict η σ) hS.prime
      (TwE6Setup.orderOf_restrict hS) F' hF'
  have hkS : ∀ c ∈ fixSubfield (fixSubfieldRestrict η σ), c ∈ A := by
    intro c hc
    rw [mem_fixSubfield] at hc
    have hηc : η (c : K) = (c : K) := by
      have h := congrArg Subtype.val hc
      rw [coe_fixSubfieldRestrict] at h
      exact h
    exact hfixX 3 (by decide) (c : K) c.2 hηc
  have ht : (⟨t, htF⟩ : ↥(fixSubfield σ)) ∉ fixSubfield (fixSubfieldRestrict η σ) := by
    intro h
    rw [mem_fixSubfield] at h
    apply hηt
    have h' := congrArg Subtype.val h
    rw [coe_fixSubfieldRestrict] at h'
    exact h'
  have htA : (⟨t, htF⟩ : ↥(fixSubfield σ)) ∈ A := hmem
  have hA : A = ⊤ := eq_top_of_subring (fixSubfield (fixSubfieldRestrict η σ)) hk A hkS ht htA
  intro i hi c hc
  have hcA : (⟨c, (show c ∈ fixSubfield σ from hc)⟩ : ↥(fixSubfield σ)) ∈ A := by
    rw [hA]
    exact Subring.mem_top _
  have h3 : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) c ∈ H.map (twIncl σ) := hcA
  have h1 : xPar (rootOperatorFamily Tag.E6) (Pi.single 1 1) c ∈ H.map (twIncl σ) :=
    (twE6_neighbour_one_three (H.map (twIncl σ)) hw1 hw3 c).mp h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · refine ⟨h1, ?_⟩
    have h := (twE6_mem_reflect_node (H.map (twIncl σ)) hw1 (isRoot_single Tag.E6 1) c).mp h1
    rwa [twE6_reflect_self 1] at h
  · refine ⟨h3, ?_⟩
    have h := (twE6_mem_reflect_node (H.map (twIncl σ)) hw3 (isRoot_single Tag.E6 3) c).mp h3
    rwa [twE6_reflect_self 3] at h

private theorem alp_nr_2_4 : ¬ IsRoot Tag.E6 (Pi.single 2 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) :=
  fun h => (by decide +kernel :
    (Pi.single 2 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6) (mem_rootFinset.2 h)

private theorem alp_nr_4_m2 : ¬ IsRoot Tag.E6 (Pi.single 4 1 + -Pi.single 2 1 : Fin Tag.E6.rank → ℤ) :=
  fun h => (by decide +kernel :
    (Pi.single 4 1 + -Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6) (mem_rootFinset.2 h)

private theorem alp_nr_m4_2 : ¬ IsRoot Tag.E6 (-Pi.single 4 1 + Pi.single 2 1 : Fin Tag.E6.rank → ℤ) :=
  fun h => (by decide +kernel :
    (-Pi.single 4 1 + Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6) (mem_rootFinset.2 h)

private theorem alp_nr_m2_m4 : ¬ IsRoot Tag.E6 (-Pi.single 2 1 + -Pi.single 4 1 : Fin Tag.E6.rank → ℤ) :=
  fun h => (by decide +kernel :
    (-Pi.single 2 1 + -Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6) (mem_rootFinset.2 h)

private theorem alp_nr_0_5 : ¬ IsRoot Tag.E6 (Pi.single 0 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) :=
  fun h => (by decide +kernel :
    (Pi.single 0 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6) (mem_rootFinset.2 h)

private theorem alp_nr_m0_m5 : ¬ IsRoot Tag.E6 (-Pi.single 0 1 + -Pi.single 5 1 : Fin Tag.E6.rank → ℤ) :=
  fun h => (by decide +kernel :
    (-Pi.single 0 1 + -Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∉ rootFinset Tag.E6) (mem_rootFinset.2 h)

private theorem alp_root_4_5 : IsRoot Tag.E6 (Pi.single 4 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) :=
  mem_rootFinset.1 (by decide +kernel)

private theorem alp_root_m4_m5 : IsRoot Tag.E6 (-Pi.single 4 1 + -Pi.single 5 1 : Fin Tag.E6.rank → ℤ) :=
  mem_rootFinset.1 (by decide +kernel)

private theorem alp_root_m0 : IsRoot Tag.E6 (-Pi.single 0 1 : Fin Tag.E6.rank → ℤ) :=
  mem_rootFinset.1 (by decide +kernel)

private theorem alp_root_m2 : IsRoot Tag.E6 (-Pi.single 2 1 : Fin Tag.E6.rank → ℤ) :=
  mem_rootFinset.1 (by decide +kernel)

private theorem alp_root_m4 : IsRoot Tag.E6 (-Pi.single 4 1 : Fin Tag.E6.rank → ℤ) :=
  mem_rootFinset.1 (by decide +kernel)

private theorem alp_root_m5 : IsRoot Tag.E6 (-Pi.single 5 1 : Fin Tag.E6.rank → ℤ) :=
  mem_rootFinset.1 (by decide +kernel)

private theorem alp_refl_4_0 :
    reflect Tag.E6 4 (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 := by decide +kernel

private theorem alp_refl_2_0 :
    reflect Tag.E6 2 (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 + Pi.single 2 1 := by
  decide +kernel

private theorem alp_refl_4_5 :
    reflect Tag.E6 4 (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1 + Pi.single 5 1 := by
  decide +kernel

private theorem alp_refl_2_45 :
    reflect Tag.E6 2 (Pi.single 4 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single 4 1 + Pi.single 5 1 := by
  decide +kernel

private theorem alp_refl_4_m0 :
    reflect Tag.E6 4 (-Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = -Pi.single 0 1 := by decide +kernel

private theorem alp_refl_2_m0 :
    reflect Tag.E6 2 (-Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = -Pi.single 0 1 + -Pi.single 2 1 := by
  decide +kernel

private theorem alp_refl_4_m5 :
    reflect Tag.E6 4 (-Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = -Pi.single 4 1 + -Pi.single 5 1 := by
  decide +kernel

private theorem alp_refl_2_m45 :
    reflect Tag.E6 2 (-Pi.single 4 1 + -Pi.single 5 1 : Fin Tag.E6.rank → ℤ) =
      -Pi.single 4 1 + -Pi.single 5 1 := by
  decide +kernel

private theorem alp_exp_2 :
    (∑ j, Tag.E6.cartan 3 j * (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) j) = -1 := by decide +kernel

private theorem alp_exp_4 :
    (∑ j, Tag.E6.cartan 3 j * (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) j) = -1 := by decide +kernel

private theorem alp_exp_02 :
    (∑ j, Tag.E6.cartan 3 j * (Pi.single 0 1 + Pi.single 2 1 : Fin Tag.E6.rank → ℤ) j) = -1 := by
  decide +kernel

private theorem alp_exp_45 :
    (∑ j, Tag.E6.cartan 3 j * (Pi.single 4 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) j) = -1 := by
  decide +kernel

private theorem alp_exp_m2 :
    (∑ j, Tag.E6.cartan 3 j * (-Pi.single 2 1 : Fin Tag.E6.rank → ℤ) j) = 1 := by decide +kernel

private theorem alp_exp_m4 :
    (∑ j, Tag.E6.cartan 3 j * (-Pi.single 4 1 : Fin Tag.E6.rank → ℤ) j) = 1 := by decide +kernel

private theorem alp_exp_m02 :
    (∑ j, Tag.E6.cartan 3 j * (-Pi.single 0 1 + -Pi.single 2 1 : Fin Tag.E6.rank → ℤ) j) = 1 := by
  decide +kernel

private theorem alp_exp_m45 :
    (∑ j, Tag.E6.cartan 3 j * (-Pi.single 4 1 + -Pi.single 5 1 : Fin Tag.E6.rank → ℤ) j) = 1 := by
  decide +kernel

private theorem alp_ne_2_4 : (Pi.single 2 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  decide +kernel

private theorem alp_ne_m2_m4 : (-Pi.single 2 1 + -Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  decide +kernel

private theorem alp_ne_4_m2 : (Pi.single 4 1 + -Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  decide +kernel

private theorem alp_ne_m4_2 : (-Pi.single 4 1 + Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  decide +kernel

private theorem alp_ne_0_5 : (Pi.single 0 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  decide +kernel

private theorem alp_ne_m0_m5 : (-Pi.single 0 1 + -Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  decide +kernel

private theorem alp_conj_mul {G : Type*} [Group G] (d X Y : G) :
    d * (X * Y) * d⁻¹ = (d * X * d⁻¹) * (d * Y * d⁻¹) := by
  group

private theorem alp_sq_of_pm {ε : K} (h : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> norm_num

private theorem alp_XYX {G : Type*} [Group G] {a b c d : G} (hbc : b * c = c * b) (hda : d * a = a * d)
    (hba : b * a = a * b) : (a * b) * (c * d) * (a * b) = (a * c * a) * (b * d * b) := by
  have h1 : ∀ Y : G, b * (c * Y) = c * (b * Y) := fun Y => by rw [← mul_assoc, hbc, mul_assoc]
  have h2 : ∀ Y : G, d * (a * Y) = a * (d * Y) := fun Y => by rw [← mul_assoc, hda, mul_assoc]
  have h3 : ∀ Y : G, b * (a * Y) = a * (b * Y) := fun Y => by rw [← mul_assoc, hba, mul_assoc]
  calc (a * b) * (c * d) * (a * b) = a * (b * (c * (d * (a * b)))) := by simp only [mul_assoc]
    _ = a * (c * (b * (d * (a * b)))) := by rw [h1]
    _ = a * (c * (b * (a * (d * b)))) := by rw [h2]
    _ = a * (c * (a * (b * (d * b)))) := by rw [h3]
    _ = (a * c * a) * (b * d * b) := by simp only [mul_assoc]

private theorem alp_commute {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ)
    (hne : γ + δ ≠ 0) (hn : ¬IsRoot Tag.E6 (γ + δ)) (a b : K) :
    Commute (xE6 γ a) (xE6 δ b) :=
  commute_xPar e6AdjData_valid noG2_E6 hγ hδ hne hn a b

private theorem alp_xE6_zero (γ : Fin Tag.E6.rank → ℤ) : xE6 γ (0 : K) = 1 := by
  simp only [xE6, xPar_zero]

private theorem alp_torus_xE6 (t : Kˣ) (γ : Fin Tag.E6.rank → ℤ) (u : K) :
    torusElement Tag.E6 K 3 t * xE6 γ u * (torusElement Tag.E6 K 3 t)⁻¹ =
      xE6 γ (((t ^ (∑ j, Tag.E6.cartan 3 j * γ j) : Kˣ) : K) * u) := by
  by_cases h : IsRoot Tag.E6 γ
  · simp only [xE6, xPar_of_isRoot h]
    exact (rootOperatorFamily Tag.E6).torusElement_mul_eltElement_mul_inv 3 t ⟨γ, h⟩ u
  · simp only [xE6, xPar_of_not_isRoot h, mul_one, mul_inv_cancel]

private theorem alp_torus_neg {γ : Fin Tag.E6.rank → ℤ} (s : K) (hs : s ≠ 0)
    (he : ∑ j, Tag.E6.cartan 3 j * γ j = -1) (u : K) :
    torusElement Tag.E6 K 3 (Units.mk0 s hs) * xE6 γ u *
      (torusElement Tag.E6 K 3 (Units.mk0 s hs))⁻¹ = xE6 γ (s⁻¹ * u) := by
  rw [alp_torus_xE6, he, zpow_neg_one, Units.val_inv_eq_inv_val, Units.val_mk0]

private theorem alp_torus_pos {γ : Fin Tag.E6.rank → ℤ} (s : K) (hs : s ≠ 0)
    (he : ∑ j, Tag.E6.cartan 3 j * γ j = 1) (u : K) :
    torusElement Tag.E6 K 3 (Units.mk0 s hs) * xE6 γ u *
      (torusElement Tag.E6 K 3 (Units.mk0 s hs))⁻¹ = xE6 γ (s * u) := by
  rw [alp_torus_xE6, he, zpow_one, Units.val_mk0]

private theorem alp_torus_mem {σ : K ≃+* K} {P : Subgroup ↥(adjointGroup Tag.E6 K)}
    (h3 : ∀ c : K, σ c = c → xE6 (Pi.single 3 1) c ∈ P ∧ xE6 (-Pi.single 3 1) c ∈ P)
    (t : Kˣ) (ht : σ (t : K) = t) : torusElement Tag.E6 K 3 t ∈ P := by
  have hw : ∀ u : Kˣ, σ (u : K) = u →
      CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 3 u ∈ P := by
    intro u hu
    unfold CFSG.LieType.Steinberg.weylElement
    refine P.mul_mem (P.mul_mem (h3 _ hu).1 (h3 _ ?_).2) (h3 _ hu).1
    simp only [map_neg, Units.val_inv_eq_inv_val, map_inv₀, hu]
  have e1 : torusElement Tag.E6 K 3 t =
      CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 3 t *
        (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 3 1)⁻¹ := by
    rw [weylElement_xPar, weylElement_xPar, torusElement_one_eq, one_mul, mul_inv_cancel_right]
  rw [e1]
  exact P.mul_mem (hw t ht) (P.inv_mem (hw 1 (by simp)))

private theorem alp_conj_back {N : ↥(adjointGroup Tag.E6 K)} {α β : Fin Tag.E6.rank → ℤ} {ε : K}
    (hε : ε * ε = 1) (h : ∀ v : K, N * xE6 α v * N⁻¹ = xE6 β (ε * v)) (w : K) :
    N⁻¹ * xE6 β w * N = xE6 α (ε * w) := by
  have h2 := h (ε * w)
  rw [show ε * (ε * w) = w by rw [← mul_assoc, hε, one_mul]] at h2
  rw [← h2]
  group

private theorem alp_conj_scale {N d : ↥(adjointGroup Tag.E6 K)} {α α' β β' : Fin Tag.E6.rank → ℤ}
    {ε ε' t : K} (hε : ε * ε = 1) (hε' : ε' * ε' = 1)
    (h0 : ∀ v : K, N * xE6 α v * N⁻¹ = xE6 β (ε * v))
    (h5 : ∀ v : K, N * xE6 α' v * N⁻¹ = xE6 β' (ε' * v))
    (hd : ∀ v : K, d * xE6 β v * d⁻¹ = xE6 β (t * v))
    (hd' : ∀ v : K, d * xE6 β' v * d⁻¹ = xE6 β' (t * v)) (v w : K) :
    (N⁻¹ * d * N) * (xE6 α v * xE6 α' w) * (N⁻¹ * d * N)⁻¹ =
      xE6 α (t * v) * xE6 α' (t * w) := by
  have e1 : (N⁻¹ * d * N) * (xE6 α v * xE6 α' w) * (N⁻¹ * d * N)⁻¹ =
      N⁻¹ * (d * ((N * xE6 α v * N⁻¹) * (N * xE6 α' w * N⁻¹)) * d⁻¹) * N := by group
  rw [e1, h0 v, h5 w]
  have e2 : d * (xE6 β (ε * v) * xE6 β' (ε' * w)) * d⁻¹ =
      (d * xE6 β (ε * v) * d⁻¹) * (d * xE6 β' (ε' * w) * d⁻¹) := by group
  rw [e2, hd, hd']
  have e3 : N⁻¹ * (xE6 β (t * (ε * v)) * xE6 β' (t * (ε' * w))) * N =
      (N⁻¹ * xE6 β (t * (ε * v)) * N) * (N⁻¹ * xE6 β' (t * (ε' * w)) * N) := by group
  rw [e3, alp_conj_back hε h0 (t * (ε * v)), alp_conj_back hε' h5 (t * (ε' * w))]
  have k1 : ε * (t * (ε * v)) = t * v := by linear_combination (t * v) * hε
  have k2 : ε' * (t * (ε' * w)) = t * w := by linear_combination (t * w) * hε'
  rw [k1, k2]

private theorem alp_scale_pair {σ : K ≃+* K} {P : Subgroup ↥(adjointGroup Tag.E6 K)}
    {N d : ↥(adjointGroup Tag.E6 K)} {α α' β β' : Fin Tag.E6.rank → ℤ} {ε ε' t : K}
    (hε : ε * ε = 1) (hε' : ε' * ε' = 1) (hN : N ∈ P) (hd : d ∈ P)
    (h0 : ∀ v : K, N * xE6 α v * N⁻¹ = xE6 β (ε * v))
    (h5 : ∀ v : K, N * xE6 α' v * N⁻¹ = xE6 β' (ε' * v))
    (hdβ : ∀ v : K, d * xE6 β v * d⁻¹ = xE6 β (t * v))
    (hdβ' : ∀ v : K, d * xE6 β' v * d⁻¹ = xE6 β' (t * v)) (hσt : σ t = t) (v : K)
    (hv : xE6 α v * xE6 α' (σ v) ∈ P) : xE6 α (t * v) * xE6 α' (σ (t * v)) ∈ P := by
  have hg : N⁻¹ * d * N ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hN) hd) hN
  have key := P.mul_mem (P.mul_mem hg hv) (P.inv_mem hg)
  rw [alp_conj_scale hε hε' h0 h5 hdβ hdβ' v (σ v)] at key
  rw [map_mul, hσt]
  exact key

private theorem alp_pair_add {σ : K ≃+* K} {P : Subgroup ↥(adjointGroup Tag.E6 K)}
    {γ δ : Fin Tag.E6.rank → ℤ} (hc : ∀ a b : K, Commute (xE6 γ a) (xE6 δ b)) {v w : K}
    (hv : xE6 γ v * xE6 δ (σ v) ∈ P) (hw : xE6 γ w * xE6 δ (σ w) ∈ P) :
    xE6 γ (v + w) * xE6 δ (σ (v + w)) ∈ P := by
  have key : xE6 γ (v + w) * xE6 δ (σ (v + w)) =
      (xE6 γ v * xE6 δ (σ v)) * (xE6 γ w * xE6 δ (σ w)) := by
    simp only [xE6]
    rw [map_add, xPar_add, xPar_add]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, (hc w (σ v)).eq, mul_assoc]
  rw [key]
  exact P.mul_mem hv hw

private theorem alp_decomp {σ : K ≃+* K} (hσ2 : ∀ x : K, σ (σ x) = x) {u : K} (hu : σ u ≠ u) (c : K) :
    ∃ a b : K, σ a = a ∧ σ b = b ∧ c = a + b * u := by
  have hu' : u - σ u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
  obtain ⟨b, hb⟩ : ∃ b : K, b = (c - σ c) * (u - σ u)⁻¹ := ⟨_, rfl⟩
  have hbu : b * (u - σ u) = c - σ c := by
    rw [hb]
    exact inv_mul_cancel_right₀ hu' (c - σ c)
  have hσb : σ b = b := by
    rw [hb, map_mul, map_sub, map_inv₀, map_sub, hσ2 c, hσ2 u,
      show σ c - c = -(c - σ c) by ring, show σ u - u = -(u - σ u) by ring, inv_neg]
    ring
  refine ⟨c - b * u, b, ?_, hσb, by ring⟩
  rw [map_sub, map_mul, hσb]
  linear_combination hbu

private theorem alp_span {σ : K ≃+* K} {P : Subgroup ↥(adjointGroup Tag.E6 K)}
    {γ δ : Fin Tag.E6.rank → ℤ} (hc : ∀ a b : K, Commute (xE6 γ a) (xE6 δ b))
    (hσ2 : ∀ x : K, σ (σ x) = x) {u₀ : K} (hu₀ : σ u₀ ≠ u₀)
    (hscale : ∀ τ : K, τ ≠ 0 → σ τ = τ → ∀ v : K,
      xE6 γ v * xE6 δ (σ v) ∈ P → xE6 γ (τ⁻¹ * v) * xE6 δ (σ (τ⁻¹ * v)) ∈ P)
    (h1 : xE6 γ 1 * xE6 δ (σ 1) ∈ P) (hu : xE6 γ u₀ * xE6 δ (σ u₀) ∈ P) (c : K) :
    xE6 γ c * xE6 δ (σ c) ∈ P := by
  have hfix : ∀ a : K, σ a = a → xE6 γ a * xE6 δ (σ a) ∈ P := by
    intro a ha
    rcases eq_or_ne a 0 with rfl | h0
    · rw [map_zero, alp_xE6_zero, alp_xE6_zero, mul_one]
      exact P.one_mem
    · have h := hscale a⁻¹ (inv_ne_zero h0) (by rw [map_inv₀, ha]) 1 h1
      rwa [inv_inv, mul_one] at h
  have hfixu : ∀ b : K, σ b = b → xE6 γ (b * u₀) * xE6 δ (σ (b * u₀)) ∈ P := by
    intro b hb
    rcases eq_or_ne b 0 with rfl | h0
    · rw [zero_mul, map_zero, alp_xE6_zero, alp_xE6_zero, mul_one]
      exact P.one_mem
    · have h := hscale b⁻¹ (inv_ne_zero h0) (by rw [map_inv₀, hb]) u₀ hu
      rwa [inv_inv] at h
  obtain ⟨a, b, ha, hb, hcab⟩ := alp_decomp hσ2 hu₀ c
  rw [hcab]
  exact alp_pair_add hc (hfix a ha) (hfixu b hb)

private theorem alp_W_conj (i : Fin Tag.E6.rank) {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ v : K,
      CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) i 1 *
          xE6 β v *
        (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) i 1)⁻¹ =
      xE6 (reflect Tag.E6 i β) (ε * v) := by
  obtain ⟨ε, hε, hc⟩ := weylElement_xPar_conj (K := K) (F := rootOperatorFamily Tag.E6) i hβ
  refine ⟨(ε : K), ?_, fun v => ?_⟩
  · rcases hε with rfl | rfl
    · left; simp
    · right; simp
  · have h := hc 1 v
    have h1 : (((1 : Kˣ) ^ (-(∑ j, Tag.E6.cartan i j * β j)) : Kˣ) : K) = 1 := by simp
    have h2 : CFSG.LieType.RootSystem.reflection Tag.E6.cartan i β = reflect Tag.E6 i β := by
      rw [CFSG.LieType.RootSystem.reflection_apply]
      rfl
    rw [h1, mul_one, h2] at h
    exact h

private theorem alp_N_conj {α α' β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h4 : reflect Tag.E6 4 α = α') (hα' : IsRoot Tag.E6 α') (h2 : reflect Tag.E6 2 α' = β) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ v : K,
      (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 2 1 *
          CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 4 1) *
        xE6 α v *
        (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 2 1 *
          CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 4 1)⁻¹ =
      xE6 β (ε * v) := by
  obtain ⟨ε₄, h₄, c₄⟩ := alp_W_conj (K := K) 4 hα
  obtain ⟨ε₂, h₂, c₂⟩ := alp_W_conj (K := K) 2 hα'
  refine ⟨ε₂ * ε₄, ?_, fun v => ?_⟩
  · rcases h₂ with rfl | rfl <;> rcases h₄ with rfl | rfl <;> norm_num
  · have e : (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 2 1 *
          CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 4 1) *
        xE6 α v *
        (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 2 1 *
          CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 4 1)⁻¹ =
        CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 2 1 *
          (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 4 1 *
            xE6 α v *
            (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 4 1)⁻¹) *
          (CFSG.LieType.Steinberg.weylElement (xPar (K := K) (rootOperatorFamily Tag.E6)) 2 1)⁻¹ := by
      group
    rw [e, c₄ v, h4, c₂ (ε₄ * v), h2, mul_assoc]

private theorem alp_sigma_invol (hS : TwE6Setup K σ η p) : ∀ x : K, σ (σ x) = x := by
  intro x
  have h := congrArg (fun f : K ≃+* K => f x) hS.sigma_sq
  simpa [sq] using h

private theorem alp_N_mem {P : Subgroup ↥(adjointGroup Tag.E6 K)}
    (hab : xE6 (Pi.single 2 1) (1 : K) * xE6 (Pi.single 4 1) (1 : K) ∈ P)
    (hcd : xE6 (-Pi.single 2 1) (-1 : K) * xE6 (-Pi.single 4 1) (-1 : K) ∈ P) :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 2 (1 : Kˣ) *
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 4 (1 : Kˣ) ∈ P := by
  have hbc : xE6 (Pi.single 4 1) (1 : K) * xE6 (-Pi.single 2 1) (-1 : K) =
      xE6 (-Pi.single 2 1) (-1 : K) * xE6 (Pi.single 4 1) (1 : K) :=
    (alp_commute (isRoot_single Tag.E6 4) alp_root_m2 alp_ne_4_m2
      alp_nr_4_m2 (1 : K) (-1 : K)).eq
  have hda : xE6 (-Pi.single 4 1) (-1 : K) * xE6 (Pi.single 2 1) (1 : K) =
      xE6 (Pi.single 2 1) (1 : K) * xE6 (-Pi.single 4 1) (-1 : K) :=
    (alp_commute alp_root_m4 (isRoot_single Tag.E6 2) alp_ne_m4_2
      alp_nr_m4_2 (-1 : K) (1 : K)).eq
  have hba : xE6 (Pi.single 4 1) (1 : K) * xE6 (Pi.single 2 1) (1 : K) =
      xE6 (Pi.single 2 1) (1 : K) * xE6 (Pi.single 4 1) (1 : K) :=
    (alp_commute (isRoot_single Tag.E6 2) (isRoot_single Tag.E6 4) alp_ne_2_4 alp_nr_2_4
      (1 : K) (1 : K)).eq.symm
  have e := alp_XYX hbc hda hba
  have e2 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 2 (1 : Kˣ) *
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) 4 (1 : Kˣ) =
      (xE6 (Pi.single 2 1) (1 : K) * xE6 (-Pi.single 2 1) (-1 : K) * xE6 (Pi.single 2 1) (1 : K)) *
        (xE6 (Pi.single 4 1) (1 : K) * xE6 (-Pi.single 4 1) (-1 : K) *
          xE6 (Pi.single 4 1) (1 : K)) := by
    unfold CFSG.LieType.Steinberg.weylElement
    simp only [inv_one, Units.val_one]
  rw [e2, ← e]
  exact P.mul_mem (P.mul_mem hab hcd) hab

theorem twE6_short_full_one (hS : TwE6Setup K σ η p) (H : Subgroup ↥(twistedE6RootGroup K σ))
    (hRH : twR σ η ≤ H)
    (hlong : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c →
      xE6 (Pi.single i 1) c ∈ H.map (twIncl σ) ∧ xE6 (-Pi.single i 1) c ∈ H.map (twIncl σ)) :
    ∀ c : K, xE6 (Pi.single 2 1) c * xE6 (Pi.single 4 1) (σ c) ∈ H.map (twIncl σ) ∧
      xE6 (-Pi.single 2 1) c * xE6 (-Pi.single 4 1) (σ c) ∈ H.map (twIncl σ) := by
  have hgen : TwGens σ η (twRP σ η) := twR_gens hS
  have hRHP : twRP σ η ≤ H.map (twIncl σ) := Subgroup.map_mono hRH
  have h3 : ∀ c : K, σ c = c → xE6 (Pi.single 3 1) c ∈ H.map (twIncl σ) ∧
      xE6 (-Pi.single 3 1) c ∈ H.map (twIncl σ) := hlong 3 (by decide)
  have hσ2 := alp_sigma_invol hS
  obtain ⟨u₀, hηu₀, hσu₀⟩ := hS.exists_fixEta_not_fixSigma
  have hX : ∀ c : K, η c = c → xE6 (Pi.single 2 1) c * xE6 (Pi.single 4 1) (σ c) ∈
      H.map (twIncl σ) :=
    fun c hc => hRHP (hgen.orbX (2, 4) (by decide) c hc)
  have hY : ∀ c : K, η c = c → xE6 (-Pi.single 2 1) c * xE6 (-Pi.single 4 1) (σ c) ∈
      H.map (twIncl σ) :=
    fun c hc => hRHP (hgen.orbY (2, 4) (by decide) c hc)
  have hcX : ∀ a b : K, Commute (xE6 (Pi.single 2 1) a) (xE6 (Pi.single 4 1) b) :=
    fun a b => alp_commute (isRoot_single Tag.E6 2) (isRoot_single Tag.E6 4) alp_ne_2_4
      alp_nr_2_4 a b
  have hcY : ∀ a b : K, Commute (xE6 (-Pi.single 2 1) a) (xE6 (-Pi.single 4 1) b) :=
    fun a b => alp_commute alp_root_m2 alp_root_m4
      alp_ne_m2_m4 alp_nr_m2_m4 a b
  have hscX : ∀ τ : K, τ ≠ 0 → σ τ = τ → ∀ v : K,
      xE6 (Pi.single 2 1) v * xE6 (Pi.single 4 1) (σ v) ∈ H.map (twIncl σ) →
      xE6 (Pi.single 2 1) (τ⁻¹ * v) * xE6 (Pi.single 4 1) (σ (τ⁻¹ * v)) ∈ H.map (twIncl σ) := by
    intro τ hτ hστ v hv
    have hd : torusElement Tag.E6 K 3 (Units.mk0 τ hτ) ∈ H.map (twIncl σ) :=
      alp_torus_mem h3 (Units.mk0 τ hτ) (by rw [Units.val_mk0]; exact hστ)
    have key := (H.map (twIncl σ)).mul_mem ((H.map (twIncl σ)).mul_mem hd hv)
      ((H.map (twIncl σ)).inv_mem hd)
    rw [map_mul, map_inv₀, hστ]
    rw [alp_conj_mul, alp_torus_neg τ hτ alp_exp_2, alp_torus_neg τ hτ alp_exp_4] at key
    exact key
  have hscY : ∀ τ : K, τ ≠ 0 → σ τ = τ → ∀ v : K,
      xE6 (-Pi.single 2 1) v * xE6 (-Pi.single 4 1) (σ v) ∈ H.map (twIncl σ) →
      xE6 (-Pi.single 2 1) (τ⁻¹ * v) * xE6 (-Pi.single 4 1) (σ (τ⁻¹ * v)) ∈
        H.map (twIncl σ) := by
    intro τ hτ hστ v hv
    have hτi : τ⁻¹ ≠ 0 := inv_ne_zero hτ
    have hστi : σ (τ⁻¹) = τ⁻¹ := by rw [map_inv₀, hστ]
    have hd : torusElement Tag.E6 K 3 (Units.mk0 (τ⁻¹) hτi) ∈ H.map (twIncl σ) :=
      alp_torus_mem h3 (Units.mk0 (τ⁻¹) hτi) (by rw [Units.val_mk0]; exact hστi)
    have key := (H.map (twIncl σ)).mul_mem ((H.map (twIncl σ)).mul_mem hd hv)
      ((H.map (twIncl σ)).inv_mem hd)
    rw [map_mul, map_inv₀, hστ]
    rw [alp_conj_mul, alp_torus_pos (τ⁻¹) hτi alp_exp_m2, alp_torus_pos (τ⁻¹) hτi alp_exp_m4]
      at key
    exact key
  intro c
  exact ⟨alp_span hcX hσ2 hσu₀ hscX (hX 1 (by simp)) (hX u₀ hηu₀) c,
    alp_span hcY hσ2 hσu₀ hscY (hY 1 (by simp)) (hY u₀ hηu₀) c⟩

theorem twE6_short_full_zero (hS : TwE6Setup K σ η p) (H : Subgroup ↥(twistedE6RootGroup K σ))
    (hRH : twR σ η ≤ H)
    (hlong : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c →
      xE6 (Pi.single i 1) c ∈ H.map (twIncl σ) ∧ xE6 (-Pi.single i 1) c ∈ H.map (twIncl σ))
    (hone : ∀ c : K, xE6 (Pi.single 2 1) c * xE6 (Pi.single 4 1) (σ c) ∈ H.map (twIncl σ) ∧
      xE6 (-Pi.single 2 1) c * xE6 (-Pi.single 4 1) (σ c) ∈ H.map (twIncl σ)) :
    ∀ c : K, xE6 (Pi.single 0 1) c * xE6 (Pi.single 5 1) (σ c) ∈ H.map (twIncl σ) ∧
      xE6 (-Pi.single 0 1) c * xE6 (-Pi.single 5 1) (σ c) ∈ H.map (twIncl σ) := by
  have hgen : TwGens σ η (twRP σ η) := twR_gens hS
  have hRHP : twRP σ η ≤ H.map (twIncl σ) := Subgroup.map_mono hRH
  have h3 : ∀ c : K, σ c = c → xE6 (Pi.single 3 1) c ∈ H.map (twIncl σ) ∧
      xE6 (-Pi.single 3 1) c ∈ H.map (twIncl σ) := hlong 3 (by decide)
  have hσ2 := alp_sigma_invol hS
  obtain ⟨u₀, hηu₀, hσu₀⟩ := hS.exists_fixEta_not_fixSigma
  have hX : ∀ c : K, η c = c → xE6 (Pi.single 0 1) c * xE6 (Pi.single 5 1) (σ c) ∈
      H.map (twIncl σ) :=
    fun c hc => hRHP (hgen.orbX (0, 5) (by decide) c hc)
  have hY : ∀ c : K, η c = c → xE6 (-Pi.single 0 1) c * xE6 (-Pi.single 5 1) (σ c) ∈
      H.map (twIncl σ) :=
    fun c hc => hRHP (hgen.orbY (0, 5) (by decide) c hc)
  have hcX : ∀ a b : K, Commute (xE6 (Pi.single 0 1) a) (xE6 (Pi.single 5 1) b) :=
    fun a b => alp_commute (isRoot_single Tag.E6 0) (isRoot_single Tag.E6 5) alp_ne_0_5
      alp_nr_0_5 a b
  have hcY : ∀ a b : K, Commute (xE6 (-Pi.single 0 1) a) (xE6 (-Pi.single 5 1) b) :=
    fun a b => alp_commute alp_root_m0 alp_root_m5
      alp_ne_m0_m5 alp_nr_m0_m5 a b
  have hab : xE6 (Pi.single 2 1) (1 : K) * xE6 (Pi.single 4 1) (1 : K) ∈ H.map (twIncl σ) := by
    have h := (hone 1).1
    rwa [map_one] at h
  have hcd : xE6 (-Pi.single 2 1) (-1 : K) * xE6 (-Pi.single 4 1) (-1 : K) ∈
      H.map (twIncl σ) := by
    have h := (hone (-1)).2
    rwa [map_neg, map_one] at h
  have hN := alp_N_mem hab hcd
  obtain ⟨ε₀, hε₀, h0⟩ := alp_N_conj (K := K) (isRoot_single Tag.E6 0) alp_refl_4_0
    (isRoot_single Tag.E6 0) alp_refl_2_0
  obtain ⟨ε₅, hε₅, h5⟩ := alp_N_conj (K := K) (isRoot_single Tag.E6 5) alp_refl_4_5
    alp_root_4_5 alp_refl_2_45
  obtain ⟨ε₀', hε₀', h0'⟩ := alp_N_conj (K := K) alp_root_m0 alp_refl_4_m0
    alp_root_m0 alp_refl_2_m0
  obtain ⟨ε₅', hε₅', h5'⟩ := alp_N_conj (K := K) alp_root_m5 alp_refl_4_m5
    alp_root_m4_m5 alp_refl_2_m45
  have hscZ : ∀ τ : K, τ ≠ 0 → σ τ = τ → ∀ v : K,
      xE6 (Pi.single 0 1) v * xE6 (Pi.single 5 1) (σ v) ∈ H.map (twIncl σ) →
      xE6 (Pi.single 0 1) (τ⁻¹ * v) * xE6 (Pi.single 5 1) (σ (τ⁻¹ * v)) ∈ H.map (twIncl σ) := by
    intro τ hτ hστ v hv
    have hστi : σ (τ⁻¹) = τ⁻¹ := by rw [map_inv₀, hστ]
    have hd : torusElement Tag.E6 K 3 (Units.mk0 τ hτ) ∈ H.map (twIncl σ) :=
      alp_torus_mem h3 (Units.mk0 τ hτ) (by rw [Units.val_mk0]; exact hστ)
    exact alp_scale_pair (t := τ⁻¹) (alp_sq_of_pm hε₀) (alp_sq_of_pm hε₅) hN hd h0 h5
      (alp_torus_neg τ hτ alp_exp_02) (alp_torus_neg τ hτ alp_exp_45) hστi v hv
  have hscZ' : ∀ τ : K, τ ≠ 0 → σ τ = τ → ∀ v : K,
      xE6 (-Pi.single 0 1) v * xE6 (-Pi.single 5 1) (σ v) ∈ H.map (twIncl σ) →
      xE6 (-Pi.single 0 1) (τ⁻¹ * v) * xE6 (-Pi.single 5 1) (σ (τ⁻¹ * v)) ∈
        H.map (twIncl σ) := by
    intro τ hτ hστ v hv
    have hτi : τ⁻¹ ≠ 0 := inv_ne_zero hτ
    have hστi : σ (τ⁻¹) = τ⁻¹ := by rw [map_inv₀, hστ]
    have hd : torusElement Tag.E6 K 3 (Units.mk0 (τ⁻¹) hτi) ∈ H.map (twIncl σ) :=
      alp_torus_mem h3 (Units.mk0 (τ⁻¹) hτi) (by rw [Units.val_mk0]; exact hστi)
    exact alp_scale_pair (t := τ⁻¹) (alp_sq_of_pm hε₀') (alp_sq_of_pm hε₅') hN hd h0' h5'
      (alp_torus_pos (τ⁻¹) hτi alp_exp_m02) (alp_torus_pos (τ⁻¹) hτi alp_exp_m45) hστi v hv
  intro c
  exact ⟨alp_span hcX hσ2 hσu₀ hscZ (hX 1 (by simp)) (hX u₀ hηu₀) c,
    alp_span hcY hσ2 hσu₀ hscZ' (hY 1 (by simp)) (hY u₀ hηu₀) c⟩

theorem twE6_twFull_of_irrational (hS : TwE6Setup K σ η p) (H : Subgroup ↥(twistedE6RootGroup K σ))
    (hRH : twR σ η ≤ H) {t : K} (hσt : σ t = t) (hηt : η t ≠ t)
    (hmem : xE6 (Pi.single 3 1) t ∈ H.map (twIncl σ)) : TwFull σ (H.map (twIncl σ)) := by
  have hlong := twE6_long_full hS H hRH hσt hηt hmem
  have h1 := twE6_short_full_one hS H hRH hlong
  have h0 := twE6_short_full_zero hS H hRH hlong h1
  refine ⟨fun i hi c hc => (hlong i hi c hc).1, fun i hi c hc => (hlong i hi c hc).2, ?_, ?_⟩
  · intro ij hij c
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl
    · exact (h0 c).1
    · exact (h1 c).1
  · intro ij hij c
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl
    · exact (h0 c).2
    · exact (h1 c).2

theorem twE6_eq_top_of_irrational (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) (H : Subgroup ↥(twistedE6RootGroup K σ)) (hRH : twR σ η ≤ H)
    {t : K} (hσt : σ t = t) (hηt : η t ≠ t) (hmem : xE6 θ t ∈ H.map (twIncl σ)) : H = ⊤ := by
  obtain ⟨n, hn, ε, hε, hconj⟩ := twE6_theta_conj_simple hS hθ
  have hnP : twIncl σ n ∈ H.map (twIncl σ) := Subgroup.mem_map_of_mem _ (hRH hn)
  have h1 : xE6 (Pi.single 3 1) ((ε : K) * t) ∈ H.map (twIncl σ) := by
    rw [← hconj t]
    exact (H.map (twIncl σ)).mul_mem ((H.map (twIncl σ)).mul_mem hnP hmem)
      ((H.map (twIncl σ)).inv_mem hnP)
  have h2 : xE6 (Pi.single 3 1) t ∈ H.map (twIncl σ) := by
    rcases hε with rfl | rfl
    · simpa using h1
    · have h3 := (H.map (twIncl σ)).inv_mem h1
      rw [xE6, xPar_neg] at h3
      simpa using h3
  exact twE6_eq_top_of_twFull σ hS.sigma_sq H (twE6_twFull_of_irrational hS H hRH hσt hηt h2)

end Close

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
