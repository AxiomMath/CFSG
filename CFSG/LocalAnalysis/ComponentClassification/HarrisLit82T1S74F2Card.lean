module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F2Lin

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K]

noncomputable abbrev vZero (m : Fin 3 ⊕ Fin 3 ⊕ Unit → K) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  m - oddVec 3 K 0 false - polar (quadOdd 3 K) m (oddVec 3 K 0 false) • oddVec 3 K 0 true

noncomputable abbrev vOne (m : Fin 3 ⊕ Fin 3 ⊕ Unit → K) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  m - oddVec 3 K 1 false - polar (quadOdd 3 K) m (oddVec 3 K 0 false) • oddVec 3 K 0 true -
    polar (quadOdd 3 K) m (oddVec 3 K 1 false) • oddVec 3 K 1 true

theorem polar_single_inl_left (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (i : Fin 3) :
    polar (quadOdd 3 K) (Pi.single (.inl i) 1) v = v (.inr (.inl i)) := by
  rw [polar_comm, polar_quadOdd_single_inl]

theorem polar_single_inr_inl_left (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (i : Fin 3) :
    polar (quadOdd 3 K) (Pi.single (.inr (.inl i)) 1) v = v (.inl i) := by
  rw [polar_comm, polar_quadOdd_single_inr_inl]

section Pair

variable {m₀ m₁ : Fin 3 ⊕ Fin 3 ⊕ Unit → K}

theorem polar_vZero_eZero (h00 : polar (quadOdd 3 K) m₀ (oddVec 3 K 0 true) = 1) :
    polar (quadOdd 3 K) (vZero m₀) (oddVec 3 K 0 true) = 0 := by
  rw [polar_vecT] at h00 ⊢
  simp [vZero, h00]

theorem polar_vZero_eOne (h01 : polar (quadOdd 3 K) m₀ (oddVec 3 K 1 true) = 0) :
    polar (quadOdd 3 K) (vZero m₀) (oddVec 3 K 1 true) = 0 := by
  rw [polar_vecT] at h01 ⊢
  simp [vZero, h01]

theorem polar_vZero_fZero : polar (quadOdd 3 K) (vZero m₀) (oddVec 3 K 0 false) = 0 := by
  rw [polar_vecF]
  simp [vZero, polar_quadOdd_single_inr_inl]

theorem polar_vOne_eZero (h10 : polar (quadOdd 3 K) m₁ (oddVec 3 K 0 true) = 0) :
    polar (quadOdd 3 K) (vOne m₁) (oddVec 3 K 0 true) = 0 := by
  rw [polar_vecT] at h10 ⊢
  simp [vOne, h10]

theorem polar_vOne_eOne (h11 : polar (quadOdd 3 K) m₁ (oddVec 3 K 1 true) = 1) :
    polar (quadOdd 3 K) (vOne m₁) (oddVec 3 K 1 true) = 0 := by
  rw [polar_vecT] at h11 ⊢
  simp [vOne, h11]

theorem polar_vOne_fZero : polar (quadOdd 3 K) (vOne m₁) (oddVec 3 K 0 false) = 0 := by
  rw [polar_vecF]
  simp [vOne, polar_quadOdd_single_inr_inl]

theorem polar_vOne_fOne : polar (quadOdd 3 K) (vOne m₁) (oddVec 3 K 1 false) = 0 := by
  rw [polar_vecF]
  simp [vOne, polar_quadOdd_single_inr_inl]

theorem eichlerPair_vZero_vOne (h00 : polar (quadOdd 3 K) m₀ (oddVec 3 K 0 true) = 1)
    (h01 : polar (quadOdd 3 K) m₀ (oddVec 3 K 1 true) = 0)
    (h10 : polar (quadOdd 3 K) m₁ (oddVec 3 K 0 true) = 0)
    (h11 : polar (quadOdd 3 K) m₁ (oddVec 3 K 1 true) = 1) (hQ0 : quadOdd 3 K m₀ = 0)
    (hQ1 : quadOdd 3 K m₁ = 0) (hp : polar (quadOdd 3 K) m₀ m₁ = 0) :
    (eichler (quadOdd 3 K) (oddVec 3 K 0 true) (vZero m₀) *
        eichler (quadOdd 3 K) (oddVec 3 K 1 true) (vOne m₁)) (oddVec 3 K 0 false) = m₀ ∧
      (eichler (quadOdd 3 K) (oddVec 3 K 0 true) (vZero m₀) *
        eichler (quadOdd 3 K) (oddVec 3 K 1 true) (vOne m₁)) (oddVec 3 K 1 false) = m₁ := by
  have e00 := polar_vZero_eZero h00
  have e01 := polar_vZero_eOne h01
  have e0f := polar_vZero_fZero (m₀ := m₀)
  have e10 := polar_vOne_eZero h10
  have e11 := polar_vOne_eOne h11
  have e1f0 := polar_vOne_fZero (m₁ := m₁)
  have e1f1 := polar_vOne_fOne (m₁ := m₁)
  have hp' : polar (quadOdd 3 K) m₁ m₀ = 0 := by rw [polar_comm, hp]
  rw [polar_vecT] at h00 h01 h10 h11
  have hQy0 : quadOdd 3 K (vZero m₀) = -polar (quadOdd 3 K) m₀ (oddVec 3 K 0 false) := by
    rw [quadOdd_apply, Fin.sum_univ_three, polar_vecF]
    rw [quadOdd_apply, Fin.sum_univ_three] at hQ0
    simp [vZero, polar_quadOdd_single_inr_inl, h00, h01]
    linear_combination hQ0 - m₀ (.inl 0) * h00 - m₀ (.inl 1) * h01
  have hQy1 : quadOdd 3 K (vOne m₁) = -polar (quadOdd 3 K) m₁ (oddVec 3 K 1 false) := by
    rw [quadOdd_apply, Fin.sum_univ_three, polar_vecF]
    rw [quadOdd_apply, Fin.sum_univ_three] at hQ1
    simp [vOne, polar_quadOdd_single_inr_inl, h10, h11]
    linear_combination hQ1 - m₁ (.inl 0) * h10 - m₁ (.inl 1) * h11
  have hpp : polar (quadOdd 3 K) (oddVec 3 K 1 false) (vZero m₀) +
      polar (quadOdd 3 K) (vOne m₁) (vZero m₀) =
        -polar (quadOdd 3 K) m₁ (oddVec 3 K 0 false) := by
    simp only [vZero, vOne, polar_sub_left, polar_sub_right, polar_smul_left, polar_smul_right,
      hp', oddVec_true, oddVec_false, polar_quadOdd_single_inl, polar_quadOdd_single_inr_inl,
      polar_single_inl_left, polar_single_inr_inl_left, h00, h01, h10]
    simp
    try ring
  refine ⟨?_, ?_⟩
  · rw [eichlerPair_apply_fZero e00 e0f e1f0, hQy0]
    simp only [vZero]
    module
  · rw [eichlerPair_apply_fOne e00 e01 e10 e11 e1f1, hpp, hQy1]
    simp only [vOne]
    module

end Pair

theorem eq_one_of_mem_radU {g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hg : g ∈ radU K) (h0 : g (oddVec 3 K 0 false) = oddVec 3 K 0 false)
    (h1 : g (oddVec 3 K 1 false) = oddVec 3 K 1 false) : g = 1 := by
  obtain ⟨hgO, hg0, hg1, hgL⟩ := hg
  refine LinearEquiv.ext fun x => ?_
  show g x = x
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 ⊕ Fin 3 ⊕ Unit → K, c =
      polar (quadOdd 3 K) x (oddVec 3 K 0 false) • oddVec 3 K 0 true +
        polar (quadOdd 3 K) x (oddVec 3 K 1 false) • oddVec 3 K 1 true +
        polar (quadOdd 3 K) x (oddVec 3 K 0 true) • oddVec 3 K 0 false +
        polar (quadOdd 3 K) x (oddVec 3 K 1 true) • oddVec 3 K 1 false := ⟨_, rfl⟩
  have hgc : g c = c := by
    rw [hc, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hg0, hg1, h0, h1]
  have hpc : ∀ i (s : Bool), i ≠ 2 →
      polar (quadOdd 3 K) (x - c) (oddVec 3 K i s) = 0 := by
    intro i s hi
    rw [hc]
    fin_cases i <;> cases s <;> simp [polar_sub_left, polar_add_left, polar_smul_left,
      polar_quadOdd_single_inl, polar_quadOdd_single_inr_inl, quadOdd_single_inl,
      quadOdd_single_inr] at hi ⊢
  obtain ⟨a, b, hab⟩ := mem_planeL.mp (hgL (x - c) (hpc 0 true (by decide))
    (hpc 1 true (by decide)))
  have hf : ∀ i : Fin 3, i ≠ 2 →
      polar (quadOdd 3 K) (g (x - c) - (x - c)) (oddVec 3 K i false) = 0 := by
    intro i hi
    have hgi : g (oddVec 3 K i false) = oddVec 3 K i false := by
      fin_cases i
      · exact h0
      · exact h1
      · exact absurd rfl hi
    rw [polar_sub_left, ← hgi, polar_apply_of_map hgO, hgi, sub_self]
  have ha : a = 0 := by
    have := hf 0 (by decide)
    rw [← hab] at this
    simpa [polar_add_left, polar_smul_left, polar_quadOdd_single_inl,
        polar_quadOdd_single_inr_inl, polar_quadOdd_single_inr_inr,
      Pi.single_apply] using this
  have hb : b = 0 := by
    have := hf 1 (by decide)
    rw [← hab] at this
    simpa [polar_add_left, polar_smul_left, polar_quadOdd_single_inl,
        polar_quadOdd_single_inr_inl, polar_quadOdd_single_inr_inr,
      Pi.single_apply] using this
  rw [ha, hb, zero_smul, zero_smul, add_zero] at hab
  have hgr : g (x - c) = x - c := (sub_eq_zero.mp hab.symm)
  calc g x = g (x - c) + g c := by rw [← map_add, sub_add_cancel]
    _ = x := by rw [hgr, hgc, sub_add_cancel]

abbrev yZero (c : Fin 7 → K) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  c 0 • oddVec 3 K 1 true + c 1 • oddVec 3 K 2 true + c 2 • oddVec 3 K 2 false + c 3 • oddZ 3 K

abbrev yOne (c : Fin 7 → K) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  c 4 • oddVec 3 K 2 true + c 5 • oddVec 3 K 2 false + c 6 • oddZ 3 K

noncomputable abbrev uMap (c : Fin 7 → K) :
    (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  eichler (quadOdd 3 K) (oddVec 3 K 0 true) (yZero c) *
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (yOne c)

theorem uMap_mem (c : Fin 7 → K) : uMap c ∈ radU K := by
  refine mul_mem (eichler_mem_radU (mem_planeL.mpr ⟨1, 0, by simp⟩) ?_ ?_)
    (eichler_mem_radU (mem_planeL.mpr ⟨0, 1, by simp⟩) ?_ ?_) <;>
    (rw [polar_vecT]; simp [yZero, yOne, oddZ])

abbrev pairCoords (m₀ m₁ : Fin 3 ⊕ Fin 3 ⊕ Unit → K) : Fin 7 → K :=
  ![m₀ (.inl 1), m₀ (.inl 2), m₀ (.inr (.inl 2)), m₀ (.inr (.inr ())), m₁ (.inl 2),
    m₁ (.inr (.inl 2)), m₁ (.inr (.inr ()))]

theorem yZero_pairCoords {m₀ m₁ : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (h00 : polar (quadOdd 3 K) m₀ (oddVec 3 K 0 true) = 1)
    (h01 : polar (quadOdd 3 K) m₀ (oddVec 3 K 1 true) = 0) :
    yZero (pairCoords m₀ m₁) = vZero m₀ := by
  rw [polar_vecT] at h00 h01
  funext σ
  rcases σ with i | i | ⟨⟩
  · fin_cases i <;> simp [yZero, vZero, pairCoords, oddZ, polar_quadOdd_single_inr_inl]
  · fin_cases i <;> simp [yZero, vZero, pairCoords, oddZ, polar_quadOdd_single_inr_inl, h00, h01]
  · simp [yZero, vZero, pairCoords, oddZ, polar_quadOdd_single_inr_inl]

theorem yOne_pairCoords {m₀ m₁ : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (h10 : polar (quadOdd 3 K) m₁ (oddVec 3 K 0 true) = 0)
    (h11 : polar (quadOdd 3 K) m₁ (oddVec 3 K 1 true) = 1) :
    yOne (pairCoords m₀ m₁) = vOne m₁ := by
  rw [polar_vecT] at h10 h11
  funext σ
  rcases σ with i | i | ⟨⟩
  · fin_cases i <;> simp [yOne, vOne, pairCoords, oddZ, polar_quadOdd_single_inr_inl]
  · fin_cases i <;> simp [yOne, vOne, pairCoords, oddZ, polar_quadOdd_single_inr_inl, h10, h11]
  · simp [yOne, vOne, pairCoords, oddZ, polar_quadOdd_single_inr_inl]

theorem pairCoords_uMap (c : Fin 7 → K) :
    pairCoords (uMap c (oddVec 3 K 0 false)) (uMap c (oddVec 3 K 1 false)) = c := by
  have h0 : uMap c (oddVec 3 K 0 false) = oddVec 3 K 0 false + yZero c -
      quadOdd 3 K (yZero c) • oddVec 3 K 0 true :=
    eichlerPair_apply_fZero (by rw [polar_vecT]; simp [yZero, oddZ])
      (by rw [polar_vecF]; simp [yZero, oddZ]) (by rw [polar_vecF]; simp [yOne, oddZ])
  have h1 : uMap c (oddVec 3 K 1 false) = oddVec 3 K 1 false + yOne c -
      (polar (quadOdd 3 K) (oddVec 3 K 1 false) (yZero c) +
        polar (quadOdd 3 K) (yOne c) (yZero c)) • oddVec 3 K 0 true -
      quadOdd 3 K (yOne c) • oddVec 3 K 1 true :=
    eichlerPair_apply_fOne (by rw [polar_vecT]; simp [yZero, oddZ])
      (by rw [polar_vecT]; simp [yZero, oddZ]) (by rw [polar_vecT]; simp [yOne, oddZ])
      (by rw [polar_vecT]; simp [yOne, oddZ]) (by rw [polar_vecF]; simp [yOne, oddZ])
  rw [h0, h1]
  funext i
  fin_cases i <;> simp [pairCoords, yZero, yOne, oddZ]

theorem uMap_pairCoords {g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hg : g ∈ radU K) :
    uMap (pairCoords (g (oddVec 3 K 0 false)) (g (oddVec 3 K 1 false))) = g := by
  have hg' := hg
  obtain ⟨hgO, hg0, hg1, -⟩ := hg'
  have a00 : polar (quadOdd 3 K) (g (oddVec 3 K 0 false)) (oddVec 3 K 0 true) = 1 := by
    rw [← hg0, polar_apply_of_map hgO, polar_quadOdd_oddVec]
    simp
  have a01 : polar (quadOdd 3 K) (g (oddVec 3 K 0 false)) (oddVec 3 K 1 true) = 0 := by
    rw [← hg1, polar_apply_of_map hgO, polar_quadOdd_oddVec]
    simp
  have a10 : polar (quadOdd 3 K) (g (oddVec 3 K 1 false)) (oddVec 3 K 0 true) = 0 := by
    rw [← hg0, polar_apply_of_map hgO, polar_quadOdd_oddVec]
    simp
  have a11 : polar (quadOdd 3 K) (g (oddVec 3 K 1 false)) (oddVec 3 K 1 true) = 1 := by
    rw [← hg1, polar_apply_of_map hgO, polar_quadOdd_oddVec]
    simp
  have hQ0 : quadOdd 3 K (g (oddVec 3 K 0 false)) = 0 := by rw [hgO, quadOdd_oddVec]
  have hQ1 : quadOdd 3 K (g (oddVec 3 K 1 false)) = 0 := by rw [hgO, quadOdd_oddVec]
  have hp : polar (quadOdd 3 K) (g (oddVec 3 K 0 false)) (g (oddVec 3 K 1 false)) = 0 := by
    rw [polar_apply_of_map hgO, polar_quadOdd_oddVec]
    simp
  obtain ⟨hf0, hf1⟩ := eichlerPair_vZero_vOne a00 a01 a10 a11 hQ0 hQ1 hp
  have hu : uMap (pairCoords (g (oddVec 3 K 0 false)) (g (oddVec 3 K 1 false))) =
      eichler (quadOdd 3 K) (oddVec 3 K 0 true) (vZero (g (oddVec 3 K 0 false))) *
        eichler (quadOdd 3 K) (oddVec 3 K 1 true) (vOne (g (oddVec 3 K 1 false))) := by
    show eichler (quadOdd 3 K) (oddVec 3 K 0 true) (yZero _) *
      eichler (quadOdd 3 K) (oddVec 3 K 1 true) (yOne _) = _
    rw [yZero_pairCoords a00 a01, yOne_pairCoords a10 a11]
  rw [← hu] at hf0 hf1
  have h := eq_one_of_mem_radU (mul_mem (inv_mem (uMap_mem
      (pairCoords (g (oddVec 3 K 0 false)) (g (oddVec 3 K 1 false))))) hg)
    (by rw [LinearEquiv.mul_apply]; exact (LinearEquiv.symm_apply_eq _).mpr hf0.symm)
    (by rw [LinearEquiv.mul_apply]; exact (LinearEquiv.symm_apply_eq _).mpr hf1.symm)
  exact inv_mul_eq_one.mp h

theorem card_radU [Finite K] : Nat.card (radU K) = Nat.card K ^ 7 := by
  let φ : (Fin 7 → K) → radU K := fun c => ⟨uMap c, uMap_mem c⟩
  have hinj : Function.Injective φ := fun c d h => by
    have h' : uMap c = uMap d := congrArg Subtype.val h
    calc c = pairCoords (uMap c (oddVec 3 K 0 false)) (uMap c (oddVec 3 K 1 false)) :=
          (pairCoords_uMap c).symm
      _ = pairCoords (uMap d (oddVec 3 K 0 false)) (uMap d (oddVec 3 K 1 false)) := by rw [h']
      _ = d := pairCoords_uMap d
  have hsurj : Function.Surjective φ := fun g => ⟨_, Subtype.ext (uMap_pairCoords g.2)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), Nat.card_fun, Nat.card_fin]

end CFSG.ComponentClassification.HarrisLit.T1.S74
