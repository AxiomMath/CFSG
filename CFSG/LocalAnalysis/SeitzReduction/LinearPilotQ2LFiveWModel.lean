module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def pointRadMat (c : Fin n) (r : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 + vecMulVec (Pi.single c 1) (Function.update r c 0)

theorem pointRadMat_apply (c : Fin n) (r : Fin n → K) (i j : Fin n) :
    pointRadMat c r i j = (1 : Matrix (Fin n) (Fin n) K) i j + if i = c ∧ j ≠ c then r j else 0 := by
  simp only [pointRadMat, Matrix.add_apply, vecMulVec_apply, Pi.single_apply, Function.update_apply]
  by_cases hi : i = c <;> by_cases hj : j = c <;> simp [hi, hj]

theorem det_pointRadMat (c : Fin n) (r : Fin n → K) : (pointRadMat c r).det = 1 := by
  rw [pointRadMat, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_single,
    Function.update_self, zero_mul, add_zero]

theorem pointRadMat_mul (c : Fin n) (r s : Fin n → K) :
    pointRadMat c r * pointRadMat c s = pointRadMat c (r + s) := by
  have hupd : Function.update (r + s) c 0 = Function.update r c 0 + Function.update s c 0 := by
    ext j
    by_cases hj : j = c
    · subst hj
      simp
    · simp [hj]
  simp only [pointRadMat, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    vecMulVec_mul_vecMulVec, dotProduct_single, Function.update_self, zero_mul, zero_smul,
    vecMulVec_zero, add_zero, hupd, vecMulVec_add]
  abel

@[expose] def pointRadElem (c : Fin n) (r : Fin n → K) : SpecialLinearGroup (Fin n) K :=
  ⟨pointRadMat c r, det_pointRadMat c r⟩

theorem coe_pointRadElem (c : Fin n) (r : Fin n → K) :
    ((pointRadElem c r : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      pointRadMat c r :=
  rfl

theorem pointRadElem_mul (c : Fin n) (r s : Fin n → K) :
    pointRadElem c r * pointRadElem c s = pointRadElem c (r + s) :=
  Subtype.ext (pointRadMat_mul c r s)

theorem pointRadElem_zero (c : Fin n) : pointRadElem c (0 : Fin n → K) = 1 := by
  apply Subtype.ext
  ext i j
  rw [coe_pointRadElem, pointRadMat_apply, SpecialLinearGroup.coe_one]
  simp

@[expose] def pointRadSL (c : Fin n) (S : Finset (Fin n)) :
    Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | ∃ r : Fin n → K, (∀ j ∉ S, r j = 0) ∧ pointRadElem c r = A}
  mul_mem' := by
    rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨r + s, fun j hj => by simp [hr j hj, hs j hj], (pointRadElem_mul c r s).symm⟩
  one_mem' := ⟨0, fun _ _ => rfl, pointRadElem_zero c⟩
  inv_mem' := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨-r, fun j hj => by simp [hr j hj], ?_⟩
    exact eq_inv_of_mul_eq_one_left (by rw [pointRadElem_mul, neg_add_cancel, pointRadElem_zero])

theorem pointRadSL_mono (c : Fin n) {S T : Finset (Fin n)} (h : S ⊆ T) :
    pointRadSL (K := K) c S ≤ pointRadSL c T := by
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, fun j hj => hr j fun hjS => hj (h hjS), rfl⟩

theorem pointRadSL_le_blockSpecialLinear (c : Fin n) (S : Finset (Fin n)) :
    pointRadSL (K := K) c S ≤ blockSpecialLinear (insert c S) := by
  rintro _ ⟨r, hr, rfl⟩
  rw [mem_blockSpecialLinear]
  intro i j hij
  rw [coe_pointRadElem, pointRadMat_apply]
  by_cases h : i = c ∧ j ≠ c
  · rw [ite_eq_left h]
    obtain ⟨rfl, hj⟩ := h
    have hjS : j ∉ S := by
      rcases hij with hi | hj'
      · exact absurd (Finset.mem_insert_self i S) hi
      · exact fun hjS => hj' (Finset.mem_insert_of_mem hjS)
    rw [hr j hjS, add_zero]
  · rw [ite_eq_right h, add_zero]

@[expose] def pointRadOn (c : Fin n) (S : Finset (Fin n)) :
    Subgroup (LinearFlag.projectiveSL n K) :=
  (pointRadSL c S).map (LinearFlag.proj n K)

@[expose] def pointRadical (c : Fin n) : Subgroup (LinearFlag.projectiveSL n K) :=
  pointRadOn c ({c}ᶜ : Finset (Fin n))

theorem pointRadOn_mono (c : Fin n) {S T : Finset (Fin n)} (h : S ⊆ T) :
    pointRadOn (K := K) c S ≤ pointRadOn c T :=
  map_mono (pointRadSL_mono c h)

theorem pointRadOn_le_blockSL (c : Fin n) (S : Finset (Fin n)) :
    pointRadOn (K := K) c S ≤ blockSL (insert c S) := by
  rintro _ ⟨A, hA, rfl⟩
  exact proj_mem_blockSL (pointRadSL_le_blockSpecialLinear c S hA)

theorem pointRadOn_empty (c : Fin n) : pointRadOn (K := K) c (∅ : Finset (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  have hr0 : r = 0 := funext fun j => hr j (Finset.notMem_empty j)
  rw [hr0, pointRadElem_zero, map_one]
  exact one_mem _

theorem pointRadOn_mul_self [CharP K 2] (c : Fin n) (S : Finset (Fin n))
    {v : LinearFlag.projectiveSL n K} (hv : v ∈ pointRadOn c S) : v * v = 1 := by
  obtain ⟨_, ⟨r, -, rfl⟩, rfl⟩ := hv
  rw [← map_mul, pointRadElem_mul, show r + r = 0 from by
    ext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [← two_mul, CharTwo.two_eq_zero, zero_mul], pointRadElem_zero, map_one]

omit [Field K] in
theorem eq_zero_or_eq_one_of_natCard_eq_two [Field K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  rcases eq_or_ne x 0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (mul_left_cancel₀ h0 (h.trans (mul_one x).symm))

theorem proj_injective_of_natCard_eq_two (hK : Nat.card K = 2) :
    Function.Injective (LinearFlag.proj n K) := by
  rw [← MonoidHom.ker_eq_bot_iff, LinearFlag.ker_proj, eq_bot_iff]
  rintro A ⟨u, -, hA⟩
  rw [Subgroup.mem_bot]
  have hu : (u : K) = 1 :=
    (eq_zero_or_eq_one_of_natCard_eq_two hK (u : K)).resolve_left u.ne_zero
  apply Subtype.ext
  rw [hA, hu, map_one, SpecialLinearGroup.coe_one]

theorem card_pointRadOn (hK : Nat.card K = 2) (c : Fin n) {S : Finset (Fin n)} (hcS : c ∉ S) :
    Nat.card (pointRadOn (K := K) c S) = 2 ^ S.card := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  rw [pointRadOn, Subgroup.card_map_of_injective (proj_injective_of_natCard_eq_two hK)]
  classical
  let ext : (S → K) → Fin n → K := fun f j => if h : j ∈ S then f ⟨j, h⟩ else 0
  have hext : ∀ f, ∀ j ∉ S, ext f j = 0 := fun f j hj => by simp only [ext, dite_eq_right hj]
  let φ : (S → K) → pointRadSL (K := K) c S := fun f => ⟨pointRadElem c (ext f), ext f, hext f, rfl⟩
  have hentry : ∀ (r : Fin n → K) (j : Fin n), j ≠ c → pointRadMat c r c j = r j := fun r j hj => by
    rw [pointRadMat_apply, one_apply_ne (Ne.symm hj), ite_eq_left ⟨rfl, hj⟩, zero_add]
  have hbij : Function.Bijective φ := by
    constructor
    · intro f g hfg
      funext j
      have h1 := congrArg (fun A : pointRadSL (K := K) c S =>
        ((A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) c j) hfg
      simp only [φ, coe_pointRadElem] at h1
      have hjc : (j : Fin n) ≠ c := fun h => hcS (h ▸ j.2)
      rw [hentry _ _ hjc, hentry _ _ hjc] at h1
      simpa [ext, dite_eq_left j.2] using h1
    · rintro ⟨_, r, hr, rfl⟩
      refine ⟨fun j => r j, Subtype.ext ?_⟩
      simp only [φ]
      congr 1
      funext j
      by_cases hj : j ∈ S
      · simp [ext, dite_eq_left hj]
      · simp only [ext, dite_eq_right hj]
        exact (hr j hj).symm
  rw [← Nat.card_congr (Equiv.ofBijective φ hbij), Nat.card_fun, hK, Nat.card_eq_fintype_card,
    Fintype.card_coe]

theorem pointRadOn_inf_centralizer [Finite K] [CharP K 2] {a b c : Fin n} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (S : Finset (Fin n)) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1) :
    pointRadOn c S ⊓ centralizer (X₀ : Set (LinearFlag.projectiveSL n K)) =
      pointRadOn c (S \ {a, b}) := by
  apply le_antisymm
  · rintro v ⟨hv, hvX⟩
    obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hv
    obtain ⟨x, hxX, y, hy, rfl, -, hxm, hyy⟩ := exists_lift_torusQ1 hX₀ hX₀c
    have hc : LinearFlag.proj n K (pointRadElem c r) * LinearFlag.proj n K y =
        LinearFlag.proj n K y * LinearFlag.proj n K (pointRadElem c r) :=
      ((mem_centralizer_iff.1 hvX) _ hxX).symm
    have hcomm := mul_eq_mul_of_proj_commute hc hxm
    have hmat : pointRadMat c r * (y : Matrix (Fin n) (Fin n) K) =
        (y : Matrix (Fin n) (Fin n) K) * pointRadMat c r := by
      have := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K))
        hcomm
      simpa only [SpecialLinearGroup.coe_mul, coe_pointRadElem] using this
    have hyy' : (y : Matrix (Fin n) (Fin n) K) * y ≠ 1 := fun h =>
      hyy (Subtype.ext (by rw [SpecialLinearGroup.coe_mul, h, SpecialLinearGroup.coe_one]))
    have hblk := blockDiag_of_mul_eq_mul hab (mem_blockSpecialLinear.1 hy) y.2 hyy' hmat
    have hentry : ∀ j : Fin n, j ≠ c → pointRadMat c r c j = r j := fun j hj => by
      rw [pointRadMat_apply, one_apply_ne (Ne.symm hj), ite_eq_left ⟨rfl, hj⟩, zero_add]
    have hra : r a = 0 := by
      rw [← hentry a (Ne.symm hca)]
      exact hblk c a (by simp [hca, hcb])
    have hrb : r b = 0 := by
      rw [← hentry b (Ne.symm hcb)]
      exact hblk c b (by simp [hca, hcb])
    refine ⟨pointRadElem c r, ⟨r, fun j hj => ?_, rfl⟩, rfl⟩
    by_cases hjS : j ∈ S
    · have hjab : j ∈ ({a, b} : Finset (Fin n)) := by
        by_contra h
        exact hj (Finset.mem_sdiff.2 ⟨hjS, h⟩)
      rcases Finset.mem_insert.1 hjab with rfl | hjb
      · exact hra
      · rw [Finset.mem_singleton.1 hjb]
        exact hrb
    · exact hr j hjS
  · intro v hv
    refine Subgroup.mem_inf.2 ⟨pointRadOn_mono c Finset.sdiff_subset hv, ?_⟩
    have hsub : insert c (S \ {a, b}) ⊆ ({a, b} : Finset (Fin n))ᶜ := by
      intro j hj
      rw [Finset.mem_compl]
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simp [hca, hcb]
      · exact (Finset.mem_sdiff.1 hj).2
    exact blockSL_compl_le_centralizer hX₀
      (blockSL_mono hsub (pointRadOn_le_blockSL c _ hv))

end CFSG.SeitzReduction.LinearPilot
