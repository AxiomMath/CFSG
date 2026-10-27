module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Classification.Orthogonal3.Mu

import CFSG.OddTranspositions.F3NoSqE1

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open

open _root_.CFSG.Fischer.Classification.F3

variable {Y : Type} [Group Y] {F : Set Y} {m : ℕ}
  {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

namespace F3

def sympU (y : Fin 5 → Fin m → ZMod 3) : Fin m → ZMod 3 :=
  y 0

def sympV (y : Fin 5 → Fin m → ZMod 3) : Fin m → ZMod 3 :=
  y 0 + y 1 + y 2 + y 3

def sympW (y : Fin 5 → Fin m → ZMod 3) : Fin m → ZMod 3 :=
  y 0 + y 1 + (2 : ZMod 3) • y 2 + y 4

theorem sympWitness_norm_pair {y : Fin 5 → Fin m → ZMod 3}
    (hy : ∀ i j, f (y i) (y j) = if i = j then 1 else 0) :
    f (sympU y) (sympU y) = 1 ∧ f (sympV y) (sympV y) = 1 ∧
      f (sympW y) (sympW y) = 1 ∧ f (sympU y) (sympV y) = 1 ∧
      f (sympW y) (sympU y) = 1 ∧ f (sympW y) (sympV y) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sympU, hy]
  · simp only [sympV, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hy]
    decide
  · simp only [sympW, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hy]
    decide
  · simp only [sympU, sympV, LinearMap.BilinForm.add_right, hy]
    decide
  · simp only [sympW, sympU, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hy]
    decide
  · simp only [sympW, sympV, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, hy]
    decide

theorem sympWitness_aux {y : Fin 5 → Fin m → ZMod 3}
    (hy : ∀ i j, f (y i) (y j) = if i = j then 1 else 0) :
    f (sympU y) (y 1) = 0 ∧ f (sympV y) (y 1) = 1 ∧
      f (sympU y) (y 2) = 0 ∧ f (sympW y) (y 2) = 2 ∧
      f (sympU y) (y 4) = 0 ∧ f (sympV y) (y 4) = 0 ∧
      f (sympW y) (y 4) = 1 ∧ f (sympV y + sympU y) (y 4) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sympU, hy]
  · simp only [sympV, LinearMap.BilinForm.add_left, hy]
    decide
  · simp [sympU, hy]
  · simp only [sympW, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hy]
    decide
  · simp [sympU, hy]
  · simp only [sympV, LinearMap.BilinForm.add_left, hy]
    decide
  · simp only [sympW, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hy]
    decide
  · rw [LinearMap.BilinForm.add_left]
    simp [sympV, sympU, hy]

theorem sympWitness_distinct {y : Fin 5 → Fin m → ZMod 3}
    (hy : ∀ i j, f (y i) (y j) = if i = j then 1 else 0) :
    sympV y ≠ sympU y ∧ sympV y ≠ -sympU y ∧
      sympW y ≠ sympU y ∧ sympW y ≠ -sympU y ∧
      sympW y ≠ sympV y ∧ sympW y ≠ -sympV y ∧
      sympW y ≠ sympV y + sympU y ∧ sympW y ≠ -(sympV y + sympU y) := by
  obtain ⟨hu1, hv1, hu2, hw2, hu4, hv4, hw4, hvu4⟩ := sympWitness_aux (f := f) hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, hu1] at hv1
    exact zero_ne_one hv1
  · intro h
    rw [h, LinearMap.BilinForm.neg_left, hu1, neg_zero] at hv1
    exact zero_ne_one hv1
  · intro h
    rw [h, hu2] at hw2
    exact (by decide : (0 : ZMod 3) ≠ 2) hw2
  · intro h
    rw [h, LinearMap.BilinForm.neg_left, hu2, neg_zero] at hw2
    exact (by decide : (0 : ZMod 3) ≠ 2) hw2
  · intro h
    rw [h, hv4] at hw4
    exact zero_ne_one hw4
  · intro h
    rw [h, LinearMap.BilinForm.neg_left, hv4, neg_zero] at hw4
    exact zero_ne_one hw4
  · intro h
    rw [h, hvu4] at hw4
    exact zero_ne_one hw4
  · intro h
    rw [h, LinearMap.BilinForm.neg_left, hvu4, neg_zero] at hw4
    exact zero_ne_one hw4

theorem sympWitness_not_commute (hf : IsF3Form f) (hm4 : 4 ≤ m)
    {y : Fin 5 → Fin m → ZMod 3}
    (hy : ∀ i j, f (y i) (y j) = if i = j then 1 else 0) :
    reflBar f (sympU y) * reflBar f (sympV y) ≠
        reflBar f (sympV y) * reflBar f (sympU y) ∧
      reflBar f (sympW y) * reflBar f (sympU y) ≠
        reflBar f (sympU y) * reflBar f (sympW y) ∧
      reflBar f (sympW y) * reflBar f (sympV y) ≠
        reflBar f (sympV y) * reflBar f (sympW y) ∧
      reflBar f (sympW y) *
          (reflBar f (sympU y) * reflBar f (sympV y) * reflBar f (sympU y)) ≠
        reflBar f (sympU y) * reflBar f (sympV y) * reflBar f (sympU y) *
          reflBar f (sympW y) := by
  obtain ⟨hu, hv, hw, huv, hwu, hwv⟩ := sympWitness_norm_pair (f := f) hy
  obtain ⟨-, -, -, -, -, -, -, hvu4⟩ := sympWitness_aux (f := f) hy
  obtain ⟨hvu_ne, hvu_ne_neg, hwu_ne, hwu_ne_neg, hwv_ne, hwv_ne_neg, hwvu_ne,
    hwvu_ne_neg⟩ := sympWitness_distinct (f := f) hy
  have hwvu : f (sympW y) (sympV y + sympU y) = 2 := by
    rw [LinearMap.BilinForm.add_right, hwv, hwu, one_add_one_eq_two]
  have hact : act (F3.refl f (sympU y)) (sympV y) = sympV y + sympU y := by
    rw [act_refl hu (sympV y), hf.symm (sympV y) (sympU y), huv, one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rcases (reflBar_commute_iff hf hm4 hu hv).1 h with h1 | h1 | h1
    · rw [huv] at h1
      exact one_ne_zero h1
    · exact hvu_ne h1
    · exact hvu_ne_neg h1
  · intro h
    rcases (reflBar_commute_iff hf hm4 hw hu).1 h with h1 | h1 | h1
    · rw [hwu] at h1
      exact one_ne_zero h1
    · exact hwu_ne h1.symm
    · exact hwu_ne_neg (by rw [h1, neg_neg])
  · intro h
    rcases (reflBar_commute_iff hf hm4 hw hv).1 h with h1 | h1 | h1
    · rw [hwv] at h1
      exact one_ne_zero h1
    · exact hwv_ne h1.symm
    · exact hwv_ne_neg (by rw [h1, neg_neg])
  · rw [reflBar_conj hf (sympU y) (sympV y)]
    intro h
    rcases (reflBar_commute_iff hf hm4 hw (by
      rw [(isIsom_refl hf (sympU y)).norm, hv])).1 h with h1 | h1 | h1
    · rw [hact, LinearMap.BilinForm.add_right, hwv, hwu, one_add_one_eq_two] at h1
      exact (by decide : (2 : ZMod 3) ≠ 0) h1
    · rw [hact] at h1
      exact hwvu_ne h1.symm
    · rw [hact] at h1
      exact hwvu_ne_neg (by rw [h1, neg_neg])

end F3

theorem not_isSymplecticType_D3 (hf : IsF3Form f) (hm : 6 ≤ m) :
    ¬ IsSymplecticType (D3 f) := by
  intro hsymp
  have hm4 : 4 ≤ m := by omega
  obtain ⟨y, hy⟩ := Beta.exists_orthonormalF3 (f := f) hf 5 (by omega)
  obtain ⟨hu, hv, hw, -⟩ := sympWitness_norm_pair (f := f) hy
  obtain ⟨hde, hzd, hze, hzded⟩ := sympWitness_not_commute hf hm4 hy
  rcases hsymp (reflBar f (sympU y)) (reflBar_mem_D3 hu)
    (reflBar f (sympV y)) (reflBar_mem_D3 hv)
    (reflBar f (sympW y)) (reflBar_mem_D3 hw) hde with h | h | h
  · exact hzd h
  · exact hze h
  · exact hzded h

theorem image_F_eq_D3 (hmod : fischerCentralQuotientModel F
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ∃ ψ : Y ≃* R3 f, ψ '' F = D3 f := by
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff (f := f) F).1 hmod
  refine ⟨ψ, ?_⟩
  rw [Set.image_eq_iff_surjOn_mapsTo]
  exact ⟨fun y hy => ⟨ψ.symm y, (hψ _).2 (by simpa using hy), ψ.apply_symm_apply y⟩,
    fun x hx => (hψ x).1 hx⟩

theorem reflection_tripleProperty (hm : 6 ≤ m)
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel F
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    TripleProperty F := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψD⟩ := image_F_eq_D3 (F := F) hmod
  exact (tripleProperty_congr ψ hψD).2 (tripleProperty_D3 hf (by omega))

theorem reflection_localQuotient_simple (hY : Hyp Y F) (hm : 6 ≤ m)
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel F
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ∀ d ∈ F, IsSimpleGroup (commutator (LocalQuotient F d)) ∧
      ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff (f := f) F).1 hmod
  have hψD : ψ '' F = D3 f := by
    rw [Set.image_eq_iff_surjOn_mapsTo]
    exact ⟨fun y hy => ⟨ψ.symm y, (hψ _).2 (by simpa using hy), ψ.apply_symm_apply y⟩,
      fun x hx => (hψ x).1 hx⟩
  obtain ⟨v₀, hv₀⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  let d₀ : Y := ψ.symm (reflBar f v₀)
  have hd₀ : d₀ ∈ F := (hψ d₀).2 (by simpa [d₀] using reflBar_mem_D3 hv₀)
  obtain ⟨f', hf', -, Φ, hΦ⟩ := exists_localQuotient_equiv hf (by omega) hv₀
  let Φ₀ : LocalQuotient F d₀ ≃* R3 f' :=
    (localQuotientCongr ψ hψD (ψ.apply_symm_apply (reflBar f v₀))).trans Φ
  have hΦ₀ : Φ₀ '' LocalImages F d₀ = D3 f' := by
    rw [MulEquiv.coe_trans, Set.image_comp, localQuotientCongr_image, hΦ]
  intro d hd
  obtain ⟨Ψ, -⟩ := LocalR3.exists_localQuotient_equiv_of_mem hY.pair hd₀ hd Φ₀ hΦ₀
  have hS : IsSimpleGroup (commutator (R3 f')) :=
    CFSG.LargeExtraspecial.r3SimpleInput (m - 1) f' hf' (by omega)
      (fun h4 => absurd h4 (by omega))
  have hna : ∃ a b : commutator (R3 f'), a * b ≠ b * a :=
    Recognition.R3.nonabelian_commutator_R3 hf' (by omega) hS
  refine ⟨@Recognition.R3.isSimpleGroup_commutator_of_mulEquiv (R3 f')
    (LocalQuotient F d) _ _ Ψ.symm hS, ?_⟩
  exact CFSG.OddTranspositions.nonabelianCommutator_of_mulEquiv Ψ hna

theorem reflection_nonabelianCommutator (hY : Hyp Y F) (hm : 6 ≤ m)
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel F
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    NonabelianCommutator Y := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, -⟩ := (fischerCentralQuotientModel_iff (f := f) F).1 hmod
  have hS : IsSimpleGroup (commutator (R3 f)) :=
    @Recognition.R3.isSimpleGroup_commutator_of_mulEquiv Y (R3 f) _ _ ψ hY.simple
  exact CFSG.OddTranspositions.nonabelianCommutator_of_mulEquiv ψ
    (Recognition.R3.nonabelian_commutator_R3 hf (by omega) hS)

theorem reflection_not_isSymplecticType (hm : 6 ≤ m)
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel F
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ¬ IsSymplecticType F := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψD⟩ := image_F_eq_D3 (F := F) hmod
  intro hF
  have hsymp : IsSymplecticType (D3 f) := by
    refine LocalSymp.isSymplecticType_of_mulEquiv (E := D3 f) ψ.symm ?_ hF
    intro q
    rw [← hψD]
    constructor
    · rintro ⟨g, hg, hgq⟩
      rwa [← hgq, ψ.symm_apply_apply]
    · intro hq
      exact ⟨ψ.symm q, hq, ψ.apply_symm_apply q⟩
  exact not_isSymplecticType_D3 hf hm hsymp

end CFSG.Fischer.Classification
