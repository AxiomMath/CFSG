module

public import CFSG.GH74.Uniqueness.Bender.FrameTorus

public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {E : Type} [Field E]

theorem frame_expand {hU : UnitaryFieldData 2 f E} {v : Fin 3 → (Fin 3 → E)}
    (hv : IsOrthonormalFrame hU v) (x : Fin 3 → E) :
    x = ∑ j, herm hU (v j) x • v j := by
  have h : frameMat v *ᵥ (frameMatStar hU v *ᵥ x) = x := by
    rw [mulVec_mulVec, frameMat_mul_frameMatStar hv, one_mulVec]
  conv_lhs => rw [← h]
  ext a
  simp only [mulVec, dotProduct, frameMat_apply, frameMatStar_apply, herm, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_one_of_sq_eq_one {F : Type*} [Field F] [CharP F 2] {x : F} (h : x ^ 2 = 1) :
    x = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have : (x - 1) ^ 2 = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

theorem exists_rootsOfUnity_ne_one (hU : UnitaryFieldData 2 f E) :
    ∃ x : rootsOfUnity (2 ^ f + 1) E, x ≠ 1 := by
  have hcard := card_rootsOfUnity_eq hU
  have hf : 1 ≤ f := hU.one_le
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_contra hno
  push Not at hno
  have : Subsingleton (rootsOfUnity (2 ^ f + 1) E) := ⟨fun a b => by rw [hno a, hno b]⟩
  have h1 : Nat.card (rootsOfUnity (2 ^ f + 1) E) = 1 := Nat.card_of_subsingleton 1
  omega

theorem permutesLines_of_normalizes {hU : UnitaryFieldData 2 f E} {v : Fin 3 → (Fin 3 → E)}
    (hv : IsOrthonormalFrame hU v) {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (hg : ∀ h ∈ frameTorusSU hU v, g * h * g⁻¹ ∈ frameTorusSU hU v) :
    PermutesLines v ((g : GL (Fin 3) E)) := by
  classical
  have hchar : CharP E 2 := hU.charP
  obtain ⟨x, hx⟩ := exists_rootsOfUnity_ne_one hU
  set c : Fin 3 → E := ![((x : Eˣ) : E), (((x⁻¹ : rootsOfUnity (2 ^ f + 1) E) : Eˣ) : E), 1]
    with hcdef
  have hc : ∀ i, hU.norm (c i) = 1 := by
    intro i
    fin_cases i
    · exact norm_coe_rootsOfUnity hU x
    · exact norm_coe_rootsOfUnity hU x⁻¹
    · simp [hcdef, UnitaryFieldData.norm]
  have hprod : ∏ i, c i = 1 := by
    simp [hcdef, Fin.prod_univ_three]
  have hx1 : ((x : Eˣ) : E) ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    apply Units.ext
    simpa using h
  have hxx : ((x : Eˣ) : E) ≠ (((x⁻¹ : rootsOfUnity (2 ^ f + 1) E) : Eˣ) : E) := by
    intro h
    apply hx1
    apply eq_one_of_sq_eq_one (F := E)
    have h' : ((x : Eˣ) : E) * ((x : Eˣ) : E) = ((x : Eˣ) : E) *
        (((x⁻¹ : rootsOfUnity (2 ^ f + 1) E) : Eˣ) : E) := by rw [← h]
    rw [sq, h']
    simp
  have hx1' : (((x⁻¹ : rootsOfUnity (2 ^ f + 1) E) : Eˣ) : E) ≠ 1 := by
    intro h
    apply hx1
    have : ((x : Eˣ) : E) * (((x⁻¹ : rootsOfUnity (2 ^ f + 1) E) : Eˣ) : E) = 1 := by simp
    rw [h, mul_one] at this
    exact this
  have hcinj : Function.Injective c := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [hcdef, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hij ⊢
    all_goals first
      | rfl
      | exact absurd hij hxx
      | exact absurd hij.symm hxx
      | exact absurd hij hx1
      | exact absurd hij.symm hx1
      | exact absurd hij hx1'
      | exact absurd hij.symm hx1'
  let d₀ := frameDiagElt hv c hc hprod
  have hd₀ : d₀ ∈ frameTorusSU hU v := frameDiagElt_mem_frameTorusSU hv c hc hprod
  have hd' := hg d₀ hd₀
  choose e he0 he using hd'
  set gm : Matrix (Fin 3) (Fin 3) E := ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) with hgm
  have hde : ∀ i, (((g * d₀ * g⁻¹ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) *ᵥ (gm *ᵥ v i) = c i • (gm *ᵥ v i) := by
    intro i
    change (gm * ((d₀ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
      ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) *ᵥ (gm *ᵥ v i) = _
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec (v i)
      ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) gm, hgm, Units.inv_mul,
      one_mulVec, frameDiagElt_mulVec hv c hc hprod i, mulVec_smul]
  have hsupp : ∀ i j, herm hU (v j) (gm *ᵥ v i) ≠ 0 → e j = c i := by
    intro i j ha
    have h1 := herm_mulVec_mulVec hU (g * d₀ * g⁻¹).2 (v j) (gm *ᵥ v i)
    rw [he j, hde i, herm_smul_left, herm_smul_right] at h1
    have hn : hU.norm (e j) = 1 :=
      norm_eq_one_of_mulVec hv (g * d₀ * g⁻¹).2 (he j)
    have h2 : (hU.bar (e j) * c i) * herm hU (v j) (gm *ᵥ v i) =
        1 * herm hU (v j) (gm *ᵥ v i) := by
      rw [one_mul, mul_assoc]
      exact h1
    have h3 : hU.bar (e j) * c i = 1 := mul_right_cancel₀ ha h2
    have h4 : e j * hU.bar (e j) = 1 := hn
    calc e j = e j * (hU.bar (e j) * c i) := by rw [h3, mul_one]
      _ = (e j * hU.bar (e j)) * c i := by rw [mul_assoc]
      _ = c i := by rw [h4, one_mul]
  have hex : ∀ i, ∃ j, herm hU (v j) (gm *ᵥ v i) ≠ 0 := by
    intro i
    by_contra hno
    push Not at hno
    have h1 := frame_expand hv (gm *ᵥ v i)
    rw [Finset.sum_eq_zero (fun j _ => by rw [hno j, zero_smul])] at h1
    exact mulVec_ne_zero (g : GL (Fin 3) E) (frame_ne_zero hv i) h1
  choose j0 hj0 using hex
  have hinj : Function.Injective j0 := by
    intro i i' h
    apply hcinj
    rw [← hsupp i (j0 i) (hj0 i), ← hsupp i' (j0 i') (hj0 i'), h]
  have hsurj : Function.Surjective j0 := Finite.injective_iff_surjective.mp hinj
  intro i
  refine ⟨j0 i, herm hU (v (j0 i)) (gm *ᵥ v i), ?_⟩
  conv_lhs => rw [frame_expand hv (gm *ᵥ v i)]
  rw [Finset.sum_eq_single (j0 i)]
  · intro j _ hj
    by_contra hne
    have ha : herm hU (v j) (gm *ᵥ v i) ≠ 0 := fun h0 => hne (by rw [h0, zero_smul])
    obtain ⟨i', rfl⟩ := hsurj j
    have h1 := hsupp i (j0 i') ha
    have h2 := hsupp i' (j0 i') (hj0 i')
    have h3 : i' = i := hcinj (h2.symm.trans h1)
    exact hj (by rw [h3])
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_frameMonoSU_of_normalizes {hU : UnitaryFieldData 2 f E} {v : Fin 3 → (Fin 3 → E)}
    (hv : IsOrthonormalFrame hU v) {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (hg : ∀ h ∈ frameTorusSU hU v, g * h * g⁻¹ ∈ frameTorusSU hU v)
    (hg' : ∀ h ∈ frameTorusSU hU v, g⁻¹ * h * g ∈ frameTorusSU hU v) :
    g ∈ frameMonoSU hU v :=
  ⟨permutesLines_of_normalizes hv hg,
    permutesLines_of_normalizes hv (g := g⁻¹) (by simpa using hg')⟩

theorem mem_frameTorusSU_of_mk_mem {hU : UnitaryFieldData 2 f E} {v : Fin 3 → (Fin 3 → E)}
    {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (hg : (QuotientGroup.mk g : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ∈ frameTorus hU v) :
    g ∈ frameTorusSU hU v := by
  obtain ⟨h', hh', he⟩ := Subgroup.mem_map.mp hg
  have hz : h'⁻¹ * g ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3 :=
    QuotientGroup.eq.mp he
  have hz' := normOneScalars_le_frameTorusSU hU v 3 hz
  have : g = h' * (h'⁻¹ * g) := by group
  rw [this]
  exact mul_mem hh' hz'

theorem normalizer_frameTorus_le {hU : UnitaryFieldData 2 f E} {v : Fin 3 → (Fin 3 → E)}
    (hv : IsOrthonormalFrame hU v) :
    Subgroup.normalizer ((frameTorus hU v : Subgroup (primeFormP hU (1 : Matrix (Fin 3)
      (Fin 3) E))) : Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) ≤ frameMono hU v := by
  intro x hx
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  have key : ∀ y : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E),
      y ∈ Subgroup.normalizer ((frameTorus hU v : Subgroup (primeFormP hU (1 : Matrix (Fin 3)
        (Fin 3) E))) : Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) →
      ∀ s : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E), (QuotientGroup.mk s : primeFormP hU
        (1 : Matrix (Fin 3) (Fin 3) E)) = y → ∀ h ∈ frameTorusSU hU v,
        s * h * s⁻¹ ∈ frameTorusSU hU v := by
    intro y hy s hs h hh
    have h1 : (QuotientGroup.mk h : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ∈
        frameTorus hU v := Subgroup.mem_map_of_mem _ hh
    have h2 := (Subgroup.mem_normalizer_iff.mp hy _).mp h1
    rw [← hs] at h2
    have h3 : (QuotientGroup.mk s : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) *
        (QuotientGroup.mk h) * (QuotientGroup.mk s)⁻¹ =
        (QuotientGroup.mk (s * h * s⁻¹) : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) := by
      simp
    rw [h3] at h2
    exact mem_frameTorusSU_of_mk_mem h2
  have hs1 := key _ hx s rfl
  have hx' := Subgroup.inv_mem _ hx
  have hs2 := key _ hx' s⁻¹ (by simp)
  have hs : s ∈ frameMonoSU hU v :=
    mem_frameMonoSU_of_normalizes hv hs1 (fun h hh => by simpa using hs2 h hh)
  exact Subgroup.mem_map_of_mem _ hs

theorem frameMono_eq_normalizer {hU : UnitaryFieldData 2 f E} (hf : 2 ≤ f)
    {v : Fin 3 → (Fin 3 → E)} (hv : IsOrthonormalFrame hU v) :
    frameMono hU v = Subgroup.normalizer ((frameTorus hU v : Subgroup (primeFormP hU
      (1 : Matrix (Fin 3) (Fin 3) E))) : Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨-, hnormal, -⟩ := frame_group_structure hU hf hv
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hnormal x hx h hh
    · intro hh
      have h1 := hnormal x⁻¹ ((frameMono hU v).inv_mem hx) _ hh
      have h2 : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [h2] at h1
  · exact normalizer_frameTorus_le hv

end CFSG.GH74.Uniqueness.Bender.Frame
