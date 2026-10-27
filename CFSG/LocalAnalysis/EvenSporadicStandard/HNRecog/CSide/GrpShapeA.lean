module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpShapeBase

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

open scoped Classical

private theorem cSideShape_baseEmb_fst {p : ℕ} (hp : p = 3 ∨ p = 5)
    {x : alternatingGroup (Fin 5)} (hx : orderOf x = p) :
    IsShapeZpTimesA5 p
      ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo)) := by
  haveI : Finite A5WrTwo :=
    Nat.finite_of_card_ne_zero (by rw [cSideShape_natCard_A5WrTwo]; norm_num)
  have hCx' : Nat.card ↥(Subgroup.centralizer
      ({x} : Set (alternatingGroup (Fin 5)))) = p := cSideShape_card_centralizer_a5 hp hx
  let Cx : Subgroup (alternatingGroup (Fin 5)) :=
    Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))
  have hCx : Nat.card ↥Cx = p := hCx'
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    rcases hp with h3 | h5 <;> omega
  have hnotconj : ¬ IsConj x (1 : alternatingGroup (Fin 5)) :=
    fun h => hx1 (isConj_one_left.mp h)
  have hCbase : Nat.card ↥(Subgroup.centralizer
      ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo)) = p * 60 := by
    rw [card_centralizer_baseEmb_of_not_isConj (x := x) (y := 1) hnotconj, hCx',
      cSideShape_card_centralizer_one_a5]
  let M : Subgroup A5WrTwo := (Cx.prod ⊤).map A5WrTwo.baseEmb
  have hle : M ≤ Subgroup.centralizer ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo) := by
    intro y hy
    dsimp only [M] at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_prod] at hq
    have hq1 : q.1 * x = x * q.1 := Subgroup.mem_centralizer_singleton_iff.mp hq.1
    calc A5WrTwo.baseEmb q * A5WrTwo.baseEmb (x, 1)
        = A5WrTwo.baseEmb (q * (x, 1)) := (map_mul A5WrTwo.baseEmb q (x, 1)).symm
      _ = A5WrTwo.baseEmb ((x, 1) * q) :=
            congrArg A5WrTwo.baseEmb (Prod.ext hq1 (by simp))
      _ = A5WrTwo.baseEmb (x, 1) * A5WrTwo.baseEmb q := map_mul A5WrTwo.baseEmb (x, 1) q
  have hMcard : Nat.card ↥M = p * 60 := by
    dsimp only [M]
    rw [Subgroup.card_map_of_injective A5WrTwo.baseEmb_injective,
      Nat.card_congr (Subgroup.prodEquiv Cx ⊤).toEquiv, Nat.card_prod]
    rw [hCx, Subgroup.card_top, cSideShape_natCard_A5]
  have hM : M = Subgroup.centralizer ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hCbase, hMcard])
  have eZp : ↥Cx ≃* Z p := cSideShape_centralizerMulEquiv (x := x) hp hCx'
  refine ⟨(MulEquiv.subgroupCongr hM.symm).trans ?_⟩
  exact ((Subgroup.equivMapOfInjective (Cx.prod ⊤) A5WrTwo.baseEmb
      A5WrTwo.baseEmb_injective).symm).trans
    ((Subgroup.prodEquiv Cx ⊤).trans (MulEquiv.prodCongr eZp Subgroup.topEquiv))

private theorem cSideShape_baseEmb_snd {p : ℕ} (hp : p = 3 ∨ p = 5)
    {x : alternatingGroup (Fin 5)} (hx : orderOf x = p) :
    IsShapeZpTimesA5 p
      ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (1, x)} : Set A5WrTwo)) := by
  obtain ⟨e⟩ := cSideShape_baseEmb_fst hp hx
  have hconj := cSideShape_conjCentralizerMulEquiv (⟨1, Multiplicative.ofAdd 1⟩ : A5WrTwo)
    (A5WrTwo.baseEmb (x, 1))
  have hswap := A5WrTwo.swap_mul_baseEmb_mul_inv x 1
  refine ⟨(MulEquiv.subgroupCongr (by rw [hswap])).trans (hconj.symm.trans e)⟩

private theorem cSideShape_baseEmb_same {p : ℕ} (hp : p = 3 ∨ p = 5)
    {x : alternatingGroup (Fin 5)} (hx : orderOf x = p) :
    IsShapeZpWrTwo p
      ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, x)} : Set A5WrTwo)) := by
  haveI : Finite A5WrTwo :=
    Nat.finite_of_card_ne_zero (by rw [cSideShape_natCard_A5WrTwo]; norm_num)
  have hCx' : Nat.card ↥(Subgroup.centralizer
      ({x} : Set (alternatingGroup (Fin 5)))) = p := cSideShape_card_centralizer_a5 hp hx
  let Cx : Subgroup (alternatingGroup (Fin 5)) :=
    Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))
  let ι : Z p ≃* ↥Cx := (cSideShape_centralizerMulEquiv (x := x) hp hCx').symm
  let κ : Z p → alternatingGroup (Fin 5) := fun z => (ι z : alternatingGroup (Fin 5))
  let Φ : Z p ≀ᵣ Z 2 →* A5WrTwo :=
    { toFun := fun w => A5WrTwo.baseEmb
        (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) * cSideShape_t w.right
      map_one' := by
        show A5WrTwo.baseEmb (κ ((1 : Z p ≀ᵣ Z 2).left 1),
            κ ((1 : Z p ≀ᵣ Z 2).left (Multiplicative.ofAdd 1))) *
            cSideShape_t (1 : Z p ≀ᵣ Z 2).right = 1
        dsimp only [κ]
        simp [map_one, cSideShape_t]
        exact map_one A5WrTwo.baseEmb
      map_mul' := by
        rintro ⟨f, r⟩ ⟨g, r'⟩
        have hpair : (κ (f 1), κ (f (Multiplicative.ofAdd 1))) *
            (if r = 1 then (κ (g 1), κ (g (Multiplicative.ofAdd 1)))
              else (κ (g (Multiplicative.ofAdd 1)), κ (g 1))) =
            (κ (f 1 * g (r⁻¹ * 1)),
              κ (f (Multiplicative.ofAdd 1) * g (r⁻¹ * Multiplicative.ofAdd 1))) := by
          rcases cSideShape_coord_cases r with rfl | rfl
          · dsimp only [κ]
            simp [map_mul]
          · dsimp only [κ]
            simp [cSideShape_sigma_ne_one, cSideShape_sigma_inv, cSideShape_sigma_mul_self, map_mul]
        have hcomm : cSideShape_t r * A5WrTwo.baseEmb (κ (g 1), κ (g (Multiplicative.ofAdd 1))) =
            A5WrTwo.baseEmb (if r = 1 then (κ (g 1), κ (g (Multiplicative.ofAdd 1)))
              else (κ (g (Multiplicative.ofAdd 1)), κ (g 1))) * cSideShape_t r :=
          cSideShape_t_mul_baseEmb r _ _
        show A5WrTwo.baseEmb (κ ((⟨f, r⟩ * ⟨g, r'⟩ : Z p ≀ᵣ Z 2).left 1),
              κ ((⟨f, r⟩ * ⟨g, r'⟩ : Z p ≀ᵣ Z 2).left (Multiplicative.ofAdd 1))) *
              cSideShape_t (⟨f, r⟩ * ⟨g, r'⟩ : Z p ≀ᵣ Z 2).right =
            (A5WrTwo.baseEmb (κ ((⟨f, r⟩ : Z p ≀ᵣ Z 2).left 1),
                κ ((⟨f, r⟩ : Z p ≀ᵣ Z 2).left (Multiplicative.ofAdd 1))) *
              cSideShape_t (⟨f, r⟩ : Z p ≀ᵣ Z 2).right) *
            (A5WrTwo.baseEmb (κ ((⟨g, r'⟩ : Z p ≀ᵣ Z 2).left 1),
                κ ((⟨g, r'⟩ : Z p ≀ᵣ Z 2).left (Multiplicative.ofAdd 1))) *
              cSideShape_t (⟨g, r'⟩ : Z p ≀ᵣ Z 2).right)
        simp only [RegularWreathProduct.mul_left, RegularWreathProduct.mul_right, Pi.mul_apply]
        calc A5WrTwo.baseEmb (κ (f 1 * g (r⁻¹ * 1)),
                κ (f (Multiplicative.ofAdd 1) * g (r⁻¹ * Multiplicative.ofAdd 1))) *
              cSideShape_t (r * r')
            = A5WrTwo.baseEmb ((κ (f 1), κ (f (Multiplicative.ofAdd 1))) *
                (if r = 1 then (κ (g 1), κ (g (Multiplicative.ofAdd 1)))
                  else (κ (g (Multiplicative.ofAdd 1)), κ (g 1)))) *
              cSideShape_t (r * r') := by rw [hpair]
          _ = A5WrTwo.baseEmb (κ (f 1), κ (f (Multiplicative.ofAdd 1))) *
                A5WrTwo.baseEmb (if r = 1 then (κ (g 1), κ (g (Multiplicative.ofAdd 1)))
                  else (κ (g (Multiplicative.ofAdd 1)), κ (g 1))) *
              cSideShape_t (r * r') := by rw [map_mul]
          _ = A5WrTwo.baseEmb (κ (f 1), κ (f (Multiplicative.ofAdd 1))) *
                A5WrTwo.baseEmb (if r = 1 then (κ (g 1), κ (g (Multiplicative.ofAdd 1)))
                  else (κ (g (Multiplicative.ofAdd 1)), κ (g 1))) *
              (cSideShape_t r * cSideShape_t r') := by rw [cSideShape_t_mul]
          _ = A5WrTwo.baseEmb (κ (f 1), κ (f (Multiplicative.ofAdd 1))) *
                (A5WrTwo.baseEmb (if r = 1 then (κ (g 1), κ (g (Multiplicative.ofAdd 1)))
                  else (κ (g (Multiplicative.ofAdd 1)), κ (g 1))) * cSideShape_t r) *
              cSideShape_t r' := by group
          _ = A5WrTwo.baseEmb (κ (f 1), κ (f (Multiplicative.ofAdd 1))) *
                (cSideShape_t r * A5WrTwo.baseEmb (κ (g 1),
                  κ (g (Multiplicative.ofAdd 1)))) * cSideShape_t r' := by rw [hcomm]
          _ = (A5WrTwo.baseEmb (κ (f 1), κ (f (Multiplicative.ofAdd 1))) * cSideShape_t r) *
                (A5WrTwo.baseEmb (κ (g 1), κ (g (Multiplicative.ofAdd 1))) *
                  cSideShape_t r') := by group }
  have hΦright : ∀ w : Z p ≀ᵣ Z 2, (Φ w).right = w.right := by
    intro w
    show (A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) *
        cSideShape_t w.right).right = w.right
    rw [RegularWreathProduct.mul_right, cSideShape_baseEmb_right, one_mul, cSideShape_t_right]
  have hΦinj : Function.Injective Φ := by
    intro w v h
    have hright : w.right = v.right := by
      have h1 : (Φ w).right = (Φ v).right := congrArg RegularWreathProduct.right h
      rwa [hΦright w, hΦright v] at h1
    apply RegularWreathProduct.ext
    · funext q
      have hbase : A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) =
          A5WrTwo.baseEmb (κ (v.left 1), κ (v.left (Multiplicative.ofAdd 1))) := by
        have h1 : A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) *
              cSideShape_t w.right =
            A5WrTwo.baseEmb (κ (v.left 1), κ (v.left (Multiplicative.ofAdd 1))) *
              cSideShape_t v.right := h
        rw [hright] at h1
        exact mul_right_cancel h1
      have hpair := A5WrTwo.baseEmb_injective hbase
      rcases cSideShape_coord_cases q with rfl | rfl
      · exact ι.injective (Subtype.ext (congrArg Prod.fst hpair))
      · exact ι.injective (Subtype.ext (congrArg Prod.snd hpair))
    · exact hright
  have hrange_le : Φ.range ≤
      Subgroup.centralizer ({A5WrTwo.baseEmb (x, x)} : Set A5WrTwo) := by
    rintro y ⟨w, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) *
        cSideShape_t w.right) * A5WrTwo.baseEmb (x, x) =
      A5WrTwo.baseEmb (x, x) * (A5WrTwo.baseEmb (κ (w.left 1),
        κ (w.left (Multiplicative.ofAdd 1))) * cSideShape_t w.right)
    calc (A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) *
            cSideShape_t w.right) * A5WrTwo.baseEmb (x, x)
        = A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) *
            (cSideShape_t w.right * A5WrTwo.baseEmb (x, x)) := by group
      _ = A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) *
            (A5WrTwo.baseEmb (x, x) * cSideShape_t w.right) := by
            rw [cSideShape_t_baseEmb_diag]
      _ = (A5WrTwo.baseEmb (κ (w.left 1), κ (w.left (Multiplicative.ofAdd 1))) *
            A5WrTwo.baseEmb (x, x)) * cSideShape_t w.right := by group
      _ = (A5WrTwo.baseEmb (x, x) * A5WrTwo.baseEmb (κ (w.left 1),
            κ (w.left (Multiplicative.ofAdd 1)))) * cSideShape_t w.right := by
            rw [cSideShape_baseEmb_diag_comm x _ _
              (ι (w.left 1)).2 (ι (w.left (Multiplicative.ofAdd 1))).2]
      _ = A5WrTwo.baseEmb (x, x) * (A5WrTwo.baseEmb (κ (w.left 1),
            κ (w.left (Multiplicative.ofAdd 1))) * cSideShape_t w.right) := by group
  have hcard_range : Nat.card ↥Φ.range = Nat.card (Z p ≀ᵣ Z 2) :=
    (Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv).symm
  have hcard_wr : Nat.card (Z p ≀ᵣ Z 2) = p * p * 2 := by
    rw [RegularWreathProduct.card]
    have hZp : Nat.card (Z p) = p := by
      show Nat.card (Multiplicative (ZMod p)) = p
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hZ2 : Nat.card (Z 2) = 2 := by
      show Nat.card (Multiplicative (ZMod 2)) = 2
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hZp, hZ2, pow_two]
  have hcard_cent : Nat.card ↥(Subgroup.centralizer
      ({A5WrTwo.baseEmb (x, x)} : Set A5WrTwo)) = p * p * 2 := by
    rw [card_centralizer_baseEmb_of_isConj (IsConj.refl x), hCx']
  have hM : Φ.range = Subgroup.centralizer ({A5WrTwo.baseEmb (x, x)} : Set A5WrTwo) :=
    Subgroup.eq_of_le_of_card_ge hrange_le
      (le_of_eq (hcard_cent.trans (hcard_range.trans hcard_wr).symm))
  exact ⟨((MonoidHom.ofInjective hΦinj).trans (MulEquiv.subgroupCongr hM)).symm⟩

theorem cSide_shape_one_coord {p : ℕ} (hp : p = 3 ∨ p = 5) {x : alternatingGroup (Fin 5)}
    (hx : orderOf x = p) :
    IsShapeZpTimesA5 p ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo)) ∧
      IsShapeZpTimesA5 p ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (1, x)} : Set A5WrTwo)) :=
  ⟨cSideShape_baseEmb_fst hp hx, cSideShape_baseEmb_snd hp hx⟩

theorem cSide_shape_conj {p : ℕ} (hp : p = 3 ∨ p = 5) {x y : alternatingGroup (Fin 5)}
    (hx : orderOf x = p) (hy : orderOf y = p) (hxy : IsConj x y) :
    IsShapeZpWrTwo p ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo)) := by
  obtain ⟨e⟩ := cSideShape_baseEmb_same hp hx
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hc' : c⁻¹ * y * c = x := by rw [← hc]; group
  have hkey : A5WrTwo.baseEmb (1, c⁻¹) * A5WrTwo.baseEmb (x, y) *
      (A5WrTwo.baseEmb (1, c⁻¹))⁻¹ = A5WrTwo.baseEmb (x, x) := by
    rw [← map_mul, ← map_inv, ← map_mul]
    exact congrArg A5WrTwo.baseEmb (by ext <;> simp [hc'])
  have hconj := cSideShape_conjCentralizerMulEquiv (A5WrTwo.baseEmb (1, c⁻¹))
    (A5WrTwo.baseEmb (x, y))
  refine ⟨(hconj.trans (MulEquiv.subgroupCongr (by rw [hkey]))).trans e⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
