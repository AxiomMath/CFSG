module

public import CFSG.LieType.Chevalley.E6GraphRadicalCoords
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRootSL2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi
open Matrix

variable {F : Type} [Field F]

theorem SL2_ext {A B : SL2 F}
    (h : ∀ i j, (A : Matrix (Fin 2) (Fin 2) F) i j = (B : Matrix (Fin 2) (Fin 2) F) i j) :
    A = B :=
  Subtype.ext (Matrix.ext h)

theorem WSL_eq_of_two (h2 : (2 : F) = 0) : (WSL : SL2 F) = uSL 1 * vSL 1 * uSL 1 := by
  refine SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [WSL, coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    first | linear_combination -h2 | linear_combination -2 * h2 | linear_combination h2

theorem uSL_mul_vSL_pow_three (h2 : (2 : F) = 0) : (uSL 1 * vSL 1 : SL2 F) ^ 3 = 1 := by
  refine SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    first | linear_combination 2 * h2 | linear_combination 4 * h2 | linear_combination h2 |
      linear_combination 3 * h2 | linear_combination 5 * h2 | linear_combination 6 * h2

theorem entry_mul (A B : SL2 F) (i j : Fin 2) :
    ((A * B : SL2 F) : Matrix (Fin 2) (Fin 2) F) i j =
      (A : Matrix (Fin 2) (Fin 2) F) i 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 j +
        (A : Matrix (Fin 2) (Fin 2) F) i 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_entries (A : SL2 F) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h := A.2
  rwa [Matrix.det_fin_two] at h

theorem eq_one_of_commute (h2 : (2 : F) = 0) {Y : SL2 F} (hu : Y * uSL 1 = uSL 1 * Y)
    (hv : Y * vSL 1 = vSL 1 * Y) : Y = 1 := by
  have e := fun i j => congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) i j) hu
  have e' := fun i j => congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) i j) hv
  have h1 := e 0 0
  have h2' := e 0 1
  have h3 := e' 0 0
  simp only [entry_mul, coe_uSL, coe_vSL] at h1 h2' h3
  simp at h1 h2' h3
  have hdet := det_entries Y
  set a := (Y : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (Y : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (Y : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (Y : Matrix (Fin 2) (Fin 2) F) 1 1
  have hd : d = a := by linear_combination -h2'
  have ha : (a - 1) ^ 2 = 0 := by
    rw [hd, h3, h1] at hdet
    linear_combination hdet + (1 - a) * h2
  have ha1 : a = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 ha)
  refine SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_one]
  · exact ha1
  · exact h3
  · exact h1
  · exact hd.trans ha1

theorem eq_conj_vSL_of_two (h2 : (2 : F) = 0) {Z : SL2 F} (hZ : Z * Z = 1)
    (h3 : uSL 1 * Z * (uSL 1 * Z * (uSL 1 * Z)) = 1) (hne : Z ≠ uSL 1) :
    Z = uSL ((Z : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) * vSL 1 *
      (uSL ((Z : Matrix (Fin 2) (Fin 2) F) 0 0 + 1))⁻¹ := by
  have e := fun i j => congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) i j) hZ
  have e' := fun i j => congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) i j) h3
  have z00 := e 0 0
  have z11 := e 1 1
  have m00 := e' 0 0
  have m01 := e' 0 1
  have m10 := e' 1 0
  have m11 := e' 1 1
  simp only [entry_mul, coe_uSL] at z00 z11 m00 m01 m10 m11
  simp at z00 z11 m00 m01 m10 m11
  have hdet := det_entries Z
  set a := (Z : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (Z : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (Z : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (Z : Matrix (Fin 2) (Fin 2) F) 1 1
  have hsq : (a + d) ^ 2 = 0 := by linear_combination z00 + z11 + 2 * hdet + 2 * h2
  have hs : a + d = 0 := pow_eq_zero_iff two_ne_zero |>.1 hsq
  have hd : d = a := by linear_combination hs - a * h2
  rw [hd] at m10 m11 m01
  have hc : c * (c + 1) ^ 2 = 0 := by
    linear_combination m10 - c * z00 + (c ^ 2 - a ^ 2 * c - 2 * a * c ^ 2) * h2
  have hc1 : c = 1 := by
    by_contra hc1
    have hc1' : (c + 1) ^ 2 ≠ 0 := pow_ne_zero 2 fun h => hc1 (by linear_combination h - h2)
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 hc with h | h
      · exact h
      · exact absurd h hc1'
    rw [hc0] at m11 m01 z00
    have ha1 : a = 1 := by linear_combination m11 - a * z00
    rw [ha1] at m01
    have hb1 : b = 1 := by linear_combination m01 - (b + 2) * h2
    refine hne (SL2_ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [coe_uSL]
    · exact ha1
    · exact hb1
    · exact hc0
    · exact hd.trans ha1
  rw [hc1] at z00
  have hb : b = 1 - a ^ 2 := by linear_combination z00
  refine SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [entry_mul, coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  · show a = _
    linear_combination -h2
  · show b = _
    linear_combination hb + (1 + a) * h2
  · exact hc1
  · show d = _
    linear_combination hd + a * h2

section Weyl

variable {E : Type} [Field E]

@[expose] def thetaWord : List (Fin TwistTag.E6.tag.rank) :=
  ([1, 3, 4, 5, 2, 3, 4, 1, 3, 2] : List (Fin 6))

theorem pinnedData_e6HighestRoot :
    pinnedData TwistTag.E6.tag e6HighestRoot = (e6Idx 0, [2, 3, 1, 4, 3, 2, 5, 4, 3, 1], 1) := by
  decide +kernel

theorem pinnedWeyl_e6HighestRoot :
    pinnedWeyl TwistTag.E6.tag E e6HighestRoot = wordElt E thetaWord := by
  rw [pinnedWeyl_eq_list_prod, pinnedWord, pinnedData_e6HighestRoot]
  rfl

theorem thetaSL2_WSL :
    thetaSL2 E WSL = wordElt E thetaWord * weylElt TwistTag.E6.tag E (e6Idx 0) 1 *
      (wordElt E thetaWord)⁻¹ := by
  rw [rootSL2_apply, pinnedData_e6HighestRoot, simpleRootSL2_WSL, pinnedWeyl_e6HighestRoot]

theorem canonicalRep_inv_mul_pinnedX_mul
    (h2 : (2 : E) = 0) (w : WeylGroup TwistTag.E6.tag)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (c : E) :
    (canonicalRep (coxeterSystem TwistTag.E6.tag) E w)⁻¹ * pinnedX TwistTag.E6.tag E β c *
        canonicalRep (coxeterSystem TwistTag.E6.tag) E w =
      pinnedX TwistTag.E6.tag E (w⁻¹ • β) c := by
  have h := canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (IsRoot.smul hβ w⁻¹) c
  rw [smul_inv_smul] at h
  rw [← h]
  group

theorem thetaSL2_WSL_conj
    (h2 : (2 : E) = 0) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (c : E) :
    thetaSL2 E WSL * pinnedX TwistTag.E6.tag E β c * (thetaSL2 E WSL)⁻¹ =
      pinnedX TwistTag.E6.tag E (thetaWord.foldr (reflect TwistTag.E6.tag)
        (reflect TwistTag.E6.tag (e6Idx 0) (thetaWord.reverse.foldr (reflect TwistTag.E6.tag) β)))
        c := by
  set w := (coxeterSystem TwistTag.E6.tag).wordProd thetaWord with hw
  have hn : wordElt E thetaWord = canonicalRep (coxeterSystem TwistTag.E6.tag) E w :=
    wordElt_eq_canonicalRep h2 thetaWord
  have hm : weylElt TwistTag.E6.tag E (e6Idx 0) 1 =
      canonicalRep (coxeterSystem TwistTag.E6.tag) E
        ((coxeterSystem TwistTag.E6.tag).wordProd [e6Idx 0]) := by
    rw [← wordElt_eq_canonicalRep h2]
    simp [wordElt]
  have h1 := canonicalRep_inv_mul_pinnedX_mul h2 w hβ c
  have h2' := canonicalRep_mul_pinnedX_mul_inv_of_two h2
    ((coxeterSystem TwistTag.E6.tag).wordProd [e6Idx 0]) (IsRoot.smul hβ w⁻¹) c
  have h3 := canonicalRep_mul_pinnedX_mul_inv_of_two h2 w
    (IsRoot.smul (IsRoot.smul hβ w⁻¹) ((coxeterSystem TwistTag.E6.tag).wordProd [e6Idx 0])) c
  rw [thetaSL2_WSL, hn, hm]
  calc canonicalRep (coxeterSystem TwistTag.E6.tag) E w *
        canonicalRep (coxeterSystem TwistTag.E6.tag) E
          ((coxeterSystem TwistTag.E6.tag).wordProd [e6Idx 0]) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) E w)⁻¹ * pinnedX TwistTag.E6.tag E β c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) E w *
          canonicalRep (coxeterSystem TwistTag.E6.tag) E
            ((coxeterSystem TwistTag.E6.tag).wordProd [e6Idx 0]) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) E w)⁻¹)⁻¹ =
        canonicalRep (coxeterSystem TwistTag.E6.tag) E w *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) E
              ((coxeterSystem TwistTag.E6.tag).wordProd [e6Idx 0]) *
            ((canonicalRep (coxeterSystem TwistTag.E6.tag) E w)⁻¹ *
              pinnedX TwistTag.E6.tag E β c * canonicalRep (coxeterSystem TwistTag.E6.tag) E w) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) E
              ((coxeterSystem TwistTag.E6.tag).wordProd [e6Idx 0]))⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) E w)⁻¹ := by group
    _ = _ := by
      rw [h1, h2', h3, wordProd_smul, wordProd_smul, ← CoxeterSystem.wordProd_reverse,
        wordProd_smul]
      rfl

theorem thetaRefl_radList : ∀ β ∈ E6GraphRadical.radList,
    thetaWord.foldr (reflect TwistTag.E6.tag)
        (reflect TwistTag.E6.tag (e6Idx 0) (thetaWord.reverse.foldr (reflect TwistTag.E6.tag) β)) ∈
      rootFinset TwistTag.E6.tag ∧
    height (thetaWord.foldr (reflect TwistTag.E6.tag)
        (reflect TwistTag.E6.tag (e6Idx 0)
          (thetaWord.reverse.foldr (reflect TwistTag.E6.tag) β))) < 0 := by
  decide +kernel

theorem thetaSL2_WSL_conj_mem_negUnipotent
    (h2 : (2 : E) = 0) {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) :
    thetaSL2 E WSL * q * (thetaSL2 E WSL)⁻¹ ∈ negUnipotent TwistTag.E6.tag E := by
  have hle : parabolicRadical TwistTag.E6.tag E setA ≤ (negUnipotent TwistTag.E6.tag E).comap
      (MulAut.conj (thetaSL2 E WSL)).toMonoidHom := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    have hα' := (E6GraphRadical.mem_radList_iff α).2 hα
    obtain ⟨h1, h2'⟩ := thetaRefl_radList α hα'
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      thetaSL2_WSL_conj h2 (E6GraphRadical.radList_pos hα').1]
    exact pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ height α < 0})
      ⟨mem_rootFinset.1 h1, h2'⟩ c
  have := hle hq
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem thetaSL2_WSL_eq
    (h2 : (2 : E) = 0) :
    thetaSL2 E WSL = pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
      pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 * pinnedX TwistTag.E6.tag E e6HighestRoot 1 := by
  rw [WSL_eq_of_two h2, map_mul, map_mul, thetaSL2_uSL h2, thetaSL2_vSL h2]

end Weyl

section Radical

variable {E : Type} [Field E] {F₀ : Type} [Field F₀]

theorem two_eq_zero_of_map (ι : F₀ →+* E) (h2 : (2 : E) = 0) : (2 : F₀) = 0 :=
  (map_eq_zero_iff ι ι.injective).1 (by rw [map_ofNat]; exact h2)

theorem vSL_mul_self_of_two (h2 : (2 : F) = 0) : (vSL 1 : SL2 F) * vSL 1 = 1 := by
  refine SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h2

theorem vSL_ne_uSL : (vSL 1 : SL2 F) ≠ uSL 1 := fun h => by
  have := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_vSL, coe_uSL] at this

theorem comp_map_uSL
    (h2 : (2 : E) = 0) (ι : F₀ →+* E) (c : F₀) :
    (thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι) (uSL c) =
      pinnedX TwistTag.E6.tag E e6HighestRoot (ι c) := by
  rw [MonoidHom.comp_apply, map_uSL, thetaSL2_uSL h2]

theorem comp_map_vSL
    (h2 : (2 : E) = 0) (ι : F₀ →+* E) (c : F₀) :
    (thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι) (vSL c) =
      pinnedX TwistTag.E6.tag E (-e6HighestRoot) (ι c) := by
  rw [MonoidHom.comp_apply, map_vSL, thetaSL2_vSL h2]

theorem thetaRankOneGroup_inf_eq_bot
    (h2 : (2 : E) = 0) (ι : F₀ →+* E)
    {C : Subgroup (ModGL TwistTag.E6.tag E)}
    (hC : C ≤ Subgroup.centralizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E))) :
    thetaRankOneGroup ι ⊓ C = ⊥ := by
  have h2' := two_eq_zero_of_map ι h2
  set ρ := (thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι) with hρ
  have hinj : Function.Injective ρ := injective_thetaSL2_comp_map h2 ι
  have hXr : thetaRankOneGroup ι = ρ.range := thetaRankOneGroup_eq_range h2 ι
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgX, hgC⟩ := Subgroup.mem_inf.1 hg
  have hc := Subgroup.mem_centralizer_iff.1 (hC hgC)
  rw [hXr] at hgX
  obtain ⟨Y, rfl⟩ := hgX
  have hu := hc (ρ (uSL 1)) (by rw [SetLike.mem_coe, hXr]; exact ⟨_, rfl⟩)
  have hv := hc (ρ (vSL 1)) (by rw [SetLike.mem_coe, hXr]; exact ⟨_, rfl⟩)
  rw [← map_mul, ← map_mul] at hu hv
  rw [eq_one_of_commute h2' (hinj hu).symm (hinj hv).symm, map_one]
  exact Subgroup.one_mem _

theorem mem_thetaRootGroup_of_mem_normalizer
    (h2 : (2 : E) = 0) (ι : F₀ →+* E)
    {q₀ : ModGL TwistTag.E6.tag E} (hq : q₀ ∈ parabolicRadical TwistTag.E6.tag E setA)
    (hN : q₀ ∈ Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E))) :
    q₀ ∈ thetaRootGroup ι := by
  have h2' := two_eq_zero_of_map ι h2
  set ρ := (thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι) with hρ
  have hinj : Function.Injective ρ := injective_thetaSL2_comp_map h2 ι
  have hXr : thetaRankOneGroup ι = ρ.range := thetaRankOneGroup_eq_range h2 ι
  have hcomm : ∀ c, pinnedX TwistTag.E6.tag E e6HighestRoot c * q₀ =
      q₀ * pinnedX TwistTag.E6.tag E e6HighestRoot c := fun c => E6GraphRadical.theta_mul_comm hq c
  have hx : ρ (uSL 1) = pinnedX TwistTag.E6.tag E e6HighestRoot 1 := by
    rw [hρ, comp_map_uSL h2, map_one]
  have hy : ρ (vSL 1) = pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 := by
    rw [hρ, comp_map_vSL h2, map_one]
  have hzX := (Subgroup.mem_normalizer_iff.1 hN (ρ (vSL 1))).1 (by rw [hXr]; exact ⟨_, rfl⟩)
  rw [hXr] at hzX
  obtain ⟨Z, hZ⟩ := hzX
  have hZ2 : Z * Z = 1 := hinj (by
    rw [map_mul, hZ, map_one]
    calc q₀ * ρ (vSL 1) * q₀⁻¹ * (q₀ * ρ (vSL 1) * q₀⁻¹) = q₀ * ρ (vSL 1 * vSL 1) * q₀⁻¹ := by
          rw [map_mul]
          group
      _ = 1 := by rw [vSL_mul_self_of_two h2', map_one, mul_one, mul_inv_cancel])
  have hxz : ρ (uSL 1 * Z) = q₀ * ρ (uSL 1 * vSL 1) * q₀⁻¹ := by
    rw [map_mul, map_mul, hZ, hx]
    calc pinnedX TwistTag.E6.tag E e6HighestRoot 1 * (q₀ * ρ (vSL 1) * q₀⁻¹) =
          (pinnedX TwistTag.E6.tag E e6HighestRoot 1 * q₀) * ρ (vSL 1) * q₀⁻¹ := by group
      _ = q₀ * (pinnedX TwistTag.E6.tag E e6HighestRoot 1 * ρ (vSL 1)) * q₀⁻¹ := by
          rw [hcomm]
          group
  have hZ3 : uSL 1 * Z * (uSL 1 * Z * (uSL 1 * Z)) = 1 := hinj (by
    rw [map_mul ρ (uSL 1 * Z), map_mul ρ (uSL 1 * Z) (uSL 1 * Z), hxz, map_one]
    have h := uSL_mul_vSL_pow_three h2'
    rw [pow_succ, pow_succ, pow_one] at h
    calc q₀ * ρ (uSL 1 * vSL 1) * q₀⁻¹ *
          (q₀ * ρ (uSL 1 * vSL 1) * q₀⁻¹ * (q₀ * ρ (uSL 1 * vSL 1) * q₀⁻¹)) =
          q₀ * ρ (uSL 1 * vSL 1 * (uSL 1 * vSL 1) * (uSL 1 * vSL 1)) * q₀⁻¹ := by
          simp only [map_mul]
          group
      _ = 1 := by rw [h, map_one, mul_one, mul_inv_cancel])
  have hne : Z ≠ uSL 1 := by
    intro hZu
    apply vSL_ne_uSL (F := F₀)
    apply hinj
    calc ρ (vSL 1) = q₀⁻¹ * ρ Z * q₀ := by rw [hZ]; group
      _ = q₀⁻¹ * (ρ (uSL 1) * q₀) := by rw [hZu]; group
      _ = ρ (uSL 1) := by rw [hx, hcomm]; group
  set t := (Z : Matrix (Fin 2) (Fin 2) F₀) 0 0 + 1 with ht
  have hZt := eq_conj_vSL_of_two h2' hZ2 hZ3 hne
  have hθ : e6HighestRoot ∈ E6GraphRadical.radList := by decide
  set r := pinnedX TwistTag.E6.tag E e6HighestRoot (ι t) with hr
  have hrR : r ∈ thetaRootGroup ι := (mem_thetaRootGroup ι).2 ⟨t, rfl⟩
  have hq' : r⁻¹ * q₀ ∈ parabolicRadical TwistTag.E6.tag E setA :=
    mul_mem (inv_mem (E6GraphRadical.pinnedX_mem_parabolicRadical hθ _)) hq
  have hyfix : r⁻¹ * q₀ * pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 * (r⁻¹ * q₀)⁻¹ =
      pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 := by
    have e : q₀ * pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 * q₀⁻¹ =
        r * pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 * r⁻¹ := by
      rw [← hy, ← hZ, hZt, map_mul, map_mul, map_inv, hρ, comp_map_uSL h2, ← hρ, hy]
    calc r⁻¹ * q₀ * pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 * (r⁻¹ * q₀)⁻¹ =
          r⁻¹ * (q₀ * pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 * q₀⁻¹) * r := by group
      _ = _ := by rw [e]; group
  have hxfix : r⁻¹ * q₀ * pinnedX TwistTag.E6.tag E e6HighestRoot 1 * (r⁻¹ * q₀)⁻¹ =
      pinnedX TwistTag.E6.tag E e6HighestRoot 1 := by
    rw [← E6GraphRadical.theta_mul_comm hq', mul_inv_cancel_right]
  have hnfix : r⁻¹ * q₀ * thetaSL2 E WSL * (r⁻¹ * q₀)⁻¹ = thetaSL2 E WSL := by
    rw [thetaSL2_WSL_eq h2]
    calc r⁻¹ * q₀ * (pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
          pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 *
          pinnedX TwistTag.E6.tag E e6HighestRoot 1) * (r⁻¹ * q₀)⁻¹ =
          (r⁻¹ * q₀ * pinnedX TwistTag.E6.tag E e6HighestRoot 1 * (r⁻¹ * q₀)⁻¹) *
          (r⁻¹ * q₀ * pinnedX TwistTag.E6.tag E (-e6HighestRoot) 1 * (r⁻¹ * q₀)⁻¹) *
          (r⁻¹ * q₀ * pinnedX TwistTag.E6.tag E e6HighestRoot 1 * (r⁻¹ * q₀)⁻¹) := by group
      _ = _ := by rw [hxfix, hyfix]
  have hneg := thetaSL2_WSL_conj_mem_negUnipotent h2 hq'
  have heq : thetaSL2 E WSL * (r⁻¹ * q₀) * (thetaSL2 E WSL)⁻¹ = r⁻¹ * q₀ := by
    calc thetaSL2 E WSL * (r⁻¹ * q₀) * (thetaSL2 E WSL)⁻¹ =
          (r⁻¹ * q₀ * thetaSL2 E WSL * (r⁻¹ * q₀)⁻¹) * (r⁻¹ * q₀) * (thetaSL2 E WSL)⁻¹ := by
          rw [hnfix]
      _ = r⁻¹ * q₀ := by group
  rw [heq] at hneg
  have h1 : r⁻¹ * q₀ ∈ posUnipotent TwistTag.E6.tag E ⊓ negUnipotent TwistTag.E6.tag E :=
    Subgroup.mem_inf.2 ⟨parabolicRadical_le_posUnipotent setA hq', hneg⟩
  rw [Chevalley.posUnipotent_inf_negUnipotent, Subgroup.mem_bot, inv_mul_eq_one] at h1
  rw [← h1]
  exact hrR

end Radical

section Sylow

variable {E : Type} [Field E] {F₀ : Type} [Field F₀] [Finite F₀]

theorem card_thetaRankOneGroup
    (h2 : (2 : E) = 0) (ι : F₀ →+* E) :
    Nat.card (thetaRankOneGroup ι) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
  rw [thetaRankOneGroup_eq_range h2 ι,
    ← Nat.card_congr (MonoidHom.ofInjective (injective_thetaSL2_comp_map h2 ι)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num)]
  simp

omit [Finite F₀] in
theorem card_thetaRootGroup
    (ι : F₀ →+* E) : Nat.card (thetaRootGroup ι) = Nat.card F₀ := by
  have hbij : Function.Bijective fun c : F₀ =>
      (⟨pinnedX TwistTag.E6.tag E e6HighestRoot (ι c), (mem_thetaRootGroup ι).2 ⟨c, rfl⟩⟩ :
        thetaRootGroup ι) := by
    refine ⟨fun c d h => ?_, fun g => ?_⟩
    · have h' := congrArg (fun x : thetaRootGroup ι => (x : ModGL TwistTag.E6.tag E)) h
      simp only at h'
      exact ι.injective (pinnedX_injective (τ := TwistTag.E6.tag) (R := E) e6HighestRoot h')
    obtain ⟨g, hg⟩ := g
    obtain ⟨c, hc⟩ := (mem_thetaRootGroup ι).1 hg
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem exists_two_pow_card (h2 : (2 : F₀) = 0) : ∃ m : ℕ, 1 ≤ m ∧ Nat.card F₀ = 2 ^ m := by
  have : Fintype F₀ := Fintype.ofFinite F₀
  have : CharP F₀ 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨n, -, hn⟩ := FiniteField.card F₀ 2
  exact ⟨n, n.2, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem isPGroup_and_not_dvd_index
    (h2 : (2 : E) = 0) (ι : F₀ →+* E)
    {S : Subgroup (thetaRankOneGroup ι)} (hS : Nat.card S = Nat.card F₀) :
    IsPGroup 2 S ∧ ¬ 2 ∣ S.index := by
  obtain ⟨m, hm, hq⟩ := exists_two_pow_card (two_eq_zero_of_map ι h2)
  refine ⟨IsPGroup.of_card (hS.trans hq), fun hdvd => ?_⟩
  have h := S.card_mul_index
  rw [hS, card_thetaRankOneGroup h2 ι] at h
  have hpos : 0 < Nat.card F₀ := by rw [hq]; positivity
  have hi : S.index = Nat.card F₀ ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left hpos h
  have h2q : 2 ∣ Nat.card F₀ ^ 2 := dvd_pow (by rw [hq]; exact dvd_pow_self 2 (by omega))
    two_ne_zero
  have hq1 : 1 ≤ Nat.card F₀ ^ 2 := Nat.one_le_pow _ _ hpos
  rw [hi] at hdvd
  omega

theorem exists_mul_mem_normalizer
    (h2 : (2 : E) = 0) (ι : F₀ →+* E) {n : ModGL TwistTag.E6.tag E}
    (hn : n ∈ Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E))) :
    ∃ x ∈ thetaRankOneGroup ι,
      x * n ∈ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : thetaRootGroup ι ≤ thetaRankOneGroup ι := le_sup_left
  have : Finite (thetaRankOneGroup ι) := Nat.finite_of_card_ne_zero (by
    rw [card_thetaRankOneGroup h2 ι]
    obtain ⟨m, hm, hq⟩ := exists_two_pow_card (two_eq_zero_of_map ι h2)
    rw [hq]
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm
    have : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
    exact Nat.mul_ne_zero (by positivity) (by omega))
  have hRn : (thetaRootGroup ι).map (MulAut.conj n).toMonoidHom ≤ thetaRankOneGroup ι := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hn r).1 (hRX hr)
  set P₁ := (thetaRootGroup ι).subgroupOf (thetaRankOneGroup ι) with hP₁
  set P₂ := ((thetaRootGroup ι).map (MulAut.conj n).toMonoidHom).subgroupOf
    (thetaRankOneGroup ι) with hP₂
  have hc₁ : Nat.card P₁ = Nat.card F₀ :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv).trans (card_thetaRootGroup ι)
  have hc₂ : Nat.card P₂ = Nat.card F₀ :=
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRn).toEquiv).trans
      (Subgroup.card_map_of_injective (MulAut.conj n).injective)).trans (card_thetaRootGroup ι)
  obtain ⟨hp₁, hi₁⟩ := isPGroup_and_not_dvd_index h2 ι hc₁
  obtain ⟨hp₂, hi₂⟩ := isPGroup_and_not_dvd_index h2 ι hc₂
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (thetaRankOneGroup ι) (hp₂.toSylow hi₂)
    (hp₁.toSylow hi₁)
  have hmem : ∀ r ∈ thetaRootGroup ι, (x : ModGL TwistTag.E6.tag E) * n * r *
      ((x : ModGL TwistTag.E6.tag E) * n)⁻¹ ∈ thetaRootGroup ι := by
    intro r hr
    have h1 : (⟨n * r * n⁻¹, hRn ⟨r, hr, rfl⟩⟩ : thetaRankOneGroup ι) ∈ P₂ :=
      Subgroup.mem_subgroupOf.2 ⟨r, hr, rfl⟩
    have h2' : MulAut.conj x • (⟨n * r * n⁻¹, hRn ⟨r, hr, rfl⟩⟩ : thetaRankOneGroup ι) ∈
        ((x • hp₂.toSylow hi₂ : Sylow 2 (thetaRankOneGroup ι)) :
          Subgroup (thetaRankOneGroup ι)) := by
      rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hx, IsPGroup.toSylow_coe] at h2'
    have h3 := Subgroup.mem_subgroupOf.1 h2'
    rw [MulAut.smul_def, MulAut.conj_apply] at h3
    simpa [mul_assoc] using h3
  have hle : (thetaRootGroup ι).map (MulAut.conj ((x : ModGL TwistTag.E6.tag E) * n)).toMonoidHom ≤
      thetaRootGroup ι := by
    rintro _ ⟨r, hr, rfl⟩
    exact hmem r hr
  have : Finite (thetaRootGroup ι) := Nat.finite_of_card_ne_zero (by
    rw [card_thetaRootGroup ι]
    exact Nat.card_pos.ne')
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])
  refine ⟨x, x.2, Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hmem h hh, fun hh => ?_⟩⟩
  rw [← heq] at hh
  obtain ⟨r, hr, hrh⟩ := hh
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hrh
  have : r = h := by
    have := congrArg (fun g => ((x : ModGL TwistTag.E6.tag E) * n)⁻¹ * g *
      ((x : ModGL TwistTag.E6.tag E) * n)) hrh
    simpa [mul_assoc] using this
  rw [← this]
  exact hr

end Sylow

end CFSG.LieType.Chevalley.E6GraphRootSL2
