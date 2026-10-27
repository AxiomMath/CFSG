module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3SimpSec
public import CFSG.LieType.SteinbergBRSemidirectSL2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open scoped MatrixGroups
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

private def sl2Of (F : Type) [Field F] (M : Matrix (Fin 2) (Fin 2) F) (h : M.det = 1) :
    SL(2, F) :=
  ⟨M, h⟩

private def zOrd3 (F : Type) [Field F] : SL(2, F) :=
  sl2Of F !![0, -1; 1, -1] (by simp [Matrix.det_fin_two])

private def eUp (F : Type) [Field F] : SL(2, F) :=
  sl2Of F !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])

private def eLow (F : Type) [Field F] : SL(2, F) :=
  sl2Of F !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])

private theorem zOrd3_pow_three (F : Type) [Field F] : zOrd3 F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  show (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_three, Matrix.mul_apply, Fin.sum_univ_two]

private theorem zOrd3_ne_one (F : Type) [Field F] : zOrd3 F ≠ 1 := by
  intro h
  have h01 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [zOrd3, sl2Of] at h01

private theorem zOrd3_orderOf (F : Type) [Field F] : orderOf (zOrd3 F) = 3 :=
  orderOf_eq_prime (zOrd3_pow_three F) (zOrd3_ne_one F)

private theorem eUp_not_mem_center (F : Type) [Field F] :
    eUp F ∉ Subgroup.center (SL(2, F)) := by
  intro h
  rcases CFSG.LieType.SteinbergBR.mem_center_SL2_iff.mp h with h1 | h1
  · have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) h1
    simp [eUp, sl2Of] at e
  · have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) h1
    simp [eUp, sl2Of] at e

private theorem sq_of_mem_center (F : Type) [Field F] {s : SL(2, F)}
    (hs : s ∈ Subgroup.center (SL(2, F))) : s ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  rcases CFSG.LieType.SteinbergBR.mem_center_SL2_iff.mp hs with h1 | h1 <;> simp [h1]

private theorem neg_one_mem_center (F : Type) [Field F] :
    (-1 : SL(2, F)) ∈ Subgroup.center (SL(2, F)) :=
  CFSG.LieType.SteinbergBR.mem_center_SL2_iff.mpr (Or.inr (by simp))

private theorem neg_one_ne_one_SL (F : Type) [Field F] (hp2 : ringChar F ≠ 2) :
    (-1 : SL(2, F)) ≠ 1 := by
  intro h
  apply Ring.neg_one_ne_one_of_char_ne_two hp2
  have h00 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simpa using h00

private theorem quot_nonabelian (F : Type) [Field F] (hp2 : ringChar F ≠ 2) :
    ∃ a b : SL(2, F) ⧸ Subgroup.center (SL(2, F)), a * b ≠ b * a := by
  refine ⟨((eUp F : SL(2, F)) : SL(2, F) ⧸ Subgroup.center (SL(2, F))),
    ((eLow F : SL(2, F)) : SL(2, F) ⧸ Subgroup.center (SL(2, F))), ?_⟩
  intro h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have hm : (eUp F * eLow F) * ((eUp F * eLow F)⁻¹ * (eLow F * eUp F)) = eLow F * eUp F :=
    mul_inv_cancel_left _ _
  generalize (eUp F * eLow F)⁻¹ * (eLow F * eUp F) = c at h hm
  have hmat : (eUp F : Matrix (Fin 2) (Fin 2) F) * (eLow F : Matrix (Fin 2) (Fin 2) F) *
      (c : Matrix (Fin 2) (Fin 2) F) =
      (eLow F : Matrix (Fin 2) (Fin 2) F) * (eUp F : Matrix (Fin 2) (Fin 2) F) :=
    congrArg Subtype.val hm
  have hU : (eUp F : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
  have hL : (eLow F : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
  rw [hU, hL] at hmat
  rcases CFSG.LieType.SteinbergBR.mem_center_SL2_iff.mp h with h1 | h1
  · rw [h1, Matrix.mul_one] at hmat
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hmat
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  · rw [h1, Matrix.mul_neg, Matrix.mul_one] at hmat
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hmat
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    exact Ring.neg_one_ne_one_of_char_ne_two hp2 (by simpa using e)

private theorem simple_section_SL2 (F : Type) [Field F] {A : Type} [Group A]
    (h5 : 5 ≤ Nat.card F) (hp2 : ringChar F ≠ 2) (φ : SL(2, F) →* A)
    (hφ : Function.Injective φ) :
    S622IsSimpleSection φ.range (Subgroup.map φ (Subgroup.center (SL(2, F)))) := by
  have hsimple : IsSimpleGroup (SL(2, F) ⧸ Subgroup.center (SL(2, F))) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hD : Subgroup.center (SL(2, F)) ≠ ⊤ := fun h =>
    eUp_not_mem_center F (by rw [h]; exact Subgroup.mem_top _)
  exact isSimpleSection_range_map φ hφ (Subgroup.center (SL(2, F))) hD hsimple
    (quot_nonabelian F hp2)

private theorem map_center_ne_bot (F : Type) [Field F] {A : Type} [Group A]
    (hp2 : ringChar F ≠ 2) (φ : SL(2, F) →* A) (hφ : Function.Injective φ) :
    Subgroup.map φ (Subgroup.center (SL(2, F))) ≠ ⊥ := by
  intro h
  have hm : φ (-1) ∈ Subgroup.map φ (Subgroup.center (SL(2, F))) :=
    Subgroup.mem_map_of_mem φ (neg_one_mem_center F)
  rw [h, Subgroup.mem_bot] at hm
  exact neg_one_ne_one_SL F hp2 (hφ (by rw [hm, map_one]))

private theorem map_center_isPGroup (F : Type) [Field F] {A : Type} [Group A]
    (φ : SL(2, F) →* A) :
    IsPGroup 2 (Subgroup.map φ (Subgroup.center (SL(2, F)))) := by
  intro g
  obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hsg, ← map_pow, sq_of_mem_center F hs,
    map_one]

private theorem range_le_centralizer (F : Type) [Field F] {A : Type} [Group A]
    (φ : SL(2, F) →* A) :
    φ.range ≤ Subgroup.centralizer
      ((Subgroup.map φ (Subgroup.center (SL(2, F))) : Subgroup A) : Set A) := by
  intro y hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp (SetLike.mem_coe.mp hh)
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs x]

private theorem not_mem_map_center (F : Type) [Field F] {A : Type} [Group A]
    (φ : SL(2, F) →* A) {z : A} (hz3 : orderOf z = 3) :
    z ∉ Subgroup.map φ (Subgroup.center (SL(2, F))) := by
  intro hzN
  obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.mp hzN
  have hz2 : z ^ 2 = 1 := by
    rw [← hsz, ← map_pow, sq_of_mem_center F hs, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hz2
  rw [hz3] at hdvd
  omega

theorem l3u3_exists_section {A : Type} [Group A] [Finite A] (L : Subgroup A) (z : A)
    {F₀ : Type} [Field F₀] [Finite F₀] (h5 : 5 ≤ Nat.card F₀) (hp2 : ringChar F₀ ≠ 2)
    (hp3 : ringChar F₀ ≠ 3)
    (ι : SL(2, F₀) →* ↥L) (hι : Function.Injective ι)
    (hconj : ∀ a b : ↥L, orderOf a = 3 → orderOf b = 3 → ∃ g : ↥L, g * a * g⁻¹ ∈ Subgroup.zpowers b)
    (hzL : z ∈ L) (hz3 : orderOf z = 3) :
    ∃ K₀ N : Subgroup A, K₀ ≤ L ∧ z ∈ K₀ ∧ z ∉ N ∧
      S622IsSimpleSection K₀ N ∧ N ≠ ⊥ ∧ IsPGroup 2 N ∧ K₀ ≤ Subgroup.centralizer (N : Set A) := by
  clear hp3
  obtain ⟨b, hbz⟩ : ∃ b : ↥L, (b : A) = z := ⟨⟨z, hzL⟩, rfl⟩
  have hb : orderOf b = 3 := by
    rw [← Subgroup.orderOf_coe, hbz]
    exact hz3
  have ha : orderOf (ι (zOrd3 F₀)) = 3 := by
    rw [orderOf_injective ι hι (zOrd3 F₀), zOrd3_orderOf F₀]
  obtain ⟨g, hg⟩ := hconj (ι (zOrd3 F₀)) b ha hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hb3 : b ^ (3 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one b
    rw [hb] at h
    exact_mod_cast h
  have hk3 : k % 3 ≠ 0 := by
    intro h0
    have hsplit : b ^ k = (b ^ (3 : ℤ)) ^ (k / 3) := by
      rw [← zpow_mul]
      congr 1
      omega
    have hbk : b ^ k = 1 := by rw [hsplit, hb3, one_zpow]
    have h1 : g * ι (zOrd3 F₀) * g⁻¹ = 1 := hk.symm.trans hbk
    have h2 : ι (zOrd3 F₀) = 1 := by simpa using h1
    exact zOrd3_ne_one F₀ (hι (show ι (zOrd3 F₀) = ι 1 by rw [h2, map_one]))
  have hkk : b ^ (k * k) = b := by
    have hmod : (k * k) % 3 = 1 := by
      rcases (show k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h <;>
        rw [Int.mul_emod, h] <;> norm_num
    have key : b ^ (k * k % 3) = b ^ (k * k) := by
      have h := zpow_mod_orderOf b (k * k)
      rw [hb] at h
      exact_mod_cast h
    rw [hmod, zpow_one] at key
    exact key.symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SL(2, F₀) →* ↥L, ∀ x, ψ x = g * ι x * g⁻¹ :=
    ⟨(MulAut.conj g).toMonoidHom.comp ι, fun x => rfl⟩
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    rw [hψ, hψ] at hxy
    exact hι (mul_left_cancel (mul_right_cancel hxy))
  obtain ⟨φ, hφ⟩ : ∃ φ : SL(2, F₀) →* A, ∀ x, φ x = (ψ x : A) :=
    ⟨L.subtype.comp ψ, fun x => rfl⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rw [hφ, hφ] at hxy
    exact hψinj (Subtype.ext hxy)
  have hφk : φ (zOrd3 F₀ ^ k) = z := by
    rw [← hbz, hφ, map_zpow, hψ, ← hk, ← zpow_mul, hkk]
  refine ⟨φ.range, Subgroup.map φ (Subgroup.center (SL(2, F₀))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [hφ]
    exact (ψ x).2
  · exact MonoidHom.mem_range.mpr ⟨zOrd3 F₀ ^ k, hφk⟩
  · exact not_mem_map_center F₀ φ hz3
  · exact simple_section_SL2 F₀ h5 hp2 φ hφinj
  · exact map_center_ne_bot F₀ hp2 φ hφinj
  · exact map_center_isPGroup F₀ φ
  · exact range_le_centralizer F₀ φ

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
