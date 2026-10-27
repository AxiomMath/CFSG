module

public import CFSG.RankThree.Native.HSMcLSmall
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native


@[expose] def hsA3Arr : Array ℕ := #[0, 1, 11, 52, 96, 5, 13, 4, 82, 62, 28, 26, 92, 65, 84, 35, 24, 43, 3, 8, 55, 61, 22, 95, 93, 54, 2, 12, 94, 9, 47, 90, 41, 36, 98, 74, 78, 97, 91, 39, 66, 73, 20, 44, 17, 31, 85, 68, 25, 56, 50, 51, 18, 21, 48, 42, 87, 86, 37, 46, 60, 53, 29, 14, 88, 6, 89, 57, 30, 69, 81, 23, 64, 32, 15, 77, 38, 80, 33, 79, 75, 99, 19, 34, 63, 59, 67, 49, 72, 40, 45, 76, 27, 16, 10, 71, 7, 58, 83, 70]

@[expose] def hsB3Arr : Array ℕ := #[0, 1, 89, 52, 36, 39, 71, 33, 83, 62, 31, 40, 12, 23, 16, 82, 67, 70, 3, 98, 20, 53, 79, 68, 57, 87, 66, 27, 90, 9, 65, 64, 25, 59, 15, 19, 46, 11, 76, 50, 37, 54, 42, 81, 99, 72, 4, 6, 56, 41, 5, 22, 18, 61, 49, 55, 73, 84, 2, 7, 60, 21, 29, 93, 10, 95, 97, 14, 13, 69, 75, 47, 94, 48, 8, 17, 91, 43, 85, 51, 44, 77, 34, 74, 24, 96, 63, 32, 28, 58, 88, 38, 92, 86, 45, 30, 78, 26, 35, 80]

@[expose] def hsG3Arr : Array ℕ := #[60, 0, 4, 39, 89, 12, 28, 2, 71, 22, 17, 36, 91, 90, 49, 95, 73, 34, 5, 6, 53, 29, 42, 72, 48, 24, 46, 76, 70, 51, 31, 81, 14, 40, 13, 30, 37, 7, 3, 92, 85, 16, 21, 15, 82, 43, 26, 64, 84, 63, 27, 55, 50, 62, 57, 61, 93, 87, 59, 97, 69, 9, 79, 54, 80, 88, 96, 25, 10, 1, 35, 45, 99, 67, 65, 8, 18, 83, 11, 20, 74, 19, 47, 68, 41, 66, 32, 86, 44, 78, 77, 52, 38, 56, 75, 94, 58, 33, 23, 98]

@[expose] def hsX5Arr : Array ℕ := #[55, 94, 7, 43, 76, 26, 85, 88, 99, 64, 22, 51, 95, 1, 49, 57, 42, 25, 50, 47, 35, 67, 34, 96, 73, 79, 83, 92, 5, 66, 16, 53, 74, 82, 52, 61, 24, 17, 27, 30, 23, 32, 44, 45, 39, 77, 6, 69, 46, 19, 97, 38, 71, 65, 41, 59, 0, 8, 13, 89, 54, 78, 40, 75, 18, 12, 21, 93, 37, 14, 4, 10, 2, 63, 60, 36, 33, 91, 98, 68, 62, 58, 70, 87, 72, 86, 48, 28, 84, 56, 15, 3, 11, 29, 81, 31, 80, 9, 20, 90]

@[expose] def hsY5Arr : Array ℕ := #[86, 88, 89, 37, 0, 75, 7, 84, 43, 38, 67, 79, 52, 59, 47, 68, 31, 27, 18, 60, 95, 65, 12, 28, 69, 25, 14, 8, 83, 71, 29, 53, 49, 94, 16, 42, 63, 57, 3, 34, 74, 36, 44, 64, 98, 45, 55, 5, 33, 80, 77, 97, 61, 39, 87, 4, 1, 9, 82, 56, 32, 78, 96, 54, 17, 20, 21, 30, 91, 73, 76, 10, 70, 62, 23, 26, 2, 90, 22, 50, 19, 6, 48, 40, 85, 81, 46, 41, 13, 72, 11, 51, 92, 35, 58, 66, 24, 15, 93, 99]

@[expose] def hsG5Arr : Array ℕ := #[3, 8, 64, 86, 11, 31, 57, 92, 33, 7, 83, 85, 49, 9, 20, 76, 60, 6, 81, 22, 24, 47, 19, 65, 61, 89, 67, 72, 34, 28, 54, 75, 52, 37, 40, 36, 12, 70, 94, 23, 42, 98, 80, 13, 63, 4, 91, 29, 77, 66, 1, 84, 62, 32, 71, 27, 97, 59, 68, 45, 30, 87, 93, 35, 0, 73, 74, 41, 46, 78, 25, 69, 38, 39, 44, 53, 51, 82, 96, 55, 21, 79, 43, 95, 15, 17, 99, 10, 90, 50, 2, 58, 48, 5, 18, 14, 16, 56, 26, 88]

@[expose] def hsU11Arr : Array ℕ := #[0, 4, 11, 81, 18, 53, 27, 93, 15, 39, 48, 42, 50, 68, 45, 73, 76, 36, 52, 57, 24, 29, 96, 12, 1, 32, 51, 65, 97, 69, 62, 54, 28, 80, 14, 20, 49, 72, 60, 47, 70, 33, 74, 75, 26, 85, 35, 71, 89, 98, 21, 37, 67, 30, 90, 66, 94, 10, 99, 84, 22, 92, 6, 64, 82, 61, 87, 56, 5, 9, 3, 95, 8, 41, 88, 2, 58, 40, 83, 59, 44, 63, 79, 17, 77, 55, 91, 16, 25, 38, 7, 19, 13, 78, 46, 23, 86, 43, 31, 34]

@[expose] def hsH11Arr : Array ℕ := #[0, 2, 26, 82, 74, 62, 6, 90, 91, 29, 45, 72, 23, 92, 1, 10, 46, 7, 32, 16, 25, 9, 87, 47, 97, 8, 86, 61, 44, 71, 13, 93, 41, 19, 35, 42, 83, 89, 34, 39, 40, 96, 73, 15, 60, 52, 75, 95, 66, 49, 21, 57, 43, 65, 17, 20, 88, 99, 18, 3, 85, 30, 53, 70, 63, 68, 4, 11, 5, 12, 81, 50, 22, 38, 80, 33, 24, 59, 36, 77, 48, 84, 79, 31, 64, 94, 14, 67, 51, 76, 98, 55, 27, 78, 28, 69, 58, 37, 54, 56]

@[expose] def hsPwArr (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 100
  | k + 1 => compA 100 t (hsPwArr t k)

@[expose] def hsZArr : Array ℕ :=
  compA 100 (compA 100 (compA 100 hsX5Arr hsY5Arr) (invCand 100 hsX5Arr)) (invCand 100 hsY5Arr)

abbrev KGHS3HSChecks : Prop :=
  validA 100 hsA3Arr = true ∧ validA 100 hsB3Arr = true ∧ validA 100 hsG3Arr = true ∧
  validA 100 hsX5Arr = true ∧ validA 100 hsY5Arr = true ∧ validA 100 hsG5Arr = true ∧
  validA 100 hsU11Arr = true ∧ validA 100 hsH11Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsA3Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsB3Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsG3Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsX5Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsY5Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsG5Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsU11Arr = true ∧
  siftA 100 hs100PLevels hs100BaseArr 0 hsH11Arr = true ∧
  eqA 100 (hsPwArr hsA3Arr 3) (idA 100) = true ∧ eqA 100 (hsPwArr hsB3Arr 3) (idA 100) = true ∧
  eqA 100 hsA3Arr (idA 100) = false ∧
  eqA 100 (compA 100 hsA3Arr hsB3Arr) (compA 100 hsB3Arr hsA3Arr) = true ∧
  eqA 100 (compA 100 hsG3Arr hsA3Arr) (compA 100 hsB3Arr hsG3Arr) = true ∧
  eqA 100 (compA 100 hsG3Arr hsB3Arr) (compA 100 (compA 100 hsA3Arr hsB3Arr) hsG3Arr) = true ∧
  eqA 100 (hsPwArr hsZArr 5) (idA 100) = true ∧ eqA 100 hsZArr (idA 100) = false ∧
  eqA 100 (compA 100 hsX5Arr hsZArr) (compA 100 hsZArr hsX5Arr) = true ∧
  eqA 100 (compA 100 hsY5Arr hsZArr) (compA 100 hsZArr hsY5Arr) = true ∧
  eqA 100 (compA 100 hsG5Arr hsZArr) (compA 100 (hsPwArr hsZArr 2) hsG5Arr) = true ∧
  eqA 100 (hsPwArr hsU11Arr 11) (idA 100) = true ∧ eqA 100 hsU11Arr (idA 100) = false ∧
  eqA 100 (compA 100 hsH11Arr hsU11Arr) (compA 100 (hsPwArr hsU11Arr 3) hsH11Arr) = true

theorem rep_hsPwArr {t : Array ℕ} {g : Equiv.Perm (Fin 100)} (ht : Rep 100 t g) :
    ∀ k, Rep 100 (hsPwArr t k) (g ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA ht (rep_hsPwArr ht k)

theorem hsPowEqOne {t : Array ℕ} {g : Equiv.Perm (Fin 100)} (ht : Rep 100 t g) {k : ℕ}
    (h : eqA 100 (hsPwArr t k) (idA 100) = true) : g ^ k = 1 :=
  (eqA_iff (rep_hsPwArr ht k) rep_idA).1 h

theorem hsNeOne {t : Array ℕ} {g : Equiv.Perm (Fin 100)} (ht : Rep 100 t g)
    (h : eqA 100 t (idA 100) = false) : g ≠ 1 := fun h1 => by
  have := (eqA_iff ht rep_idA).2 h1
  rw [h] at this
  exact Bool.false_ne_true this

theorem mem_of_hsSift {t : Array ℕ} (hv : validA 100 t = true)
    (hs : siftA 100 hs100PLevels hs100BaseArr 0 t = true) : permOfArr 100 t ∈ hs100P := by
  rw [hs100P_eq_original]
  exact mem_of_siftA hs100ChainArrays hs100_chain_check.1 (rep_of_validA hv) hs

noncomputable def hsElemP {t : Array ℕ} (hv : validA 100 t = true)
    (hs : siftA 100 hs100PLevels hs100BaseArr 0 t = true) : hs100P :=
  ⟨permOfArr 100 t, mem_of_hsSift hv hs⟩

theorem hsC3_of_checks (hK : KGHS3HSChecks) : ∃ a b g : Carrier .HS, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
    a * b = b * a ∧ a ≠ 1 ∧ g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a * b := by
  obtain ⟨hva, hvb, hvg, hvx, hvy, hvg5, hvu, hvh, hsa, hsb, hsg, hsx, hsy, hsg5, hsu, hsh,
    hra3, hrb3, hra3ne, hrab, hrg3a, hrg3b, hrz5, hrzne, hrxz, hryz, hrgz, hru11, hru11ne,
    hrh11⟩ := hK
  let e : Carrier .HS ≃* hs100P := hs100Equiv
  let aP := hsElemP hva hsa
  let bP := hsElemP hvb hsb
  let gP := hsElemP hvg hsg
  have ha : Rep 100 hsA3Arr (aP : Equiv.Perm (Fin 100)) := rep_of_validA hva
  have hb : Rep 100 hsB3Arr (bP : Equiv.Perm (Fin 100)) := rep_of_validA hvb
  have hg : Rep 100 hsG3Arr (gP : Equiv.Perm (Fin 100)) := rep_of_validA hvg
  have h3a : aP ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hsPowEqOne ha hra3)
  have h3b : bP ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hsPowEqOne hb hrb3)
  have hne : aP ≠ 1 := fun h => hsNeOne ha hra3ne (congrArg Subtype.val h)
  have hab : aP * bP = bP * aP :=
    Subtype.ext (eq_of_eqA (rep_compA ha hb) (rep_compA hb ha) hrab)
  have hgab : gP * aP * gP⁻¹ = bP :=
    mul_inv_eq_iff_eq_mul.2 (Subtype.ext (eq_of_eqA (rep_compA hg ha) (rep_compA hb hg) hrg3a))
  have hgbb : gP * bP * gP⁻¹ = aP * bP :=
    mul_inv_eq_iff_eq_mul.2 (Subtype.ext (eq_of_eqA (rep_compA hg hb)
      (rep_compA (rep_compA ha hb) hg) hrg3b))
  refine ⟨e.symm aP, e.symm bP, e.symm gP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h3a, map_one]
  · rw [← map_pow, h3b, map_one]
  · rw [← map_mul, ← map_mul, hab]
  · intro h
    apply hne
    apply e.symm.injective
    rw [h, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hgab]
  · rw [← map_inv, ← map_mul, ← map_mul, hgbb, map_mul]

theorem hsC5_of_checks (hK : KGHS3HSChecks) : ∃ x y z g : Carrier .HS, z = x * y * x⁻¹ * y⁻¹ ∧
    z ^ 5 = 1 ∧ z ≠ 1 ∧ x * z = z * x ∧ y * z = z * y ∧ g * z * g⁻¹ = z ^ 2 := by
  obtain ⟨hva, hvb, hvg, hvx, hvy, hvg5, hvu, hvh, hsa, hsb, hsg, hsx, hsy, hsg5, hsu, hsh,
    hra3, hrb3, hra3ne, hrab, hrg3a, hrg3b, hrz5, hrzne, hrxz, hryz, hrgz, hru11, hru11ne,
    hrh11⟩ := hK
  let e : Carrier .HS ≃* hs100P := hs100Equiv
  let xP := hsElemP hvx hsx
  let yP := hsElemP hvy hsy
  let gP := hsElemP hvg5 hsg5
  have hx : Rep 100 hsX5Arr (xP : Equiv.Perm (Fin 100)) := rep_of_validA hvx
  have hy : Rep 100 hsY5Arr (yP : Equiv.Perm (Fin 100)) := rep_of_validA hvy
  have hg : Rep 100 hsG5Arr (gP : Equiv.Perm (Fin 100)) := rep_of_validA hvg5
  obtain ⟨zP, hzP⟩ : ∃ z : hs100P, z = xP * yP * xP⁻¹ * yP⁻¹ := ⟨_, rfl⟩
  have hz : Rep 100 hsZArr (zP : Equiv.Perm (Fin 100)) := by
    rw [hzP]
    exact rep_compA (rep_compA (rep_compA hx hy) (rep_inv_of_validA hvx)) (rep_inv_of_validA hvy)
  have hz5 : zP ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hsPowEqOne hz hrz5)
  have hzne : zP ≠ 1 := fun h => hsNeOne hz hrzne (congrArg Subtype.val h)
  have hxz : xP * zP = zP * xP :=
    Subtype.ext (eq_of_eqA (rep_compA hx hz) (rep_compA hz hx) hrxz)
  have hyz : yP * zP = zP * yP :=
    Subtype.ext (eq_of_eqA (rep_compA hy hz) (rep_compA hz hy) hryz)
  have hgz : gP * zP * gP⁻¹ = zP ^ 2 := mul_inv_eq_iff_eq_mul.2 (Subtype.ext
    (eq_of_eqA (rep_compA hg hz) (rep_compA (rep_hsPwArr hz 2) hg) hrgz))
  have hzE : e.symm zP = e.symm xP * e.symm yP * (e.symm xP)⁻¹ * (e.symm yP)⁻¹ := by
    rw [hzP, map_mul, map_mul, map_mul, map_inv, map_inv]
  refine ⟨e.symm xP, e.symm yP, e.symm xP * e.symm yP * (e.symm xP)⁻¹ * (e.symm yP)⁻¹,
    e.symm gP, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hzE, ← map_pow, hz5, map_one]
  · rw [← hzE]
    intro h
    apply hzne
    apply e.symm.injective
    rw [h, map_one]
  · rw [← hzE, ← map_mul, ← map_mul, hxz]
  · rw [← hzE, ← map_mul, ← map_mul, hyz]
  · rw [← hzE, ← map_inv, ← map_mul, ← map_mul, ← map_pow, hgz]

theorem hsC11_of_checks (hK : KGHS3HSChecks) : ∃ u h : Carrier .HS, u ^ 11 = 1 ∧ u ≠ 1 ∧
    h * u * h⁻¹ = u ^ 3 := by
  obtain ⟨hva, hvb, hvg, hvx, hvy, hvg5, hvu, hvh, hsa, hsb, hsg, hsx, hsy, hsg5, hsu, hsh,
    hra3, hrb3, hra3ne, hrab, hrg3a, hrg3b, hrz5, hrzne, hrxz, hryz, hrgz, hru11, hru11ne,
    hrh11⟩ := hK
  let e : Carrier .HS ≃* hs100P := hs100Equiv
  let uP := hsElemP hvu hsu
  let hP := hsElemP hvh hsh
  have hu : Rep 100 hsU11Arr (uP : Equiv.Perm (Fin 100)) := rep_of_validA hvu
  have hh : Rep 100 hsH11Arr (hP : Equiv.Perm (Fin 100)) := rep_of_validA hvh
  have hu11 : uP ^ 11 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hsPowEqOne hu hru11)
  have hune : uP ≠ 1 := fun h => hsNeOne hu hru11ne (congrArg Subtype.val h)
  have hhu : hP * uP * hP⁻¹ = uP ^ 3 := mul_inv_eq_iff_eq_mul.2 (Subtype.ext
    (eq_of_eqA (rep_compA hh hu) (rep_compA (rep_hsPwArr hu 3) hh) hrh11))
  refine ⟨e.symm uP, e.symm hP, ?_, ?_, ?_⟩
  · rw [← map_pow, hu11, map_one]
  · intro h
    apply hune
    apply e.symm.injective
    rw [h, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, hhu]

end CFSG.ComponentClassification.CatFC.KGHS3
