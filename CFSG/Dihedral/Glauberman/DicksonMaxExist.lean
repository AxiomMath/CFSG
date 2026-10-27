module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split

public section

namespace CFSG.Glauberman.Dickson

open BenderSuzuki.MatrixGroups

universe u v

theorem exists_cyclic_subgroup_card {G : Type*} [Group G] (A : Subgroup G) [IsCyclic A]
    [Finite A] {z : ℕ} (hz : z ∣ Nat.card A) :
    ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = z ∧ IsCyclic H := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  have hn : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hn (zero_dvd_iff.mp hz)
  have hd : Nat.card A / z ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hz)
    (Nat.pos_of_ne_zero hz0)).ne'
  refine ⟨Subgroup.zpowers ((g ^ (Nat.card A / z) : A) : G), ?_, ?_, inferInstance⟩
  · rw [Subgroup.zpowers_le]
    exact (g ^ (Nat.card A / z)).2
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe,
      orderOf_pow_of_dvd hd (by rw [hg]; exact Nat.div_dvd_of_dvd hz), hg,
      Nat.div_div_self hz hn]

theorem nonempty_sup_zpowers_mulEquiv_dihedral {G : Type*} [Group G] (C : Subgroup G)
    (hC : IsCyclic C) (w : G) (hw : w ∉ C) (hw2 : w * w = 1)
    (hinv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) :
    Nonempty ((C ⊔ Subgroup.zpowers w : Subgroup G) ≃* DihedralGroup (Nat.card C)) := by
  classical
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C := zmodCyclicMulEquiv hC
  let rot : ZMod (Nat.card C) → G := fun i => (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C := (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) : rot (i + j) = rot i * rot j :=
    congrArg Subtype.val (e.map_mul (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) : rot (-i) = (rot i)⁻¹ :=
    congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := congrArg Subtype.val e.map_one
  have hw_inv_eq : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  have hw_mul_rot (i : ZMod (Nat.card C)) : w * rot i = rot (-i) * w := by
    calc w * rot i = (w * rot i * w⁻¹) * w := by rw [hw_inv_eq, mul_assoc, hw2, mul_one]
      _ = (rot i)⁻¹ * w := by rw [hinv (rot i) (hrot_mem i)]
      _ = rot (-i) * w := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) : rot i * w = w * rot (-i) := by
    calc rot i * w = rot (-(-i)) * w := by rw [neg_neg]
      _ = w * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* G :=
    { toFun := fun x => match x with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => w * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change w * rot (j - i) = rot i * (w * rot j)
          calc w * rot (j - i) = w * rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = w * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (w * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * w) * rot j := by rw [hrot_mul_w]
            _ = rot i * (w * rot j) := by rw [mul_assoc]
        · change w * rot (i + j) = (w * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (w * rot i) * (w * rot j)
          calc rot (j - i) = rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (w * w) * (rot (-i) * rot j) := by rw [hw2, one_mul]
            _ = (w * (w * rot (-i))) * rot j := by simp only [mul_assoc]
            _ = (w * (rot i * w)) * rot j := by rw [hrot_mul_w]
            _ = (w * rot i) * (w * rot j) := by simp only [mul_assoc] }
  have hinj : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j :=
        e.injective (Subtype.ext hij)
      exact congrArg Multiplicative.toAdd heq
    · exfalso
      apply hw
      change rot i = w * rot j at hij
      have hwrj : w * rot j ∈ C := hij ▸ hrot_mem i
      exact (C.mul_mem_cancel_right (hrot_mem j)).mp hwrj
    · exfalso
      apply hw
      change w * rot i = rot j at hij
      have hwri : w * rot i ∈ C := hij ▸ hrot_mem j
      exact (C.mul_mem_cancel_right (hrot_mem i)).mp hwri
    · apply congrArg DihedralGroup.sr
      change w * rot i = w * rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j :=
        e.injective (Subtype.ext (mul_left_cancel hij))
      exact congrArg Multiplicative.toAdd heq
  have hrange : hom.range = C ⊔ Subgroup.zpowers w := by
    apply le_antisymm
    · rintro x ⟨(i | i), rfl⟩
      · exact Subgroup.mem_sup_left (hrot_mem i)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
          (Subgroup.mem_sup_left (hrot_mem i))
    · apply sup_le
      · intro c hc
        refine ⟨DihedralGroup.r (Multiplicative.toAdd (e.symm ⟨c, hc⟩)), ?_⟩
        change rot (Multiplicative.toAdd (e.symm ⟨c, hc⟩)) = c
        change ((e (Multiplicative.ofAdd (Multiplicative.toAdd (e.symm ⟨c, hc⟩))) : C) : G) = c
        rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      · rw [Subgroup.zpowers_le]
        refine ⟨DihedralGroup.sr 0, ?_⟩
        change w * rot 0 = w
        rw [hrot_zero, mul_one]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

@[expose] noncomputable def psl2Map {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L) :
    PSL2MatrixGroup K →* PSL2MatrixGroup L :=
  QuotientGroup.map _ _ (Matrix.SpecialLinearGroup.map φ) (by
    intro A hA
    rw [Subgroup.mem_comap, Matrix.SpecialLinearGroup.mem_center_iff]
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    refine ⟨φ r, by rw [← map_pow, hr, map_one], ?_⟩
    ext i j
    have h := congrFun (congrFun hrA i) j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, ← h]
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp)

theorem psl2Map_mk {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    psl2Map φ (QuotientGroup.mk' _ A) =
      QuotientGroup.mk' _ (Matrix.SpecialLinearGroup.map φ A) :=
  rfl

theorem psl2Map_injective {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L) :
    Function.Injective (psl2Map φ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) x
  rw [MonoidHom.mem_ker, psl2Map_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at hx
  obtain ⟨r, hr, hrA⟩ := hx
  have hent : ∀ i j : Fin 2,
      φ ((A : Matrix (Fin 2) (Fin 2) K) i j) = if i = j then r else 0 := by
    intro i j
    have h := congrFun (congrFun hrA i) j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h
    rw [← h]
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  have h01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 :=
    (map_eq_zero_iff φ φ.injective).mp (by simpa using hent 0 1)
  have h10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    (map_eq_zero_iff φ φ.injective).mp (by simpa using hent 1 0)
  have h11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    φ.injective (by rw [hent 1 1, hent 0 0]; simp)
  have hsq : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 = 1 := by
    apply φ.injective
    rw [map_pow, map_one, hent 0 0]
    simpa using hr
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 0, by simpa using hsq, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h11]

theorem nonempty_galoisField_ringHom {F : Type u} [Field F] [Finite F] {p f : ℕ}
    [hp : Fact p.Prime] (hF : Nat.card F = p ^ f) {m : ℕ} (hm : m ∣ f) :
    Nonempty (GaloisField p m →+* F) := by
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  let : Algebra (ZMod p) F := ZMod.algebra F p
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hf0 (zero_dvd_iff.mp hm)
  have : Module.Finite (ZMod p) F := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod p) F = f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := F)
    rw [hF, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p)
    (K := GaloisField p m) (L := F) (by rw [GaloisField.finrank p hm0, hfin]; exact hm)
  exact ⟨φ.toRingHom⟩

universe w

variable {F : Type w} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem psl2_mul_comm_of_mem_sylow (hF : Nat.card F = p ^ f) (P : Sylow p (PSL2MatrixGroup F))
    {x y : PSL2MatrixGroup F} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  have h := congrArg e (mul_comm (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩))
  rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h
  exact congrArg Subtype.val h

theorem exists_elementaryAbelian_subgroup (hF : Nat.card F = p ^ f) {m : ℕ} (hm : m ≤ f) :
    ∃ H : Subgroup (PSL2MatrixGroup F), Nat.card H = p ^ m ∧ IsElementaryAbelian p H := by
  let P : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  have hPcard : Nat.card (P : Subgroup (PSL2MatrixGroup F)) = p ^ f := by
    rw [← Nat.card_congr e.toEquiv]
    exact hF
  have hdvd : p ^ m ∣ Nat.card (P : Subgroup (PSL2MatrixGroup F)) :=
    hPcard ▸ pow_dvd_pow p hm
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨K.map (P : Subgroup (PSL2MatrixGroup F)).subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
  · have hmem : ∀ x ∈ K.map (P : Subgroup (PSL2MatrixGroup F)).subtype, x ∈ P := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    exact
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
          (psl2_mul_comm_of_mem_sylow hF P (hmem _ a.2) (hmem _ b.2))⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
          rw [Subgroup.coe_pow, psl2_pow_eq_one_of_mem_sylow hF P (hmem _ g.2),
            Subgroup.coe_one]) }

theorem exists_cyclic_subgroup (hF : Nat.card F = p ^ f) {z : ℕ}
    (hz : z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) :
    ∃ H : Subgroup (PSL2MatrixGroup F), Nat.card H = z ∧ IsCyclic H := by
  obtain ⟨U, S, hUc, hU, hSc, hS, -⟩ :=
    BenderSuzuki.External.huppert_II_8_5_a_psl2_cover hF (default : Sylow p _)
  rw [← card_add_one_div_eq hF, ← card_sub_one_div_eq hF, ← hU, ← hS] at hz
  rcases hz with hz | hz
  · obtain ⟨H, -, hH, hHc⟩ := exists_cyclic_subgroup_card S hz
    exact ⟨H, hH, hHc⟩
  · obtain ⟨H, -, hH, hHc⟩ := exists_cyclic_subgroup_card U hz
    exact ⟨H, hH, hHc⟩

theorem exists_dihedral_subgroup (hF : Nat.card F = p ^ f) {z : ℕ}
    (hz : z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) :
    ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* DihedralGroup z) := by
  rcases hz with hz | hz
  · obtain ⟨S, w, hSc, hS, -, hwS, hw2, hinv, -, -⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
    rw [← card_add_one_div_eq hF, ← hS] at hz
    obtain ⟨R, hRS, hR, hRc⟩ := exists_cyclic_subgroup_card S hz
    subst hR
    obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral R hRc w (fun h => hwS (hRS h)) hw2
      (fun c hc => hinv c (hRS hc))
    exact ⟨_, ⟨e⟩⟩
  · obtain ⟨U, w, hUc, hU, -, hwU, hw2, hinv, -, -⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
    rw [← card_sub_one_div_eq hF, ← hU] at hz
    obtain ⟨R, hRU, hR, hRc⟩ := exists_cyclic_subgroup_card U hz
    subst hR
    obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral R hRc w (fun h => hwU (hRU h)) hw2
      (fun c hc => hinv c (hRU hc))
    exact ⟨_, ⟨e⟩⟩

theorem exists_psl2_subfield_subgroup (hF : Nat.card F = p ^ f) {m : ℕ} (hm : m ∣ f) :
    ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m)) := by
  obtain ⟨φ⟩ := nonempty_galoisField_ringHom hF hm
  exact ⟨(psl2Map φ).range, ⟨(MonoidHom.ofInjective (psl2Map_injective φ)).symm⟩⟩

theorem isSquare_of_galoisField_ringHom (hF : Nat.card F = p ^ f) {m : ℕ} (hm : 2 * m ∣ f)
    (φ : GaloisField p m →+* F) (x : GaloisField p m) : IsSquare (φ x) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField p m) := Fintype.ofFinite _
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hf0 (zero_dvd_iff.mp (by simpa using hm))
  by_cases hx : x = 0
  · rw [hx, map_zero]
    exact ⟨0, by rw [mul_zero]⟩
  have hφx : φ x ≠ 0 := (map_ne_zero φ).mpr hx
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  by_cases h2 : ringChar F = 2
  · exact FiniteField.isSquare_of_char_two h2 _
  have hp2 : p ≠ 2 := by
    intro hp2
    exact h2 (by rw [ringChar.eq F p, hp2])
  rw [FiniteField.isSquare_iff h2 hφx]
  have hKcard : Fintype.card (GaloisField p m) = p ^ m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p m hm0]
  have hx1 : x ^ (p ^ m - 1) = 1 := by
    rw [← hKcard]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  have hFcard : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨s, hs⟩ := hm
  have hodd : Odd (p ^ m) := (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨r, hr⟩ := hodd
  have hdvd : p ^ m - 1 ∣ Fintype.card F / 2 := by
    have h1 : p ^ (2 * m) - 1 ∣ p ^ f - 1 := by
      rw [hs, pow_mul p (2 * m) s]
      simpa using Nat.sub_dvd_pow_sub_pow (p ^ (2 * m)) 1 s
    have h2' : 2 * (p ^ m - 1) ∣ p ^ (2 * m) - 1 := by
      refine ⟨r + 1, ?_⟩
      rw [show p ^ (2 * m) = p ^ m * p ^ m by ring, hr]
      have : (2 * r + 1) * (2 * r + 1) - 1 = 2 * r * (2 * r + 2) := by
        rw [show (2 * r + 1) * (2 * r + 1) = 2 * r * (2 * r + 2) + 1 by ring]
        simp
      rw [this, show 2 * r + 1 - 1 = 2 * r by omega]
      ring
    have h3 : Fintype.card F / 2 = (p ^ f - 1) / 2 := by
      rw [hFcard]
      have : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
      obtain ⟨t, ht⟩ := this
      omega
    rw [h3]
    exact Nat.dvd_div_of_mul_dvd (h2'.trans h1)
  obtain ⟨d, hd⟩ := hdvd
  rw [hd, pow_mul, ← map_pow, hx1, map_one, one_pow]

theorem exists_pgl2_subfield_subgroup
    (hF : Nat.card F = p ^ f) {m : ℕ} (hm : 2 * m ∣ f) :
    ∃ H : Subgroup (PSL2MatrixGroup F),
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
  obtain ⟨φ⟩ := nonempty_galoisField_ringHom hF (dvd_of_mul_left_dvd hm)
  let Ψ := h826_pglMap φ
  have hΨ : Function.Injective Ψ := h826_pglMap_injective φ φ.injective
  let ι := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  have hι : Function.Injective ι := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hle : Ψ.range ≤ ι.range := by
    rintro x ⟨y, rfl⟩
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
    change h826_pglMap φ (Matrix.ProjGenLinGroup.mk A) ∈ ι.range
    rw [h826_pglMap_mk]
    obtain ⟨c, hc⟩ := isSquare_of_galoisField_ringHom hF hm φ
      ((A : Matrix (Fin 2) (Fin 2) (GaloisField p m)).det)
    have hdet : ((Matrix.GeneralLinearGroup.map φ A : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).det = c * c := by
      rw [← hc, RingHom.map_det]
      rfl
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 := (Matrix.GeneralLinearGroup.map φ A).isUnit.map Matrix.detMonoidHom
      rw [Matrix.coe_detMonoidHom, hdet, h0, mul_zero] at h1
      exact not_isUnit_zero h1
    let B : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨c⁻¹ • ((Matrix.GeneralLinearGroup.map φ A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
        rw [Matrix.det_smul, hdet, Fintype.card_fin]
        field_simp⟩
    refine ⟨QuotientGroup.mk B, ?_⟩
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 c hc0, ?_⟩
    ext i j
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, Matrix.mul_diagonal]
    change (c⁻¹ * _) * c = _
    field_simp
  let H : Subgroup (PSL2MatrixGroup F) := Ψ.range.comap ι
  refine ⟨H, ⟨((Subgroup.equivMapOfInjective H ι hι).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hle))).trans
    (MonoidHom.ofInjective hΨ).symm⟩⟩

end CFSG.Glauberman.Dickson
