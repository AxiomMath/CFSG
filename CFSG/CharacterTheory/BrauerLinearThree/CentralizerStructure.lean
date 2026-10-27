module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerStructureMatrix
public import CFSG.LinearAlgebra.DesarguesianPlanes.RootSubgroups

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type*} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

omit [Finite F] in
theorem linearCentralizerHom_mem (A : GL (Fin 2) F) :
    linearCentralizerHom φ A ∈ Subgroup.centralizer ({J} : Set G) :=
  (φ.symm (QuotientGroup.mk A)).2

include φ in
theorem card_centralizer_J :
    Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card Z =
      Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr φ.toEquiv, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
    Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card (α := F)]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h1 : 1 ≤ Fintype.card F ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : Fintype.card F ≤ Fintype.card F ^ 2 := by nlinarith
  zify [h1, h2, hq]
  ring

omit [Finite F] in
theorem card_statedScalars :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) = Nat.card F - 1 := by
  have hinj :
      Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
    intro a b h
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
    exact Units.ext (by simpa using this)
  rw [CFSG.Assembly.LowTwoRank.StatedScalars, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_units]

omit [Finite F] [Z.Normal] in
@[expose] noncomputable def diagHom : Fˣ × Fˣ →* GL (Fin 2) F where
  toFun x := diagGL x.1 x.2
  map_one' := diagGL_one_one
  map_mul' _ _ := (diagGL_mul _ _ _ _).symm

omit [Finite F] [Z.Normal] in
theorem diagHom_apply (x : Fˣ × Fˣ) : diagHom x = (diagGL x.1 x.2 : GL (Fin 2) F) := rfl

omit [Finite F] [Z.Normal] in
theorem diagHom_injective : Function.Injective (diagHom : Fˣ × Fˣ →* GL (Fin 2) F) := by
  intro x y h
  have h0 : ((diagHom x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      ((diagHom y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 := by rw [h]
  have h1 : ((diagHom x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      ((diagHom y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 := by rw [h]
  simp [diagHom_apply, diagGL] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

omit [Finite F] in
@[expose] noncomputable def centralizerHom : GL (Fin 2) F →* Subgroup.centralizer ({J} : Set G) :=
  φ.symm.toMonoidHom.comp (QuotientGroup.mk' Z)

omit [Finite F] in
theorem coe_centralizerHom (A : GL (Fin 2) F) :
    ((centralizerHom φ A : Subgroup.centralizer ({J} : Set G)) : G) = linearCentralizerHom φ A :=
  rfl

omit [Finite F] in
@[expose] noncomputable def torusC : Subgroup (Subgroup.centralizer ({J} : Set G)) :=
  ((centralizerHom φ).comp diagHom).range

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
include hZ

omit [Finite F] [Z.Normal] in
theorem card_Z_dvd : Nat.card Z ∣ Nat.card F - 1 := by
  rw [← card_statedScalars]
  exact Subgroup.card_dvd_of_le hZ

omit [Z.Normal] in
theorem coprime_ringChar_card_Z : Nat.Coprime (ringChar F) (Nat.card Z) := by
  have : Fintype F := Fintype.ofFinite F
  have hprime : (ringChar F).Prime := CharP.char_is_prime F _
  apply Nat.Coprime.coprime_dvd_right (card_Z_dvd hZ)
  rw [Nat.Prime.coprime_iff_not_dvd hprime]
  intro hdvd
  have hcard : ringChar F ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact ringChar.dvd (FiniteField.cast_card_eq_zero F)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have : ringChar F ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hcard hdvd
  rw [Nat.sub_sub_self hpos] at this
  exact hprime.one_lt.ne' (Nat.dvd_one.mp this)

omit [Finite F] [Z.Normal] hZ in
theorem commute_of_mem_scalars {w : GL (Fin 2) F}
    (hw : w ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (A : GL (Fin 2) F) :
    Commute w A := by
  have hc : w ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hw
  exact ((Subgroup.mem_center_iff.mp hc) A).symm

omit [Finite F] in
theorem exists_lift_pow_eq_one {g : G} (hg : J * g = g * J) {m : ℕ}
    (hm : Nat.Coprime (Nat.card Z) m) (hgm : g ^ m = 1) :
    ∃ A : GL (Fin 2) F, linearCentralizerHom φ A = g ∧ A ^ m = 1 := by
  obtain ⟨A, rfl⟩ := exists_linearCentralizerHom_eq φ hg
  have hAm : A ^ m ∈ Z := by
    rw [← linearCentralizerHom_eq_one_iff φ, map_pow, hgm]
  set z : Z := ⟨A ^ m, hAm⟩
  set w : Z := (powCoprime hm).symm z with hw
  have hwm : w ^ m = z := by
    have := (powCoprime hm).apply_symm_apply z
    rwa [powCoprime_apply] at this
  have hcomm : Commute A ((w : GL (Fin 2) F)⁻¹) :=
    (commute_of_mem_scalars (hZ (Z.inv_mem w.2)) A).symm
  refine ⟨A * (w : GL (Fin 2) F)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, (linearCentralizerHom_eq_one_iff φ _).mpr w.2, inv_one, mul_one]
  · rw [hcomm.mul_pow, inv_pow, ← Subgroup.coe_pow, hwm]
    exact mul_inv_cancel _

variable (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0)
include hZodd h2

omit [Finite F] in
theorem mem_center_iff_scalar {g : G} (hg : J * g = g * J) :
    (∀ h : G, J * h = h * J → g * h = h * g) ↔
      ∃ a : Fˣ, g = linearCentralizerHom φ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  constructor
  · intro hc
    obtain ⟨A, rfl⟩ := exists_linearCentralizerHom_eq φ hg
    have hA : A ∈ Subgroup.center (GL (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro B
      exact (commute_of_linearCentralizerHom_commute φ hZ hZodd h2
        (hc _ (linearCentralizerHom_commute φ B))).symm
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
    obtain ⟨a, rfl⟩ := hA
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩ h hh
    obtain ⟨B, rfl⟩ := exists_linearCentralizerHom_eq φ hh
    rw [← map_mul, ← map_mul, (commute_of_mem_scalars ⟨a, rfl⟩ B).eq]

omit [Finite F] hZodd h2 in
theorem card_scalarImage :
    Nat.card ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F).map (linearCentralizerHom φ)) *
      Nat.card Z = Nat.card F - 1 := by
  set S := CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F
  set ψ := (linearCentralizerHom φ).comp S.subtype
  have hrange : ψ.range = S.map (linearCentralizerHom φ) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card Z := by
    have hk : ψ.ker = Z.subgroupOf S := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
        Subgroup.coe_subtype, linearCentralizerHom_eq_one_iff]
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv
  rw [← hrange, ← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup, card_statedScalars]

omit [Finite F] in
theorem centralizer_rootUp {c : F} (hc : c ≠ 0) {g : G} (hg : J * g = g * J)
    (hgc : g * rootUp φ c = rootUp φ c * g) :
    ∃ (a : Fˣ) (b : F),
      g = linearCentralizerHom φ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) * rootUp φ b := by
  obtain ⟨A, rfl⟩ := exists_linearCentralizerHom_eq φ hg
  have hA := commute_of_linearCentralizerHom_commute φ hZ hZodd h2 hgc
  obtain ⟨a, b, rfl⟩ := eq_scalar_mul_upperGL_of_commute hc A hA
  exact ⟨a, b, map_mul _ _ _⟩

omit hZodd h2 in
theorem exists_unipotent_lift {g : G} (hg : J * g = g * J) (hgp : g ^ ringChar F = 1) :
    ∃ A : GL (Fin 2) F, linearCentralizerHom φ A = g ∧ A ^ ringChar F = 1 ∧
      ((A : Matrix (Fin 2) (Fin 2) F) - 1) * ((A : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
  obtain ⟨A, hA, hAp⟩ := exists_lift_pow_eq_one φ hZ hg (coprime_ringChar_card_Z hZ).symm hgp
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  exact ⟨A, hA, hAp, sub_one_mul_self_eq_zero (ringChar F) A hAp⟩

omit hZodd in
theorem exists_conj_mem_rootX₁ {g : G} (hg : J * g = g * J) (hgp : g ^ ringChar F = 1) :
    ∃ h : G, J * h = h * J ∧ h * g * h⁻¹ ∈ rootX₁ φ := by
  obtain ⟨A, rfl, -, hA⟩ := exists_unipotent_lift φ hZ hg hgp
  obtain ⟨P, c, hP⟩ := exists_conj_upperGL h2 A hA
  refine ⟨linearCentralizerHom φ P⁻¹, linearCentralizerHom_commute φ _, ?_⟩
  rw [mem_rootX₁]
  refine ⟨c, ?_⟩
  rw [rootUp, ← hP, map_mul, map_mul, map_inv, inv_inv]

omit hZodd in
theorem inverted_mem_rootX {g : G} (hg : J * g = g * J) (hgp : g ^ ringChar F = 1)
    (hinv : invJ₁ φ * g * (invJ₁ φ)⁻¹ = g⁻¹) : g ∈ rootX₁ φ ∨ g ∈ rootX₂ φ := by
  obtain ⟨A, rfl, hAp, hA⟩ := exists_unipotent_lift φ hZ hg hgp
  set D : GL (Fin 2) F := diagGL 1 (-1)
  set μ : GL (Fin 2) F := D * A * D⁻¹ * A with hμ
  have hμZ : μ ∈ Z := by
    rw [← linearCentralizerHom_eq_one_iff φ, hμ, map_mul, map_mul, map_mul, map_inv]
    change invJ₁ φ * linearCentralizerHom φ A * (invJ₁ φ)⁻¹ * linearCentralizerHom φ A = 1
    rw [hinv, inv_mul_cancel]
  have hcomm : ∀ B : GL (Fin 2) F, Commute μ B := commute_of_mem_scalars (hZ hμZ)
  have hDA : D * A * D⁻¹ = μ * A⁻¹ := by rw [hμ, mul_inv_cancel_right]
  have hμp : μ ^ ringChar F = 1 := by
    have h1 : (D * A * D⁻¹) ^ ringChar F = 1 := by
      rw [show D * A * D⁻¹ = MulAut.conj D A from rfl, ← map_pow, hAp, map_one]
    rw [hDA, (hcomm A⁻¹).mul_pow, inv_pow, hAp, inv_one, mul_one] at h1
    exact h1
  have hμ1 : μ = 1 := by
    have hord : orderOf (⟨μ, hμZ⟩ : Z) ∣ Nat.gcd (ringChar F) (Nat.card Z) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hμp)))
        (orderOf_dvd_natCard _)
    rw [(coprime_ringChar_card_Z hZ).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact congrArg Subtype.val hord
  rw [hμ1, one_mul] at hDA
  rcases upper_or_lower_of_diag_conj_eq_inv h2 A hA hDA with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact Or.inl ((mem_rootX₁ φ).mpr ⟨c, rfl⟩)
  · exact Or.inr ((mem_rootX₂ φ).mpr ⟨c, rfl⟩)

omit hZodd in
theorem rootX₁_le_of_unipotent (H : Subgroup G) (hW : swapW φ ∈ H)
    (hT : ∀ t : G, IsTorus φ t → t ∈ H) {g : G} (hgH : g ∈ H) (hg : J * g = g * J)
    (hg1 : g ≠ 1) (hgp : g ^ ringChar F = 1) : rootX₁ φ ≤ H := by
  obtain ⟨A, rfl, -, hA⟩ := exists_unipotent_lift φ hZ hg hgp
  obtain ⟨k, ⟨c, hk⟩, hform⟩ := exists_conj_upperGL_mem h2 A hA
  have hdiag : ∀ l : Fˣ, linearCentralizerHom φ (diagGL l 1) ∈ H := fun l =>
    hT _ (isTorus_diag φ l 1)
  have hkH : linearCentralizerHom φ k ∈ H := by
    rcases hform with rfl | rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [map_one]; exact H.one_mem
    · exact hW
    · rw [map_mul]; exact H.mul_mem (hdiag l) hgH
    · rw [map_mul, map_mul]; exact H.mul_mem (H.mul_mem (hdiag l) hgH) hW
  have hcH : rootUp φ c ∈ H := by
    rw [rootUp, ← hk, map_mul, map_mul, map_inv]
    exact H.mul_mem (H.mul_mem (H.inv_mem hkH) hgH) hkH
  have hc1 : rootUp φ c ≠ 1 := by
    intro h
    apply hg1
    rw [rootUp, ← hk, map_mul, map_mul, map_inv] at h
    have h' := congrArg (fun x => linearCentralizerHom φ k * x * (linearCentralizerHom φ k)⁻¹) h
    simpa [mul_assoc] using h'
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; exact H.one_mem
  obtain ⟨t, ht, htx⟩ := torusTransitive_rootX₁ φ _ ((mem_rootX₁ φ).mpr ⟨c, rfl⟩) x hx hc1 hx1
  rw [← htx, conjHom_apply]
  exact H.mul_mem (H.mul_mem (hT t ht) hcH) (H.inv_mem (hT t ht))

omit [Finite F] in
theorem exists_conj_invJ₁ (hJ : orderOf J = 2) {x : G} (hx : J * x = x * J) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hxJ : x ≠ J) : ∃ h : G, J * h = h * J ∧ h * invJ₁ φ * h⁻¹ = x := by
  have hcop : Nat.Coprime (Nat.card Z) 2 := Nat.coprime_two_right.mpr hZodd
  obtain ⟨A, rfl, hA2⟩ := exists_lift_pow_eq_one φ hZ hx hcop (by rw [sq]; exact hx2)
  have hneg := linearCentralizerHom_neg_one φ hZ hZodd h2 hJ
  have hA1 : A ≠ 1 := by rintro rfl; exact hx1 (map_one _)
  have hAm1 : A ≠ -1 := by rintro rfl; exact hxJ hneg
  obtain ⟨P, hP⟩ := exists_conj_diagGL_of_mul_self h2 A (by rw [← sq]; exact hA2) hA1 hAm1
  refine ⟨linearCentralizerHom φ P, linearCentralizerHom_commute φ P, ?_⟩
  rw [invJ₁, ← hP, map_mul, map_mul, map_inv]
  group

omit [Finite F] hZodd h2 in
theorem card_torusC : Nat.card (torusC φ) * Nat.card Z = (Nat.card F - 1) ^ 2 := by
  set ψ := (centralizerHom φ).comp (diagHom : Fˣ × Fˣ →* GL (Fin 2) F)
  have hker : Nat.card ψ.ker = Nat.card Z := by
    have hmap : ψ.ker.map diagHom = Z := by
      ext A
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : centralizerHom φ (diagHom x) = 1 := hx
        have : linearCentralizerHom φ (diagHom x) = 1 := by
          rw [← coe_centralizerHom, hx']; rfl
        exact (linearCentralizerHom_eq_one_iff φ _).mp this
      · intro hA
        obtain ⟨c, rfl⟩ := hZ hA
        refine ⟨(c, c), ?_, ?_⟩
        · change centralizerHom φ (diagHom (c, c)) = 1
          apply Subtype.ext
          rw [coe_centralizerHom, OneMemClass.coe_one, linearCentralizerHom_eq_one_iff]
          convert hA using 1
          ext i j
          fin_cases i <;> fin_cases j <;> simp [diagHom_apply, diagGL]
        · ext i j
          fin_cases i <;> fin_cases j <;> simp [diagHom_apply, diagGL]
    rw [← hmap]
    exact (Subgroup.card_map_of_injective diagHom_injective).symm
  rw [torusC, ← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_prod, Nat.card_units, sq]

omit [Z.Normal] hZ hZodd in
theorem odd_card_F : Odd (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  have hc : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this
    exact_mod_cast this
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact FiniteField.odd_card_of_char_ne_two hc

include φ in
theorem sylow_center_involution (hJ : orderOf J = 2)
    (S : Sylow 2 (Subgroup.centralizer ({J} : Set G))) :
    (⟨J, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({J} : Set G)) ∈ S ∧
      ∀ x : S, x ∈ Subgroup.center S → x * x = 1 →
        x = 1 ∨ (((x : Subgroup.centralizer ({J} : Set G)) : G) = J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  set J' : Subgroup.centralizer ({J} : Set G) := ⟨J, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hJ'c : J' ∈ Subgroup.center (Subgroup.centralizer ({J} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  constructor
  ·
    have hle : Subgroup.zpowers J' ≤ Subgroup.center (Subgroup.centralizer ({J} : Set G)) :=
      Subgroup.zpowers_le.mpr hJ'c
    have hnormal : (Subgroup.zpowers J').Normal := by
      constructor
      intro n hn g
      rw [(Subgroup.mem_center_iff.mp (hle hn) g), mul_inv_cancel_right]
      exact hn
    have hp : IsPGroup 2 (Subgroup.zpowers J') := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, pow_one, ← hJ]
      exact Subgroup.orderOf_mk J _
    exact hp.le_sylow_of_normal S (Subgroup.mem_zpowers J')
  · intro x hx hxx
    by_contra hcon
    push Not at hcon
    obtain ⟨hx1, hxJ⟩ := hcon
    set x' : G := ((x : Subgroup.centralizer ({J} : Set G)) : G)
    have hx'J : J * x' = x' * J :=
      (Subgroup.mem_centralizer_singleton_iff.mp (x : Subgroup.centralizer ({J} : Set G)).2).symm
    have hx'2 : x' * x' = 1 := by
      have := congrArg (fun y : S => ((y : Subgroup.centralizer ({J} : Set G)) : G)) hxx
      simpa using this
    have hx'1 : x' ≠ 1 := by
      intro h
      apply hx1
      apply Subtype.ext; apply Subtype.ext
      exact h
    obtain ⟨h, hhJ, hhx⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ hx'J hx'2 hx'1 hxJ
    set h' : Subgroup.centralizer ({J} : Set G) :=
      ⟨h, Subgroup.mem_centralizer_singleton_iff.mpr hhJ.symm⟩
    have hle : (S : Subgroup (Subgroup.centralizer ({J} : Set G))).map
        (MulAut.conj h'⁻¹).toMonoidHom ≤ torusC φ := by
      rintro _ ⟨y, hy, rfl⟩
      have hyx : (y : G) * x' = x' * y := by
        have := (Subgroup.mem_center_iff.mp hx) ⟨y, hy⟩
        exact congrArg (fun z : S => ((z : Subgroup.centralizer ({J} : Set G)) : G)) this
      have hJ₁ : invJ₁ φ = h⁻¹ * x' * h := by rw [← hhx]; group
      have htor : IsTorus φ (h⁻¹ * (y : G) * h) := by
        refine ⟨?_, ?_⟩
        · have hyJ : Commute J (y : G) :=
            (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
          have hhJ' : Commute J h := hhJ
          exact ((hhJ'.inv_right.mul_right hyJ).mul_right hhJ').eq
        · rw [hJ₁]
          calc h⁻¹ * x' * h * (h⁻¹ * ↑y * h) = h⁻¹ * (x' * ↑y) * h := by group
            _ = h⁻¹ * (↑y * x') * h := by rw [hyx]
            _ = h⁻¹ * ↑y * h * (h⁻¹ * x' * h) := by group
      obtain ⟨a, b, hab⟩ := (isTorus_iff φ hZ hZodd h2 _).mp htor
      refine ⟨(a, b), Subtype.ext ?_⟩
      rw [MonoidHom.comp_apply, coe_centralizerHom, diagHom_apply, ← hab,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rfl
    have hdvd : Nat.card S ∣ Nat.card (torusC φ) := by
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective (MulAut.conj h'⁻¹).injective] at h1
    have hidx := Sylow.not_dvd_index S
    obtain ⟨k, hk⟩ := hdvd
    have hC := card_centralizer_J φ
    have hT := card_torusC φ hZ
    rw [← Subgroup.card_mul_index (S : Subgroup (Subgroup.centralizer ({J} : Set G)))] at hC
    have hq := odd_card_F h2
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have hSpos : 0 < Nat.card S := Nat.card_pos
    have hkey : (S : Subgroup (Subgroup.centralizer ({J} : Set G))).index =
        Nat.card F * (Nat.card F + 1) * k := by
      rw [hk] at hT
      have h3 : Nat.card S * (S : Subgroup (Subgroup.centralizer ({J} : Set G))).index *
          Nat.card Z = Nat.card S * (Nat.card F * (Nat.card F + 1) * k) * Nat.card Z := by
        rw [hC, ← hT]; ring
      have h4 := Nat.eq_of_mul_eq_mul_right hZpos h3
      exact Nat.eq_of_mul_eq_mul_left hSpos h4
    apply hidx
    rw [hkey]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (even_iff_two_dvd.mp hq.add_one) _) _

end CFSG.BrauerLinearThree
