module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchDValueDataProjective
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.UnitaryBranch
  CFSG.Semidihedral.Principal

section Projective

variable {K : Type} [Field K]

theorem eq_multiplier_of_fixes_infty_zero {g : Equiv.Perm (Omega K)} (hg : g ∈ coordinateD K)
    (hinf : g none = none) (h0 : g (some 0) = some 0) : ∃ μ : Kˣ, g = multiplier K μ := by
  rcases eq_multiplier_or_of_preserves K hg (Or.inl ⟨hinf, h0⟩) with h | ⟨μ, hμ⟩
  · exact h
  · exfalso
    rw [hμ, Equiv.Perm.mul_apply, inversion_none, multiplier_some, mul_zero] at hinf
    exact Option.some_ne_none _ hinf

theorem two_point_stabilizer_eq_map {x y : Omega K} {g : Equiv.Perm (Omega K)}
    (hg : g ∈ coordinateG K) (hgx : g none = x) (hgy : g (some 0) = y) :
    (coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x ⊓
        MulAction.stabilizer (Equiv.Perm (Omega K)) y : Subgroup (Equiv.Perm (Omega K))) =
      (multiplierHom K).range.map (MulAut.conj g).toMonoidHom := by
  have hgD : g ∈ coordinateD K := coordinateG_le_D K hg
  ext h
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
    Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨⟨hhD, hhx⟩, hhy⟩
    have hD' : g⁻¹ * h * g ∈ coordinateD K :=
      (coordinateD K).mul_mem ((coordinateD K).mul_mem ((coordinateD K).inv_mem hgD) hhD) hgD
    have h1 : (g⁻¹ * h * g) none = none := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgx, hhx, ← hgx, ← Equiv.Perm.mul_apply,
        inv_mul_cancel, Equiv.Perm.one_apply]
    have h2 : (g⁻¹ * h * g) (some 0) = some 0 := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgy, hhy, ← hgy, ← Equiv.Perm.mul_apply,
        inv_mul_cancel, Equiv.Perm.one_apply]
    obtain ⟨μ, hμ⟩ := eq_multiplier_of_fixes_infty_zero hD' h1 h2
    refine ⟨multiplier K μ, ⟨μ, rfl⟩, ?_⟩
    rw [← hμ]
    group
  · rintro ⟨m, ⟨μ, rfl⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (coordinateD K).mul_mem ((coordinateD K).mul_mem hgD
        (multiplier_mem_coordinateD K μ)) ((coordinateD K).inv_mem hgD)
    · rw [multiplierHom_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hgx,
        ← Equiv.Perm.mul_apply g⁻¹ g, inv_mul_cancel, Equiv.Perm.one_apply, multiplier_none]
    · rw [multiplierHom_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hgy,
        ← Equiv.Perm.mul_apply g⁻¹ g, inv_mul_cancel, Equiv.Perm.one_apply, multiplier_some,
        mul_zero]

theorem two_point_stabilizer [Finite K] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hK : Nat.card K = p ^ f) {x y : Omega K} (hxy : x ≠ y) :
    IsCyclic (coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x ⊓
        MulAction.stabilizer (Equiv.Perm (Omega K)) y : Subgroup (Equiv.Perm (Omega K))) ∧
      Nat.card (coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x ⊓
        MulAction.stabilizer (Equiv.Perm (Omega K)) y : Subgroup (Equiv.Perm (Omega K))) =
        p ^ f - 1 := by
  have _ := hp.pos; have _ := hpodd.pos
  obtain ⟨g, hg, hgx, hgy⟩ := exists_coordinateG_infinity_zero (F := K) hxy
  rw [two_point_stabilizer_eq_map hg hgx hgy]
  refine ⟨?_, ?_⟩
  · have : IsCyclic (multiplierHom K).range :=
      isCyclic_of_surjective (multiplierHom K).rangeRestrict
        (multiplierHom K).rangeRestrict_surjective
    exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap _)
      ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      ← Nat.card_congr (MonoidHom.ofInjective (multiplierHom_injective K)).toEquiv,
      Nat.card_units, hK]

theorem pow_eq_one_of_dvd_pow_sub_one {p f k : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : p ^ k ∣ p ^ f - 1) : p ^ k = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · exfalso
    have h1 : p ∣ p ^ f - 1 := (dvd_pow_self p hk.ne').trans h
    have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h3 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    have h4 : p ∣ 1 := (Nat.dvd_sub_iff_right h3 h2).mp h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

theorem one_le_of_card_eq_pow {p f : ℕ} (hK : Nat.card K = p ^ f) [Finite K] : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · exfalso
    rw [pow_zero] at hK
    have : Nontrivial K := inferInstance
    have := Finite.one_lt_card_iff_nontrivial.mpr this
    omega
  · exact hf

theorem existsUnique_fixed_of_isPGroup [Finite K] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hK : Nat.card K = p ^ f)
    {X : Subgroup (Equiv.Perm (Omega K))} (hXD : X ≤ coordinateD K) (hX : IsPGroup p X)
    (hX1 : X ≠ ⊥) : ∃! x : Omega K, ∀ g ∈ X, g x = x := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := one_le_of_card_eq_pow hK
  have hcard : Nat.card (Omega K) = p ^ f + 1 := by
    rw [Omega, Finite.card_option, hK]
  have hndvd : ¬ p ∣ Nat.card (Omega K) := by
    rw [hcard]
    intro h
    have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h))
  obtain ⟨x, hx⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card (Omega K) hndvd
  have hx' : ∀ g ∈ X, g x = x := fun g hg => hx ⟨g, hg⟩
  refine ⟨x, hx', fun y hy => ?_⟩
  by_contra hyx
  have hle : X ≤ (coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Omega K)) y : Subgroup (Equiv.Perm (Omega K))) :=
    fun g hg => ⟨⟨hXD hg, hx' g hg⟩, hy g hg⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [(two_point_stabilizer hp hpodd hK (Ne.symm hyx)).2] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk] at hdvd
  have h1 := pow_eq_one_of_dvd_pow_sub_one hp hf hdvd
  exact hX1 (Subgroup.eq_bot_of_card_eq X (hk.trans h1))

theorem fixed_of_mem_normalizer_of_isPGroup [Finite K] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hK : Nat.card K = p ^ f) {X : Subgroup (Equiv.Perm (Omega K))} (hXD : X ≤ coordinateD K)
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) {x : Omega K} (hx : ∀ g ∈ X, g x = x)
    {n : Equiv.Perm (Omega K)} (hn : n ∈ Subgroup.normalizer (X : Set (Equiv.Perm (Omega K)))) :
    n x = x := by
  obtain ⟨y, -, hy⟩ := existsUnique_fixed_of_isPGroup hp hpodd hK hXD hX hX1
  have h2 : ∀ g ∈ X, g (n x) = n x := by
    intro g hg
    have hg' : n⁻¹ * g * n ∈ X := (Subgroup.mem_normalizer_iff''.mp hn g).mp hg
    have h3 := hx _ hg'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq] at h3
    exact h3
  rw [hy (n x) h2, hy x hx]

theorem exists_affine_of_mem_coordinateD {g : Equiv.Perm (Omega K)} (hg : g ∈ coordinateD K)
    (hinf : g none = none) : ∃ (s : Kˣ) (b : K), ∀ x : K, g (some x) = some (s * x + b) := by
  obtain ⟨A, rfl⟩ := exists_coordinateGLAction_eq hg
  have hc : A.val 1 0 = 0 := by
    by_contra hc
    rw [coordinateGLAction_infinity K A hc] at hinf
    exact Option.some_ne_none _ hinf
  have hdet : A.val 0 0 * A.val 1 1 ≠ 0 := by
    have h := A.det_ne_zero
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
    exact h
  have ha : A.val 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd1 : A.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 (A.val 0 0 / A.val 1 1) (div_ne_zero ha hd1), A.val 0 1 / A.val 1 1,
    fun x => ?_⟩
  rw [coordinateGLAction_finite K A x (by rw [hc, zero_mul, zero_add]; exact hd1), hc, zero_mul,
    zero_add, Units.val_mk0]
  congr 1
  field_simp

theorem affine_pow {g : Equiv.Perm (Omega K)} {s : Kˣ} {b : K}
    (hg : ∀ x : K, g (some x) = some (s * x + b)) (n : ℕ) :
    ∃ c : K, ∀ x : K, (g ^ n) (some x) = some ((s ^ n : Kˣ) * x + c) := by
  induction n with
  | zero => exact ⟨0, fun x => by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨s * c + b, fun x => ?_⟩
    rw [pow_succ', Equiv.Perm.mul_apply, hc, hg]
    congr 1
    push_cast
    ring

theorem eq_translation_of_pow_eq_one [Finite K] {p f k : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) {g : Equiv.Perm (Omega K)} (hg : g ∈ coordinateD K)
    (hinf : g none = none) (hgk : g ^ p ^ k = 1) : ∃ b : K, g = translation K b := by
  obtain ⟨s, b, hsb⟩ := exists_affine_of_mem_coordinateD hg hinf
  obtain ⟨c, hc⟩ := affine_pow hsb (p ^ k)
  have h0 := hc 0
  have h1 := hc 1
  rw [hgk, Equiv.Perm.one_apply, mul_zero, zero_add, Option.some_inj] at h0
  rw [hgk, Equiv.Perm.one_apply, ← h0, add_zero, mul_one, Option.some_inj] at h1
  have hs1 : s ^ p ^ k = 1 := Units.ext h1.symm
  have hsq : s ^ (p ^ f - 1) = 1 := by
    rw [← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  have hord : orderOf s ∣ Nat.gcd (p ^ k) (p ^ f - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hs1) (orderOf_dvd_of_pow_eq_one hsq)
  have hf : 1 ≤ f := one_le_of_card_eq_pow hK
  have hgcd : Nat.gcd (p ^ k) (p ^ f - 1) = 1 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := pow_eq_one_of_dvd_pow_sub_one (k := 1) hp hf (by simpa using h)
    exact hp.one_lt.ne' (by simpa using this)
  rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
  refine ⟨b, Equiv.ext fun x => ?_⟩
  cases x with
  | none => rw [hinf, translation_none]
  | some x => rw [hsb, hord, Units.val_one, one_mul, translation_some, add_comm]

theorem translation_mul_comm (a b : K) :
    translation K a * translation K b = translation K b * translation K a := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => rfl
  | some x => simp only [Equiv.Perm.mul_apply, translation_some, add_assoc, add_comm a b]

theorem coordinateD_inf_centralizer_coordinateU :
    coordinateD K ⊓ Subgroup.centralizer (coordinateU K : Set (Equiv.Perm (Omega K))) =
      coordinateU K := by
  rw [CFSG.LinearGroups.coordinateU_eq_range]
  apply le_antisymm
  · rintro d ⟨hdD, hdC⟩
    have h1 : translation K 1 ∈ (CFSG.LinearGroups.translationHom K).range :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hdC) _ h1
    obtain ⟨c, rfl⟩ := eq_translation_of_commute K hdD one_ne_zero hcomm.symm
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro _ ⟨b, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨translation_mem_coordinateD K _,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨c, rfl⟩
    exact translation_mul_comm _ _

theorem map_conj_eq_coordinateU [Finite K] {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ f)
    {X : Subgroup (Equiv.Perm (Omega K))} (hXD : X ≤ coordinateD K) (hX : IsPGroup p X)
    (hXcard : Nat.card X = p ^ f) {x : Omega K} (hx : ∀ g ∈ X, g x = x)
    {h : Equiv.Perm (Omega K)} (hhD : h ∈ coordinateD K) (hhx : h none = x) :
    X.map (MulAut.conj h⁻¹).toMonoidHom = coordinateU K := by
  have hmemX' : ∀ y, y ∈ X.map (MulAut.conj h⁻¹).toMonoidHom ↔ h * y * h⁻¹ ∈ X := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [mul_assoc] using hz
    · intro h1
      refine ⟨h * y * h⁻¹, h1, ?_⟩
      simp [mul_assoc]
  have hle : X.map (MulAut.conj h⁻¹).toMonoidHom ≤ coordinateU K := by
    intro y hy
    have hyX := (hmemX' y).mp hy
    have hyD : y ∈ coordinateD K := by
      have := (coordinateD K).mul_mem ((coordinateD K).mul_mem ((coordinateD K).inv_mem hhD)
        (hXD hyX)) hhD
      simpa [mul_assoc] using this
    have hyinf : y none = none := by
      have h1 := hx _ hyX
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.mpr hhx.symm,
        ← hhx] at h1
      exact h.injective h1
    obtain ⟨k, hk⟩ := hX ⟨_, hyX⟩
    have hk' : y ^ p ^ k = 1 := by
      have h1 := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      rw [conj_pow] at h1
      have := congrArg (fun z => h⁻¹ * z * h) h1
      simpa [mul_assoc] using this
    obtain ⟨b, rfl⟩ := eq_translation_of_pow_eq_one hp hK hyD hyinf hk'
    rw [CFSG.LinearGroups.coordinateU_eq_range]
    exact ⟨Multiplicative.ofAdd b, rfl⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [CFSG.LinearGroups.card_coordinateU, hK,
    Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hXcard]

theorem coordinateD_inf_centralizer_eq_of_isPGroup [Finite K] {p f : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hK : Nat.card K = p ^ f) {X : Subgroup (Equiv.Perm (Omega K))}
    (hXD : X ≤ coordinateD K) (hX : IsPGroup p X) (hXcard : Nat.card X = p ^ f) :
    coordinateD K ⊓ Subgroup.centralizer (X : Set (Equiv.Perm (Omega K))) = X := by
  have hf : 1 ≤ f := one_le_of_card_eq_pow hK
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXcard
    have := Nat.one_lt_pow (by omega : f ≠ 0) hp.one_lt
    omega
  obtain ⟨x, hx, -⟩ := existsUnique_fixed_of_isPGroup hp hpodd hK hXD hX hX1
  obtain ⟨⟨g, hgG⟩, hgx⟩ := coordinateG_orbit_infinity K x
  have hgD : g ∈ coordinateD K := coordinateG_le_D K hgG
  have hX'eq := map_conj_eq_coordinateU hp hK hXD hX hXcard hx hgD hgx
  have hmemX' : ∀ y, y ∈ X.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ X := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [mul_assoc] using hz
    · intro h1
      refine ⟨g * y * g⁻¹, h1, ?_⟩
      simp [mul_assoc]
  have hconj : ∀ y z : Equiv.Perm (Omega K), z * y = y * z →
      (g⁻¹ * z * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * z * g) := by
    intro y z hyz
    calc (g⁻¹ * z * g) * (g⁻¹ * y * g) = g⁻¹ * (z * y) * g := by group
      _ = g⁻¹ * (y * z) * g := by rw [hyz]
      _ = (g⁻¹ * y * g) * (g⁻¹ * z * g) := by group
  apply le_antisymm
  · rintro d ⟨hdD, hdC⟩
    have hd' : g⁻¹ * d * g ∈ coordinateD K ⊓
        Subgroup.centralizer (coordinateU K : Set (Equiv.Perm (Omega K))) := by
      refine Subgroup.mem_inf.mpr ⟨(coordinateD K).mul_mem ((coordinateD K).mul_mem
        ((coordinateD K).inv_mem hgD) hdD) hgD, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      rw [← hX'eq] at hh
      have hc := (Subgroup.mem_centralizer_iff.mp hdC) _ ((hmemX' h).mp hh)
      have := hconj _ _ hc
      simpa [mul_assoc] using this
    rw [coordinateD_inf_centralizer_coordinateU, ← hX'eq] at hd'
    have := (hmemX' _).mp hd'
    simpa [mul_assoc] using this
  · intro y hy
    refine Subgroup.mem_inf.mpr ⟨hXD hy, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hy' : g⁻¹ * y * g ∈ coordinateU K := by
      rw [← hX'eq, hmemX']
      simpa [mul_assoc] using hy
    have hz' : g⁻¹ * z * g ∈ coordinateU K := by
      rw [← hX'eq, hmemX']
      simpa [mul_assoc] using hz
    have hcomm : (g⁻¹ * z * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * z * g) := by
      have hC := (coordinateD_inf_centralizer_coordinateU (K := K)).ge hy'
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hC).2) _ hz'
    have := congrArg (fun w => g * w * g⁻¹) hcomm
    simpa [mul_assoc] using this

theorem conj_mem_coordinateU_of_fixes {m u : Equiv.Perm (Omega K)} (hmD : m ∈ coordinateD K)
    (hminf : m none = none) (hu : u ∈ coordinateU K) : m * u * m⁻¹ ∈ coordinateU K := by
  obtain ⟨s, c, hsc⟩ := exists_affine_of_mem_coordinateD hmD hminf
  rw [CFSG.LinearGroups.coordinateU_eq_range] at hu ⊢
  obtain ⟨b, rfl⟩ := hu
  have hb : CFSG.LinearGroups.translationHom K b = translation K (Multiplicative.toAdd b) := rfl
  rw [hb, CFSG.LinearGroups.conj_translation_of_affine hminf hsc]
  exact ⟨Multiplicative.ofAdd (s * Multiplicative.toAdd b), rfl⟩

theorem mem_normalizer_of_fixes [Finite K] {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ f)
    {X : Subgroup (Equiv.Perm (Omega K))} (hXD : X ≤ coordinateD K) (hX : IsPGroup p X)
    (hXcard : Nat.card X = p ^ f) {x : Omega K} (hx : ∀ g ∈ X, g x = x)
    {n : Equiv.Perm (Omega K)} (hnD : n ∈ coordinateD K) (hnx : n x = x) :
    n ∈ Subgroup.normalizer (X : Set (Equiv.Perm (Omega K))) := by
  obtain ⟨⟨h, hhG⟩, hhx⟩ := coordinateG_orbit_infinity K x
  have hhD : h ∈ coordinateD K := coordinateG_le_D K hhG
  have hX'eq := map_conj_eq_coordinateU hp hK hXD hX hXcard hx hhD hhx
  have hmemX' : ∀ y, y ∈ X ↔ h⁻¹ * y * h ∈ coordinateU K := by
    intro y
    rw [← hX'eq]
    constructor
    · intro hy
      exact ⟨y, hy, by simp⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = y := by
        have := congrArg (fun w => h * w * h⁻¹) hzy
        simpa [mul_assoc] using this
      rwa [← this]
  have hn'D : h⁻¹ * n * h ∈ coordinateD K :=
    (coordinateD K).mul_mem ((coordinateD K).mul_mem ((coordinateD K).inv_mem hhD) hnD) hhD
  have hn'inf : (h⁻¹ * n * h) none = none := by
    simp only [Equiv.Perm.mul_apply]
    rw [show h none = x from hhx, hnx, Equiv.Perm.inv_eq_iff_eq, ← hhx]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [hmemX' y, hmemX' (n * y * n⁻¹)]
  have hn'Dinv : (h⁻¹ * n * h)⁻¹ ∈ coordinateD K := (coordinateD K).inv_mem hn'D
  have hn'infinv : (h⁻¹ * n * h)⁻¹ none = none := by
    rw [Equiv.Perm.inv_eq_iff_eq, hn'inf]
  constructor
  · intro hy
    have := conj_mem_coordinateU_of_fixes hn'D hn'inf hy
    simpa [mul_assoc] using this
  · intro hy
    have := conj_mem_coordinateU_of_fixes hn'Dinv hn'infinv hy
    simpa [mul_assoc] using this

theorem multiplier_mem_coordinateG_iff [Finite K] (c : Kˣ) :
    multiplier K c ∈ coordinateG K ↔ IsSquare (c : K) := by
  constructor
  · intro h
    rw [← coordinatePSLAction_range_eq_G] at h
    obtain ⟨g, hg⟩ := h
    rw [← coordinatePGLAction_toPGL, ← coordinatePGLAction_diagonal] at hg
    have hmem : Matrix.ProjGenLinGroup.mk (diagonalGL K c) ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
      ⟨g, coordinatePGLAction_injective K hg⟩
    rw [CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare] at hmem
    rwa [diagonalGL_det K c] at hmem
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [ha, mul_zero])
    have h := CFSG.LinearGroups.multiplier_sq_mem_coordinateG (Units.mk0 a ha0)
    have hc : (Units.mk0 a ha0) ^ 2 = c := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, ha, pow_two]
    rwa [hc] at h

theorem two_ne_zero_of_card_eq_pow [Finite K] {p f : ℕ} (hpodd : Odd p)
    (hK : Nat.card K = p ^ f) : (2 : K) ≠ 0 := by
  intro h
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h
  have : Fintype K := Fintype.ofFinite K
  have h2 := FiniteField.even_card_of_char_two (F := K) (ringChar.eq K 2)
  rw [Fintype.card_eq_nat_card, hK] at h2
  have := Nat.odd_iff.mp (hpodd.pow : Odd (p ^ f))
  omega

theorem mem_coordinateG_iff_of_involution_fixed [Finite K] {p f : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hK : Nat.card K = p ^ f) {g : Equiv.Perm (Omega K)}
    (hgD : g ∈ coordinateD K) (hg : orderOf g = 2) {x : Omega K} (hx : g x = x) :
    g ∈ coordinateG K ↔ p ^ f % 4 = 1 := by
  have _ := hp.pos
  obtain ⟨⟨h, hhG⟩, hhx⟩ := coordinateG_orbit_infinity K x
  have hhD : h ∈ coordinateD K := coordinateG_le_D K hhG
  set g' := h⁻¹ * g * h with hg'
  have hg'D : g' ∈ coordinateD K :=
    (coordinateD K).mul_mem ((coordinateD K).mul_mem ((coordinateD K).inv_mem hhD) hgD) hhD
  have hg'inf : g' none = none := by
    simp only [hg', Equiv.Perm.mul_apply]
    rw [show h none = x from hhx, hx, Equiv.Perm.inv_eq_iff_eq, ← hhx]
  have hg'2 : g' * g' = 1 := by
    have h2 : g * g = 1 := by rw [← pow_two, ← hg, pow_orderOf_eq_one]
    calc g' * g' = h⁻¹ * (g * g) * h := by simp only [hg']; group
      _ = 1 := by rw [h2]; group
  have hg'1 : g' ≠ 1 := by
    intro h1
    have : g = 1 := by
      calc g = h * g' * h⁻¹ := by simp only [hg']; group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hg
    omega
  obtain ⟨s, b, hsb⟩ := exists_affine_of_mem_coordinateD hg'D hg'inf
  have hsq : ∀ z : K, (s : K) * ((s : K) * z + b) + b = z := by
    intro z
    have := congrArg (fun φ : Equiv.Perm (Omega K) => φ (some z)) hg'2
    simp only [Equiv.Perm.mul_apply, hsb, Equiv.Perm.one_apply, Option.some_inj] at this
    exact this
  have h0 := hsq 0
  have h1 := hsq 1
  have hs2 : (s : K) * s = 1 := by linear_combination h1 - h0
  have hsne : (s : K) ≠ 1 := by
    intro hs1
    rw [hs1, mul_zero, zero_add, one_mul] at h0
    have hb : b = 0 := by
      have h2 : (2 : K) * b = 0 := by linear_combination h0
      exact (mul_eq_zero.mp h2).resolve_left (two_ne_zero_of_card_eq_pow hpodd hK)
    apply hg'1
    refine Equiv.ext fun z => ?_
    cases z with
    | none => rw [hg'inf, Equiv.Perm.one_apply]
    | some z => rw [hsb, hs1, hb, one_mul, add_zero, Equiv.Perm.one_apply]
  have hsm : (s : K) = -1 := by
    have h3 : ((s : K) - 1) * ((s : K) + 1) = 0 := by linear_combination hs2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) hsne
    · exact eq_neg_of_add_eq_zero_left h4
  have hg'eq : g' = translation K b * multiplier K (-1) := by
    refine Equiv.ext fun z => ?_
    cases z with
    | none => rw [hg'inf, Equiv.Perm.mul_apply, multiplier_none, translation_none]
    | some z =>
      rw [hsb, hsm, Equiv.Perm.mul_apply, multiplier_some, translation_some]
      simp
  have hiff1 : g ∈ coordinateG K ↔ g' ∈ coordinateG K := by
    constructor
    · intro hgG
      exact (coordinateG K).mul_mem ((coordinateG K).mul_mem ((coordinateG K).inv_mem hhG) hgG)
        hhG
    · intro hg'G
      have : g = h * g' * h⁻¹ := by simp only [hg']; group
      rw [this]
      exact (coordinateG K).mul_mem ((coordinateG K).mul_mem hhG hg'G) ((coordinateG K).inv_mem hhG)
  have hiff2 : g' ∈ coordinateG K ↔ multiplier K (-1) ∈ coordinateG K := by
    rw [hg'eq]
    constructor
    · intro h1
      have := (coordinateG K).mul_mem
        ((coordinateG K).inv_mem (CFSG.LinearGroups.translation_mem_coordinateG b)) h1
      simpa using this
    · intro h1
      exact (coordinateG K).mul_mem (CFSG.LinearGroups.translation_mem_coordinateG b) h1
  rw [hiff1, hiff2, multiplier_mem_coordinateG_iff, Units.val_neg, Units.val_one]
  have : Fintype K := Fintype.ofFinite K
  rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card, hK]
  have := Nat.odd_iff.mp (hpodd.pow : Odd (p ^ f))
  omega

theorem card_coordinateD_inf_stabilizer [Finite K] (x : Omega K) :
    Nat.card (coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x :
      Subgroup (Equiv.Perm (Omega K))) = Nat.card K * (Nat.card K - 1) := by
  have h : (MulAction.stabilizer (coordinateD K) x).map (coordinateD K).subtype =
      coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x := by
    ext g
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.mem_inf,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
    · rintro ⟨hg, hgx⟩
      exact ⟨⟨g, hg⟩, hgx, rfl⟩
  rw [← h, Subgroup.card_map_of_injective (coordinateD K).subtype_injective,
    card_stabilizer_coordinateD]

theorem eq_one_of_commute_two_point [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) {x y : Omega K} (hxy : x ≠ y) {w u : Equiv.Perm (Omega K)}
    (hwD : w ∈ coordinateD K) (hwx : w x = x) (hwy : w y = y) (hw1 : w ≠ 1)
    (huD : u ∈ coordinateD K) (hux : u x = x) {k : ℕ} (huk : u ^ p ^ k = 1)
    (hcomm : w * u = u * w) : u = 1 := by
  have hwuy : w (u y) = u y := by
    have := congrArg (fun φ : Equiv.Perm (Omega K) => φ y) hcomm
    simp only [Equiv.Perm.mul_apply, hwy] at this
    exact this
  have huyx : u y ≠ x := by
    intro h
    exact hxy (u.injective (h.trans hux.symm)).symm
  have huy : u y = y := by
    by_contra huy
    exact hw1 (eq_one_of_three_fixed_points K hwD hxy (Ne.symm huyx) (Ne.symm huy) hwx hwy hwuy)
  have hmem : u ∈ (coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Omega K)) y : Subgroup (Equiv.Perm (Omega K))) :=
    ⟨⟨huD, hux⟩, huy⟩
  have hf : 1 ≤ f := one_le_of_card_eq_pow hK
  have hcard : Nat.card (coordinateD K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Omega K)) y : Subgroup (Equiv.Perm (Omega K))) =
      p ^ f - 1 := by
    obtain ⟨g, hg, hgx, hgy⟩ := exists_coordinateG_infinity_zero (F := K) hxy
    rw [two_point_stabilizer_eq_map hg hgx hgy, Subgroup.card_map_of_injective
      (MulAut.conj g).injective, ← Nat.card_congr (MonoidHom.ofInjective
        (multiplierHom_injective K)).toEquiv, Nat.card_units, hK]
  have h1 : orderOf u ∣ p ^ f - 1 := by
    rw [← hcard]
    have := Subgroup.orderOf_dvd_natCard _ hmem
    exact this
  have h2 : orderOf u ∣ p ^ k := orderOf_dvd_of_pow_eq_one huk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h2
  rw [hj] at h1
  have := pow_eq_one_of_dvd_pow_sub_one hp hf h1
  rw [← hj, orderOf_eq_one_iff] at this
  exact this

theorem fixes_two_of_prime_dvd [Finite K] {p f r : ℕ} (hK : Nat.card K = p ^ f)
    {g : Equiv.Perm (Omega K)} (hgD : g ∈ coordinateD K) (hr : r.Prime) (hr2 : r ≠ 2)
    (hg : orderOf g = r) (hrq : r ∣ p ^ f - 1) :
    ∃ x y : Omega K, x ≠ y ∧ g x = x ∧ g y = y := by
  have : Fact r.Prime := ⟨hr⟩
  have hgr : IsPGroup r (Subgroup.zpowers g) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hg, pow_one]
  have hmod := hgr.card_modEq_card_fixedPoints (Omega K)
  have hfix : ∀ x : Omega K, x ∈ MulAction.fixedPoints (Subgroup.zpowers g) (Omega K) ↔
      g x = x := by
    intro x
    constructor
    · intro hx
      exact hx ⟨g, Subgroup.mem_zpowers g⟩
    · intro hx h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
      change (h : Equiv.Perm (Omega K)) x = x
      rw [← hk]
      exact (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx k)
  set S := MulAction.fixedPoints (Subgroup.zpowers g) (Omega K) with hS
  have hcardS : Nat.card S = S.ncard := Nat.card_coe_set_eq S
  have hle : S.ncard ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff).mp hlt
    have h1 := eq_one_of_three_fixed_points K hgD hab hac hbc ((hfix a).mp ha) ((hfix b).mp hb)
      ((hfix c).mp hc)
    rw [h1, orderOf_one] at hg
    exact hr.one_lt.ne' hg.symm
  have hΩ : Nat.card (Omega K) = p ^ f + 1 := by rw [Omega, Finite.card_option, hK]
  rw [hΩ, hcardS] at hmod
  have h1 : 1 ≤ p ^ f := by
    rcases Nat.eq_zero_or_pos (p ^ f) with h | h
    · rw [h] at hK
      exact absurd hK (Nat.card_pos (α := K)).ne'
    · exact h
  have hmod2 : p ^ f + 1 ≡ 2 [MOD r] := by
    have : p ^ f + 1 = (p ^ f - 1) + 2 := by omega
    rw [this]
    exact (Nat.modEq_zero_iff_dvd.mpr hrq).add_right 2
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hS2 : S.ncard = 2 := by
    have h3 := hmod.symm.trans hmod2
    interval_cases hS : S.ncard
    · exact absurd ((Nat.modEq_iff_dvd' (by omega)).mp h3) (fun h => by
        have := Nat.le_of_dvd (by omega) h; omega)
    · exact absurd ((Nat.modEq_iff_dvd' (by omega)).mp h3) (fun h => by
        have := Nat.le_of_dvd (by omega) h; omega)
    · rfl
  obtain ⟨x, y, hxy, hSxy⟩ := Set.ncard_eq_two.mp hS2
  refine ⟨x, y, hxy, (hfix x).mp ?_, (hfix y).mp ?_⟩
  · rw [hSxy]; exact Or.inl rfl
  · rw [hSxy]; exact Or.inr rfl

theorem card_add_one_le_of_two_point [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) {x y : Omega K} (hxy : x ≠ y)
    {A X : Subgroup (Equiv.Perm (Omega K))} (hAD : A ≤ coordinateD K) (hAx : ∀ a ∈ A, a x = x)
    (hAy : ∀ a ∈ A, a y = y) (hXD : X ≤ coordinateD K) (hX : IsPGroup p X)
    (hXx : ∀ u ∈ X, u x = x) (hX1 : X ≠ ⊥)
    (hAX : A ≤ Subgroup.normalizer (X : Set (Equiv.Perm (Omega K)))) :
    Nat.card A + 1 ≤ Nat.card X := by
  obtain ⟨⟨u, huX⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  have hconjX : ∀ a ∈ A, a * u * a⁻¹ ∈ X := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hAX ha) u).mp huX
  let φ : Option A → X := fun o => match o with
    | none => 1
    | some a => ⟨(a : Equiv.Perm (Omega K)) * u * (a : Equiv.Perm (Omega K))⁻¹, hconjX a a.2⟩
  have hinj : Function.Injective φ := by
    intro o₁ o₂ h
    cases o₁ with
    | none =>
      cases o₂ with
      | none => rfl
      | some b =>
        exfalso
        have h1 : (b : Equiv.Perm (Omega K)) * u * (b : Equiv.Perm (Omega K))⁻¹ = 1 :=
          (congrArg Subtype.val h).symm
        apply hu1
        have := congrArg (fun z => (b : Equiv.Perm (Omega K))⁻¹ * z * b) h1
        simpa [mul_assoc] using this
    | some a =>
      cases o₂ with
      | none =>
        exfalso
        have h1 : (a : Equiv.Perm (Omega K)) * u * (a : Equiv.Perm (Omega K))⁻¹ = 1 :=
          congrArg Subtype.val h
        apply hu1
        have := congrArg (fun z => (a : Equiv.Perm (Omega K))⁻¹ * z * a) h1
        simpa [mul_assoc] using this
      | some b =>
        have h1 : (a : Equiv.Perm (Omega K)) * u * (a : Equiv.Perm (Omega K))⁻¹ =
            (b : Equiv.Perm (Omega K)) * u * (b : Equiv.Perm (Omega K))⁻¹ := congrArg Subtype.val h
        set w : Equiv.Perm (Omega K) := (b : Equiv.Perm (Omega K))⁻¹ * a with hw
        have hwA : w ∈ A := A.mul_mem (A.inv_mem b.2) a.2
        have hwu : w * u = u * w := by
          have := congrArg (fun z => (b : Equiv.Perm (Omega K))⁻¹ * z * a) h1
          simp only [hw] at this ⊢
          calc (b : Equiv.Perm (Omega K))⁻¹ * a * u
              = (b : Equiv.Perm (Omega K))⁻¹ * (a * u * (a : Equiv.Perm (Omega K))⁻¹) * a := by
                group
            _ = (b : Equiv.Perm (Omega K))⁻¹ * (b * u * (b : Equiv.Perm (Omega K))⁻¹) * a := by
                rw [h1]
            _ = u * ((b : Equiv.Perm (Omega K))⁻¹ * a) := by group
        obtain ⟨k, hk⟩ := hX ⟨u, huX⟩
        have hk' : u ^ p ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        by_cases hw1 : w = 1
        · congr 1
          apply Subtype.ext
          have : (b : Equiv.Perm (Omega K))⁻¹ * a = 1 := hw1
          have := congrArg (fun z => (b : Equiv.Perm (Omega K)) * z) this
          simpa using this
        · exact absurd (eq_one_of_commute_two_point hp hK hxy (hAD hwA) (hAx w hwA)
            (hAy w hwA) hw1 (hXD huX) (hXx u huX) hk' hwu) hu1
  have := Nat.card_le_card_of_injective φ hinj
  rwa [Finite.card_option] at this

theorem mem_pair_of_mem_normalizer {x y : Omega K} (hxy : x ≠ y)
    {E : Subgroup (Equiv.Perm (Omega K))} (hED : E ≤ coordinateD K) (hEx : ∀ e ∈ E, e x = x)
    (hEy : ∀ e ∈ E, e y = y) (hE1 : E ≠ ⊥) {n : Equiv.Perm (Omega K)}
    (hn : n ∈ Subgroup.normalizer (E : Set (Equiv.Perm (Omega K)))) :
    (n x = x ∧ n y = y) ∨ (n x = y ∧ n y = x) := by
  obtain ⟨⟨e, heE⟩, he1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
  have he1 : e ≠ 1 := fun h => he1' (Subtype.ext h)
  have hfix : ∀ z, z = x ∨ z = y → e (n z) = n z := by
    intro z hz
    have hn' : n⁻¹ * e * n ∈ E := (Subgroup.mem_normalizer_iff''.mp hn e).mp heE
    have h1 : (n⁻¹ * e * n) z = z := by
      rcases hz with rfl | rfl
      · exact hEx _ hn'
      · exact hEy _ hn'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq] at h1
    exact h1
  have hcase : ∀ z, z = x ∨ z = y → n z = x ∨ n z = y := by
    intro z hz
    by_contra hc
    push Not at hc
    exact he1 (eq_one_of_three_fixed_points K (hED heE) hxy (Ne.symm hc.1) (Ne.symm hc.2)
      (hEx e heE) (hEy e heE) (hfix z hz))
  rcases hcase x (Or.inl rfl) with h1 | h1 <;> rcases hcase y (Or.inr rfl) with h2 | h2
  · exact absurd (n.injective (h1.trans h2.symm)) hxy
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (n.injective (h1.trans h2.symm)) hxy

omit [Field K] in
theorem fixes_of_odd_of_pair {x y : Omega K} (hxy : x ≠ y) {n : Equiv.Perm (Omega K)}
    (hn : Odd (orderOf n)) (h : (n x = x ∧ n y = y) ∨ (n x = y ∧ n y = x)) :
    n x = x ∧ n y = y := by
  rcases h with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hsq : (n ^ 2) y = y := by rw [pow_two, Equiv.Perm.mul_apply, h2, h1]
    obtain ⟨k, hk⟩ := hn
    have hpow : (n ^ (2 * k)) y = y := by
      rw [pow_mul]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hsq k
    have h3 : (n ^ (2 * k + 1)) x = y := by
      rw [pow_succ, Equiv.Perm.mul_apply, h1, hpow]
    rw [← hk, pow_orderOf_eq_one, Equiv.Perm.one_apply] at h3
    exact hxy h3

end Projective

end CFSG.Semidihedral.FixedCoreNontrivial
