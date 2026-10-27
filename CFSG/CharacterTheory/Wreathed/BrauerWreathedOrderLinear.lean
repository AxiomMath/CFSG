module

public import CFSG.CharacterTheory.BrauerLinearThree.LayerSetting

public section

namespace CFSG.Wreathed.BrauerWreathedOrder

open Matrix CFSG.DesarguesianPlanes CFSG.BrauerLinearThree

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_orderOf_mul_of_commute {M : Type*} [Monoid M] {x y : M} (hxy : Commute x y)
    (hx : Odd (orderOf x)) (hy : Odd (orderOf y)) : Odd (orderOf (x * y)) :=
  (hx.mul hy).of_dvd_nat (hxy.orderOf_mul_dvd_mul_orderOf)

@[expose] def oddUnits (F : Type) [Field F] : Subgroup Fˣ where
  carrier := {x | Odd (orderOf x)}
  mul_mem' {x y} hx hy := odd_orderOf_mul_of_commute (Commute.all x y) hx hy
  one_mem' := by simp
  inv_mem' {x} hx := by
    change Odd (orderOf x⁻¹)
    rw [orderOf_inv]
    exact hx

theorem mem_oddUnits {F : Type} [Field F] {x : Fˣ} : x ∈ oddUnits F ↔ Odd (orderOf x) :=
  Iff.rfl

theorem orderOf_scalar {F : Type} [Field F] (a : Fˣ) :
    orderOf (GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) F) = orderOf a := by
  apply orderOf_injective _ _ a
  intro x y h
  have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
  exact Units.ext (by simpa [GeneralLinearGroup.scalar] using this)

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0)

omit [Finite F] [Z.Normal] in
include hZ hZodd in
theorem exists_scalar_of_mem {A : GL (Fin 2) F} (hA : A ∈ Z) :
    ∃ μ : Fˣ, Odd (orderOf μ) ∧ A = GeneralLinearGroup.scalar (Fin 2) μ := by
  obtain ⟨μ, rfl⟩ := hZ hA
  refine ⟨μ, ?_, rfl⟩
  rw [← orderOf_scalar, ← Subgroup.orderOf_mk _ hA]
  exact hZodd.of_dvd_nat (orderOf_dvd_natCard _)

omit [Finite F] [Z.Normal] in
include hZodd in
theorem odd_orderOf_of_scalar_mem {a : Fˣ} (ha : GeneralLinearGroup.scalar (Fin 2) a ∈ Z) :
    Odd (orderOf a) := by
  rw [← orderOf_scalar, ← Subgroup.orderOf_mk _ ha]
  exact hZodd.of_dvd_nat (orderOf_dvd_natCard _)

omit [Finite F] in
theorem scalar_commute (a : Fˣ) (B : GL (Fin 2) F) :
    Commute (GeneralLinearGroup.scalar (Fin 2) a) B := by
  have h : GeneralLinearGroup.scalar (Fin 2) a ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨a, rfl⟩
  exact (Subgroup.mem_center_iff.mp h B).symm

include hZ hZodd h2 in
theorem centralizerHom_mem_oddCore_iff (hq3 : 3 ≤ Nat.card F) (A : GL (Fin 2) F) :
    centralizerHom φ A ∈ CFSG.oddCore (Subgroup.centralizer ({J} : Set G)) ↔
      ∃ a : Fˣ, Odd (orderOf a) ∧ A = GeneralLinearGroup.scalar (Fin 2) a := by
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hA
    have hA' : centralizerHom φ A ∈ CFSG.pPrimeCore 2 (Subgroup.centralizer ({J} : Set G)) := by
      rwa [← oddCore_eq_pPrimeCore_two]
    obtain ⟨a₀, ha₀⟩ := (mem_centerSub φ).mp (mem_centerSub_of_mem_pPrimeCore φ hZ hZodd h2 hq3 hA')
    rw [coe_centralizerHom, linearCentralizerHom_eq_iff] at ha₀
    obtain ⟨μ, -, hμ⟩ := exists_scalar_of_mem hZ hZodd ha₀
    set a₁ : Fˣ := μ⁻¹ * a₀ with ha₁
    have hA₁ : A = GeneralLinearGroup.scalar (Fin 2) a₁ := by
      rw [ha₁, map_mul, map_inv, ← hμ]
      group
    refine ⟨a₁, ?_, hA₁⟩
    have hk : Odd (orderOf (centralizerHom φ A)) := by
      rw [← Subgroup.orderOf_mk _ hA']
      exact (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))).of_dvd_nat
        (orderOf_dvd_natCard _)
    set k := orderOf (centralizerHom φ A)
    have hAk : A ^ k ∈ Z := by
      rw [← linearCentralizerHom_eq_one_iff φ, map_pow, ← coe_centralizerHom, ← Subgroup.coe_pow,
        pow_orderOf_eq_one, Subgroup.coe_one]
    rw [hA₁, ← map_pow] at hAk
    have ho := odd_orderOf_of_scalar_mem hZodd hAk
    apply (hk.mul ho).of_dvd_nat
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  · rintro ⟨a, ha, rfl⟩
    set K : Subgroup (Subgroup.centralizer ({J} : Set G)) :=
      ((oddUnits F).map (GeneralLinearGroup.scalar (Fin 2))).map (centralizerHom φ) with hK
    have hmemK : centralizerHom φ (GeneralLinearGroup.scalar (Fin 2) a) ∈ K :=
      ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have hKc : K ≤ Subgroup.center (Subgroup.centralizer ({J} : Set G)) := by
      rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨B, rfl⟩ := centralizerHom_surjective φ c
      rw [← map_mul, ← map_mul, (scalar_commute b B).eq]
    have hKn : K.Normal := Subgroup.normal_of_le_center hKc
    have hKodd : Odd (Nat.card K) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
      rw [Subgroup.orderOf_mk] at hx2
      obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hx
      have hdvd : orderOf (centralizerHom φ (GeneralLinearGroup.scalar (Fin 2) b)) ∣
          orderOf b := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
      rw [hx2] at hdvd
      exact (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr hdvd)
    have hKle : K ≤ CFSG.oddCore (Subgroup.centralizer ({J} : Set G)) :=
      le_sSup ⟨hKn, hKodd⟩
    exact hKle hmemK

end CFSG.Wreathed.BrauerWreathedOrder
