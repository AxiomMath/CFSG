module

public import CFSG.LieType.Chevalley.ChevalleyFrobeniusFixedNormalizer
import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

@[expose] def normSeq {S : Type*} [Group S] (Φ : MulAut S) (g : S) : ℕ → S
  | 0 => 1
  | n + 1 => normSeq Φ g n * (Φ ^ n) g

theorem conj_mul_pow_eq {S : Type*} [Group S] (g : S) (Φ : MulAut S) (n : ℕ) :
    (MulAut.conj g * Φ) ^ n = MulAut.conj (normSeq Φ g n) * Φ ^ n := by
  induction n with
  | zero => simp [normSeq]
  | succ n ih =>
    have e : Φ ^ n * MulAut.conj g = MulAut.conj ((Φ ^ n) g) * Φ ^ n := by
      ext m
      simp [MulAut.mul_apply, map_mul, map_inv]
    calc (MulAut.conj g * Φ) ^ (n + 1)
        = MulAut.conj (normSeq Φ g n) * (Φ ^ n * MulAut.conj g) * Φ := by
          rw [pow_succ, ih]; simp only [mul_assoc]
      _ = MulAut.conj (normSeq Φ g n) * (MulAut.conj ((Φ ^ n) g) * Φ ^ n) * Φ := by rw [e]
      _ = MulAut.conj (normSeq Φ g (n + 1)) * Φ ^ (n + 1) := by
          rw [normSeq, map_mul, pow_succ]; simp only [mul_assoc]

theorem normSeq_eq_one_of_pow_eq_one {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥)
    {g : S} {Φ : MulAut S} {r : ℕ} (hΦ : Φ ^ r = 1) (h : (MulAut.conj g * Φ) ^ r = 1) :
    normSeq Φ g r = 1 := by
  rw [conj_mul_pow_eq, hΦ, mul_one] at h
  have hmem : normSeq Φ g r ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun φ : MulAut S => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem

section Lang

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_conj_mul_eq_of_norm_eq_one_r_aux {τ : Tag} {K : Type} [Field K] [Finite K]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] {p m r : ℕ} [Fact p.Prime]
    [CharP L p] (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : Nat.card K = p ^ (r * m)) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ p ^ m) {Φ : MulAut (adjointGroup τ K)}
    (hΦ : ∀ h, (Φ h : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K))
    {g : adjointGroup τ K} (hN : normSeq Φ g r = 1) :
    ∃ β : MulAut (adjointGroup τ K), MulAut.conj g * Φ = β * Φ * β⁻¹ := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set ι : K →+* L := algebraMap K L with hι
  set Fr0 : L →+* L := iterateFrobenius L p m with hFr0
  have hFr0ι : Fr0.comp ι = ι.comp σ.toRingHom := by
    ext c
    simp only [RingHom.comp_apply, hFr0, iterateFrobenius_def, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, hσ, map_pow]
  set Fr : L →+* L := iterateFrobenius L p ((n + 1) * m) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    rw [hK]
    rfl
  obtain ⟨S, hS, hLang⟩ :=
    (CFSG.LieType.AlgebraicGroups.exceptional_all_characteristic_field_Lang_surjectivity p L m
      hm).1 τ
  have hS' : ∀ y : adjointGroup τ L, (S y : ModGL τ L) = baseChangeGL Fr0 (y : ModGL τ L) :=
    fun y => hS y
  have hSpow : ∀ (k : ℕ) (y : adjointGroup τ L), ((S ^ (k + 1)) y : ModGL τ L) =
      baseChangeGL (iterateFrobenius L p ((k + 1) * m)) (y : ModGL τ L) := by
    intro k
    induction k with
    | zero => intro y; rw [zero_add, pow_one, hS', one_mul]
    | succ k ih =>
      intro y
      have hcomp : (iterateFrobenius L p ((k + 1) * m)).comp Fr0 =
          iterateFrobenius L p ((k + 1 + 1) * m) := by
        rw [show (k + 1 + 1) * m = (k + 1) * m + m by ring, iterateFrobenius_add]
      rw [pow_succ, MulAut.mul_apply, ih, hS', baseChangeGL_baseChangeGL, hcomp]
  let J : adjointGroup τ K →* adjointGroup τ L :=
    ((baseChangeGL ι).comp (adjointGroup τ K).subtype).codRestrict (adjointGroup τ L)
      fun x => CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι x.2
  have hJ : ∀ x, (J x : ModGL τ L) = baseChangeGL ι (x : ModGL τ K) := fun x => rfl
  have hJinj : Function.Injective J := fun x y hxy =>
    Subtype.ext (baseChangeGL_injective ι (by rw [← hJ, ← hJ, hxy]))
  have hSJ : ∀ x, S (J x) = J (Φ x) := by
    intro x
    refine Subtype.ext ?_
    rw [hS', hJ, hJ, hΦ, baseChangeGL_baseChangeGL]
    change _ = baseChangeGL ι (baseChangeGL σ.toRingHom (x : ModGL τ K))
    rw [baseChangeGL_baseChangeGL, hFr0ι]
  have hSJn : ∀ (k : ℕ) (x : adjointGroup τ K), (S ^ k) (J x) = J ((Φ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hSJ, ih]
  obtain ⟨h, hh⟩ := hLang (J g)
  have hSh : S h = h * J g := by
    rw [hh]
    group
  have hSk : ∀ k : ℕ, (S ^ k) h = h * J (normSeq Φ g k) := by
    intro k
    induction k with
    | zero => simp [normSeq]
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, hSh, map_mul, ih, hSJn, mul_assoc, ← map_mul, normSeq]
  have hSr : (S ^ (n + 1)) h = h := by
    rw [hSk, hN, map_one, mul_one]
  obtain ⟨-, -, hnorm⟩ := Chevalley_Frobenius_fixed_ambient_normalizer τ K L Fr hFr
  have hFh : Units.map (entrywiseHom Fr) (h : ModGL τ L) = (h : ModGL τ L) := by
    change baseChangeGL Fr (h : ModGL τ L) = (h : ModGL τ L)
    have h1 := congrArg (fun y : adjointGroup τ L => (y : ModGL τ L)) hSr
    simp only [hSpow] at h1
    exact h1
  have hhN := hnorm ⟨h.2, hFh⟩
  have hmemJ : ∀ z : adjointGroup τ L, z ∈ J.range ↔
      (z : ModGL τ L) ∈ (adjointGroup τ K).map (baseChangeGL ι) := by
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, hxz⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  have hhJ : h⁻¹ ∈ Subgroup.normalizer (J.range : Set (adjointGroup τ L)) := by
    refine inv_mem (Subgroup.mem_normalizer_iff.mpr fun z => ?_)
    rw [hmemJ, hmemJ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hhN z
  let ιJ : adjointGroup τ K ≃* J.range := MonoidHom.ofInjective hJinj
  let β : MulAut (adjointGroup τ K) :=
    MulAut.congr ιJ.symm (J.range.normalizerMonoidHom ⟨h⁻¹, hhJ⟩)
  have hJβ : ∀ x, J (β x) = h⁻¹ * J x * h := by
    intro x
    have h1 : ιJ (β x) = J.range.normalizerMonoidHom ⟨h⁻¹, hhJ⟩ (ιJ x) := by
      simp only [β, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      MonoidHom.ofInjective_apply, inv_inv] at h2
    exact h2
  refine ⟨β, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  refine MulEquiv.ext fun x => hJinj ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulAut.mul_apply, hJβ, ← hSJ, ← hSJ, hJβ, hh]
  simp only [map_mul, map_inv]
  group

theorem exists_conj_mul_eq_of_norm_eq_one_r {τ : Tag} {K : Type} [Field K] [Finite K]
    {p m r : ℕ} [Fact p.Prime] [CharP K p] (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hK : Nat.card K = p ^ (r * m)) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ p ^ m)
    {Φ : MulAut (adjointGroup τ K)}
    (hΦ : ∀ h, (Φ h : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K))
    {g : adjointGroup τ K} (hN : normSeq Φ g r = 1) :
    ∃ β : MulAut (adjointGroup τ K), MulAut.conj g * Φ = β * Φ * β⁻¹ :=
  exists_conj_mul_eq_of_norm_eq_one_r_aux (AlgebraicClosure K) hm hr hK hσ hΦ hN

end Lang

end CFSG.GH74.GLS.Stage2.OddAut
