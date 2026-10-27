module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenFinal
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenNabSympl
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilDual
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilJoint
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilWeight

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
open scoped commutatorElement

section FieldFacts

variable {K : Type} [Field K] [CharP K 2]

theorem exists_isPrimitiveRoot_five [IsAlgClosed K] : ∃ ζ : K, IsPrimitiveRoot ζ 5 := by
  have h5 : ((5 : ℕ) : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 5).mp h
    omega
  have : NeZero ((5 : ℕ) : K) := ⟨h5⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 5 K)
    (by rw [Polynomial.degree_cyclotomic]; norm_num)
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

theorem cast_odd_eq_one {n : ℕ} (hn : Odd n) : (n : K) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  push_cast
  rw [h2, zero_mul, zero_add]

theorem pow_two_pow_ne_one (ξ : Kˣ) (hξ : ξ ≠ 1) (j : ℕ) : ξ ^ (2 ^ j) ≠ 1 := by
  intro h
  apply hξ
  have h1 : (ξ : K) ^ (2 ^ j) = 1 := by
    have := congrArg Units.val h
    simpa using this
  have h2 : ((ξ : K) - 1) ^ (2 ^ j) = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  have h3 : (ξ : K) - 1 = 0 := pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h2
  exact Units.ext (sub_eq_zero.mp h3)

end FieldFacts

section Distinct

variable {K : Type} [Field K]

theorem dvd_of_pow_eq_one_of_pow_prime {p : ℕ} (hp : p.Prime) {k : ℕ} (η : Kˣ) (hη : η ≠ 1)
    (hηk : η ^ (p ^ k) = 1) {n : ℕ} (hn : η ^ n = 1) : p ∣ n := by
  have h1 : orderOf η ∣ p ^ k := orderOf_dvd_of_pow_eq_one hηk
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow hp).mp h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hη (orderOf_eq_one_iff.mp (by simpa using hs))
  have h2 : p ∣ orderOf η := by
    rw [hs]
    exact dvd_pow_self p hs0
  exact h2.trans (orderOf_dvd_of_pow_eq_one hn)

theorem pow_two_pow_injective [CharP K 2] {p : ℕ} (hp : p.Prime) (hodd : Odd p) {k : ℕ} (ξ : Kˣ)
    (hξ : ξ ≠ 1) (hξk : ξ ^ (p ^ k) = 1) {ℓ : ℕ} (hℓ : ℓ = if p = 3 then 2 else 3) :
    ∀ i j : ℕ, i < ℓ → j < ℓ → ξ ^ (2 ^ i) = ξ ^ (2 ^ j) → i = j := by
  have key : ∀ i j : ℕ, i < j → j < ℓ → ξ ^ (2 ^ i) = ξ ^ (2 ^ j) → False := by
    intro i j hij hjℓ h
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    set η : Kˣ := ξ ^ (2 ^ i) with hη
    have hη1 : η ≠ 1 := pow_two_pow_ne_one ξ hξ i
    have hηk : η ^ (p ^ k) = 1 := by
      rw [hη, ← pow_mul, mul_comm, pow_mul, hξk, one_pow]
    have hηm : η ^ (2 ^ (m + 1)) = η := by
      have : η ^ (2 ^ (m + 1)) = ξ ^ (2 ^ (i + m + 1)) := by
        rw [hη, ← pow_mul, ← pow_add, show i + (m + 1) = i + m + 1 from by ring]
      rw [this]
      exact h.symm
    have hηm' : η ^ (2 ^ (m + 1) - 1) = 1 := by
      have h2 : (2 : ℕ) ^ (m + 1) = (2 ^ (m + 1) - 1) + 1 := by
        have := Nat.one_le_two_pow (n := m + 1)
        omega
      rw [h2, pow_succ] at hηm
      exact mul_right_cancel (hηm.trans (one_mul η).symm)
    have hpd := dvd_of_pow_eq_one_of_pow_prime hp η hη1 hηk hηm'
    have hp3 : 3 ≤ p := by
      obtain ⟨c, rfl⟩ := hodd
      have := hp.two_le
      omega
    by_cases hp3' : p = 3
    · have hℓ2 : ℓ = 2 := by simp [hℓ, hp3']
      have hm : m = 0 := by omega
      subst hm
      norm_num at hpd
      exact hp.one_lt.ne' hpd
    · have hℓ3 : ℓ = 3 := by simp [hℓ, hp3']
      have hm : m = 0 ∨ m = 1 := by omega
      rcases hm with rfl | rfl
      · norm_num at hpd
        exact hp.one_lt.ne' hpd
      · norm_num at hpd
        have := Nat.le_of_dvd (by norm_num) hpd
        omega
  intro i j hi hj h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj h).elim
  · exact hij
  · exact (key j i hij hi h.symm).elim

end Distinct

section Eigen

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem exists_hom_of_eigen {Z : Type} [Group Z] (f : Z →* Module.End K W) {φ : W} (hφ : φ ≠ 0)
    (h : ∀ z, ∃ μ : K, f z φ = μ • φ) : ∃ χ : Z →* Kˣ, ∀ z, f z φ = (χ z : K) • φ := by
  choose μ hμ using h
  have huniq : ∀ a b : K, a • φ = b • φ → a = b := fun a b hab =>
    smul_left_injective K hφ hab
  have h1 : μ 1 = 1 := by
    apply huniq
    rw [← hμ, map_one, Module.End.one_apply, one_smul]
  have hm : ∀ a b, μ (a * b) = μ a * μ b := by
    intro a b
    apply huniq
    rw [← hμ, map_mul, Module.End.mul_apply, hμ b, map_smul, hμ a, smul_smul, mul_comm, mul_smul]
  have hne : ∀ z, μ z ≠ 0 := by
    intro z hz
    have := hm z z⁻¹
    rw [mul_inv_cancel, h1, hz, zero_mul] at this
    exact one_ne_zero this
  refine ⟨MonoidHom.mk' (fun z => Units.mk0 (μ z) (hne z)) (fun a b => Units.ext (hm a b)),
    fun z => hμ z⟩

end Eigen

section WeightSpace

open WeilDual

variable {V : Type} [CommGroup V] (K : Type) [Field K] [Algebra (ZMod 2) K]
  [Module (ZMod 2) (Additive V)]

@[expose] noncomputable def actP (P : Subgroup (MulAut V)) :
    ↥P →* Module.End K (Additive V →ₗ[ZMod 2] K) :=
  (actHom K).comp P.subtype

theorem actP_apply (P : Subgroup (MulAut V)) (g : ↥P) :
    actP K P g = actHom K (g : MulAut V) := rfl

@[expose] def wsp (P : Subgroup (MulAut V)) (lam : Subgroup.center ↥P →* Kˣ) :
    Submodule K (Additive V →ₗ[ZMod 2] K) where
  carrier := {φ | ∀ z : Subgroup.center ↥P, actP K P (z : ↥P) φ = (lam z : K) • φ}
  zero_mem' := fun z => by simp
  add_mem' := fun {a b} (ha : ∀ z : Subgroup.center ↥P, actP K P (z : ↥P) a = (lam z : K) • a)
      (hb : ∀ z : Subgroup.center ↥P, actP K P (z : ↥P) b = (lam z : K) • b) z => by
    simp only [map_add, smul_add, ha z, hb z]
  smul_mem' := fun c a
      (ha : ∀ z : Subgroup.center ↥P, actP K P (z : ↥P) a = (lam z : K) • a) z => by
    simp only [map_smul, ha z, smul_comm c]

theorem mem_wsp {P : Subgroup (MulAut V)} {lam : Subgroup.center ↥P →* Kˣ}
    {φ : Additive V →ₗ[ZMod 2] K} :
    φ ∈ wsp K P lam ↔ ∀ z : Subgroup.center ↥P, actP K P (z : ↥P) φ = (lam z : K) • φ := Iff.rfl

theorem actP_mem_wsp {P : Subgroup (MulAut V)} {lam : Subgroup.center ↥P →* Kˣ} (g : ↥P)
    {φ : Additive V →ₗ[ZMod 2] K} (hφ : φ ∈ wsp K P lam) : actP K P g φ ∈ wsp K P lam := by
  intro z
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.mp z.2 g,
    map_mul, Module.End.mul_apply, hφ z, map_smul]

theorem actHom_mem_wsp {P : Subgroup (MulAut V)} {lam : Subgroup.center ↥P →* Kˣ} {y : MulAut V}
    (hy : ∀ z : Subgroup.center ↥P, y * ((z : ↥P) : MulAut V) = ((z : ↥P) : MulAut V) * y)
    {φ : Additive V →ₗ[ZMod 2] K} (hφ : φ ∈ wsp K P lam) : actHom K y φ ∈ wsp K P lam := by
  intro z
  have h : actP K P (z : ↥P) * actHom K y = actHom K y * actP K P (z : ↥P) := by
    rw [actP_apply, ← map_mul, ← map_mul, (hy z).symm]
  rw [← Module.End.mul_apply, h, Module.End.mul_apply, hφ z, map_smul]

section Frobenius

variable [CharP K 2]

theorem frob_mem_wsp {P : Subgroup (MulAut V)} {lam : Subgroup.center ↥P →* Kˣ}
    {φ : Additive V →ₗ[ZMod 2] K} (hφ : φ ∈ wsp K P lam) : frob K φ ∈ wsp K P (lam ^ 2) := by
  intro z
  rw [actP_apply, actHom_frob, ← actP_apply, hφ z, frob_smul]
  simp [MonoidHom.pow_apply]

theorem frob_iter_mem_wsp {P : Subgroup (MulAut V)} {lam : Subgroup.center ↥P →* Kˣ}
    {φ : Additive V →ₗ[ZMod 2] K} (hφ : φ ∈ wsp K P lam) (j : ℕ) :
    (frob K)^[j] φ ∈ wsp K P (lam ^ (2 ^ j)) := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply', pow_succ, pow_mul]
    exact frob_mem_wsp K ih

theorem frob_iter_ne_zero {φ : Additive V →ₗ[ZMod 2] K} (hφ : φ ≠ 0) (j : ℕ) :
    (frob K)^[j] φ ≠ 0 := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact frob_ne_zero K ih

end Frobenius

end WeightSpace

section Main

open Module WeilDual

variable {V : Type} [CommGroup V] [Finite V] {K : Type} [Field K] [IsAlgClosed K] [CharP K 2]
  [Algebra (ZMod 2) K] [Module (ZMod 2) (Additive V)]

theorem exists_weight (P : Subgroup (MulAut V)) (hodd : Odd (Nat.card ↥P))
    (z₀ : Subgroup.center ↥P) (hz₀ : ((z₀ : ↥P) : MulAut V) ≠ 1) :
    ∃ (φ₀ : Additive V →ₗ[ZMod 2] K) (χ : Subgroup.center ↥P →* Kˣ),
      φ₀ ≠ 0 ∧ φ₀ ∈ wsp K P χ ∧ χ z₀ ≠ 1 := by
  classical
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have : Fintype ↥(Subgroup.center ↥P) := Fintype.ofFinite _
  set ρ := actP K P with hρ
  have hcommZ : ∀ z z' : Subgroup.center ↥P,
      ρ (z : ↥P) * ρ (z' : ↥P) = ρ (z' : ↥P) * ρ (z : ↥P) := by
    intro z z'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp z'.2 (z : ↥P)
  obtain ⟨φ, hφ⟩ := exists_act_ne_one K _ hz₀
  have hρz₀ : ρ (z₀ : ↥P) ≠ 1 := fun h => hφ (by
    have := congrArg (fun f : Module.End K (Additive V →ₗ[ZMod 2] K) => f φ) h
    exact this)
  set c := ρ (z₀ : ↥P) with hc
  let I : Submodule K (Additive V →ₗ[ZMod 2] K) := LinearMap.range (c - 1)
  have hI : I ≠ ⊥ := by
    intro h
    exact hρz₀ (sub_eq_zero.mp (LinearMap.range_eq_bot.mp h))
  have hinvI : ∀ z : Subgroup.center ↥P, ∀ u ∈ I, ρ (z : ↥P) u ∈ I := by
    rintro z _ ⟨w, rfl⟩
    refine ⟨ρ (z : ↥P) w, ?_⟩
    have h : c (ρ (z : ↥P) w) = ρ (z : ↥P) (c w) :=
      congrArg (fun f : Module.End K (Additive V →ₗ[ZMod 2] K) => f w) (hcommZ z₀ z)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, h]
  obtain ⟨φ₀, hφ₀I, hφ₀ne, hφ₀eig⟩ := WeilJoint.exists_joint_eigenvector
    (fun z : Subgroup.center ↥P => ρ (z : ↥P)) hcommZ Finset.univ I hI hinvI
  obtain ⟨χ, hχ⟩ := exists_hom_of_eigen (ρ.comp (Subgroup.center ↥P).subtype) hφ₀ne
    (fun z => hφ₀eig z (Finset.mem_univ z))
  refine ⟨φ₀, χ, hφ₀ne, hχ, fun h1 => ?_⟩
  obtain ⟨u, hu⟩ := hφ₀I
  have hcN : c ^ Nat.card ↥P = 1 := by
    rw [hc, ← map_pow]
    have : ((z₀ : ↥P)) ^ Nat.card ↥P = 1 := pow_card_eq_one'
    rw [this, map_one]
  have hNK : (Nat.card ↥P : K) = 1 := cast_odd_eq_one hodd
  have hfix : c φ₀ = φ₀ := by
    have := hχ z₀
    simp only [MonoidHom.comp_apply] at this
    rw [h1] at this
    simpa using this
  have h0 := WeilJoint.sub_one_apply_eq_zero_of_sq c hcN hNK u (by rw [hu]; exact hfix)
  exact hφ₀ne (hu ▸ h0)

include K in
theorem base_false_aux (hA : ArithStmt) (P : Subgroup (MulAut V)) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) (hab : ¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (x : MulAut V) (hx : x ∈ Subgroup.normalizer (P : Set (MulAut V))) (hx5 : x ^ 5 = 1)
    (hxc : Nat.card (commV (Subgroup.zpowers x)) ≤ 16)
    (G1 : ∀ g h : ↥P, ⁅g, h⁆ ∈ Subgroup.center ↥P)
    (G3 : ∀ z : ↥P, z ∈ Subgroup.center ↥P → normConj P x hx z = z)
    (G4 : ∀ (K : Type) [Field K] (lam : ↥(Subgroup.center ↥P) →* Kˣ),
      (∃ (g h : ↥P) (hc : ⁅g, h⁆ ∈ Subgroup.center ↥P), lam ⟨⁅g, h⁆, hc⟩ ≠ 1) →
      ∀ g : ↥P, (∀ (h : ↥P) (hc : ⁅g, h⁆ ∈ Subgroup.center ↥P), lam ⟨⁅g, h⁆, hc⟩ = 1) →
        g ∈ Subgroup.center ↥P)
    {j : ℕ} (hj : 2 ≤ j) (hMj : Nat.card (↥P ⧸ Subgroup.center ↥P) = p ^ j)
    (hC1 : Nat.card (fixPbar P x hx) * p ≤ Nat.card (↥P ⧸ Subgroup.center ↥P))
    (hC2 : p ≠ 5 → Nat.card (fixPbar P x hx) * p ^ 2 ≤ Nat.card (↥P ⧸ Subgroup.center ↥P))
    (hC3 : p = 3 → Nat.card (fixPbar P x hx) * 81 ≤ Nat.card (↥P ⧸ Subgroup.center ↥P)) :
    False := by
  classical
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have : Fintype ↥P := Fintype.ofFinite _
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hoddP : Odd (Nat.card ↥P) := by
    rw [hk]
    exact hodd.pow
  obtain ⟨a, ha, b, hb, hab'⟩ : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hab h
  set a' : ↥P := ⟨a, ha⟩ with ha'
  set b' : ↥P := ⟨b, hb⟩ with hb'
  set z₀ : Subgroup.center ↥P := ⟨⁅a', b'⁆, G1 a' b'⟩ with hz₀
  have hz₀ne : ((z₀ : ↥P) : MulAut V) ≠ 1 := by
    intro h
    apply hab'
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [h1, one_mul]
  obtain ⟨φ₀, χ, hφ₀, hφ₀χ, hχ1⟩ := exists_weight (K := K) P hoddP z₀ hz₀ne
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_five (K := K)
  set ℓ : ℕ := if p = 3 then 2 else 3 with hℓ
  set lamj : ℕ → (Subgroup.center ↥P →* Kˣ) := fun j => χ ^ (2 ^ j) with hlamj
  have hU0 : ∀ j, wsp K P (lamj j) ≠ ⊥ := fun j h => by
    have hmem : (frob K)^[j] φ₀ ∈ wsp K P (lamj j) := frob_iter_mem_wsp K hφ₀χ j
    rw [h] at hmem
    exact frob_iter_ne_zero K hφ₀ j ((Submodule.mem_bot K).mp hmem)
  have hxz : ∀ z : Subgroup.center ↥P,
      x * ((z : ↥P) : MulAut V) = ((z : ↥P) : MulAut V) * x := by
    intro z
    have h := congrArg (fun y : ↥P => (y : MulAut V)) (G3 (z : ↥P) z.2)
    simp only [coe_normConj] at h
    calc x * ((z : ↥P) : MulAut V) = (x * ((z : ↥P) : MulAut V) * x⁻¹) * x := by group
      _ = ((z : ↥P) : MulAut V) * x := by rw [h]
  have hxz' : ∀ z : Subgroup.center ↥P,
      x⁻¹ * ((z : ↥P) : MulAut V) = ((z : ↥P) : MulAut V) * x⁻¹ := by
    intro z
    calc x⁻¹ * ((z : ↥P) : MulAut V) = x⁻¹ * (((z : ↥P) : MulAut V) * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * ((z : ↥P) : MulAut V)) * x⁻¹ := by rw [hxz z]
      _ = ((z : ↥P) : MulAut V) * x⁻¹ := by group
  have hlam1 : ∀ j, lamj j z₀ ≠ 1 := fun j => by
    simp only [hlamj, MonoidHom.pow_apply]
    exact pow_two_pow_ne_one (χ z₀) hχ1 j
  have hΓ : (Fintype.card ↥P : K) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, cast_odd_eq_one hoddP]
    exact one_ne_zero
  have h5 : (xbar P x hx) ^ 5 = 1 := by
    ext a
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    exact xbar_pow_five hx hx5 a
  have hT5 : (actHom K x) ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  have hmain : ∀ j : ℕ, (if p = 3 then 3 else 2) ≤
      finrank K (Submodule.map (actHom K x - 1) (wsp K P (lamj j))) := by
    intro j
    refine WeilCount.weight_bound hA hp hodd hj (actP K P) (wsp K P (lamj j))
      (fun g u hu => actP_mem_wsp K g hu) (lamj j) (fun z u hu => (mem_wsp K).mp hu z) G1 ?_
      (normConj P x hx) G3 (actHom K x) (actHom K x⁻¹)
      (by rw [← map_mul, mul_inv_cancel, map_one]) (by rw [← map_mul, inv_mul_cancel, map_one])
      (fun u hu => actHom_mem_wsp K hxz hu) (fun u hu => actHom_mem_wsp K hxz' hu) ?_
      hΓ ζ hζ (xbar P x hx) (fun g => xbar_mk P x hx g) h5 hT5 hMj hC1 hC2 hC3 (hU0 j)
    · intro g hg
      exact G4 K (lamj j) ⟨a', b', G1 a' b', hlam1 j⟩ g (fun h hc => hg h)
    · intro g
      rw [actP_apply, actP_apply, coe_normConj, map_mul, map_mul]
  set N : Module.End K (Additive V →ₗ[ZMod 2] K) := actHom K x - 1 with hN
  have hUN : ∀ j, ∀ u ∈ wsp K P (lamj j), N u ∈ wsp K P (lamj j) := fun j u hu => by
    have h1 := actHom_mem_wsp K hxz hu
    have h2 : N u = actHom K x u - u := by simp [hN]
    rw [h2]
    exact Submodule.sub_mem _ h1 hu
  set μ : Fin ℓ → K := fun i => ((χ z₀ : Kˣ) : K) ^ (2 ^ (i : ℕ)) with hμ
  have hξk : (χ z₀) ^ (p ^ k) = 1 := by
    have h1 : z₀ ^ Nat.card ↥P = 1 := Subtype.ext (by simp)
    have : (χ z₀) ^ Nat.card ↥P = 1 := by rw [← map_pow, h1, map_one]
    rwa [hk] at this
  have hμinj : Function.Injective μ := by
    intro i i' h
    have h1 : (χ z₀) ^ (2 ^ (i : ℕ)) = (χ z₀) ^ (2 ^ (i' : ℕ)) :=
      Units.ext (by simpa [hμ] using h)
    exact Fin.ext (pow_two_pow_injective hp hodd (χ z₀) hχ1 hξk hℓ i i' i.2 i'.2 h1)
  have hle : ∀ i : Fin ℓ, Submodule.map N (wsp K P (lamj i)) ≤
      Module.End.eigenspace (actP K P (z₀ : ↥P)) (μ i) := by
    rintro i _ ⟨u, hu, rfl⟩
    refine Module.End.mem_eigenspace_iff.mpr ?_
    rw [(mem_wsp K).mp (hUN i u hu) z₀]
    congr 1
  have hsum := WeilJoint.sum_finrank_map_le (actP K P (z₀ : ↥P)) N
    (fun i : Fin ℓ => wsp K P (lamj i)) μ hμinj hle
  have hrank : finrank K (LinearMap.range N) ≤ 4 :=
    finrank_range_act_sub_one_le K x (m := 4) (by simpa using hxc)
  have hlow : ∑ _i : Fin ℓ, (if p = 3 then 3 else 2) ≤
      ∑ i : Fin ℓ, finrank K (Submodule.map N (wsp K P (lamj i))) :=
    Finset.sum_le_sum fun i _ => hmain i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlow
  have := hlow.trans (hsum.trans hrank)
  by_cases hp3 : p = 3
  · simp [hℓ, hp3] at this
  · simp [hℓ, hp3] at this

end Main

theorem noCaseB_holds : NoCaseB := by
  intro V _ _ hV Y hY P p hp hpodd hP hYP hPne hmin hab _
  obtain ⟨x, hx, hx5, hxc, G1, _, G3, G4, ⟨j, hj, hMj⟩, hC1, hC2, hC3⟩ :=
    nabSymplStmt_holds V hV Y P hY p hp hpodd hP hab hYP hmin hPne
  have : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (fun v =>
    Additive.toMul.injective (by rw [toMul_nsmul, toMul_zero]; exact hV _))
  exact base_false_aux (K := AlgebraicClosure (ZMod 2)) arithStmt_holds P hp hpodd hP hab x hx
    hx5 hxc G1 G3 G4 hj hMj hC1 hC2 hC3

theorem emb_four_seven_of_m4 {V : Type} [CommGroup V] [Finite V] (hM4 : SchurMultL2Two)
    (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)} (cfg : Emb4Cfg G T Y)
    {X : Subgroup (MulAut V)} (hXG : X ≤ G) (hX : ¬ 2 ∣ Nat.card X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
  emb_four_seven_of_noCaseB hM4 noCaseB_holds hV cfg hXG hX hYX

end CFSG.CGT.PushingUpLit.CGT6
