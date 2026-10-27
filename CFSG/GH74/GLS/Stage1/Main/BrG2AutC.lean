module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.CharacterTheory.Semidihedral.MatrixCoverData
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.ClassicalInvolution.TwoGroupCase.Q8

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Local
open scoped MatrixGroups

abbrev SL2F3 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

theorem m3_cube_q : ∀ x : SL2F3, (x ^ 3) ^ 4 = 1 := by decide +kernel

theorem m3_two_pow : ∀ g : SL2F3, g ^ 8 = 1 → g ^ 4 = 1 := by decide +kernel

theorem m3_mul_q : ∀ a b : SL2F3, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by decide +kernel

theorem m3_conj_q : ∀ g a : SL2F3, a ^ 4 = 1 → (g * a * g⁻¹) ^ 4 = 1 := by decide +kernel

theorem m3_centralizer_q : ∀ c : SL2F3, (∀ p : SL2F3, p ^ 4 = 1 → c * p = p * c) →
    ∀ y : SL2F3, c * y = y * c := by decide +kernel

theorem m3_center_sq : ∀ c : SL2F3, (∀ y : SL2F3, c * y = y * c) → c * c = 1 := by decide +kernel

theorem m3_card : Nat.card SL2F3 = 24 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem m3_card_q : Nat.card {g : SL2F3 // g ^ 4 = 1} = 8 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem m3_card_center : Nat.card {c : SL2F3 // ∀ y : SL2F3, c * y = y * c} = 2 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

@[expose] def m3Q : Subgroup SL2F3 where
  carrier := {g | g ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' := fun {a b} ha hb => m3_mul_q a b ha hb
  inv_mem' := fun {a} ha => by
    have h : a ^ 4 = 1 := ha
    show a⁻¹ ^ 4 = 1
    rw [inv_pow, h, inv_one]

theorem m3Q_normal : m3Q.Normal := ⟨fun a ha g => m3_conj_q g a ha⟩

theorem card_m3Q : Nat.card m3Q = 8 := m3_card_q

theorem m3_index_q : m3Q.index = 3 := by
  have h := Subgroup.card_mul_index m3Q
  rw [card_m3Q, m3_card] at h
  omega

theorem m3Q_equiv_quaternion : Nonempty (QuaternionGroup 2 ≃* m3Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 m3Q := IsPGroup.of_card (n := 3) (by rw [card_m3Q]; norm_num)
  let P : Sylow 2 SL2F3 := hp.toSylow (by rw [m3_index_q]; norm_num)
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]; exact ⟨1, rfl⟩
  obtain ⟨n, hn3, ⟨e⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion (ZMod 3) hodd P
  have hcard : Nat.card (P : Subgroup SL2F3) = 8 := card_m3Q
  have hcard' : Nat.card (QuaternionGroup (2 ^ (n - 2))) = 8 := by
    rw [← Nat.card_congr e.toEquiv, hcard]
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hcard'
  have hn : n - 2 = 1 := by
    have h2 : 2 ^ (n - 2) = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2
  rw [hn] at e
  exact ⟨e.symm⟩

@[expose] def sl2EquivOfRingEquiv {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F' where
  toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_mul' := map_mul _

theorem nonempty_equiv_m3 {Q : Type} [Group Q] {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3)
    (e : Q ≃* StatedSL 2 F) : Nonempty (Q ≃* SL2F3) := by
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  exact ⟨(e.trans (specialLinearGroupEquivStatedSL 2 F).symm).trans
    (sl2EquivOfRingEquiv (FiniteField.ringEquivOfCardEq hF))⟩

theorem factorization_24 : (24 : ℕ).factorization 2 = 3 := by
  have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  simp

theorem sl2_three_sylow {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F]
    (h3 : Nat.card F = 3) (e : Q ≃* StatedSL 2 F) {P : Subgroup Q}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤) : P.Normal ∧ IVK.IsQuaternionTwoGroup ↥P 3 := by
  obtain ⟨e₀⟩ := nonempty_equiv_m3 h3 e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₀ : Subgroup Q := m3Q.comap e₀.toMonoidHom with hQ₀
  have hQ₀map : Q₀ = m3Q.map e₀.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm e₀ m3Q
  have hQcard : Nat.card Q = 24 := by rw [Nat.card_congr e₀.toEquiv, m3_card]
  have hPcard : Nat.card P = 8 := by
    have h1 := hP.card_eq
    rw [Subgroup.card_top, hQcard, factorization_24] at h1
    rw [h1]; norm_num
  have hQ₀card : Nat.card Q₀ = 8 := by
    rw [hQ₀map, Subgroup.card_map_of_injective e₀.symm.injective, card_m3Q]
  have hPle : P ≤ Q₀ := by
    intro x hx
    have hp2 := hP.isPGroup
    obtain ⟨k, hk⟩ := hp2 ⟨x, hx⟩
    have hxk : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hod : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hod
    have hod24 : orderOf x ∣ 24 := hQcard ▸ orderOf_dvd_natCard x
    have hj3 : j ≤ 3 := by
      rw [hj] at hod24
      by_contra hj4
      have h16 : 2 ^ 4 ∣ 24 := (pow_dvd_pow 2 (by omega : 4 ≤ j)).trans hod24
      norm_num at h16
    have hx8 : x ^ 8 = 1 := by
      have : orderOf x ∣ 8 := by
        rw [hj]; exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
      exact orderOf_dvd_iff_pow_eq_one.1 this
    show (e₀ x) ^ 4 = 1
    exact m3_two_pow _ (by rw [← map_pow, hx8, map_one])
  have hPQ : P = Q₀ := Subgroup.eq_of_le_of_card_ge hPle (by rw [hPcard, hQ₀card])
  refine ⟨?_, ?_⟩
  · rw [hPQ]; exact m3Q_normal.comap e₀.toMonoidHom
  · refine ⟨le_refl 3, ?_⟩
    obtain ⟨eQ⟩ := m3Q_equiv_quaternion
    have e1 : ↥P ≃* ↥(m3Q.map e₀.symm.toMonoidHom) :=
      MulEquiv.subgroupCongr (hPQ.trans hQ₀map)
    have e2 : ↥(m3Q.map e₀.symm.toMonoidHom) ≃* ↥m3Q :=
      (e₀.symm.subgroupMap m3Q).symm
    exact ⟨((e1.trans e2).trans eQ.symm : ↥P ≃* QuaternionGroup 2)⟩

theorem gl3_central : ∀ G : GL (Fin 2) (ZMod 3),
    (∀ X : SL2F3, (G : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (X : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (X : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (G : Matrix (Fin 2) (Fin 2) (ZMod 3))) →
    ∀ H : GL (Fin 2) (ZMod 3), G * H = H * G := by decide +kernel

@[expose] def resQ : MulAut SL2F3 →* MulAut ↥m3Q where
  toFun φ :=
    { toFun := fun q => ⟨φ q, by
        have h : (q : SL2F3) ^ 4 = 1 := q.2
        show φ q ^ 4 = 1
        rw [← map_pow, h, map_one]⟩
      invFun := fun q => ⟨φ.symm q, by
        have h : (q : SL2F3) ^ 4 = 1 := q.2
        show φ.symm q ^ 4 = 1
        rw [← map_pow, h, map_one]⟩
      left_inv := fun q => by ext; simp
      right_inv := fun q => by ext; simp
      map_mul' := fun a b => by ext; simp }
  map_one' := by ext; rfl
  map_mul' := fun φ ψ => by ext; rfl

theorem resQ_injective : Function.Injective resQ := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have hq : ∀ x : SL2F3, x ^ 4 = 1 → φ x = x := by
    intro x hx
    have := congrArg (fun ψ : MulAut ↥m3Q => ((ψ ⟨x, hx⟩ : ↥m3Q) : SL2F3)) hφ
    simpa [resQ] using this
  apply MulEquiv.ext
  intro x
  rw [MulAut.one_apply]
  set z : SL2F3 := x⁻¹ * φ x with hz
  have hzc : ∀ y : SL2F3, z * y = y * z := by
    apply m3_centralizer_q z
    intro p hp
    have h1 : φ (x * p * x⁻¹) = x * p * x⁻¹ := hq _ (m3_conj_q x p hp)
    rw [map_mul, map_mul, map_inv, hq p hp] at h1
    calc z * p = x⁻¹ * φ x * p := rfl
      _ = x⁻¹ * (φ x * p * (φ x)⁻¹) * φ x := by group
      _ = x⁻¹ * (x * p * x⁻¹) * φ x := by rw [h1]
      _ = p * (x⁻¹ * φ x) := by group
  have hz2 : z * z = 1 := m3_center_sq z hzc
  have hx3 : φ (x ^ 3) = x ^ 3 := hq _ (m3_cube_q x)
  have hφx : φ x = x * z := by rw [hz]; group
  have h3z : φ (x ^ 3) = x ^ 3 * z := by
    rw [map_pow, hφx]
    have hcomm : Commute x z := (hzc x).symm
    rw [hcomm.mul_pow]
    have : z ^ 3 = z := by rw [pow_succ, pow_two, hz2, one_mul]
    rw [this]
  have hz1 : z = 1 := by
    have h := hx3.symm.trans h3z
    have : x ^ 3 * z = x ^ 3 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  rw [hφx, hz1, mul_one]

theorem card_mulAut_m3_le : Nat.card (MulAut SL2F3) ≤ 24 := by
  obtain ⟨eQ⟩ := m3Q_equiv_quaternion
  have h1 : Nat.card (MulAut SL2F3) ≤ Nat.card (MulAut ↥m3Q) :=
    Nat.card_le_card_of_injective _ resQ_injective
  have h2 : Nat.card (MulAut ↥m3Q) = Nat.card (QuaternionGroup 2 ≃* QuaternionGroup 2) :=
    (Nat.card_congr (MulAut.congr eQ).toEquiv).symm
  exact h1.trans (h2 ▸ CFSG.ClassicalInvolution.q8_natCard_mulEquiv_le)

theorem slConjugation_center_eq_one {G : GL (Fin 2) (ZMod 3)}
    (hG : G ∈ Subgroup.center (GL (Fin 2) (ZMod 3))) :
    CFSG.Semidihedral.MatrixCoverData.slConjugation (ZMod 3) G = 1 := by
  apply MulEquiv.ext
  intro X
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.Semidihedral.MatrixCoverData.slConjugation_toGL, MulAut.one_apply]
  have h := Subgroup.mem_center_iff.1 hG (Matrix.SpecialLinearGroup.toGL X)
  rw [← h]
  group

@[expose] noncomputable def slConjTheta3 : CFSG.GorensteinWalter.PGL2 (ZMod 3) →* MulAut SL2F3 :=
  Matrix.ProjGenLinGroup.lift (CFSG.Semidihedral.MatrixCoverData.slConjugation (ZMod 3))
    (MonoidHom.ext fun u => slConjugation_center_eq_one (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩))

theorem slConjTheta3_mk (G : GL (Fin 2) (ZMod 3)) :
    slConjTheta3 (Matrix.ProjGenLinGroup.mk G) = CFSG.Semidihedral.MatrixCoverData.slConjugation (ZMod 3) G :=
  rfl

theorem slConjTheta3_injective : Function.Injective slConjTheta3 := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using Matrix.ProjGenLinGroup.induction_on with
  | mk G =>
    rw [slConjTheta3_mk] at hx
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
    refine fun H => (gl3_central G (fun X => ?_) H).symm
    have h1 := congrArg (fun α : MulAut SL2F3 => (α X : Matrix (Fin 2) (Fin 2) (ZMod 3))) hx
    simp only [MulAut.one_apply, CFSG.Semidihedral.MatrixCoverData.slConjugation_matrix] at h1
    calc (G : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (X : Matrix (Fin 2) (Fin 2) (ZMod 3))
        = ((G : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (X : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
            ((G⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))) *
            (G : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
          rw [mul_assoc _ _ (G : Matrix (Fin 2) (Fin 2) (ZMod 3)), mul_assoc,
            ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      _ = (X : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (G : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by rw [h1]

theorem slConjTheta3_bijective : Function.Bijective slConjTheta3 :=
  slConjTheta3_injective.bijective_of_nat_card_le (by
    rw [CFSG.GorensteinWalter.nat_card_pgl2_zmod3]; exact card_mulAut_m3_le)

@[expose] noncomputable def mulAutM3Equiv : CFSG.GorensteinWalter.PGL2 (ZMod 3) ≃* MulAut SL2F3 :=
  MulEquiv.ofBijective slConjTheta3 slConjTheta3_bijective

theorem exists_slConjugation_of_mulAut (α : MulAut SL2F3) :
    ∃ G : GL (Fin 2) (ZMod 3), α = CFSG.Semidihedral.MatrixCoverData.slConjugation (ZMod 3) G := by
  obtain ⟨x, hx⟩ := slConjTheta3_bijective.2 α
  induction x using Matrix.ProjGenLinGroup.induction_on with
  | mk G => exact ⟨G, hx.symm⟩

section Act

variable {Y : Type} [Group Y]

@[expose] def actOnK (K : Subgroup Y) (s : Y) (hs : s ∈ normalizer (K : Set Y)) : MulAut ↥K where
  toFun k := ⟨s * k * s⁻¹, (mem_normalizer_iff.mp hs k).mp k.2⟩
  invFun k := ⟨s⁻¹ * k * s, by
    have := (mem_normalizer_iff.mp ((normalizer (K : Set Y)).inv_mem hs) k).mp k.2
    simpa using this⟩
  left_inv k := by ext; simp [mul_assoc]
  right_inv k := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[expose] def actOnKHom (K B : Subgroup Y) (hB : B ≤ normalizer (K : Set Y)) : ↥B →* MulAut ↥K where
  toFun b := actOnK K b (hB b.2)
  map_one' := by ext; simp [actOnK]
  map_mul' a b := by ext; simp [actOnK, mul_assoc]

theorem actOnKHom_apply (K B : Subgroup Y) (hB : B ≤ normalizer (K : Set Y)) (b : ↥B) (k : ↥K) :
    ((actOnKHom K B hB b k : ↥K) : Y) = b * k * (b : Y)⁻¹ := rfl

theorem actOnKHom_ker (K B : Subgroup Y) (hB : B ≤ normalizer (K : Set Y)) :
    (actOnKHom K B hB).ker = (centralizer (K : Set Y)).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : Y)) h
    simp only [actOnKHom_apply, MulAut.one_apply] at this
    calc k * (b : Y) = (b * k * (b : Y)⁻¹) * b := by rw [this]
      _ = (b : Y) * k := by group
  · intro h
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    rw [actOnKHom_apply, MulAut.one_apply]
    have := h (k : Y) k.2
    calc (b : Y) * k * (b : Y)⁻¹ = (k * (b : Y)) * (b : Y)⁻¹ := by rw [this]
      _ = k := by group

end Act

theorem card_mulAut_of_equiv_m3 {Q : Type} [Group Q] (eM : Q ≃* SL2F3) : Nat.card (MulAut Q) = 24 := by
  have h1 : Nat.card (MulAut Q) = Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod 3)) :=
    Nat.card_congr (((MulAut.congr eM).trans mulAutM3Equiv.symm)).toEquiv
  rw [h1, CFSG.GorensteinWalter.nat_card_pgl2_zmod3]

theorem isSolvable_m3 : Group.IsSolvable SL2F3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 2 m3Q := IsPGroup.of_card (n := 3) (by rw [card_m3Q]; norm_num)
  have : Group.IsNilpotent ↥m3Q := hp.isNilpotent
  have := m3Q_normal
  have : IsCyclic (SL2F3 ⧸ m3Q) := isCyclic_of_prime_card (p := 3) (by
    have h := m3_index_q
    rw [Subgroup.index] at h
    exact h)
  exact Group.isSolvable_of_subgroup_quotient m3Q

theorem isSolvable_of_natCard_le_two {G : Type} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    Group.IsSolvable G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2) with h1 | h2
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card (p := 2) h2
    infer_instance

theorem m3_two_elt {g : SL2F3} (h : ∃ m : ℕ, g ^ (2 ^ m) = 1) : g ^ 4 = 1 := by
  obtain ⟨m, hm⟩ := h
  have hod : orderOf g ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hod
  have hod24 : orderOf g ∣ 24 := m3_card ▸ orderOf_dvd_natCard g
  have hj3 : j ≤ 3 := by
    rw [hj] at hod24
    by_contra hj4
    have h16 : 2 ^ 4 ∣ 24 := (pow_dvd_pow 2 (by omega : 4 ≤ j)).trans hod24
    norm_num at h16
  have hg8 : g ^ 8 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hj]; exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3))
  exact m3_two_pow g hg8

theorem m3_three_elt {g : SL2F3} (h : ∃ m : ℕ, g ^ (3 ^ m) = 1) : g ^ 3 = 1 := by
  obtain ⟨m, hm⟩ := h
  have hod : orderOf g ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hod
  have hod24 : orderOf g ∣ 24 := m3_card ▸ orderOf_dvd_natCard g
  have hj1 : j ≤ 1 := by
    rw [hj] at hod24
    by_contra hj2
    have h9 : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 (by omega : 2 ≤ j)).trans hod24
    norm_num at h9
  exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hj]; simpa using (pow_dvd_pow 3 hj1))

theorem m3_third_conj : ∀ y : SL2F3, y ≠ 1 → y ^ 3 = 1 → ∃ g : SL2F3, (y * (g * y * g⁻¹)) ^ 3 ≠ 1 := by
  decide +kernel

section Over

variable {D : Type} [Group D] [Finite D] {K : Subgroup D}

omit [Finite D] in
theorem pow_eq_one_iff_eM (eM : ↥K ≃* SL2F3) {x : D} (hx : x ∈ K) (n : ℕ) :
    x ^ n = 1 ↔ (eM ⟨x, hx⟩) ^ n = 1 := by
  rw [← map_pow, MulEquiv.map_eq_one_iff]
  constructor
  · intro h; exact Subtype.ext (by simpa using h)
  · intro h; simpa using congrArg Subtype.val h

omit [Finite D] in
theorem two_elt_q (eM : ↥K ≃* SL2F3) {x : D} (hx : x ∈ K) (h : ∃ m : ℕ, x ^ (2 ^ m) = 1) :
    x ^ 4 = 1 := by
  obtain ⟨m, hm⟩ := h
  rw [pow_eq_one_iff_eM eM hx]
  exact m3_two_elt ⟨m, (pow_eq_one_iff_eM eM hx _).1 hm⟩

omit [Finite D] in
theorem three_elt_pow (eM : ↥K ≃* SL2F3) {x : D} (hx : x ∈ K) (h : ∃ m : ℕ, x ^ (3 ^ m) = 1) :
    x ^ 3 = 1 := by
  obtain ⟨m, hm⟩ := h
  rw [pow_eq_one_iff_eM eM hx]
  exact m3_three_elt ⟨m, (pow_eq_one_iff_eM eM hx _).1 hm⟩

theorem three_elt_mem_K (hK : K.Normal) (hidx : K.index ≤ 2) {x : D}
    (h : ∃ m : ℕ, x ^ (3 ^ m) = 1) : x ∈ K := by
  obtain ⟨m, hm⟩ := h
  have hq : (QuotientGroup.mk x : D ⧸ K) ^ (3 ^ m) = 1 := by
    rw [← QuotientGroup.mk_pow, hm]; rfl
  have hod : orderOf (QuotientGroup.mk x : D ⧸ K) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hq
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hod
  have hle : orderOf (QuotientGroup.mk x : D ⧸ K) ≤ 2 := by
    have h1 : orderOf (QuotientGroup.mk x : D ⧸ K) ∣ Nat.card (D ⧸ K) := orderOf_dvd_natCard _
    have h2 : Nat.card (D ⧸ K) = K.index := rfl
    exact (Nat.le_of_dvd Nat.card_pos h1).trans (h2 ▸ hidx)
  have hj0 : j = 0 := by
    by_contra hne
    have : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hne)
    omega
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact (QuotientGroup.eq_one_iff x).1 hj

theorem gl3_inner : ∀ G : GL (Fin 2) (ZMod 3),
    (∀ y : SL2F3, ((G : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((G⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((y⁻¹ : SL2F3) : Matrix (Fin 2) (Fin 2) (ZMod 3))) ^ 4 = 1) →
    ∃ s : SL2F3, ∀ y : SL2F3, (G : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((G⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((s⁻¹ : SL2F3) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by decide +kernel

omit [Finite D] in
theorem mem_K_of_comm_q (hK : K.Normal) (eM : ↥K ≃* SL2F3)
    (hC : ∀ d : D, (∀ k ∈ K, k * d = d * k) → d ∈ K) (x : D)
    (hx : ∀ k ∈ K, (x * k * x⁻¹ * k⁻¹) ^ 4 = 1) : x ∈ K := by
  have := hK
  set α : MulAut SL2F3 := MulAut.congr eM (MulAut.conjNormal (H := K) x) with hα
  obtain ⟨G, hG⟩ := exists_slConjugation_of_mulAut α
  have hαk : ∀ k : ↥K, α (eM k) = eM (MulAut.conjNormal (H := K) x k) := by
    intro k
    rw [hα, MulAut.congr_apply]
    simp
  have hin : ∀ y : SL2F3, ((G : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((G⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((y⁻¹ : SL2F3) : Matrix (Fin 2) (Fin 2) (ZMod 3))) ^ 4 = 1 := by
    intro y
    obtain ⟨k, rfl⟩ := eM.surjective y
    have h1 : (α (eM k) * (eM k)⁻¹) ^ 4 = 1 := by
      rw [hαk, ← map_inv, ← map_mul, ← map_pow]
      have : (MulAut.conjNormal (H := K) x k * k⁻¹) ^ 4 = 1 := by
        apply Subtype.ext
        simpa [MulAut.conjNormal_apply] using hx k k.2
      rw [this, map_one]
    rw [hG] at h1
    have h2 := congrArg (fun z : SL2F3 => (z : Matrix (Fin 2) (Fin 2) (ZMod 3))) h1
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one,
      CFSG.Semidihedral.MatrixCoverData.slConjugation_matrix] using h2
  obtain ⟨s, hs⟩ := gl3_inner G hin
  have hconj : ∀ y : SL2F3, α y = s * y * s⁻¹ := by
    intro y
    rw [hG]
    apply Subtype.ext
    rw [CFSG.Semidihedral.MatrixCoverData.slConjugation_matrix, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    exact hs y
  set s' : ↥K := eM.symm s with hs'
  have hxk : ∀ k : ↥K, x * (k : D) * x⁻¹ = (s' : D) * k * (s' : D)⁻¹ := by
    intro k
    have h1 : eM (MulAut.conjNormal (H := K) x k) = eM (s' * k * s'⁻¹) := by
      rw [← hαk, hconj, map_mul, map_mul, map_inv, hs']
      simp
    have := congrArg Subtype.val (eM.injective h1)
    simpa [MulAut.conjNormal_apply] using this
  have hd : (s' : D)⁻¹ * x ∈ K := by
    apply hC
    intro k hk
    have := hxk ⟨k, hk⟩
    calc k * ((s' : D)⁻¹ * x) = (s' : D)⁻¹ * ((s' : D) * k * (s' : D)⁻¹) * x := by group
      _ = (s' : D)⁻¹ * (x * k * x⁻¹) * x := by rw [← this]
      _ = (s' : D)⁻¹ * x * k := by group
  have : x = (s' : D) * ((s' : D)⁻¹ * x) := by group
  rw [this]
  exact K.mul_mem s'.2 hd

omit [Finite D] in
theorem ker_conjNormal_mem_K (hK : K.Normal) (hC : ∀ d : D, (∀ k ∈ K, k * d = d * k) → d ∈ K)
    {d : D} (hd : d ∈ (MulAut.conjNormal : D →* MulAut ↥K).ker) : d ∈ K ∧ ∀ k ∈ K, k * d = d * k := by
  have hcomm : ∀ k ∈ K, k * d = d * k := by
    intro k hk
    have h := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : D)) (MonoidHom.mem_ker.1 hd)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc k * d = (d * k * d⁻¹) * d := by rw [h]
      _ = d * k := by group
  exact ⟨hC d hcomm, hcomm⟩

theorem card_D_le (hK : K.Normal) (eM : ↥K ≃* SL2F3)
    (hC : ∀ d : D, (∀ k ∈ K, k * d = d * k) → d ∈ K) : Nat.card D ≤ 48 := by
  have := hK
  set ρ : D →* MulAut ↥K := MulAut.conjNormal with hρ
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have hrange : Nat.card ρ.range ≤ 24 :=
    (card_mulAut_of_equiv_m3 eM) ▸ Subgroup.card_le_card_group _
  have hker : Nat.card ρ.ker ≤ 2 := by
    let f : ρ.ker → {c : SL2F3 // ∀ y : SL2F3, c * y = y * c} := fun d =>
      ⟨eM ⟨d, (ker_conjNormal_mem_K hK hC d.2).1⟩, by
        intro y
        obtain ⟨k, rfl⟩ := eM.surjective y
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext ((ker_conjNormal_mem_K hK hC d.2).2 k k.2).symm⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 := eM.injective (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg (fun z : ↥K => (z : D)) h1)
    have := Nat.card_le_card_of_injective f hinj
    rwa [m3_card_center] at this
  calc Nat.card D = Nat.card ρ.ker * Nat.card ρ.range := h1.symm
    _ ≤ 2 * 24 := Nat.mul_le_mul hker hrange
    _ = 48 := by norm_num

end Over

theorem inducedPGL2_sl2_three {Y : Type} [Group Y] [Finite Y] {K T : Subgroup Y} {F : Type} [Field F]
    [Finite F] (h3 : Nat.card F = 3) (e : ↥K ≃* StatedSL 2 F) (hTN : T ≤ normalizer (K : Set Y))
    {u : Y} (huT : u ∈ T) (hnon : ∀ k ∈ K, ∃ x ∈ K, u * x * u⁻¹ ≠ k * x * k⁻¹) :
    InducedPGL2 K T 3 := by
  obtain ⟨eM⟩ := nonempty_equiv_m3 h3 e
  set B : Subgroup Y := K ⊔ T with hB
  have hBN : B ≤ normalizer (K : Set Y) := sup_le Subgroup.le_normalizer hTN
  have hKB : K ≤ B := le_sup_left
  set Ψ := actOnKHom K B hBN with hΨ
  have hAcard : Nat.card (MulAut ↥K) = 24 := card_mulAut_of_equiv_m3 eM
  set Inn : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range with hInn
  have hInnR : Inn ≤ Ψ.range := by
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨(k : Y), hKB k.2⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp [hΨ, actOnKHom_apply, MulAut.conj_apply]
  have hKcard : Nat.card ↥K = 24 := by rw [Nat.card_congr eM.toEquiv, m3_card]
  have hInncard : Nat.card Inn = 12 := by
    have h1 : Nat.card (MulAut.conj : ↥K →* MulAut ↥K).ker * Nat.card Inn = Nat.card ↥K :=
      Subgroup.card_ker_mul_card_range (MulAut.conj : ↥K →* MulAut ↥K)
    have hker : (MulAut.conj : ↥K →* MulAut ↥K).ker = Subgroup.center ↥K := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
      constructor
      · intro h g
        have := congrArg (fun α : MulAut ↥K => α g) h
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * c = (c * g * c⁻¹) * c := by rw [this]
          _ = c * g := by group
      · intro h
        apply MulEquiv.ext
        intro g
        rw [MulAut.conj_apply, MulAut.one_apply]
        have := h g
        calc c * g * c⁻¹ = (g * c) * c⁻¹ := by rw [this]
          _ = g := by group
    have hcen : Nat.card (Subgroup.center ↥K) = 2 := by
      rw [← m3_card_center]
      refine Nat.card_congr (Equiv.subtypeEquiv eM.toEquiv (fun c => ?_))
      rw [Subgroup.mem_center_iff]
      constructor
      · intro h y
        obtain ⟨g, rfl⟩ := eM.surjective y
        show eM c * eM g = eM g * eM c
        rw [← map_mul, ← map_mul, h g]
      · intro h g
        apply eM.injective
        rw [map_mul, map_mul]
        exact (h (eM g)).symm
    rw [hker, hcen, hKcard] at h1
    omega
  have huB : u ∈ B := (le_sup_right : T ≤ K ⊔ T) huT
  have hnotIn : Ψ ⟨u, huB⟩ ∉ Inn := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hxK, hx⟩ := hnon k k.2
    apply hx
    have := congrArg (fun α : MulAut ↥K => ((α ⟨x, hxK⟩ : ↥K) : Y)) hk
    simp only [MulAut.conj_apply, hΨ, actOnKHom_apply] at this
    exact this.symm
  have hRcard : Nat.card Ψ.range = 24 := by
    have hle : Nat.card Ψ.range ≤ 24 := hAcard ▸ Subgroup.card_le_card_group _
    have hdvd : Nat.card Inn ∣ Nat.card Ψ.range := Subgroup.card_dvd_of_le hInnR
    have hne : Nat.card Inn ≠ Nat.card Ψ.range := by
      intro h
      have hEq : Inn = Ψ.range := Subgroup.eq_of_le_of_card_ge hInnR (by omega)
      exact hnotIn (hEq ▸ ⟨⟨u, huB⟩, rfl⟩)
    obtain ⟨m, hm⟩ := hdvd
    rw [hInncard] at hm hne
    have hpos : 0 < Nat.card Ψ.range := Nat.card_pos
    have key : ∀ N m : ℕ, 0 < N → N ≤ 24 → 12 ≠ N → N = 12 * m → N = 24 := by
      intro N m h0 h1 h2 h3
      omega
    exact key _ m hpos hle hne hm
  have hsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (by rw [hRcard, hAcard])
  have hCn : ((centralizer (K : Set Y)).subgroupOf B).Normal := by
    rw [← actOnKHom_ker K B hBN]; exact MonoidHom.normal_ker _
  refine ⟨hCn, ZMod 3, inferInstance, inferInstance, by rw [Nat.card_zmod], ?_⟩
  have e1 : ↥B ⧸ (centralizer (K : Set Y)).subgroupOf B ≃* MulAut ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (actOnKHom_ker K B hBN).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hsurj)
  exact ⟨e1.trans (((MulAut.congr eM).trans mulAutM3Equiv.symm))⟩

theorem sl2_three_overgroup {D : Type} [Group D] [Finite D] {K : Subgroup D} (hK : K.Normal)
    {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) (e : ↥K ≃* StatedSL 2 F)
    (hC : ∀ d : D, (∀ k ∈ K, k * d = d * k) → d ∈ K) :
    Group.IsSolvable D ∧ ∃ P : Subgroup D, P ≤ K ∧ P.Normal ∧ IVK.IsQuaternionTwoGroup ↥P 3 ∧
      fittingSubgroup D = P ∧ ∀ x ∈ K, (∃ m : ℕ, x ^ (2 ^ m) = 1) → x ∈ P := by
  obtain ⟨eM⟩ := nonempty_equiv_m3 h3 e
  have := hK
  have hKcard : Nat.card K = 24 := by rw [Nat.card_congr eM.toEquiv, m3_card]
  have hD48 : Nat.card D ≤ 48 := card_D_le hK eM hC
  have hmul := Subgroup.card_mul_index K
  rw [hKcard] at hmul
  have hidx : K.index ≤ 2 := by omega
  have hDcard : Nat.card D = 24 ∨ Nat.card D = 48 := by
    have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have : K.index = 1 ∨ K.index = 2 := by omega
    omega
  let Pk : Subgroup ↥K := m3Q.comap eM.toMonoidHom
  let P : Subgroup D := Pk.map K.subtype
  have hPmem : ∀ x : D, x ∈ P ↔ x ∈ K ∧ x ^ 4 = 1 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have h1 : (eM y) ^ 4 = 1 := hy
      rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
      simpa using congrArg Subtype.val h1
    · rintro ⟨hx, hx4⟩
      exact ⟨⟨x, hx⟩, (pow_eq_one_iff_eM eM hx 4).1 hx4, rfl⟩
  have hPK : P ≤ K := fun x hx => ((hPmem x).1 hx).1
  have hPn : P.Normal := by
    refine ⟨fun x hx d => (hPmem _).2 ⟨hK.conj_mem x ((hPmem x).1 hx).1 d, ?_⟩⟩
    rw [conj_pow, ((hPmem x).1 hx).2]
    group
  have hP2 : IsPGroup 2 ↥P := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    simpa using ((hPmem g.1).1 g.2).2
  have hPnil : Group.IsNilpotent ↥P := hP2.isNilpotent
  have h2elt : ∀ x ∈ K, (∃ m : ℕ, x ^ (2 ^ m) = 1) → x ∈ P :=
    fun x hx h => (hPmem x).2 ⟨hx, two_elt_q eM hx h⟩
  have hsolM : Group.IsSolvable SL2F3 := isSolvable_m3
  have hsolK : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective (f := eM.toMonoidHom) eM.injective
  have hsolq : Group.IsSolvable (D ⧸ K) := isSolvable_of_natCard_le_two (by
    have : Nat.card (D ⧸ K) = K.index := rfl
    omega)
  have hsolD : Group.IsSolvable D := Group.isSolvable_of_subgroup_quotient K
  refine ⟨hsolD, P, hPK, hPn, ?_, ?_, h2elt⟩
  · refine ⟨le_refl 3, ?_⟩
    obtain ⟨eQ⟩ := m3Q_equiv_quaternion
    have e1 : ↥P ≃* ↥Pk := (Subgroup.equivMapOfInjective Pk K.subtype K.subtype_injective).symm
    have hPk : Pk = m3Q.map eM.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm eM m3Q
    have e2 : ↥Pk ≃* ↥m3Q := (MulEquiv.subgroupCongr hPk).trans (eM.symm.subgroupMap m3Q).symm
    exact ⟨((e1.trans e2).trans eQ.symm : ↥P ≃* QuaternionGroup 2)⟩
  ·
    apply le_antisymm
    · rw [CFSG.fitting_eq_sup_pCore]
      refine iSup_le fun p => ?_
      have hpf := Nat.mem_primeFactors.1 p.1.2
      have hp48 : p.1.1 ∣ 48 := by
        rcases hDcard with h | h
        · exact hpf.2.1.trans (h ▸ (by norm_num : 24 ∣ 48))
        · exact h ▸ hpf.2.1
      have hp23 : p.1.1 = 2 ∨ p.1.1 = 3 := by
        have : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
        rw [this] at hp48
        rcases (Nat.Prime.dvd_mul hpf.1).1 hp48 with h | h
        · left
          exact (Nat.prime_dvd_prime_iff_eq hpf.1 Nat.prime_two).1 (hpf.1.dvd_of_dvd_pow h)
        · right
          exact (Nat.prime_dvd_prime_iff_eq hpf.1 Nat.prime_three).1 h
      rcases hp23 with h2 | h3'
      · rw [h2]
        intro x hx
        have hpc := CFSG.pCore_isPGroup (p := 2) (G := D)
        have hx2 : ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
          obtain ⟨m, hm⟩ := hpc ⟨x, hx⟩
          exact ⟨m, by simpa using congrArg Subtype.val hm⟩
        have hxK : x ∈ K := by
          apply mem_K_of_comm_q hK eM hC x
          intro k hk
          have hz : x * k * x⁻¹ * k⁻¹ ∈ CFSG.pCore 2 D := by
            have := (CFSG.pCore_normal (p := 2) (G := D)).conj_mem x⁻¹ ((CFSG.pCore 2 D).inv_mem hx) k
            have h' := (CFSG.pCore 2 D).mul_mem hx this
            simpa [mul_assoc] using h'
          have hzK : x * k * x⁻¹ * k⁻¹ ∈ K :=
            K.mul_mem (hK.conj_mem k hk x |> fun h => by simpa using h) (K.inv_mem hk)
          obtain ⟨m, hm⟩ := hpc ⟨_, hz⟩
          exact two_elt_q eM hzK ⟨m, by simpa using congrArg Subtype.val hm⟩
        exact h2elt x hxK hx2
      · rw [h3']
        intro x hx
        have hpc := CFSG.pCore_isPGroup (p := 3) (G := D)
        have hx3 : ∃ m : ℕ, x ^ (3 ^ m) = 1 := by
          obtain ⟨m, hm⟩ := hpc ⟨x, hx⟩
          exact ⟨m, by simpa using congrArg Subtype.val hm⟩
        have hxK : x ∈ K := three_elt_mem_K hK hidx hx3
        have hx1 : x = 1 := by
          by_contra hne
          have hy3 : (eM ⟨x, hxK⟩) ^ 3 = 1 :=
            (pow_eq_one_iff_eM eM hxK 3).1 (three_elt_pow eM hxK hx3)
          have hy1 : eM ⟨x, hxK⟩ ≠ 1 := by
            intro h
            apply hne
            have h1 := eM.injective (h.trans (map_one eM).symm)
            simpa using congrArg Subtype.val h1
          obtain ⟨g, hg⟩ := m3_third_conj _ hy1 hy3
          set g' : ↥K := eM.symm g with hg'
          have hxx : x * ((g' : D) * x * (g' : D)⁻¹) ∈ CFSG.pCore 3 D :=
            (CFSG.pCore 3 D).mul_mem hx ((CFSG.pCore_normal (p := 3) (G := D)).conj_mem x hx (g' : D))
          have hxxK : x * ((g' : D) * x * (g' : D)⁻¹) ∈ K :=
            K.mul_mem hxK (hK.conj_mem x hxK g')
          obtain ⟨m, hm⟩ := hpc ⟨_, hxx⟩
          have hz3 : (eM ⟨x * ((g' : D) * x * (g' : D)⁻¹), hxxK⟩) ^ 3 = 1 :=
            (pow_eq_one_iff_eM eM hxxK 3).1
              (three_elt_pow eM hxxK ⟨m, by simpa using congrArg Subtype.val hm⟩)
          apply hg
          have hel : (⟨x * ((g' : D) * x * (g' : D)⁻¹), hxxK⟩ : ↥K) =
              ⟨x, hxK⟩ * (g' * ⟨x, hxK⟩ * g'⁻¹) := rfl
          rw [hel, map_mul, map_mul, map_mul, map_inv, hg', MulEquiv.apply_symm_apply] at hz3
          exact hz3
        rw [hx1]
        exact P.one_mem
    · exact le_sSup ⟨hPn, hPnil⟩
  

end CFSG.GH74.GLS.Stage1.Main
