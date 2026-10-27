module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMonDefs
public import CFSG.GF2Type.Smith1979.CaseI25U43
public import CFSG.GF2Type.Smith1979.IdxFourIdentU43
public import CFSG.GF2Type.Smith1979.IdxFourIdentFrattini

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

theorem levMat_pow_three : ∀ k : CFSG.GF2Type.Smith1979.Case25.U43Weights.Gen,
    CFSG.GF2Type.Smith1979.Case25.U43Weights.levMat k ^ 3 = 1 := by decide +kernel

open CFSG.GF2Type.Smith1979.GammaU
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six
open CFSG.GF2Type.Smith1979.Case25.U43Weights

structure Ctx where
  X : Subgroup G12
  E : Subgroup G12
  hXg : X ≤ gammaU
  hEX : E ≤ X
  hEnorm : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E
  hX4 : Nat.card X = 4 * Nat.card E
  hXcard : Nat.card X = 39191040
  π : E →* X₀
  hπs : Function.Surjective π
  hπk : π.ker = Subgroup.center E
  hZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers theta0e

theorem card_comap_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup H) :
    Nat.card (N.comap f) = Nat.card f.ker * Nat.card N := by
  have h1 := Subgroup.card_mul_index (N.comap f)
  rw [Subgroup.index_comap_of_surjective _ hf] at h1
  have h2 := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h2
  have h3 := Subgroup.card_mul_index N
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, ← h2, ← h3]
  ring

namespace Ctx

variable (C : Ctx)

theorem card_E : Nat.card C.E = 9797760 := by
  have h := C.hX4
  rw [C.hXcard] at h
  omega

theorem theta0e_pow_three : theta0e ^ 3 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  show theta0e (theta0e (theta0e x)) = x
  simp only [theta0e_apply]
  exact theta0_theta0_theta0 x

theorem theta0e_ne_one : theta0e ≠ 1 := by
  intro h
  have h1 := LinearEquiv.congr_fun h (Pi.single (lo 0) 1)
  have h2 := congrFun h1 (hi 0)
  simp only [theta0e_apply, theta0_hi] at h2
  revert h2
  decide +revert

theorem orderOf_theta0e : orderOf theta0e = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime theta0e_pow_three theta0e_ne_one

theorem theta0e_mem_E : theta0e ∈ C.E := by
  have : theta0e ∈ (Subgroup.center C.E).map C.E.subtype := by
    rw [C.hZ]; exact Subgroup.mem_zpowers _
  obtain ⟨z, -, hz⟩ := this
  rw [← hz]
  exact z.2

theorem mem_center_iff (e : C.E) :
    e ∈ Subgroup.center C.E ↔ (e : G12) ∈ Subgroup.zpowers theta0e := by
  rw [← C.hZ]
  constructor
  · intro h
    exact ⟨e, h, rfl⟩
  · rintro ⟨z, hz, hze⟩
    have : z = e := Subtype.ext hze
    rwa [this] at hz

theorem theta0e_mem_center : (⟨theta0e, C.theta0e_mem_E⟩ : C.E) ∈ Subgroup.center C.E := by
  rw [C.mem_center_iff]
  exact Subgroup.mem_zpowers _

theorem theta0e_comm (e : C.E) : (e : G12) * theta0e = theta0e * e := by
  have h := Subgroup.mem_center_iff.mp C.theta0e_mem_center e
  exact congrArg Subtype.val h

theorem card_center : Nat.card (Subgroup.center C.E) = 3 := by
  have h1 : Nat.card ((Subgroup.center C.E).map C.E.subtype) = Nat.card (Subgroup.center C.E) :=
    Subgroup.card_map_of_injective C.E.subtype_injective
  rw [C.hZ, Nat.card_zpowers, orderOf_theta0e] at h1
  exact h1.symm

theorem pow_three_of_mem_center {z : C.E} (hz : z ∈ Subgroup.center C.E) : z ^ 3 = 1 := by
  rw [C.mem_center_iff] at hz
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine Subtype.ext ?_
  show (z : G12) ^ 3 = 1
  rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, theta0e_pow_three,
    one_zpow]

@[expose] noncomputable def AtildeE : Subgroup C.E := thetaBar.range.comap C.π

theorem mem_AtildeE {e : C.E} : e ∈ C.AtildeE ↔ C.π e ∈ thetaBar.range := Iff.rfl

theorem AtildeE_comm {x y : C.E} (hx : x ∈ C.AtildeE) (hy : y ∈ C.AtildeE) : x * y = y * x :=
  commute_of_mem_range C.hπs C.hπk.le hx hy

theorem AtildeE_pow_three {x : C.E} (hx : x ∈ C.AtildeE) : x ^ 3 = 1 := by
  obtain ⟨y, hy, hy3⟩ := exists_lift_of_mem_range C.hπs C.hπk.le hx
  have hz : y⁻¹ * x ∈ C.π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have hzc : y⁻¹ * x ∈ Subgroup.center C.E := C.hπk ▸ hz
  have hz3 := C.pow_three_of_mem_center hzc
  have hcomm : Commute y (y⁻¹ * x) := Subgroup.mem_center_iff.mp hzc y
  calc x ^ 3 = (y * (y⁻¹ * x)) ^ 3 := by rw [mul_inv_cancel_left]
    _ = y ^ 3 * (y⁻¹ * x) ^ 3 := hcomm.mul_pow 3
    _ = 1 := by rw [hy3, hz3, one_mul]

theorem card_AtildeE : Nat.card C.AtildeE = 243 := by
  haveI : Finite C.E := Nat.finite_of_card_ne_zero (by rw [C.card_E]; norm_num)
  haveI : Finite X₀ := Finite.of_surjective C.π C.hπs
  have h := card_comap_of_surjective C.π C.hπs thetaBar.range
  rw [C.hπk, C.card_center, card_range_thetaBar] at h
  exact h.trans (by norm_num)

theorem theta0_mem_AtildeE : (⟨theta0e, C.theta0e_mem_E⟩ : C.E) ∈ C.AtildeE := by
  have h : C.π ⟨theta0e, C.theta0e_mem_E⟩ = 1 := by
    rw [← MonoidHom.mem_ker, C.hπk]
    exact C.theta0e_mem_center
  rw [mem_AtildeE, h]
  exact one_mem _

@[expose] noncomputable def AtildeG : Subgroup G12 := C.AtildeE.map C.E.subtype

@[expose] noncomputable def PE : Subgroup C.E := Psub.comap C.π

@[expose] noncomputable def PG : Subgroup G12 := C.PE.map C.E.subtype

theorem AtildeE_le_PE : C.AtildeE ≤ C.PE := fun _ hx => A_le_Psub hx

theorem AtildeG_le_PG : C.AtildeG ≤ C.PG := Subgroup.map_mono C.AtildeE_le_PE

theorem card_PE : Nat.card C.PE = 3 ^ 7 := by
  haveI : Finite C.E := Nat.finite_of_card_ne_zero (by rw [C.card_E]; norm_num)
  haveI : Finite X₀ := Finite.of_surjective C.π C.hπs
  have h := card_comap_of_surjective C.π C.hπs Psub
  rw [C.hπk, C.card_center, card_Psub] at h
  exact h.trans (by norm_num)

theorem card_PG : Nat.card C.PG = 3 ^ 7 := by
  rw [PG, Subgroup.card_map_of_injective C.E.subtype_injective, C.card_PE]

theorem factorization_card_E : (Nat.card C.E).factorization 3 = 7 := by
  rw [C.card_E]
  have h7 := (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (9797760 : ℕ) ≠ 0)).1
    (by norm_num : 3 ^ 7 ∣ 9797760)
  have h8 : ¬ 8 ≤ (9797760 : ℕ).factorization 3 := fun h =>
    absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (9797760 : ℕ) ≠ 0)).2 h)
      (by norm_num)
  omega

@[expose] def conjE {n : G12} (hn : n ∈ C.X) : C.E →* C.E where
  toFun e := ⟨n * e * n⁻¹, C.hEnorm n hn e e.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[simp] theorem coe_conjE {n : G12} (hn : n ∈ C.X) (e : C.E) :
    ((C.conjE hn e : C.E) : G12) = n * e * n⁻¹ := rfl

theorem conjE_injective {n : G12} (hn : n ∈ C.X) : Function.Injective (C.conjE hn) := by
  intro a b h
  have := congrArg Subtype.val h
  simp only [coe_conjE, mul_left_inj, mul_right_inj] at this
  exact Subtype.ext this

theorem mem_PE_of_mem_PG {e : C.E} (h : (e : G12) ∈ C.PG) : e ∈ C.PE := by
  obtain ⟨p, hp, hpe⟩ := h
  have : p = e := Subtype.ext hpe
  rwa [this] at hp

theorem normalizes_AtildeG_of_normalizes_PG {n : G12} (hn : n ∈ C.X)
    (hP : ∀ p ∈ C.PG, n * p * n⁻¹ ∈ C.PG) : ∀ a ∈ C.AtildeG, n * a * n⁻¹ ∈ C.AtildeG := by
  haveI : Finite C.E := Nat.finite_of_card_ne_zero (by rw [C.card_E]; norm_num)
  set B : Subgroup C.E := C.AtildeE.map (C.conjE hn) with hB
  have hBP : B ≤ C.PE := by
    rintro _ ⟨a, ha, rfl⟩
    apply C.mem_PE_of_mem_PG
    rw [coe_conjE]
    exact hP _ (C.AtildeG_le_PG ⟨a, ha, rfl⟩)
  have hBcard : Nat.card B = 243 := by
    rw [hB, Subgroup.card_map_of_injective (C.conjE_injective hn), C.card_AtildeE]
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, C.AtildeE_comm ha hb]
  have hBpow : ∀ x ∈ B, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, C.AtildeE_pow_three ha, map_one]
  set Bbar : Subgroup X₀ := B.map C.π with hBbar
  have hBbarP : Bbar ≤ Psub := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBP hb
  have hBbarAb : CFSG.Open.IsElemAbelian 3 Bbar := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x, b, hb, rfl⟩ := x
      obtain ⟨y, b', hb', rfl⟩ := y
      refine Subtype.ext ?_
      show C.π b * C.π b' = C.π b' * C.π b
      rw [← map_mul, ← map_mul, hBcomm b hb b' hb']
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hBpow b hb, map_one]
  have hBbar_le : Nat.card Bbar ≤ 3 ^ 4 := card_le_of_le_Psub hBbarAb hBbarP
  have hBbar_ge : 3 ^ 4 ≤ Nat.card Bbar := by
    have h1 := Subgroup.card_ker_mul_card_range (C.π.domRestrict B)
    have h2 : Nat.card (C.π.domRestrict B).ker ≤ 3 := by
      have hle : (C.π.domRestrict B).ker.map B.subtype ≤ C.π.ker := by
        rintro _ ⟨b, hb, rfl⟩
        exact hb
      calc Nat.card (C.π.domRestrict B).ker = Nat.card ((C.π.domRestrict B).ker.map B.subtype) :=
            (Subgroup.card_map_of_injective B.subtype_injective).symm
        _ ≤ Nat.card C.π.ker := Subgroup.card_le_of_le hle
        _ = 3 := by rw [C.hπk, C.card_center]
    have h3 : (C.π.domRestrict B).range = Bbar := by
      ext x
      constructor
      · rintro ⟨⟨b, hb⟩, rfl⟩
        exact ⟨b, hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
    rw [h3, hBcard] at h1
    have h4 := Nat.mul_le_mul_right (Nat.card Bbar) h2
    omega
  have hBbarA : Bbar = thetaBar.range :=
    elemAbelian_eq_range_thetaBar hBbarP (fun x hx y hy => by
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨b', hb', rfl⟩ := hy
      rw [← map_mul, ← map_mul, hBcomm b hb b' hb'])
      (fun x hx => hBbarAb.2 x hx) (le_antisymm hBbar_le hBbar_ge)
  intro a ha
  obtain ⟨ae, hae, rfl⟩ := ha
  have hb : C.conjE hn ae ∈ B := ⟨ae, hae, rfl⟩
  have hπb : C.π (C.conjE hn ae) ∈ thetaBar.range := by
    rw [← hBbarA]
    exact ⟨_, hb, rfl⟩
  exact ⟨C.conjE hn ae, hπb, rfl⟩

theorem frattini : ∀ x ∈ C.X, ∃ e ∈ C.E, ∃ n ∈ C.X,
    (∀ a ∈ C.AtildeG, n * a * n⁻¹ ∈ C.AtildeG) ∧ x = e * n := by
  haveI : Finite G12 := Finite.of_injective (fun e : G12 => (e : V12 → V12))
    fun _ _ h => LinearEquiv.ext (congrFun h)
  refine frattini_of_normalizes C.X C.E C.PG C.AtildeG C.hEX C.hEnorm ?_ ?_ ?_
  · exact Subgroup.map_subtype_le _
  · rw [C.card_PG, C.factorization_card_E]
  · intro n hn hP
    exact C.normalizes_AtildeG_of_normalizes_PG hn hP

@[expose] noncomputable def psiE : C.AtildeE →* A4 :=
  (MonoidHom.ofInjective thetaBar_injective).symm.toMonoidHom.comp
    ((C.π.domRestrict C.AtildeE).codRestrict thetaBar.range (fun a => a.2))

theorem thetaBar_psiE (a : C.AtildeE) : thetaBar (C.psiE a) = C.π a := by
  have h := (MonoidHom.ofInjective thetaBar_injective).apply_symm_apply
    ⟨C.π a, a.2⟩
  exact congrArg Subtype.val h

theorem psiE_surjective : Function.Surjective C.psiE := by
  intro x
  obtain ⟨e, he⟩ := C.hπs (thetaBar x)
  refine ⟨⟨e, by rw [mem_AtildeE, he]; exact ⟨x, rfl⟩⟩, ?_⟩
  apply thetaBar_injective
  rw [C.thetaBar_psiE]
  exact he

theorem psiE_eq_one_iff (a : C.AtildeE) : C.psiE a = 1 ↔ (a : C.E) ∈ Subgroup.center C.E := by
  rw [← C.hπk, MonoidHom.mem_ker, ← C.thetaBar_psiE, ← map_one thetaBar]
  exact thetaBar_injective.eq_iff.symm

@[expose] noncomputable def levLift (k : Gen) : C.E := (C.hπs (levBar k)).choose

theorem π_levLift (k : Gen) : C.π (C.levLift k) = levBar k := (C.hπs (levBar k)).choose_spec

theorem levLift_normalizes {k : Gen} {a : C.E} (ha : a ∈ C.AtildeE) :
    C.levLift k * a * (C.levLift k)⁻¹ ∈ C.AtildeE := by
  obtain ⟨x, hx⟩ := ha
  rw [mem_AtildeE, map_mul, map_mul, map_inv, C.π_levLift, ← hx, levBar_conj]
  exact ⟨_, rfl⟩

theorem psiE_levLift_conj {k : Gen} (a : C.AtildeE) :
    C.psiE ⟨C.levLift k * a * (C.levLift k)⁻¹, C.levLift_normalizes a.2⟩ = sg k (C.psiE a) := by
  apply thetaBar_injective
  rw [C.thetaBar_psiE, ← levBar_conj]
  show C.π (C.levLift k * a * (C.levLift k)⁻¹) = _
  rw [map_mul, map_mul, map_inv, C.π_levLift, C.thetaBar_psiE]

theorem levBar_pow_three (k : Gen) : levBar k ^ 3 = 1 := by
  have h : levSU k ^ 3 = 1 := by
    refine ext_matrix ?_
    have := levMat_pow_three k
    simpa [levSU, toSU, pow_succ] using this
  show (QuotientGroup.mk (levSU k) : X₀) ^ 3 = 1
  rw [← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]

theorem levLift_pow_three_mem_center (k : Gen) : C.levLift k ^ 3 ∈ Subgroup.center C.E := by
  rw [← C.hπk, MonoidHom.mem_ker, map_pow, C.π_levLift, levBar_pow_three]

end Ctx

end CFSG.GF2Type.Smith1979.IdxFour
