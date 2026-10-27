module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

lemma orderOf_eq_four {G : Type*} [Group G] {a : G} (ha4 : a ^ 4 = 1)
    (ha2 : a ^ 2 ≠ 1) : orderOf a = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (x := a) (p := 2) (n := 1) (by simpa using ha2) (by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    exact ha4)
  simpa using h

private noncomputable def zmod4Equiv {G : Type*} [Group G] (a : G)
    (hcard : Nat.card (Subgroup.zpowers a) = 4) :
    Multiplicative (ZMod 4) ≃* Subgroup.zpowers a :=
  zmodMulEquivOfGenerator (g := ⟨a, Subgroup.mem_zpowers a⟩)
    (fun x => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.property
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by ext; simpa using hk⟩)
    hcard

private noncomputable def zmod4Hom {G : Type*} [Group G] (a : G)
    (hcard : Nat.card (Subgroup.zpowers a) = 4) :
    Multiplicative (ZMod 4) →* G :=
  (Subgroup.subtype (Subgroup.zpowers a)).comp (zmod4Equiv a hcard).toMonoidHom

private lemma zmod4Hom_apply_one {G : Type*} [Group G] {a : G}
    (hcard : Nat.card (Subgroup.zpowers a) = 4) :
    zmod4Hom a hcard (Multiplicative.ofAdd 1) = a := by
  simp [zmod4Hom, zmod4Equiv]

private lemma zmod4Hom_mem {G : Type*} [Group G] {a : G}
    (hcard : Nat.card (Subgroup.zpowers a) = 4) (i : Multiplicative (ZMod 4)) :
    zmod4Hom a hcard i ∈ Subgroup.zpowers a :=
  (zmod4Equiv a hcard i).property

private lemma zmod4Hom_injective {G : Type*} [Group G] {a : G}
    (hcard : Nat.card (Subgroup.zpowers a) = 4) :
    Function.Injective (zmod4Hom a hcard) := by
  intro x y hxy
  exact (zmod4Equiv a hcard).injective (Subtype.ext hxy)

private def quatMap {G : Type*} [Group G] (pw : Multiplicative (ZMod 4) →* G) (b : G) :
    QuaternionGroup 2 → G
  | QuaternionGroup.a i => pw (Multiplicative.ofAdd i)
  | QuaternionGroup.xa i => b * pw (Multiplicative.ofAdd i)

private def dihedMap {G : Type*} [Group G] (pw : Multiplicative (ZMod 4) →* G) (b : G) :
    DihedralGroup 4 → G
  | DihedralGroup.r i => pw (Multiplicative.ofAdd i)
  | DihedralGroup.sr i => b * pw (Multiplicative.ofAdd i)

theorem exists_quaternion_hom {G : Type*} [Group G] (a b : G) (ha4 : a ^ 4 = 1)
    (ha2 : a ^ 2 ≠ 1) (hb : b ^ 2 = a ^ 2) (hba : b * a * b⁻¹ = a⁻¹) :
    ∃ φ : QuaternionGroup 2 →* G, Function.Injective φ ∧ φ (QuaternionGroup.a 1) = a ∧
      φ (QuaternionGroup.xa 0) = b := by
  have ha_order : orderOf a = 4 := orderOf_eq_four ha4 ha2
  have hcard : Nat.card (Subgroup.zpowers a) = 4 := by
    rw [Nat.card_zpowers, ha_order]
  set pw := zmod4Hom a hcard with hpw
  have hpw_one : pw (Multiplicative.ofAdd 1) = a := zmod4Hom_apply_one hcard
  have hpw_inj : Function.Injective pw := zmod4Hom_injective hcard
  have hpw_mem : ∀ i, pw i ∈ Subgroup.zpowers a := zmod4Hom_mem hcard
  have hofadd : Function.Injective (Multiplicative.ofAdd : ZMod 4 → Multiplicative (ZMod 4)) :=
    fun i j h => by simpa using congrArg Multiplicative.toAdd h
  have hpw_comm : ∀ i j : Multiplicative (ZMod 4), pw i * pw j = pw j * pw i := by
    intro i j
    rw [← map_mul, ← map_mul, mul_comm]
  have hconj : ∀ i : Multiplicative (ZMod 4), b * pw i * b⁻¹ = (pw i)⁻¹ := by
    intro i
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hpw_mem i)
    rw [← hk, ← conj_zpow (a := b) (b := a) (i := k), hba, inv_zpow]
  have hbw : ∀ i : Multiplicative (ZMod 4), pw i * b = b * (pw i)⁻¹ := by
    intro i
    have h := hconj i⁻¹
    rw [map_inv, inv_inv] at h
    have h' : b * (pw i)⁻¹ = pw i * b := by
      calc b * (pw i)⁻¹ = b * (pw i)⁻¹ * b⁻¹ * b := by group
        _ = pw i * b := by rw [h]
    exact h'.symm
  have ha2pw : a ^ 2 = pw (Multiplicative.ofAdd 2) := by
    rw [← hpw_one, ← map_pow]
    rw [show (Multiplicative.ofAdd 1 : Multiplicative (ZMod 4)) ^ 2 =
      Multiplicative.ofAdd 2 by decide +kernel]
  have hb2 : b * b = pw (Multiplicative.ofAdd 2) := by
    rw [← pow_two, hb, ha2pw]
  have h_aa : ∀ i j : ZMod 4, pw (Multiplicative.ofAdd (i + j)) =
      pw (Multiplicative.ofAdd i) * pw (Multiplicative.ofAdd j) := by
    intro i j
    rw [← map_mul]
    rfl
  have hidx : ∀ i j : ZMod 4,
      (Multiplicative.ofAdd i)⁻¹ * Multiplicative.ofAdd j =
        Multiplicative.ofAdd (j - i) := by
    intro i j
    rw [← ofAdd_neg, ← ofAdd_add]
    congr 1
    abel
  have h_axa : ∀ i j : ZMod 4,
      pw (Multiplicative.ofAdd i) * (b * pw (Multiplicative.ofAdd j)) =
        b * pw (Multiplicative.ofAdd (j - i)) := by
    intro i j
    rw [← mul_assoc, hbw (Multiplicative.ofAdd i), mul_assoc, ← map_inv, ← map_mul, hidx i j]
  have h_xaa : ∀ i j : ZMod 4,
      (b * pw (Multiplicative.ofAdd i)) * pw (Multiplicative.ofAdd j) =
        b * pw (Multiplicative.ofAdd (i + j)) := by
    intro i j
    rw [mul_assoc, ← map_mul]
    rfl
  have h_xaxa : ∀ i j : ZMod 4,
      (b * pw (Multiplicative.ofAdd i)) * (b * pw (Multiplicative.ofAdd j)) =
        pw (Multiplicative.ofAdd (2 + (j - i))) := by
    intro i j
    have step : (b * pw (Multiplicative.ofAdd i)) * (b * pw (Multiplicative.ofAdd j)) =
        b * (pw (Multiplicative.ofAdd i) * b) * pw (Multiplicative.ofAdd j) := by
      group
    rw [step, hbw (Multiplicative.ofAdd i), ← mul_assoc, hb2, mul_assoc]
    rw [← map_inv, hpw_comm ((Multiplicative.ofAdd i)⁻¹) (Multiplicative.ofAdd j)]
    rw [← mul_assoc, ← map_mul, ← map_mul]
    congr 1
    rw [← ofAdd_neg, ← ofAdd_add, ← ofAdd_add]
    congr 1
    abel
  have hbA : b ∉ Subgroup.zpowers a := by
    intro hb'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hconj : b * a * b⁻¹ = a := by
      rw [← hk]
      group
    rw [hconj] at hba
    have h2 : a ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hba]
      rw [inv_mul_cancel]
    exact ha2 h2
  have hf : ∀ x y : QuaternionGroup 2,
      quatMap pw b (x * y) = quatMap pw b x * quatMap pw b y := by
    rintro (i | i) (j | j)
    · simpa only [QuaternionGroup.a_mul_a, quatMap] using h_aa i j
    · simpa only [QuaternionGroup.a_mul_xa, quatMap] using (h_axa i j).symm
    · simpa only [QuaternionGroup.xa_mul_a, quatMap] using (h_xaa i j).symm
    · simp only [QuaternionGroup.xa_mul_xa, quatMap]
      rw [h_xaxa i j]
      congr 1
      congr 1
      ring
  refine ⟨MonoidHom.mk' (quatMap pw b) hf, ?_, ?_, ?_⟩
  · intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · have h1 : Multiplicative.ofAdd i = Multiplicative.ofAdd j := hpw_inj hxy
      rw [hofadd h1]
    · exfalso
      have h1 : pw (Multiplicative.ofAdd i) = b * pw (Multiplicative.ofAdd j) := hxy
      have hb_eq : b = pw (Multiplicative.ofAdd i) * (pw (Multiplicative.ofAdd j))⁻¹ := by
        rw [h1]
        group
      exact hbA (hb_eq ▸ Subgroup.mul_mem _ (hpw_mem i) (Subgroup.inv_mem _ (hpw_mem j)))
    · exfalso
      have h1 : b * pw (Multiplicative.ofAdd i) = pw (Multiplicative.ofAdd j) := hxy
      have hb_eq : b = pw (Multiplicative.ofAdd j) * (pw (Multiplicative.ofAdd i))⁻¹ := by
        rw [← h1]
        group
      exact hbA (hb_eq ▸ Subgroup.mul_mem _ (hpw_mem j) (Subgroup.inv_mem _ (hpw_mem i)))
    · have h1 : pw (Multiplicative.ofAdd i) = pw (Multiplicative.ofAdd j) :=
        mul_left_cancel hxy
      rw [hofadd (hpw_inj h1)]
  · simpa [quatMap] using hpw_one
  · simp [quatMap]

theorem exists_dihedral_hom {G : Type*} [Group G] (a b : G) (ha4 : a ^ 4 = 1)
    (ha2 : a ^ 2 ≠ 1) (hb : b ^ 2 = 1) (hba : b * a * b⁻¹ = a⁻¹) :
    ∃ φ : DihedralGroup 4 →* G, Function.Injective φ ∧ φ (DihedralGroup.r 1) = a ∧
      φ (DihedralGroup.sr 0) = b := by
  have ha_order : orderOf a = 4 := orderOf_eq_four ha4 ha2
  have hcard : Nat.card (Subgroup.zpowers a) = 4 := by
    rw [Nat.card_zpowers, ha_order]
  set pw := zmod4Hom a hcard with hpw
  have hpw_one : pw (Multiplicative.ofAdd 1) = a := zmod4Hom_apply_one hcard
  have hpw_inj : Function.Injective pw := zmod4Hom_injective hcard
  have hpw_mem : ∀ i, pw i ∈ Subgroup.zpowers a := zmod4Hom_mem hcard
  have hofadd : Function.Injective (Multiplicative.ofAdd : ZMod 4 → Multiplicative (ZMod 4)) :=
    fun i j h => by simpa using congrArg Multiplicative.toAdd h
  have hconj : ∀ i : Multiplicative (ZMod 4), b * pw i * b⁻¹ = (pw i)⁻¹ := by
    intro i
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hpw_mem i)
    rw [← hk, ← conj_zpow (a := b) (b := a) (i := k), hba, inv_zpow]
  have hbw : ∀ i : Multiplicative (ZMod 4), pw i * b = b * (pw i)⁻¹ := by
    intro i
    have h := hconj i⁻¹
    rw [map_inv, inv_inv] at h
    have h' : b * (pw i)⁻¹ = pw i * b := by
      calc b * (pw i)⁻¹ = b * (pw i)⁻¹ * b⁻¹ * b := by group
        _ = pw i * b := by rw [h]
    exact h'.symm
  have hb2 : b * b = 1 := by
    rw [← pow_two, hb]
  have h_aa : ∀ i j : ZMod 4, pw (Multiplicative.ofAdd (i + j)) =
      pw (Multiplicative.ofAdd i) * pw (Multiplicative.ofAdd j) := by
    intro i j
    rw [← map_mul]
    rfl
  have hidx : ∀ i j : ZMod 4,
      (Multiplicative.ofAdd i)⁻¹ * Multiplicative.ofAdd j =
        Multiplicative.ofAdd (j - i) := by
    intro i j
    rw [← ofAdd_neg, ← ofAdd_add]
    congr 1
    abel
  have h_axa : ∀ i j : ZMod 4,
      pw (Multiplicative.ofAdd i) * (b * pw (Multiplicative.ofAdd j)) =
        b * pw (Multiplicative.ofAdd (j - i)) := by
    intro i j
    rw [← mul_assoc, hbw (Multiplicative.ofAdd i), mul_assoc, ← map_inv, ← map_mul, hidx i j]
  have h_xaa : ∀ i j : ZMod 4,
      (b * pw (Multiplicative.ofAdd i)) * pw (Multiplicative.ofAdd j) =
        b * pw (Multiplicative.ofAdd (i + j)) := by
    intro i j
    rw [mul_assoc, ← map_mul]
    rfl
  have h_xaxa : ∀ i j : ZMod 4,
      (b * pw (Multiplicative.ofAdd i)) * (b * pw (Multiplicative.ofAdd j)) =
        pw (Multiplicative.ofAdd (j - i)) := by
    intro i j
    have step : (b * pw (Multiplicative.ofAdd i)) * (b * pw (Multiplicative.ofAdd j)) =
        b * (pw (Multiplicative.ofAdd i) * b) * pw (Multiplicative.ofAdd j) := by
      group
    rw [step, hbw (Multiplicative.ofAdd i), ← mul_assoc, hb2, one_mul]
    rw [← map_inv, ← map_mul, hidx i j]
  have hbA : b ∉ Subgroup.zpowers a := by
    intro hb'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hconj : b * a * b⁻¹ = a := by
      rw [← hk]
      group
    rw [hconj] at hba
    have h2 : a ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hba]
      rw [inv_mul_cancel]
    exact ha2 h2
  have hf : ∀ x y : DihedralGroup 4,
      dihedMap pw b (x * y) = dihedMap pw b x * dihedMap pw b y := by
    rintro (i | i) (j | j)
    · simpa only [DihedralGroup.r_mul_r, dihedMap] using h_aa i j
    · simpa only [DihedralGroup.r_mul_sr, dihedMap] using (h_axa i j).symm
    · simpa only [DihedralGroup.sr_mul_r, dihedMap] using (h_xaa i j).symm
    · simp only [DihedralGroup.sr_mul_sr, dihedMap]
      rw [h_xaxa i j]
  refine ⟨MonoidHom.mk' (dihedMap pw b) hf, ?_, ?_, ?_⟩
  · intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · have h1 : Multiplicative.ofAdd i = Multiplicative.ofAdd j := hpw_inj hxy
      rw [hofadd h1]
    · exfalso
      have h1 : pw (Multiplicative.ofAdd i) = b * pw (Multiplicative.ofAdd j) := hxy
      have hb_eq : b = pw (Multiplicative.ofAdd i) * (pw (Multiplicative.ofAdd j))⁻¹ := by
        rw [h1]
        group
      exact hbA (hb_eq ▸ Subgroup.mul_mem _ (hpw_mem i) (Subgroup.inv_mem _ (hpw_mem j)))
    · exfalso
      have h1 : b * pw (Multiplicative.ofAdd i) = pw (Multiplicative.ofAdd j) := hxy
      have hb_eq : b = pw (Multiplicative.ofAdd j) * (pw (Multiplicative.ofAdd i))⁻¹ := by
        rw [← h1]
        group
      exact hbA (hb_eq ▸ Subgroup.mul_mem _ (hpw_mem j) (Subgroup.inv_mem _ (hpw_mem i)))
    · have h1 : pw (Multiplicative.ofAdd i) = pw (Multiplicative.ofAdd j) :=
        mul_left_cancel hxy
      rw [hofadd (hpw_inj h1)]
  · simpa [dihedMap] using hpw_one
  · simp [dihedMap]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
