module

public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open

section FStar

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem genFittingFitting_normal : (genFittingFitting X).Normal :=
  fittingSubgroup_normal

omit [Finite X] in
theorem genFittingLayer_normal : (genFittingLayer X).Normal :=
  ComponentClassification.Layer.normal X

omit [Finite X] in
theorem genFittingFStar_isNormal : (genFittingFStar X).Normal :=
  ComponentClassification.GeneralizedFitting.normal X

theorem centralizer_genFittingFStar_le :
    Subgroup.centralizer (genFittingFStar X : Set X) ≤ genFittingFStar X :=
  ComponentClassification.GeneralizedFitting.centralizer_le X

omit [Finite X] in
theorem normal_centralizer_genFittingFStar :
    (Subgroup.centralizer (genFittingFStar X : Set X)).Normal := by
  have hn := genFittingFStar_isNormal (X := X)
  refine ⟨fun z hz g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro f hf
  have h1 := hz (g⁻¹ * f * g) (by simpa using hn.conj_mem f hf g⁻¹)
  calc f * (g * z * g⁻¹) = g * ((g⁻¹ * f * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * f := by group

theorem isPGroup_two_centralizer_genFittingFStar (hO : oddCore X = ⊥) :
    IsPGroup 2 (Subgroup.centralizer (genFittingFStar X : Set X)) := by
  set Z := Subgroup.centralizer (genFittingFStar X : Set X) with hZ
  have hZF : Z ≤ genFittingFStar X := centralizer_genFittingFStar_le
  have hcomm : ∀ a b : Z, a * b = b * a := fun a b =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp b.2) a (hZF a.2))
  let _ : CommGroup Z := { (inferInstance : Group Z) with mul_comm := hcomm }
  have hnil : Group.IsNilpotent Z := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isPGroup_of_nilpotent_normal Z normal_centralizer_genFittingFStar hnil
    (by rw [← QuaternionStructure.oddCore_eq_pPrimeCore_two]; exact hO)

@[expose] def autFixSubgroup (η : MulAut X) : Subgroup X where
  carrier := {y | η y = y}
  one_mem' := map_one η
  mul_mem' {a b} ha hb := by
    change η a = a at ha
    change η b = b at hb
    change η (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    change η a = a at ha
    change η a⁻¹ = a⁻¹
    rw [map_inv, ha]

omit [Finite X] in
theorem mem_autFixSubgroup {η : MulAut X} {y : X} : y ∈ autFixSubgroup η ↔ η y = y := Iff.rfl

theorem exists_pow_two_pow_eq_one_of_fixes_fstar (hO : oddCore X = ⊥) (η : MulAut X)
    (hη : ∀ y ∈ genFittingFStar X, η y = y) : ∃ m : ℕ, η ^ 2 ^ m = 1 := by
  have hn := genFittingFStar_isNormal (X := X)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_two_centralizer_genFittingFStar hO)
  refine ⟨m, ?_⟩
  have hu : ∀ g : X, g⁻¹ * η g ∈ Subgroup.centralizer (genFittingFStar X : Set X) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 : η (g * f * g⁻¹) = g * f * g⁻¹ := hη _ (hn.conj_mem f hf g)
    rw [map_mul, map_mul, map_inv, hη f hf] at h1
    have h2 := mul_inv_eq_iff_eq_mul.mp h1
    calc f * (g⁻¹ * η g) = g⁻¹ * (g * f * g⁻¹ * η g) := by group
      _ = g⁻¹ * (η g * f) := by rw [h2]
      _ = g⁻¹ * η g * f := by group
  have hpow : ∀ (n : ℕ), ∀ y ∈ genFittingFStar X, (η ^ n) y = y := by
    intro n
    induction n with
    | zero => intro y _; simp
    | succ n ih =>
      intro y hy
      rw [pow_succ, MulAut.mul_apply, hη y hy, ih y hy]
  have hform : ∀ (n : ℕ) (g : X), (η ^ n) g = g * (g⁻¹ * η g) ^ n := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      have hg : η g = g * (g⁻¹ * η g) := by group
      rw [pow_succ, MulAut.mul_apply, hg, map_mul, ih g, hpow n _ (centralizer_genFittingFStar_le
        (hu g)), pow_succ]
      group
  refine MulEquiv.ext fun g => ?_
  rw [hform, MulAut.one_apply]
  have hz : ((⟨g⁻¹ * η g, hu g⟩ : Subgroup.centralizer (genFittingFStar X : Set X)) ^
      Nat.card (Subgroup.centralizer (genFittingFStar X : Set X))) = 1 := pow_card_eq_one'
  rw [hm] at hz
  have hz' := congrArg Subtype.val hz
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at hz'
  rw [hz', mul_one]

end FStar

section Main

variable {X : Type*} [Group X] [Finite X]

theorem genFittingFitting_isNilpotent : Group.IsNilpotent (genFittingFitting X) :=
  fittingSubgroup_nilpotent

theorem isPGroup_two_genFittingFitting (hO : oddCore X = ⊥) :
    IsPGroup 2 (genFittingFitting X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (genFittingFitting X) := genFittingFitting_isNilpotent
  exact isPGroup_of_nilpotent_normal _ genFittingFitting_normal this
    (by rw [← QuaternionStructure.oddCore_eq_pPrimeCore_two]; exact hO)

theorem layer_commutes_fitting {e p : X} (he : e ∈ genFittingLayer X)
    (hp : p ∈ genFittingFitting X) : e * p = p * e := by
  have hn := genFittingFitting_normal (X := X)
  have hsub : IsSubnormal (genFittingFitting X) ⊤ :=
    (Adapters.isSubnormal_top_iff _).mpr hn.isSubnormal
  have : Group.IsNilpotent (genFittingFitting X) := genFittingFitting_isNilpotent
  have hcomm := ComponentClassification.Layer.commutes_with_solvable_subnormal
    (genFittingFitting X) hsub
  have hle : ComponentClassification.Layer.subgroup X ≤
      Subgroup.centralizer (genFittingFitting X : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact ((Subgroup.mem_centralizer_iff.mp (hle he)) p hp).symm

theorem exists_inner_of_fixes_fitting_inner_layer (hO : oddCore X = ⊥) (δ : MulAut X) {k : ℕ}
    (hk : δ ^ 3 ^ k = 1) (hF : ∀ p ∈ genFittingFitting X, δ p = p) {e : X}
    (he : e ∈ genFittingLayer X) (hE : ∀ y ∈ genFittingLayer X, δ y = e * y * e⁻¹) :
    ∃ g : X, ∀ y, δ y = g * y * g⁻¹ := by
  set η : MulAut X := MulAut.conj e⁻¹ * δ with hη
  have hηapp : ∀ y, η y = e⁻¹ * δ y * e := fun y => by
    rw [hη, MulAut.mul_apply, MulAut.conj_apply]; simp
  have hηF : ∀ p ∈ genFittingFitting X, η p = p := by
    intro p hp
    rw [hηapp, hF p hp]
    have := layer_commutes_fitting he hp
    calc e⁻¹ * p * e = e⁻¹ * (p * e) := by group
      _ = e⁻¹ * (e * p) := by rw [this]
      _ = p := by group
  have hηE : ∀ y ∈ genFittingLayer X, η y = y := by
    intro y hy
    rw [hηapp, hE y hy]; group
  have hηFs : ∀ y ∈ genFittingFStar X, η y = y := by
    have hle : genFittingFStar X ≤ autFixSubgroup η := sup_le (fun p hp => hηF p hp)
      (fun y hy => hηE y hy)
    exact fun y hy => hle hy
  obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_fixes_fstar hO η hηFs
  have hδ : δ = MulAut.conj e * η := by
    rw [hη, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hInnNormal : ((MulAut.conj : X →* MulAut X).range).Normal := by
    refine ⟨fun n hn φ => ?_⟩
    obtain ⟨m, rfl⟩ := hn
    refine ⟨φ m, ?_⟩
    refine MulEquiv.ext fun g => ?_
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
  let q : MulAut X →* MulAut X ⧸ (MulAut.conj : X →* MulAut X).range :=
    QuotientGroup.mk' _
  have hqδη : q δ = q η := by
    rw [hδ, map_mul]
    have : q (MulAut.conj e) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨e, rfl⟩
    rw [this, one_mul]
  have h1 : q δ ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h2 : q δ ^ 2 ^ m = 1 := by rw [hqδη, ← map_pow, hm, map_one]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ m) := Nat.Coprime.pow k m (by norm_num)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hd
  have hq1 : q δ = 1 := orderOf_eq_one_iff.mp hd
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff _).mp hq1
  exact ⟨g, fun y => by rw [← hg]; simp [MulAut.conj_apply]⟩

end Main

section OddKernel

theorem oddCore_characteristic_of_finite (X : Type*) [Group X] [Finite X] :
    (oddCore X).Characteristic := by
  rw [QuaternionStructure.oddCore_eq_pPrimeCore_two]
  infer_instance

theorem odd_natCard_comap_of_odd_ker {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hker : Odd (Nat.card f.ker)) (K : Subgroup B) (hK : Odd (Nat.card K)) :
    Odd (Nat.card (K.comap f)) := by
  by_contra hcon
  have h2 : 2 ∣ Nat.card (K.comap f) := by
    rcases Nat.even_or_odd (Nat.card (K.comap f)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hfg : (⟨f g, g.2⟩ : K) ^ 2 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, ← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one]
    simp
  have hord : orderOf (⟨f g, g.2⟩ : K) ∣ 2 := orderOf_dvd_of_pow_eq_one hfg
  have hodd : Odd (orderOf (⟨f g, g.2⟩ : K)) := hK.of_dvd_nat (orderOf_dvd_natCard _)
  have h1 : orderOf (⟨f g, g.2⟩ : K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have hfg1 : f g = 1 := by
    have := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  have hker1 : ((g : A)) ∈ f.ker := hfg1
  have hord2 : orderOf (⟨(g : A), hker1⟩ : f.ker) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact hg
  have := orderOf_dvd_natCard (⟨(g : A), hker1⟩ : f.ker)
  rw [hord2] at this
  exact (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr this)

end OddKernel

end CFSG.ClassicalInvolution.Q3
