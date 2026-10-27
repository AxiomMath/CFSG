module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

public section

namespace CFSG

noncomputable section

def autFixedSubgroup {J : Type*} [Group J] (α : MulAut J) : Subgroup J where
  carrier := {j : J | α j = j}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change α (x * y) = x * y
    have hx' : α x = x := hx
    have hy' : α y = y := hy
    rw [map_mul, hx', hy']
  inv_mem' := by
    intro x hx
    change α x⁻¹ = x⁻¹
    have hx' : α x = x := hx
    rw [map_inv, hx']

@[simp]
lemma mem_autFixedSubgroup {J : Type*} [Group J] {α : MulAut J} {j : J} :
    j ∈ autFixedSubgroup α ↔ α j = j :=
  Iff.rfl

def quotientAut {J : Type*} [Group J] (α : MulAut J) :
    MulAut (J ⧸ Subgroup.center J) :=
  QuotientGroup.congr (Subgroup.center J) (Subgroup.center J) α (Subgroup.map_center_eq α)

@[simp]
lemma quotientAut_mk {J : Type*} [Group J] (α : MulAut J) (j : J) :
    quotientAut α (QuotientGroup.mk' (Subgroup.center J) j) =
      QuotientGroup.mk' (Subgroup.center J) (α j) :=
  QuotientGroup.congr_mk _ _ α _ j

def centerAut {J : Type*} [Group J] (α : MulAut J) :
    MulAut (Subgroup.center J) :=
  Subgroup.centerCongr α

@[simp]
lemma centerAut_coe {J : Type*} [Group J] (α : MulAut J) (z : Subgroup.center J) :
    ((centerAut α z : Subgroup.center J) : J) = α z :=
  Subgroup.centerCongr_apply_coe α z

lemma zpowers_self_eq_top {A : Type*} [Group A] (a : A) :
    Subgroup.zpowers (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, Subtype.ext hk⟩

theorem fixedPointSubgroup_eq_autFixedSubgroup_of_zpowers_eq_top
    {A X : Type*} [Group A] [Group X] [MulDistribMulAction A X]
    (a : A) (hgen : Subgroup.zpowers a = ⊤) (τ : MulAut X)
    (h : ∀ x : X, a • x = τ x) :
    fixedPointSubgroup A X = autFixedSubgroup τ := by
  ext x
  rw [mem_autFixedSubgroup]
  constructor
  · intro hfix
    have hgenfix : a • x = x := hfix a
    rwa [h x] at hgenfix
  · intro hfix b
    have hb : b ∈ Subgroup.zpowers a := by rw [hgen]; trivial
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    have hfix' : x ∈ MulAction.fixedBy X a := by
      rw [MulAction.mem_fixedBy, h x]
      exact hfix
    simpa [MulAction.mem_fixedBy] using MulAction.mem_fixedBy_zpow hfix' k

lemma fixedPointSubgroup_zpowers_eq_autFixedSubgroup
    {J : Type*} [Group J] (α : MulAut J) :
    fixedPointSubgroup (Subgroup.zpowers α) J = autFixedSubgroup α :=
  fixedPointSubgroup_eq_autFixedSubgroup_of_zpowers_eq_top
    (a := (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α))
    (zpowers_self_eq_top α) α (fun _ => rfl)

lemma fixedPointSubgroup_quotient_eq_autFixedSubgroup
    {J : Type*} [Group J] (α : MulAut J) :
    letI : (Subgroup.center J).Characteristic := Subgroup.centerCharacteristic
    letI : IsInvariant (Subgroup.zpowers α) J (Subgroup.center J) :=
      isInvariant_of_characteristic (Subgroup.center J)
    letI : MulDistribMulAction (Subgroup.zpowers α) (J ⧸ Subgroup.center J) :=
      quotientMulDistribMulAction (A := Subgroup.zpowers α) (G := J) (Subgroup.center J)
        (inferInstance)
    fixedPointSubgroup (Subgroup.zpowers α) (J ⧸ Subgroup.center J) =
      autFixedSubgroup (quotientAut α) := by
  letI : (Subgroup.center J).Characteristic := Subgroup.centerCharacteristic
  letI hInv : IsInvariant (Subgroup.zpowers α) J (Subgroup.center J) :=
    isInvariant_of_characteristic (Subgroup.center J)
  letI : MulDistribMulAction (Subgroup.zpowers α) (J ⧸ Subgroup.center J) :=
    quotientMulDistribMulAction (A := Subgroup.zpowers α) (G := J) (Subgroup.center J) hInv
  letI : MulAction.QuotientAction (Subgroup.zpowers α) (Subgroup.center J) :=
    quotientAction_of_isInvariant (A := Subgroup.zpowers α) (Subgroup.center J) hInv
  refine fixedPointSubgroup_eq_autFixedSubgroup_of_zpowers_eq_top
    (a := (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α))
    (zpowers_self_eq_top α) (quotientAut α) ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H j =>
    change (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) •
        (↑j : J ⧸ Subgroup.center J) =
      (QuotientGroup.congr (Subgroup.center J) (Subgroup.center J) α
        (Subgroup.map_center_eq α)) (↑j : J ⧸ Subgroup.center J)
    rw [QuotientGroup.congr_mk, MulAction.Quotient.smul_mk]
    congr 1

theorem card_autFixedSubgroup_eq_card_inf_mul_card_quotient
    {J : Type*} [Group J] [Finite J] (α : MulAut J)
    (hcop : Nat.Coprime (orderOf α) (Nat.card J)) :
    Nat.card (autFixedSubgroup α) =
      Nat.card ↥(autFixedSubgroup α ⊓ Subgroup.center J) *
        Nat.card (autFixedSubgroup (quotientAut α)) := by
  classical
  let A := Subgroup.zpowers α
  let Z : Subgroup J := Subgroup.center J
  have hcardA : Nat.card A = orderOf α := Nat.card_zpowers α
  have hcopA : Nat.Coprime (Nat.card A) (Nat.card J) := by
    rw [hcardA]
    exact hcop
  have hcopZ : Nat.Coprime (Nat.card A) (Nat.card Z) :=
    hcopA.coprime_dvd_right (Subgroup.card_subgroup_dvd_card Z)
  have hZchar : Z.Characteristic := Subgroup.centerCharacteristic
  letI : Z.Characteristic := hZchar
  letI hInv : IsInvariant A J Z := isInvariant_of_characteristic Z
  letI : IsMulCommutative Z := Subgroup.center.isMulCommutative (G := J)
  letI : MulDistribMulAction A (J ⧸ Z) :=
    quotientMulDistribMulAction (A := A) (G := J) Z hInv
  have hC : fixedPointSubgroup A J = autFixedSubgroup α := by
    simpa [A] using fixedPointSubgroup_zpowers_eq_autFixedSubgroup (J := J) α
  have hQ : fixedPointSubgroup A (J ⧸ Z) = autFixedSubgroup (quotientAut α) := by
    simpa [A, Z] using fixedPointSubgroup_quotient_eq_autFixedSubgroup (J := J) α
  have hquot : fixedPointSubgroup A (J ⧸ Z) =
      (fixedPointSubgroup A J).map (QuotientGroup.mk' Z) :=
    fixedPointSubgroup_quotient_eq_map_of_isMulCommutative (G := J) (A := A) Z hInv hcopZ
  let C : Subgroup J := fixedPointSubgroup A J
  let f : C →* J ⧸ Z := (QuotientGroup.mk' Z).comp C.subtype
  have hker : f.ker = (Z ⊓ C).subgroupOf C := by
    ext x
    simp [f, Subgroup.mem_subgroupOf, Subgroup.mem_inf, QuotientGroup.eq_one_iff]
  have hkercard : Nat.card ↥f.ker = Nat.card ↥(Z ⊓ C) := by
    rw [hker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : Z ⊓ C ≤ C)).toEquiv
  have hrange : f.range = fixedPointSubgroup A (J ⧸ Z) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hquot.symm
  have hcard := Subgroup.card_ker_mul_card_range f
  have hCcard : Nat.card ↥C = Nat.card (autFixedSubgroup α) := by
    rw [show C = fixedPointSubgroup A J from rfl, hC]
  have hQcard : Nat.card ↥f.range = Nat.card (autFixedSubgroup (quotientAut α)) := by
    rw [hrange, hQ]
  have hinf : Z ⊓ C = autFixedSubgroup α ⊓ Z := by
    rw [show C = fixedPointSubgroup A J from rfl, hC, inf_comm]
  calc Nat.card (autFixedSubgroup α)
      = Nat.card ↥C := hCcard.symm
    _ = Nat.card ↥f.ker * Nat.card ↥f.range := hcard.symm
    _ = Nat.card ↥(Z ⊓ C) * Nat.card (autFixedSubgroup (quotientAut α)) := by
        rw [hkercard, hQcard]
    _ = Nat.card ↥(autFixedSubgroup α ⊓ Z) *
          Nat.card (autFixedSubgroup (quotientAut α)) := by
        rw [hinf]

private abbrev counterexampleC3 : Type := Multiplicative (ZMod 3)

private instance : Fintype counterexampleC3 :=
  Fintype.ofEquiv (ZMod 3) Multiplicative.toAdd.symm

private instance : Finite counterexampleC3 := Finite.of_fintype counterexampleC3

end

end CFSG
