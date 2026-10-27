module

public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.ClassicalInvolution.Q3.TL3Act
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneAutomorphisms

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution
open scoped commutatorElement

theorem eq_one_of_isPerfect_of_isSolvable {H M : Type*} [Group H] [Group M] [Group.IsPerfect H]
    [Group.IsSolvable M] (φ : H →* M) : φ = 1 := by
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Group.IsSolvable φ.range :=
    Group.isSolvable_of_isSolvable_injective (f := φ.range.subtype) φ.range.subtype_injective
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range this
  ext h
  have : (⟨φ h, h, rfl⟩ : φ.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}

theorem datum_quotient_equiv (hD : TightDatum R S t) :
    ∃ m : ℕ, Nonempty ((R ⧸ oddCore R) ≃* QuaternionGroup (2 ^ m)) := by
  obtain ⟨r, -, ⟨eS⟩⟩ := hD.quat
  have hO : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hD.quat hD.mem hD.order hD.cent hD.normal hD.twoGroup
  let eS' : ↥((S : Subgroup R).map R.subtype) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS
  exact ⟨r - 2, ⟨(MulEquiv.ofBijective _ hO.bijective_restrict).symm.trans eS'⟩⟩

theorem datum_commutator_mem (hD : TightDatum R S t) {H : Subgroup X}
    (hHC : H ≤ Subgroup.centralizer ({t} : Set X)) [Group.IsPerfect H] :
    ∀ h ∈ H, ∀ r ∈ R, ⁅h, r⁆ ∈ oddCoreImg R := by
  intro h hh r hr
  obtain ⟨m, ⟨e⟩⟩ := datum_quotient_equiv hD
  have : Group.IsSolvable (MulAut (QuaternionGroup (2 ^ m))) :=
    ProperTwoGeneratedCore.quaternion_power_two_automorphism_solvable m
  have : Group.IsSolvable (MulAut (R ⧸ oddCore R)) :=
    Group.isSolvable_of_isSolvable_injective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).injective
  have hle : H ≤ Subgroup.normalizer (R : Set X) := hHC.trans hD.le_normalizer
  have hφ := eq_one_of_isPerfect_of_isSolvable ((tl3Act R).comp (Subgroup.inclusion hle))
  have h1 : tl3Act R ⟨h, hle hh⟩ = 1 := DFunLike.congr_fun hφ ⟨h, hh⟩
  exact (tl3Act_eq_one_iff R ⟨h, hle hh⟩).mp h1 r hr

theorem datum_commute_of_perfect (hD : TightDatum R S t) {H : Subgroup X}
    (hHC : H ≤ Subgroup.centralizer ({t} : Set X)) [Group.IsPerfect H]
    (hO : ∀ x ∈ oddCoreImg R, ∀ h ∈ H, x * h = h * x) :
    ∀ r ∈ R, ∀ h ∈ H, r * h = h * r := by
  intro r hr
  have hc := datum_commutator_mem hD hHC
  let φ : H →* oddCoreImg R :=
    { toFun := fun h => ⟨⁅(h : X), r⁆⁻¹, (oddCoreImg R).inv_mem (hc h h.2 r hr)⟩
      map_one' := by ext; simp [commutatorElement_def]
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb : ⁅(b : X), r⁆ * a = a * ⁅(b : X), r⁆ := hO _ (hc b b.2 r hr) a a.2
        have key : ⁅(a : X) * b, r⁆ = ⁅(b : X), r⁆ * ⁅(a : X), r⁆ := by
          have e : ⁅(a : X) * b, r⁆ = (a : X) * ⁅(b : X), r⁆ * (a : X)⁻¹ * ⁅(a : X), r⁆ := by
            simp only [commutatorElement_def]; group
          rw [e, ← hb]; group
        simp only [MulMemClass.coe_mul]
        rw [key, mul_inv_rev] }
  have : Group.IsSolvable (oddCoreImg R) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_natCard_oddCoreImg R)
  have hφ := eq_one_of_isPerfect_of_isSolvable φ
  intro h hh
  have h1 : ⁅h, r⁆⁻¹ = 1 := congrArg Subtype.val (DFunLike.congr_fun hφ ⟨h, hh⟩)
  have h2 : ⁅h, r⁆ = 1 := inv_eq_one.mp h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

end CFSG.ClassicalInvolution.Q3.TA3
