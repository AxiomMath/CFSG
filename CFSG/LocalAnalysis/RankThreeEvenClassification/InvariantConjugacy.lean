module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem subgroup_map_conj_mul {G : Type u} [Group G]
    (subgroup : Subgroup G) (first second : G) :
    subgroup.map (MulAut.conj (first * second)).toMonoidHom =
      (subgroup.map (MulAut.conj second).toMonoidHom).map (MulAut.conj first).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext element
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev, mul_assoc]

def conjugatorEquivNormalizer {G : Type u} [Group G]
    (first second : Subgroup G) (representative : G)
    (hrepresentative : first.map (MulAut.conj representative).toMonoidHom = second) :
    Subgroup.normalizer (first : Set G) ≃
      {conjugator : G // first.map (MulAut.conj conjugator).toMonoidHom = second} where
  toFun member := ⟨representative * member, by
    rw [subgroup_map_conj_mul]
    have hfixed : first.map (MulAut.conj (member : G)).toMonoidHom = first :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp member.property
    rw [hfixed, hrepresentative]⟩
  invFun conjugator := ⟨representative⁻¹ * conjugator, by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change first.map (MulAut.conj (representative⁻¹ * conjugator)).toMonoidHom = first
    rw [subgroup_map_conj_mul, conjugator.property, ← hrepresentative,
      ← subgroup_map_conj_mul, inv_mul_cancel]
    have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext element
      simp
    rw [hone, Subgroup.map_id]
    ⟩
  left_inv member := Subtype.ext (inv_mul_cancel_left representative member)
  right_inv conjugator := Subtype.ext (mul_inv_cancel_left representative conjugator)

theorem action_subgroup_conjugate_map {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (subgroup : Subgroup acted) (member : actor) (conjugator : acted) :
    (subgroup.map (MulAut.conj conjugator).toMonoidHom).map
        (MulDistribMulAction.toMonoidHom acted member) =
      (subgroup.map (MulDistribMulAction.toMonoidHom acted member)).map
        (MulAut.conj (member • conjugator)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext element
  change member • (conjugator * element * conjugator⁻¹) =
    (member • conjugator) * (member • element) * (member • conjugator)⁻¹
  rw [smul_mul', smul_mul', smul_inv']

theorem exists_fixed_conjugator_of_pGroup_prime_complement_action
    {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (first second : Subgroup acted)
    (hfirst : ∀ member : actor, first.map (MulDistribMulAction.toMonoidHom acted member) = first)
    (hsecond : ∀ member : actor, second.map (MulDistribMulAction.toMonoidHom acted member) = second)
    (hconjugate : ∃ conjugator : acted, first.map (MulAut.conj conjugator).toMonoidHom = second) :
    ∃ conjugator : acted, (∀ member : actor, member • conjugator = conjugator) ∧
      first.map (MulAut.conj conjugator).toMonoidHom = second := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨representative, hrepresentative⟩ := hconjugate
  let transporter := {conjugator : acted // first.map (MulAut.conj conjugator).toMonoidHom = second}
  have hinvariant : ∀ member : actor, ∀ conjugator : transporter,
      first.map (MulAut.conj (member • (conjugator : acted))).toMonoidHom = second := by
    intro member conjugator
    have hmapped := congrArg (fun subgroup : Subgroup acted =>
      subgroup.map (MulDistribMulAction.toMonoidHom acted member)) conjugator.property
    rw [action_subgroup_conjugate_map, hfirst, hsecond] at hmapped
    exact hmapped
  let action : MulAction actor transporter :=
    { smul := fun member conjugator => ⟨member • (conjugator : acted), hinvariant member conjugator⟩
      one_smul := fun conjugator => Subtype.ext (one_smul actor (conjugator : acted))
      mul_smul := fun first second conjugator => Subtype.ext (mul_smul first second (conjugator : acted)) }
  let : MulAction actor transporter := action
  have hcard : Nat.card transporter = Nat.card (Subgroup.normalizer (first : Set acted)) :=
    (Nat.card_congr (conjugatorEquivNormalizer first second representative hrepresentative)).symm
  have htransporterComplement : ¬prime ∣ Nat.card transporter := by
    rw [hcard]
    exact fun hdiv => hcomplement (hdiv.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨conjugator, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card transporter
    htransporterComplement
  refine ⟨conjugator, ?_, conjugator.property⟩
  intro member
  exact congrArg (fun value : transporter => (value : acted)) (MulAction.mem_fixedPoints.mp hfixed member)

theorem exists_fixed_conjugator_of_invariant_sylows
    {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime)
    (first second : Sylow sylowPrime acted)
    (hfirst : ∀ member : actor, (first : Subgroup acted).map
      (MulDistribMulAction.toMonoidHom acted member) = first)
    (hsecond : ∀ member : actor, (second : Subgroup acted).map
      (MulDistribMulAction.toMonoidHom acted member) = second) :
    ∃ conjugator : acted, (∀ member : actor, member • conjugator = conjugator) ∧
      (first : Subgroup acted).map (MulAut.conj conjugator).toMonoidHom = second := by
  have : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq acted first second
  apply exists_fixed_conjugator_of_pGroup_prime_complement_action prime hprime hpgroup hcomplement
    first second hfirst hsecond
  refine ⟨conjugator, ?_⟩
  have hmapped := congrArg (fun sylow : Sylow sylowPrime acted => (sylow : Subgroup acted)) hconjugator
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hmapped
  exact hmapped

end CFSG.RankThreeEvenClassification.Helpers
