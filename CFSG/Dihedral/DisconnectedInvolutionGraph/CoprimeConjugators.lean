module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.FixedPairTransitivity
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

@[expose] def conjugateImage (subgroup : Subgroup G) (element : G) : Subgroup G :=
  subgroup.map (MulAut.conj element).toMonoidHom

theorem conjugateImage_mul (subgroup : Subgroup G) (first second : G) :
    conjugateImage subgroup (first * second) =
      conjugateImage (conjugateImage subgroup second) first := by
  unfold conjugateImage
  rw [Subgroup.map_map]
  congr 1
  ext element
  change (first * second) * element * (first * second)⁻¹ =
    first * (second * element * second⁻¹) * first⁻¹
  simp only [mul_inv_rev, mul_assoc]

theorem conjugateImage_one (subgroup : Subgroup G) : conjugateImage subgroup 1 = subgroup := by
  unfold conjugateImage
  have hidentity : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext element
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one,
      MonoidHom.id_apply]
  rw [hidentity, Subgroup.map_id]

abbrev SubgroupTransporter (source target : Subgroup G) :=
  {element : G // conjugateImage source element = target}

def subgroupTransporterEquivNormalizer (source target : Subgroup G) (base : G)
    (hbase : conjugateImage source base = target) :
    ↥(Subgroup.normalizer (source : Set G)) ≃ SubgroupTransporter source target where
  toFun element := ⟨base * element.val, by
    rw [conjugateImage_mul]
    have hnormalizes := Subgroup.mem_normalizer_iff_map_conj_eq.mp element.property
    change conjugateImage (conjugateImage source element.val) base = target
    rw [show conjugateImage source element.val = source from hnormalizes, hbase]⟩
  invFun element := ⟨base⁻¹ * element.val, by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change conjugateImage source (base⁻¹ * element.val) = source
    rw [conjugateImage_mul, element.property, ← hbase, ← conjugateImage_mul,
      inv_mul_cancel, conjugateImage_one]⟩
  left_inv element := by
    apply Subtype.ext
    exact inv_mul_cancel_left base element.val
  right_inv element := by
    apply Subtype.ext
    exact mul_inv_cancel_left base element.val

variable {A : Type*} [Group A] [MulDistribMulAction A G]

theorem invariant_subgroup_transporter (source target : Subgroup G)
    (hsource : InvariantSubgroup (A := A) source)
    (htarget : InvariantSubgroup (A := A) target) (actor : A) (element : G)
    (htransports : conjugateImage source element = target) :
    conjugateImage source (actor • element) = target := by
  ext other
  constructor
  · intro hmem
    obtain ⟨original, horiginal, hconj⟩ := Subgroup.mem_map.mp hmem
    have hpreimage : (MulAut.conj element) (actor⁻¹ • original) ∈ target := by
      rw [← htransports]
      exact Subgroup.mem_map.mpr
        ⟨actor⁻¹ • original, hsource actor⁻¹ original horiginal, rfl⟩
    have himage := htarget actor _ hpreimage
    rw [← hconj]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_mul', smul_inv',
      smul_inv_smul] using himage
  · intro hmem
    have hpreimage := htarget actor⁻¹ other hmem
    rw [← htransports] at hpreimage
    obtain ⟨original, horiginal, hconj⟩ := Subgroup.mem_map.mp hpreimage
    refine Subgroup.mem_map.mpr ⟨actor • original, hsource actor original horiginal, ?_⟩
    have himage := congrArg (fun value : G => actor • value) hconj
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_mul', smul_inv',
      smul_inv_smul] using himage

@[instance_reducible]
def subgroupTransporterAction (source target : Subgroup G)
    (hsource : InvariantSubgroup (A := A) source)
    (htarget : InvariantSubgroup (A := A) target) :
    MulAction A (SubgroupTransporter source target) where
  smul actor element := ⟨actor • element.val,
    invariant_subgroup_transporter source target hsource htarget actor element.val element.property⟩
  one_smul element := Subtype.ext (one_smul A element.val)
  mul_smul first second element := Subtype.ext (mul_smul first second element.val)

theorem coprime_pgroup_fixed_conjugator [Finite G] (prime : ℕ) [Fact (Nat.Prime prime)]
    (hpgroup : IsPGroup prime A) (hcoprime : ¬ prime ∣ Nat.card G)
    (source target : Subgroup G) (hsource : InvariantSubgroup (A := A) source)
    (htarget : InvariantSubgroup (A := A) target)
    (hconjugate : ∃ element : G, conjugateImage source element = target) :
    ∃ element : G, (∀ actor : A, actor • element = element) ∧
      conjugateImage source element = target := by
  obtain ⟨base, hbase⟩ := hconjugate
  let _ : MulAction A (SubgroupTransporter source target) :=
    subgroupTransporterAction source target hsource htarget
  have hcard : Nat.card (SubgroupTransporter source target) =
      Nat.card ↥(Subgroup.normalizer (source : Set G)) :=
    Nat.card_congr (subgroupTransporterEquivNormalizer source target base hbase).symm
  have hnotdvd : ¬ prime ∣ Nat.card (SubgroupTransporter source target) := by
    rw [hcard]
    intro hdiv
    exact hcoprime (hdiv.trans (Subgroup.normalizer (source : Set G)).card_subgroup_dvd_card)
  obtain ⟨element, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card
    (SubgroupTransporter source target) hnotdvd
  refine ⟨element.val, ?_, element.property⟩
  intro actor
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hfixed actor)

theorem coprime_pgroup_invariant_sylows_conjugate [Finite G]
    (actorPrime sylowPrime : ℕ) [Fact (Nat.Prime actorPrime)] [Fact (Nat.Prime sylowPrime)]
    (hpgroup : IsPGroup actorPrime A) (hcoprime : ¬ actorPrime ∣ Nat.card G)
    (source target : Sylow sylowPrime G)
    (hsource : InvariantSubgroup (A := A) (source : Subgroup G))
    (htarget : InvariantSubgroup (A := A) (target : Subgroup G)) :
    ∃ element : G, (∀ actor : A, actor • element = element) ∧ element • source = target := by
  obtain ⟨base, hbase⟩ := MulAction.exists_smul_eq G source target
  have hconjugate : ∃ element : G,
      conjugateImage (source : Subgroup G) element = (target : Subgroup G) := by
    refine ⟨base, ?_⟩
    rw [conjugateImage, ← sylow_smul_subgroup_eq_map, hbase]
  obtain ⟨element, hfixed, htransports⟩ := coprime_pgroup_fixed_conjugator actorPrime hpgroup
    hcoprime (source : Subgroup G) (target : Subgroup G) hsource htarget hconjugate
  refine ⟨element, hfixed, ?_⟩
  apply Sylow.ext
  rw [sylow_smul_subgroup_eq_map]
  exact htransports

end CFSG.DisconnectedInvolutionGraph.Helpers
