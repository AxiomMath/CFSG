module

public import CFSG.Adapters.TauCetiExceptional.EvenBlockEndgame
public import CFSG.Adapters.TauCetiExceptional.EvenMono
public import CFSG.Adapters.TauCetiExceptional.EvenInterface
public import CFSG.Adapters.TauCetiExceptional.TwistedD4Push
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell Twisted
open TauCeti.DynkinType

theorem d4Wt_refl (i : Fin (Tag.rank .D4)) (b : Fin 24) :
    d4Wt (d4TripledReflection (d4Node.symm i) b) i = -d4Wt b i := by
  rw [d4Wt, d4Wt, d4TripledWeight_reflection_apply]
  have h2 : CartanMatrix.D 4 (d4Node.symm i) (d4Node.symm i) = 2 := by
    rw [CartanMatrix.D_four]
    revert i
    decide
  rw [h2]
  ring

@[expose] def d4Mono (L : Type) [Field L] : MonoRoots L 24 (Tag.rank .D4) where
  E := d4E L
  F := d4F L
  wt := d4Wt
  refl i := d4TripledReflection (d4Node.symm i)
  E_apply i a b := by
    rw [d4E, Matrix.map_apply, D4Tripled.raisingMatrix_apply, d4Wt]
    split_ifs <;> simp
  F_apply i a b := by
    rw [d4F, Matrix.map_apply, D4Tripled.loweringMatrix_apply, d4Wt]
    split_ifs <;> simp
  refl_refl i b := d4TripledReflection_apply_apply _ b
  wt_refl := d4Wt_refl

theorem d4_isDiag_of_commute_two {L : Type} [Field L] {z : Matrix (Fin 24) (Fin 24) L}
    (hE : ∀ i, z * d4E L i = d4E L i * z) (hF : ∀ i, z * d4F L i = d4F L i * z) {a b : Fin 24}
    (hab : a ≠ b) : z a b = 0 :=
  (d4Mono L).isDiag_of_commute d4Wt_injective d4Wt_mem hE hF hab

theorem d4_heads : ∀ h : Fin 24, (∀ i, d4Wt h i ≠ -1) →
    ∀ b, d4Blk b = d4Blk h → b ≠ h → ∃ i, d4Wt b i = -1 := by
  decide +kernel

theorem d4_head_excl : ∀ π' : Equiv.Perm (Fin (Tag.rank .D4)),
    (∀ ij : Fin (Tag.rank .D4) × Fin (Tag.rank .D4),
      Tag.cartan .D4 (π' ij.1) (π' ij.2) = Tag.cartan .D4 ij.1 ij.2) →
    (∀ h : Fin 24, (∀ i, d4Wt h i ≠ -1) → ∀ j, (d4Wt h j = 1 ↔ d4Wt h (π' j) = 1)) →
      π' = 1 := by
  decide +kernel

namespace D4PushDown

variable {L : Type} [Field L] (P : Twisted.D4PushDown L)

theorem mem_center_of_commute_two
    {z : ↥(D4Tripled.points L)}
    (h : ∀ i, ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) *
        d4E L i = d4E L i * ((z : Matrix.GeneralLinearGroup (Fin 24) L) :
          Matrix (Fin 24) (Fin 24) L) ∧
      ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) * d4F L i =
        d4F L i * ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L)) :
    z ∈ Subgroup.center ↥(D4Tripled.points L) := by
  have hdiag : ∀ a b, a ≠ b →
      ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) a b = 0 :=
    fun a b hab => d4_isDiag_of_commute_two (fun i => (h i).1) (fun i => (h i).2) hab
  rw [Subgroup.mem_center_iff]
  intro w
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact (commute_of_diag d4Blk hdiag
    (fun a b hab => d4_diag_eq_of_commute hdiag (fun i => (h i).1) (fun i => (h i).2) hab)
    (d4_points_isBlockDiag L _ w.2)).symm

@[expose] def blockCarrierTwo :
    BlockCarrier .D4 L 24 3 where
  C := D4Tripled.points L
  π := P.π
  u := Twisted.D4PushDown.u
  v := Twisted.D4PushDown.v
  E := d4E L
  F := d4F L
  coe_u := Twisted.D4PushDown.coe_u
  coe_v := Twisted.D4PushDown.coe_v
  u_add i c d := by simp only [Twisted.D4PushDown.u, ofAdd_add, map_mul]
  v_add i c d := by simp only [Twisted.D4PushDown.v, ofAdd_add, map_mul]
  π_u i c := by rw [P.π_u, Equiv.apply_symm_apply]
  π_v i c := by rw [P.π_v, Equiv.apply_symm_apply]
  blk := d4Blk
  block z := d4_points_isBlockDiag L _ z.2
  ker_diag z hz _ _ hab :=
    d4_isDiag_of_commute_two (fun i => ((P.ker_iff z).1 hz i).1)
      (fun i => ((P.ker_iff z).1 hz i).2) hab
  ker_center z hz := mem_center_of_commute_two ((P.ker_iff z).1 hz)
  wt := d4Wt
  wt_mem := d4Wt_mem
  comm := d4E_comm L
  comm_HE := d4E_commH L
  E_ne := d4E_ne_zero L
  cartan_off := cartan_D4_off
  excl := d4_excl

end D4PushDown

theorem exclTwo_d4
    {L : Type} [Field L] (P : Twisted.D4PushDown L) :
    ExclTwo (D4PushDown.blockCarrierTwo P) := by
  intro z π' c hc hcart hE hF
  refine d4_head_excl π' (fun ij => hcart ij.1 ij.2) fun h hh j => ?_
  exact (d4Mono L).wt_eq_one_iff_of_conj d4Blk ((D4PushDown.blockCarrierTwo P).mat_inv_mul z)
    ((D4PushDown.blockCarrierTwo P).block z) π' hc hE hF hh (d4_heads h hh) j

variable {q : PrimePower} {hv : (LieTypeIndex.trialityD4 q).Valid}

theorem isTwistedIsogeny_steinberg_two
    (P : Twisted.D4PushDown (d4Closure q hv)) (hp2 : q.p = 2) :
    IsTwistedIsogeny .D4 (d4Closure q hv) (d4Fr q hv) (d4Index q hv).steinberg P.π := by
  have hp2' : d4Char q hv = 2 := by rw [d4Char_eq]; exact hp2
  refine isTwistedIsogeny_two (t := .D4) (D4PushDown.blockCarrierTwo P) (p := d4Char q hv) hp2'
    (by decide) (exclTwo_d4 P) P.zeros (d4Index q hv).steinberg (d4Fr q hv) d4_steinberg_u
    d4_steinberg_v fun k hk => ?_
  apply P.π_eq_one_of_mem_center
  have hc := Subgroup.mem_center_iff.1 ((D4PushDown.blockCarrierTwo P).ker_center k hk)
  refine Subgroup.mem_center_iff.2 fun w => ?_
  obtain ⟨w', rfl⟩ := d4_steinberg_surjective w
  exact ((map_mul _ w' k).symm.trans (congrArg (d4Index q hv).steinberg (hc w'))).trans
    (map_mul _ k w')

theorem nonempty_mulEquiv_group_trialityD4_two
    (P : Twisted.D4PushDown (d4Closure q hv))
    (hp2 : q.p = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card ^ TwistTag.D4.order) (σ : K →+* K) (hσ : ∀ x, σ x = x ^ q.card) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ) ≃*
      ValidLieTypeIndex.Group ⟨LieTypeIndex.trialityD4 q, hv⟩) := by
  set p := d4Char q hv with hpdef
  set f := ValidLieTypeIndex.fieldExponent ⟨_, hv⟩ with hfdef
  have hq : q.card = p ^ f := by
    rw [← LieTypeIndex.fieldOrder_trialityD4 q]
    exact ValidLieTypeIndex.fieldOrder_eq_characteristic_pow ⟨_, hv⟩
  have hp : p.Prime := Fact.out
  have hf : 1 ≤ f := ValidLieTypeIndex.fieldExponent_pos ⟨_, hv⟩
  have hK' : Nat.card K = (p ^ f) ^ TwistTag.D4.order := by rw [hK, hq]
  have hσ' : ∀ c, σ c = c ^ (p ^ f) := fun c => by rw [hσ, hq]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := f * 3) (by omega) (by rw [hK', pow_mul]; rfl)
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : Algebra.IsAlgebraic (ZMod p) K := Algebra.IsAlgebraic.of_finite (ZMod p) K
  let ι : K →ₐ[ZMod p] d4Closure q hv := IsAlgClosed.lift
  let : Algebra K (d4Closure q hv) := ι.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) K (d4Closure q hv) :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic K (d4Closure q hv) :=
    Algebra.IsAlgebraic.tower_top (K := ZMod p) K
  have : IsAlgClosure K (d4Closure q hv) := ⟨inferInstance, inferInstance⟩
  have hFr : ∀ c, d4Fr q hv c = c ^ (p ^ f) := fun c => by rw [iterateFrobenius_def]
  obtain ⟨e⟩ := nonempty_derivedCentralQuotient_equiv (t := .D4) (d4Closure q hv) (d4Fr q hv) hp
    hf hK' hσ' hFr (isTwistedIsogeny_steinberg_two P hp2)
  exact ⟨e.symm⟩

theorem twistedBridgeEven_trialityD4
    : TwistedBridgeEven .D4 LieTypeIndex.trialityD4 :=
  fun q hv hp2 K _ _ hK σ hσ =>
    nonempty_mulEquiv_group_trialityD4_two (d4PushDown (d4Closure q hv)) hp2 K hK σ hσ

end CFSG.TauCetiBridge.Even
