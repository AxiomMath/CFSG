module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorusEichler
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Chamber
import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Supported
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmMS1

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open QuadraticMap CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.FramedPlanes

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem mem_normBlock_iff_fixes_suppPerp {n : ℕ} {S : Finset (Fin n)} (hS : 2 ≤ S.card)
    (g : normOmega E n) :
    g ∈ normBlock E n S ↔ ∀ v ∈ suppPerp (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S),
        (g : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v = v := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  rw [normBlock, Subgroup.mem_subgroupOf,
    mem_supportedDerived_iff_mem_orthDerived (Q := normHypForm E n)
      (normHypForm_polarBilin_nondegenerate E n)
      (coordSupport_nondegenerate (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (hψ := normHypForm_apply_coord E n)
        (hQ := normHypForm_polarBilin_nondegenerate E n)
        (hQE := normQuad_polarBilin_nondegenerate E) S)
      (exists_totallySingular_coordSupport E S hS)]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem eichler_mem_normBlock {n : ℕ} (hn : 2 ≤ n) {S : Finset (Fin n)} (hS : 2 ≤ S.card)
    {u w : (F × F) × (Fin n → K)}
    (hu : u ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S)
    (hw : w ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) :
    (⟨eichler (normHypForm E n) u w, eichler_mem_normOmega E hn u w⟩ : normOmega E n) ∈
      normBlock E n S := by
  rw [mem_normBlock_iff_fixes_suppPerp E hS]
  intro v hv
  have hvu : polar (normHypForm E n) v u = 0 := by
    rw [polar_comm]
    exact mem_suppPerp.mp hv u hu
  have hvw : polar (normHypForm E n) v w = 0 := by
    rw [polar_comm]
    exact mem_suppPerp.mp hv w hw
  exact eichler_apply_of_polar_eq_zero hvu hvw

theorem fixes_anchor_of_commute_normBlock {n : ℕ} (hn : 2 ≤ n) {S : Finset (Fin n)}
    (hS : 2 ≤ S.card) {a : normOmega E n} (ha : ∀ b ∈ normBlock E n S, Commute a b) :
    ∀ w : F × F,
      (a : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (w, 0) = (w, 0) := by
  classical
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  obtain ⟨k, hk⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  let V := (F × F) × (Fin n → K)
  let x : V := (0, Pi.single k 1)
  have hxS : x ∈ coordSupport (LinearEquiv.refl F V) S := by
    rw [mem_coordSupport_refl_iff E S]
    intro j hj
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    simp [x, Pi.single_eq_of_ne hjk]
  have hQx : normHypForm E n x ≠ 0 := by
    rw [show normHypForm E n x = normQuad E 1 from normHypForm_zero_single E n k 1,
      normQuad_one]
    exact one_ne_zero
  have hO : (a : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n) :=
    Subgroup.commutator_le_self _ a.2
  have hfix : ∀ v : F × F, v.1 * v.2 = 0 → v ≠ 0 →
      (a : V ≃ₗ[F] V) (v, 0) = (v, 0) := by
    intro v hv hv0
    have hvS : ((v, 0) : V) ∈ coordSupport (LinearEquiv.refl F V) S := by
      rw [mem_coordSupport_refl_iff E S]
      intro j _
      rfl
    have hQv : normHypForm E n ((v, 0) : V) = 0 := by
      rw [normHypForm_apply_coord]
      simp [CFSG.Timmesfeld.ClassicalOrders.hypPlane_apply, hv]
    have hvx : polar (normHypForm E n) ((v, 0) : V) x = 0 := by
      rw [normHypForm, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum]
      simp [x]
    have hcomm : ∀ y : V, (a : V ≃ₗ[F] V) (eichler (normHypForm E n) (v, 0) x y) =
        eichler (normHypForm E n) (v, 0) x ((a : V ≃ₗ[F] V) y) := by
      intro y
      have h := ha _ (eichler_mem_normBlock E hn hS hvS hxS)
      have h' := congrArg (fun g : normOmega E n => (g : V ≃ₗ[F] V) y) h.eq
      simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using h'
    exact (CFSG.StandardType.RCKC1.rckSOmM1_commute_fixes
      (normHypForm_polarBilin_nondegenerate E n) hQv hvx hQx
      (by simpa using hv0) hO hcomm).1
  have he : (a : V ≃ₗ[F] V) ((1, 0), 0) = ((1, 0), 0) :=
    hfix (1, 0) (by simp) (by simp)
  have hf : (a : V ≃ₗ[F] V) ((0, 1), 0) = ((0, 1), 0) :=
    hfix (0, 1) (by simp) (by simp)
  intro w
  have hw : ((w, 0) : V) = w.1 • (((1, 0), 0) : V) + w.2 • (((0, 1), 0) : V) := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp
  rw [hw, map_add, map_smul, map_smul, he, hf]

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
