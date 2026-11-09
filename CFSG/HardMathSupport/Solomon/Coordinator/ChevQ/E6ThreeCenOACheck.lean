module

public import CFSG.LieType.Steinberg.Adjoint.IformFast
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjOrbit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Adjoint (iform)

private local instance e6CenOA_neZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def E6CenPlanePat (x y : Fin Tag.E6.rank → ZMod 3) : Prop :=
  (e6KerCount x = 18 ∧ e6KerCount y = 18 ∧ e6KerCount (x + y) = 18 ∧
      e6KerCount (x + y + y) = 18) ∨
    (e6KerCount x = 30 ∨ e6KerCount y = 30 ∨ e6KerCount (x + y) = 30 ∨
      e6KerCount (x + y + y) = 30) ∨
    (e6KerCount x = 18 ∧ e6KerCount y = 24 ∧ e6KerCount (x + y) = 24 ∧
      e6KerCount (x + y + y) = 24) ∨
    (e6KerCount x = 24 ∧ e6KerCount y = 18 ∧ e6KerCount (x + y) = 24 ∧
      e6KerCount (x + y + y) = 24) ∨
    (e6KerCount x = 24 ∧ e6KerCount y = 24 ∧ e6KerCount (x + y) = 18 ∧
      e6KerCount (x + y + y) = 24) ∨
    (e6KerCount x = 24 ∧ e6KerCount y = 24 ∧ e6KerCount (x + y) = 24 ∧
      e6KerCount (x + y + y) = 18)

private local instance e6CenOA_decPlanePat (x y : Fin Tag.E6.rank → ZMod 3) :
    Decidable (E6CenPlanePat x y) := by
  unfold E6CenPlanePat
  infer_instance

private def e6KerNv (x : Fin Tag.E6.rank → ZMod 3) : ℕ :=
  e6KerN (x 0).val (x 1).val (x 2).val (x 3).val (x 4).val (x 5).val

private def E6CenPlanePatN (x y : Fin Tag.E6.rank → ZMod 3) : Prop :=
  (e6KerNv x = 18 ∧ e6KerNv y = 18 ∧ e6KerNv (x + y) = 18 ∧
      e6KerNv (x + y + y) = 18) ∨
    (e6KerNv x = 30 ∨ e6KerNv y = 30 ∨ e6KerNv (x + y) = 30 ∨
      e6KerNv (x + y + y) = 30) ∨
    (e6KerNv x = 18 ∧ e6KerNv y = 24 ∧ e6KerNv (x + y) = 24 ∧
      e6KerNv (x + y + y) = 24) ∨
    (e6KerNv x = 24 ∧ e6KerNv y = 18 ∧ e6KerNv (x + y) = 24 ∧
      e6KerNv (x + y + y) = 24) ∨
    (e6KerNv x = 24 ∧ e6KerNv y = 24 ∧ e6KerNv (x + y) = 18 ∧
      e6KerNv (x + y + y) = 24) ∨
    (e6KerNv x = 24 ∧ e6KerNv y = 24 ∧ e6KerNv (x + y) = 24 ∧
      e6KerNv (x + y + y) = 18)

private local instance e6CenOA_decPlanePatN (x y : Fin Tag.E6.rank → ZMod 3) :
    Decidable (E6CenPlanePatN x y) := by
  unfold E6CenPlanePatN
  infer_instance

private theorem e6CenPlanePat_iff (x y : Fin Tag.E6.rank → ZMod 3) :
    E6CenPlanePat x y ↔ E6CenPlanePatN x y := by
  simp only [E6CenPlanePat, E6CenPlanePatN, e6KerNv, e6KerCount_eq]

theorem e6Cen_OA_planePat : ∀ t e1 e3 e4 m c : ZMod 3, t ≠ 0 → (m ≠ 0 ∨ c ≠ 0) →
    E6CenPlanePat (e6ConjVec 0 m 0 c (2 * m) (2 * m)) (e6ConjVec t e1 t e3 e4 e4) := by
  simp only [e6CenPlanePat_iff]
  decide +kernel

private theorem e6CenOA_coroot_listed : ∀ a b c d e f : ZMod 3,
    e6KerCount (e6ConjVec a b c d e f) = 30 → ∃ k < 72, ∀ j, e6ConjVec a b c d e f j =
      ((iform (e6Certificate.root k) (Pi.single j 1) : ℤ) : ZMod 3) := by
  simp only [e6KerCount_eq, CFSG.LieType.Steinberg.Adjoint.iform_eq_iform6]
  decide +kernel

theorem e6Cen_coroot_of_kerCount (x : Fin Tag.E6.rank → ZMod 3)
    (hx : e6KerCount x = 30) :
    ∃ ρ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 ρ ∧
      ∀ j, x j = ((iform ρ (Pi.single j 1) : ℤ) : ZMod 3) := by
  have hx' : x = e6ConjVec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨k, hk, hkx⟩ := e6CenOA_coroot_listed (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (by rw [← hx']; exact hx)
  have hlen : e6Certificate.roots.length = 72 := by decide
  exact ⟨e6Certificate.root k, RootCertificate.isRoot_root e6Certificate_check k (hlen ▸ hk),
    fun j => (congrFun hx' j).trans (hkx j)⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
