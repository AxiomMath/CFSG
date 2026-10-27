module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3TwinBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3Pure

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW

namespace ThmE

namespace EndGame

section Quat

variable {G : Type} [Group G]

theorem exists_q8Hom {r : ℕ} (hr : 3 ≤ r) {P : Subgroup G}
    (e : ↥P ≃* QuaternionGroup (2 ^ (r - 2))) :
    ∃ ι : QuaternionGroup 2 →* G, Function.Injective ι ∧ (∀ q, ι q ∈ P) ∧
      ι (QuaternionGroup.a 2) = ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥P) : G) := by
  obtain ⟨h, hh, hpos⟩ : ∃ h : ℕ, 2 ^ (r - 2) = h + h ∧ 0 < h :=
    ⟨2 ^ (r - 3), by rw [show r - 2 = (r - 3) + 1 by omega, pow_succ]; ring, by positivity⟩
  refine ⟨P.subtype.comp (e.symm.toMonoidHom.comp (q8ToQuat _ h hh)),
    Subtype.val_injective.comp (e.symm.injective.comp (q8ToQuat_injective _ h hh hpos)),
    fun q => (e.symm (q8ToQuat _ h hh q)).2, ?_⟩
  show ((e.symm (q8ToQuat _ h hh (QuaternionGroup.a 2)) : ↥P) : G) = _
  rw [q8ToQuat_a_two, QSub.Alg.z_eq e]

theorem exists_subgroup_q8 {r : ℕ} (hr : 3 ≤ r) {P : Subgroup G}
    (e : ↥P ≃* QuaternionGroup (2 ^ (r - 2))) :
    ∃ Q : Subgroup G, Q ≤ P ∧ Nonempty (↥Q ≃* QuaternionGroup 2) := by
  obtain ⟨ι, hι, hP, -⟩ := exists_q8Hom hr e
  exact ⟨ι.range, by rintro _ ⟨q, rfl⟩; exact hP q, ⟨(MonoidHom.ofInjective hι).symm⟩⟩

theorem u3QTriple_of_q8Hom {ι : QuaternionGroup 2 →* G} (hι : Function.Injective ι) {z : G}
    (hz : ι (QuaternionGroup.a 2) = z) :
    U3QTriple z (ι (QuaternionGroup.a 1)) (ι (QuaternionGroup.xa 0)) := by
  refine ⟨?_, ?_, ?_, fun h => ?_⟩
  · rw [← map_mul, ← hz]
    congr 1
  · rw [← map_mul, ← hz]
    congr 1
  · rw [← map_mul, ← map_mul, ← hz]
    congr 1
  · rw [← map_mul, ← map_mul] at h
    revert h
    have := hι.ne (show (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 by decide)
    exact this

theorem exists_u3QTriple_quat {r : ℕ} (hr : 3 ≤ r) {K R : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hRK : R ≤ K) (e : ↥R ≃* QuaternionGroup (2 ^ (r - 2))) :
    ∃ a ∈ R, ∃ b ∈ R, U3QTriple z a b := by
  obtain ⟨ι, hι, hR, hιz⟩ := exists_q8Hom hr e
  have hzR : ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥R) : G) = z :=
    ((hz.unique _ (hRK (e.symm _).2) (QSub.Alg.z_mul_self e)).resolve_left
      (QSub.Alg.z_ne_one e))
  exact ⟨_, hR _, _, hR _, u3QTriple_of_q8Hom hι (hιz.trans hzR)⟩

end Quat

end EndGame

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
