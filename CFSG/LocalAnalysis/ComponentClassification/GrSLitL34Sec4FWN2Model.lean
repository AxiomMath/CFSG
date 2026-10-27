module

public import Certificates.Certificate22256
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit.FW

open CFSG CFSG.ComponentClassification.PSL3Four

theorem involution_closure_S
    (P : Equiv.Perm (Fin 42) → Prop)
    (hP : ∀ x y, x ∈ S → y ∈ S → x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x * y = y * x →
      P x → P y)
    {x₀ : Equiv.Perm (Fin 42)} (hx₀S : x₀ ∈ S) (hx₀2 : x₀ * x₀ = 1) (hx₀1 : x₀ ≠ 1)
    (h₀ : P x₀) : ∀ y ∈ S, y * y = 1 → y ≠ 1 → P y :=
  Certificates.certificate22256.1 P hP x₀ hx₀S hx₀2 hx₀1 h₀

theorem le_of_involutions_S
    {H : Subgroup (Equiv.Perm (Fin 42))} (hH : ∀ y ∈ S, y * y = 1 → y ≠ 1 → y ∈ H) : S ≤ H :=
  Certificates.certificate22256.2 H hH

theorem exists_commute_involution_S
    {x : Equiv.Perm (Fin 42)} (hxS : x ∈ S) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ y ∈ S, y * y = 1 ∧ y ≠ 1 ∧ y ≠ x ∧ x * y = y * x := by
  by_contra hno
  push Not at hno
  have hall := involution_closure_S (fun y => y = x)
    (fun a b _ hbS _ hb2 _ hb1 hab ha => by
      subst ha
      by_contra hba
      exact hno b hbS hb2 hb1 hba hab) hxS hx2 hx1 rfl
  have hle : S ≤ Subgroup.zpowers x := le_of_involutions_S fun y hyS hy2 hy1 => by
    rw [hall y hyS hy2 hy1]
    exact Subgroup.mem_zpowers x
  have hc := Subgroup.card_le_of_le hle
  rw [card_S, Nat.card_zpowers] at hc
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have := Nat.le_of_dvd (by norm_num) hd
  omega

end CFSG.ComponentClassification.GrSLit.FW
