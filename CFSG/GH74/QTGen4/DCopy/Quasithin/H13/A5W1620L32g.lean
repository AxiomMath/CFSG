module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.Quasithin.H13.A5W1620L32a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_commute_of_fix_red_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ : Subgroup G} (hK₀K : K₀ ≤ K) (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G))
    (y : ↥(Subgroup.normalizer (V : Set G))) (hyρ : S.frame.ρ y = c234 ∨ S.frame.ρ y = c234⁻¹)
    (hyW : (y : G) ∈ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G))
    (hcomm : ∀ k ∈ K₀, ∀ w ∈ S.WK K,
      k * ((y : G) * w * (y : G)⁻¹) * k⁻¹ = (y : G) * (k * w * k⁻¹) * (y : G)⁻¹)
    (hfix : ∀ k ∈ K₀, (y : G) * (k * S.z * k⁻¹ * S.z⁻¹) * (y : G)⁻¹ = k * S.z * k⁻¹ * S.z⁻¹) :
    False := by
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have hW2 : ∀ x ∈ S.WK K, x * x = 1 := fun x hx => by rw [← pow_two]; exact hR.2.2.1.2 x hx
  have hKW : K₀ ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    hK₀K.trans ((le_sup_left.trans le_sup_left).trans hR.2.1)
  set W := S.WK K with hWdef
  have hzW : S.z ∈ W := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  set y' : G := (y : G) with hy'
  have hyiW : y'⁻¹ ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) := Subgroup.inv_mem _ hyW
  have hmemW : ∀ g ∈ Subgroup.normalizer ((W : Subgroup G) : Set G), ∀ w ∈ W,
      g * w * g⁻¹ ∈ W := fun g hg w hw => (Subgroup.mem_normalizer_iff.mp hg w).mp hw

  have hcomm' : ∀ k ∈ K₀, ∀ w ∈ W, k * (y'⁻¹ * w * y') * k⁻¹ = y'⁻¹ * (k * w * k⁻¹) * y' := by
    intro k hk w hw
    have hw' : y'⁻¹ * w * y' ∈ W := by simpa using hmemW _ hyiW w hw
    have h1 := hcomm k hk _ hw'
    have e1 : y' * (y'⁻¹ * w * y') * y'⁻¹ = w := by group
    rw [e1] at h1
    calc k * (y'⁻¹ * w * y') * k⁻¹ = y'⁻¹ * (y' * (k * (y'⁻¹ * w * y') * k⁻¹) * y'⁻¹) * y' := by
          group
      _ = y'⁻¹ * (k * w * k⁻¹) * y' := by rw [h1]
  have hfix' : ∀ k ∈ K₀, y'⁻¹ * (k * S.z * k⁻¹ * S.z⁻¹) * y' = k * S.z * k⁻¹ * S.z⁻¹ := by
    intro k hk
    have h1 := hfix k hk
    calc y'⁻¹ * (k * S.z * k⁻¹ * S.z⁻¹) * y' =
        y'⁻¹ * (y' * (k * S.z * k⁻¹ * S.z⁻¹) * y'⁻¹) * y' := by rw [h1]
      _ = k * S.z * k⁻¹ * S.z⁻¹ := by group

  apply hz
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  set w := k * S.z * k⁻¹ * S.z⁻¹ with hwdef
  have hkz : k * S.z * k⁻¹ = w * S.z := by rw [hwdef]; group
  have hwW : w ∈ W := W.mul_mem (hmemW k (hKW hk) _ hzW) (W.inv_mem hzW)
  have hzyW : y' * S.z * y'⁻¹ ∈ W := hmemW _ hyW _ hzW
  have hzyiW : y'⁻¹ * S.z * y' ∈ W := by simpa using hmemW _ hyiW _ hzW

  have hv : S.v12 = S.z * (y' * S.z * y'⁻¹) * (y'⁻¹ * S.z * y') := S.v12_eq_mul y hyρ
  have h1 : k * (y' * S.z * y'⁻¹) * k⁻¹ = w * (y' * S.z * y'⁻¹) := by
    rw [hcomm k hk _ hzW, hkz]
    calc y' * (w * S.z) * y'⁻¹ = (y' * w * y'⁻¹) * (y' * S.z * y'⁻¹) := by group
      _ = w * (y' * S.z * y'⁻¹) := by
        rw [show y' * w * y'⁻¹ = w from hfix k hk]
  have h2 : k * (y'⁻¹ * S.z * y') * k⁻¹ = w * (y'⁻¹ * S.z * y') := by
    rw [hcomm' k hk _ hzW, hkz]
    calc y'⁻¹ * (w * S.z) * y' = (y'⁻¹ * w * y') * (y'⁻¹ * S.z * y') := by group
      _ = w * (y'⁻¹ * S.z * y') := by
        rw [show y'⁻¹ * w * y' = w from hfix' k hk]
  have hvk : k * S.v12 * k⁻¹ = w * S.v12 := by
    have e1 : k * S.v12 * k⁻¹ = (k * S.z * k⁻¹) * (k * (y' * S.z * y'⁻¹) * k⁻¹) *
        (k * (y'⁻¹ * S.z * y') * k⁻¹) := by rw [hv]; group
    rw [e1, hkz, h1, h2, hv]
    have key := L32.mul_three_of_sq (⟨w, hwW⟩ : ↥W) ⟨S.z, hzW⟩ ⟨_, hzyW⟩ ⟨_, hzyiW⟩
      (Subtype.ext (hW2 w hwW))
    exact congrArg Subtype.val key
  have hvc : k * S.v12 * k⁻¹ = S.v12 := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hK.1 (hK₀K hk))
    rw [hc, mul_inv_cancel_right]
  have hw1 : w = 1 := by
    have h3 : w * S.v12 = S.v12 := hvk.symm.trans hvc
    exact mul_eq_right.mp h3
  have h4 : k * S.z * k⁻¹ = S.z := by rw [hkz, hw1, one_mul]
  calc k * S.z = k * S.z * k⁻¹ * k := by group
    _ = S.z * k := by rw [h4]

end Setting

end CFSG.Quasithin.H13.A5
