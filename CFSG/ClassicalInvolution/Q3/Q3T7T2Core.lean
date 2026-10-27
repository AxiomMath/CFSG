module

public import CFSG.ClassicalInvolution.Q3.Q3T7T2Grp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7T2

open CFSG.Open CFSG.ClassicalInvolution

variable {G : Type} [Group G] [Finite G]

theorem normalizes_of_comm {N J : Subgroup G} [N.Normal] (hN2 : IsPGroup 2 N) {w : G}
    (hcomm : ∀ j ∈ J, w * j = j * w)
    (hsub : IsSubnormal J (Subgroup.centralizer ({w} : Set G)))
    (hgen : Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} = J)
    {x : G} (hx : x ∈ N) (hxw : x * w = w * x) : x ∈ Subgroup.normalizer (J : Set G) := by
  set C : Subgroup G := Subgroup.centralizer ({w} : Set G) with hC
  set X : Subgroup G := N ⊓ C with hXdef
  have hX2 : IsPGroup 2 X := hN2.to_le inf_le_left
  have hJX : ∀ j ∈ J, ∀ y ∈ X, j * y * j⁻¹ ∈ X := by
    intro j hj y hy
    have hyw : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hmem : j * y * j⁻¹ ∈ C := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc j * y * j⁻¹ * w = j * y * (j⁻¹ * w) := by group
        _ = j * y * (w * j⁻¹) := by rw [← hcomm j⁻¹ (J.inv_mem hj)]
        _ = j * (y * w) * j⁻¹ := by group
        _ = j * (w * y) * j⁻¹ := by rw [hyw]
        _ = (j * w) * y * j⁻¹ := by group
        _ = (w * j) * y * j⁻¹ := by rw [← hcomm j hj]
        _ = w * (j * y * j⁻¹) := by group
    exact ⟨(inferInstance : N.Normal).conj_mem y hy.1 j, hmem⟩
  have hJC : J ≤ C := isSubnormal_le hsub
  obtain ⟨H, hJH, hXH, hHC, hHX⟩ : ∃ H : Subgroup G, J ≤ H ∧ X ≤ H ∧ H ≤ C ∧
      ∀ h ∈ H, ∃ j ∈ J, ∃ y ∈ X, h = j * y := by
    refine ⟨{ carrier := {g | ∃ j ∈ J, ∃ y ∈ X, g = j * y}
              one_mem' := ⟨1, J.one_mem, 1, X.one_mem, by simp⟩
              mul_mem' := ?_
              inv_mem' := ?_ }, ?_, ?_, ?_, fun h hh => hh⟩
    · rintro _ _ ⟨j₁, hj₁, y₁, hy₁, rfl⟩ ⟨j₂, hj₂, y₂, hy₂, rfl⟩
      refine ⟨j₁ * j₂, J.mul_mem hj₁ hj₂, (j₂⁻¹ * y₁ * j₂) * y₂, X.mul_mem ?_ hy₂, by group⟩
      simpa using hJX j₂⁻¹ (J.inv_mem hj₂) y₁ hy₁
    · rintro _ ⟨j, hj, y, hy, rfl⟩
      exact ⟨j⁻¹, J.inv_mem hj, j * y⁻¹ * j⁻¹, hJX j hj y⁻¹ (X.inv_mem hy), by group⟩
    · intro j hj
      exact ⟨j, hj, 1, X.one_mem, by simp⟩
    · intro y hy
      exact ⟨1, J.one_mem, y, hy, by simp⟩
    · rintro _ ⟨j, hj, y, hy, rfl⟩
      exact C.mul_mem (hJC hj) hy.2
  have hsubH : IsSubnormal J H := by
    have := isSubnormal_inf hsub H
    rwa [inf_eq_left.mpr hJH, inf_eq_right.mpr hHC] at this
  have h2 := exists_pow_two_mem hX2 hHX hsubH le_rfl
  have hnorm := le_normalizer_of_odd_closure hJH hgen h2
  exact hnorm (hXH ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxw⟩)

theorem core_centralizes {N J : Subgroup G} [N.Normal] (hN2 : IsPGroup 2 N) {w : G}
    (hwJ : w ∈ J) (hw1 : w ≠ 1) (hww : w * w = 1) (hwN : w ∈ N)
    (hcomm : ∀ j ∈ J, w * j = j * w)
    (hsub : IsSubnormal J (Subgroup.centralizer ({w} : Set G)))
    (hgen : Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} = J)
    (hZ : ∀ c ∈ J ⊓ N, (∀ d ∈ J ⊓ N, c * d = d * c) → c = 1 ∨ c = w)
    {a : G} (haN : a ∈ N) (ha : ∀ d ∈ J ⊓ N, a * d = d * a) :
    ∀ j ∈ J, j * a = a * j := by
  have haw : a * w = w * a := ha w ⟨hwJ, hwN⟩
  have hanorm : a ∈ Subgroup.normalizer (J : Set G) :=
    normalizes_of_comm hN2 hcomm hsub hgen haN haw
  have hDn : ∀ j ∈ J, ∀ d ∈ J ⊓ N, j * d * j⁻¹ ∈ J ⊓ N := fun j hj d hd =>
    ⟨J.mul_mem (J.mul_mem hj hd.1) (J.inv_mem hj), (inferInstance : N.Normal).conj_mem d hd.2 j⟩
  have hodd : ∀ y ∈ J, Odd (orderOf y) → y * a = a * y := by
    intro y hy hyodd
    obtain ⟨c, hc⟩ : ∃ c : G, c = y * a * y⁻¹ * a⁻¹ := ⟨_, rfl⟩
    have hcJ : c ∈ J := by
      have h1 : a * y⁻¹ * a⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hanorm y⁻¹).mp (J.inv_mem hy)
      have : c = y * (a * y⁻¹ * a⁻¹) := by rw [hc]; group
      rw [this]
      exact J.mul_mem hy h1
    have hcN : c ∈ N := by
      rw [hc]
      exact N.mul_mem ((inferInstance : N.Normal).conj_mem a haN y) (N.inv_mem haN)
    have hcD : ∀ d ∈ J ⊓ N, c * d = d * c := by
      intro d hd
      have hd' : y⁻¹ * d * y ∈ J ⊓ N := by
        have := hDn y⁻¹ (J.inv_mem hy) d hd
        rwa [inv_inv] at this
      have h1 : a * (y⁻¹ * d * y) = (y⁻¹ * d * y) * a := ha _ hd'
      have h2 : y * a * y⁻¹ * d = d * (y * a * y⁻¹) := by
        calc y * a * y⁻¹ * d = y * (a * (y⁻¹ * d * y)) * y⁻¹ := by group
          _ = y * ((y⁻¹ * d * y) * a) * y⁻¹ := by rw [h1]
          _ = d * (y * a * y⁻¹) := by group
      have h3 : a⁻¹ * d = d * a⁻¹ := (Commute.inv_left (ha d hd : Commute a d)).eq
      calc c * d = y * a * y⁻¹ * (a⁻¹ * d) := by rw [hc]; group
        _ = y * a * y⁻¹ * (d * a⁻¹) := by rw [h3]
        _ = (y * a * y⁻¹ * d) * a⁻¹ := by group
        _ = (d * (y * a * y⁻¹)) * a⁻¹ := by rw [h2]
        _ = d * c := by rw [hc]; group
    have hcw : c = 1 ∨ c = w := hZ c ⟨hcJ, hcN⟩ hcD
    have hca : y * a * y⁻¹ = c * a := by rw [hc]; group
    have hcy : y * c * y⁻¹ = c := by
      rcases hcw with h | h
      · rw [h]
        group
      · rw [h, ← hcomm y hy]
        group
    have hpow : ∀ k : ℕ, y ^ k * a * (y ^ k)⁻¹ = c ^ k * a := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        have e1 : y ^ (k + 1) * a * (y ^ (k + 1))⁻¹ = y * (y ^ k * a * (y ^ k)⁻¹) * y⁻¹ := by
          rw [pow_succ']
          group
        rw [e1, ihk]
        have e2 : y * (c ^ k * a) * y⁻¹ = (y * c * y⁻¹) ^ k * (y * a * y⁻¹) := by
          rw [conj_pow]
          group
        rw [e2, hcy, hca]
        group
    have hk := hpow (orderOf y)
    rw [pow_orderOf_eq_one] at hk
    have hck : c ^ orderOf y = 1 := by
      have h5 : c ^ orderOf y * a = a := by simpa using hk.symm
      exact mul_eq_right.mp h5
    have hc1 : c = 1 := by
      rcases hcw with h | h
      · exact h
      · exfalso
        obtain ⟨m, hm⟩ := hyodd
        have hw2 : w ^ 2 = 1 := by rw [sq]; exact hww
        have hwm : w ^ (2 * m + 1) = w := by rw [pow_succ, pow_mul, hw2, one_pow, one_mul]
        rw [h, hm, hwm] at hck
        exact hw1 hck
    rw [hc1, one_mul] at hca
    calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [hca]
  intro j hj
  have hle : Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} ≤
      Subgroup.centralizer ({a} : Set G) := (Subgroup.closure_le _).mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hodd y hy.1 hy.2)
  have hj' : j ∈ Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} := by rwa [hgen]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hj')

theorem centralizes_of_forall_eq {N J : Subgroup G} [N.Normal] (hN2 : IsPGroup 2 N) {w : G}
    (hwJ : w ∈ J) (hw1 : w ≠ 1) (hww : w * w = 1) (hwN : w ∈ N)
    (hcomm : ∀ j ∈ J, w * j = j * w)
    (hsub : IsSubnormal J (Subgroup.centralizer ({w} : Set G)))
    (hgen : Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} = J)
    (hA : ∀ d ∈ J ⊓ N, d = 1 ∨ d = w) : ∀ j ∈ J, ∀ n ∈ N, j * n = n * j := by
  have hZ : ∀ c ∈ J ⊓ N, (∀ d ∈ J ⊓ N, c * d = d * c) → c = 1 ∨ c = w :=
    fun c hc _ => hA c hc
  have hX : ∀ a ∈ N, a * w = w * a → ∀ j ∈ J, j * a = a * j := by
    intro a haN haw
    refine core_centralizes hN2 hwJ hw1 hww hwN hcomm hsub hgen hZ haN fun d hd => ?_
    rcases hA d hd with h | h
    · rw [h]
      simp
    · rw [h]
      exact haw
  have hodd : ∀ y ∈ J, Odd (orderOf y) → ∀ n ∈ N, y * n = n * y := fun y hy hyodd n hn =>
    engel_odd hN2 (fun g hg => (inferInstance : N.Normal).conj_mem g hg y) hyodd hwN
      (hcomm y hy).symm (fun g hg hgw => hX g hg hgw y hy) n hn
  intro j hj n hn
  have hle : Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} ≤
      Subgroup.centralizer ({n} : Set G) := (Subgroup.closure_le _).mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hodd y hy.1 hy.2 n hn)
  have hj' : j ∈ Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} := by rwa [hgen]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hj')

end CFSG.ClassicalInvolution.Q3.Q3T7T2
