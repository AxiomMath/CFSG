module

public import CFSG.CGT.Timmesfeld75.Sec78Core
public import CFSG.CGT.Timmesfeld75.Sec77

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem orderOf_mul_eq_four_of_normalizes {U : Subgroup G} (hU : IsElemAbelian 2 U) {a β : G}
    (haa : a * a = 1) (haN : a ∈ Subgroup.normalizer (U : Set G)) (hβ : β ∈ U)
    (hne : a * β ≠ β * a) : orderOf (a * β) = 4 := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hmem : a * β * a⁻¹ ∈ U := conj_mem_of_mem_normalizer haN hβ
  have hsq : (a * β) ^ 2 = (a * β * a⁻¹) * β := by
    rw [pow_two, hai]
    group
  have hsqU : (a * β) ^ 2 ∈ U := by
    rw [hsq]
    exact U.mul_mem hmem hβ
  have h2 : (a * β) ^ 2 * (a * β) ^ 2 = 1 := elemAbelian_mul_self hU hsqU
  have h1 : (a * β) ^ 2 ≠ 1 := by
    intro h
    apply hne
    have h' : a * β * (a * β) = 1 := by rw [← pow_two]; exact h
    have e1 : a * β = (a * β)⁻¹ := (inv_eq_of_mul_eq_one_right h').symm
    rw [e1, mul_inv_rev, hai, elemAbelian_inv hU hβ]
  exact orderOf_eq_four_of_sq h1 h2

section Comm

variable {x z b : G}

theorem comm_right_of_comm_mul (hx2 : x * x = 1) (hbc : b * (x * z) = (x * z) * b)
    (hbx : b * x = x * b) : b * z = z * b := by
  calc b * z = b * (x * (x * z)) := by rw [← mul_assoc x x z, hx2, one_mul]
    _ = (b * x) * (x * z) := by group
    _ = (x * b) * (x * z) := by rw [hbx]
    _ = x * (b * (x * z)) := by group
    _ = x * ((x * z) * b) := by rw [hbc]
    _ = (x * (x * z)) * b := by group
    _ = z * b := by rw [← mul_assoc x x z, hx2, one_mul]

theorem comm_left_of_comm_mul (hz2 : z * z = 1) (hbc : b * (x * z) = (x * z) * b)
    (hbz : b * z = z * b) : b * x = x * b := by
  calc b * x = b * ((x * z) * z) := by rw [mul_assoc x z z, hz2, mul_one]
    _ = (b * (x * z)) * z := by group
    _ = ((x * z) * b) * z := by rw [hbc]
    _ = (x * z) * (b * z) := by group
    _ = (x * z) * (z * b) := by rw [hbz]
    _ = ((x * z) * z) * b := by group
    _ = x * b := by rw [mul_assoc x z z, hz2, mul_one]

end Comm

section Final

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem Sec6Ctx.false_of_big_group (h77 : Sec77) (hc : Sec6Ctx T T₁ n m)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n) (hA8 : ¬ (n = 4 ∧ m = 1))
    (M : TModel T T₁ n m) {x z δ p : G} (hxT : x ∈ T) (hx1 : x ≠ 1) (hz : z ∈ normD T)
    (hzT : z ∉ T) (hxz : x * z = z * x) (hxzD : x * z ∉ classD T) (hδ : δ ∈ normD T)
    (hδx : δ * x = x * δ) (hδz : δ * z = z * δ) (hp : p = x ∨ p = z)
    {B : Subgroup G} {s : G} (hBs : B ≤ conjSubgroup s T) (hsT : conjSubgroup s T ≠ T)
    (hBc : ∀ b ∈ B, b * (x * z) = (x * z) * b) (hδB : δ ∈ B)
    (hcard : Nat.card B = (2 ^ m) ^ (n - 1))
    {fδ fz : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {vδ vz : Fin n → GaloisField 2 m} (hvδ : vδ ≠ 0) (hvz : vz ≠ 0)
    (hdδ : ∀ v, sact (ubar M.ε δ) v = v + fδ v • vδ)
    (hdz : ∀ v, sact (ubar M.ε z) v = v + fz v • vz)
    (hind : ∀ r t : GaloisField 2 m, r • fδ + t • fz = 0 → r = 0 ∧ t = 0) : False := by
  have := hc.finite
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have hxD : x ∈ classD T := mem_classD_of_mem hxT hx1
  have hzD : z ∈ classD T := hz.1
  have hx2 : x * x = 1 := elemAbelian_mul_self hTab hxT
  have hz2 : z * z = 1 := mul_self_eq_one_of_mem_classD hTab hzD
  have hxz1 : x * z ≠ 1 := by
    intro h
    apply hzT
    have h' : z = x⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h', elemAbelian_inv hTab hxT]
    exact hxT
  have hδ1 : δ ≠ 1 := ne_one_of_mem_classD hδ.1
  by_cases hBp : ∀ b ∈ B, b * p = p * b
  ·
    have hBxz : ∀ b ∈ B, b * x = x * b ∧ b * z = z * b := by
      intro b hb
      rcases hp with rfl | rfl
      · exact ⟨hBp b hb, comm_right_of_comm_mul hx2 (hBc b hb) (hBp b hb)⟩
      · exact ⟨comm_left_of_comm_mul hz2 (hBc b hb) (hBp b hb), hBp b hb⟩
    have hBN : B ≤ Subgroup.normalizer (T : Set G) := fun b hb =>
      hTwc.centralizer_le_normalizer hxT hx1
        (Subgroup.mem_centralizer_singleton_iff.2 (hBxz b hb).1)
    exact hc.false_of_commuting_subgroup M (by omega) hz hδ hBs hsT hBN
      (fun b hb => (hBxz b hb).2) hδB hcard hvδ hvz hdδ hdz hind
  · push Not at hBp
    obtain ⟨β, hβB, hβ⟩ := hBp
    have hβ1 : β ≠ 1 := by
      rintro rfl
      exact hβ (by rw [one_mul, mul_one])
    have hβD : β ∈ classD T := mem_classD_of_mem_conjSubgroup (hBs hβB) hβ1
    have hpδ : p * δ = δ * p := by
      rcases hp with rfl | rfl
      · exact hδx.symm
      · exact hδz.symm
    have hpN : p ∈ Subgroup.normalizer ((conjSubgroup s T : Subgroup G) : Set G) :=
      (hTwc.conj s).centralizer_le_normalizer (hBs hδB) hδ1
        (Subgroup.mem_centralizer_singleton_iff.2 hpδ)
    have hpp : p * p = 1 := by
      rcases hp with rfl | rfl
      · exact hx2
      · exact hz2
    have hord : orderOf (p * β) = 4 :=
      orderOf_mul_eq_four_of_normalizes (isElemAbelian_conjSubgroup hTab s) hpp hpN (hBs hβB)
        (fun h => hβ h.symm)
    rcases hp with rfl | rfl
    · exact h77 G T T₁ n m hc hnat hn3 hA8 p hxD z hzD hxz hxz1 hxzD β hβD (hBc β hβB) hord
    · have hzx1 : p * x ≠ 1 := by rw [← hxz]; exact hxz1
      have hzxD : p * x ∉ classD T := by rw [← hxz]; exact hxzD
      exact h77 G T T₁ n m hc hnat hn3 hA8 p hzD x hxD hxz.symm hzx1 hzxD β hβD
        (by rw [← hxz]; exact hBc β hβB) hord

end Final

end CFSG.CGT.Timmesfeld75
