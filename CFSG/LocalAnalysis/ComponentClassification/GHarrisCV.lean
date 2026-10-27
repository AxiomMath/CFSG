module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisVQ
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisP313a

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem mem_of_index_two_of_odd {X : Type*} [Group X] {H : Subgroup X} (hH : H.index = 2)
    {g : X} (hg : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨k, hk⟩ := hg
  have h : g = (g * g) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h]
  exact pow_mem (mul_self_mem_of_index_two hH g) _

theorem eq_one_of_odd_of_pow_two_pow {X : Type*} [Monoid X] {g : X} (hg : Odd (orderOf g))
    {k : ℕ} (h : g ^ 2 ^ k = 1) : g = 1 := by
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  rcases b with _ | b
  · rwa [pow_zero, orderOf_eq_one_iff] at hb
  · rw [hb] at hg
    exact absurd hg (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, b.succ_ne_zero⟩))

theorem SCert.SE.d_eq_zero_of_comm : ∀ s : SE, s * invRep 1 = invRep 1 * s →
    s * invRep 2 = invRep 2 * s → s.d = 0 := by
  decide +kernel

section Ybar

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem eq_one_of_odd_comm_Y (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) {c : Y} (hodd : Odd (orderOf c))
    (ht : c * D.t = D.t * c) (ha : c * D.a1l = D.a1l * c) : c = 1 := by
  have hcY : c ∈ D.Y1 := mem_of_index_two_of_odd (D.index_centralizer_l hO hz) hodd
  set w := D.piX ⟨c, hcY⟩ with hw
  have hwodd : Odd (orderOf w) := by
    have h1 : orderOf w ∣ orderOf (⟨c, hcY⟩ : D.Y1) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  have hwt : w * D.tX = D.tX * w := by
    rw [hw, ← map_mul, ← map_mul]
    exact congrArg D.piX (Subtype.ext ht)
  have hwa : w * D.a1lX = D.a1lX * w := by
    rw [hw, ← map_mul, ← map_mul]
    exact congrArg D.piX (Subtype.ext ha)
  have hZ : ∀ e ∈ D.Et ⊓ D.Ft, w * e = e * w := by
    intro e he
    rcases D.mem_ZT_cases hO hz he with rfl | rfl | rfl | rfl
    · rw [mul_one, one_mul]
    · exact hwt
    · exact hwa
    · rw [← mul_assoc, hwt, mul_assoc, hwa, ← mul_assoc]
  have hw1 : w = 1 := by
    rcases D.prop38_Xt hC hO hz with ⟨-, -, hE, hF, hCT⟩ | ⟨hA, hCE, -, -⟩
    · exact D.eq_one_of_centralizes_ZT hO hz hE hF hCT hwodd hZ
    · have hEn : D.Et.Normal := hA ▸ pCore_normal
      have hwE := D.centralizes_Et hwodd hZ fun e he => hEn.conj_mem e he w
      have hwmem : w ∈ D.Et := hCE (mem_centralizer_iff.mpr fun e he => (hwE e he).symm)
      obtain ⟨k, hk⟩ := ((D.sylowXt hO hz).isPGroup'.to_le (D.Et_le hO hz)) ⟨w, hwmem⟩
      exact eq_one_of_odd_of_pow_two_pow hwodd (k := k) (congrArg Subtype.val hk)
  have hcl : (⟨c, hcY⟩ : D.Y1) ∈ zpowers D.lY := by
    rw [← QuotientGroup.ker_mk' (zpowers D.lY)]
    exact hw1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hcl
  have h4 : (⟨c, hcY⟩ : D.Y1) ^ 2 ^ 2 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← D.orderOf_lY,
      pow_orderOf_eq_one, one_zpow]
  exact eq_one_of_odd_of_pow_two_pow hodd (k := 2) (congrArg Subtype.val h4)

end GHSylow

end Ybar

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem eq_one_of_odd_comm_M (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    {c : G} (hcM : c ∈ D.M) (hodd : Odd (orderOf c)) (ht : c * D.t = D.t * c)
    (ha : c * D.a1l = D.a1l * c) : c = 1 := by
  have h := D.toMb.eq_one_of_odd_comm_Y hC D.pPrimeCore_Mb D.z_comm_Mb (c := D.piM ⟨c, hcM⟩)
    (by
      have h1 : orderOf (D.piM ⟨c, hcM⟩) ∣ orderOf (⟨c, hcM⟩ : ↥D.M) := orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      exact hodd.of_dvd_nat h1)
    (by
      change D.piM ⟨c, hcM⟩ * D.piM ⟨D.t, D.S_le_M (D.toG_mem _)⟩ =
        D.piM ⟨D.t, D.S_le_M (D.toG_mem _)⟩ * D.piM ⟨c, hcM⟩
      rw [← map_mul, ← map_mul]
      exact congrArg D.piM (Subtype.ext ht))
    (by
      change D.piM ⟨c, hcM⟩ * D.piM ⟨D.a1l, D.S_le_M (D.toG_mem _)⟩ =
        D.piM ⟨D.a1l, D.S_le_M (D.toG_mem _)⟩ * D.piM ⟨c, hcM⟩
      rw [← map_mul, ← map_mul]
      exact congrArg D.piM (Subtype.ext ha))
  have hmem : (⟨c, hcM⟩ : ↥D.M) ∈ pPrimeCore 2 ↥D.M := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥D.M)]
    exact h
  rw [hOM, mem_bot] at hmem
  exact congrArg Subtype.val hmem

omit [Finite G]
  in
theorem S_le_normalizer_centralizer_V :
    (D.S : Subgroup G) ≤ normalizer (centralizer (D.V : Set G) : Set G) := by
  have key : ∀ s ∈ (D.S : Subgroup G), ∀ c ∈ centralizer (D.V : Set G),
      s * c * s⁻¹ ∈ centralizer (D.V : Set G) := by
    intro s hs c hc
    rw [mem_centralizer_iff]
    intro v hv
    have h := mem_centralizer_iff.mp hc _ (D.conj_mem_V hs hv)
    calc v * (s * c * s⁻¹) = s * ((s⁻¹ * v * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * v * s)) * s⁻¹ := by rw [h]
      _ = s * c * s⁻¹ * v := by group
  intro s hs
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key s hs c, fun h => ?_⟩
  have h' := key s⁻¹ (inv_mem hs) _ h
  rwa [show s⁻¹ * (s * c * s⁻¹) * s⁻¹⁻¹ = c by group] at h'

theorem centralizer_V_eq_Q (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥) :
    centralizer (D.V : Set G) = D.Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ fun q hq => mem_centralizer_iff.mpr fun v hv => D.Q_comm (D.V_le_Q hv) hq
  have hP : IsPGroup 2 (centralizer (D.V : Set G)) := by
    intro g
    obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    refine ⟨a, Subtype.ext ?_⟩
    have hgV := mem_centralizer_iff.mp g.2
    have hc : ∀ v ∈ D.V, (g : G) ^ 2 ^ a * v = v * (g : G) ^ 2 ^ a := fun v hv =>
      ((Commute.pow_left (hgV v hv).symm _)).eq
    have hodd : Odd (orderOf ((g : G) ^ 2 ^ a)) := by
      refine hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
      rw [← pow_mul, ← hgm, pow_orderOf_eq_one]
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact D.eq_one_of_odd_comm_M hC hOM
      (mem_centralizer_singleton_iff.mpr (hc _ D.z_mem_V)) hodd (hc _ D.t_mem_V)
      (hc _ D.a1l_mem_V)
  have hle : centralizer (D.V : Set G) ⊔ (D.S : Subgroup G) = D.S :=
    D.S.is_maximal' (hP.to_sup_of_normal_left' D.S.isPGroup' D.S_le_normalizer_centralizer_V)
      le_sup_right
  intro g hg
  have hgS : g ∈ (D.S : Subgroup G) := hle ▸ mem_sup_left hg
  obtain ⟨s, rfl⟩ := D.exists_toG hgS
  have hgV := mem_centralizer_iff.mp hg
  refine (D.toG_mem_Q_iff).mpr (SE.d_eq_zero_of_comm s ?_ ?_)
  · exact D.toG_injective (by rw [map_mul, map_mul]; exact (hgV _ D.t_mem_V).symm)
  · exact D.toG_injective (by rw [map_mul, map_mul]; exact (hgV _ D.a1l_mem_V).symm)

end GHSylow

end CFSG.ComponentClassification.GHarris
