module

public import CFSG.ClassicalInvolution.Asc77.AscT7U6
public import CFSG.ClassicalInvolution.Asc77.AscT7U5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T7U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {R V : Subgroup G} {z : G}

theorem exists_involution_of_isFAut (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (hRV : R ≤ V) (hV2 : IsPGroup 2 ↥V) (hVR : ∀ y ∈ V, conjSub y R = R) {a : G}
    (haV : a ∈ V) (hF : IsFAut R a) (ha2 : a * a ∈ Subgroup.zpowers z) :
    ∃ r ∈ R, (a * r) * (a * r) = 1 ∧ IsFAut R (a * r) := by
  have hz2 : z * z = 1 := hz.sq
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha2
  rcases Int.even_or_odd' k with ⟨k', hk' | hk'⟩
  ·
    have haa : a * a = 1 := by
      rw [← hk, hk', zpow_mul, zpow_two, hz2, one_zpow]
    exact ⟨1, R.one_mem, by simpa using haa, by simpa using hF⟩
  ·
    have haa : a * a = z := by
      rw [← hk, hk', zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
    obtain ⟨x, y, n, c, hinv⟩ := T7F2.exists_coord hR hz hV2 hVR
    have s : T7F2.Out.Setting R V x y n := ⟨c, hRV, hVR, hinv⟩
    obtain ⟨hn2, hkey, j, hjb, hxj⟩ := coord_of_isFAut hR hz s haV hF ha2
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    have hzx : z = x ^ (2 ^ (n' + 2)) := z_eq_pow_of_coord c hz
    set m : ℤ := (2 : ℤ) ^ (n' + 1) with hm
    set u : G := x ^ m with hu
    have huR : u ∈ R := R.zpow_mem c.ha m
    have hE : ∀ e : ℤ, x ^ e = 1 ↔ (2 : ℤ) ^ (n' + 2 + 1) ∣ e := by
      intro e
      have := c.zpow_eq_iff (i := e) (j := 0)
      simpa using this
    have hau : a * u * a⁻¹ = u := by
      rw [hu, T7F2.Out.conj_zpow_a hkey m, c.zpow_eq_iff]
      refine ⟨2 ^ n', ?_⟩
      rw [hm]; ring
    have hau' : a * u = u * a := by
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [hau]
    have hmm : x ^ (m + m) = x ^ (2 ^ (n' + 2)) := by
      rw [← zpow_natCast]
      congr 1
      rw [hm]; push_cast; ring
    have huu : u * u = z := by
      rw [hu, ← zpow_add, hmm, hzx]
    have hb2 : (a * u) * (a * u) = 1 := by
      calc (a * u) * (a * u) = a * (u * a) * u := by group
        _ = a * (a * u) * u := by rw [hau']
        _ = (a * a) * (u * u) := by group
        _ = 1 := by rw [haa, huu, hz2]
    have hux : u * x * u⁻¹ = x := by
      rw [hu]
      have : Commute (x ^ m) x := (Commute.refl x).zpow_left m
      rw [this.eq]; group
    have huy : u * y * u⁻¹ = y * x ^ (2 ^ (n' + 2)) := by
      have h1 : y * x ^ (-m) = x ^ m * y := by
        have := c.conj_zpow (-m)
        have h2 : y * x ^ (-m) * y⁻¹ = x ^ m := by rw [this]; simp
        calc y * x ^ (-m) = (y * x ^ (-m) * y⁻¹) * y := by group
          _ = x ^ m * y := by rw [h2]
      have hz' : x ^ (2 ^ (n' + 2)) * y = y * x ^ (2 ^ (n' + 2)) := by
        rw [← hzx]; exact (AscL62.uniqueInvolution_comm hz c.hb).symm
      calc u * y * u⁻¹ = x ^ m * (y * x ^ (-m)) := by rw [hu, zpow_neg]; group
        _ = x ^ m * (x ^ m * y) := by rw [h1]
        _ = x ^ (m + m) * y := by rw [← mul_assoc, ← zpow_add]
        _ = x ^ (2 ^ (n' + 2)) * y := by rw [hmm]
        _ = y * x ^ (2 ^ (n' + 2)) := hz'
    have hbV : a * u ∈ V := V.mul_mem haV (hRV huR)
    have hbx : (a * u) * x * (a * u)⁻¹ = x ^ ((1 : ℤ) + 2 ^ (n' + 2)) := by
      calc (a * u) * x * (a * u)⁻¹ = a * (u * x * u⁻¹) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [hux]
        _ = x ^ ((1 : ℤ) + 2 ^ (n' + 2)) := hkey
    have hax2 : a * x ^ (2 ^ (n' + 2)) * a⁻¹ = x ^ (2 ^ (n' + 2)) := by
      rw [← zpow_natCast, T7F2.Out.conj_zpow_a hkey, c.zpow_eq_iff]
      refine ⟨2 ^ (n' + 1), ?_⟩
      push_cast; ring
    have hby : (a * u) * y * (a * u)⁻¹ = (y * x ^ j) * x ^ (2 ^ (n' + 2)) := by
      calc (a * u) * y * (a * u)⁻¹ = a * (u * y * u⁻¹) * a⁻¹ := by group
        _ = a * (y * x ^ (2 ^ (n' + 2))) * a⁻¹ := by rw [huy]
        _ = (a * y * a⁻¹) * (a * x ^ (2 ^ (n' + 2)) * a⁻¹) := by group
        _ = (y * x ^ j) * x ^ (2 ^ (n' + 2)) := by rw [hjb, hax2]
    have hF' : IsFAut R (a * u) := by
      refine isFAut_of_action_pm s hV2 hbV hbx ?_
      rcases hxj with h | h
      · right
        rw [hby, h, mul_one]
      · left
        rw [hby, h, mul_assoc, ← pow_add, ← two_mul, ← pow_succ', c.pow_card, mul_one]
    exact ⟨u, huR, hb2, hF'⟩

end CFSG.ClassicalInvolution.Asc77.T7U
