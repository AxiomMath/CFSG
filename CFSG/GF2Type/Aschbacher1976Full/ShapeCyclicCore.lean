module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeHallR3
public import CFSG.Holt.TwoGroups
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GF2Type.Aschbacher1976Full.ShapeBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm CFSG.Blueprint Subgroup

variable {G : Type} [Group G] [Finite G]

theorem no_normal_four_of_cyclic_core {z : G} (hsymp : CFSG.Open.GLASymplecticType (Fz z))
    {D E R : Subgroup ↥(Fz z)} {zz : ↥(Fz z)} (cd : CritData D E R zz)
    (hmax : ∀ D' : Subgroup ↥(Fz z), ThompsonCritical D' → Nat.card D' ≤ Nat.card D)
    (hk8 : 8 ≤ Nat.card (Zof D)) (hE : E = ⊥) :
    ∀ V : Subgroup ↥(Fz z), V.Normal → CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4 := by
  intro V hVn hV hV4
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  have hDZ : D = Zof D := cd.D_eq_Z hE
  obtain ⟨a, k, hag⟩ := exists_gen hF2 cd
  have hk : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hag.card] at this
    omega
  haveI := cd.Z_normal
  obtain ⟨v, hvV, hvz⟩ : ∃ v ∈ V, v ∉ zpowers zz := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show V ≤ zpowers zz from hall)
    rw [Nat.card_zpowers, cd.z_ord, hV4] at h1
    omega
  have hvD : v ∈ D := by
    refine hallR hF2 cd hmax hk8 (g := v) fun y hy hy4 => ?_
    obtain ⟨n, rfl⟩ := hag.gen y hy
    have hu0V : v * a * v⁻¹ * a⁻¹ ∈ V := by
      have h := hVn.conj_mem v⁻¹ (inv_mem hvV) a
      have : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
      rw [this]
      exact mul_mem hvV h
    have hu0Z : v * a * v⁻¹ * a⁻¹ ∈ Zof D :=
      mul_mem (Normal.conj_mem inferInstance a hag.mem v) (inv_mem hag.mem)
    have hu02 : (v * a * v⁻¹ * a⁻¹) ^ 2 = 1 := hV.2 _ hu0V
    have hcomm : Commute (v * a * v⁻¹ * a⁻¹) a :=
      (CritData.Z_comm D hu0Z (CritData.Z_le_D D hag.mem)).symm
    have hn : (2 : ℤ) ∣ n := by
      have h1 : a ^ (4 * n) = 1 := by
        rw [← hy4, ← zpow_natCast, ← zpow_mul]
        congr 1
        ring
      have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hag.ord] at h2
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have h3 : (4 : ℤ) * 2 ∣ 4 * n := by
        refine dvd_trans ⟨2 ^ j, ?_⟩ (by exact_mod_cast h2)
        push_cast
        ring
      exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h3
    obtain ⟨m, rfl⟩ := hn
    have hconj : v * a ^ (2 * m) * v⁻¹ = a ^ (2 * m) := by
      calc v * a ^ (2 * m) * v⁻¹ = (v * a * v⁻¹) ^ (2 * m) := conj_zpow.symm
        _ = ((v * a * v⁻¹ * a⁻¹) * a) ^ (2 * m) := by congr 1; group
        _ = (v * a * v⁻¹ * a⁻¹) ^ (2 * m) * a ^ (2 * m) := hcomm.mul_zpow _
        _ = a ^ (2 * m) := by rw [zpow_mul, zpow_two, ← sq, hu02, one_zpow, one_mul]
    exact hconj
  have hvZ : v ∈ Zof D := hDZ ▸ hvD
  have hv2 : v ^ 2 = 1 := hV.2 v hvV
  have hv1 : v ≠ 1 := fun h => hvz (h ▸ one_mem _)
  have := cd.z_uniq v hvZ (orderOf_eq_prime hv2 hv1)
  exact hvz (this ▸ mem_zpowers zz)

theorem exists_orderOf_ge {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {D E R : Subgroup P}
    {z : P} (c : CritData D E R z) (hk8 : 8 ≤ Nat.card (Zof D)) : ∃ a : P, 8 ≤ orderOf a := by
  obtain ⟨a, k, hag⟩ := exists_gen hP c
  exact ⟨a, by rw [hag.ord]; rw [hag.card] at hk8; exact hk8⟩

theorem shape_cyclic_core {z : G} (hsymp : CFSG.Open.GLASymplecticType (Fz z))
    {D E R : Subgroup ↥(Fz z)} {zz : ↥(Fz z)} (cd : CritData D E R zz)
    (hmax : ∀ D' : Subgroup ↥(Fz z), ThompsonCritical D' → Nat.card D' ≤ Nat.card D)
    (hk8 : 8 ≤ Nat.card (Zof D)) (hE : E = ⊥) : Asc76Shape z := by
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  have hDZ : D = Zof D := cd.D_eq_Z hE
  have hH : Hz z = Fz z := by
    refine Hz_eq_Fz_of_odd hF2 fun u hu hodd => ?_
    haveI := cd.char
    refine eq_one_of_stable_cyclic hF2 hu hodd cd.cyc fun d hd => ?_
    refine fixes_of_cyclic hF2 hu hodd cd.cyc d ?_
    have h : d ∈ centralizer ((Zof D : Subgroup ↥(Fz z)) : Set ↥(Fz z)) :=
      mem_centralizer_iff.mpr hd
    rw [cd.cent] at h
    rwa [hDZ] at h
  have hP8 : 8 ≤ Nat.card ↥(Fz z) := hk8.trans (Subgroup.card_le_card_group _)
  obtain ⟨a, ha8⟩ := exists_orderOf_ge hF2 cd hk8
  rcases CFSG.Holt.cyclic_or_dihedral_or_semidihedral_or_quaternion_of_no_normal_four hF2
    (no_normal_four_of_cyclic_core hsymp cd hmax hk8 hE) with
    hcyc | ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Asc76Shape.uniqueInvolution hH (Or.inl hcyc)
  · haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
    have hcard : Nat.card ↥(Fz z) = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Asc76Shape.dihedral (m + 1) (by omega) hH ⟨e⟩
  · exact Asc76Shape.semidihedral n hn hH ⟨e⟩
  · have hn4 : 4 ≤ n := by
      by_contra hlt
      obtain rfl : n = 3 := by omega
      haveI : NeZero (2 ^ (3 - 2)) := ⟨by norm_num⟩
      have h1 : orderOf (e a) ∣ Monoid.exponent (QuaternionGroup (2 ^ (3 - 2))) :=
        Monoid.order_dvd_exponent _
      have h3 : orderOf (e a) = orderOf a := orderOf_injective e.toMonoidHom e.injective a
      rw [QuaternionGroup.exponent, h3] at h1
      have h2 := Nat.le_of_dvd (by norm_num) h1
      norm_num at h2
      omega
    exact Asc76Shape.uniqueInvolution hH (Or.inr ⟨n, hn4, ⟨e⟩⟩)

end CFSG.GF2Type.Aschbacher1976Full.Shape
