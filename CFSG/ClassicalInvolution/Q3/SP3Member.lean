module

public import CFSG.ClassicalInvolution.Q3.TwinLemmaSL2
import CFSG.ClassicalInvolution.Q3.SP3TwoGroup
import CFSG.ClassicalInvolution.Q3.CoprimeCentralizer

public section

namespace CFSG.ClassicalInvolution.Q3.SP3

open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Q3.Twin
open scoped MatrixGroups commutatorElement

private theorem sl2_exists_order_three : ∃ s : SL(2, ZMod 3), s ^ 3 = 1 ∧ s ≠ 1 := by
  decide +kernel

private theorem sl2_conj_commutators : ∀ g q : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 → q ^ 4 = 1 →
    ∃ a b : SL(2, ZMod 3), a ^ 4 = 1 ∧ b ^ 4 = 1 ∧
      q = a⁻¹ * (g * a * g⁻¹) * (b⁻¹ * (g * b * g⁻¹)) := by
  decide +kernel

section Member

variable {Y : Type*} [Group Y]

theorem quatIn_le_closure_conj {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3)) {s : Y} (hs : s ∈ J)
    (h3 : s ^ 3 = 1) (h1 : s ≠ 1) :
    quatIn e ≤ Subgroup.closure {y | ∃ x ∈ quatIn e, y = x⁻¹ * (s * x * s⁻¹)} := by
  intro q hq
  obtain ⟨hqJ, hq4⟩ := (mem_quatIn e).mp hq
  have hs3 : (⟨s, hs⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  have hs1 : (⟨s, hs⟩ : ↥J) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  obtain ⟨a, b, ha, hb, hab⟩ := sl2_conj_commutators (e ⟨s, hs⟩) (e ⟨q, hqJ⟩)
    (by rw [← map_pow, hs3, map_one]) (fun h => hs1 (e.injective (by simpa using h)))
    (by rw [← map_pow]; have : (⟨q, hqJ⟩ : ↥J) ^ 4 = 1 := Subtype.ext (by simpa using hq4)
        rw [this, map_one])
  have ha' : (e.symm a : ↥J) ^ 4 = 1 := e.injective (by simpa using ha)
  have hb' : (e.symm b : ↥J) ^ 4 = 1 := e.injective (by simpa using hb)
  have hqe : (⟨q, hqJ⟩ : ↥J) = (e.symm a)⁻¹ * (⟨s, hs⟩ * e.symm a * ⟨s, hs⟩⁻¹) *
      ((e.symm b)⁻¹ * (⟨s, hs⟩ * e.symm b * ⟨s, hs⟩⁻¹)) := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hab
  have hmem : ∀ w : ↥J, w ^ 4 = 1 → (w : Y) ∈ quatIn e := fun w hw =>
    (mem_quatIn e).mpr ⟨w.2, by simpa using congrArg Subtype.val hw⟩
  have hq' := congrArg Subtype.val hqe
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hq'
  rw [hq']
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hmem _ ha', rfl⟩)
    (Subgroup.subset_closure ⟨_, hmem _ hb', rfl⟩)

theorem quatIn_le_of_member {U : Subgroup Y} [U.Normal] [Finite Y] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3))
    {z : Y} (hz : z * z = 1)
    (hJ : CFSG.Open.IsSubnormal J (Subgroup.centralizer ({z} : Set Y))) : quatIn e ≤ U := by
  intro y hy
  obtain ⟨hyJ, hy4⟩ := (mem_quatIn e).mp hy
  exact pow_four_mem_of_isSubnormal_centralizer_sl2Three hU hC hz hJ e y hyJ hy4

theorem commutator_mem_quatIn_of_member {U : Subgroup Y} [U.Normal] [Finite Y]
    (hU : IsPGroup 2 U) {z : Y} {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3))
    (hJ : CFSG.Open.IsSubnormal J (Subgroup.centralizer ({z} : Set Y))) {g : Y} (hgJ : g ∈ J)
    (hg3 : g ^ 3 = 1) :
    ∀ x ∈ U, x * z = z * x → x⁻¹ * (g * x * g⁻¹) ∈ quatIn e := by
  intro x hxU hxz
  set H : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hHdef
  have hJH : J ≤ H := CFSG.ClassicalInvolution.isSubnormal_le hJ
  have hgH : g ∈ H := hJH hgJ
  set A : Subgroup Y := U ⊓ H with hAdef
  have hAH : A ≤ H := inf_le_right
  have hAU : A ≤ U := inf_le_left
  have hAn : (A.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAH]
    intro n h hnA hhH
    exact ⟨Subgroup.Normal.conj_mem inferInstance n hnA.1 h, H.mul_mem (H.mul_mem hhH (hAH hnA))
      (H.inv_mem hhH)⟩
  have hcop : ¬ 3 ∣ Nat.card A := not_three_dvd_card_of_isPGroup_two (hU.to_le hAU)
  have hP : IsPGroup 3 (Subgroup.zpowers g) := isPGroup_zpowers (j := 1) (by simpa using hg3)
  have hPJ : Subgroup.zpowers g ≤ J := (Subgroup.zpowers_le).mpr hgJ
  have h1 : ⁅A, Subgroup.zpowers g⁆ ≤ J :=
    commutator_le_of_isSubnormal Nat.prime_three hJ hAH hAn hcop hPJ hP
  have hxA : x⁻¹ ∈ A := ⟨U.inv_mem hxU, Subgroup.mem_centralizer_singleton_iff.mpr
    (Commute.inv_left (show Commute x z from hxz)).eq⟩
  have hc : ⁅x⁻¹, g⁆ ∈ J := h1 (Subgroup.commutator_mem_commutator hxA (Subgroup.mem_zpowers g))
  have he : ⁅x⁻¹, g⁆ = x⁻¹ * (g * x * g⁻¹) := by
    simp only [commutatorElement_def, inv_inv]
    group
  rw [he] at hc
  have hcU : x⁻¹ * (g * x * g⁻¹) ∈ U :=
    U.mul_mem (U.inv_mem hxU) (Subgroup.Normal.conj_mem inferInstance x hxU g)
  obtain ⟨k, hk⟩ := hU ⟨_, hcU⟩
  exact mem_quatIn_of_pow_two_pow e hc (n := k) (by simpa using congrArg Subtype.val hk)

theorem commutator_mem_quatIn_of_member' {U : Subgroup Y} [U.Normal] [Finite Y]
    (hU : IsPGroup 2 U) (hC : Subgroup.centralizer (U : Set Y) ≤ U) {J : Subgroup Y}
    (e : ↥J ≃* SL(2, ZMod 3)) {z : Y} (hz : orderOf z = 2) (hzJ : z ∈ J)
    (hJ : CFSG.Open.IsSubnormal J (Subgroup.centralizer ({z} : Set Y))) {g : Y} (hgJ : g ∈ J)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) : ∀ x ∈ U, x⁻¹ * (g * x * g⁻¹) ∈ quatIn e := by
  have hz2 : z * z = 1 := by rw [← sq, ← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hQU : quatIn e ≤ U := quatIn_le_of_member hU hC e hz2 hJ
  have hz2' : z ^ 2 = 1 := by rw [sq]; exact hz2
  have hzQ : z ∈ quatIn e := involution_mem_quatIn e hzJ hz2'
  have hzU : z ∈ U := hQU hzQ
  let g' : ↥U →* ↥U := (MulAut.conjNormal (H := U) g).toMonoidHom
  have hg' : ∀ x : ↥U, (g' x : Y) = g * x * g⁻¹ := fun x => MulAut.conjNormal_apply g x
  have hg3' : ∀ x : ↥U, g' (g' (g' x)) = x := by
    intro x
    apply Subtype.ext
    rw [hg', hg', hg']
    have hggg : g * g * g = 1 := by simpa [pow_succ] using hg3
    calc g * (g * (g * (x : Y) * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * (x : Y) * (g * g * g)⁻¹ := by
          group
      _ = x := by rw [hggg]; group
  have hgz : g' ⟨z, hzU⟩ = ⟨z, hzU⟩ := by
    apply Subtype.ext
    rw [hg']
    have h := involution_central_in e hzJ hz2' hz1 g hgJ
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [← h]
      _ = z := by group
  have hQ2 : ∀ x ∈ (quatIn e).subgroupOf U, x * x = 1 → x = 1 ∨ x = ⟨z, hzU⟩ := by
    intro x hx hsq
    have hx' : (x : Y) ∈ quatIn e := hx
    have hsq' : (x : Y) ^ 2 = 1 := by rw [sq]; exact congrArg Subtype.val hsq
    by_cases h1 : (x : Y) = 1
    · left; exact Subtype.ext h1
    · right
      exact Subtype.ext (involution_unique_in e (quatIn_le e hx') hzJ hsq' hz2' h1 hz1)
  have hQg : (quatIn e).subgroupOf U ≤
      Subgroup.closure {y : ↥U | ∃ x ∈ (quatIn e).subgroupOf U, y = x⁻¹ * g' x} := by
    intro q hq
    have h1 : (q : Y) ∈ Subgroup.closure {y | ∃ x ∈ quatIn e, y = x⁻¹ * (g * x * g⁻¹)} :=
      quatIn_le_closure_conj e hgJ hg3 hg1 hq
    have hmap : (Subgroup.closure {y : ↥U | ∃ x ∈ (quatIn e).subgroupOf U,
        y = x⁻¹ * g' x}).map U.subtype =
        Subgroup.closure {y | ∃ x ∈ quatIn e, y = x⁻¹ * (g * x * g⁻¹)} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, by simp [hg']⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨⟨x, hQU hx⟩, hx, rfl⟩, by simp [hg']⟩
    rw [← hmap] at h1
    obtain ⟨w, hw, hwq⟩ := h1
    have : w = q := Subtype.ext hwq
    rw [← this]
    exact hw
  have H1 : ∀ x : ↥U, x * ⟨z, hzU⟩ = ⟨z, hzU⟩ * x → x⁻¹ * g' x ∈ (quatIn e).subgroupOf U := by
    intro x hx
    have hxz : (x : Y) * z = z * x := congrArg Subtype.val hx
    have := commutator_mem_quatIn_of_member hU e hJ hgJ hg3 x x.2 hxz
    rw [Subgroup.mem_subgroupOf]
    simpa [hg'] using this
  have key := inv_mul_map_mem_of_centralizer (T := ↥U) hU g' hg3' ((quatIn e).subgroupOf U)
    ⟨z, hzU⟩ (Subgroup.mem_subgroupOf.mpr hzQ) (Subtype.ext hz2) hQ2 hgz hQg H1
  intro x hx
  have := key ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa [hg'] using this

theorem exists_order_three {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3)) :
    ∃ g ∈ J, g ^ 3 = 1 ∧ g ≠ 1 := by
  obtain ⟨s, hs3, hs1⟩ := sl2_exists_order_three
  refine ⟨(e.symm s : Y), (e.symm s).2, ?_, ?_⟩
  · have := congrArg (fun w => ((e.symm w : ↥J) : Y)) hs3
    simpa [map_pow] using this
  · intro h
    apply hs1
    have : e.symm s = 1 := Subtype.ext h
    simpa using this

theorem mem_zpowers_cases {g h : Y} (hg : g ^ 3 = 1) (hh : h ∈ Subgroup.zpowers g) :
    h = 1 ∨ h = g ∨ h = g * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have h3 : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  have hk : g ^ k = g ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · left; rw [hk, hr]; simp
  · right; left; rw [hk, hr]; simp
  · right; right; rw [hk, hr]; exact zpow_two g

theorem commutator_zpowers_eq_quatIn {U : Subgroup Y} {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3))
    (hQU : quatIn e ≤ U) {g : Y} (hgJ : g ∈ J) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hall : ∀ x ∈ U, x⁻¹ * (g * x * g⁻¹) ∈ quatIn e) :
    ⁅U, Subgroup.zpowers g⁆ = quatIn e := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro u hu h hh
    have hu1 : ⁅u, g⁆ ∈ quatIn e := by
      have := hall u⁻¹ (U.inv_mem hu)
      simpa [commutatorElement_def, mul_assoc] using this
    rcases mem_zpowers_cases hg3 hh with rfl | rfl | rfl
    · simp [(quatIn e).one_mem]
    · exact hu1
    · have e1 : ⁅u, g * g⁆ = ⁅u, g⁆ * (g * ⁅u, g⁆ * g⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact Subgroup.mul_mem _ hu1 (conj_mem_quatIn e hgJ hu1)
  · calc quatIn e = ⁅quatIn e, Subgroup.zpowers g⁆ := (commutator_quatIn e hgJ hg3 hg1).symm
      _ ≤ ⁅U, Subgroup.zpowers g⁆ := Subgroup.commutator_mono hQU le_rfl

theorem le_normalizer_quatIn {U : Subgroup Y} {J : Subgroup Y} (e : ↥J ≃* SL(2, ZMod 3))
    (hQU : quatIn e ≤ U) {g : Y} (hgJ : g ∈ J) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hall : ∀ x ∈ U, x⁻¹ * (g * x * g⁻¹) ∈ quatIn e) :
    U ≤ Subgroup.normalizer ((quatIn e : Subgroup Y) : Set Y) := by
  rw [← commutator_zpowers_eq_quatIn e hQU hgJ hg3 hg1 hall]
  exact Subgroup.normalizer_commutator_ge_left U _

theorem mul_comm_involution_of_member {U : Subgroup Y} {J : Subgroup Y}
    (e : ↥J ≃* SL(2, ZMod 3)) (hQU : quatIn e ≤ U) {z : Y} (hz : orderOf z = 2) (hzJ : z ∈ J)
    {g : Y} (hgJ : g ∈ J) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hall : ∀ x ∈ U, x⁻¹ * (g * x * g⁻¹) ∈ quatIn e) : ∀ u ∈ U, u * z = z * u := by
  have hz2' : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hzQ : z ∈ quatIn e := involution_mem_quatIn e hzJ hz2'
  intro u hu
  have hmem : u * z * u⁻¹ ∈ quatIn e :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_quatIn e hQU hgJ hg3 hg1 hall hu) z).mp hzQ
  have hsq : (u * z * u⁻¹) ^ 2 = 1 := by
    rw [sq]
    calc u * z * u⁻¹ * (u * z * u⁻¹) = u * (z * z) * u⁻¹ := by group
      _ = 1 := by rw [← sq, hz2']; group
  have hne : u * z * u⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
      _ = 1 := by rw [h]; group
  have heq := involution_unique_in e (quatIn_le e hmem) hzJ hsq hz2' hne hz1
  calc u * z = (u * z * u⁻¹) * u := by group
    _ = z * u := by rw [heq]

theorem mul_comm_of_involution_central {U : Subgroup Y} [U.Normal] {J : Subgroup Y}
    (e : ↥J ≃* SL(2, ZMod 3)) {z : Y} (hz : orderOf z = 2) (hzJ : z ∈ J) {g : Y} (hgJ : g ∈ J)
    (hg3 : g ^ 3 = 1) (hall : ∀ x ∈ U, x⁻¹ * (g * x * g⁻¹) ∈ quatIn e) {w : Y} (hwU : w ∈ U)
    (hwc : ∀ u ∈ U, u * w = w * u) (hw2 : w * w = 1) : g * w = w * g := by
  have hz2' : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hzz : z * z = 1 := by rw [← sq]; exact hz2'
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hgz : g * z * g⁻¹ = z := by
    have h := involution_central_in e hzJ hz2' hz1 g hgJ
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [← h]
      _ = z := by group
  have hggg : g * g * g = 1 := by simpa [pow_succ] using hg3
  have hw'U : g * w * g⁻¹ ∈ U := Subgroup.Normal.conj_mem inferInstance w hwU g
  have hw'c : ∀ u ∈ U, u * (g * w * g⁻¹) = (g * w * g⁻¹) * u := by
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      simpa using Subgroup.Normal.conj_mem inferInstance u hu g⁻¹
    have := hwc _ hu'
    calc u * (g * w * g⁻¹) = g * ((g⁻¹ * u * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = (g * w * g⁻¹) * u := by group
  have hvQ : w⁻¹ * (g * w * g⁻¹) ∈ quatIn e := hall w hwU
  have hv2 : (w⁻¹ * (g * w * g⁻¹)) ^ 2 = 1 := by
    have hc : (g * w * g⁻¹) * w⁻¹ = w⁻¹ * (g * w * g⁻¹) := (hw'c w⁻¹ (U.inv_mem hwU)).symm
    have hww' : (g * w * g⁻¹) * (g * w * g⁻¹) = 1 := by
      calc (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    rw [sq]
    calc w⁻¹ * (g * w * g⁻¹) * (w⁻¹ * (g * w * g⁻¹))
        = w⁻¹ * ((g * w * g⁻¹) * w⁻¹) * (g * w * g⁻¹) := by group
      _ = w⁻¹ * (w⁻¹ * (g * w * g⁻¹)) * (g * w * g⁻¹) := by rw [hc]
      _ = (w * w)⁻¹ * ((g * w * g⁻¹) * (g * w * g⁻¹)) := by group
      _ = 1 := by rw [hw2, hww']; group
  by_cases hv1 : w⁻¹ * (g * w * g⁻¹) = 1
  · have h1 : g * w * g⁻¹ = w := by
      calc g * w * g⁻¹ = w * (w⁻¹ * (g * w * g⁻¹)) := by group
        _ = w := by rw [hv1, mul_one]
    calc g * w = (g * w * g⁻¹) * g := by group
      _ = w * g := by rw [h1]
  · exfalso
    have hvz := involution_unique_in e (quatIn_le e hvQ) hzJ hv2 hz2' hv1 hz1
    have h1 : g * w * g⁻¹ = w * z := by
      calc g * w * g⁻¹ = w * (w⁻¹ * (g * w * g⁻¹)) := by group
        _ = w * z := by rw [hvz]
    have e2 : g * (g * w * g⁻¹) * g⁻¹ = w := by
      calc g * (g * w * g⁻¹) * g⁻¹ = g * (w * z) * g⁻¹ := by rw [h1]
        _ = (g * w * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (w * z) * z := by rw [h1, hgz]
        _ = w := by rw [mul_assoc, hzz, mul_one]
    have e3 : g * (g * (g * w * g⁻¹) * g⁻¹) * g⁻¹ = w := by
      calc g * (g * (g * w * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * w * (g * g * g)⁻¹ := by group
        _ = w := by rw [hggg]; group
    rw [e2] at e3
    have hwz : w * z = w := h1.symm.trans e3
    exact hz1 (mul_eq_left.mp hwz)

end Member

end CFSG.ClassicalInvolution.Q3.SP3
