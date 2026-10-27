module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG.EvenSporadicStandard.SolomonRed

variable {G : Type*} [Group G]

theorem exists_involution_of_even [Finite G] {Y : Subgroup G} (hev : Even (Nat.card Y)) :
    ∃ u ∈ Y, u * u = 1 ∧ u ≠ 1 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (G := Y) (even_iff_two_dvd.mp hev)
  refine ⟨u.1, u.2, ?_, ?_⟩
  · have h : u * u = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu, pow_two] at this
      exact this
    exact congrArg Subtype.val h
  · intro h1
    have : u = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hu
    omega

theorem even_natCard_inf_centralizer [Finite G] {t : G} (ht : t * t = 1) {L : Subgroup G}
    (hL : ∀ x ∈ L, t * x * t⁻¹ ∈ L) (hev : Even (Nat.card L)) :
    Even (Nat.card ↥(L ⊓ centralizer ({t} : Set G))) := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  let A : Subgroup G := L ⊓ centralizer ({t} : Set G)
  let f : L → L := fun x => ⟨t * x * t⁻¹, hL x x.2⟩
  have hf : Function.Involutive f := by
    intro x
    apply Subtype.ext
    show t * (t * ↑x * t⁻¹) * t⁻¹ = ↑x
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [ht']
    calc t * (t * ↑x * t) * t = (t * t) * ↑x * (t * t) := by group
      _ = ↑x := by rw [ht, one_mul, mul_one]
  let c : Equiv.Perm L := hf.toPerm f
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    exact Equiv.ext (fun x => hf x)
  have hmod := Equiv.Perm.card_compl_support_modEq (σ := c) (p := 2) (n := 1)
    (by simpa using hc2)
  have hfixcard : Fintype.card (Function.fixedPoints c) = c.supportᶜ.card :=
    Fintype.card_of_finset' c.supportᶜ (fun x => by
      simp [Equiv.Perm.mem_support, Function.mem_fixedPoints_iff, Function.IsFixedPt])
  let e : ↥A ≃ Function.fixedPoints c :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        apply Subtype.ext
        show t * x.1 * t⁻¹ = x.1
        have hx : x.1 * t = t * x.1 := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
        calc t * x.1 * t⁻¹ = (x.1 * t) * t⁻¹ := by rw [hx]
          _ = x.1 := by group⟩
      invFun := fun x => ⟨x.1.1, ⟨x.1.2, by
        change x.1.1 ∈ centralizer ({t} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hx : t * x.1.1 * t⁻¹ = x.1.1 := by
          have := congrArg Subtype.val x.2
          simpa [c, f] using this
        calc x.1.1 * t = (t * x.1.1 * t⁻¹) * t := by rw [hx]
          _ = t * x.1.1 := by group⟩⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  have hcardA : Nat.card ↥A = c.supportᶜ.card := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, hfixcard]
  have h2supp : 2 ∣ c.supportᶜ.card := by
    have hL2 : 2 ∣ Fintype.card L := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp hev
    exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hL2))
  have h2A : 2 ∣ Nat.card ↥A := by rw [hcardA]; exact h2supp
  exact even_iff_two_dvd.mpr h2A

theorem eq_one_of_mem_odd_of_pow_two_pow_eq_one [Finite G] {W : Subgroup G}
    (hW : Odd (Nat.card W)) {x : G} (hx : x ∈ W) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have hdiv1 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hx
  have hdiv2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hodd : Odd (orderOf x) := hW.of_dvd_nat hdiv1
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv2
  have hj0 : j = 0 := by
    by_contra hj
    exact (Nat.not_even_iff_odd.mpr (hjeq ▸ hodd))
      (even_iff_two_dvd.mpr (dvd_pow_self 2 hj))
  exact orderOf_eq_one_iff.mp (hjeq.trans (by rw [hj0, pow_zero]))

private theorem four_dvd_natCard_inf_centralizer_of_isPerfect_aux {K : Type*} [Group K]
    [Finite K] {X : Subgroup K} (hX : Group.IsPerfect X) {z : K} (hzX : z ∈ X)
    (hz : z * z = 1) (hz1 : z ≠ 1) : 4 ∣ Nat.card ↥(X ⊓ centralizer ({z} : Set K)) := by
  by_contra hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let z' : X := ⟨z, hzX⟩
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'2 : z' * z' = 1 := Subtype.ext hz
  have hord : orderOf z' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz'2) hz'1
  have hpg : IsPGroup 2 (zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hz'S : z' ∈ (S : Subgroup X) := hS (mem_zpowers z')
  haveI hnt : Nontrivial (S : Subgroup X) :=
    ⟨⟨⟨z', hz'S⟩, 1, fun h => hz'1 (congrArg Subtype.val h)⟩⟩
  let A : Subgroup K := X ⊓ centralizer ({z} : Set K)
  let CT : Subgroup X := (S : Subgroup X) ⊓ centralizer ({z'} : Set X)
  have hCTpg : IsPGroup 2 CT := S.isPGroup'.to_le inf_le_left
  have hcardA : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hCTle : CT ≤ A.subgroupOf X := by
    intro c hc
    rw [Subgroup.mem_subgroupOf]
    refine ⟨c.2, ?_⟩
    change (c : K) ∈ centralizer ({z} : Set K)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcz : c * z' = z' * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    simpa using congrArg Subtype.val hcz
  have hdivCT : Nat.card CT ∣ Nat.card A := by
    rw [← hcardA]
    exact Subgroup.card_dvd_of_le hCTle
  obtain ⟨j, hj⟩ := hCTpg.exists_card_eq
  have hjle : j ≤ 1 := by
    by_contra hj1
    push_neg at hj1
    have h4dvd : 4 ∣ Nat.card A := by
      have h1 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 hj1
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at h1
      rw [hj] at hdivCT
      exact h1.trans hdivCT
    exact hcon h4dvd
  have hCTle2 : Nat.card CT ≤ 2 := by
    rw [hj]
    interval_cases j <;> norm_num
  have hzpw_le : zpowers z' ≤ CT := Subgroup.zpowers_le.mpr ⟨hz'S, by
    change z' ∈ centralizer ({z'} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]⟩
  have h2dvd : 2 ∣ Nat.card CT := by
    have h := Subgroup.card_dvd_of_le hzpw_le
    rwa [Nat.card_zpowers, hord] at h
  have hCTeq2 : Nat.card CT = 2 := by
    have hpos : 0 < Nat.card CT := Nat.card_pos
    obtain ⟨m, hm⟩ := h2dvd
    have hmpos : 0 < m := by
      by_contra h
      rw [Nat.not_lt] at h
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero h
      rw [hm, hm0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    have hm2 : 2 * m ≤ 2 := by rw [← hm]; exact hCTle2
    have h2m : 2 ≤ 2 * m := by
      simpa using Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hmpos)
    have h2 : 2 * m = 2 := le_antisymm hm2 h2m
    rw [hm, h2]
  have hCTeq : CT = zpowers z' :=
    (Subgroup.eq_of_le_of_card_ge hzpw_le
      (by simp [hCTeq2, Nat.card_zpowers, hord])).symm
  haveI : Nontrivial (Subgroup.center (S : Subgroup X)) := S.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center (S : Subgroup X))
  have hcz : ((c : S) : X) = z' := by
    have hccent : ((c : S) : X) ∈ CT := by
      refine ⟨c.1.2, ?_⟩
      change ((c : S) : X) ∈ centralizer ({z'} : Set X)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm := Subgroup.mem_center_iff.1 c.2 ⟨z', hz'S⟩
      exact (congrArg Subtype.val hcomm).symm
    rw [hCTeq] at hccent
    rcases (mem_zpowers_iff_of_mul_self_eq_one hz'2).1 hccent with h1 | h1
    · exfalso
      exact hc1 (Subtype.ext (Subtype.ext h1))
    · exact h1
  have hzcen : (⟨z', hz'S⟩ : S) ∈ Subgroup.center (S : Subgroup X) := by
    have hcz' : c.1 = ⟨z', hz'S⟩ := Subtype.ext hcz
    rw [← hcz']
    exact c.2
  have hSle : (S : Subgroup X) ≤ centralizer ({z'} : Set X) := by
    intro s hs
    change s ∈ centralizer ({z'} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_center_iff.1 hzcen ⟨s, hs⟩
    exact congrArg Subtype.val hcomm
  have hSCT : (S : Subgroup X) ≤ CT := le_inf le_rfl hSle
  have hSeq : (S : Subgroup X) = zpowers z' := by
    rw [← hCTeq]
    exact le_antisymm hSCT inf_le_left
  have hcard : Nat.card (S : Subgroup X) = 2 := by
    rw [hSeq, Nat.card_zpowers, hord]
  have hcyc : IsCyclic (S : Subgroup X) := isCyclic_of_prime_card hcard
  obtain ⟨N, hN, hcompl⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two S hcyc
  have hidx : N.index = 2 := by
    rw [hcompl.symm.index_eq_card, hcard]
  exact not_isPerfect_of_index_eq_two hidx hX

theorem four_dvd_natCard_inf_centralizer_of_isPerfect [Finite G] {X : Subgroup G}
    (hX : ⁅X, X⁆ = X) {t : G} (htX : t ∈ X) (ht : t * t = 1) (ht1 : t ≠ 1) :
    4 ∣ Nat.card ↥(X ⊓ centralizer ({t} : Set G)) :=
  four_dvd_natCard_inf_centralizer_of_isPerfect_aux (Subgroup.isPerfect_iff.mpr hX) htX ht ht1

theorem normal_two_group_eq_bot_or_center [Finite G] {t : G} (ht : t * t = 1) (ht1 : t ≠ 1)
    {W : Subgroup G} [W.Normal] (hW : IsPGroup 2 W)
    (hfix : ∀ w ∈ W, t * w = w * t → w ∈ zpowers t) :
    W = ⊥ ∨ t ∈ Subgroup.center G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hW1 : W = ⊥
  · exact Or.inl hW1
  right
  haveI hntW : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hW1
  by_cases htW : t ∈ W
  · haveI : Nontrivial (Subgroup.center W) := hW.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center W)
    have hct : (c : W) = ⟨t, htW⟩ := by
      have hcomm : t * (c : W).1 = (c : W).1 * t := by
        have := Subgroup.mem_center_iff.1 c.2 ⟨t, htW⟩
        exact congrArg Subtype.val this
      rcases (mem_zpowers_iff_of_mul_self_eq_one ht).1
        (hfix (c : W).1 (c : W).2 hcomm) with h1 | h1
      · exfalso
        exact hc1 (Subtype.ext (Subtype.ext h1))
      · exact Subtype.ext h1
    have htcen : (⟨t, htW⟩ : W) ∈ Subgroup.center W := by
      rw [← hct]
      exact c.2
    have hWt : ∀ w ∈ W, w = 1 ∨ w = t := by
      intro w hw
      apply (mem_zpowers_iff_of_mul_self_eq_one ht).1
      apply hfix w hw
      have := Subgroup.mem_center_iff.1 htcen ⟨w, hw⟩
      exact (congrArg Subtype.val this).symm
    have htc : ∀ y : G, y * t = t * y := by
      intro y
      have hy : y * t * y⁻¹ ∈ W := (inferInstance : W.Normal).conj_mem t htW y
      rcases hWt _ hy with h1 | h1
      · exfalso
        apply ht1
        calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      · calc y * t = (y * t * y⁻¹) * y := by group
          _ = t * y := by rw [h1]
    exact Subgroup.mem_center_iff.mpr htc
  · exfalso
    have hfp : ∀ w ∈ W, t * w = w * t → w = 1 := by
      intro w hw hwz
      rcases (mem_zpowers_iff_of_mul_self_eq_one ht).1 (hfix w hw hwz) with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hw) htW
    have hσ : ∀ x, (MulAut.conj t) ((MulAut.conj t) x) = x := by
      intro x
      simpa [MulAut.conj_apply] using conj_conj_of_mul_self_eq_one ht x
    have hWσ : ∀ w ∈ W, (MulAut.conj t) w ∈ W := fun w hw => by
      simpa [MulAut.conj_apply] using (inferInstance : W.Normal).conj_mem w hw t
    have hfpσ : ∀ w ∈ W, (MulAut.conj t) w = w → w = 1 := fun w hw hw' =>
      hfp w hw (conj_eq_self_iff.1 (by simpa [MulAut.conj_apply] using hw'))
    have hinv := fixedPointFree_inverts (MulAut.conj t) hσ hWσ hfpσ
    have h2 : 2 ∣ Nat.card W := by
      obtain ⟨n, hn⟩ := hW.exists_card_eq
      rcases n with _ | n
      · exfalso
        have : Nat.card W = 1 := by simpa using hn
        exact hW1 (Subgroup.card_eq_one.mp this)
      · rw [hn, pow_succ]
        exact dvd_mul_left _ _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (G := W) h2
    have hx2 : (x : G) * (x : G) = 1 := by
      have h : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rw [hx, pow_two] at this
        exact this
      exact congrArg Subtype.val h
    have hx1 : (x : G) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      omega
    have hxi : (MulAut.conj t) (x : G) = (x : G)⁻¹ := hinv x x.2
    have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv] at hxi
    exact absurd (hfp x x.2 (conj_eq_self_iff.1 (by simpa [MulAut.conj_apply] using hxi))) hx1

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
