module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45

section A5

variable {X : Type*} [Group X] {K : Subgroup X}

theorem a5_card (e : ↥K ≃* alternatingGroup (Fin 5)) : Nat.card ↥K = 60 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem a5_simple (e : ↥K ≃* alternatingGroup (Fin 5)) : IsSimpleGroup ↥K :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  MulEquiv.isSimpleGroup e

theorem a5_nonab (e : ↥K ≃* alternatingGroup (Fin 5)) : ∃ a b : ↥K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hs := a5_simple e
  let _ : CommGroup ↥K := { (inferInstance : Group ↥K) with mul_comm := h }
  have hp := IsSimpleGroup.prime_card (α := ↥K)
  rw [a5_card e] at hp
  norm_num at hp

theorem a5_center (e : ↥K ≃* alternatingGroup (Fin 5)) : Subgroup.center ↥K = ⊥ := by
  have := a5_simple e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := a5_nonab e
    have : a ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem a5_eq_one_of_forall_comm (e : ↥K ≃* alternatingGroup (Fin 5)) {k : X} (hk : k ∈ K)
    (h : ∀ k' ∈ K, k' * k = k * k') : k = 1 := by
  have : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h g g.2)
  rw [a5_center e, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem a5_exists_five (e : ↥K ≃* alternatingGroup (Fin 5)) : ∃ z ∈ K, orderOf z = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [a5_card e]; norm_num)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [a5_card e]; norm_num : 5 ∣ Nat.card ↥K)
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩

theorem a5_perfect (e : ↥K ≃* alternatingGroup (Fin 5)) : ⁅K, K⁆ = K := by
  have := a5_simple e
  have hnormal : (commutator ↥K).Normal := inferInstance
  have h1 : commutator ↥K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥K) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := a5_nonab e
      apply hab
      have : ⁅a, b⁆ ∈ commutator ↥K := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  have h2 : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h2, h1, Subgroup.map_top, Subgroup.range_subtype]

end A5

section Lemmas

variable {X : Type*} [Group X]

theorem eq_one_or_eq_of_cent5 {H : Subgroup X} {t : X} (ht2 : t * t = 1)
    (hcent5 : ∀ z ∈ H, z ∈ centralizer ({t} : Set X) → orderOf z = 5 →
      ∀ c ∈ H, c ∈ centralizer ({t} : Set X) → c * z = z * c → ∃ j : ℕ, c = z ^ j ∨ c = t * z ^ j)
    {K : Subgroup X} (hKH : K ≤ H) (hK : K ≤ centralizer ({t} : Set X))
    (e : ↥K ≃* alternatingGroup (Fin 5)) {w : X} (hwH : w ∈ H) (hw : w ∈ centralizer ({t} : Set X))
    (hwK : ∀ k ∈ K, k * w = w * k) : w = 1 ∨ w = t := by
  obtain ⟨z, hzK, hz5⟩ := a5_exists_five e
  obtain ⟨j, hj⟩ := hcent5 z (hKH hzK) (hK hzK) hz5 w hwH hw (hwK z hzK).symm
  have hzjK : z ^ j ∈ K := K.pow_mem hzK j
  have htK : ∀ k ∈ K, k * t = t * k := fun k hk => by
    have := hK hk
    rw [mem_centralizer_singleton_iff] at this
    exact this
  rcases hj with hj | hj
  · left
    have : z ^ j = 1 := a5_eq_one_of_forall_comm e hzjK fun k hk => by rw [← hj]; exact hwK k hk
    rw [hj, this]
  · right
    have : z ^ j = 1 := by
      refine a5_eq_one_of_forall_comm e hzjK fun k hk => ?_
      have h1 : t * z ^ j = w := hj.symm
      have h2 : z ^ j = t * w := by
        calc z ^ j = (t * t) * z ^ j := by rw [ht2, one_mul]
          _ = t * (t * z ^ j) := by rw [mul_assoc]
          _ = t * w := by rw [h1]
      rw [h2, ← mul_assoc, htK k hk, mul_assoc, hwK k hk, ← mul_assoc]
    rw [hj, this, mul_one]

theorem eq_of_perfect_le_derived [Finite X] {K D M : Subgroup X} (hKD : K ≤ D) (hperf : ⁅K, K⁆ = K)
    (hcomm : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ M) (hcard : Nat.card ↥M ≤ Nat.card ↥K) : K = M := by
  have hle : K ≤ M := by
    rw [← hperf, Subgroup.commutator_le]
    exact fun x hx y hy => hcomm x (hKD hx) y (hKD hy)
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem exists_elemAb_of_two_le_pRank [Finite X] {Y : Subgroup X} (h : 2 ≤ CFSG.pRank 2 ↥Y) :
    ∃ E : Subgroup X, E ≤ Y ∧ IsElementaryAbelian 2 ↥E ∧ 4 ≤ Nat.card ↥E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set ℕ := {r | ∃ A : Subgroup ↥Y, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r}
  have hbot : IsElementaryAbelian 2 ↥(⊥ : Subgroup ↥Y) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 ⊥).mpr
      ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  have hne : S.Nonempty := ⟨0, ⊥, hbot, by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card ↥Y, ?_⟩
    rintro r ⟨A, -, hA⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card ↥A := hA.symm
      _ ≤ Nat.card ↥Y := Subgroup.card_le_card_group A
  obtain ⟨A, hAe, hAc⟩ := Nat.sSup_mem hne hbdd
  have h4 : 4 ≤ Nat.card ↥A := by
    rw [hAc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (sSup S) := Nat.pow_le_pow_right (by norm_num) h
  refine ⟨A.map Y.subtype, fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  · have := hAe
    exact IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact h4

theorem card_le_two_of_centralizer_le [Finite X] {Y : Subgroup X} {y : X} (hy : y ∈ Y)
    (hy2 : orderOf y = 2) (hC : ∀ w ∈ Y, w * y = y * w → w = 1 ∨ w = y) {E : Subgroup X}
    (hE : E ≤ Y) (hEp : IsPGroup 2 ↥E) : Nat.card ↥E ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  let y' : ↥Y := ⟨y, hy⟩
  have hy'2 : orderOf y' = 2 := by rw [← Subgroup.orderOf_coe]; exact hy2
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'2]; norm_num)
  obtain ⟨T, hT⟩ := hzp.exists_le_sylow
  have hTle : Nat.card ↥(T : Subgroup ↥Y) ≤ 2 := by
    have hTp : IsPGroup 2 ↥(T : Subgroup ↥Y) := T.isPGroup'
    have hy'T : y' ∈ (T : Subgroup ↥Y) := hT (Subgroup.mem_zpowers y')
    let yT : ↥(T : Subgroup ↥Y) := ⟨y', hy'T⟩
    have hyT1 : yT ≠ 1 := fun h => hy1 (congrArg Subtype.val (congrArg Subtype.val h))
    have : Nontrivial ↥(T : Subgroup ↥Y) := ⟨⟨yT, 1, hyT1⟩⟩
    have : Nontrivial ↥(Subgroup.center ↥(T : Subgroup ↥Y)) := hTp.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥(T : Subgroup ↥Y)))
    have hzy : ((z : ↥(T : Subgroup ↥Y)) : X) * y = y * ((z : ↥(T : Subgroup ↥Y)) : X) := by
      have := (Subgroup.mem_center_iff.mp z.2) yT
      have h2 := congrArg (fun g : ↥(T : Subgroup ↥Y) => ((g : ↥Y) : X)) this
      simpa [yT, y'] using h2.symm
    have hz1 : ((z : ↥(T : Subgroup ↥Y)) : X) ≠ 1 := by
      intro h
      apply hz
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hzeq : ((z : ↥(T : Subgroup ↥Y)) : X) = y :=
      (hC _ ((z : ↥(T : Subgroup ↥Y)) : ↥Y).2 hzy).resolve_left hz1
    have hyTz : yT = (z : ↥(T : Subgroup ↥Y)) :=
      Subtype.ext (Subtype.ext hzeq.symm)
    have hyTc : yT ∈ Subgroup.center ↥(T : Subgroup ↥Y) := by rw [hyTz]; exact z.2
    have hall : ∀ g : ↥(T : Subgroup ↥Y), g = 1 ∨ g = yT := by
      intro g
      have h1 := (Subgroup.mem_center_iff.mp hyTc) g
      have h2 := congrArg (fun g : ↥(T : Subgroup ↥Y) => ((g : ↥Y) : X)) h1
      have hcomm : ((g : ↥Y) : X) * y = y * ((g : ↥Y) : X) := by simpa [yT, y'] using h2
      rcases hC _ (g : ↥Y).2 hcomm with h | h
      · left
        exact Subtype.ext (Subtype.ext h)
      · right
        exact Subtype.ext (Subtype.ext h)
    have hle : (⊤ : Subgroup ↥(T : Subgroup ↥Y)) ≤ Subgroup.zpowers yT := by
      intro g _
      rcases hall g with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    calc Nat.card ↥(T : Subgroup ↥Y) = Nat.card ↥(⊤ : Subgroup ↥(T : Subgroup ↥Y)) := by
          rw [Subgroup.card_top]
      _ ≤ Nat.card ↥(Subgroup.zpowers yT) := Subgroup.card_le_of_le hle
      _ = 2 := by
          rw [Nat.card_zpowers]
          have : orderOf yT = 2 := by
            rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]; exact hy2
          exact this
  let E' : Subgroup ↥Y := E.subgroupOf Y
  have hE'p : IsPGroup 2 ↥E' := hEp.comap_subtype
  obtain ⟨T2, hT2⟩ := hE'p.exists_le_sylow
  have hcard : Nat.card ↥(T2 : Subgroup ↥Y) = Nat.card ↥(T : Subgroup ↥Y) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  calc Nat.card ↥E = Nat.card ↥E' := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv).symm
    _ ≤ Nat.card ↥(T2 : Subgroup ↥Y) := Subgroup.card_le_of_le hT2
    _ = Nat.card ↥(T : Subgroup ↥Y) := hcard
    _ ≤ 2 := hTle

theorem sylow_elemAb [Finite X] {N E : Subgroup X} (hE : E ≤ N) (hEa : IsElementaryAbelian 2 ↥E)
    {a m : ℕ} (hEcard : Nat.card ↥E = 2 ^ a) (hN : Nat.card ↥N = 2 ^ a * m) (hm : Odd m)
    {S : Subgroup X} (hS : IsSylowOf 2 S N) : IsElementaryAbelian 2 ↥S ∧ Nat.card ↥S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hfac : (Nat.card ↥N).factorization 2 = a := by
    rw [hN, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hm; omega)]
    simp
  have hScard : Nat.card ↥S = 2 ^ a := by rw [hS.card_eq, hfac]
  have hEsyl : IsSylowOf 2 E N := isSylowOf_of_card hE (by rw [hEcard, hfac])
  obtain ⟨k, -, hk⟩ := hEsyl.exists_mem_conj hS
  refine ⟨?_, hScard⟩
  rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    have h1 := (hk x).mp hx
    have h2 := (hk y).mp hy
    have h3 : (⟨k⁻¹ * x * k, h1⟩ : ↥E) * ⟨k⁻¹ * y * k, h2⟩ = ⟨k⁻¹ * y * k, h2⟩ * ⟨k⁻¹ * x * k, h1⟩ :=
      hEa.toIsMulCommutative.is_comm.comm _ _
    have h4 := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul] at h4
    calc x * y = k * (k⁻¹ * x * k * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * (k⁻¹ * y * k * (k⁻¹ * x * k)) * k⁻¹ := by rw [h4]
      _ = y * x := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  have h1 := (hk x).mp hx
  have h2 : (k⁻¹ * x * k) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ h1
  have h2' : (k⁻¹ * x * k) * (k⁻¹ * x * k) = 1 := by rw [← pow_two]; exact h2
  calc x ^ 2 = x * x := pow_two x
    _ = k * ((k⁻¹ * x * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
    _ = 1 := by rw [h2']; group

theorem mem_map_conj_iff (S : Subgroup X) (g x : X) :
    x ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ S := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem exists_two_involutions [Finite X] {E : Subgroup X} (hE : IsElementaryAbelian 2 ↥E)
    (h4 : 4 ≤ Nat.card ↥E) :
    ∃ x ∈ E, ∃ x' ∈ E, orderOf x = 2 ∧ orderOf x' = 2 ∧ x' ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ a ∈ E, a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hord : ∀ a ∈ E, a ≠ 1 → orderOf a = 2 := fun a ha ha1 => orderOf_eq_prime (hsq a ha) ha1
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := Subgroup.eq_bot_iff_forall E |>.2 hcon
    rw [this, Subgroup.card_bot] at h4
    omega
  obtain ⟨x', hx'E, hx'z⟩ : ∃ x' ∈ E, x' ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers x := hcon
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord x hxE hx1] at this
    omega
  have hx'1 : x' ≠ 1 := fun h => hx'z (h ▸ Subgroup.one_mem _)
  have hx'x : x' ≠ x := fun h => hx'z (h ▸ Subgroup.mem_zpowers x)
  exact ⟨x, hxE, x', hx'E, hord x hxE hx1, hord x' hx'E hx'1, hx'x⟩

end Lemmas


end CFSG.GH74.Generic.S45
