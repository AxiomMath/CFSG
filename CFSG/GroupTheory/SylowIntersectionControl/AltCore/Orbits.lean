module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Radical
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Diagonal
public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Commute
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.TransitiveCase
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction CFSG.ABGLocalTools CFSG.ClassicalInvolution.GlaubermanAut

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def IsEvenSet (H : Subgroup (Perm α)) (O : Set α) : Prop :=
  ∃ x ∈ normalizer (H : Set (Perm α)), x ∈ fixOutside O ∧ x ∉ H ∧ x ^ 2 ∈ H

abbrev IsRadical (H : Subgroup (Perm α)) : Prop :=
  ∀ P : Subgroup (Perm α), IsPGroup 2 P → P ≤ normalizer (H : Set (Perm α)) →
    normalizer (H : Set (Perm α)) ≤ normalizer (P : Set (Perm α)) → P ≤ H

omit [DecidableEq α] in
theorem isRadical_of_isPIsolatedOver {H : Subgroup (Perm α)} (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) : IsRadical H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact fun P hP _ hNP => hiso.le_of_normalizer_le hH hP hNP

variable {H : Subgroup (Perm α)}

omit [DecidableEq α] in
theorem restrHom_mem_normalizer (hH : IsPGroup 2 H) (hrad : IsRadical H) {O : Set α}
    [DecidablePred (· ∈ O)] (hO : normalizer (H : Set (Perm α)) ≤ setStab O) {n : Perm α}
    (hn : n ∈ normalizer (H : Set (Perm α))) :
    restrHom O ⟨n, hO hn⟩ ∈ normalizer (H : Set (Perm α)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOc : normalizer (H : Set (Perm α)) ≤ setStab Oᶜ := by rw [setStab_compl]; exact hO
  refine mem_normalizer_fintype fun h hh => ?_
  have hhN : h ∈ normalizer (H : Set (Perm α)) := le_normalizer hh
  have hb := restrHom_mem hH hrad hOc hh
  have hc := restrHom_mem hH hrad hO (show n * h * n⁻¹ ∈ H from
    (mem_normalizer_iff.mp hn h).mp hh)
  have e : restrHom O ⟨h, hO hhN⟩ * restrHom Oᶜ ⟨h, hOc hhN⟩ = h :=
    restrHom_mul_restrHom_compl ⟨h, hO hhN⟩
  have hcomm := (restrHom_commute_compl (O := O) ⟨n, hO hn⟩ ⟨h, hOc hhN⟩).eq
  have e2 : restrHom O ⟨n, hO hn⟩ * restrHom O ⟨h, hO hhN⟩ * (restrHom O ⟨n, hO hn⟩)⁻¹ =
      restrHom O ⟨n * h * n⁻¹, hO (mul_mem (mul_mem hn hhN) (inv_mem hn))⟩ := by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  set r := restrHom O ⟨n, hO hn⟩
  set a := restrHom O ⟨h, hO hhN⟩
  set b := restrHom Oᶜ ⟨h, hOc hhN⟩
  have hcomm' : r * b * r⁻¹ = b := by rw [hcomm, mul_inv_cancel_right]
  have key : r * h * r⁻¹ = (r * a * r⁻¹) * b := by
    conv_lhs => rw [← e]
    calc r * (a * b) * r⁻¹ = r * a * r⁻¹ * (r * b * r⁻¹) := by group
      _ = r * a * r⁻¹ * b := by rw [hcomm']
  rw [key, e2]
  exact mul_mem hc hb

omit [DecidableEq α] in
theorem IsEvenSet.of_union (hH : IsPGroup 2 H) (hrad : IsRadical H) {O₁ O₂ : Set α}
    [DecidablePred (· ∈ O₁)] (h₁ : normalizer (H : Set (Perm α)) ≤ setStab O₁)
    (he : IsEvenSet H (O₁ ∪ O₂)) : IsEvenSet H O₁ ∨ IsEvenSet H O₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxN, hxO, hxH, hx2⟩ := he
  have h₁c : normalizer (H : Set (Perm α)) ≤ setStab O₁ᶜ := by rw [setStab_compl]; exact h₁
  have e : restrHom O₁ ⟨x, h₁ hxN⟩ * restrHom O₁ᶜ ⟨x, h₁c hxN⟩ = x :=
    restrHom_mul_restrHom_compl ⟨x, h₁ hxN⟩
  have hsq : ∀ (O : Set α) [DecidablePred (· ∈ O)] (hO : normalizer (H : Set (Perm α)) ≤ setStab O),
      (restrHom O ⟨x, hO hxN⟩) ^ 2 ∈ H := fun O _ hO => by
    rw [← map_pow]
    exact restrHom_mem hH hrad hO hx2
  by_contra hne
  push Not at hne
  obtain ⟨hn₁, hn₂⟩ := hne
  have ha : restrHom O₁ ⟨x, h₁ hxN⟩ ∈ H := by
    by_contra ha
    exact hn₁ ⟨_, restrHom_mem_normalizer hH hrad h₁ hxN,
      fun y hy => restrHom_apply_of_not_mem _ hy, ha, hsq O₁ h₁⟩
  have hb : restrHom O₁ᶜ ⟨x, h₁c hxN⟩ ∈ H := by
    by_contra hb
    refine hn₂ ⟨_, restrHom_mem_normalizer hH hrad h₁c hxN, fun y hy => ?_, hb, hsq O₁ᶜ h₁c⟩
    by_cases hy₁ : y ∈ O₁
    · exact restrHom_apply_of_not_mem _ (by simpa using hy₁)
    · rw [restrHom_apply_of_mem _ hy₁]
      exact hxO y (by simp [hy₁, hy])
  exact hxH (e ▸ mul_mem ha hb)

theorem exists_pow_not_mem_sq_mem {G : Type*} [Group G] {H : Subgroup G} {y : G} {m : ℕ}
    (hy : y ^ 2 ^ m = 1) (hyH : y ∉ H) : ∃ k, y ^ 2 ^ k ∉ H ∧ (y ^ 2 ^ k) ^ 2 ∈ H := by
  classical
  have hex : ∃ k, y ^ 2 ^ k ∈ H := ⟨m, by rw [hy]; exact one_mem _⟩
  have hk0 : Nat.find hex ≠ 0 := fun h0 => hyH (by simpa [h0] using Nat.find_spec hex)
  refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
  exact Nat.find_spec hex

theorem _root_.CFSG.GroupTheory.IsPIsolatedOver.exists_sq_mem_of_le
    {G : Type*} [Group G] [Finite G] {H N : Subgroup G}
    (hiso : IsPIsolatedOver 2 N H) (hH : IsPGroup 2 H) (hHN : H ≤ N)
    (hN : N ≤ normalizer (H : Set G)) : ∃ x ∈ N, x ∉ H ∧ x ^ 2 ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨S, T, hS, hT, hST⟩ := hiso
  have key : ∀ P, IsSylowOf 2 P N → P = H := fun P hP => by
    refine le_antisymm (fun y hy => ?_) (isSylowOf_le_of_le_normalizer hP hH hHN hN)
    by_contra hyH
    obtain ⟨m, hm⟩ := hP.isPGroup ⟨y, hy⟩
    obtain ⟨k, hk, hk2⟩ := exists_pow_not_mem_sq_mem (m := m)
      (by simpa using congrArg Subtype.val hm) hyH
    exact hne _ (pow_mem (hP.le hy) _) hk hk2
  exact hST (by rw [key S hS, key T hT]; exact Relation.EqvGen.refl _)

theorem _root_.CFSG.GroupTheory.IsPIsolatedOver.exists_sq_mem
    {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hH : IsPGroup 2 H) :
    ∃ x ∈ normalizer (H : Set G), x ∉ H ∧ x ^ 2 ∈ H :=
  IsPIsolatedOver.exists_sq_mem_of_le hiso hH le_normalizer le_rfl

omit [Fintype α] [DecidableEq α] in
theorem orbit_mem_setStab (x : α) :
    normalizer (H : Set (Perm α)) ≤ setStab (orbit (normalizer (H : Set (Perm α))) x) :=
  fun n hn z => by
    change (⟨n, hn⟩ : normalizer (H : Set (Perm α))) • z ∈ _ ↔ _
    rw [← orbit_eq_iff, orbit_smul, orbit_eq_iff]

omit [DecidableEq α] in
theorem exists_isEvenSet_orbit (hH : IsPGroup 2 H) (hrad : IsRadical H) :
    ∀ (m : ℕ) (O : Set α), O.ncard = m → normalizer (H : Set (Perm α)) ≤ setStab O →
      IsEvenSet H O → ∃ x ∈ O, IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro O hOm hO he
    classical
    obtain ⟨y, hyO⟩ : O.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      obtain ⟨x, -, hxO, hxH, -⟩ := he
      exact hxH (by rw [show x = 1 from Equiv.ext fun z => hxO z (by simp [hne])]; exact one_mem _)
    have hsub : orbit (normalizer (H : Set (Perm α))) y ⊆ O := by
      rintro _ ⟨⟨n, hn⟩, rfl⟩
      exact (hO hn y).mpr hyO
    rcases IsEvenSet.of_union hH hrad (orbit_mem_setStab y)
      (O₂ := O \ orbit (normalizer (H : Set (Perm α))) y)
      (by rwa [Set.union_diff_cancel hsub]) with h1 | h2
    · exact ⟨y, hyO, h1⟩
    · have hO₂ : normalizer (H : Set (Perm α)) ≤
          setStab (O \ orbit (normalizer (H : Set (Perm α))) y) := fun n hn z => by
        simp only [Set.mem_diff, (hO hn z), (orbit_mem_setStab y hn z)]
      have hlt : (O \ orbit (normalizer (H : Set (Perm α))) y).ncard < m := by
        rw [← hOm]
        exact Set.ncard_lt_ncard (Set.ssubset_iff_of_subset Set.diff_subset |>.mpr
          ⟨y, hyO, fun h => h.2 (mem_orbit_self y)⟩) (Set.toFinite O)
      obtain ⟨x, hx, hxe⟩ := ih _ hlt _ rfl hO₂ h2
      exact ⟨x, hx.1, hxe⟩

section Sec

variable (O : Set α) [DecidablePred (· ∈ O)]

omit [Fintype α] [DecidableEq α] [DecidablePred (· ∈ O)] in
theorem setStab_compl_le (hO : normalizer (H : Set (Perm α)) ≤ setStab O) :
    normalizer (H : Set (Perm α)) ≤ setStab Oᶜ := by
  rw [setStab_compl]
  exact hO

@[expose] def secOf (hO : normalizer (H : Set (Perm α)) ≤ setStab O) : Subgroup (Perm α) where
  carrier := {g | ∃ hg : g ∈ normalizer (H : Set (Perm α)),
    restrHom Oᶜ ⟨g, setStab_compl_le O hO hg⟩ ∈ H}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e := map_mul (restrHom Oᶜ) ⟨a, setStab_compl_le O hO ha⟩ ⟨b, setStab_compl_le O hO hb⟩
    exact (congrArg (· ∈ H) e).mpr (mul_mem ha' hb')
  one_mem' := ⟨one_mem _, by
    have e := map_one (restrHom Oᶜ)
    exact (congrArg (· ∈ H) e).mpr (one_mem _)⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e := map_inv (restrHom Oᶜ) ⟨a, setStab_compl_le O hO ha⟩
    exact (congrArg (· ∈ H) e).mpr (inv_mem ha')

variable {O}

omit [DecidableEq α] in
theorem le_secOf (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hO : normalizer (H : Set (Perm α)) ≤ setStab O) : H ≤ secOf O hO := fun _ hh =>
  ⟨le_normalizer hh, restrHom_mem hH hrad (setStab_compl_le O hO) hh⟩

omit [Fintype α] [DecidableEq α] in
theorem secOf_le (hO : normalizer (H : Set (Perm α)) ≤ setStab O) :
    secOf O hO ≤ normalizer (H : Set (Perm α)) := fun _ ⟨hg, _⟩ => hg

omit [DecidableEq α] in
theorem le_normalizer_secOf (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hO : normalizer (H : Set (Perm α)) ≤ setStab O) :
    normalizer (H : Set (Perm α)) ≤ normalizer (secOf O hO : Set (Perm α)) := by
  refine le_normalizer_of_conj_mem fun n hn g ⟨hg, hg'⟩ =>
    ⟨mul_mem (mul_mem hn hg) (inv_mem hn), ?_⟩
  have hc := setStab_compl_le O hO
  have e : restrHom Oᶜ ⟨n * g * n⁻¹, hc (mul_mem (mul_mem hn hg) (inv_mem hn))⟩ =
      restrHom Oᶜ ⟨n, hc hn⟩ * restrHom Oᶜ ⟨g, hc hg⟩ * (restrHom Oᶜ ⟨n, hc hn⟩)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  rw [e]
  exact (mem_normalizer_iff.mp (restrHom_mem_normalizer hH hrad hc hn) _).mp hg'

omit [DecidableEq α] in
theorem two_dvd_relIndex_secOf (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hO : normalizer (H : Set (Perm α)) ≤ setStab O) (he : IsEvenSet H O) :
    2 ∣ H.relIndex (secOf O hO) := by
  obtain ⟨x, hxN, hxO, hxH, hx2⟩ := he
  have h1 : restrHom Oᶜ ⟨x, setStab_compl_le O hO hxN⟩ = 1 := by
    ext z
    by_cases hz : z ∈ Oᶜ
    · rw [restrHom_apply_of_mem _ hz]
      exact hxO z hz
    · rw [restrHom_apply_of_not_mem _ hz]
      rfl
  exact two_dvd_relIndex_of_sq_mem (le_secOf hH hrad hO) ((secOf_le hO).trans le_rfl)
    ⟨hxN, by rw [h1]; exact one_mem _⟩ hxH hx2

end Sec

omit [Fintype α] [DecidableEq α] in
private theorem restrHom_restrHom {O O' : Set α} [DecidablePred (· ∈ O)] [DecidablePred (· ∈ O')]
    (hOO' : O ⊆ O'ᶜ) {g : Perm α} (hg : g ∈ setStab O) (hg' : g ∈ setStab O'ᶜ)
    (hr : restrHom O'ᶜ ⟨g, hg'⟩ ∈ setStab O) :
    restrHom O ⟨g, hg⟩ = restrHom O ⟨restrHom O'ᶜ ⟨g, hg'⟩, hr⟩ := by
  ext z
  by_cases hz : z ∈ O
  · rw [restrHom_apply_of_mem _ hz, restrHom_apply_of_mem _ hz,
      restrHom_apply_of_mem _ (hOO' hz)]
  · rw [restrHom_apply_of_not_mem _ hz, restrHom_apply_of_not_mem _ hz]

omit [DecidableEq α] in
theorem commutator_mem_of_mem_secOf (hH : IsPGroup 2 H) (hrad : IsRadical H) {O O' : Set α}
    [DecidablePred (· ∈ O)] [DecidablePred (· ∈ O')]
    (hO : normalizer (H : Set (Perm α)) ≤ setStab O)
    (hO' : normalizer (H : Set (Perm α)) ≤ setStab O') (hOO' : O ⊆ O'ᶜ) {g k : Perm α}
    (hg : g ∈ secOf O hO) (hk : k ∈ secOf O' hO') : g * k * g⁻¹ * k⁻¹ ∈ H := by
  obtain ⟨hgN, hg'⟩ := hg
  obtain ⟨hkN, hk'⟩ := hk
  have hc := setStab_compl_le O hO
  have hc' := setStab_compl_le O' hO'
  have hcN : g * k * g⁻¹ * k⁻¹ ∈ normalizer (H : Set (Perm α)) :=
    mul_mem (mul_mem (mul_mem hgN hkN) (inv_mem hgN)) (inv_mem hkN)
  refine (congrArg (· ∈ H) (restrHom_mul_restrHom_compl ⟨_, hO hcN⟩)).mp (mul_mem ?_ ?_)
  · have hkO : restrHom O ⟨k, hO hkN⟩ ∈ H := by
      rw [restrHom_restrHom hOO' (hO hkN) (hc' hkN)
        (hO (restrHom_mem_normalizer hH hrad hc' hkN))]
      exact restrHom_mem hH hrad hO hk'
    have e : restrHom O ⟨g * k * g⁻¹ * k⁻¹, hO hcN⟩ =
        restrHom O ⟨g, hO hgN⟩ * restrHom O ⟨k, hO hkN⟩ * (restrHom O ⟨g, hO hgN⟩)⁻¹ *
          (restrHom O ⟨k, hO hkN⟩)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp (restrHom_mem_normalizer hH hrad hO hgN) _).mp hkO)
      (inv_mem hkO)
  · show restrHom Oᶜ ⟨g * k * g⁻¹ * k⁻¹, hc hcN⟩ ∈ H
    have e : restrHom Oᶜ ⟨g * k * g⁻¹ * k⁻¹, hc hcN⟩ =
        restrHom Oᶜ ⟨g, hc hgN⟩ * (restrHom Oᶜ ⟨k, hc hkN⟩ * (restrHom Oᶜ ⟨g, hc hgN⟩)⁻¹ *
          (restrHom Oᶜ ⟨k, hc hkN⟩)⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact mul_mem hg' ((mem_normalizer_iff.mp (restrHom_mem_normalizer hH hrad hc hkN) _).mp
      (inv_mem hg'))

omit [DecidableEq α] in
theorem orbit_eq_of_isEvenSet (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x y : α}
    (hx : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x))
    (hy : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) y)) :
    orbit (normalizer (H : Set (Perm α))) x = orbit (normalizer (H : Set (Perm α))) y := by
  classical
  have hrad := isRadical_of_isPIsolatedOver hH hiso
  by_contra hne
  have hdisj : orbit (normalizer (H : Set (Perm α))) x ⊆
      (orbit (normalizer (H : Set (Perm α))) y)ᶜ := fun z hzx hzy =>
    hne ((orbit_eq_iff.mpr hzx).symm.trans (orbit_eq_iff.mpr hzy))
  refine not_isPIsolatedOver_of_commute hH le_normalizer le_rfl
    (le_secOf hH hrad (orbit_mem_setStab x)) (le_secOf hH hrad (orbit_mem_setStab y))
    (secOf_le _) (secOf_le _) (le_normalizer_secOf hH hrad _) (le_normalizer_secOf hH hrad _)
    (fun g hg k hk => commutator_mem_of_mem_secOf hH hrad _ _ hdisj hg hk)
    (two_dvd_relIndex_secOf hH hrad _ hx) (two_dvd_relIndex_secOf hH hrad _ hy) hiso

end CFSG.GroupTheory.AltCore
