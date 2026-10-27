module

public import CFSG.ClassicalInvolution.Asc77.AscC25W1
public import CFSG.ClassicalInvolution.Asc77.AscC25Y4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25W

section TwoGroup

variable {G : Type} [Group G] [Finite G]

@[expose] def InFour (a z y : G) : Prop := y = 1 ∨ y = a ∨ y = z ∨ y = a * z

theorem exists_mod_normal {S A T : Subgroup G} (hS : IsPGroup 2 ↥S) (hAS : A ≤ S)
    (hAn : ∀ s ∈ S, conjSub s A = A) (hTA : T ≤ A) (hTn : ∀ s ∈ S, conjSub s T = T)
    (hne : T ≠ A) : ∃ x ∈ A, x ∉ T ∧ ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ T := by
  classical
  let N : Subgroup ↥S := T.subgroupOf S
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ T := hn
    show ((g * n * g⁻¹ : ↥S) : G) ∈ T
    have : (g : G) * n * (g : G)⁻¹ ∈ conjSub (g : G) T := conj_mem_conjSub hn'
    rw [hTn g g.2] at this
    exact this⟩
  have := hNn
  have hQ2 : IsPGroup 2 (↥S ⧸ N) := hS.to_quotient N
  have hnil : Group.IsNilpotent (↥S ⧸ N) := hQ2.isNilpotent
  have hAsn : (A.subgroupOf S).Normal := ⟨fun a ha g => by
    have ha' : (a : G) ∈ A := ha
    show ((g * a * g⁻¹ : ↥S) : G) ∈ A
    have : (g : G) * a * (g : G)⁻¹ ∈ conjSub (g : G) A := conj_mem_conjSub ha'
    rw [hAn g g.2] at this
    exact this⟩
  let H : Subgroup (↥S ⧸ N) := (A.subgroupOf S).map (QuotientGroup.mk' N)
  have hHn : H.Normal :=
    Subgroup.Normal.map hAsn (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  obtain ⟨x₁, hx₁A, hx₁T⟩ : ∃ x ∈ A, x ∉ T := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hTA h)
  have hHbot : H ≠ ⊥ := by
    intro hbot
    have hmem : (QuotientGroup.mk (⟨x₁, hAS hx₁A⟩ : ↥S) : ↥S ⧸ N) ∈ H :=
      Subgroup.mem_map.mpr ⟨⟨x₁, hAS hx₁A⟩, hx₁A, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hx₁T hmem
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hHbot)
  obtain ⟨hcH, hcc⟩ := Subgroup.mem_inf.mp c.2
  obtain ⟨x', hx'A, hx'c⟩ := Subgroup.mem_map.mp hcH
  have hc1 : (c : ↥S ⧸ N) ≠ 1 := fun h => hc (Subtype.ext h)
  refine ⟨(x' : G), hx'A, fun hxT => hc1 ?_, fun s hs => ?_⟩
  · rw [← hx'c]
    exact (QuotientGroup.eq_one_iff _).mpr hxT
  · have hcent := Subgroup.mem_center_iff.mp hcc (QuotientGroup.mk (⟨s⁻¹, S.inv_mem hs⟩ : ↥S))
    rw [← hx'c] at hcent
    simp only [QuotientGroup.mk'_apply] at hcent
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcent
    have hT1 : (x' : G)⁻¹ * s * x' * s⁻¹ ∈ T := by
      have : (((⟨s⁻¹, S.inv_mem hs⟩ * x')⁻¹ * (x' * ⟨s⁻¹, S.inv_mem hs⟩) : ↥S) : G) ∈ T := hcent
      simpa [mul_assoc] using this
    have hxS : (x' : G) ∈ S := x'.2
    have h2 : (x' : G) * ((x' : G)⁻¹ * s * x' * s⁻¹) * (x' : G)⁻¹ ∈ conjSub (x' : G) T :=
      conj_mem_conjSub hT1
    rw [hTn x' hxS] at h2
    have e : s * (x' : G) * s⁻¹ * (x' : G)⁻¹ =
        (x' : G) * ((x' : G)⁻¹ * s * x' * s⁻¹) * (x' : G)⁻¹ := by group
    rw [e]
    exact h2

theorem exists_sq_mem_mod {S A F : Subgroup G} (hS : IsPGroup 2 ↥S) (hAS : A ≤ S)
    (hAn : ∀ s ∈ S, conjSub s A = A) (hFA : F ≤ A) (hFn : ∀ s ∈ S, conjSub s F = F)
    (hne : F ≠ A) :
    ∃ y ∈ A, y ∉ F ∧ y * y ∈ F ∧ ∀ s ∈ S, s * y * s⁻¹ * y⁻¹ ∈ F := by
  obtain ⟨x, hxA, hxF, hxc⟩ := exists_mod_normal hS hAS hAn hFA hFn hne
  obtain ⟨m, hm⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup hS (hAS hxA)
  induction m using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    rcases m with _ | _ | m
    · exfalso
      have : x = 1 := orderOf_eq_one_iff.mp (by simpa using hm)
      exact hxF (this ▸ F.one_mem)
    · refine ⟨x, hxA, hxF, ?_, hxc⟩
      have hxx : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rw [hm] at this
        simpa [pow_two] using this
      rw [hxx]
      exact F.one_mem
    · by_cases hxxF : x * x ∈ F
      · exact ⟨x, hxA, hxF, hxxF, hxc⟩
      · have hdvd : 2 ∣ orderOf x := by rw [hm]; exact dvd_pow_self 2 (Nat.succ_ne_zero _)
        have hxx_ord : orderOf (x * x) = 2 ^ (m + 1) := by
          rw [← pow_two, orderOf_pow_of_dvd (by norm_num) hdvd, hm]
          rw [pow_succ]; omega
        have hxS : x ∈ S := hAS hxA
        refine ih (m + 1) (by omega) (x * x) (A.mul_mem hxA hxA) hxxF (fun s hs => ?_) hxx_ord
        have hw := hxc s hs
        have h2 : x * (s * x * s⁻¹ * x⁻¹) * x⁻¹ ∈ conjSub x F := conj_mem_conjSub hw
        rw [hFn x hxS] at h2
        have e : s * (x * x) * s⁻¹ * (x * x)⁻¹ =
            (s * x * s⁻¹ * x⁻¹) * (x * (s * x * s⁻¹ * x⁻¹) * x⁻¹) := by group
        rw [e]
        exact F.mul_mem hw h2

end TwoGroup

section Ext

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}



theorem z_mem_zpowers_of_sq {y b : G} (hyz : y * y = z) (hz2 : z * z = 1)
    (hb : b ∈ Subgroup.zpowers y) (hb1 : b ≠ 1) : z ∈ Subgroup.zpowers b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.even_or_odd' k with ⟨k', hk | hk⟩
  · have h1 : y ^ k = z ^ k' := by rw [hk, zpow_mul, zpow_two, hyz]
    rcases C25Y.zpow_eq_one_or_self hz2 k' with h | h
    · exact absurd (h1.trans h) hb1
    · rw [h1, h]
      exact Subgroup.mem_zpowers z
  · refine ⟨2, ?_⟩
    have h1 : y ^ k = z ^ k' * y := by
      rw [hk, zpow_add_one, zpow_mul, zpow_two, hyz]
    have hzy : z * y = y * z := by
      have : y * (y * y) = (y * y) * y := by group
      rw [hyz] at this
      exact this.symm
    have hzc : z ^ k' * y = y * z ^ k' := (Commute.zpow_left (show Commute z y from hzy) k').eq
    show (y ^ k) ^ (2 : ℤ) = z
    rw [zpow_two, h1]
    calc z ^ k' * y * (z ^ k' * y) = z ^ k' * (y * z ^ k') * y := by group
      _ = z ^ k' * (z ^ k' * y) * y := by rw [← hzc]
      _ = (z ^ k' * z ^ k') * (y * y) := by group
      _ = z := by
        rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz2, one_zpow, one_mul, hyz]

theorem inFour_iff_mem_closure {a : G} (ha2 : a * a = 1) (hz2 : z * z = 1) (haz : a * z = z * a)
    {f : G} : InFour a z f ↔ f ∈ Subgroup.closure ({a, z} : Set G) := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · intro h
    exact C25Y.mem_closure_pair ha2 hz2 haz h

theorem conj_mem_closure_pair {a : G} {S : Sylow 2 G} (ha2 : a * a = 1) (hz2 : z * z = 1)
    (haz' : a * z = z * a)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z) :
    ∀ s ∈ (S : Subgroup G), ∀ g ∈ Subgroup.closure ({a, z} : Set G),
      s * g * s⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
  intro s hs g hg
  rcases C25Y.mem_closure_pair ha2 hz2 haz' hg with h | h | h | h
  · rw [h]
    simp
  · rw [h]
    rcases hconj s hs with h' | h'
    · rw [h']; exact Subgroup.subset_closure (by simp)
    · rw [h']
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rw [h, hzS s hs]; exact Subgroup.subset_closure (by simp)
  · rw [h]
    have e : s * (a * z) * s⁻¹ = (s * a * s⁻¹) * (s * z * s⁻¹) := by group
    rw [e, hzS s hs]
    rcases hconj s hs with h' | h'
    · rw [h']
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [h']
      have : a * z * z = a := by rw [mul_assoc, hz2, mul_one]
      rw [this]
      exact Subgroup.subset_closure (by simp)

theorem conjSub_closure_pair {a : G} {S : Sylow 2 G} (ha2 : a * a = 1) (hz2 : z * z = 1)
    (haz' : a * z = z * a)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z) :
    ∀ s ∈ (S : Subgroup G), conjSub s (Subgroup.closure ({a, z} : Set G)) =
      Subgroup.closure ({a, z} : Set G) := by
  intro s hs
  have hc := conj_mem_closure_pair ha2 hz2 haz' hconj hzS
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have := hc s hs _ hx
    simpa [mul_assoc] using this
  · intro hx
    have := hc s⁻¹ ((S : Subgroup G).inv_mem hs) _ hx
    simpa [mul_assoc] using this

theorem twisted_false {hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂} {a y : G}
    (ha2 : a * a = 1)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hy2 : InFour a z (y * y))
    (hyc : ∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹))
    (hyaz : y * a * y⁻¹ = a * z) : False := by
  have haS : a ∈ (S : Subgroup G) := haA.1
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have haz' : a * z = z * a := hyp.hzS a haS
  have hyS : y ∈ (S : Subgroup G) := hyA.1
  have hyz : y * z = z * y := hyp.hzS y hyS
  have hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z := by
    intro s hs
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
      _ = z := by group
  have hya : y * a = a * z * y := by
    calc y * a = (y * a * y⁻¹) * y := by group
      _ = a * z * y := by rw [hyaz]
  have hcomm_false : y * a = a * y → False := by
    intro hc
    have h1 : y * a * y⁻¹ = a := by rw [hc]; group
    rw [hyaz] at h1
    exact hz1 (mul_left_cancel (a := a) (b := z) (c := 1) (by rw [mul_one]; exact h1))
  have hy2' : y * y = 1 ∨ y * y = z := by
    rcases hy2 with h | h | h | h
    · exact Or.inl h
    · exfalso
      apply hcomm_false
      calc y * a = y * (y * y) := by rw [h]
        _ = (y * y) * y := by group
        _ = a * y := by rw [h]
    · exact Or.inr h
    · exfalso
      apply hcomm_false
      have h1 : y * (a * z) = (a * z) * y := by
        calc y * (a * z) = y * (y * y) := by rw [h]
          _ = (y * y) * y := by group
          _ = (a * z) * y := by rw [h]
      have h2 : (y * a) * z = (a * y) * z := by
        calc (y * a) * z = y * (a * z) := by group
          _ = (a * z) * y := h1
          _ = a * (z * y) := by group
          _ = a * (y * z) := by rw [hyz]
          _ = (a * y) * z := by group
      exact mul_right_cancel h2
  have hFc := conj_mem_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  have hFyc : ∀ s ∈ (S : Subgroup G),
      s * y * s⁻¹ * y⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := fun s hs =>
    (inFour_iff_mem_closure ha2 hz2 haz').mp (hyc s hs)
  obtain ⟨y', hy'A, hy'sq, hy'a, hy'c⟩ : ∃ y' : G,
      y' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      y' * y' = z ∧ y' * a = a * z * y' ∧
      ∀ s ∈ (S : Subgroup G), s * y' * s⁻¹ * y'⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
    rcases hy2' with h | h
    ·
      refine ⟨y * a, Subgroup.mul_mem _ hyA haA, ?_, ?_, ?_⟩
      · calc y * a * (y * a) = (y * a * y⁻¹) * (y * y) * a := by group
          _ = a * z * 1 * a := by rw [hyaz, h]
          _ = a * (z * a) := by rw [mul_one]; group
          _ = a * (a * z) := by rw [haz']
          _ = (a * a) * z := by group
          _ = z := by rw [ha2, one_mul]
      · calc y * a * a = y := by rw [mul_assoc, ha2, mul_one]
          _ = a * z * (a * z * y) := by
            calc y = (a * z * a * z) * y := by
                  have : a * z * a * z = 1 := by
                    calc a * z * a * z = a * (z * a) * z := by group
                      _ = a * (a * z) * z := by rw [haz']
                      _ = (a * a) * (z * z) := by group
                      _ = 1 := by rw [ha2, hz2, one_mul]
                  rw [this, one_mul]
              _ = a * z * (a * z * y) := by group
          _ = a * z * (y * a) := by rw [hya]
      · intro s hs
        have hsa : s * a * s⁻¹ * a⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
          have := hFc s hs a (Subgroup.subset_closure (by simp))
          exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        have h3 := Subgroup.mul_mem _ (hFyc s hs) (hFc y hyS _ hsa)
        convert h3 using 1
        group
    · exact ⟨y, hyA, h, hya, hFyc⟩
  have hy'S : y' ∈ (S : Subgroup G) := hy'A.1
  have hy'z : y' * z = z * y' := hyp.hzS y' hy'S
  have hy'az : y' * (a * z) = a * y' := by
    calc y' * (a * z) = (y' * a) * z := by group
      _ = (a * z * y') * z := by rw [hy'a]
      _ = a * z * (y' * z) := by group
      _ = a * z * (z * y') := by rw [hy'z]
      _ = a * (z * z) * y' := by group
      _ = a * y' := by rw [hz2, mul_one]
  have haz4 : a * z * a * z = 1 := by
    calc a * z * a * z = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [haz']
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2, one_mul]
  have hy'zp : z ∈ Subgroup.zpowers y' := ⟨2, by show y' ^ (2 : ℤ) = z; rw [zpow_two, hy'sq]⟩
  have hBc : ∀ s ∈ (S : Subgroup G), s * y' * s⁻¹ ∈ Subgroup.zpowers y' := by
    intro s hs
    set w := s * y' * s⁻¹ with hw
    have hww : w * w = z := by
      calc w * w = s * (y' * y') * s⁻¹ := by rw [hw]; group
        _ = z := by rw [hy'sq, hzS s hs]
    have hwf : w = (w * y'⁻¹) * y' := by group
    have hf := hy'c s hs
    rcases C25Y.mem_closure_pair ha2 hz2 haz' hf with h | h | h | h
    · have : w = y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = y'; rw [h, one_mul]
      rw [this]
      exact Subgroup.mem_zpowers y'
    · exfalso
      have hw' : w = a * y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = a * y'; rw [h]
      have h1 : (a * y') * (a * y') = 1 := by
        calc (a * y') * (a * y') = a * (y' * a) * y' := by group
          _ = a * (a * z * y') * y' := by rw [hy'a]
          _ = (a * a) * z * (y' * y') := by group
          _ = 1 := by rw [ha2, hy'sq, one_mul, hz2]
      rw [hw', h1] at hww
      exact hz1 hww.symm
    · have : w = z * y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = z * y'; rw [h]
      rw [this]
      exact Subgroup.mul_mem _ hy'zp (Subgroup.mem_zpowers y')
    · exfalso
      have hw' : w = a * z * y' := by
        rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = a * z * y'; rw [h]
      have h1 : (a * z * y') * (a * z * y') = 1 := by
        calc (a * z * y') * (a * z * y') = a * z * (y' * (a * z)) * y' := by group
          _ = a * z * (a * y') * y' := by rw [hy'az]
          _ = (a * z * a) * (y' * y') := by group
          _ = (a * z * a) * z := by rw [hy'sq]
          _ = 1 := haz4
      rw [hw', h1] at hww
      exact hz1 hww.symm
  have hBc' : ∀ s ∈ (S : Subgroup G), ∀ b ∈ Subgroup.zpowers y',
      s * b * s⁻¹ ∈ Subgroup.zpowers y' := by
    intro s hs b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hBc s hs) k
  have hBn : ∀ s ∈ (S : Subgroup G), conjSub s (Subgroup.zpowers y') = Subgroup.zpowers y' := by
    intro s hs
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have := hBc' s hs _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hBc' s⁻¹ ((S : Subgroup G).inv_mem hs) _ hx
      simpa [mul_assoc] using this
  have hBS : Subgroup.zpowers y' ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hy'S
  have hall : ∀ b ∈ Subgroup.zpowers y', b ≠ 1 →
      z ∈ zStarOf (Subgroup.centralizer ({b} : Set G)) := fun b hb hb1 =>
    good_of_mem_zpowers (z_mem_zpowers_of_sq hy'sq hz2 hb hb1)
  have hE := T7T.c25_5_proved (p := p) (f := f) G Ω K K' W S R R' z t u₁ u₂ hyp
    (Subgroup.zpowers y') hy'zp hBS hBn hall
  have hy'z' : y' ∈ Subgroup.zpowers z := hE ▸ Subgroup.mem_zpowers y'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'z'
  have h1 : y' * y' = 1 := by
    rcases C25Y.zpow_eq_one_or_self hz2 k with h | h
    · rw [← hk, h]; simp
    · rw [← hk, h]; exact hz2
  rw [hy'sq] at h1
  exact hz1 h1

end Ext

section Residual

section Def

variable (p f : ℕ) [Fact p.Prime]

@[expose] def CentExt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            y * a = a * y → InFour a z (y * y) →
            (∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) → InFour a z y

end Def

section Reduction

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}



theorem fourExhausts_of_centExt (hExt : CentExt p f)
    {hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂} {a : G}
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))) :
    ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      InFour a z b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbA, hbF⟩ := hcon
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have haS : a ∈ (S : Subgroup G) := haA.1
  have haz' : a * z = z * a := hyp.hzS a haS
  have hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z := by
    intro s hs
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
      _ = z := by group
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
    with hA
  set F : Subgroup G := Subgroup.closure ({a, z} : Set G) with hF
  have hFA : F ≤ A := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact haA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hzA
  have hFne : F ≠ A := by
    intro hFA'
    apply hbF
    exact (inFour_iff_mem_closure ha2 hz2 haz').mpr (by rw [← hF, hFA']; exact hbA)
  have hAn : ∀ s ∈ (S : Subgroup G), conjSub s A = A := fun s hs =>
    T7T.conjSub_centralizer_of_hyp hyp hs
  have hFn := conjSub_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  have hFc := conj_mem_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  obtain ⟨y, hyA, hyF, hy2, hyc⟩ := exists_sq_mem_mod S.isPGroup' inf_le_left hAn hFA hFn hFne
  have hyS : y ∈ (S : Subgroup G) := hyA.1
  have hyaF : y * a * y⁻¹ ∈ F := hFc y hyS a (Subgroup.subset_closure (by simp))
  rcases C25Y.mem_closure_pair ha2 hz2 haz' hyaF with h | h | h | h
  · exfalso
    apply ha1
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · apply hyF
    have hcomm : y * a = a * y := by
      calc y * a = (y * a * y⁻¹) * y := by group
        _ = a * y := by rw [h]
    exact (inFour_iff_mem_closure ha2 hz2 haz').mp
      (hExt G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hcomm
        ((inFour_iff_mem_closure ha2 hz2 haz').mpr hy2)
        fun s hs => (inFour_iff_mem_closure ha2 hz2 haz').mpr (hyc s hs))
  · exfalso
    apply haz
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = y⁻¹ * z * y := by rw [h]
      _ = z := by
        have := hyp.hzS y hyS
        calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
          _ = y⁻¹ * (y * z) := by rw [this]
          _ = z := by group
  · exact twisted_false (hyp := hyp) ha2 haA hconj hyA
      ((inFour_iff_mem_closure ha2 hz2 haz').mpr hy2)
      (fun s hs => (inFour_iff_mem_closure ha2 hz2 haz').mpr (hyc s hs)) h

end Reduction

end Residual

end C25W

end CFSG.ClassicalInvolution.Asc77
