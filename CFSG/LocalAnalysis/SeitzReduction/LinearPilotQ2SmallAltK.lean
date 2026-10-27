module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallAlt
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent)

section Fixed

theorem fix_and_card_of_properFixedComponent_alternating {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {τ : Perm (Fin n)} {P : Subgroup (alternatingGroup (Fin n))}
    (h : ProperFixedComponent (MulAut.conjNormal τ) P) :
    (∀ x ∈ P, ∀ i : Fin n, τ i ≠ i → (x : Perm (Fin n)) i = i) ∧
      5 ≤ Nat.card (MulAction.fixedPoints (zpowers τ) (Fin n)) ∧
      Nat.card P = (Nat.card (MulAction.fixedPoints (zpowers τ) (Fin n))).factorial / 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hσ1 := h.ne_one
  obtain ⟨hσ, hPF, hP, -⟩ := h
  set c := (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
    Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) with hcdef
  have hcapp : ∀ x : alternatingGroup (Fin n), ((c τ x : alternatingGroup (Fin n)) : Perm (Fin n))
      = τ * x * τ⁻¹ := fun x => rfl
  have hττ : τ * τ = 1 := by
    apply hbij.1
    rw [map_mul, map_one]
    ext x
    rw [MulAut.mul_apply, hσ, MulAut.one_apply]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact hσ1 (map_one c)
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hττ) hτ1
  set Q : Subgroup (Perm (Fin n)) := zpowers τ with hQdef
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  set N := normalizer (Q : Set (Perm (Fin n))) with hNdef
  set F := fixedSubgroup (c τ) with hFdef
  have hmemF : ∀ x : alternatingGroup (Fin n), x ∈ F ↔ τ * (x : Perm (Fin n)) = x * τ := by
    intro x
    change c τ x = x ↔ _
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      calc τ * (x : Perm (Fin n)) = τ * x * τ⁻¹ * τ := by group
        _ = x * τ := by rw [h1]
    · intro hx
      apply Subtype.ext
      rw [hcapp, hx]
      group
  have hcN : ∀ g : Perm (Fin n), τ * g = g * τ → g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQdef, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  let ι : F →* N := ((alternatingGroup (Fin n)).subtype.comp F.subtype).codRestrict N
    fun x => hcN _ ((hmemF x.1).mp x.2)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = ((y : alternatingGroup (Fin n)) :
        Perm (Fin n)) := congrArg (fun z : N => (z : Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h1)
  set R : Subgroup N := (alternatingGroup (Fin n)).subgroupOf N with hRdef
  have hR : R.Normal := inferInstance
  have hrange : ι.range = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (x : alternatingGroup (Fin n)).2
    · intro y hy
      have hyA : (y : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hy
      have hyτ : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ = τ := by
        have hord : orderOf ((y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rw [← hk] at hord ⊢
        rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_zero,
            orderOf_one] at hord
          omega
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_one]
      have hcomm : τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ := by
        calc τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin n)) * τ := by group
      exact ⟨⟨⟨y, hyA⟩, (hmemF ⟨y, hyA⟩).mpr hcomm⟩, Subtype.ext rfl⟩
  let e₁ : F ≃* R := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  set L₀ := P.subgroupOf F with hL₀def
  have hL₁ : IsPComponent 2 (L₀.map e₁.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁ hP
  have hL := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_of_normal_subgroup 2 R
    (L₀.map e₁.toMonoidHom) hL₁
  set Lc := (L₀.map e₁.toMonoidHom).map R.subtype with hLdef
  obtain ⟨hdeg, hLeq, -⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ Lc hL
  have himg : ∀ x : alternatingGroup (Fin n), ∀ hxP : x ∈ P,
      ι ⟨x, hPF hxP⟩ ∈ Lc := by
    intro x hxP
    refine ⟨e₁ ⟨x, hPF hxP⟩, ⟨⟨x, hPF hxP⟩, mem_subgroupOf.2 hxP, rfl⟩, ?_⟩
    rfl
  refine ⟨fun x hxP i hi => ?_, hdeg, ?_⟩
  · have h1 := himg x hxP
    rw [hLeq] at h1
    obtain ⟨f, -, hf⟩ := h1
    have h2 : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((CFSG.ComponentClassification.CatalogueBAlternating.fixedPointsNormalizerHom Q f : N) :
          Perm (Fin n)) := by
      rw [hf]
      rfl
    have hnot : i ∉ MulAction.fixedPoints Q (Fin n) := by
      intro hfix
      exact hi (hfix ⟨τ, mem_zpowers τ⟩)
    rw [h2, CFSG.ComponentClassification.CatalogueBAlternating.fixedPointsNormalizerHom_coe,
      Perm.ofSubtype_apply_of_not_mem _ hnot]
  · have : Nontrivial (MulAction.fixedPoints Q (Fin n)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have h1 : Nat.card P = Nat.card Lc := by
      rw [hLdef, Subgroup.card_map_of_injective R.subtype_injective,
        Subgroup.card_map_of_injective e₁.injective, hL₀def,
        Nat.card_congr (P.subgroupOfEquivOfLe hPF).toEquiv]
    rw [h1, hLeq, Subgroup.card_map_of_injective
      (CFSG.ComponentClassification.CatalogueBAlternating.fixedPointsNormalizerHom_injective Q),
      nat_card_alternatingGroup]

end Fixed

section Degree

theorem card_fixedPoints_add_card_support {k : ℕ} {π : Perm (Fin k)} :
    Nat.card (MulAction.fixedPoints (zpowers π) (Fin k)) + π.support.card = k := by
  classical
  have hfix : ∀ i : Fin k, i ∈ MulAction.fixedPoints (zpowers π) (Fin k) ↔ π i = i := by
    intro i
    constructor
    · intro h
      exact h ⟨π, mem_zpowers π⟩
    · intro h g
      obtain ⟨g, hg⟩ := g
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
      change (π ^ m) i = i
      exact (Perm.zpow_apply_eq_self_of_apply_eq_self h m)
  have h1 : Nat.card (MulAction.fixedPoints (zpowers π) (Fin k)) =
      (Finset.univ.filter fun i => π i = i).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i => by rw [hfix]; simp)
  rw [h1, Perm.support, Finset.card_filter_add_card_filter_not, Finset.card_univ,
    Fintype.card_fin]

theorem swap_mul_swap_comm_of_pairwise_ne {k : ℕ} {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d = swap c d * swap a b := by
  have h : Perm.Disjoint (swap a b) (swap c d) := by
    rw [Perm.disjoint_iff_disjoint_support, Perm.support_swap hab, Perm.support_swap hcd]
    simp [Finset.disjoint_left, hac, had, hbc, hbd]
  exact h.commute.eq

set_option linter.unusedSimpArgs false in
theorem klein_of_two_cycles {k : ℕ} {a b c d : Fin k} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin k) ∧
      swap a c * swap b d ∈ alternatingGroup (Fin k) ∧
      (swap a b * swap c d) * (swap a c * swap b d) =
        (swap a c * swap b d) * (swap a b * swap c d) ∧
      swap a c * swap b d ≠ 1 ∧ swap a c * swap b d ≠ swap a b * swap c d := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hac, Perm.sign_swap hbd]
    decide
  · ext i
    simp only [Perm.mul_apply]
    by_cases hia : i = a
    · subst hia; simp [swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
        had.symm, hbc.symm, hbd.symm, hcd.symm]
    by_cases hib : i = b
    · subst hib; simp [swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
        had.symm, hbc.symm, hbd.symm, hcd.symm]
    by_cases hic : i = c
    · subst hic; simp [swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
        had.symm, hbc.symm, hbd.symm, hcd.symm]
    by_cases hid : i = d
    · subst hid; simp [swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
        had.symm, hbc.symm, hbd.symm, hcd.symm]
    simp [swap_apply_of_ne_of_ne, hia, hib, hic, hid]
  · intro h
    have := congrArg (fun f : Perm (Fin k) => f a) h
    simp [swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
      had.symm] at this
  · intro h
    have := congrArg (fun f : Perm (Fin k) => f a) h
    simp [swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
      had.symm, hbc.symm, hbd.symm, hcd.symm] at this

theorem exists_klein_alternatingGroup {k : ℕ} {a b c d : Fin k} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ U : Subgroup (alternatingGroup (Fin k)), IsPGroup 2 U ∧ 2 < Nat.card U ∧
      ∀ u ∈ U, ∀ i : Fin k, i ≠ a → i ≠ b → i ≠ c → i ≠ d → (u : Perm (Fin k)) i = i := by
  classical
  obtain ⟨h1, h2, hcomm, hx2, hx12⟩ := klein_of_two_cycles hab hac had hbc hbd hcd
  set x₁ : alternatingGroup (Fin k) := ⟨_, h1⟩ with hx₁
  set x₂ : alternatingGroup (Fin k) := ⟨_, h2⟩ with hx₂
  have hx₁x₂ : x₁ * x₂ = x₂ * x₁ := Subtype.ext hcomm
  have hsq₁ : x₁ * x₁ = 1 := by
    apply Subtype.ext
    change swap a b * swap c d * (swap a b * swap c d) = 1
    have hc : swap a b * swap c d = swap c d * swap a b :=
      swap_mul_swap_comm_of_pairwise_ne hab hcd hac had hbc hbd
    calc swap a b * swap c d * (swap a b * swap c d) =
        swap a b * (swap c d * swap a b) * swap c d := by group
      _ = swap a b * (swap a b * swap c d) * swap c d := by rw [hc]
      _ = 1 := by simp [← mul_assoc]
  have hsq₂ : x₂ * x₂ = 1 := by
    apply Subtype.ext
    change swap a c * swap b d * (swap a c * swap b d) = 1
    have hc : swap a c * swap b d = swap b d * swap a c :=
      swap_mul_swap_comm_of_pairwise_ne hac hbd hab had hbc.symm hcd
    calc swap a c * swap b d * (swap a c * swap b d) =
        swap a c * (swap b d * swap a c) * swap b d := by group
      _ = swap a c * (swap a c * swap b d) * swap b d := by rw [hc]
      _ = 1 := by simp [← mul_assoc]
  set U : Subgroup (alternatingGroup (Fin k)) := closure {x₁, x₂} with hU
  have hUC : U ≤ centralizer ({x₁, x₂} : Set (alternatingGroup (Fin k))) := by
    rw [hU, closure_le]
    rintro y (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
      rintro z (rfl | rfl) <;> simp [hx₁x₂]
  have hUcomm : ∀ g ∈ U, ∀ h ∈ U, g * h = h * g := by
    intro g hg h hh
    have hle : U ≤ centralizer ({g} : Set (alternatingGroup (Fin k))) := by
      rw [hU, closure_le]
      rintro y (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      · exact (mem_centralizer_iff.1 (hUC hg) _ (Set.mem_insert _ _))
      · exact (mem_centralizer_iff.1 (hUC hg) _ (Set.mem_insert_of_mem _ rfl))
    exact (mem_centralizer_singleton_iff.1 (hle hh)).symm
  have hUsq : ∀ g ∈ U, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hsq₁
      · exact hsq₂
    | one => exact mul_one 1
    | mul g h hgU hhU hg hh =>
      calc g * h * (g * h) = g * (h * g) * h := by group
        _ = g * (g * h) * h := by rw [hUcomm h hhU g hgU]
        _ = (g * g) * (h * h) := by group
        _ = 1 := by rw [hg, hh, mul_one]
    | inv g hgU hg =>
      rw [← mul_inv_rev, hg, inv_one]
  refine ⟨U, fun g => ⟨1, ?_⟩, ?_, ?_⟩
  · rw [pow_one, sq]
    exact Subtype.ext (hUsq g g.2)
  · have : Fintype U := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
    refine ⟨1, ⟨x₁, subset_closure (Set.mem_insert _ _)⟩,
      ⟨x₂, subset_closure (Set.mem_insert_of_mem _ rfl)⟩, ?_, ?_, ?_⟩
    · intro h
      have h' := congrArg (fun z : U => ((z : alternatingGroup (Fin k)) : Perm (Fin k)) a) h
      simp [hx₁, swap_apply_of_ne_of_ne, hab, hac, had] at h'
    · intro h
      have h' := congrArg (fun z : U => ((z : alternatingGroup (Fin k)) : Perm (Fin k))) h
      exact hx2 h'.symm
    · intro h
      have h' := congrArg (fun z : U => ((z : alternatingGroup (Fin k)) : Perm (Fin k))) h
      exact hx12 h'.symm
  · intro u hu i hia hib hic hid
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · simp [hx₁, swap_apply_of_ne_of_ne, hia, hib, hic, hid]
      · simp [hx₂, swap_apply_of_ne_of_ne, hia, hib, hic, hid]
    | one => rfl
    | mul g h _ _ hg hh =>
      simp only [Subgroup.coe_mul, Perm.mul_apply, hh, hg]
    | inv g _ hg =>
      simp only [Subgroup.coe_inv]
      rw [Perm.inv_eq_iff_eq]
      exact hg.symm

end Degree

section Component

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_ten_of_alternating {Kc : Subgroup Y} {k : ℕ} (ε : Kc ≃* alternatingGroup (Fin k))
    {s : Y} (hsN : s ∈ normalizer (Kc : Set Y)) (hs2 : s * s = 1)
    (hsK : s ∉ centralizer (Kc : Set Y)) {D : Subgroup Y} (hDK : D ≤ Kc) (hDne : D ≠ Kc)
    (hDs : D ≤ centralizer ({s} : Set Y))
    (hDcomp : IsComponent (D.subgroupOf (Kc ⊓ centralizer ({s} : Set Y))))
    (hDc : Nat.card D = 20160)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2) :
    k = 10 := by
  classical
  have hk8 : 8 ≤ k := by
    have h1 : Nat.card D ∣ Nat.card Kc := Subgroup.card_dvd_of_le hDK
    by_contra hk
    push Not at hk
    have hk2 : 2 ≤ k := by
      by_contra h2
      push Not at h2
      have : Subsingleton (Fin k) := by
        interval_cases k <;> infer_instance
      have hc : Nat.card Kc = 1 := by
        rw [Nat.card_congr ε.toEquiv]
        exact Nat.card_unique
      rw [hc, hDc] at h1
      exact absurd h1 (by decide)
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk2
    rw [Nat.card_congr ε.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hDc] at h1
    interval_cases k <;> revert h1 <;> decide
  have : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  set τ := Kc.normalizerMonoidHom ⟨s, hsN⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN (by rw [sq]; exact hs2)
  have hPC : ProperFixedComponent τ (D.subgroupOf Kc) := by
    refine ⟨fun y => ?_, ?_, ?_, ?_⟩
    · rw [← MulAut.mul_apply, hτ2, MulAut.one_apply]
    · rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
      intro x hx
      exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
    · exact LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
        (F4Pilot.isComponent_subgroupOf_subgroupOf
          (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp)
    · intro htop
      apply hDne
      refine le_antisymm hDK fun x hx => ?_
      have h1 : (⟨x, hx⟩ : Kc) ∈ D.subgroupOf Kc := htop ▸ mem_top _
      exact mem_subgroupOf.1 h1
  obtain ⟨hPC', -⟩ := hPC.map ε
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj k
    (by omega) (by omega)
  obtain ⟨π, hπ⟩ := hbij.2 (MulAut.congr ε τ)
  rw [← hπ] at hPC'
  obtain ⟨hfix, -, hcard⟩ := fix_and_card_of_properFixedComponent_alternating (by omega)
    (by omega) hPC'
  have hDA : Nat.card ((D.subgroupOf Kc).map ε.toMonoidHom) = 20160 := by
    rw [Subgroup.card_map_of_injective ε.injective,
      Nat.card_congr (D.subgroupOfEquivOfLe hDK).toEquiv, hDc]
  rw [hDA] at hcard
  have hfix8 : Nat.card (MulAction.fixedPoints (zpowers π) (Fin k)) = 8 := by
    generalize Nat.card (MulAction.fixedPoints (zpowers π) (Fin k)) = m at hcard ⊢
    have hm9 : m ≤ 8 := by
      by_contra h
      push Not at h
      have h1 := Nat.factorial_le (show 9 ≤ m by omega)
      have h9 : (9 : ℕ).factorial = 362880 := by decide
      omega
    interval_cases m
    all_goals first | rfl | (norm_num [Nat.factorial] at hcard)
  have hππ : π * π = 1 := by
    apply hbij.1
    rw [map_mul, hπ, ← map_mul, hτ2, map_one, map_one]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply hsK
    rw [mem_centralizer_iff]
    intro q hq
    have h1 : MulAut.congr ε τ = 1 := by rw [← hπ, map_one]
    have h2 : τ = 1 := (MulAut.congr ε).injective (by rw [h1, map_one])
    have h3 : τ ⟨q, hq⟩ = ⟨q, hq⟩ := by rw [h2, MulAut.one_apply]
    have h4 := congrArg Subtype.val h3
    rw [hτ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h4
    calc q * s = s * q * s⁻¹ * s := by rw [h4]
      _ = s * q := by group
  have hπ2 : orderOf π = 2 := orderOf_eq_prime (by rw [sq]; exact hππ) hπ1
  have hsupp : π.support.card ≤ 3 := by
    by_contra h4
    push Not at h4
    obtain ⟨T, hTs, hT4⟩ := Finset.exists_subset_card_eq (show 4 ≤ π.support.card by omega)
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 hT4
    obtain ⟨U, hU2, hU3, hUfix⟩ := exists_klein_alternatingGroup hab hac had hbc hbd hcd
    have hmem : ∀ i ∈ ({a, b, c, d} : Finset (Fin k)), π i ≠ i := fun i hi =>
      Perm.mem_support.1 (hTs hi)
    set W : Subgroup Y := (U.map ε.symm.toMonoidHom).map Kc.subtype with hW
    have hWc : Nat.card W = Nat.card U := by
      rw [hW, Subgroup.card_map_of_injective Kc.subtype_injective,
        Subgroup.card_map_of_injective ε.symm.injective]
    have hWp : IsPGroup 2 W := (hU2.map ε.symm.toMonoidHom).map Kc.subtype
    have hWD : W ≤ centralizer (D : Set Y) := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      have hxA : ε ⟨x, hDK hx⟩ ∈ (D.subgroupOf Kc).map ε.toMonoidHom :=
        ⟨⟨x, hDK hx⟩, mem_subgroupOf.2 hx, rfl⟩
      have hdisj : Perm.Disjoint ((ε ⟨x, hDK hx⟩ : alternatingGroup (Fin k)) : Perm (Fin k))
          (u : Perm (Fin k)) := by
        intro i
        by_cases hi : i ∈ ({a, b, c, d} : Finset (Fin k))
        · exact Or.inl (hfix _ hxA i (hmem i hi))
        · right
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
          exact hUfix u hu i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
      have hcomm : ε ⟨x, hDK hx⟩ * u = u * ε ⟨x, hDK hx⟩ := Subtype.ext hdisj.commute.eq
      have h1 : (⟨x, hDK hx⟩ : Kc) * ε.symm u = ε.symm u * ⟨x, hDK hx⟩ := by
        apply ε.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcomm]
      exact congrArg Subtype.val h1
    have := hsyl W hWp hWD
    omega
  obtain ⟨r, hr⟩ := Perm.cycleType_prime_order (σ := π) (by rw [hπ2]; exact Nat.prime_two)
  rw [hπ2] at hr
  have hsum := Perm.sum_cycleType π
  rw [hr, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk := card_fixedPoints_add_card_support (π := π)
  omega

end Component

section Setting

open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_alternating_linear_two (hset : SeitzSetting G L) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin 6} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 6 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin 6))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) < Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    {k : ℕ} (hA : Nonempty (Kc ≃* alternatingGroup (Fin k))) : False := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ε⟩ := hA
  obtain ⟨-, -, -, -, hcomp, hsyl, -, -⟩ :=
    neighbour_hyps_linear_two hset hK e (by norm_num) htC ht hab hX₀ hX₀c hX htX hDe
  obtain ⟨-, -, ⟨eDb⟩⟩ :=
    nonempty_map_oddCore_mulEquiv_specialLinear_two hK e (by norm_num) htC hab hX₀ hX₀c hX hDe
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin (6 - 2)) K) = 20160 := by
    have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    rw [Matrix.card_SL_field, hq]
    decide
  have hDbc : Nat.card ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = 20160 := by
    rw [Nat.card_congr eDb.toEquiv, hcardSL]
  have hs : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hs2 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← sq, ← hs, pow_orderOf_eq_one]
  have hDs := hcomp.1
  have hDc : IsComponent (((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))) :=
    (isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
  have hk : k = 10 := eq_ten_of_alternating ε hsN hs2 hsC hDK.le hDK.ne hDs hDcomp hDbc hsyl
  subst hk
  exact false_of_alternating_ten_linear_two hset hK e htC ht hab hX₀ hX₀c hX htX hDe hKc hDK.le
    hsN hsC ⟨ε⟩

theorem sporadic_of_neighbourOvergroupSLmSmall_six (hset : SeitzSetting G L) {K : Type}
    [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin 6} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 6 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin 6))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (h : NeighbourOvergroupSLmSmall (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 1) :
    ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc ∧
      (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) < Kc ∧
      Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom = Kc ∧
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
        centralizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) ∧
      center Kc = ⊥ ∧ CFSG.Blueprint.NativeSporadic.SporadicRep (Kc ⧸ center Kc) := by
  obtain ⟨Kc, hKc, hDK, hKt, hsC, hZ, -, hsm⟩ := h
  refine ⟨Kc, hKc, hDK, hKt, hsC, hZ, ?_⟩
  rcases hsm with ⟨-, ⟨k, -, ⟨φ⟩⟩⟩ | ⟨h3, -⟩ | ⟨-, hsp⟩
  · exfalso
    have hsN := mem_normalizer_iff_map_conj_eq.2 hKt
    exact false_of_alternating_linear_two hset hK e htC ht hab hX₀ hX₀c hX htX hDe hKc hDK hsN
      hsC ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ⟩
  · exact absurd h3 (by norm_num)
  · exact hsp

end Setting

end CFSG.SeitzReduction.LinearPilot
