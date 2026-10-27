module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBUnique
import CFSG.LocalAnalysis.ComponentClassification.Asc75T4RankOneBasic
import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Faithful

public section

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)

namespace CFSG.ComponentClassification.GS79bSec5

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem perfect_le_of_le_centralizer_of_mulEquiv {K : Type} [Field K] [Finite K]
    (e : (A ⧸ center A) ≃* projectiveSL 3 K) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPt : P ≤ centralizer ({d.t} : Set G)) : P ≤ A := by
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer A) := by
    have : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer (projectiveSL 3 K)) :=
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_schreier
        (K := K) (n := 3) le_rfl).2
    have : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer (A ⧸ center A)) :=
      CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
    have : Group.IsPerfect A := ⟨d.sector.standard.1.1⟩
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient A
  have hK : Group.IsSolvable
      (centralizer (A : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
    have : Group.IsSolvable (centralizer (A : Set G)) :=
      CFSG.ComponentClassification.Asc75T4.RankOne.isSolvable_of_isCyclic_sylow d.R
        d.sector.cyclic
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  exact CFSG.SeitzReduction.perfect_le_of_isSolvable_outer (L := A)
    (H := centralizer ({d.t} : Set G)) hOut
    (CFSG.SeitzReduction.le_centralizer_of_mem_centralizer d.t_mem_K)
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard d.sector.standard d.t_mem_K
      d.sector.t_order) hK hP hPt

theorem range_linearSwapDiag_eq_of_mulEquiv {K : Type} [Field K] [Finite K]
    (e : (A ⧸ center A) ≃* projectiveSL 3 K) {A' : Subgroup G} (hq : CFSG.Open.IsQuasisimple A')
    (hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G))
    (he' : Nonempty (↥A' ⧸ center ↥A' ≃* projectiveSL 3 K)) :
    (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').range = A := by
  obtain ⟨e'⟩ := he'
  have : Group.IsPerfect A' := ⟨hq.1⟩
  have : Group.IsPerfect A := ⟨d.sector.standard.1.1⟩
  set δ' := CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA' with hδ'
  have hHperf : ⁅δ'.range, δ'.range⁆ = δ'.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.SeitzReduction.LinearPilot.commutator_map_eq_of_commutator_eq δ' (by
      rw [← commutator_def]
      exact hq.1)
  have hHle : δ'.range ≤ A :=
    perfect_le_of_le_centralizer_of_mulEquiv e hHperf
      (CFSG.SeitzReduction.LinearPilot.range_linearSwapDiag_le_centralizer d.t_mul_self hA')
  by_contra hne
  have hlt : δ'.range < A := lt_of_le_of_ne hHle hne
  have hindex := CFSG.LocalAnalysis.ComponentInitial.index_center_lt_of_lt hlt
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at hindex
  have hker : δ'.rangeRestrict.ker ≤ center A' := by
    rw [MonoidHom.ker_rangeRestrict]
    exact CFSG.SeitzReduction.LinearPilot.ker_linearSwapDiag_le_center hA'
  have hcard : Nat.card (↥δ'.range ⧸ center ↥δ'.range) = Nat.card (↥A ⧸ center ↥A) :=
    Nat.card_congr (((CFSG.ComponentClassification.PerfectCentralQuotient.equivalence
      δ'.rangeRestrict (MonoidHom.rangeRestrict_surjective δ') hker).symm.trans e').trans
      e.symm).toEquiv
  exact (ne_of_lt hindex) hcard

private theorem exists_liftSq_data {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : FrameData A d.V K) {f : ℕ} (hKc : Nat.card K = 2 ^ f) {i : Fin 2}
    (w : WData d (F.rad i) (2 ^ f)) {A' : Subgroup G}
    (hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G))
    (hinv : ∀ z ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom, z * z = 1 → z = 1)
    (hker : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker ≤ center A')
    (hodd : Odd (Nat.card (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker))
    (hrange : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').range = A) :
    ∃ (R : Subgroup A') (R' : Subgroup G), R' = R.map A'.subtype ∧
      (∀ x, x ∈ R ↔
        CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA' x ∈ F.rad i ∧ x * x = 1) ∧
      R' ≤ A' ∧
      (∀ x ∈ R', ∀ y ∈ R', x * y = y * x) ∧
      (∀ x ∈ R', x * x = 1) ∧
      (∀ x ∈ R', ∀ y ∈ R', x * (d.t * y * d.t) = d.t * y * d.t * x) ∧
      (∀ r ∈ R', r * (d.t * r * d.t) ∈ F.rad i) ∧
      (∀ v ∈ F.rad i, ∃ r ∈ R', r * (d.t * r * d.t) = v) ∧
      (R' ⊓ R'.map (MulAut.conj d.t).toMonoidHom = ⊥) ∧
      Nat.card R' * Nat.card R' = (2 ^ f) ^ 4 := by
  have htt := d.t_mul_self
  set δ' := CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA' with hδ'
  have hδ'app : ∀ x : A', δ' x = x * (d.t * x * d.t) := fun x => by
    rw [hδ', CFSG.SeitzReduction.LinearPilot.linearSwapDiag_apply, mul_conj_inv_eq htt]
  obtain ⟨hVile, hVie, hVicard⟩ : F.rad i ≤ d.V ∧ CFSG.Open.IsElemAbelian 2 (F.rad i) ∧
      Nat.card (F.rad i) = Nat.card K ^ 2 := by
    fin_cases i
    · exact F.radicals.property (Or.inl rfl)
    · exact F.radicals.property (Or.inr rfl)
  have hVic : ∀ a ∈ F.rad i, ∀ b ∈ F.rad i, a * b = b * a :=
    fun a ha b hb => comm_of_isElemAbelian hVie ha hb
  have hVi2 : ∀ a ∈ F.rad i, a * a = 1 := fun a ha => by
    rw [← sq]; exact hVie.2 a ha
  have hViA : F.rad i ≤ A := hVile.trans d.V_isSylow.le
  obtain ⟨R, hRmem⟩ := exists_liftSq hker hodd (F.rad i) hVic
  have hViδ : F.rad i ≤ δ'.range := by rw [hrange]; exact hViA
  have hRmap := map_liftSq hodd hViδ hVi2 hRmem
  have hRcard := card_liftSq hodd hViδ hVi2 hRmem
  set R' := R.map A'.subtype with hR'
  have hR'A : R' ≤ A' := map_subtype_le R
  have hR'c : ∀ x ∈ R', ∀ y ∈ R', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (comm_of_liftSq hker hodd hVic hRmem x hx y hy)
  have hR'2 : ∀ x ∈ R', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val ((hRmem x).1 hx).2
  have hR't : ∀ x ∈ R', ∀ y ∈ R', x * (d.t * y * d.t) = d.t * y * d.t * x := by
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨y0, hy0, rfl⟩ := hy
    have hy' : d.t * (y0 : G) * d.t ∈ A'.map (MulAut.conj d.t).toMonoidHom :=
      conj_mem_map_conj htt y0.2
    exact mem_centralizer_iff.1 (hA' hy') (x0 : G) x0.2
  have hR'δ : ∀ r ∈ R', r * (d.t * r * d.t) ∈ F.rad i := by
    rintro _ ⟨r, hr, rfl⟩
    have := ((hRmem r).1 hr).1
    rwa [hδ'app] at this
  have hR'onto : ∀ v ∈ F.rad i, ∃ r ∈ R', r * (d.t * r * d.t) = v := by
    intro v hv
    rw [← hRmap] at hv
    obtain ⟨r, hr, rfl⟩ := hv
    exact ⟨r, ⟨r, hr, rfl⟩, (hδ'app r).symm⟩
  have hR'inf : R' ⊓ R'.map (MulAut.conj d.t).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    exact mem_bot.2 (hinv z ⟨hR'A hz1, map_mono hR'A hz2⟩ (hR'2 z hz1))
  have hR'card : Nat.card R' * Nat.card R' = (2 ^ f) ^ 4 := by
    rw [hR', Subgroup.card_map_of_injective A'.subtype_injective, hRcard, hVicard, hKc]
    ring
  exact ⟨R, R', hR', hRmem, hR'A, hR'c, hR'2, hR't, hR'δ, hR'onto, hR'inf, hR'card⟩

private theorem lift_le_M_sup_of_frameData {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : FrameData A d.V K) {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) {i : Fin 2}
    {w : WData d (F.rad i) (2 ^ f)} (N : CaseBNotation w (F.leviData i))
    (hB : w.CaseB (F.leviData i).lev.range) {A' : Subgroup G}
    (hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G))
    (hinv : ∀ z ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom, z * z = 1 → z = 1)
    (hker : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker ≤ center A')
    (hodd : Odd (Nat.card (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker))
    (hrange : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').range = A)
    {X : Subgroup A'} (hXp : ⁅X, X⁆ = X)
    (hXL : X.map (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA') ≤
      (F.leviData i).lev.range) :
    X.map A'.subtype ≤ N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom := by
  obtain ⟨R, R', hR'def, hRmem, hR'A, hR'c, hR'2, hR't, hR'δ, hR'onto, hR'inf, hR'card⟩ :=
    exists_liftSq_data F hKc w hA' hinv hker hodd hrange
  have hW : w.W = R' ⊔ R'.map (MulAut.conj d.t).toMonoidHom :=
    w.eq_sup_of_lift hR'c hR'2 hR't hR'δ hR'onto hR'inf hR'card
  have hXN : X.map A'.subtype ≤ w.N := by
    subst R'
    rintro _ ⟨x, hx, rfl⟩
    refine CaseBModule.mem_normalizer_of_map_le ?_
    rw [hW, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      have hxL : CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA' x ∈
          (F.leviData i).lev.range := hXL ⟨x, hx, rfl⟩
      have hxN := WData.levRange_le_normalizer (F.leviData i) hxL
      have hmem : x * r * x⁻¹ ∈ R := by
        refine (hRmem _).2 ⟨?_, ?_⟩
        · rw [map_mul, map_mul, map_inv]
          exact (mem_normalizer_iff.1 hxN _).1 ((hRmem r).1 hr).1
        · rw [show x * r * x⁻¹ * (x * r * x⁻¹) = x * (r * r) * x⁻¹ by group,
            ((hRmem r).1 hr).2, mul_one, mul_inv_cancel]
      exact mem_sup_left ⟨_, hmem, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyA : y ∈ A'.map (MulAut.conj d.t).toMonoidHom := map_mono hR'A hy
      have hxy : (x : G) * y * (x : G)⁻¹ = y := by
        rw [mem_centralizer_iff.1 (hA' hyA) x x.2, mul_inv_cancel_right]
      change (x : G) * y * (x : G)⁻¹ ∈
        R.map A'.subtype ⊔ (R.map A'.subtype).map (MulAut.conj d.t).toMonoidHom
      rw [hxy]
      exact mem_sup_right hy
  exact N.perfect_le_M_sup hB hf hKc hXN (by rw [← map_commutator, hXp])

private theorem le_sup_of_perfect_lifts {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : FrameData A d.V K) {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f)
    {w₀ : WData d (F.rad 0) (2 ^ f)} {w₁ : WData d (F.rad 1) (2 ^ f)}
    (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    {G₁ A' : Subgroup G} (hq' : CFSG.Open.IsQuasisimple A')
    (hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G))
    (hinv : ∀ z ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom, z * z = 1 → z = 1)
    (hker : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker ≤ center A')
    (hodd : Odd (Nat.card (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker))
    (hrange : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').range = A)
    (hM₀ : N₀.M₁ ⊔ N₀.M₁.map (MulAut.conj d.t).toMonoidHom ≤
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom)
    (hM₁ : N₁.M₁ ⊔ N₁.M₁.map (MulAut.conj d.t).toMonoidHom ≤
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom) :
    A' ≤ G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom := by
  have : Group.IsPerfect A' := ⟨hq'.1⟩
  set δ' := CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA' with hδ'
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hlevA : ∀ i : Fin 2, (F.leviData i).lev.range ≤ δ'.range := fun i => by
    rw [hrange]
    rintro _ ⟨B, rfl⟩
    exact (F.leviData i).lev_mem B
  obtain ⟨X₀, hX₀p, hX₀map, -⟩ :=
    exists_liftPerfect hker (WData.commutator_levRange hK3 (F.leviData 0)) (hlevA 0)
  obtain ⟨X₁, hX₁p, hX₁map, -⟩ :=
    exists_liftPerfect hker (WData.commutator_levRange hK3 (F.leviData 1)) (hlevA 1)
  have hle₀ := lift_le_M_sup_of_frameData (F := F) (i := 0) hf hKc N₀ hB₀ hA' hinv hker hodd
    hrange hX₀p (hX₀map.le : X₀.map _ ≤ (F.leviData 0).lev.range)
  have hle₁ := lift_le_M_sup_of_frameData (F := F) (i := 1) hf hKc N₁ hB₁ hA' hinv hker hodd
    hrange hX₁p (hX₁map.le : X₁.map _ ≤ (F.leviData 1).lev.range)
  have htop : X₀ ⊔ X₁ = ⊤ := by
    refine CFSG.SeitzReduction.LinearPilot.eq_top_of_sup_center_eq_top_of_perfect
      (eq_top_iff.2 fun y _ => ?_)
    have hy : δ' y ∈ (X₀ ⊔ X₁).map δ' := by
      rw [Subgroup.map_sup, hX₀map, hX₁map, F.sup_lev_range, ← hrange]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy
    have hk : x⁻¹ * y ∈ δ'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [show y = x * (x⁻¹ * y) by group]
    exact mul_mem (mem_sup_left hx) (mem_sup_right (hker hk))
  intro x hx
  have hmem : (⟨x, hx⟩ : A') ∈ X₀ ⊔ X₁ := htop ▸ mem_top _
  have h2 : x ∈ (X₀ ⊔ X₁).map A'.subtype := ⟨⟨x, hx⟩, hmem, rfl⟩
  rw [Subgroup.map_sup] at h2
  exact (sup_le (hle₀.trans hM₀) (hle₁.trans hM₁)) h2

omit [Finite G] in
private theorem eq_one_of_mem_centralizer_of_odd_center {X : Subgroup G}
    (hZ : Odd (Nat.card (center ↥X))) {y : G} (hyX : y ∈ X)
    (hyC : y ∈ centralizer (X : Set G)) (hy : y * y = 1) : y = 1 := by
  have hy' : (⟨y, hyX⟩ : ↥X) ∈ center ↥X := by
    rw [mem_center_iff]
    intro w
    exact Subtype.ext (mem_centralizer_iff.1 hyC (w : G) w.2)
  have hj : (⟨y, hyX⟩ : ↥X) ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact Subtype.ext hy
  exact congrArg Subtype.val
    (CFSG.ComponentClassification.Asc75T4.eq_one_of_mem_of_odd hZ hy' (j := 1) hj)

omit [Finite G] in
private theorem eq_one_of_mem_conjugate_inf_of_odd_center {G₁ G₂ : Subgroup G}
    (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    (hZ : Odd (Nat.card (center ↥(G₁ ⊔ G₂)))) {g z : G}
    (hz1 : z ∈ CFSG.conjugate G₁ g) (hz2 : z ∈ CFSG.conjugate G₂ g) (hzsq : z * z = 1) :
    z = 1 := by
  have h1 : g * z * g⁻¹ ∈ G₁ := CFSG.SeitzReduction.F4Pilot.mem_conjugate_iff_of_mul.1 hz1
  have h2 : g * z * g⁻¹ ∈ G₂ := CFSG.SeitzReduction.F4Pilot.mem_conjugate_iff_of_mul.1 hz2
  have hsq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hzsq, mul_one,
      mul_inv_cancel]
  have hcent : g * z * g⁻¹ ∈ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
    refine zpowers_le.1 (Subgroup.le_centralizer_iff.1 (sup_le ?_ ?_))
    · rw [Subgroup.le_centralizer_iff]
      exact zpowers_le.2 (h₁₂ h2)
    · rw [Subgroup.le_centralizer_iff]
      refine zpowers_le.2 (mem_centralizer_iff.2 fun x hx => ?_)
      exact (mem_centralizer_iff.1 (h₁₂ hx) (g * z * g⁻¹) h1).symm
  have key : g * z * g⁻¹ = 1 :=
    eq_one_of_mem_centralizer_of_odd_center hZ (mem_sup_left h1) hcent hsq
  calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
    _ = 1 := by rw [key, mul_one, inv_mul_cancel]

private theorem odd_card_ker_linearSwapDiag_of_inv {A' : Subgroup G}
    (hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G))
    (hinv : ∀ z ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom, z * z = 1 → z = 1) :
    Odd (Nat.card (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker) := by
  have htt := d.t_mul_self
  set δ' := CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA' with hδ'
  have hδ'app : ∀ x : A', δ' x = x * (d.t * x * d.t) := fun x => by
    rw [hδ', CFSG.SeitzReduction.LinearPilot.linearSwapDiag_apply, mul_conj_inv_eq htt]
  have hinv' : ∀ x ∈ δ'.ker, x * x = 1 → x = 1 := by
    intro x hx hx2
    have h1 : (x : G) * (d.t * x * d.t) = 1 := by rw [← hδ'app]; exact hx
    have hx2' : (x : G) * x = 1 := by rw [← Subgroup.coe_mul, hx2, Subgroup.coe_one]
    have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2'
    have h2 : d.t * x * d.t = x := by
      rw [eq_inv_of_mul_eq_one_right h1, hxinv]
    have hmem : (x : G) ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom :=
      ⟨x.2, (mem_map_conj_iff htt).2 (by rw [h2]; exact x.2)⟩
    exact Subtype.ext (hinv _ hmem hx2')
  refine (CFSG.BrauerSuzuki.Helpers.odd_natCard_iff_no_involution ↥δ'.ker).2 ?_
  intro y hy
  have hy2 : (y : A') * y = 1 := by
    rw [← Subgroup.coe_mul, ← sq, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
  have hy1 : y = 1 := Subtype.ext (hinv' y y.2 hy2)
  rw [hy1, orderOf_one] at hy
  exact absurd hy (by norm_num)

private theorem conjugate_eq_of_le_of_swap {G₁ G₂ A' : Subgroup G} {g : G}
    (hG₂ : G₂ = G₁.map (MulAut.conj d.t).toMonoidHom)
    (hA' : A' = CFSG.conjugate G₁ g) (hle : A' ≤ G₁ ⊔ G₂)
    (hswap : A'.map (MulAut.conj d.t).toMonoidHom = CFSG.conjugate G₂ g) :
    CFSG.conjugate (G₁ ⊔ G₂) g = G₁ ⊔ G₂ := by
  have htG₀ : d.t ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
    rw [hG₂]
    exact CFSG.SeitzReduction.F4Pilot.mem_normalizer_sup_of_map_conj_eq d.t_mul_self rfl
  have hle₁ : CFSG.conjugate G₁ g ≤ G₁ ⊔ G₂ := by
    rw [← hA']
    exact hle
  have hB'le : CFSG.conjugate G₂ g ≤ G₁ ⊔ G₂ := by
    rw [← hswap, hA']
    calc (CFSG.conjugate G₁ g).map (MulAut.conj d.t).toMonoidHom ≤
          (G₁ ⊔ G₂).map (MulAut.conj d.t).toMonoidHom := map_mono hle₁
      _ = G₁ ⊔ G₂ :=
          CFSG.SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 htG₀
  have hle' : CFSG.conjugate (G₁ ⊔ G₂) g ≤ G₁ ⊔ G₂ := by
    rw [CFSG.conjugate, Subgroup.map_sup]
    exact sup_le hle₁ hB'le
  exact Subgroup.eq_of_le_of_card_ge hle'
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).ge

theorem conjugate_eq_of_swap_of_frameData {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : FrameData A d.V K) (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f)
    {w₀ : WData d (F.rad 0) (2 ^ f)} {w₁ : WData d (F.rad 1) (2 ^ f)}
    (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hZ : Odd (Nat.card (center ↥(G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom))))
    (he₁ : Nonempty (↥G₁ ⧸ center ↥G₁ ≃* projectiveSL 3 K))
    (hM₀ : N₀.M₁ ⊔ N₀.M₁.map (MulAut.conj d.t).toMonoidHom ≤
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom)
    (hM₁ : N₁.M₁ ⊔ N₁.M₁.map (MulAut.conj d.t).toMonoidHom ≤
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom)
    (g : G) (hswap : (CFSG.conjugate G₁ g).map (MulAut.conj d.t).toMonoidHom =
      CFSG.conjugate (G₁.map (MulAut.conj d.t).toMonoidHom) g) :
    CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom) g =
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom := by
  have htt := d.t_mul_self
  set G₂ := G₁.map (MulAut.conj d.t).toMonoidHom with hG₂
  set A' := CFSG.conjugate G₁ g with hA'def
  set B' := CFSG.conjugate G₂ g with hB'def
  have hBA : B' ≤ centralizer (A' : Set G) :=
    CFSG.SeitzReduction.LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ g
  have hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G) := by
    rw [hswap]
    exact hBA
  have hinv : ∀ z ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom, z * z = 1 → z = 1 := by
    intro z hz hz2
    rw [hswap] at hz
    rw [hA'def] at hz
    exact eq_one_of_mem_conjugate_inf_of_odd_center h₁₂ hZ hz.1 hz.2 hz2
  have hq' : CFSG.Open.IsQuasisimple A' :=
    CFSG.SeitzReduction.LinearPilot.isQuasisimple_conjugate hq g
  have he' : Nonempty (↥A' ⧸ center ↥A' ≃* projectiveSL 3 K) :=
    he₁.map fun e₁ =>
      (CFSG.SeitzReduction.LinearPilot.conjugateQuotientCenterEquiv G₁ g).symm.trans e₁
  have hrange : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').range = A :=
    range_linearSwapDiag_eq_of_mulEquiv e hq' hA' he'
  have hker : (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker ≤ center A' :=
    CFSG.SeitzReduction.LinearPilot.ker_linearSwapDiag_le_center hA'
  have hodd : Odd (Nat.card (CFSG.SeitzReduction.LinearPilot.linearSwapDiag hA').ker) :=
    odd_card_ker_linearSwapDiag_of_inv hA' hinv
  have hA'le : A' ≤ G₁ ⊔ G₂ :=
    le_sup_of_perfect_lifts F hf hKc N₀ N₁ hB₀ hB₁ hq' hA' hinv hker hodd hrange hM₀ hM₁
  exact conjugate_eq_of_le_of_swap hG₂ hA'def hA'le hswap

end CFSG.ComponentClassification.GS79bSec5

end
