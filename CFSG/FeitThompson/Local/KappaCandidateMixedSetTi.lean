module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Representations.CanonicalPiSetComponent
import CFSG.FeitThompson.Local.MixedElementsKappaCandidateTorus
import CFSG.FeitThompson.Local.KappaFixedCoreMeetsNoConjugateMaximal
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

variable {G : Type*} [Group G]

theorem mem_mixedTorusSet_iff [Finite G] {Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G} {x : G} :
    x ∈ mixedTorusSet Z I KT ↔ x ∈ Z ∧ x ≠ 1 ∧ ∀ V ∈ I, x ∉ kappaA KT V := by
  constructor
  · rintro ⟨⟨hxZ, hx1⟩, hx⟩
    have hx1' : x ≠ 1 := by simpa using hx1
    exact ⟨hxZ, hx1', fun V hV hmem => hx (Set.mem_biUnion hV ⟨hmem, hx1⟩)⟩
  · rintro ⟨hxZ, hx1, hx⟩
    refine ⟨⟨hxZ, by simpa using hx1⟩, fun hmem => ?_⟩
    obtain ⟨V, hV, hmem'⟩ := Set.mem_iUnion₂.1 hmem
    exact hx V hV hmem'.1

theorem mixedTorusSet_subset [Finite G] {Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G} : mixedTorusSet Z I KT ⊆ (Z : Set G) :=
  fun _ hx => (mem_mixedTorusSet_iff.1 hx).1

theorem le_normalizer_mixedTorusSet [Finite G] {Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G}
    (hAnorm : ∀ V ∈ I, Z ≤ normalizer ((kappaA KT V : Subgroup G) : Set G)) :
    Z ≤ normalizer (mixedTorusSet Z I KT) := by
  intro z hz
  rw [mem_set_normalizer_iff]
  intro h
  rw [mem_mixedTorusSet_iff, mem_mixedTorusSet_iff]
  constructor
  · rintro ⟨hhZ, hh1, hhA⟩
    refine ⟨mul_mem (mul_mem hz hhZ) (inv_mem hz), ?_, fun V hV hmem => ?_⟩
    · exact fun hc => hh1 (by
        have hh : h = z⁻¹ * (z * h * z⁻¹) * z := by group
        rw [hh, hc]; group)
    · exact hhA V hV ((mem_normalizer_iff.1 (hAnorm V hV hz) h).2 hmem)
  · rintro ⟨hhZ, hh1, hhA⟩
    have hh : h = z⁻¹ * (z * h * z⁻¹) * z := by group
    refine ⟨by rw [hh]; exact mul_mem (mul_mem (inv_mem hz) hhZ) hz, ?_, fun V hV hmem => ?_⟩
    · exact fun hc => hh1 (by rw [hc]; group)
    · exact hhA V hV ((mem_normalizer_iff.1 (hAnorm V hV hz) h).1 hmem)

theorem mem_of_mem_of_isHallPiOf [Finite G] {π : Set ℕ} {Y X : Subgroup G}
    (hY : IsHallPiOf π Y X) {x : G} (hx : x ∈ Y) {r : ℕ} (hr : r ∈ (orderOf x).primeFactors) :
    r ∈ π :=
  hY.2.1 r (Nat.primeFactors_mono (Y.orderOf_dvd_natCard hx) Nat.card_pos.ne' hr)

theorem isPiNumber_orderOf_of_isHallPiOf [Finite G] {π : Set ℕ} {Y X : Subgroup G}
    (hY : IsHallPiOf π Y X) {x : G} (hx : x ∈ Y) :
    CoprimeComponent.IsPiNumber π (orderOf x) :=
  CoprimeComponent.isPiNumber_iff_forall_prime.2
    ⟨orderOf_pos x, fun _ hr hrd =>
      mem_of_mem_of_isHallPiOf hY hx (Nat.mem_primeFactors.2 ⟨hr, hrd, (orderOf_pos x).ne'⟩)⟩

theorem mem_of_isHallPiOf_of_le_normalizer [Finite G] {π : Set ℕ} {Y X : Subgroup G}
    (hY : IsHallPiOf π Y X) (hn : X ≤ normalizer (Y : Set G))
    {x : G} (hx : x ∈ X) (hprimes : ∀ r ∈ (orderOf x).primeFactors, r ∈ π) : x ∈ Y := by
  have hnormal : (Y.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hY.1).2 hn
  have hcard : Nat.card ↥(Y.subgroupOf X) = Nat.card ↥Y := by
    rw [← Subgroup.card_subtype X (Y.subgroupOf X), Subgroup.map_subgroupOf_eq_of_le hY.1]
  have hHall : IsHallPiSubgroup π (Y.subgroupOf X) :=
    ⟨isPiSubgroup_iff.2 fun r hr => hY.2.1 r (by rwa [hcard] at hr), fun r hr => hY.2.2 r hr⟩
  have hord : orderOf (⟨x, hx⟩ : ↥X) = orderOf x := (orderOf_coe (⟨x, hx⟩ : ↥X)).symm
  have hiff := hHall.mem_iff (⟨x, hx⟩ : ↥X)
  rw [mem_subgroupOf, hord] at hiff
  exact hiff.2 hprimes

theorem mem_of_mem_mixedTorusSet_of_conj_mem [Finite G] {Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G}
    (hdesc : mixedTorusSet Z I KT
      = ⋃ V ∈ I, {x : G | ∃ a ∈ kappaA KT V, a ≠ 1 ∧ ∃ b ∈ KT V, b ≠ 1 ∧ x = a * b})
    (hZV : ∀ V ∈ I, Z ≤ V)
    (hAhall : ∀ V ∈ I, IsHallPiOf (sigmaPrimes V) (kappaA KT V) Z)
    (hKhall : ∀ V ∈ I, IsHallPiOf (sigmaPrimes V)ᶜ (KT V) Z)
    (hKnorm : ∀ V ∈ I, Z ≤ normalizer ((KT V : Subgroup G) : Set G))
    (hZeq : ∀ V ∈ I, Z = normalizer ((KT V : Subgroup G) : Set G) ⊓ V)
    (hfix : ∀ V ∈ I, ∀ g : G, g ∉ V → kappaA KT V ⊓ conjBy V g = ⊥)
    (hti : ∀ V ∈ I, ∀ g ∈ V, g ∉ normalizer ((KT V : Subgroup G) : Set G) →
      KT V ⊓ conjBy (KT V) g = ⊥)
    (t g : G) (ht : t ∈ mixedTorusSet Z I KT) (hu : g⁻¹ * t * g ∈ mixedTorusSet Z I KT) :
    g ∈ Z := by
  have huZ : g⁻¹ * t * g ∈ Z := mixedTorusSet_subset hu
  rw [hdesc] at ht
  obtain ⟨V, hV, a, ha, ha1, b, hb, hb1, hab⟩ := Set.mem_iUnion₂.1 ht
  have hcomm : Commute a b := mul_comm_of_mem_kappaA ha hb
  have hapi : CoprimeComponent.IsPiNumber (sigmaPrimes V) (orderOf a) :=
    isPiNumber_orderOf_of_isHallPiOf (hAhall V hV) ha
  have hbpi : CoprimeComponent.IsPiPrimeNumber (sigmaPrimes V) (orderOf b) :=
    CoprimeComponent.isPiPrimeNumber_iff.2 (isPiNumber_orderOf_of_isHallPiOf (hKhall V hV) hb)
  obtain ⟨hae, hbe⟩ := CoprimeComponent.eq_piComponent_of_mul_eq hcomm hab.symm hapi hbpi
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1
    (CoprimeComponent.piComponent_mem_powers (sigmaPrimes V) t)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1
    (CoprimeComponent.piComponent_mem_powers (sigmaPrimes V)ᶜ t)
  have hatn : a = t ^ n := by rw [hae, ← hn]
  have hbtm : b = t ^ m := by rw [hbe, ← hm]
  have hconjpow : ∀ k : ℕ, g⁻¹ * t ^ k * g = (g⁻¹ * t * g) ^ k := fun k => by
    have h := conj_pow (a := g⁻¹) (b := t) (i := k)
    simpa using h.symm
  have hag : g⁻¹ * a * g ∈ V := by
    rw [hatn, hconjpow n]; exact hZV V hV (pow_mem huZ n)
  have hginv : g⁻¹ ∈ V := by
    by_contra hgV
    have hmem : a ∈ kappaA KT V ⊓ conjBy V g⁻¹ :=
      Subgroup.mem_inf.2 ⟨ha, mem_conjBy.2 (by simpa using hag)⟩
    rw [hfix V hV g⁻¹ hgV] at hmem
    exact ha1 (by simpa using hmem)
  have hbgZ : g⁻¹ * b * g ∈ Z := by rw [hbtm, hconjpow m]; exact pow_mem huZ m
  have hbgK : g⁻¹ * b * g ∈ KT V := by
    refine mem_of_isHallPiOf_of_le_normalizer (hKhall V hV) (hKnorm V hV) hbgZ fun r hr => ?_
    have horder : orderOf (g⁻¹ * b * g) = orderOf b :=
      (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * b = g⁻¹ * b * g * g⁻¹ by group)).symm
    rw [horder] at hr
    exact mem_of_mem_of_isHallPiOf (hKhall V hV) hb hr
  have hgn : g⁻¹ ∈ normalizer ((KT V : Subgroup G) : Set G) := by
    by_contra hgn
    have hmem : b ∈ KT V ⊓ conjBy (KT V) g⁻¹ :=
      Subgroup.mem_inf.2 ⟨hb, mem_conjBy.2 (by simpa using hbgK)⟩
    rw [hti V hV g⁻¹ hginv hgn] at hmem
    exact hb1 (by simpa using hmem)
  rw [hZeq V hV]
  exact Subgroup.mem_inf.2 ⟨by simpa using inv_mem hgn, by simpa using inv_mem hginv⟩

theorem FNI_kappa_candidate_mixed_set_ti
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_candidate_family_common_factors.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_candidate_mixed_set_ti.{u} := by
  intro G _ _ M K A Z I KT hs
  have hamb : Prep03.IsAmbient G := hs.base.ambient
  have hFT : IsFTAmbient G :=
    ⟨hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.odd_natCard, hamb.forall_isSolvable⟩
  obtain ⟨-, -, hmain, -⟩ := h₂ G M K A Z I hs.base hs.I_eq
  obtain ⟨hknonempty, hb, -⟩ := hmain KT hs.KT_self hs.KT_hall
  have hcoatom : ∀ V ∈ I, IsCoatom V := by
    intro V hV
    rw [hs.I_eq] at hV
    rcases hV with h | h
    · rw [h]; exact hs.base.isCoatom
    · exact h.1
  have hhall : ∀ V ∈ I, IsHallPiOf (kappaPrimes V) (KT V) V := by
    intro V hV
    by_cases hVM : V = M
    · subst hVM; rw [hs.KT_self]; exact hs.base.isHall_K
    · exact (hs.KT_hall V hV hVM).1
  have hhall' : ∀ V ∈ I, IsHallPiSubgroupOf (kappaPrimes V) (KT V) V := fun V hV =>
    isHallPiSubgroupOf_of_isHallPiOf (hhall V hV) fun _ _ => Iff.rfl
  have htiV := FTS_kappa_hall_local_ti h₃ h₄
  have hfixV := FTS_kappa_fixed_core_outside_conjugate_disjoint h₁ h₄ h₅
  obtain ⟨hdesc, hne, -⟩ := FNI_kappa_candidate_mixed_set_description h₂ G M K A Z I KT hs
  have hZV : ∀ V ∈ I, Z ≤ V := fun V hV => le_of_lt (hb V hV).2.2.2.1
  have hAhall : ∀ V ∈ I, IsHallPiOf (sigmaPrimes V) (kappaA KT V) Z := fun V hV =>
    (hb V hV).2.2.2.2.2.2.1
  have hKhall : ∀ V ∈ I, IsHallPiOf (sigmaPrimes V)ᶜ (KT V) Z := fun V hV =>
    (hb V hV).2.2.2.2.1
  have hKnorm : ∀ V ∈ I, Z ≤ normalizer ((KT V : Subgroup G) : Set G) := fun V hV =>
    (hb V hV).2.2.2.2.2.1
  have hAnorm : ∀ V ∈ I, Z ≤ normalizer ((kappaA KT V : Subgroup G) : Set G) := fun V hV =>
    (hb V hV).2.2.2.2.2.2.2
  have hZeq : ∀ V ∈ I, Z = normalizer ((KT V : Subgroup G) : Set G) ⊓ V := fun V hV =>
    (hb V hV).2.2.1
  have hfix : ∀ V ∈ I, ∀ g : G, g ∉ V → kappaA KT V ⊓ conjBy V g = ⊥ := fun V hV g hg =>
    hfixV G hFT V (hcoatom V hV) (hknonempty V hV) (KT V) (hhall' V hV) g hg
  have hti : ∀ V ∈ I, ∀ g ∈ V, g ∉ normalizer ((KT V : Subgroup G) : Set G) →
      KT V ⊓ conjBy (KT V) g = ⊥ := fun V hV g hgV hgn =>
    (htiV G hFT V (hcoatom V hV) (hknonempty V hV) (KT V) (hhall' V hV)).1 g hgV hgn
  have hkey : ∀ t g : G, t ∈ mixedTorusSet Z I KT → g⁻¹ * t * g ∈ mixedTorusSet Z I KT → g ∈ Z :=
    mem_of_mem_mixedTorusSet_of_conj_mem hdesc hZV hAhall hKhall hKnorm hZeq hfix hti
  refine ⟨le_antisymm (fun g hg => ?_) (le_normalizer_mixedTorusSet hAnorm), fun g hg => ?_⟩
  ·
    obtain ⟨t, ht⟩ := hne
    have hginv : g⁻¹ ∈ normalizer (mixedTorusSet Z I KT) := inv_mem hg
    have ht' : g⁻¹ * t * g ∈ mixedTorusSet Z I KT := by
      have h := (mem_set_normalizer_iff.1 hginv t).1 ht
      simpa using h
    exact hkey t g ht ht'
  ·
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨hx1, t, ht, hxt⟩ := hx
    have hxt' : g⁻¹ * t * g = x := hxt
    exact hg (hkey t g ht (by rw [hxt']; exact hx1))

end

end CFSG.FeitThompson.Proofs
