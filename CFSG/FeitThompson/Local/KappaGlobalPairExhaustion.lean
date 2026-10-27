module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Foundations.PrimeConstituentsOfElement
import CFSG.FeitThompson.Local.KappaPairMixedDensity
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.SignalizerProductComponents
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.TwoCoreMixedSaturationMeasure

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Prep03

open Subgroup Pointwise

variable {G : Type*} [Group G] {π : Set ℕ} {X Y : Subgroup G} {c : G}

theorem conjSub_eq_map (Y : Subgroup G) (c : G) :
    conjSub Y c = Y.map (MulAut.conj c⁻¹ : G →* G) := rfl

theorem mem_conjSub {x : G} : x ∈ conjSub Y c ↔ c * x * c⁻¹ ∈ Y := by
  simp only [conjSub_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj, mul_assoc] using hy
  · intro h
    exact ⟨c * x * c⁻¹, h, by simp [MulAut.conj, mul_assoc]⟩

theorem mem_conjSet {S : Set G} {x : G} : x ∈ conjSet S c ↔ c * x * c⁻¹ ∈ S := by
  simp only [conjSet, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa [mul_assoc] using hy
  · intro h; exact ⟨c * x * c⁻¹, h, by group⟩

theorem coe_conjSub (Y : Subgroup G) (c : G) :
    ((conjSub Y c : Subgroup G) : Set G) = conjSet (Y : Set G) c := by
  ext x; simp only [SetLike.mem_coe, mem_conjSub, mem_conjSet]

theorem conjSet_sdiff (S T : Set G) (c : G) :
    conjSet (S \ T) c = conjSet S c \ conjSet T c := by
  ext x; simp only [Set.mem_sdiff, mem_conjSet]

theorem conjSet_union (S T : Set G) (c : G) :
    conjSet (S ∪ T) c = conjSet S c ∪ conjSet T c := by
  ext x; simp only [Set.mem_union, mem_conjSet]

theorem conjSet_singleton (x c : G) : conjSet ({x} : Set G) c = {c⁻¹ * x * c} := by
  simp [conjSet]

theorem conjSub_mono (h : Y ≤ X) (c : G) : conjSub Y c ≤ conjSub X c := Subgroup.map_mono h

theorem natCard_conjSub (Y : Subgroup G) (c : G) : Nat.card (conjSub Y c) = Nat.card Y :=
  Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective

theorem conjSub_sup (Y X : Subgroup G) (c : G) :
    conjSub (Y ⊔ X) c = conjSub Y c ⊔ conjSub X c := Subgroup.map_sup _ _ _

theorem conjSub_inf (Y X : Subgroup G) (c : G) :
    conjSub (Y ⊓ X) c = conjSub Y c ⊓ conjSub X c :=
  Subgroup.map_inf _ _ _ (MulAut.conj c⁻¹).injective

theorem conjSub_eq_bot_iff : conjSub Y c = ⊥ ↔ Y = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c⁻¹).injective

theorem conjSub_conjSub (Y : Subgroup G) (c d : G) :
    conjSub (conjSub Y c) d = conjSub Y (c * d) := by
  ext x; simp [mem_conjSub, mul_assoc]

@[simp] theorem conjSub_one (Y : Subgroup G) : conjSub Y 1 = Y := by ext x; simp [mem_conjSub]

theorem relIndex_conjSub (Y X : Subgroup G) (c : G) :
    (conjSub Y c).relIndex (conjSub X c) = Y.relIndex X := by
  rw [conjSub_eq_map, conjSub_eq_map, Subgroup.relIndex_map_map]
  have hk : ((MulAut.conj c⁻¹ : G →* G)).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (MulAut.conj c⁻¹).injective
  rw [hk, sup_bot_eq, sup_bot_eq]

theorem conjSub_centralizer (S : Set G) (c : G) :
    conjSub (centralizer S) c = centralizer (conjSet S c) := by
  rw [conjSub_eq_map, map_centralizer_eq_centralizer_image S (MulAut.conj c⁻¹)]
  congr 1
  ext x
  simp [conjSet, MulAut.conj]

theorem cent_conjSub (X : Subgroup G) (S : Set G) (c : G) :
    conjSub (cent X S) c = cent (conjSub X c) (conjSet S c) := by
  rw [cent, cent, conjSub_inf, conjSub_centralizer]

theorem isCyclic_conjSub_iff (Y : Subgroup G) (c : G) :
    IsCyclic (conjSub Y c) ↔ IsCyclic Y := isCyclic_map_conj_iff Y c⁻¹

theorem isHallPiOf_conjSub (h : IsHallPiOf π Y X) (c : G) :
    IsHallPiOf π (conjSub Y c) (conjSub X c) :=
  ⟨conjSub_mono h.1 c, by rw [natCard_conjSub]; exact h.2.1,
    by rw [relIndex_conjSub]; exact h.2.2⟩

theorem sigmaCore_conjSub [Finite G] (M : Subgroup G) (c : G) :
    sigmaCore (conjSub M c) = conjSub (sigmaCore M) c :=
  sigmaCore_conj_smul M c⁻¹

theorem sigmaPrimes_conjSub [Finite G] (M : Subgroup G) (c : G) :
    sigmaPrimes (conjSub M c) = sigmaPrimes M :=
  sigmaPrimes_conj_smul M c⁻¹

theorem isCoatom_conjSub (hM : IsCoatom X) (c : G) : IsCoatom (conjSub X c) :=
  isCoatom_conj_smul hM c⁻¹

theorem kappaPrimes_conjSub_subset [Finite G] (M : Subgroup G) (c : G) :
    kappaPrimes M ⊆ kappaPrimes (conjSub M c) := by
  intro p hpmem
  have hp := prime_of_mem_kappaPrimes hpmem
  rw [mem_kappaPrimes_iff_exists_subgroup hp] at hpmem
  obtain ⟨hdvd, hσ, P, hPM, hcard, hcyc, x, hxP, hx1, hne⟩ := hpmem
  rw [mem_kappaPrimes_iff_exists_subgroup hp, natCard_conjSub, sigmaPrimes_conjSub]
  refine ⟨hdvd, hσ, conjSub P c, conjSub_mono hPM c, by rw [natCard_conjSub]; exact hcard,
    (isCyclic_conjSub_iff P c).2 hcyc, c⁻¹ * x * c, ?_, ?_, ?_⟩
  · rw [mem_conjSub]; simpa [mul_assoc] using hxP
  · simp only [ne_eq]
    intro hcon
    exact hx1 (by simpa [mul_assoc] using congrArg (fun z => c * z * c⁻¹) hcon)
  · rw [sigmaCore_conjSub, ← conjSet_singleton, ← conjSub_centralizer, ← conjSub_inf]
    exact fun hc => hne (conjSub_eq_bot_iff.1 hc)

theorem kappaPrimes_conjSub [Finite G] (M : Subgroup G) (c : G) :
    kappaPrimes (conjSub M c) = kappaPrimes M := by
  refine le_antisymm ?_ (kappaPrimes_conjSub_subset M c)
  have h := kappaPrimes_conjSub_subset (conjSub M c) c⁻¹
  rwa [conjSub_conjSub, mul_inv_cancel, conjSub_one] at h

theorem IsKappaSetup.conjSub {G : Type*} [Group G] [Fintype G] {M K A Z : Subgroup G}
    (h : IsKappaSetup G M K A Z) (c : G) :
    IsKappaSetup G (Prep03.conjSub M c) (Prep03.conjSub K c) (Prep03.conjSub A c)
      (Prep03.conjSub Z c) where
  ambient := h.ambient
  isCoatom := isCoatom_conjSub h.isCoatom c
  kappa_nonempty := by rw [kappaPrimes_conjSub]; exact h.kappa_nonempty
  isHall_K := by rw [kappaPrimes_conjSub]; exact isHallPiOf_conjSub h.isHall_K c
  A_eq := by rw [h.A_eq, cent_conjSub, sigmaCore_conjSub, coe_conjSub]
  Z_eq := by rw [h.Z_eq, conjSub_sup]

theorem IsKappaSetup.torus_blocks {G : Type*} [Group G] [Fintype G] {M K A Z : Subgroup G}
    (h : IsKappaSetup G M K A Z) :
    (Z : Set G) = (K : Set G) * (A : Set G) ∧ (∀ x ∈ K, ∀ y ∈ A, Commute x y) ∧
      IsPiSubgroup (kappaPrimes M) K ∧ IsPiSubgroup (sigmaPrimes M) A ∧
      kappaPrimes M ∩ sigmaPrimes M = ∅ := by
  have hcomm : ∀ x ∈ K, ∀ y ∈ A, Commute x y := by
    intro x hx y hy
    rw [h.A_eq] at hy
    exact mem_centralizer_iff.1 hy.2 x hx
  refine ⟨by rw [h.Z_eq]; exact coe_sup_eq_mul_of_commute hcomm, hcomm,
    isPiSubgroup_iff.2 fun r hr => h.isHall_K.2.1 r hr,
    (isPiSubgroup_sigmaCore M).of_le (by rw [h.A_eq]; exact inf_le_left),
    Set.disjoint_iff_inter_eq_empty.1 (disjoint_kappaPrimes_sigmaPrimes M)⟩

theorem exists_isHallPiOf [Finite G] (π : Set ℕ) (H : Subgroup G) [Group.IsSolvable ↥H] :
    ∃ L : Subgroup G, IsHallPiOf π L H := by
  obtain ⟨H₀, hH₀⟩ := exists_isHallSubgroup (X := ↥H) π
  have hrel : (H₀.map H.subtype).relIndex H = H₀.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  refine ⟨H₀.map H.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro r hr
    rw [Subgroup.card_subtype] at hr
    exact isPiNumber_iff.1 hH₀.natCard r hr
  · intro r hr
    rw [hrel] at hr
    exact isPiNumber_iff.1 hH₀.index r hr

end CFSG.FeitThompson.Prep03

namespace CFSG.FeitThompson

open Subgroup Pointwise CFSG.FeitThompson.Prep03

variable {G : Type*} [Group G]

theorem exists_subgroup_natCard_prime_le_zpowers [Finite G] {x : G} (hx : x ≠ 1) :
    ∃ (W : Subgroup G) (q : ℕ), q.Prime ∧ Nat.card ↥W = q ∧ W ≤ zpowers x := by
  have hord : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.1 h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hord
  have hcard : q ∣ Nat.card ↥(zpowers x) := by rw [Nat.card_zpowers]; exact hqd
  obtain ⟨y, hy, hyord⟩ := exists_mem_orderOf_eq_of_dvd hq hcard
  exact ⟨zpowers y, q, hq, by rw [Nat.card_zpowers, hyord], zpowers_le.2 hy⟩

omit [Group G] in
theorem exists_mem_and_mem_of_half_lt_ncard [Finite G] {S₁ S₂ : Set G}
    (h₁ : (Nat.card G : ℚ) / 2 < (S₁.ncard : ℚ)) (h₂ : (Nat.card G : ℚ) / 2 < (S₂.ncard : ℚ)) :
    ∃ x, x ∈ S₁ ∧ x ∈ S₂ := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have hunion : (S₁ ∪ S₂).ncard = S₁.ncard + S₂.ncard :=
    Set.ncard_union_eq (Set.disjoint_left.2 hc) (Set.toFinite _) (Set.toFinite _)
  have hle : (S₁ ∪ S₂).ncard ≤ Nat.card G := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  have hcast : (S₁.ncard : ℚ) + (S₂.ncard : ℚ) ≤ (Nat.card G : ℚ) := by
    rw [hunion] at hle
    exact_mod_cast hle
  linarith

theorem exists_mem_and_mem_of_coe_eq_mul [Finite G] {π₁ π₂ : Set ℕ} {L B W : Subgroup G}
    (hW : (W : Set G) = (L : Set G) * (B : Set G)) (hcomm : ∀ x ∈ L, ∀ y ∈ B, Commute x y)
    (hL : IsPiSubgroup π₁ L) (hB : IsPiSubgroup π₂ B) (hd : π₁ ∩ π₂ = ∅)
    {s : G} (hs : s ∈ W) :
    ∃ l ∈ L, ∃ b ∈ B, l ∈ zpowers s ∧ b ∈ zpowers s ∧ s = l * b := by
  obtain ⟨l, hl, b, hb, hlb⟩ : s ∈ (L : Set G) * (B : Set G) := by rw [← hW]; exact hs
  have hlb' : l * b = s := hlb
  have hlpi : IsPiElement π₁ l := isPiElement_of_mem_of_isPiSubgroup hL hl
  have hbpi : IsPiElement π₂ b := isPiElement_of_mem_of_isPiSubgroup hB hb
  have hcop : (orderOf l).Coprime (orderOf b) :=
    hlpi.coprime_orderOf (orderOf_pos l).ne' (orderOf_pos b).ne' hbpi hd
  have hC : Commute l b := hcomm l hl b hb
  have h1 : piConstituent π₁ s = l := by
    rw [← hlb', piConstituent_mul_of_commute_of_coprime hC (orderOf_pos l).ne' (orderOf_pos b).ne'
      hcop, hlpi.piConstituent_eq_self (orderOf_pos l).ne',
      piConstituent_eq_one_of_inter_eq_empty (orderOf_pos b).ne' hbpi hd, mul_one]
  have h2 : piConstituent π₂ s = b := by
    rw [← hlb', piConstituent_mul_of_commute_of_coprime hC (orderOf_pos l).ne' (orderOf_pos b).ne'
      hcop, hbpi.piConstituent_eq_self (orderOf_pos b).ne',
      piConstituent_eq_one_of_inter_eq_empty (orderOf_pos l).ne' hlpi
        (by rw [Set.inter_comm]; exact hd), one_mul]
  exact ⟨l, hl, b, hb, h1 ▸ piConstituent_mem_zpowers _ _, h2 ▸ piConstituent_mem_zpowers _ _,
    hlb'.symm⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_global_pair_exhaustion
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_global_pair_exhaustion.{u} := by
  have hfix := FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₃ h₄
  have hdens := FNI_kappa_pair_mixed_density h₂
  intro G _ _ M K A Z Mstar hMset hMstar hMstarEx hMstarUniq H hH hκH
  obtain ⟨Ms, ⟨hMsCo, hMsEx⟩, -, -, -, -, -, -, -, -, -, hKcl, -, -, -⟩ := h₂ G M K A Z hMset
  rw [hMstarUniq Ms hMsCo hMsEx] at hKcl
  have hHsolv : Group.IsSolvable ↥H := hMset.ambient.forall_isSolvable H hH.1
  obtain ⟨L, hL⟩ := exists_isHallPiOf (kappaPrimes H) H
  set B : Subgroup G := cent (sigmaCore H) (L : Set G) with hBdef
  set W : Subgroup G := L ⊔ B with hWdef
  have hHset : IsKappaSetup G H L B W := ⟨hMset.ambient, hH, hκH, hL, hBdef, hWdef⟩
  obtain ⟨x, hxT, hxQ⟩ :=
    exists_mem_and_mem_of_half_lt_ncard (G := G)
      (hdens G M K A Z hMset).2 (hdens G H L B W hHset).2
  obtain ⟨g, hg⟩ := Set.mem_iUnion.1 hxT
  obtain ⟨h, hh⟩ := Set.mem_iUnion.1 hxQ
  set t : G := g * x * g⁻¹ with htdef
  have htT : t ∈ (Z : Set G) \ ((K : Set G) ∪ (A : Set G)) := Prep03.mem_conjSet.1 hg
  set d : G := h * g⁻¹ with hddef
  refine ⟨d, ?_⟩
  set H' : Subgroup G := conjSub H d with hH'def
  set L' : Subgroup G := conjSub L d with hL'def
  set B' : Subgroup G := conjSub B d with hB'def
  set W' : Subgroup G := conjSub W d with hW'def
  have hH'set : IsKappaSetup G H' L' B' W' := hHset.conjSub d
  have htQ' : t ∈ (W' : Set G) \ ((L' : Set G) ∪ (B' : Set G)) := by
    rw [hW'def, hL'def, hB'def, coe_conjSub, coe_conjSub, coe_conjSub, ← conjSet_union,
      ← conjSet_sdiff, Prep03.mem_conjSet]
    have hdt : d * t * d⁻¹ = h * x * h⁻¹ := by simp only [hddef, htdef]; group
    rw [hdt]
    exact Prep03.mem_conjSet.1 hh
  obtain ⟨hW'mul, hW'comm, hL'pi, hB'pi, hW'd⟩ := hH'set.torus_blocks
  obtain ⟨l, hlL', b, hbB', -, hbt, hfac⟩ :=
    exists_mem_and_mem_of_coe_eq_mul hW'mul hW'comm hL'pi hB'pi hW'd htQ'.1
  have hb1 : b ≠ 1 := fun hb => htQ'.2 (Or.inl (by rw [hfac, hb, mul_one]; exact hlL'))
  have hbZ : b ∈ Z := zpowers_le.2 htT.1 hbt
  obtain ⟨hZmul, hZcomm, hKpi, hApi, hZd⟩ := hMset.torus_blocks
  obtain ⟨k₀, hk₀K, a₀, ha₀A, hk₀b, ha₀b, hbfac⟩ :=
    exists_mem_and_mem_of_coe_eq_mul hZmul hZcomm hKpi hApi hZd hbZ
  by_cases ha₀ : a₀ = 1
  ·
    right
    have hbk : b = k₀ := by rw [hbfac, ha₀, mul_one]
    obtain ⟨Xp, q, hq, hXcard, hXle⟩ := exists_subgroup_natCard_prime_le_zpowers hb1
    obtain ⟨-, hCstar, -⟩ :=
      hKcl Xp (hXle.trans (zpowers_le.2 (hbk ▸ hk₀K))) (by rw [hXcard]; exact hq)
    obtain ⟨-, hcentH, -⟩ := hfix G H' L' B' W' hH'set
    exact ((hcentH q Xp hq (hXle.trans (zpowers_le.2 hbB')) hXcard).2 Mstar hMstar hCstar).symm
  ·
    left
    have ha₀B' : a₀ ∈ B' := zpowers_le.2 hbB' ha₀b
    obtain ⟨Yp, q, hq, hYcard, hYle⟩ := exists_subgroup_natCard_prime_le_zpowers ha₀
    obtain ⟨-, hcentM, -⟩ := hfix G M K A Z hMset
    obtain ⟨hCM, -⟩ := hcentM q Yp hq (hYle.trans (zpowers_le.2 ha₀A)) hYcard
    obtain ⟨-, hcentH, -⟩ := hfix G H' L' B' W' hH'set
    exact ((hcentH q Yp hq (hYle.trans (zpowers_le.2 ha₀B')) hYcard).2
      M hMset.isCoatom hCM).symm

end CFSG.FeitThompson.Proofs
