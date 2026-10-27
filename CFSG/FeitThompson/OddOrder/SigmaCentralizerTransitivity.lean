module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.SigmaSylowTransporterFusion
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.OddOrder.NormalizerFactorizationRankTwoSylow
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.Foundations.NormalCommuteModIntersection
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.PrimeFixedSectionExtension
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
import CFSG.FeitThompson.Definitions.KappaPrimes
import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

omit [Finite G] in
theorem conj_smul_conj_smul (a b : G) (M : Subgroup G) :
    MulAut.conj a • (MulAut.conj b • M) = MulAut.conj (a * b) • M := by
  rw [smul_smul, map_mul]

omit [Finite G] in
theorem isCoatom_conj_smul (hM : IsCoatom M) (g : G) : IsCoatom (MulAut.conj g • M) := by
  rw [conj_smul_eq_map_conj]; exact isCoatom_map_conj hM g

def localOvergroups (M X : Subgroup G) : Set (Subgroup G) :=
  {N | (∃ g : G, N = MulAut.conj g • M) ∧ X ≤ N}

theorem mem_localOvergroups_iff {N X : Subgroup G} :
    N ∈ localOvergroups M X ↔ (∃ g : G, N = MulAut.conj g • M) ∧ X ≤ N := Iff.rfl

theorem conj_smul_mem_localOvergroups_of_le {X : Subgroup G} {g : G} (h : X ≤ MulAut.conj g • M) :
    MulAut.conj g • M ∈ localOvergroups M X := ⟨⟨g, rfl⟩, h⟩

theorem le_of_mem_localOvergroups {N X : Subgroup G} (h : N ∈ localOvergroups M X) : X ≤ N := h.2

theorem isCoatom_of_mem_localOvergroups {N X : Subgroup G} (hM : IsCoatom M)
    (h : N ∈ localOvergroups M X) : IsCoatom N := by
  obtain ⟨g, rfl⟩ := h.1
  exact isCoatom_conj_smul hM g

theorem conj_smul_mem_localOvergroups {N X : Subgroup G} (hN : N ∈ localOvergroups M X) {c : G}
    (hc : c ∈ centralizer (X : Set G)) : MulAut.conj c • N ∈ localOvergroups M X := by
  obtain ⟨⟨g, rfl⟩, hXN⟩ := hN
  refine ⟨⟨c * g, (conj_smul_conj_smul c g M).symm ▸ rfl⟩, fun x hx => ?_⟩
  have hcx : MulAut.conj c x = x := by
    have hxc := (Subgroup.mem_centralizer_iff.1 hc) x hx
    simp only [MulAut.conj_apply]
    rw [← hxc]
    group
  rw [conj_smul_eq_map_conj]
  exact hcx ▸ Subgroup.mem_map_of_mem _ (hXN hx)

omit [Finite G] in
theorem mem_normalizer_map_subtype {L : Subgroup G} {Q : Subgroup ↥L} {n : ↥L}
    (hn : n ∈ normalizer ((Q : Subgroup ↥L) : Set ↥L)) :
    (n : G) ∈ normalizer ((Q.map L.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
  have h := congrArg (Subgroup.map L.subtype) hn
  rwa [map_subtype_map_conj] at h

omit [Finite G] in
theorem notMem_elementaryAbelianRanks_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {d : ℕ}
    (e : X ≃* Y) (h : d ∉ elementaryAbelianRanks p Y) : d ∉ elementaryAbelianRanks p X := by
  intro hx
  rw [mem_elementaryAbelianRanks] at hx
  obtain ⟨H, ⟨f⟩⟩ := hx
  exact h (mem_elementaryAbelianRanks.2
    ⟨H.map e.toMonoidHom, ⟨(H.equivMapOfInjective e.toMonoidHom e.injective).symm.trans f⟩⟩)

theorem exists_conj_smul_le_of_isPGroup (hpM : p ∈ sigmaPrimes M) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : ∃ a : G, Q ≤ MulAut.conj a • M := by
  have := Fact.mk (prime_of_mem_sigmaPrimes hpM)
  obtain ⟨T, hT⟩ := hQ.exists_le_sylow
  obtain ⟨T', hT'⟩ := exists_sylow_coe_eq_map_subtype hpM (default : Sylow p M)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G T' T
  refine ⟨a, hT.trans ?_⟩
  have hTT : (T : Subgroup G) = MulAut.conj a • (T' : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, ha]
  rw [hTT, hT']
  exact pointwise_smul_le_pointwise_smul_iff.mpr (Subgroup.map_subtype_le _)

theorem eq_of_natCard_eq_pow_factorization (hpM : p ∈ sigmaPrimes M) {X : Subgroup G}
    (hXcard : Nat.card X = p ^ (Nat.card G).factorization p) {a b : G}
    (h₁ : X ≤ MulAut.conj a • M) (h₂ : X ≤ MulAut.conj b • M) :
    MulAut.conj a • M = MulAut.conj b • M := by
  set M₁ : Subgroup G := MulAut.conj a • M with hM₁
  have hp₁ : p ∈ sigmaPrimes M₁ := by rw [hM₁, sigmaPrimes_conj_smul]; exact hpM
  have hcard : Nat.card X = p ^ (Nat.card M₁).factorization p := by
    rw [factorization_eq_of_mem_sigmaPrimes hp₁]; exact hXcard
  have hM₂ : MulAut.conj b • M = MulAut.conj (b * a⁻¹) • M₁ := by
    rw [hM₁, conj_smul_conj_smul]; simp
  have hle : X.map (MulAut.conj (b * a⁻¹)⁻¹ : G →* G) ≤ M₁ := by
    have hh : MulAut.conj (b * a⁻¹)⁻¹ • X
        ≤ MulAut.conj (b * a⁻¹)⁻¹ • (MulAut.conj (b * a⁻¹) • M₁) :=
      pointwise_smul_le_pointwise_smul_iff.mpr (hM₂ ▸ h₂)
    rw [conj_smul_conj_smul, inv_mul_cancel, map_one, one_smul, conj_smul_eq_map_conj] at hh
    exact hh
  have hgM : b * a⁻¹ ∈ M₁ := mem_of_map_conj_inv_le hp₁ h₁ hcard hle
  rw [hM₂, mem_normalizer_iff_conj_smul_eq.mp (Subgroup.le_normalizer hgM)]

theorem exists_lt_inf_normalizer_of_mem_sigmaPrimes (hpM : p ∈ sigmaPrimes M) {X : Subgroup G}
    (hXp : IsPGroup p X) (hfull : Nat.card X ≠ p ^ (Nat.card G).factorization p) {c : G}
    (hXM : X ≤ MulAut.conj c • M) :
    ∃ Y : Subgroup G, X < Y ∧ Y ≤ MulAut.conj c • M ∧ Y ≤ normalizer (X : Set G) ∧
      IsPGroup p Y := by
  have hp := prime_of_mem_sigmaPrimes hpM
  have hpc : p ∈ sigmaPrimes (MulAut.conj c • M) := by rw [sigmaPrimes_conj_smul]; exact hpM
  obtain ⟨T, hXT, hTM, hTcard⟩ := exists_le_natCard_eq_pow_factorization hp hXM hXp
  rw [factorization_eq_of_mem_sigmaPrimes hpc] at hTcard
  have hTp : IsPGroup p T := IsPGroup.of_card hTcard
  have hXTlt : X < T := hXT.lt_of_ne fun h => hfull (h ▸ hTcard)
  exact ⟨T ⊓ normalizer (X : Set G), lt_inf_normalizer_of_isPGroup hp hTp hXTlt,
    inf_le_left.trans hTM, inf_le_right, hTp.to_le inf_le_left⟩

theorem map_subtype_pComplCore_le_centralizer {X : Subgroup G} (hp : p.Prime)
    (hXp : IsPGroup p X) :
    ((pComplCore p ↥(normalizer (X : Set G))).map (normalizer (X : Set G)).subtype)
      ≤ centralizer (X : Set G) := by
  have := Fact.mk hp
  set L : Subgroup G := normalizer (X : Set G) with hL
  have hXL : X ≤ L := Subgroup.le_normalizer
  have hX' : (X.subgroupOf L).Normal := Subgroup.normal_in_normalizer
  have hY' : (pComplCore p ↥L).Normal := pComplCore_normal p ↥L
  have hXp' : IsPGroup p ↥(X.subgroupOf L) := hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXL).symm
  obtain ⟨k, hk⟩ := hXp'.exists_card_eq
  have hcop : (Nat.card ↥(X.subgroupOf L)).Coprime (Nat.card (pComplCore p ↥L)) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_natCard_pComplCore hp ↥L))
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
  have hxL : (⟨x, hXL hx⟩ : ↥L) ∈ X.subgroupOf L := hx
  exact congrArg (Subtype.val)
    (mul_comm_of_normal_of_coprime_natCard (X.subgroupOf L) (pComplCore p ↥L) hcop hxL hy)

theorem exists_mem_centralizer_conj_smul_step [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {X : Subgroup G} (hXbot : X ≠ ⊥)
    (hXp : IsPGroup p X) (hfull : Nat.card X ≠ p ^ (Nat.card G).factorization p)
    (ih : ∀ Y : Subgroup G, X < Y → IsPGroup p Y → ∀ u v : G,
      Y ≤ MulAut.conj u • M → Y ≤ MulAut.conj v • M →
        ∃ c ∈ centralizer (Y : Set G),
          MulAut.conj c • (MulAut.conj u • M) = MulAut.conj v • M)
    {a b : G} (ha : X ≤ MulAut.conj a • M) (hb : X ≤ MulAut.conj b • M) :
    ∃ c ∈ centralizer (X : Set G),
      MulAut.conj c • (MulAut.conj a • M) = MulAut.conj b • M := by
  have hp : p.Prime := prime_of_mem_sigmaPrimes hpM
  have := Fact.mk hp
  set L : Subgroup G := normalizer (X : Set G) with hLdef
  have hLtop : L ≠ ⊤ := (normalizer_lt_top_of_isPGroup hna hp hXbot hXp).ne
  have hLsolv : Group.IsSolvable ↥L := hsolv L hLtop
  obtain ⟨hLcard, hLodd⟩ := odd_natCard_lt_natCard_of_ne_top hodd hLtop
  obtain ⟨X₁, hXX₁, hX₁M, hX₁L, hX₁p⟩ :=
    exists_lt_inf_normalizer_of_mem_sigmaPrimes hpM hXp hfull ha
  obtain ⟨X₂, hXX₂, hX₂M, hX₂L, hX₂p⟩ :=
    exists_lt_inf_normalizer_of_mem_sigmaPrimes hpM hXp hfull hb
  obtain ⟨P, hX₁P⟩ := (hX₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hX₁L).symm).exists_le_sylow
  set P' : Subgroup G := (P : Subgroup ↥L).map L.subtype with hP'def
  have hX₁P' : X₁ ≤ P' := by
    rw [hP'def, ← Subgroup.map_subgroupOf_eq_of_le hX₁L]
    exact Subgroup.map_mono hX₁P
  have hP'L : P' ≤ L := Subgroup.map_subtype_le _
  have hP'p : IsPGroup p ↥P' := P.isPGroup'.map _
  have hXP' : X < P' := hXX₁.trans_le hX₁P'
  obtain ⟨Q, hX₂Q⟩ := (hX₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hX₂L).symm).exists_le_sylow
  obtain ⟨t₀, ht₀⟩ := MulAction.exists_smul_eq (↥L) P Q
  have hX₂t : X₂ ≤ MulAut.conj (t₀ : G) • P' := by
    have h1 : (Q : Subgroup ↥L) = MulAut.conj t₀ • (P : Subgroup ↥L) := by
      rw [← Sylow.coe_subgroup_smul, ht₀]
    have h2 := Subgroup.map_mono (f := L.subtype) (h1 ▸ hX₂Q)
    rwa [Subgroup.map_subgroupOf_eq_of_le hX₂L, map_subtype_conj_smul] at h2
  obtain ⟨d, hP'M₀⟩ := exists_conj_smul_le_of_isPGroup hpM hP'p
  set M₀ : Subgroup G := MulAut.conj d • M with hM₀def
  have hcP : centralizer (P' : Set G) ≤ centralizer (X : Set G) :=
    Subgroup.centralizer_le hXP'.le
  have hkey : ∃ k ∈ centralizer (X : Set G),
      MulAut.conj (t₀ : G) • M₀ = MulAut.conj k • M₀ := by
    have hP'top : P' ≠ ⊤ := fun h => hLtop (top_le_iff.1 (h ▸ hP'L))
    by_cases hrank : 3 ≤ maxElementaryAbelianPRank ↥P'
    ·
      obtain ⟨M', hM'⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank
        hna hodd hsolv hP'top hrank
      have hLM' : L ≤ M' := hM'.le_of_ne_top hP'L hLtop
      have hM₀M' : M₀ = M' := hM'.eq_of_isCoatom (isCoatom_conj_smul hM d) hP'M₀
      have ht₀M₀ : (t₀ : G) ∈ M₀ := hM₀M' ▸ hLM' t₀.2
      exact ⟨1, one_mem _, by
        rw [map_one, one_smul, mem_normalizer_iff_conj_smul_eq.mp (Subgroup.le_normalizer ht₀M₀)]⟩
    ·
      have h3 : (3 : ℕ) ∉ elementaryAbelianRanks p ↥(P : Subgroup ↥L) := by
        refine notMem_elementaryAbelianRanks_of_mulEquiv
          ((P : Subgroup ↥L).equivMapOfInjective L.subtype L.subtype_injective) fun hmem => ?_
        exact hrank (le_maxElementaryAbelianPRank
          (mem_elementaryAbelianPrimeRanks.2 ⟨p, hp, hmem⟩))
      obtain ⟨y, hy, n, hn, hyn⟩ := exists_mem_pComplCore_mul_mem_normalizer hp hLodd P h3 t₀
      have hyC : (y : G) ∈ centralizer (X : Set G) :=
        map_subtype_pComplCore_le_centralizer hp hXp (Subgroup.mem_map_of_mem _ hy)
      have hnP' : (n : G) ∈ normalizer (P' : Set G) := mem_normalizer_map_subtype hn
      have hP'n : P' ≤ MulAut.conj ((n : G) * d) • M := by
        rw [← conj_smul_conj_smul, ← hM₀def, ← mem_normalizer_iff_conj_smul_eq.mp hnP']
        exact pointwise_smul_le_pointwise_smul_iff.mpr hP'M₀
      obtain ⟨c, hcC, hc⟩ := ih P' hXP' hP'p d ((n : G) * d) hP'M₀ hP'n
      have hgoal : MulAut.conj (n : G) • M₀ = MulAut.conj c • M₀ := by
        rw [hM₀def, conj_smul_conj_smul]; exact hc.symm
      refine ⟨(y : G) * c, mul_mem hyC (hcP hcC), ?_⟩
      have hcoe : ((y * n : ↥L) : G) = (y : G) * (n : G) := rfl
      rw [hyn, hcoe, ← conj_smul_conj_smul, hgoal, conj_smul_conj_smul]
  obtain ⟨k, hkC, hk⟩ := hkey
  obtain ⟨e₁, he₁C, he₁⟩ := ih X₁ hXX₁ hX₁p a d hX₁M (hX₁P'.trans hP'M₀)
  have hX₂t' : X₂ ≤ MulAut.conj ((t₀ : G) * d) • M := by
    rw [← conj_smul_conj_smul, ← hM₀def]
    exact hX₂t.trans (pointwise_smul_le_pointwise_smul_iff.mpr hP'M₀)
  obtain ⟨e₂, he₂C, he₂⟩ := ih X₂ hXX₂ hX₂p b ((t₀ : G) * d) hX₂M hX₂t'
  have hce₁ : centralizer (X₁ : Set G) ≤ centralizer (X : Set G) :=
    Subgroup.centralizer_le hXX₁.le
  have hce₂ : centralizer (X₂ : Set G) ≤ centralizer (X : Set G) :=
    Subgroup.centralizer_le hXX₂.le
  refine ⟨e₂⁻¹ * (k * e₁), mul_mem (inv_mem (hce₂ he₂C)) (mul_mem hkC (hce₁ he₁C)), ?_⟩
  have hstep : MulAut.conj (k * e₁) • (MulAut.conj a • M) = MulAut.conj ((t₀ : G) * d) • M := by
    rw [← conj_smul_conj_smul, he₁, ← hM₀def, ← hk, conj_smul_conj_smul]
  rw [← conj_smul_conj_smul, hstep, ← he₂, conj_smul_conj_smul, inv_mul_cancel, map_one, one_smul]

private theorem exists_mem_centralizer_conj_smul_ind [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) (n : ℕ) :
    ∀ X : Subgroup G, Nat.card G - Nat.card X ≤ n → IsPGroup p X →
      ∀ a b : G, X ≤ MulAut.conj a • M → X ≤ MulAut.conj b • M →
        ∃ c ∈ centralizer (X : Set G),
          MulAut.conj c • (MulAut.conj a • M) = MulAut.conj b • M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hXn hXp a b ha hb
  have hp : p.Prime := prime_of_mem_sigmaPrimes hpM
  by_cases hXbot : X = ⊥
  · subst hXbot
    refine ⟨b * a⁻¹, by simp [Subgroup.mem_centralizer_iff], ?_⟩
    rw [conj_smul_conj_smul]
    simp [mul_assoc]
  by_cases hfull : Nat.card X = p ^ (Nat.card G).factorization p
  · exact ⟨1, one_mem _, by
      rw [map_one, one_smul]; exact eq_of_natCard_eq_pow_factorization hpM hfull ha hb⟩
  refine exists_mem_centralizer_conj_smul_step hna hodd hsolv hM hpM hXbot hXp hfull
    (fun Y hXY hYp u v hu hv => ?_) ha hb
  have hlt : Nat.card G - Nat.card Y < Nat.card G - Nat.card X := by
    have h1 : Nat.card X < Nat.card Y := natCard_lt_natCard_of_lt hXY
    have h2 : Nat.card Y ≤ Nat.card G := Subgroup.card_le_card_group Y
    omega
  exact ih _ (lt_of_lt_of_le hlt hXn) Y le_rfl hYp u v hu hv

theorem exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {X : Subgroup G} (hXp : IsPGroup p X)
    {a b : G} (ha : X ≤ MulAut.conj a • M) (hb : X ≤ MulAut.conj b • M) :
    ∃ c ∈ centralizer (X : Set G),
      MulAut.conj c • (MulAut.conj a • M) = MulAut.conj b • M :=
  exists_mem_centralizer_conj_smul_ind hna hodd hsolv hM hpM (Nat.card G - Nat.card X) X le_rfl
    hXp a b ha hb

theorem exists_mem_centralizer_conj_smul_localOvergroups [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {X : Subgroup G} (_hXbot : X ≠ ⊥)
    (hXp : IsPGroup p X) {N₁ N₂ : Subgroup G} (hN₁ : N₁ ∈ localOvergroups M X)
    (hN₂ : N₂ ∈ localOvergroups M X) :
    ∃ c ∈ centralizer (X : Set G), MulAut.conj c • N₁ = N₂ := by
  obtain ⟨⟨a, rfl⟩, ha⟩ := hN₁
  obtain ⟨⟨b, rfl⟩, hb⟩ := hN₂
  exact exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes hna hodd hsolv hM hpM hXp ha hb

theorem localOvergroups_nonempty (hpM : p ∈ sigmaPrimes M) {X : Subgroup G}
    (hXp : IsPGroup p X) : (localOvergroups M X).Nonempty := by
  obtain ⟨a, ha⟩ := exists_conj_smul_le_of_isPGroup hpM hXp
  exact ⟨MulAut.conj a • M, conj_smul_mem_localOvergroups_of_le ha⟩

end

end CFSG.FeitThompson
