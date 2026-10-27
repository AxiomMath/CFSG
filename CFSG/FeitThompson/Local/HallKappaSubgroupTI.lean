module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {π : Set ℕ} {p : ℕ} {M K Q X Y : Subgroup G}

theorem isHallPiOf_of_isHallPiSubgroupOf (h : CFSG.FeitThompson.IsHallPiSubgroupOf π K M) :
    CFSG.FeitThompson.Prep03.IsHallPiOf π K M := by
  refine ⟨h.1, fun r hr => ?_, fun r hr => h.2.notMem_of_mem_primeFactors_index r hr⟩
  refine isPiSubgroup_iff.1 h.2.isPiSubgroup r ?_
  rwa [← Subgroup.card_subtype M (K.subgroupOf M), Subgroup.map_subgroupOf_eq_of_le h.1]

theorem disjoint_sdiff_image_of_inf_conjBy_eq_bot {g : G}
    (h : K ⊓ CFSG.FeitThompson.conjBy K g = ⊥) :
    Disjoint ((K : Set G) \ {1}) ((fun x : G => g⁻¹ * x * g) '' ((K : Set G) \ {1})) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have hxc : x ∈ (CFSG.FeitThompson.conjBy K g : Set G) := by
    rw [CFSG.FeitThompson.coe_conjBy]
    exact Set.image_mono Set.sdiff_subset hx'
  have hmem : x ∈ K ⊓ CFSG.FeitThompson.conjBy K g := ⟨hx.1, hxc⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hx.2 hmem

variable [Finite G]

theorem isCyclic_of_isPGroup_of_mem_kappaPrimes (hp : p.Prime) (hpk : p ∈ kappaPrimes M)
    (hQM : Q ≤ M) (hQ : IsPGroup p ↥Q) : IsCyclic ↥Q := by
  have : Fact p.Prime := ⟨hp⟩
  have hQ' : IsPGroup p ↥(Q.subgroupOf M) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  have hle : Q ≤ (S : Subgroup ↥M).map M.subtype := by
    have h := Subgroup.map_mono (f := M.subtype) hS
    rwa [Subgroup.map_subgroupOf_eq_of_le hQM] at h
  have hcyc := ((mem_kappaPrimes_iff_forall hp).1 hpk).2.2 S
  have : IsCyclic ↥((S : Subgroup ↥M).map M.subtype) := hcyc.1
  exact Subgroup.isCyclic_of_le hle

theorem eq_of_natCard_eq_prime_of_le_normalizer (hp : p.Prime) (hpk : p ∈ kappaPrimes M)
    (hKM : K ≤ M) (hXK : X ≤ K) (hYK : Y ≤ K)
    (hX : Nat.card ↥X = p) (hY : Nat.card ↥Y = p)
    (hXn : K ≤ normalizer (X : Set G)) (hYn : K ≤ normalizer (Y : Set G)) : X = Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hXnormal : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).2 hXn
  have hYnormal : (Y.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).2 hYn
  have hcX : Nat.card ↥(X.subgroupOf K) = p ^ 1 := by
    rw [← Subgroup.card_subtype K (X.subgroupOf K), Subgroup.map_subgroupOf_eq_of_le hXK, hX,
      pow_one]
  have hcY : Nat.card ↥(Y.subgroupOf K) = p ^ 1 := by
    rw [← Subgroup.card_subtype K (Y.subgroupOf K), Subgroup.map_subgroupOf_eq_of_le hYK, hY,
      pow_one]
  obtain ⟨S⟩ : Nonempty (Sylow p ↥K) := inferInstance
  have hXS : X.subgroupOf K ≤ (S : Subgroup ↥K) := (IsPGroup.of_card hcX).le_sylow_of_normal S
  have hYS : Y.subgroupOf K ≤ (S : Subgroup ↥K) := (IsPGroup.of_card hcY).le_sylow_of_normal S
  set Q : Subgroup G := (S : Subgroup ↥K).map K.subtype with hQdef
  have hXQ : X ≤ Q := by
    have h := Subgroup.map_mono (f := K.subtype) hXS
    rwa [Subgroup.map_subgroupOf_eq_of_le hXK] at h
  have hYQ : Y ≤ Q := by
    have h := Subgroup.map_mono (f := K.subtype) hYS
    rwa [Subgroup.map_subgroupOf_eq_of_le hYK] at h
  have hQp : IsPGroup p ↥Q := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥(S : Subgroup ↥K))).1 S.2
    exact IsPGroup.of_card (n := n) (by rw [hQdef, Subgroup.card_subtype, hn])
  have : IsCyclic ↥Q :=
    isCyclic_of_isPGroup_of_mem_kappaPrimes hp hpk ((Subgroup.map_subtype_le _).trans hKM) hQp
  exact eq_of_le_of_natCard_eq_of_isCyclic hXQ hYQ (by rw [hX, hY])

theorem inf_conjBy_eq_bot_of_notMem_normalizer
    (hKM : K ≤ M) (hpi : ∀ r ∈ (Nat.card ↥K).primeFactors, r ∈ kappaPrimes M)
    (hnormal : ∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime → K ≤ normalizer (X : Set G))
    (hNM : ∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
      normalizer (X : Set G) ⊓ M = normalizer (K : Set G) ⊓ M)
    {g : G} (hgM : g ∈ M) (hg : g ∉ normalizer (K : Set G)) :
    K ⊓ CFSG.FeitThompson.conjBy K g = ⊥ := by
  by_contra hne
  set D : Subgroup G := K ⊓ CFSG.FeitThompson.conjBy K g with hDdef
  have hD1 : Nat.card ↥D ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have hDlt : 1 < Nat.card ↥D := lt_of_le_of_ne Nat.card_pos (Ne.symm hD1)
  obtain ⟨p, hpmem⟩ := Nat.nonempty_primeFactors.2 hDlt
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  obtain ⟨x, hxD, hxo⟩ := exists_mem_orderOf_eq_of_dvd hp (Nat.dvd_of_mem_primeFactors hpmem)
  set P : Subgroup G := zpowers x with hPdef
  have hPcard : Nat.card ↥P = p := by rw [hPdef, Nat.card_zpowers, hxo]
  have hPprime : (Nat.card ↥P).Prime := by rw [hPcard]; exact hp
  have hPK : P ≤ K := zpowers_le.2 hxD.1
  have hPc : P ≤ CFSG.FeitThompson.conjBy K g := zpowers_le.2 hxD.2
  set P' : Subgroup G := CFSG.FeitThompson.conjBy P g⁻¹ with hP'def
  have hP'card : Nat.card ↥P' = p := by rw [hP'def, CFSG.FeitThompson.natCard_conjBy, hPcard]
  have hP'K : P' ≤ K := by
    intro y hy
    rw [hP'def, CFSG.FeitThompson.mem_conjBy] at hy
    have hy' : g⁻¹ * y * g ∈ P := by simpa [mul_assoc] using hy
    simpa [mul_assoc] using CFSG.FeitThompson.mem_conjBy.1 (hPc hy')
  have hpk : p ∈ kappaPrimes M :=
    hpi p (Nat.mem_primeFactors.2 ⟨hp, hPcard ▸ Subgroup.card_dvd_of_le hPK, Nat.card_pos.ne'⟩)
  have hPP' : P = P' :=
    eq_of_natCard_eq_prime_of_le_normalizer hp hpk hKM hPK hP'K hPcard hP'card
      (hnormal P hPK hPprime) (hnormal P' hP'K (by rw [hP'card]; exact hp))
  have hginv : g⁻¹ ∈ normalizer (P : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    refine fun n => ⟨fun hn => ?_, fun hn => ?_⟩
    · have hn' : n ∈ P' := hPP' ▸ hn
      rw [hP'def, CFSG.FeitThompson.mem_conjBy] at hn'
      simpa [mul_assoc] using hn'
    · have hn' : n ∈ P' := by
        rw [hP'def, CFSG.FeitThompson.mem_conjBy]
        simpa [mul_assoc] using hn
      exact hPP' ▸ hn'
  have hgP : g ∈ normalizer (P : Set G) := by
    simpa using (normalizer (P : Set G)).inv_mem hginv
  have hfin : g ∈ normalizer (K : Set G) ⊓ M := by
    rw [← hNM P hPK hPprime]; exact ⟨hgP, hgM⟩
  exact hg hfin.1

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

theorem FTS_kappa_hall_local_ti
    (h₁ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u}) :
    Statements.FTS_kappa_hall_local_ti.{u} := by
  intro G _ _ hG M hM hκ K hK
  have : Fintype G := Fintype.ofFinite G
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hMc : IsCoatom M := hM
  have hKH : Prep03.IsHallPiOf (kappaPrimes M) K M := isHallPiOf_of_isHallPiSubgroupOf hK
  have hsetup : Prep03.IsKappaSetup G M K (Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore M) (K : Set G)) := ⟨hamb, hMc, hκ, hKH, rfl, rfl⟩
  obtain ⟨-, -, h₁c⟩ := h₁ G M K _ _ hsetup
  obtain ⟨-, U, E₁, h₂'⟩ := h₂ G hamb M K hMc hκ hKH
  have h₂n := h₂'.2.2.2.2.2.2.2.1
  have hmain : ∀ g ∈ M, g ∉ normalizer (K : Set G) → K ⊓ conjBy K g = ⊥ := fun g hgM hg =>
    inf_conjBy_eq_bot_of_notMem_normalizer hK.le hKH.2.1 h₂n
      (fun X hXK hXp => (h₁c X hXK hXp).2.1) hgM hg
  exact ⟨hmain, fun g hgM hg =>
    disjoint_sdiff_image_of_inf_conjBy_eq_bot (hmain g hgM fun hn => hg ⟨hgM, hn⟩)⟩

end

end CFSG.FeitThompson.Proofs
