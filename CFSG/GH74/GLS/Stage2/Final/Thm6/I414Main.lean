module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Red
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.I414

open CFSG CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatalogueBPrimeJoin
  (primeResidual pComponent_iff_subnormal_generated_quasisimple)
open CFSG.ComponentClassification.CatalogueBHeldSmallCore (pComponent_perfect)

theorem commutator_subtype_eq (p : ℕ) {X : Type*} [Group X] (K : Subgroup X) :
    (⁅pPrimeCore p ↥K, (⊤ : Subgroup ↥K)⁆ : Subgroup ↥K).map K.subtype =
      ⁅pPrimeCoreOf p K, K⁆ := by
  rw [Subgroup.map_commutator]
  have : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [this]
  rfl

theorem commutator_le_pPrimeCoreOf (p : ℕ) {X : Type*} [Group X] (K : Subgroup X) :
    ⁅pPrimeCoreOf p K, K⁆ ≤ pPrimeCoreOf p K := by
  rw [← commutator_subtype_eq]
  have : (pPrimeCore p ↥K).Normal := pPrimeCore_normal (p := p) (G := ↥K)
  exact Subgroup.map_mono (Subgroup.commutator_le_left _ _)

theorem pPrimeCoreOf_le_normalizer_commutator (p : ℕ) {X : Type*} [Group X] (K : Subgroup X) :
    pPrimeCoreOf p K ≤ Subgroup.normalizer ((⁅pPrimeCoreOf p K, K⁆ : Subgroup X) : Set X) := by
  have hn : (pPrimeCore p ↥K).Normal := pPrimeCore_normal (p := p) (G := ↥K)
  have hWn : (⁅pPrimeCore p ↥K, (⊤ : Subgroup ↥K)⁆ : Subgroup ↥K).Normal :=
    Subgroup.commutator_normal _ _
  rw [← commutator_subtype_eq]
  rintro _ ⟨o, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨o * w * o⁻¹, hWn.conj_mem w hw o, rfl⟩
  · rintro ⟨w', hw', hw'eq⟩
    refine ⟨o⁻¹ * w' * o, ?_, ?_⟩
    · have := hWn.conj_mem w' hw' o⁻¹
      simpa using this
    · rw [map_mul, map_mul, map_inv, hw'eq]
      group

theorem ig_4_14_thm {X : Type} [Group X] [Finite X] (p : ℕ) [Fact p.Prime] {K : Subgroup X}
    (hK : IsPComponent p K) (hS : HasPropS ↥(pPrimeCore p ↥K)) {r : ℕ} [Fact r.Prime]
    {R : Subgroup X} (hR : IsSylowOf r R ⁅pPrimeCoreOf p K, K⁆) (hR1 : R ≠ ⊥) :
    K ⊓ Subgroup.centralizer (R : Set X) ≤ (pPrimePCore p ↥K).map K.subtype := by
  obtain ⟨-, hgen, hqs⟩ := (pComponent_iff_subnormal_generated_quasisimple p K).mp hK
  have hperf : Group.IsPerfect ↥K := pComponent_perfect p K hK
  have hWmap := commutator_subtype_eq p K
  have hRK : R ≤ K := by
    have := hR.le
    rw [← hWmap] at this
    exact this.trans (Subgroup.map_subtype_le _)
  have hR' : IsSylowOf r (R.subgroupOf K) ⁅pPrimeCore p ↥K, (⊤ : Subgroup ↥K)⁆ := by
    refine (isSylowOf_map_subtype_iff K).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hRK, hWmap]
    exact hR
  have hR1' : R.subgroupOf K ≠ ⊥ := by
    intro h
    apply hR1
    rw [← Subgroup.map_subgroupOf_eq_of_le hRK, h, Subgroup.map_bot]
  have key := ig414_intrinsic hperf hgen hqs hS hR' hR1'
  intro x hx
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
  refine ⟨⟨x, hxK⟩, key ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyR : (y : X) ∈ R := hy
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ hyR)

theorem ig_4_14_cover {X : Type} [Group X] [Finite X] (p : ℕ) [Fact p.Prime] {K : Subgroup X}
    (hK : IsPComponent p K) (hS : HasPropS ↥(pPrimeCore p ↥K)) {r : ℕ} [Fact r.Prime]
    {V : Subgroup X} (hV : IsSylowOf r V (pPrimeCoreOf p K))
    (hcov : K ≤ (K ⊓ Subgroup.centralizer (V : Set X)) ⊔ pPrimeCoreOf p K) :
    ¬ r ∣ Nat.card ↥(⁅pPrimeCoreOf p K, K⁆ : Subgroup X) := by
  intro hdvd
  obtain ⟨-, -, hqs⟩ := (pComponent_iff_subnormal_generated_quasisimple p K).mp hK
  have hWO := commutator_le_pPrimeCoreOf p K
  have hKN := pPrimeCoreOf_le_normalizer_commutator p K
  have hSyl : IsSylowOf r (V ⊓ ⁅pPrimeCoreOf p K, K⁆) ⁅pPrimeCoreOf p K, K⁆ :=
    hV.inf_of_le_normalizer hWO hKN
  have hne : V ⊓ ⁅pPrimeCoreOf p K, K⁆ ≠ ⊥ := by
    intro hbot
    have hc := hSyl.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have hpos : 0 < (Nat.card ↥(⁅pPrimeCoreOf p K, K⁆ : Subgroup X)).factorization r :=
      (Fact.out : r.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    have h1 : 1 < r ^ (Nat.card ↥(⁅pPrimeCoreOf p K, K⁆ : Subgroup X)).factorization r :=
      Nat.one_lt_pow hpos.ne' (Fact.out : r.Prime).one_lt
    omega
  have hmain := ig_4_14_thm p hK hS hSyl hne
  have hVR : Subgroup.centralizer (V : Set X) ≤
      Subgroup.centralizer ((V ⊓ ⁅pPrimeCoreOf p K, K⁆ : Subgroup X) : Set X) :=
    Subgroup.centralizer_le (fun x hx => hx.1)
  have hOQ : pPrimeCoreOf p K ≤ (pPrimePCore p ↥K).map K.subtype :=
    Subgroup.map_mono (pPrimeCore_le_pPrimePCore p K)
  have hKQ : K ≤ (pPrimePCore p ↥K).map K.subtype :=
    hcov.trans (sup_le (fun x hx => hmain ⟨hx.1, hVR hx.2⟩) hOQ)
  apply pPrimePCore_ne_top hqs
  refine eq_top_iff.mpr fun k _ => ?_
  obtain ⟨q, hq, hqk⟩ := hKQ k.2
  have : q = k := Subtype.ext hqk
  rwa [this] at hq

end CFSG.GH74.GLS.Stage2.Final.Thm6.I414
