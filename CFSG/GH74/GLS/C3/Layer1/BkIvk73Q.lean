module

public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Abs
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseISyl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53M
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L55B

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

section MLevel

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem map_conj_self_of_mem {A : Subgroup M} {r : M} (hr : r ∈ A) :
    A.map (MulAut.conj r).toMonoidHom = A := by
  ext y
  rw [mem_map_conjHom_iff]
  constructor
  · intro h
    have := A.mul_mem (A.mul_mem hr h) (A.inv_mem hr)
    simpa [mul_assoc] using this
  · intro h
    exact A.mul_mem (A.mul_mem (A.inv_mem hr) h) hr

omit [Finite M] in
theorem isCompIn_of_isPCompIn_of_quasisimple {X K : Subgroup M} (h : IsPCompIn 2 X K)
    (hq : IsQuasisimple ↥K) : IsCompIn X K := by
  refine ⟨h.1, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1).symm hq
  · obtain ⟨K', -, hsub, -⟩ := h.2
    exact hsub

theorem centralizes_of_map_commute {K : Subgroup M} {u r : M} (hKq : IsQuasisimple ↥K)
    (hKnc : ∃ a ∈ K, ∃ b ∈ K, piO M a * piO M b ≠ piO M b * piO M a)
    (hu : IsPCompIn 2 (centralizer ({u} : Set M)) K) (hr : r ∈ centralizer ({u} : Set M))
    (hrK : ∀ k ∈ K, piO M k * piO M r = piO M r * piO M k) :
    ∀ k ∈ K, r * k = k * r := by
  classical
  have hC : IsCompIn (centralizer ({u} : Set M)) K := isCompIn_of_isPCompIn_of_quasisimple hu hKq
  have hCr : (centralizer ({u} : Set M)).map (MulAut.conj r).toMonoidHom =
      centralizer ({u} : Set M) := map_conj_self_of_mem hr
  have hKrC : IsCompIn (centralizer ({u} : Set M)) (K.map (MulAut.conj r).toMonoidHom) := by
    have := CFSG.GH74.GLS.LU.Local.isCompIn_map_conj hC r
    rwa [hCr] at this
  rcases CFSG.LocalCores.distinct_components_commute hC.2 hKrC.2 with heq | hcomm
  ·
    have hKK : K = K.map (MulAut.conj r).toMonoidHom := by
      have := Subgroup.subgroupOf_inj.1 heq
      rwa [inf_eq_left.2 hC.1, inf_eq_left.2 hKrC.1] at this
    have hKr : ∀ y, y ∈ K ↔ r⁻¹ * y * r ∈ K := fun y => by
      rw [← mem_map_conjHom_iff, ← hKK]
    have hrN : r ∈ normalizer (K : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := hKr (r * h * r⁻¹)
      rw [show r⁻¹ * (r * h * r⁻¹) * r = h by group] at this
      exact this.symm
    have hcs : r ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
      refine ⟨hrN, TwoThin.mem_normalizer_pPrimeCoreOf hrN, fun k hk => ?_⟩
      have h1 : ⁅k, r⁆ ∈ K := by
        have hk' : r * k⁻¹ * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hrN k⁻¹).1 (K.inv_mem hk)
        have : ⁅k, r⁆ = k * (r * k⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]
        exact K.mul_mem hk hk'
      have h2 : ⁅k, r⁆ ∈ pPrimeCore 2 M := by
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 M), MonoidHom.mem_ker]
        have : (QuotientGroup.mk' (pPrimeCore 2 M)) ⁅k, r⁆ = ⁅piO M k, piO M r⁆ :=
          map_commutatorElement _ _ _
        rw [this]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hrK k hk)
      exact CFSG.ComponentClassification.GSThmB.OddQuot.inf_pPrimeCore_le_oddCoreIn K ⟨h1, h2⟩
    exact fun k hk => Th2.commute_of_mem_cSec hKq hcs k hk
  ·
    exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hKnc
    have hb' : r * b * r⁻¹ ∈ K.map (MulAut.conj r).toMonoidHom :=
      ⟨b, hb, by simp [MulAut.conj_apply]⟩
    have h1 : a * (r * b * r⁻¹) = (r * b * r⁻¹) * a := by
      have hmem1 : (⟨a, hC.1 ha⟩ : ↥(centralizer ({u} : Set M))) ∈
          K.subgroupOf (centralizer ({u} : Set M)) := ha
      have hmem2 : (⟨r * b * r⁻¹, hKrC.1 hb'⟩ : ↥(centralizer ({u} : Set M))) ∈
          (K.map (MulAut.conj r).toMonoidHom).subgroupOf (centralizer ({u} : Set M)) := hb'
      have h0 := Subgroup.commutator_mem_commutator hmem1 hmem2
      rw [hcomm, Subgroup.mem_bot] at h0
      exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 h0)
    have hπ : piO M (r * b * r⁻¹) = piO M b := by
      rw [map_mul, map_mul, map_inv]
      have h2 := hrK b hb
      calc piO M r * piO M b * (piO M r)⁻¹ = (piO M b * piO M r) * (piO M r)⁻¹ := by rw [h2]
        _ = piO M b := by group
    apply hab
    have h3 : piO M a * piO M (r * b * r⁻¹) = piO M (r * b * r⁻¹) * piO M a := by
      rw [← map_mul, ← map_mul, h1]
    rw [hπ] at h3
    exact h3

omit [Finite M] in
theorem isSylowOf_two_of_maximal [Finite M] {P H : Subgroup M} (hP : IsPGroup 2 ↥P) (hPH : P ≤ H)
    (hmax : ∀ B : Subgroup M, P ≤ B → B ≤ H → IsPGroup 2 ↥B → B = P) : IsSylowOf 2 P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPsub : IsPGroup 2 ↥(P.subgroupOf H) := hP.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hPsub.exists_le_sylow
  have hT₁ : IsSylowOf 2 ((S₁ : Subgroup ↥H).map H.subtype) H := ⟨S₁, rfl⟩
  have hPT₁ : P ≤ (S₁ : Subgroup ↥H).map H.subtype := by
    intro t ht
    exact ⟨⟨t, hPH ht⟩, hS₁ (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have heq := hmax _ hPT₁ hT₁.le hT₁.isPGroup
  rw [heq] at hT₁
  exact hT₁

theorem isSylowOf_comap_centralizer_map {K Q : Subgroup M} (hKq : IsQuasisimple ↥K)
    (hKnc : ∃ a ∈ K, ∃ b ∈ K, piO M a * piO M b ≠ piO M b * piO M a)
    (hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q) (hQne : Q ≠ ⊥)
    (hQS : IsSylowOf 2 Q (centralizer (K : Set M)))
    (hterm : ∀ u ∈ Q, orderOf u = 2 → IsPCompIn 2 (centralizer ({u} : Set M)) K) :
    IsSylowOf 2 Q ((centralizer ((K.map (piO M) : Subgroup (M ⧸ pPrimeCore 2 M)) :
      Set (M ⧸ pPrimeCore 2 M))).comap (piO M)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥Q := hQS.isPGroup
  have hQD : Q ≤ (centralizer ((K.map (piO M) : Subgroup (M ⧸ pPrimeCore 2 M)) :
      Set (M ⧸ pPrimeCore 2 M))).comap (piO M) := by
    intro q hq
    rw [Subgroup.mem_comap, mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h1 := mem_centralizer_iff.1 (hQS.le hq) k hk
    show piO M k * piO M q = piO M q * piO M k
    rw [← map_mul, ← map_mul, h1]
  refine isSylowOf_two_of_maximal hQ2 hQD ?_
  intro R hQR hRD hR2
  have hRC : ∀ r ∈ R, ∀ k ∈ K, piO M k * piO M r = piO M r * piO M k := by
    intro r hr k hk
    have h1 := hRD hr
    rw [Subgroup.mem_comap, mem_centralizer_iff] at h1
    exact h1 (piO M k) ⟨k, hk, rfl⟩
  obtain ⟨x, hxQ, hx2⟩ := Th2.exists_involution_mem hQ2 hQne
  have hR1 : R ⊓ centralizer ({x} : Set M) = Q := by
    have hle : R ⊓ centralizer ({x} : Set M) ≤ centralizer (K : Set M) := by
      rintro r ⟨hrR, hrx⟩
      rw [mem_centralizer_iff]
      intro k hk
      exact (centralizes_of_map_commute hKq hKnc (hterm x hxQ hx2) hrx (hRC r hrR) k hk).symm
    have hQle : Q ≤ R ⊓ centralizer ({x} : Set M) :=
      le_inf hQR fun q hq => mem_centralizer_singleton_iff.2 (hQab q hq x hxQ)
    exact hQS.eq_of_le hQle hle hR2.to_inf_left
  have hRne : R ≠ ⊥ := by
    intro h0
    have : x ∈ (⊥ : Subgroup M) := h0 ▸ hQR hxQ
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hx2
    omega
  obtain ⟨w, hwR, hw2, hwc⟩ := Th2.exists_central_involution hR2 hRne
  have hwQ : w ∈ Q := by
    rw [← hR1]
    exact ⟨hwR, mem_centralizer_singleton_iff.2 (hwc x (hQR hxQ))⟩
  have hRC' : R ≤ centralizer (K : Set M) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro k hk
    exact (centralizes_of_map_commute hKq hKnc (hterm w hwQ hw2)
      (mem_centralizer_singleton_iff.2 (hwc r hr).symm) (hRC r hr) k hk).symm
  exact hQS.eq_of_le hQR hRC' hR2

theorem isSylowOf_centralizer_map {K Q : Subgroup M} (hKq : IsQuasisimple ↥K)
    (hKnc : ∃ a ∈ K, ∃ b ∈ K, piO M a * piO M b ≠ piO M b * piO M a)
    (hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q) (hQne : Q ≠ ⊥)
    (hQS : IsSylowOf 2 Q (centralizer (K : Set M)))
    (hterm : ∀ u ∈ Q, orderOf u = 2 → IsPCompIn 2 (centralizer ({u} : Set M)) K) :
    IsSylowOf 2 (Q.map (piO M)) (centralizer ((K.map (piO M) : Subgroup (M ⧸ pPrimeCore 2 M)) :
      Set (M ⧸ pPrimeCore 2 M))) := by
  have h1 := isSylowOf_comap_centralizer_map hKq hKnc hQab hQne hQS hterm
  have h2 := CFSG.RankThree.PartTwo.Sec12.IsSylowOf.map h1 (piO M)
  rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h2

omit [Finite M] in
theorem exists_noncomm_map_of_equiv {K : Subgroup M} {n : ℕ} (hn : n = 5 ∨ n = 7)
    (e : ↥(K.map (piO M)) ≃* alternatingGroup (Fin n)) :
    ∃ a ∈ K, ∃ b ∈ K, piO M a * piO M b ≠ piO M b * piO M a := by
  by_contra h
  push Not at h
  have hc : ∀ a b : ↥(K.map (piO M)), a * b = b * a := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    exact Subtype.ext (h a ha b hb)
  have : IsMulCommutative ↥(K.map (piO M)) := ⟨⟨hc⟩⟩
  have hs : Group.IsSolvable ↥(K.map (piO M)) := inferInstance
  have hA : Group.IsSolvable (alternatingGroup (Fin n)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact alt_not_isSolvable n hn hA

theorem equiv_map_piO {K : Subgroup M}
    (hOK : ∀ k : ↥K, k ∈ pPrimeCore 2 ↥K → (k : M) ∈ pPrimeCore 2 M) :
    Nonempty (↥(K.map (piO M)) ≃* (↥K ⧸ pPrimeCore 2 ↥K)) := by
  classical
  let φ : ↥K →* ↥(K.map (piO M)) := (piO M).subgroupMap K
  have hφ : Function.Surjective φ := (piO M).subgroupMap_surjective K
  have hker : φ.ker = pPrimeCore 2 ↥K := by
    apply le_antisymm
    · have hN : φ.ker.Normal := inferInstance
      have hle : φ.ker.map K.subtype ≤ pPrimeCore 2 M := by
        rintro _ ⟨k, hk, rfl⟩
        have h1 : piO M (k : M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
        exact (QuotientGroup.eq_one_iff _).1 h1
      have h2 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective K.subtype_injective] at h2
      have hcop : Nat.Coprime 2 (Nat.card φ.ker) :=
        Nat.Coprime.coprime_dvd_right h2 pPrimeCore_coprime_card
      exact le_sSup ⟨hN, hcop⟩
    · intro k hk
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).2 (hOK k hk)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

end MLevel

end CFSG.GH74.GLS.C3.Layer1.Bk
