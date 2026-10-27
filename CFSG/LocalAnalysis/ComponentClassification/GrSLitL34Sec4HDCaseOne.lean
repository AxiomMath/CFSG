module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDTarget
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43N
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43H
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43N
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingle
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_of_le_sup {M K K' : Subgroup X} {r : X} (hrM : r ∈ M) (hKM : K ≤ M) (hK'M : K' ≤ M)
    (hK : ∀ k ∈ K, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) (hK' : ∀ k ∈ K', k⁻¹ * r⁻¹ * k * r ∈ oddIn M)
    {x : X} (hx : x ∈ K ⊔ K' ⊔ oddIn M) : x⁻¹ * r⁻¹ * x * r ∈ oddIn M := by
  have hOMN : M ≤ normalizer ((oddIn M : Subgroup X) : Set X) := GrS4.self_le_normalizer_oddIn M
  let Z : Subgroup X :=
    { carrier := {x | x ∈ M ∧ x⁻¹ * r⁻¹ * x * r ∈ oddIn M}
      one_mem' := ⟨one_mem _, by rw [inv_one, one_mul, mul_one, inv_mul_cancel]; exact one_mem _⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨mul_mem hxM hyM, ?_⟩
        rw [show (x * y)⁻¹ * r⁻¹ * (x * y) * r =
          y⁻¹ * (x⁻¹ * r⁻¹ * x * r) * y⁻¹⁻¹ * (y⁻¹ * r⁻¹ * y * r) by group]
        exact mul_mem ((mem_normalizer_iff.mp (hOMN (inv_mem hyM)) _).mp hx) hy
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨inv_mem hxM, ?_⟩
        rw [show x⁻¹⁻¹ * r⁻¹ * x⁻¹ * r = x * (x⁻¹ * r⁻¹ * x * r)⁻¹ * x⁻¹ by group]
        exact (mem_normalizer_iff.mp (hOMN hxM) _).mp (inv_mem hx) }
  have hOZ : oddIn M ≤ Z := fun o ho => by
    refine ⟨map_subtype_le _ ho, ?_⟩
    have h := (mem_normalizer_iff.mp (hOMN (inv_mem hrM)) o).mp ho
    rw [inv_inv] at h
    rw [show o⁻¹ * r⁻¹ * o * r = o⁻¹ * (r⁻¹ * o * r) by group]
    exact mul_mem (inv_mem ho) h
  have hle : K ⊔ K' ⊔ oddIn M ≤ Z :=
    sup_le (sup_le (fun k hk => ⟨hKM hk, hK k hk⟩) (fun k hk => ⟨hK'M hk, hK' k hk⟩)) hOZ
  exact (hle hx).2

theorem exists_decomposition {M K K' : Subgroup X} {r : X} (hrr : r * r = 1)
    (hKM : K ≤ M) (hK'M : K' ≤ M) (hK'NK : K' ≤ normalizer (K : Set X))
    (hrK : r ∈ normalizer (K : Set X)) (hrK' : r ∈ normalizer (K' : Set X))
    (hK : ∀ k ∈ K, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) (hK' : ∀ k ∈ K', k⁻¹ * r⁻¹ * k * r ∈ oddIn M)
    {t : X} (ht : t ∈ K ⊔ K' ⊔ oddIn M) (htr : t ∈ centralizer ({r} : Set X)) :
    ∃ k ∈ K ⊓ centralizer ({r} : Set X), ∃ k' ∈ K' ⊓ centralizer ({r} : Set X),
      ∃ o ∈ oddIn M ⊓ centralizer ({r} : Set X), t = k' * k * o := by
  have hOMN : M ≤ normalizer ((oddIn M : Subgroup X) : Set X) := GrS4.self_le_normalizer_oddIn M
  have hOodd : Odd (Nat.card ↥(oddIn M)) := UnbalancedCorr.odd_card_map_pPrimeCore M
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  obtain ⟨y, hy, o₀, ho₀, rfl⟩ :=
    Single.exists_mul_of_mem_sup (sup_le (hKM.trans hOMN) (hK'M.trans hOMN)) ht
  rw [sup_comm] at hy
  obtain ⟨k'₀, hk'₀, k₀, hk₀, rfl⟩ := Single.exists_mul_of_mem_sup hK'NK hy
  have fix : ∀ {H : Subgroup X}, r ∈ normalizer (H : Set X) →
      (∀ k ∈ H, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) → ∀ k ∈ H,
        ∃ o ∈ H ⊓ oddIn M, r * (k * o) = k * o * r := by
    intro H hrH hH k hk
    refine GrS4.exists_commute_mul_mem (hOodd.of_dvd_nat (card_dvd_of_le inf_le_right)) hrr
      (mem_inf.mpr ⟨mul_mem (inv_mem hk) ((mem_normalizer_iff.mp hrH k).mp hk), ?_⟩)
    have h := hH k hk
    rw [hri] at h ⊢
    simpa only [mul_assoc] using h
  obtain ⟨o₁, ho₁, hc₁⟩ := fix hrK hK k₀ hk₀
  obtain ⟨o₂, ho₂, hc₂⟩ := fix hrK' hK' k'₀ hk'₀
  have hk₁ : k₀ * o₁ ∈ K ⊓ centralizer ({r} : Set X) :=
    mem_inf.mpr ⟨mul_mem hk₀ (mem_inf.mp ho₁).1, mem_centralizer_singleton_iff.mpr hc₁.symm⟩
  have hk'₁ : k'₀ * o₂ ∈ K' ⊓ centralizer ({r} : Set X) :=
    mem_inf.mpr ⟨mul_mem hk'₀ (mem_inf.mp ho₂).1, mem_centralizer_singleton_iff.mpr hc₂.symm⟩
  refine ⟨k₀ * o₁, hk₁, k'₀ * o₂, hk'₁, (k'₀ * o₂ * (k₀ * o₁))⁻¹ * (k'₀ * k₀ * o₀), ?_, ?_⟩
  · refine mem_inf.mpr ⟨?_, mul_mem (inv_mem (mul_mem (mem_inf.mp hk'₁).2 (mem_inf.mp hk₁).2))
      htr⟩
    rw [show (k'₀ * o₂ * (k₀ * o₁))⁻¹ * (k'₀ * k₀ * o₀) =
      o₁⁻¹ * (k₀⁻¹ * o₂⁻¹ * k₀⁻¹⁻¹) * o₀ by group]
    exact mul_mem (mul_mem (inv_mem (mem_inf.mp ho₁).2)
      ((mem_normalizer_iff.mp (hOMN (inv_mem (hKM hk₀))) _).mp (inv_mem (mem_inf.mp ho₂).2)))
      ho₀
  · group

theorem false_of_core_trivial_involution
    (hMax : MaximalTwoComponentInputHe) (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) (h64 : HeldSylowElementarySixtyFour)
    (hMult : TBLit.HeldTrivialMultiplier) [IsSimpleGroup X] (hnab : ∃ x y : X, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog X) (hU : ¬ OutcomeLocal.UOutcome X) {a r : X}
    {L K M : Subgroup X} (ha : orderOf a = 2) (hr : orderOf r = 2) (har : a * r = r * a)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))))
    (e : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)
    (hCaN : centralizer ({a} : Set X) ≤ normalizer (L : Set X)) (hLM : L ≤ M) (haM : a ∈ M)
    (hrM : r ∈ M) (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M))
    (hKa : conjugate K a ≠ K) (hLKK : L ≤ K ⊔ conjugate K a ⊔ oddIn M)
    (hrK : r ∈ normalizer (K : Set X)) (hrK' : r ∈ normalizer (conjugate K a : Set X))
    (hrKc : ∀ k ∈ K, k⁻¹ * r⁻¹ * k * r ∈ oddIn M)
    (hrK'c : ∀ k ∈ conjugate K a, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := conjugate K a with hK'def
  set Cr := centralizer ({r} : Set X) with hCr
  have hrr : r * r = 1 := by rw [← pow_two, ← hr, pow_orderOf_eq_one]
  have hK'M : K' ≤ M := conjugate_le_of_mem hKM haM
  have hK'c : IsPComponent 2 (K'.subgroupOf M) := isPComponent_conjugate_subgroupOf haM hKc
  have hne : K ≠ K' := fun h => hKa h.symm
  have hKK' : ⁅K, K'⁆ ≤ oddIn K ⊓ oddIn K' := GrS5.commutator_le_inf_oddIn hKM hK'M hKc hK'c hne
  have hK'NK : K' ≤ normalizer (K : Set X) := (GrS5.commutator_le_of_ne hKM hK'M hKc hK'c hne).2
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hOMN : M ≤ normalizer ((oddIn M : Subgroup X) : Set X) := GrS4.self_le_normalizer_oddIn M
  have hOodd : Odd (Nat.card ↥(oddIn M)) := UnbalancedCorr.odd_card_map_pPrimeCore M
  have hrCa : r ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr har.symm
  have haCr : a ∈ Cr := mem_centralizer_singleton_iff.mpr har
  have hrL : r ∈ normalizer (L : Set X) := hCaN hrCa
  have hLr : ∀ j ∈ L, j⁻¹ * r⁻¹ * j * r ∈ (pPrimeCore 2 L).map L.subtype := by
    intro j hj
    refine GrS5.inf_oddIn_le_oddIn hLM (mem_inf.mpr ⟨mem_of_le_sup hrM hKM hK'M hrKc hrK'c
      (hLKK hj), ?_⟩)
    have h := (mem_normalizer_iff.mp (inv_mem hrL) j).mp hj
    rw [inv_inv] at h
    rw [show j⁻¹ * r⁻¹ * j * r = j⁻¹ * (r⁻¹ * j * r) by group]
    exact mul_mem (inv_mem hj) h
  obtain ⟨L', -, -, hCN, ⟨e'⟩, hTL', hcov⟩ :=
    exists_held_target hMax hS hHN h64 hMult hnab hK hU ha hr har hLa hLc e hrL hLr
  set T := gsFixedLayer L r with hTdef
  have hTLr : T ≤ L ⊓ Cr := gsFixedLayer_le_inf L r
  have hKN : K ⊓ Cr ≤ normalizer (L' : Set X) := inf_le_right.trans hCN
  have hK'N : K' ⊓ Cr ≤ normalizer (L' : Set X) := inf_le_right.trans hCN
  have hON : oddIn M ⊓ Cr ≤ normalizer (L' : Set X) := inf_le_right.trans hCN
  have hcovT : ∀ p ∈ heP, ∃ t ∈ T, heN e' t = p := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := exists_heL_eq (e := e') hp
    have hl' : l ∈ T ⊔ (pPrimeCore 2 L').map L'.subtype := by rw [hcov]; exact hl
    obtain ⟨t, ht, u, hu, rfl⟩ :=
      Single.exists_mul_of_mem_sup (hTL'.trans (GrS4.self_le_normalizer_oddIn L')) hl'
    have hu' : u ∈ L' := map_subtype_le _ hu
    refine ⟨t, ht, ?_⟩
    rw [heN_eq_heL (hTL' ht), heL_mul (hTL' ht) hu', (heL_eq_one_iff hu').mpr hu, mul_one]
  set ρ := heAutGroup.subtype.comp (heModelN e') with hρ
  have hmemρ : ∀ {U : Subgroup X}, U ≤ normalizer (L' : Set X) → ∀ {y : Equiv.Perm (Fin 8330)},
      y ∈ (U.subgroupOf (normalizer (L' : Set X))).map ρ ↔ ∃ x ∈ U, heN e' x = y := by
    intro U hU y
    constructor
    · rintro ⟨⟨x, hxN⟩, hx, rfl⟩
      exact ⟨x, hx, by rw [heN_of_mem hxN]; rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hU hx⟩, hx, by rw [heN_of_mem (hU hx)]; rfl⟩
  set B₀ := ((oddIn M ⊓ Cr).subgroupOf (normalizer (L' : Set X))).map ρ with hB₀def
  have hB₀ : ∀ b ∈ B₀, b = 1 := by
    refine eq_one_of_odd_normalized ?_ ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (hmemρ hON).mp hy
      exact heN_mem (hON hx)
    · have h1 : Nat.card ↥B₀ ∣ Nat.card ↥(oddIn M ⊓ Cr) := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe hON).toEquiv]
        exact card_map_dvd _ _
      exact (hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)).of_dvd_nat h1
    · intro p hp b hb
      obtain ⟨t, ht, rfl⟩ := hcovT p hp
      obtain ⟨o, ho, rfl⟩ := (hmemρ hON).mp hb
      have htN : t ∈ normalizer (L' : Set X) := hCN (mem_inf.mp (hTLr ht)).2
      have hoN := hON ho
      rw [← heN_inv htN, ← heN_mul htN hoN, ← heN_mul (mul_mem htN hoN) (inv_mem htN)]
      refine (hmemρ hON).mpr ⟨_, mem_inf.mpr ⟨?_, mul_mem (mul_mem (mem_inf.mp (hTLr ht)).2
        (mem_inf.mp ho).2) (inv_mem (mem_inf.mp (hTLr ht)).2)⟩, rfl⟩
      exact (mem_normalizer_iff.mp (hOMN (hLM (mem_inf.mp (hTLr ht)).1)) o).mp (mem_inf.mp ho).1
  have hρo : ∀ o ∈ oddIn M ⊓ Cr, heN e' o = 1 := fun o ho =>
    hB₀ _ ((hmemρ hON).mpr ⟨o, ho, rfl⟩)
  have hcomm : ∀ x ∈ imN e' (K ⊓ Cr), ∀ y ∈ imN e' (K' ⊓ Cr), x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := (mem_imN hKN).mp hx
    obtain ⟨k', hk', rfl⟩ := (mem_imN hK'N).mp hy
    have hkN := hKN hk
    have hk'N := hK'N hk'
    have hc : ⁅k, k'⁆ ∈ oddIn M ⊓ Cr := by
      refine mem_inf.mpr ⟨hOK (hKK' (commutator_mem_commutator (mem_inf.mp hk).1
        (mem_inf.mp hk').1)).1, ?_⟩
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (mem_inf.mp hk).2 (mem_inf.mp hk').2)
        (inv_mem (mem_inf.mp hk).2)) (inv_mem (mem_inf.mp hk').2)
    have h1 := hρo _ hc
    rw [commutatorElement_def, heN_mul (mul_mem (mul_mem hkN hk'N) (inv_mem hkN)) (inv_mem hk'N),
      heN_mul (mul_mem hkN hk'N) (inv_mem hkN), heN_mul hkN hk'N, heN_inv hkN,
      heN_inv hk'N] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcov' : ∀ p ∈ heP, ∃ x ∈ imN e' (K ⊓ Cr), ∃ y ∈ imN e' (K' ⊓ Cr), p = y * x := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := hcovT p hp
    obtain ⟨k, hk, k', hk', o, ho, hdec⟩ := exists_decomposition hrr hKM hK'M hK'NK hrK hrK'
      hrKc hrK'c (hLKK (mem_inf.mp (hTLr ht)).1) (mem_inf.mp (hTLr ht)).2
    refine ⟨heN e' k, (mem_imN hKN).mpr ⟨k, hk, rfl⟩, heN e' k', (mem_imN hK'N).mpr ⟨k', hk', rfl⟩,
      ?_⟩
    rw [hdec, heN_mul (mul_mem (hK'N hk') (hKN hk)) (hON ho), heN_mul (hK'N hk') (hKN hk),
      hρo o ho, mul_one]
  have haN : a ∈ normalizer (L' : Set X) := hCN haCr
  refine false_of_commuting_cover (fun y hy => ?_) (fun y hy => ?_) hcomm hcov'
    (heN_mem (e := e') haN) ?_ ?_
  · obtain ⟨x, hx, rfl⟩ := (mem_imN hKN).mp hy
    exact heN_mem (hKN hx)
  · obtain ⟨x, hx, rfl⟩ := (mem_imN hK'N).mp hy
    exact heN_mem (hK'N hx)
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := (mem_imN hKN).mp hx
    have hkN := hKN hk
    rw [← heN_inv haN, ← heN_mul (inv_mem haN) hkN, ← heN_mul (mul_mem (inv_mem haN) hkN) haN]
    refine (mem_imN hK'N).mpr ⟨_, mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem haCr)
      (mem_inf.mp hk).2) haCr⟩, rfl⟩
    rw [hK'def, mem_conjugate_iff, show a * (a⁻¹ * k * a) * a⁻¹ = k by group]
    exact (mem_inf.mp hk).1
  · intro y hy
    obtain ⟨k', hk', rfl⟩ := (mem_imN hK'N).mp hy
    have hk'N := hK'N hk'
    rw [← heN_inv haN, ← heN_mul haN hk'N, ← heN_mul (mul_mem haN hk'N) (inv_mem haN)]
    refine (mem_imN hKN).mpr ⟨_, mem_inf.mpr ⟨?_, mul_mem (mul_mem haCr (mem_inf.mp hk').2)
      (inv_mem haCr)⟩, rfl⟩
    exact mem_conjugate_iff.mp (mem_inf.mp hk').1

end CFSG.ComponentClassification.GrSLit.HeDiag
