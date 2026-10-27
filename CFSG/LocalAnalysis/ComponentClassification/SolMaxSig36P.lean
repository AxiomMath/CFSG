module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigDich

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem mem_coreActionKernel_of_sup_centralizer {M J : Subgroup X} {t : X}
    (htN : t ∈ normalizer (M : Set X)) (hJt : J ≤ centralizer ({t} : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) : t ∈ UnbalancedLayer.coreActionKernel M := by
  set O : Subgroup X := (pPrimeCore 2 ↥M).map M.subtype with hOdef
  have hsup' : J ⊔ O = M := hsup
  have hOM : O ≤ M := map_subtype_le _
  have hJM : J ≤ M := le_sup_left.trans hsup'.le
  have hON : ∀ g ∈ normalizer (M : Set X), ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (mem_normalizer_iff.mp (le_normalizer_pPrimeCore hg) o).mp ho
  let K : Subgroup X :=
    { carrier := {m | m ∈ M ∧ m⁻¹ * t⁻¹ * m * t ∈ O}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨mul_mem haM hbM, ?_⟩
        have h1 : b⁻¹ * (a⁻¹ * t⁻¹ * a * t) * b ∈ O := by
          have h2 := hON b⁻¹ (inv_mem (le_normalizer hbM)) _ ha
          rwa [inv_inv] at h2
        have h2 := mul_mem h1 hb
        have h3 : (a * b)⁻¹ * t⁻¹ * (a * b) * t =
            b⁻¹ * (a⁻¹ * t⁻¹ * a * t) * b * (b⁻¹ * t⁻¹ * b * t) := by group
        rw [h3]
        exact h2
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨inv_mem haM, ?_⟩
        have h1 := hON a (le_normalizer haM) _ (inv_mem ha)
        have h2 : a⁻¹⁻¹ * t⁻¹ * a⁻¹ * t = a * (a⁻¹ * t⁻¹ * a * t)⁻¹ * a⁻¹ := by group
        rw [h2]
        exact h1 }
  have hMK : M ≤ K := by
    rw [← hsup']
    refine sup_le (fun j hj => ⟨hJM hj, ?_⟩) (fun o ho => ⟨hOM ho, ?_⟩)
    · have hc : j * t = t * j := mem_centralizer_singleton_iff.mp (hJt hj)
      have h1 : j⁻¹ * t⁻¹ * j * t = 1 := by
        calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) := by group
          _ = 1 := by rw [hc]; group
      rw [h1]
      exact one_mem _
    · have h1 := hON t⁻¹ (inv_mem htN) o ho
      rw [inv_inv] at h1
      have h2 := mul_mem (inv_mem ho) h1
      have h3 : o⁻¹ * (t⁻¹ * o * t) = o⁻¹ * t⁻¹ * o * t := by group
      rw [h3] at h2
      exact h2
  exact UnbalancedLayer.mem_coreActionKernel.mpr ⟨htN, fun m hm => (hMK hm).2⟩

theorem exists_coreQuot_of_sup [Finite X] {M L : Subgroup X} (hLM : L ≤ M)
    (hsup : L ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) {r : ℕ}
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)) :
    ∃ θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin r),
      ∀ x : ↥L, θL (x : ↥L ⧸ pPrimeCore 2 ↥L) =
        θ ((⟨x, hLM x.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := L.subgroupOf M with hYdef
  have hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp Y.subtype) := by
    have h1 : Y ⊔ pPrimeCore 2 ↥M = ⊤ := by
      have h2 : (L ⊔ (pPrimeCore 2 ↥M).map M.subtype).subgroupOf M = ⊤ := by
        rw [hsup]
        exact subgroupOf_self M
      rwa [subgroupOf_sup hLM (map_subtype_le _), subgroupOf_map_subtype_self] at h2
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨φ, hφ⟩ := UnbalancedGS.FixedPrimeLayer.exists_quotient_mulEquiv Y hY
  let ψ : ↥L ⧸ pPrimeCore 2 ↥L ≃* Y ⧸ pPrimeCore 2 Y :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM).symm (pPrimeCore_map_iso 2 _)
  refine ⟨ψ.trans (φ.trans θ), fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : ψ (x : ↥L ⧸ pPrimeCore 2 ↥L) =
      (((subgroupOfEquivOfLe hLM).symm x : Y) : Y ⧸ pPrimeCore 2 Y) :=
    QuotientGroup.congr_mk _ _ _ _ _
  rw [h1, hφ]
  rfl

theorem exists_twoSylow_le [Finite X] {K P : Subgroup X} (hPK : P ≤ K) (hP : IsPGroup 2 P) :
    ∃ Q : Subgroup X, P ≤ Q ∧ Q ≤ K ∧ IsPGroup 2 Q ∧
      Nat.card Q = 2 ^ (Nat.card K).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨R, hR⟩ := hP'.exists_le_sylow
  refine ⟨(R : Subgroup K).map K.subtype, fun x hx => ⟨⟨x, hPK hx⟩, hR hx, rfl⟩,
    map_subtype_le _, R.isPGroup'.map _, ?_⟩
  rw [card_map_of_injective K.subtype_injective, R.card_eq_multiplicity]

theorem pPrimeCore_two_eq_bot [Finite X] [IsSimpleGroup X] {t : X} (ht : orderOf t = 2) :
    pPrimeCore 2 X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 X) with h | h
  · exact h
  · exfalso
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hcop
    have h1 := orderOf_dvd_natCard t
    rw [ht] at h1
    have h2 := Nat.Coprime.coprime_dvd_right h1 hcop
    exact absurd h2 (by decide)

theorem le_perfectResidual_map {C L : Subgroup X} (hLC : L ≤ C) (hL : ⁅L, L⁆ = L) :
    L ≤ (perfectResidual ↥C).map C.subtype := by
  set L' := L.subgroupOf C with hL'def
  have hL' : ⁅L', L'⁆ = L' := by
    apply map_injective C.subtype_injective
    rw [map_commutator, hL'def, map_subgroupOf_eq_of_le hLC, hL]
  have h1 : ∀ k : ℕ, L' ≤ derivedSeries ↥C k := by
    intro k
    induction k with
    | zero => rw [derivedSeries_zero]; exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hL']
      exact commutator_mono ih ih
  have h2 : L' ≤ perfectResidual ↥C := le_iInf h1
  have h3 := map_mono (f := C.subtype) h2
  rwa [hL'def, map_subgroupOf_eq_of_le hLC] at h3

end CFSG.ComponentClassification.SolMax
