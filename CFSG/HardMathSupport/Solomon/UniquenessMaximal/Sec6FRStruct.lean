module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DBar

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_core3 (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hg]

omit [Finite G] in
theorem dQ_le_normalizer (K : Subgroup G) : dQ K ≤ Subgroup.normalizer (K : Set G) :=
  fun _ hg => (mem_dQ.1 hg).1

omit [Finite G] in
theorem mem_dQ_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ dQ K ↔ ∀ y ∈ K, y * g * y⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 K :=
  ⟨fun h => (mem_dQ.1 h).2.2, fun h => mem_dQ.2 ⟨hg, normalizer_le_normalizer_core3 K hg, h⟩⟩

omit [Finite G] in
theorem normalizer_le_normalizer_dQ (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (dQ K : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (K : Set G), ∀ g ∈ dQ K, n * g * n⁻¹ ∈ dQ K := by
    intro n hn g hg
    obtain ⟨hgK, hgU, hgc⟩ := mem_dQ.1 hg
    have hnU := normalizer_le_normalizer_core3 K hn
    refine mem_dQ.2 ⟨?_, ?_, ?_⟩
    · exact mul_mem (mul_mem hn hgK) (inv_mem hn)
    · exact mul_mem (mul_mem hnU hgU) (inv_mem hnU)
    · intro y hy
      have hy' : n⁻¹ * y * n ∈ K := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) y).1 hy
        simpa using this
      have h1 := hgc _ hy'
      have h3 : y * (n * g * n⁻¹) * y⁻¹ * (n * g * n⁻¹)⁻¹ =
          n * ((n⁻¹ * y * n) * g * (n⁻¹ * y * n)⁻¹ * g⁻¹) * n⁻¹ := by group
      rw [h3]
      exact (Subgroup.mem_normalizer_iff.1 hnU _).1 h1
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun h => key n hn g h, fun h => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_commute {S T : Subgroup G}
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : G} (hx : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s * t := by
  let W : Subgroup G :=
    { carrier := {g | ∃ s ∈ S, ∃ t ∈ T, g = s * t}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
        refine ⟨s * s', mul_mem hs hs', t * t', mul_mem ht ht', ?_⟩
        have h := hcomm s' hs' t ht
        calc s * t * (s' * t') = s * (t * s') * t' := by group
          _ = s * (s' * t) * t' := by rw [h]
          _ = s * s' * (t * t') := by group
      inv_mem' := by
        rintro _ ⟨s, hs, t, ht, rfl⟩
        refine ⟨s⁻¹, inv_mem hs, t⁻¹, inv_mem ht, ?_⟩
        have h := hcomm s hs t⁻¹ (inv_mem ht)
        calc (s * t)⁻¹ = t⁻¹ * s⁻¹ := by group
          _ = s⁻¹ * t⁻¹ := by
            have h2 := hcomm s⁻¹ (inv_mem hs) t⁻¹ (inv_mem ht)
            exact h2.symm }
  have hle : S ⊔ T ≤ W :=
    sup_le (fun s hs => ⟨s, hs, 1, one_mem _, by simp⟩) (fun t ht => ⟨1, one_mem _, t, ht, by simp⟩)
  exact hle hx

theorem exists_rStruct {B K : Subgroup G} (hBp : IsPGroup 3 ↥B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hInn : ∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K, b * y * b⁻¹ * (k * y * k⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 K) :
    ∃ R : Subgroup G, B ≤ R ∧ IsPGroup 3 ↥R ∧ R ≤ K ⊔ dQ K ∧
      Nat.card ↥(R ⊓ K) = 3 ^ (Nat.card K).factorization 3 ∧
      (∀ r₁ ∈ R ⊓ K, ∀ r₂ ∈ R ⊓ dQ K, r₁ * r₂ = r₂ * r₁) ∧
      (∀ r ∈ R, ∃ r₁ ∈ R ⊓ K, ∃ r₂ ∈ R ⊓ dQ K, r = r₁ * r₂) ∧
      R ≤ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) ∧
      R ≤ Subgroup.normalizer ((R ⊓ dQ K : Subgroup G) : Set G) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup G := K ⊔ dQ K with hY
  have hKY : K ≤ Y := le_sup_left
  have hdY : dQ K ≤ Y := le_sup_right
  have hKN : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := sup_le hKN (dQ_le_normalizer K)
  have hYd : Y ≤ Subgroup.normalizer (dQ K : Set G) := fun g hg => normalizer_le_normalizer_dQ K (hYN hg)
  have hKd : K ≤ Subgroup.normalizer (dQ K : Set G) := hKY.trans hYd
  have hdK : dQ K ≤ Subgroup.normalizer (K : Set G) := dQ_le_normalizer K
  have hBY : B ≤ Y := by
    intro b hb
    obtain ⟨k, hk, h⟩ := hInn b hb
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := hKN hk
    have hd : k⁻¹ * b ∈ dQ K := by
      rw [mem_dQ_of_mem_normalizer (mul_mem (inv_mem hkN) (hBN hb))]
      intro y hy
      have h1 := h y⁻¹ (inv_mem hy)
      have h2 : y * (k⁻¹ * b) * y⁻¹ * (k⁻¹ * b)⁻¹ =
          (y * k⁻¹) * (b * y⁻¹ * b⁻¹ * (k * y⁻¹ * k⁻¹)⁻¹) * (y * k⁻¹)⁻¹ := by group
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 K
        (mul_mem hy (inv_mem hk))) _).1 h1
    have : b = k * (k⁻¹ * b) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk hd
  have hBp' : IsPGroup 3 ↥(B.subgroupOf Y) := hBp.comap_subtype
  obtain ⟨P, hP⟩ := hBp'.exists_le_sylow
  set R : Subgroup G := (P : Subgroup ↥Y).map Y.subtype with hR
  have hRY : R ≤ Y := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hBR : B ≤ R := fun b hb => ⟨⟨b, hBY hb⟩, hP (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hRp : IsPGroup 3 ↥R := (P.isPGroup').map _
  have hRc : Nat.card R = 3 ^ (Nat.card Y).factorization 3 := by
    rw [hR, Subgroup.card_map_of_injective Y.subtype_injective, Sylow.card_eq_multiplicity]
  have hRK : Nat.card ↥(R ⊓ K) = 3 ^ (Nat.card K).factorization 3 :=
    card_inf_sylow hYN hKY hRY hRp hRc
  have hRd : Nat.card ↥(R ⊓ dQ K) = 3 ^ (Nat.card (dQ K)).factorization 3 :=
    card_inf_sylow hYd hdY hRY hRp hRc
  have hcomm : ∀ r₁ ∈ R ⊓ K, ∀ r₂ ∈ R ⊓ dQ K, r₁ * r₂ = r₂ * r₁ := by
    intro r₁ h₁ r₂ h₂
    have hc : r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ R ⊓ GLAPPrimeCoreOf 3 K :=
      ⟨R.mul_mem (R.mul_mem (R.mul_mem h₁.1 h₂.1) (R.inv_mem h₁.1)) (R.inv_mem h₂.1),
        (mem_dQ.1 h₂.2).2.2 r₁ h₁.2⟩
    rw [pgroup_inf_core_eq_bot K hRp, Subgroup.mem_bot] at hc
    have : ⁅r₁, r₂⁆ = 1 := hc
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  have hsup := card_sup_sylow (p := 3) hdK hKd (inf_le_right : R ⊓ K ≤ K)
    (inf_le_right : R ⊓ dQ K ≤ dQ K) (hRp.to_inf_left) (hRp.to_inf_left) hRK hRd hcomm
  have hSTR : (R ⊓ K) ⊔ (R ⊓ dQ K) = R := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le inf_le_left inf_le_left
    · rw [hsup.2, hRc]
  refine ⟨R, hBR, hRp, hRY, hRK, hcomm, ?_, ?_, ?_⟩
  · intro r hr
    have : r ∈ (R ⊓ K) ⊔ (R ⊓ dQ K) := by rw [hSTR]; exact hr
    exact exists_mul_of_mem_sup_of_commute hcomm this
  · intro r hr
    exact mem_normalizer_inf (Subgroup.le_normalizer hr) (hYN (hRY hr))
  · intro r hr
    exact mem_normalizer_inf (Subgroup.le_normalizer hr) (hYd (hRY hr))

theorem factorization_card_quot_core (K : Subgroup G) :
    (Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K)).factorization 3 = (Nat.card K).factorization 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥K)
  have hc : Nat.card (GLAPPrimeCore 3 ↥K) = Nat.card (GLAPPrimeCoreOf 3 K) :=
    (Subgroup.card_map_of_injective K.subtype_injective).symm
  have h3 : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
  have h0 : Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h0' : Nat.card (GLAPPrimeCore 3 ↥K) ≠ 0 := Nat.card_pos.ne'
  rw [h, Nat.factorization_mul h0 h0']
  simp only [Finsupp.add_apply]
  rw [hc, Nat.factorization_eq_zero_of_not_dvd h3, add_zero]

theorem card_barX_sylow {K P : Subgroup G} (hPK : P ≤ K) (hPp : IsPGroup 3 ↥P)
    (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    Nat.card (barX 3 K P) = 3 ^ (Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K)).factorization 3 := by
  rw [card_barX_of_isPGroup Nat.prime_three hPK hPp, hPc, factorization_card_quot_core]

theorem sylow_equiv_sylowBar {K P : Subgroup G} (hPK : P ≤ K) (hPp : IsPGroup 3 ↥P)
    (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    ∃ P' : Sylow 3 (↥K ⧸ GLAPPrimeCore 3 ↥K),
      Nonempty (↥P ≃* ↥(P' : Subgroup (↥K ⧸ GLAPPrimeCore 3 ↥K))) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (P.subgroupOf K).subtype with hf
  have hfi : Function.Injective f := injective_barX_comp Nat.prime_three hPp hPK
  have hrange : f.range = barX 3 K P := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  refine ⟨Sylow.ofCard (barX 3 K P) (card_barX_sylow hPK hPp hPc), ⟨?_⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe hPK).symm.trans
    ((MonoidHom.ofInjective hfi).trans (MulEquiv.subgroupCongr hrange))

theorem mk_mem_center_iff (K : Subgroup G) (x : ↥K) :
    (QuotientGroup.mk x : ↥K ⧸ GLAPPrimeCore 3 ↥K) ∈ Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K) ↔
      (x : G) ∈ dQ K := by
  rw [mem_dQ_of_mem_normalizer (Subgroup.le_normalizer x.2), Subgroup.mem_center_iff]
  constructor
  · intro h y hy
    have h1 := h (QuotientGroup.mk ⟨y, hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem] at h1
    have h2 := (mem_coreOf_iff (p := 3) (X := K) _).2 h1
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
    group
  · intro h w
    induction w using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    apply (mem_coreOf_iff (p := 3) (X := K) _).1
    have := h y y.2
    convert this using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
    group

theorem card_sylow_inf_dQ {K P : Subgroup G} (hPK : P ≤ K) (hPp : IsPGroup 3 ↥P)
    (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    Nat.card ↥(P ⊓ dQ K) =
      3 ^ (Nat.card (Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K))).factorization 3 := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : P ⊓ dQ K ≤ K := inf_le_left.trans hPK
  set g : ↥(P ⊓ dQ K) →* ↥K ⧸ GLAPPrimeCore 3 ↥K :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hle) with hg
  have hgi : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact mk_eq_iff_of_pgroup hPp hPK a.2.1 b.2.1 hab
  have hrange : g.range = barX 3 K P ⊓ Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
    ext z
    rw [MonoidHom.mem_range, Subgroup.mem_inf, mem_barX_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨⟨a.1, hle a.2⟩, a.2.1, rfl⟩, (mk_mem_center_iff K ⟨a.1, hle a.2⟩).2 a.2.2⟩
    · rintro ⟨⟨x, hxP, rfl⟩, hz⟩
      exact ⟨⟨x.1, hxP, (mk_mem_center_iff K x).1 hz⟩, rfl⟩
  have hcard : Nat.card ↥(P ⊓ dQ K) = Nat.card ↥g.range :=
    Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv
  rw [hcard, hrange]
  have hPb : Nat.card (barX 3 K P) =
      3 ^ (Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K)).factorization 3 := card_barX_sylow hPK hPp hPc
  refine card_inf_sylow (p := 3) (N := Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K))
    (H := ⊤) (P := barX 3 K P) ?_ le_top le_top (IsPGroup.of_card hPb) ?_
  · rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
  · rw [Subgroup.card_top]; exact hPb

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
