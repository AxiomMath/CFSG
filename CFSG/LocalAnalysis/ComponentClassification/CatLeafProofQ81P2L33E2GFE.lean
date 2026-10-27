module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Tools
public import CFSG.LieType.Chevalley.OrdinaryExceptionalOuterTwoPart

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem adjoint_not_isPGroup
    {k : Type} [Field k] [Finite k] {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
    (hk : Nat.card k = 2 ^ e) :
    ¬ IsPGroup 2 (↥(adjointGroup τ k) ⧸ pPrimeCore 2 ↥(adjointGroup τ k)) := by
  have := finite_modGL (τ := τ) (K := k)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two he hk
  have h2 : 2 ∣ Nat.card (adjointGroup τ k) := by
    have h1 := card_sq_dvd_card_adjointGroup (K := k) (τ := τ)
      (by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [hk] at h1
    exact (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)).trans h1
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hDA, -, hD, hx, hx2⟩ := UnbalancedCatalog.G2_long_root_subgroup_perfect k
    refine not_isPGroup_quot_of_le hDA hD ?_
    have h := orderOf_dvd_natCard (⟨_, hx⟩ : UnbalancedCatalog.g2LongRootGroup k)
    rwa [Subgroup.orderOf_mk, hx2 (ringChar.eq k 2)] at h
  · exact not_isPGroup_quot_of_perfect
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 k).1.commutator_eq_top h2
  · exact not_isPGroup_quot_of_perfect
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k).1.commutator_eq_top h2
  · exact not_isPGroup_quot_of_perfect
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 k).1.commutator_eq_top h2
  · exact not_isPGroup_quot_of_perfect
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 k).1.commutator_eq_top h2

theorem field_not_isPGroup
    {K : Type} [Field K] [Finite K] {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    {γ : MulAut (adjointGroup τ K)}
    (hγ : ∀ u, (γ u : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K)) :
    ¬ IsPGroup 2 (↥(fixedPoints γ) ⧸ pPrimeCore 2 ↥(fixedPoints γ)) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hk := ExcSelector.card_fixSubfield_of_pow he hK hσ
  have hfix : fixedPoints γ = (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) :=
    ExcSelector.fixedSubgroup_eq_fixedFieldImage_even (by
      rcases hτ with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) (ringChar.eq K 2) σ hγ
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (fixedFieldImage_le hx).1
  have eJ : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm
  have hT := adjoint_not_isPGroup (k := fixSubfield σ) (by
    rcases hτ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) he hk
  rw [hfix]
  exact fun hP => hT (isPGroup_quot_of_equiv eJ hP)

theorem ree_not_isPGroup
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {n : ℕ}
    (hK : Nat.card K = 2 ^ (2 * n + 1)) :
    ¬ IsPGroup 2 (↥(reeFixed F4 K n) ⧸ pPrimeCore 2 ↥(reeFixed F4 K n)) := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have h4 : 4 ∣ (2 ^ (2 * n + 1)) ^ 12 := by
    rw [← pow_mul]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ ((2 * n + 1) * 12) := pow_dvd_pow 2 (by omega)
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    set D := _root_.commutator (reeFixed F4 K 0) with hD
    have hs := ExcSelector.isSimpleGroup_commutator_reeFixed_tits hK2
    have hidx := ExcSelector.index_commutator_reeFixed_tits_le hK2
    have hmul := Subgroup.card_mul_index D
    have h12 : 2 ^ 12 ∣ Nat.card D * D.index := by
      rw [hmul, ExcSelector.card_reeFixed_F4 hK]
      exact Dvd.dvd.mul_right (by norm_num) _
    have hD4 : 4 ∣ Nat.card D := by
      have hi0 : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      interval_cases h : D.index
      · rw [mul_one] at h12
        exact (by norm_num : (4 : ℕ) ∣ 2 ^ 12).trans h12
      · have h12' : 2 ^ 11 * 2 ∣ Nat.card D * 2 := by rw [← pow_succ]; exact h12
        have h11 : 2 ^ 11 ∣ Nat.card D := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h12'
        exact (by norm_num : (4 : ℕ) ∣ 2 ^ 11).trans h11
    intro hP
    exact Ree.not_isPGroup_of_perfect_equiv (F := (⊤ : Subgroup (reeFixed F4 K 0))) le_top
      (MulEquiv.refl D) (commutator_eq_top_of_simple_of_four_dvd hs hD4)
      ((by norm_num : (2 : ℕ) ∣ 4).trans hD4) (isPGroup_quot_of_equiv Subgroup.topEquiv.symm hP)
  · obtain ⟨hs, -⟩ := ExcSelector.reeFixed_F4_simple_not_smallType hn1 hK
    have hc4 : 4 ∣ Nat.card (reeFixed F4 K n) := by
      rw [ExcSelector.card_reeFixed_F4 hK]
      exact Dvd.dvd.mul_right h4 _
    exact not_isPGroup_quot_of_perfect (commutator_eq_top_of_simple_of_four_dvd hs hc4)
      ((by norm_num : (2 : ℕ) ∣ 4).trans hc4)

theorem even_GFE_not_isPGroup
    {K : Type} [Field K] [Finite K] {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (β : MulAut (adjointGroup τ K)) (hβ2 : β ^ 2 = 1) (hin : β ∉ inner (adjointGroup τ K)) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_modGL (τ := τ) (K := K)
  have hβ1 : β ≠ 1 := fun h => hin (h ▸ one_mem _)
  rcases hτ with rfl | rfl | hτ
  · rcases UnbalancedCatalog.even_G2_involution_inner_or_canonical_field (hG2 rfl) K hK β
        (orderOf_eq_prime hβ2 hβ1) with h | ⟨⟨e, he⟩, hδ⟩
    · exact absurd h hin
    have he1 : 1 ≤ e := by have := hG2 rfl; omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    set δ := iterateFrobenius K 2 (f / 2) with hδdef
    have hδc : ∀ c, δ c = c ^ 2 ^ (f / 2) := fun c => iterateFrobenius_def 2 (f / 2) c
    obtain ⟨β', ψ, hβ', hψ, -⟩ := hδ δ hδc
    set σ := ExcSelector.ringEquivOfFinite δ
    have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [ExcSelector.ringEquivOfFinite_apply, hδc, show f / 2 = e by omega]
    exact not_isPGroup_of_conj hψ (field_not_isPGroup (Or.inl rfl) he1 hK' σ hσ
      (fun u => by rw [hβ' u, ExcSelector.toRingHom_ringEquivOfFinite]))
  · have : CharP K F4.prime := inferInstanceAs (CharP K 2)
    obtain ⟨ψ, hψ, heven, hodd, -⟩ := even_F4_all_outer_involutions_canonical hf K hK β hβ2 hin
    refine not_isPGroup_of_conj hψ ?_
    obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' f
    · have hn1 : 1 ≤ n := by omega
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, hn]
      set δ := iterateFrobenius K 2 n
      have hδc : ∀ c, δ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
      set σ := ExcSelector.ringEquivOfFinite δ
      exact field_not_isPGroup (τ := .F4) (Or.inr (Or.inl rfl)) hn1 hK' σ
        (fun c => by rw [ExcSelector.ringEquivOfFinite_apply, hδc])
        (fun u => by
          have h := (heven n hn).2 δ hδc u
          rw [ExcSelector.toRingHom_ringEquivOfFinite]
          exact h)
    · have hK' : Nat.card K = 2 ^ (2 * n + 1) := by rw [hK, hn]
      rw [(hodd n hn).1]
      have hfix := ExcSelector.fixedSubgroup_finiteReeAut (K := K) n
      intro hP
      exact ree_not_isPGroup hK'
        ((congrArg (fun H : Subgroup ↥(adjointGroup F4.tag K) =>
          IsPGroup 2 (↥H ⧸ pPrimeCore 2 ↥H)) hfix).mp hP)
  · obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF β
    have hσ : Θ β = σ := hΘ β g σ hgσ
    rcases hinv β hβ2 with h1 | ⟨⟨e, he⟩, hpow⟩
    · have hker' : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
      rw [hker] at hker'
      exact absurd hker' hin
    have he1 : 1 ≤ e := by omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [← hσ, hpow c, show f / 2 = e by omega]
    obtain ⟨_, -, hdesc⟩ :=
      (even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom
        hσe).1 τ
    obtain ⟨ψ, hψ, -⟩ := (hdesc g 1).2 β
      (fun u => by rw [hgσ u, rootDiagUnit_one, mul_one, inv_one, mul_one]) (by rw [← sq, hβ2])
    refine not_isPGroup_of_conj (ψ := ψ) (γ := ψ * β * ψ⁻¹) rfl ?_
    rcases hτ with rfl | rfl
    · exact field_not_isPGroup (Or.inr (Or.inr (Or.inl rfl))) he1 hK' σ hσe hψ
    · exact field_not_isPGroup (Or.inr (Or.inr (Or.inr rfl))) he1 hK' σ hσe hψ

end CFSG.ComponentClassification.HarrisLit.L33.E2
