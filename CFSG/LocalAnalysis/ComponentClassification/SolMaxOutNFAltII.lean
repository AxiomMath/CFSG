module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFAltIIPerm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFForm

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {n : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

theorem exists_alt_of_four_fix [Finite X] (hn : 11 ≤ n) {H : Subgroup X} (hMH : M ≤ H)
    (hMpc : IsPComponent 2 (M.subgroupOf H)) (hHN : H ≤ normalizer (M : Set X))
    (hρ : IsPermAction θ ρ) {Q : Subgroup X} (hQK : Q ≤ H ⊓ UnbalancedLayer.coreActionKernel M)
    (hQ2 : IsPGroup 2 Q)
    (hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ → normalizer (T : Set X) ≤ H) {a g : X}
    (ha : a ∈ Q) (ha1 : a ≠ 1) (hs : g⁻¹ * a * g ∈ H)
    (hs2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1) {x : X} (hxM : x ∈ M)
    (hxo : x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X))) (hx2 : x * x = 1)
    (hxf : FourForm (ρ ⟨g⁻¹ * a * g, hHN hs⟩) (ρ ⟨x, le_normalizer hxM⟩))
    (hx'M : g * x * g⁻¹ ∉ M) (h10 : 10 ≤ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card) :
    ∃ (T : Subgroup X) (r : ℕ), 5 ≤ r ∧
      T ≤ centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) ∧
      ∃ f : ↥T →* alternatingGroup (Fin r), Function.Surjective f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := g⁻¹ * a * g with hsdef
  have hsN : s ∈ normalizer (M : Set X) := hHN hs
  set σ := ρ ⟨s, hsN⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul, show (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) * ⟨s, hsN⟩ = 1 from
      Subtype.ext hs2, map_one]
  obtain ⟨i₀, hi₀, i₁, hi₁, h10', h1σ0, hδ⟩ : ∃ i ∈ σ.support, ∃ i' ∈ σ.support, i' ≠ i ∧
      i' ≠ σ i ∧ ρ ⟨x, le_normalizer hxM⟩ = swap i (σ i) * swap i' (σ i') := by
    rcases hxf with ⟨-, h⟩ | ⟨h6, -⟩
    · exact h
    · omega
  have haH : a ∈ H := (hQK ha).1
  have haK : a ∈ UnbalancedLayer.coreActionKernel M := (hQK ha).2
  have ha2 : IsPGroup 2 (zpowers a) := hQ2.to_le (zpowers_le.mpr ha)
  have hCa : centralizer ({a} : Set X) ≤ H := by
    have hNa := hNT _ (zpowers_le.mpr ha) (fun h => ha1 (zpowers_eq_bot.mp h))
    intro z hz
    apply hNa
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq']
    exact hz
  obtain ⟨La, hLaM, hLaC, -, -, ⟨θLa, hθLa⟩, hLaN⟩ :=
    exists_layer_of_kernel hMH hMpc θ haH haK ha2 hCa
  have hgs : g * s * g⁻¹ = a := by rw [hsdef]; group
  have hconjN : ∀ z ∈ oddGen (centralizer ({s} : Set X)),
      g * z * g⁻¹ ∈ oddGen (centralizer ({a} : Set X)) ∧
        g * z * g⁻¹ ∈ normalizer (La : Set X) := by
    intro z hz
    have h1 := conj_mem_oddGen_centralizer (g := g) hz
    rw [hgs] at h1
    refine ⟨h1, hLaN _ (hHN (hCa (oddGen_le _ h1))) ?_⟩
    exact mem_centralizer_singleton_iff.mp (oddGen_le _ h1)
  set ιM : ↥M →* Perm (Fin n) := ρ.comp (inclusion le_normalizer) with hιMdef
  have hιM : ∀ m : ↥M, ιM m = ρ ⟨m, le_normalizer m.2⟩ := fun _ => rfl
  set PM : Subgroup ↥M := (oddCentGen σ).comap ιM ⊓
    (oddGen (centralizer ({s} : Set X))).subgroupOf M with hPMdef
  set ρP : ↥PM →* ↥(oddCentGen σ) :=
    (ιM.comp PM.subtype).codRestrict _ (fun z => (mem_inf.mp z.2).1) with hρPdef
  have hρP : ∀ z : ↥PM, ((ρP z : ↥(oddCentGen σ)) : Perm (Fin n)) =
      ρ ⟨((z : ↥M) : X), le_normalizer (z : ↥M).2⟩ := fun _ => rfl
  have hρPs : Function.Surjective ρP := by
    rintro ⟨π, hπ⟩
    obtain ⟨q, hq, hqo, hρq⟩ := hρ.exists_lift_oddCentGen (by omega) hsN hs2 hπ
    refine ⟨⟨⟨q, hq⟩, mem_inf.mpr ⟨?_, hqo⟩⟩, Subtype.ext ?_⟩
    · change ιM ⟨q, hq⟩ ∈ oddCentGen σ
      rw [hιM]
      rw [hρq]
      exact hπ
    · rw [hρP]
      exact hρq
  have hLan : (La.subgroupOf (normalizer (La : Set X))).Normal := normal_in_normalizer
  set φc : ↥PM →* X :=
    (MulAut.conj g).toMonoidHom.comp (M.subtype.comp PM.subtype) with hφcdef
  have hφc : ∀ z : ↥PM, φc z = g * ((z : ↥M) : X) * g⁻¹ := fun _ => rfl
  have hφcN : ∀ z : ↥PM, φc z ∈ normalizer (La : Set X) := fun z => by
    rw [hφc]
    exact (hconjN _ (mem_inf.mp z.2).2).2
  set ψ : ↥PM →* ↥(normalizer (La : Set X)) ⧸ La.subgroupOf (normalizer (La : Set X)) :=
    (QuotientGroup.mk' _).comp (φc.codRestrict _ hφcN) with hψdef
  have hψ : ∀ z : ↥PM, ψ z = ((⟨g * ((z : ↥M) : X) * g⁻¹, hφcN z⟩ :
      ↥(normalizer (La : Set X))) : ↥(normalizer (La : Set X)) ⧸ _) := fun _ => rfl
  have hNn : (ψ.ker.map ρP).Normal := Subgroup.Normal.map inferInstance ρP hρPs
  set κ : ↥(oddCentGen σ) →* Perm ↥σ.cycleFactorsFinset :=
    (Perm.OnCycleFactors.toPermHom σ).comp (inclusion (oddCentGen_le_centralizer σ)) with hκdef
  have hκ : ∀ w, κ w = (Perm.OnCycleFactors.toPermHom σ)
      (inclusion (oddCentGen_le_centralizer σ) w) := fun _ => rfl
  by_cases hNb : ∀ w ∈ ψ.ker.map ρP, κ w = 1
  ·
    set A := alternatingGroup ↥σ.cycleFactorsFinset with hAdef
    set F₀ : ↥PM →* ↥A := (κ.codRestrict A (oddCentGen_cycleAction_mem σ)).comp ρP with hF₀def
    have hF₀ : ∀ z, ((F₀ z : ↥A) : Perm ↥σ.cycleFactorsFinset) = κ (ρP z) := fun _ => rfl
    have hle : ψ.ker ≤ F₀.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hF₀]
      exact hNb _ ⟨z, hz, rfl⟩
    set F₁ := QuotientGroup.lift ψ.ker F₀ hle with hF₁def
    set F₂ : ↥ψ.range →* ↥A :=
      F₁.comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom with hF₂def
    have hF₂ : ∀ z : ↥PM, F₂ (ψ.rangeRestrict z) = F₀ z := by
      intro z
      have h1 : (QuotientGroup.quotientKerEquivRange ψ).symm (ψ.rangeRestrict z) =
          (z : ↥PM ⧸ ψ.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      change F₁ ((QuotientGroup.quotientKerEquivRange ψ).symm (ψ.rangeRestrict z)) = F₀ z
      rw [h1, hF₁def, QuotientGroup.lift_mk]
    have hle₀ : centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) ≤
        normalizer (La : Set X) := fun z hz =>
      hLaN z (hHN (mem_inf.mp (mem_inf.mp hz).2).1)
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hz).1)
    set φ₀ : ↥(centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M)) →*
        ↥(normalizer (La : Set X)) ⧸ La.subgroupOf (normalizer (La : Set X)) :=
      (QuotientGroup.mk' _).comp (inclusion hle₀) with hφ₀def
    set T₀ := ψ.range.comap φ₀ with hT₀def
    set T := T₀.map (centralizer ({a} : Set X) ⊓
      (H ⊓ UnbalancedLayer.coreActionKernel M)).subtype with hTdef
    set eT : ↥T₀ ≃* ↥T := T₀.equivMapOfInjective _ (subtype_injective _) with heTdef
    set φT : ↥T₀ →* ↥ψ.range := (φ₀.comp T₀.subtype).codRestrict _ (fun u => u.2) with hφTdef
    have hcard : Fintype.card ↥σ.cycleFactorsFinset = σ.cycleFactorsFinset.card :=
      Fintype.card_coe _
    have hcard5 : 5 ≤ Fintype.card ↥σ.cycleFactorsFinset := by
      rw [hcard]
      have := two_mul_card_cycleFactorsFinset hσ2
      omega
    set e𝒞 := (Fintype.equivFin ↥σ.cycleFactorsFinset).altCongrHom with he𝒞def
    refine ⟨T, Fintype.card ↥σ.cycleFactorsFinset, hcard5, map_subtype_le _,
      e𝒞.toMonoidHom.comp ((F₂.comp φT).comp eT.symm.toMonoidHom), ?_⟩
    intro π'
    obtain ⟨w, hw⟩ := exists_oddCentGen_cycleAction_eq hσ2 (e𝒞.symm π').2
    obtain ⟨z, hz⟩ := hρPs w
    obtain ⟨l, hl, u, hu, hlu⟩ := hρ.exists_mul_of_mem_oddGen_centralizer (by omega) hHN hCa hLaM
      hLaC θLa hθLa hLaN (hconjN _ (mem_inf.mp z.2).2).1
    have huK := oddGen_le _ hu
    have hφ₀u : φ₀ ⟨u, huK⟩ = ψ z := by
      rw [hψ, hφ₀def, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        mem_subgroupOf]
      change u⁻¹ * (g * ((z : ↥M) : X) * g⁻¹) ∈ La
      rw [show g * ((z : ↥M) : X) * g⁻¹ = l * u from hlu]
      have h1 : u⁻¹ * (l * u) = u⁻¹ * l * u := by group
      rw [h1]
      have h2 := (mem_normalizer_iff.mp (inv_mem (hle₀ huK)) l).mp hl
      rwa [inv_inv] at h2
    have huT₀ : (⟨u, huK⟩ : ↥(centralizer ({a} : Set X) ⊓
        (H ⊓ UnbalancedLayer.coreActionKernel M))) ∈ T₀ := by
      change φ₀ ⟨u, huK⟩ ∈ ψ.range
      rw [hφ₀u]
      exact ⟨z, rfl⟩
    refine ⟨eT ⟨⟨u, huK⟩, huT₀⟩, ?_⟩
    change e𝒞 (F₂ (φT (eT.symm (eT ⟨⟨u, huK⟩, huT₀⟩)))) = π'
    rw [MulEquiv.symm_apply_apply]
    have h2 : φT ⟨⟨u, huK⟩, huT₀⟩ = ψ.rangeRestrict z := Subtype.ext hφ₀u
    rw [h2, hF₂]
    apply e𝒞.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    rw [hF₀, hz]
    exact hw
  ·
    exfalso
    push Not at hNb
    obtain ⟨w₀, hw₀N, hw₀⟩ := exists_mem_of_normal_oddCentGen hσ2 h10 hNn
      (by obtain ⟨w, hw, hne⟩ := hNb; exact ⟨w, hw, hne⟩) hi₀ hi₁ h10' h1σ0
    obtain ⟨x₀, hx₀, hx₀w⟩ := hw₀N
    have hxδ : ρ ⟨x, le_normalizer hxM⟩ ∈ oddCentGen σ := by
      rw [hδ, ← hw₀]
      exact w₀.2
    set xP : ↥PM := ⟨⟨x, hxM⟩, mem_inf.mpr ⟨hxδ, hxo⟩⟩ with hxPdef
    have hρ1 : ρP (xP * x₀⁻¹) = 1 := by
      rw [map_mul, map_inv, hx₀w]
      apply mul_inv_eq_one.mpr
      apply Subtype.ext
      rw [hρP, hw₀, ← hδ]
    have hcore : (((xP * x₀⁻¹ : ↥PM) : ↥M) : X) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      refine mem_core_of_mem_coreActionKernel hρ (by omega) ((xP * x₀⁻¹ : ↥PM) : ↥M).2
        (hρ.mem_coreActionKernel (le_normalizer ((xP * x₀⁻¹ : ↥PM) : ↥M).2) ?_)
      have h1 := congrArg Subtype.val hρ1
      rw [hρP] at h1
      exact h1
    have hodd : Odd (orderOf (xP * x₀⁻¹)) := by
      have h1 := odd_orderOf_of_mem_oddCoreIn hcore
      rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at h1
    have hψx : ψ xP = ψ (xP * x₀⁻¹) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hx₀, inv_one, mul_one]
    have hψodd : Odd (orderOf (ψ xP)) := by
      rw [hψx]
      exact hodd.of_dvd_nat (orderOf_map_dvd _ _)
    have hψ2 : ψ xP ^ 2 = 1 := by
      have h1 : xP ^ 2 = 1 := by
        rw [sq]
        apply Subtype.ext
        apply Subtype.ext
        exact hx2
      rw [← map_pow, h1, map_one]
    have hψ1 : ψ xP = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hψ2
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hψodd
        exact absurd hψodd (by decide)
    apply hx'M
    rw [hψ, QuotientGroup.eq_one_iff, mem_subgroupOf] at hψ1
    exact hLaM hψ1

end CFSG.ComponentClassification.SolMax
