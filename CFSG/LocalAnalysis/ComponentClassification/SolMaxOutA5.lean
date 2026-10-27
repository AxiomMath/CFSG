module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutLoc
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveP
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem false_of_conjugate_outside_of_five (S : Sig36 X t J n e E D)
    (hD2 : SignalizerConjKernelExclusion) (hn : 11 ≤ n)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {Q : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
      normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) {a g : X}
    (ha : a ∈ Q) (hgH : g ∉ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hsNQ : g⁻¹ * a * g ∈ normalizer (Q : Set X))
    (hσ2 : ρ ⟨g⁻¹ * a * g, hHN hs⟩ * ρ ⟨g⁻¹ * a * g, hHN hs⟩ = 1)
    (hσ1 : ρ ⟨g⁻¹ * a * g, hHN hs⟩ ≠ 1) {x : X} (hxM : x ∈ M)
    (hxo : x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X))) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, le_normalizer hxM⟩).support.card = 4)
    (hx' : g * x * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (h5 : 5 ≤ n - (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hs2 := S.mul_self_eq_one_of_conjugate hD2 hMH hMpc hHN hsup hρ hQK hQ2 hQcard hA hNT ha hs
    hsNQ hσ2 hσ1
  have hsN : g⁻¹ * a * g ∈ normalizer (M : Set X) := hHN hs
  have hso : orderOf (g⁻¹ * a * g) = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact hs2) fun h => hσ1 ?_
    have h1 : (⟨g⁻¹ * a * g, hHN hs⟩ : ↥(normalizer (M : Set X))) = 1 := Subtype.ext h
    rw [h1, map_one]
  have haH : a ∈ H := (hQK ha).1
  have haK : a ∈ UnbalancedLayer.coreActionKernel M := (hQK ha).2
  have ha2 : IsPGroup 2 (zpowers a) := hQ2.to_le (zpowers_le.mpr ha)
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hσ1
    have h1 : (⟨g⁻¹ * 1 * g, hHN hs⟩ : ↥(normalizer (M : Set X))) = 1 :=
      Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
    rw [h1, map_one]
  have hCa : centralizer ({a} : Set X) ≤ H := by
    have hNa := hNT _ (zpowers_le.mpr ha) (fun h => ha1 (zpowers_eq_bot.mp h))
    intro z hz
    apply hNa
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq']
    exact hz
  obtain ⟨La, hLaM, hLaC, hLapc, -, ⟨θLa, hθLa⟩, hLaN⟩ :=
    exists_layer_of_kernel hMH hMpc θ haH haK ha2 hCa
  have hxs : x * (g⁻¹ * a * g) = g⁻¹ * a * g * x :=
    mem_centralizer_singleton_iff.mp (oddGen_le _ hxo)
  have hx'N : g * x * g⁻¹ ∈ normalizer (M : Set X) := hHN hx'
  have h5' : 5 ≤ n - (ρ ⟨g * x * g⁻¹, hx'N⟩).support.card := h5
  have hx'a : g * x * g⁻¹ * a = a * (g * x * g⁻¹) := by
    calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g * x) * g⁻¹ := by rw [hxs]
      _ = a * (g * x * g⁻¹) := by group
  have hx'o : g * x * g⁻¹ ∈ oddGen (centralizer ({a} : Set X)) := by
    have h1 := conj_mem_oddGen_centralizer (g := g) hxo
    rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at h1
  have hx'A : ρ ⟨g * x * g⁻¹, hx'N⟩ ∈ alternatingGroup (Fin n) :=
    mem_alternatingGroup_of_mem_oddGen (ρ := ρ) (hCa.trans hHN) hx'o hx'N
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'La : g * x * g⁻¹ ∈ normalizer (La : Set X) := hLaN _ hx'N hx'a
  obtain ⟨q, hq⟩ := θLa.surjective ⟨ρ ⟨g * x * g⁻¹, hx'N⟩, hx'A⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hyM : (y : X) ∈ M := hLaM y.2
  have hρy : ρ ⟨y, le_normalizer hyM⟩ = ρ ⟨g * x * g⁻¹, hx'N⟩ := by
    rw [hρ.apply_of_mem (by omega) ⟨y, hyM⟩, ← hθLa y y.2 hyM]
    exact congrArg Subtype.val hq
  have hce : g * x * g⁻¹ * (y : X)⁻¹ ∈ UnbalancedLayer.coreActionKernel La := by
    have hmem : g * x * g⁻¹ * (y : X)⁻¹ ∈ normalizer (M : Set X) :=
      mul_mem hx'N (inv_mem (le_normalizer hyM))
    have hK : g * x * g⁻¹ * (y : X)⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
      refine hρ.mem_coreActionKernel hmem ?_
      have h1 : (⟨g * x * g⁻¹ * (y : X)⁻¹, hmem⟩ : ↥(normalizer (M : Set X))) =
          ⟨g * x * g⁻¹, hx'N⟩ * (⟨y, le_normalizer hyM⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
      rw [h1, map_mul, map_inv, hρy, mul_inv_cancel]
    exact SolMax.mem_coreActionKernel_of_le hLaM hK (mul_mem hx'La (inv_mem (le_normalizer y.2)))
  have hci : coreImage θLa y.2 = ρ ⟨g * x * g⁻¹, hx'N⟩ := by
    change ((θLa (y : ↥La ⧸ pPrimeCore 2 ↥La) : alternatingGroup (Fin n)) : Perm (Fin n)) = _
    rw [hq]
  obtain ⟨R', hR'J, hR'pc, hinvR', -, -⟩ := exists_fixed_component_of_acts hLaC hLapc θLa
    hx'La hx'2 y.2 hce (by rw [hci]; omega)
  obtain ⟨ρa, hρa⟩ := exists_isPermAction (M := La) (by omega) (by omega) θLa
  have hρax' : ρa ⟨g * x * g⁻¹, hx'La⟩ = coreImage θLa y.2 :=
    hρa.apply_eq_coreImage_of_acts (by omega) hx'La y.2 hce
  obtain ⟨δ, hδA, hδ2, hδ4, hδs, hδc⟩ := exists_four_of_fix (ρ ⟨g * x * g⁻¹, hx'N⟩) (by omega)
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hδ4
    omega
  obtain ⟨x₀, hx₀La, hx₀c, hx₀2, hρax₀⟩ := hρa.exists_involution_lift (by omega) hx'La hx'2 hδA
    hδ2 hδ1 (by rw [hρax', hci]; exact hδc)
  have hx₀M : x₀ ∈ M := hLaM hx₀La
  have hρx₀ : ρ ⟨x₀, le_normalizer hx₀M⟩ = δ := by
    rw [hρ.apply_of_mem (by omega) ⟨x₀, hx₀M⟩, ← hθLa x₀ hx₀La hx₀M, ← hρax₀]
    exact (hρa.apply_of_mem (by omega) ⟨x₀, hx₀La⟩).symm
  have hx₀4 : (ρ ⟨x₀, le_normalizer hx₀M⟩).support.card = 4 := by rw [hρx₀]; exact hδ4
  have hx₀R' : x₀ ∈ R' := by
    refine hinvR' x₀ hx₀La (mem_centralizer_singleton_iff.mp hx₀c)
      ⟨1, by rw [pow_one, sq]; exact hx₀2⟩ ?_
    have h1 : coreImage θLa hx₀La = δ := by
      rw [← hρax₀]
      exact (hρa.apply_of_mem (by omega) ⟨x₀, hx₀La⟩).symm
    rw [h1, hci]
    exact hδs
  have hCx₀ : centralizer ({x₀} : Set X) ≤ H := hA x₀ hx₀M hx₀2 hx₀4
  have hCx : centralizer ({x} : Set X) ≤ H := hA x hxM hx2 hx4
  have hR'C : R' ≤ centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X) :=
    fun z hz => mem_inf.2 ⟨hLaC (mem_inf.1 (hR'J hz)).1, (mem_inf.1 (hR'J hz)).2⟩
  have hCmap : (centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({x} : Set X) ⊓ centralizer ({g⁻¹ * a * g} : Set X) := by
    rw [map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective, map_conj_centralizer_singleton,
      map_conj_centralizer_singleton, inv_inv, inf_comm,
      show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  set R := R'.map (MulAut.conj g⁻¹).toMonoidHom with hRdef
  have hRY : R ≤ centralizer ({x} : Set X) ⊓ centralizer ({g⁻¹ * a * g} : Set X) := by
    rw [← hCmap]
    exact map_mono hR'C
  have hRpc : IsPComponent 2
      (R.subgroupOf (centralizer ({x} : Set X) ⊓ centralizer ({g⁻¹ * a * g} : Set X))) := by
    rw [← hCmap]
    exact isPComponent_map_conj hR'C hR'pc g⁻¹
  have hfR : g⁻¹ * x₀ * g ∈ R :=
    ⟨x₀, hx₀R', by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hRK : ¬ R ≤ UnbalancedLayer.coreActionKernel M := by
    intro hRK
    have hTg : (zpowers x₀).map (MulAut.conj g⁻¹).toMonoidHom ≤ R :=
      map_mono (zpowers_le.mpr hx₀R')
    exact hD2 X t J n e E D S M hMH hMpc hHN hsup θ ρ hρ x₀ hx₀M (le_normalizer hx₀M) hx₀2 hx₀4
      hCx₀ g⁻¹ (hTg.trans (hRY.trans (inf_le_left.trans hCx))) (hTg.trans hRK)
  obtain ⟨Nx, hNx, hNxpc, -, hNxsupp, ⟨θNx⟩⟩ := S.exists_fixComp_of_sup hMH hMpc hHN hρ
    (hMH hxM) hx2 hx4
  rw [inf_eq_right.mpr hCx] at hNxpc
  have hNxM : Nx ≤ M := hNx.trans inf_le_left
  have hNxC : Nx ≤ centralizer ({x} : Set X) := hNx.trans inf_le_right
  have hNxN : Nx ≤ normalizer (M : Set X) := hNxC.trans (hCx.trans hHN)
  have hNxperf : ⁅Nx, Nx⁆ = Nx := UnbalancedCorr.commutator_eq_of_isPComponent hNxC hNxpc
  have hNxK : ¬ Nx ≤ UnbalancedLayer.coreActionKernel M := by
    intro hNxK
    have hNxO : Nx ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
      mem_core_of_mem_coreActionKernel hρ (by omega) (hNxM hz) (hNxK hz)
    have h1 : Nat.card Nx ∣ Nat.card ((pPrimeCore 2 ↥M).map M.subtype) := card_dvd_of_le hNxO
    rw [card_map_of_injective M.subtype_injective] at h1
    have h2 := card_eq_of_alt (by omega) θNx
    have h3 : 2 ∣ (n - 4).factorial / 2 := by
      have h4 : (4 : ℕ).factorial ∣ (n - 4).factorial := Nat.factorial_dvd_factorial (by omega)
      have h5 : (4 : ℕ).factorial = 4 * 6 := rfl
      obtain ⟨k, hk⟩ := h4
      rw [hk, h5]
      exact ⟨6 * k, by omega⟩
    have h6 : 2 ∣ Nat.card Nx := by rw [h2]; exact Dvd.dvd.mul_right h3 _
    exact absurd (Nat.Coprime.coprime_dvd_right (h6.trans h1) pPrimeCore_coprime_card)
      (by decide)
  have hσxc : (ρ ⟨x, le_normalizer hxM⟩).support.card ≤ n := by
    have := Finset.card_le_univ (ρ ⟨x, le_normalizer hxM⟩).support
    rwa [Fintype.card_fin] at this
  obtain ⟨hsurjNx, -⟩ := hρ.image_eq_of_le hNxN (s := n - 4) (by omega) θNx hNxperf hNxK
    (Q := (fixAlt (ρ ⟨x, le_normalizer hxM⟩)).map (alternatingGroup (Fin n)).subtype)
    (le_of_eq (by rw [card_map_of_injective (alternatingGroup (Fin n)).subtype_injective,
      card_fixAlt (by omega), hx4]))
    (fun z hz => by
      obtain ⟨hzM, hzs⟩ := hNxsupp z hz
      have hzA : ρ ⟨z, hNxN hz⟩ ∈ alternatingGroup (Fin n) := by
        have h1 : ρ ⟨z, hNxN hz⟩ = ρ ⟨z, le_normalizer hzM⟩ := rfl
        rw [h1, hρ.apply_of_mem (by omega) ⟨z, hzM⟩]
        exact (θ _).2
      exact ⟨⟨_, hzA⟩, mem_fixAlt.mpr hzs, rfl⟩)
  have hNxsurj : ∀ b ∈ fixAlt (ρ ⟨x, le_normalizer hxM⟩), ∃ (z : X) (hz : z ∈ Nx),
      ρ ⟨z, (hCx.trans hHN) (hNxC hz)⟩ = (b : Perm (Fin n)) := fun b hb =>
    hsurjNx b ⟨b, hb, rfl⟩
  have hU : ∀ P : Subgroup X, P ≤ centralizer ({x} : Set X) →
      IsPComponent 2 (P.subgroupOf (centralizer ({x} : Set X))) →
      ¬ P ≤ UnbalancedLayer.coreActionKernel M → P = Nx := fun P hP hPpc hPK =>
    eq_of_isPComponent_of_four hρ (by omega) (le_normalizer hxM) hx2 hx4 (hCx.trans hHN) hNxC
      hNxpc hNxsurj hP hPpc hPK
  have hsY : g⁻¹ * a * g ∈ centralizer ({x} : Set X) :=
    mem_centralizer_singleton_iff.mpr hxs.symm
  obtain ⟨R₁, hR₁Y, hR₁pc, hRR₁, -⟩ := pump_location_in hsY hso hRY hRpc
  obtain ⟨hR₁sY, hR₁spc⟩ := isPComponent_conj hR₁Y hR₁pc hsY
  obtain ⟨hNxsY, hNxspc⟩ := isPComponent_conj hNxC hNxpc hsY
  have hNxs : Nx.map (MulAut.conj (g⁻¹ * a * g)).toMonoidHom = Nx := by
    refine hU _ hNxsY hNxspc fun h => hNxK fun z hz => ?_
    have h1 : g⁻¹ * a * g * z * (g⁻¹ * a * g)⁻¹ ∈ UnbalancedLayer.coreActionKernel M :=
      h ⟨z, hz, rfl⟩
    have h2 := UnbalancedLayer.conj_mem_coreActionKernel (inv_mem hsN) h1
    rwa [show (g⁻¹ * a * g)⁻¹ * (g⁻¹ * a * g * z * (g⁻¹ * a * g)⁻¹) * (g⁻¹ * a * g)⁻¹⁻¹ = z by
      group] at h2
  have hRNx : R ≤ Nx := by
    by_cases h1 : R₁ ≤ UnbalancedLayer.coreActionKernel M
    · by_cases h2 : R₁.map (MulAut.conj (g⁻¹ * a * g)).toMonoidHom ≤
          UnbalancedLayer.coreActionKernel M
      · exact absurd (hRR₁.trans (sup_le h1 h2)) hRK
      · have h3 := hU _ hR₁sY hR₁spc h2
        have h4 : R₁ = Nx.map (MulAut.conj (g⁻¹ * a * g)).toMonoidHom := by
          rw [← h3, map_conj_map_conj_of_mul_self hs2]
        have h5 := hRR₁
        rwa [h3, h4, hNxs, sup_idem] at h5
    · have h3 := hU _ hR₁Y hR₁pc h1
      have h5 := hRR₁
      rwa [h3, hNxs, sup_idem] at h5
  have hfM : g⁻¹ * x₀ * g ∈ M := hNxM (hRNx hfR)
  have hf2 : g⁻¹ * x₀ * g * (g⁻¹ * x₀ * g) = 1 := by
    calc g⁻¹ * x₀ * g * (g⁻¹ * x₀ * g) = g⁻¹ * (x₀ * x₀) * g := by group
      _ = 1 := by rw [hx₀2]; group
  have hx₀1 : x₀ ≠ 1 := by
    rintro rfl
    apply hδ1
    rw [← hρx₀]
    exact map_one ρ
  have hf1 : g⁻¹ * x₀ * g ≠ 1 := by
    intro h
    apply hx₀1
    calc x₀ = g * (g⁻¹ * x₀ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hx₀o : x₀ ∉ oddGen (centralizer ({x₀} : Set X)) :=
    not_mem_oddGen_of_four (le_normalizer hx₀M) hx₀2 hx₀4 (hCx₀.trans hHN)
  have hfo : g⁻¹ * x₀ * g ∉ oddGen (centralizer ({g⁻¹ * x₀ * g} : Set X)) := by
    intro h
    have h1 := conj_mem_oddGen_centralizer (g := g) h
    rw [show g * (g⁻¹ * x₀ * g) * g⁻¹ = x₀ by group] at h1
    exact hx₀o h1
  have hf4 := hρ.card_support_eq_four_of_not_mem_oddGen (by omega) hfM hf2 hf1 hfo
  have hgf : g * (g⁻¹ * x₀ * g) * g⁻¹ = x₀ := by group
  have hx'H' : g * (g⁻¹ * x₀ * g) * g⁻¹ ∈ H := by rw [hgf]; exact hMH hx₀M
  have hx'4' : (ρ ⟨g * (g⁻¹ * x₀ * g) * g⁻¹, hHN hx'H'⟩).support.card = 4 := by
    have h1 : (⟨g * (g⁻¹ * x₀ * g) * g⁻¹, hHN hx'H'⟩ : ↥(normalizer (M : Set X))) =
        ⟨x₀, le_normalizer hx₀M⟩ := Subtype.ext hgf
    rw [h1]
    exact hx₀4
  have hCx' : centralizer ({g * (g⁻¹ * x₀ * g) * g⁻¹} : Set X) ≤ H := by
    rw [hgf]
    exact hCx₀
  exact hgH (S.mem_of_conj_of_four hD2 (by omega) hMH hMpc hHN hsup hρ hA hfM hf2 hf4 hx'H'
    hx'4' hCx')

end Sig36

end CFSG.ComponentClassification.SolMax
