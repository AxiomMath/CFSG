module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11PA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFAltI

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {n : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem false_of_five_fix (S : Sig36 X t J n e E D) (hn : 11 ≤ n)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (hρ : IsPermAction θ ρ) {Q : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
      normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) {a g : X}
    (ha : a ∈ Q) (ha1 : a ≠ 1)
    (hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hs2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1) {x : X} (hxM : x ∈ M)
    (hxo : x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X))) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, le_normalizer hxM⟩).support.card = 4)
    (hxf : FourForm (ρ ⟨g⁻¹ * a * g, hHN hs⟩) (ρ ⟨x, le_normalizer hxM⟩))
    (hx' : g * x * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hx'5 : n - (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card < 5)
    (h5 : 5 ≤ n - (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card)
    (h9 : (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card < 6 →
      9 ≤ n - (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hodd : Odd n := S.pair.2.1
  set s := g⁻¹ * a * g with hsdef
  have hsN : s ∈ normalizer (M : Set X) := hHN hs
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
  obtain ⟨La, hLaM, hLaC, hLapc, -, ⟨θLa, hθLa⟩, hLaN⟩ :=
    exists_layer_of_kernel hMH hMpc θ haH haK ha2 hCa
  have hx'N : g * x * g⁻¹ ∈ normalizer (M : Set X) := hHN hx'
  have hx'o : g * x * g⁻¹ ∈ oddGen (centralizer ({a} : Set X)) := by
    have h1 := conj_mem_oddGen_centralizer (g := g) hxo
    rwa [show g * s * g⁻¹ = a by rw [hsdef]; group] at h1
  have hx'A : ρ ⟨g * x * g⁻¹, hx'N⟩ ∈ alternatingGroup (Fin n) :=
    mem_alternatingGroup_of_mem_oddGen (ρ := ρ) (hCa.trans hHN) hx'o hx'N
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'a : g * x * g⁻¹ * a = a * (g * x * g⁻¹) :=
    mem_centralizer_singleton_iff.mp (oddGen_le _ hx'o)
  have hx'La : g * x * g⁻¹ ∈ normalizer (La : Set X) := hLaN _ hx'N hx'a
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨1, le_normalizer hxM⟩ = 1 := map_one ρ
    rw [h1, Perm.support_one, Finset.card_empty] at hx4
    omega
  have hx'1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hx'o2 : orderOf (g * x * g⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact hx'2) hx'1
  have hCx : centralizer ({x} : Set X) ≤ H := hA x hxM hx2 hx4
  have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (oddGen_le _ hxo)
  set σ := ρ ⟨s, hsN⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul, show (⟨s, hsN⟩ : ↥(normalizer (M : Set X))) * ⟨s, hsN⟩ = 1 from
      Subtype.ext hs2, map_one]
  have hσev : 2 ∣ σ.support.card := Perm.two_dvd_card_support (by rw [sq]; exact hσ2)
  obtain ⟨Ms, hMsle, hMspc, hinvs, hsubPs, χs, hχs⟩ :=
    exists_fixed_component_of_perm hMH hMpc hρ hsN hs2 h5
  have hk : Fintype.card ↥(σ.supportᶜ : Finset (Fin n)) = n - σ.support.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  set θs := χs.trans (Fintype.equivFinOfCardEq hk).altCongrHom with hθsdef
  have hMsH : Ms ≤ H ⊓ centralizer ({s} : Set X) := fun z hz =>
    mem_inf.mpr ⟨hMH (mem_inf.mp (hMsle hz)).1, (mem_inf.mp (hMsle hz)).2⟩
  have hamb : H ⊓ centralizer ({s} : Set X) ⊓ centralizer ({x} : Set X) =
      centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X) := by
    ext z
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hCx h1, h2⟩, h1⟩
  have hnodd : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hσev' : σ.support.card % 2 = 0 := Nat.even_iff.mp (even_iff_two_dvd.mpr hσev)
  obtain ⟨R₀, hR₀le, hR₀pc, f, hfM, hfR₀, hf2, hf4⟩ : ∃ R₀ : Subgroup X,
      R₀ ≤ centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X) ∧
      IsPComponent 2 (R₀.subgroupOf (centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X))) ∧
      ∃ (f : X) (hfM : f ∈ M), f ∈ R₀ ∧ f * f = 1 ∧
        (ρ ⟨f, le_normalizer hfM⟩).support.card = 4 := by
    have hres := primeResidual_eq_top_of_isPComponent hMsH hMspc
    rcases hxf with ⟨h6, i, hi, i', hi', hii', hii'σ, hδ⟩ | ⟨h6, hδs⟩
    ·
      have hxD : (ρ ⟨x, le_normalizer hxM⟩).support ⊆ σ.support := by
        rw [hδ]
        intro v hv
        have h1 := Perm.support_mul_le _ _ hv
        rw [Finset.sup_eq_union, Finset.mem_union] at h1
        have hiσ : σ i ≠ i := Perm.mem_support.mp hi
        have hi'σ : σ i' ≠ i' := Perm.mem_support.mp hi'
        have hσσ : ∀ w, σ (σ w) = w := fun w => by rw [← Perm.mul_apply, hσ2, Perm.one_apply]
        rcases h1 with h1 | h1
        · rw [Perm.support_swap hiσ.symm, Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with rfl | rfl
          · exact hi
          · exact Perm.mem_support.mpr (by rw [hσσ]; exact hiσ.symm)
        · rw [Perm.support_swap hi'σ.symm, Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with rfl | rfl
          · exact hi'
          · exact Perm.mem_support.mpr (by rw [hσσ]; exact hi'σ.symm)
      obtain ⟨hxNs, hxK⟩ := mem_coreActionKernel_of_support_subset_fix hρ hMsle hres hinvs
        hsubPs χs hχs (le_normalizer hxM) hxs hxD
      have hce : x * (1 : X)⁻¹ ∈ UnbalancedLayer.coreActionKernel Ms := by
        rw [inv_one, mul_one]
        exact hxK
      obtain ⟨R₀, hR₀, hR₀pc, -, -, χ₀, hχ₀⟩ := exists_fixed_component_of_acts hMsH hMspc θs hxNs
        hx2 (one_mem Ms) hce (by
          have h1 : coreImage θs (one_mem Ms) = 1 := by
            have h2 : ((⟨1, one_mem Ms⟩ : ↥Ms) : ↥Ms ⧸ pPrimeCore 2 ↥Ms) = 1 :=
              QuotientGroup.mk_one _
            unfold coreImage
            rw [h2, map_one]
            rfl
          rw [h1, Perm.support_one, Finset.card_empty, Nat.sub_zero]
          exact h5)
      have hcard : Fintype.card ↥((coreImage θs (one_mem Ms)).supportᶜ :
          Finset (Fin (n - σ.support.card))) = n - σ.support.card := by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
        have h1 : coreImage θs (one_mem Ms) = 1 := by
          have h2 : ((⟨1, one_mem Ms⟩ : ↥Ms) : ↥Ms ⧸ pPrimeCore 2 ↥Ms) = 1 :=
            QuotientGroup.mk_one _
          unfold coreImage
          rw [h2, map_one]
          rfl
        rw [h1, Perm.support_one, Finset.card_empty, Nat.sub_zero]
      obtain ⟨f, hfR₀, hfMs, hf2, hf4⟩ := exists_four_of_layer hρ (by omega) hMsle hχs hk hR₀ hχ₀
        hcard (by omega) (by omega)
      refine ⟨R₀, ?_, ?_, f, (mem_inf.mp (hMsle hfMs)).1, hfR₀, hf2, hf4⟩
      · rw [← hamb]
        exact fun z hz => mem_inf.mpr ⟨hMsH (mem_inf.mp (hR₀ hz)).1, (mem_inf.mp (hR₀ hz)).2⟩
      · rw [← hamb]
        exact hR₀pc
    ·
      have h4s : σ.support.card ≤ 4 := by
        obtain ⟨q, hq⟩ := hσev
        omega
      have h9' := h9 h6
      have hxMs : x ∈ Ms := hinvs x hxM hxs ⟨1, by rw [pow_one, sq]; exact hx2⟩ (by
        have h1 := hρ.apply_of_mem (by omega) ⟨x, hxM⟩
        change (θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin n)).support ⊆ _
        rw [← h1]
        exact hδs)
      have hce : x * x⁻¹ ∈ UnbalancedLayer.coreActionKernel Ms := by
        rw [mul_inv_cancel]
        exact one_mem _
      have h4 : (coreImage θs hxMs).support.card = 4 := by
        unfold coreImage
        rw [hθsdef, MulEquiv.trans_apply, Equiv.altCongrHom_apply_coe,
          card_support_permCongr, ← card_support_ofSubtype, hχs ⟨x, hxMs⟩ hxM]
        unfold coreImage
        rw [← hρ.apply_of_mem (by omega) ⟨x, hxM⟩]
        exact hx4
      obtain ⟨R₀, hR₀, hR₀pc, -, -, χ₀, hχ₀⟩ := exists_fixed_component_of_acts hMsH hMspc θs
        (le_normalizer hxMs) hx2 hxMs hce (by rw [h4]; omega)
      have hcard : Fintype.card ↥((coreImage θs hxMs).supportᶜ :
          Finset (Fin (n - σ.support.card))) = n - σ.support.card - 4 := by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h4]
      obtain ⟨f, hfR₀, hfMs, hf2, hf4⟩ := exists_four_of_layer hρ (by omega) hMsle hχs hk hR₀ hχ₀
        hcard (by omega) (by omega)
      refine ⟨R₀, ?_, ?_, f, (mem_inf.mp (hMsle hfMs)).1, hfR₀, hf2, hf4⟩
      · rw [← hamb]
        exact fun z hz => mem_inf.mpr ⟨hMsH (mem_inf.mp (hR₀ hz)).1, (mem_inf.mp (hR₀ hz)).2⟩
      · rw [← hamb]
        exact hR₀pc
  have hCmap : (centralizer ({x} : Set X) ⊓ centralizer ({s} : Set X)).map
      (MulAut.conj g).toMonoidHom =
      centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X) := by
    rw [map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_centralizer_singleton,
      map_conj_centralizer_singleton, inf_comm, show g * s * g⁻¹ = a by rw [hsdef]; group]
  set T := R₀.map (MulAut.conj g).toMonoidHom with hTdef
  have hTY : T ≤ centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X) := by
    rw [← hCmap]
    exact map_mono hR₀le
  have hTpc : IsPComponent 2
      (T.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer ({g * x * g⁻¹} : Set X))) := by
    rw [← hCmap]
    exact isPComponent_map_conj hR₀le hR₀pc g
  have hx'Ca : g * x * g⁻¹ ∈ centralizer ({a} : Set X) := oddGen_le _ hx'o
  obtain ⟨M₁, hM₁Y, hM₁pc, hTM, hTpc'⟩ := pump_location_in hx'Ca hx'o2 hTY hTpc
  by_cases hM₁K : M₁ ≤ UnbalancedLayer.coreActionKernel M
  ·
    have hM₁' : M₁.map (MulAut.conj (g * x * g⁻¹)).toMonoidHom ≤
        centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzC := hM₁Y hz
      have h1 : (MulAut.conj (g * x * g⁻¹)).toMonoidHom z ∈ centralizer ({a} : Set X) :=
        mul_mem (mul_mem hx'Ca hzC) (inv_mem hx'Ca)
      refine mem_inf.mpr ⟨h1, mem_inf.mpr ⟨hCa h1, ?_⟩⟩
      exact UnbalancedLayer.conj_mem_coreActionKernel hx'N (hM₁K hz)
    have hM₁le : M₁ ≤ centralizer ({a} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      fun z hz => mem_inf.mpr ⟨hM₁Y hz, mem_inf.mpr ⟨hCa (hM₁Y hz), hM₁K hz⟩⟩
    have hT : T ≤ H ⊓ UnbalancedLayer.coreActionKernel M :=
      (hTM.trans (sup_le hM₁le hM₁')).trans inf_le_right
    have hfT : (zpowers f).map (MulAut.conj g).toMonoidHom ≤ T :=
      map_mono (zpowers_le.mpr hfR₀)
    exact S.false_of_conj_le_coreActionKernel_of_sup_zpowers h33 h35 hT13 hML hSch hMH hMpc hHN
      hsup hρ hfM (le_normalizer hfM) hf2 hf4 (hA f hfM hf2 hf4) (hfT.trans (hT.trans inf_le_left))
      (hfT.trans (hT.trans inf_le_right))
  ·
    have hLsurj : ∀ b : alternatingGroup (Fin n), ∃ (z : X) (hz : z ∈ La),
        ρ ⟨z, (hCa.trans hHN) (hLaC hz)⟩ = (b : Perm (Fin n)) := by
      intro b
      obtain ⟨q, hq⟩ := θLa.surjective b
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨l, l.2, ?_⟩
      have h1 := hρ.apply_of_mem (by omega) ⟨l, hLaM l.2⟩
      change ρ ⟨(l : X), le_normalizer (hLaM l.2)⟩ = _
      rw [h1, ← hθLa l l.2 (hLaM l.2)]
      exact congrArg Subtype.val hq
    have hM₁La := hρ.eq_of_isPComponent_of_onto (by omega) (hCa.trans hHN) hLaC hLapc hLsurj
      hM₁Y hM₁pc hM₁K
    subst hM₁La
    have hLmap : M₁.map (MulAut.conj (g * x * g⁻¹)).toMonoidHom = M₁ := by
      apply le_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact (mem_normalizer_iff.mp hx'La z).mp hz
      · intro z hz
        refine ⟨(g * x * g⁻¹)⁻¹ * z * (g * x * g⁻¹)⁻¹⁻¹,
          (mem_normalizer_iff.mp (inv_mem hx'La) z).mp hz, ?_⟩
        change g * x * g⁻¹ * ((g * x * g⁻¹)⁻¹ * z * (g * x * g⁻¹)⁻¹⁻¹) * (g * x * g⁻¹)⁻¹ = z
        group
    rw [hLmap, sup_idem] at hTM hTpc'
    have hTLY : T ≤ M₁ ⊓ centralizer ({g * x * g⁻¹} : Set X) :=
      fun z hz => mem_inf.mpr ⟨hTM hz, (mem_inf.mp (hTY hz)).2⟩
    exact hρ.not_isPComponent_layer_of_noFix (by omega) hodd (hCa.trans hHN) hLaM θLa hθLa hLaN
      hx'N hx'2 hx'a hx'A hx'5 le_rfl
      (fun z hz => mem_inf.mpr ⟨hLaC (mem_inf.mp hz).1, (mem_inf.mp hz).2⟩) hTM hTLY hTpc'

end Sig36

end CFSG.ComponentClassification.SolMax
