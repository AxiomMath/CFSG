module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBI

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

namespace SwapP2

theorem eq_one_of_mem_pPrimeCore_of_mul_self [Finite X] {K : Subgroup X} {x : ↥K}
    (hx : x ∈ pPrimeCore 2 ↥K) (hx2 : (x : X) * x = 1) : (x : X) = 1 := by
  have h4 : orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥K)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    apply Subtype.ext
    simp [sq, hx2]
  have h5 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥K))
  have h6 : orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥K)) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4 pPrimeCore_coprime_card) h5
  rw [orderOf_eq_one_iff] at h6
  have h7 := congrArg (fun y : ↥(pPrimeCore 2 ↥K) => ((y : ↥K) : X)) h6
  simpa using h7

theorem rhoZ_eq_one_of_mem_coreActionKernel {N : Subgroup X} {k : ℕ}
    {ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin k)}
    {ρ : ↥(normalizer (N : Set X)) →* Perm (Fin k)} (hρ : IsPermActionZ ψ ρ) (hk : 4 ≤ k)
    {g : X} (hg : g ∈ UnbalancedLayer.coreActionKernel N) : ρ ⟨g, hg.1⟩ = 1 := by
  classical
  have hc : ∀ σ ∈ fixAlt (1 : Perm (Fin k)),
      ρ ⟨g, hg.1⟩ * (σ : Perm (Fin k)) = σ * ρ ⟨g, hg.1⟩ := by
    intro σ _
    obtain ⟨q, hq⟩ := ψ.surjective σ
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hρ ⟨g, hg.1⟩ m
    have h2 : ((N.normalizerMonoidHom ⟨g, hg.1⟩ m : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) =
        (m : ↥N ⧸ Open.fusionZStar ↥N) := by
      rw [QuotientGroup.eq]
      apply Sol78.pPrimeCore_le_fusionZStar
      have h3 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hg)).2 m m.2
      rw [inv_inv] at h3
      obtain ⟨w, hw, hwm⟩ := h3
      have hwm' : ((w : ↥N) : X) = (m : X)⁻¹ * g * m * g⁻¹ := hwm
      have h4 : (N.normalizerMonoidHom ⟨g, hg.1⟩ m)⁻¹ * m = w⁻¹ := by
        apply Subtype.ext
        change (g * m * g⁻¹)⁻¹ * m = ((w : ↥N) : X)⁻¹
        rw [hwm']
        group
      rw [h4]
      exact inv_mem hw
    rw [h2, hq] at h1
    calc ρ ⟨g, hg.1⟩ * σ = (ρ ⟨g, hg.1⟩ * σ * (ρ ⟨g, hg.1⟩)⁻¹) * ρ ⟨g, hg.1⟩ := by group
      _ = σ * ρ ⟨g, hg.1⟩ := by rw [← h1]
  refine Perm.ext fun ω => ?_
  rw [Perm.one_apply]
  exact apply_eq_of_commute_fixAlt (by simp; omega) hc (by simp)

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

theorem not_mem_coreActionKernel_of_mem_four (hs : Setting t J n e E D M)
    (hd : Data t J n e E D M e₀ F DF r) {f : X} (hf : f ∈ F) (hf1 : f ≠ 1) :
    f ∉ UnbalancedLayer.coreActionKernel M := by
  intro hfK
  classical
  have S := hs.sig
  have hn9 := S.nine_le
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hfJ : f ∈ J := hd.FJ hf
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hd.Fk).2 f hf
  have h1 := S.card_support_rho_of_swap hs.cent hs.le hs.pc hs.swap hs.diag θ hρ hfJ hfK.1
  rw [hρ.eq_one_of_mem_coreActionKernel (by omega) hfK, Perm.support_one,
    Finset.card_empty] at h1
  have h2 : coreImage e hfJ = 1 := Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h1.symm)
  have h3 : e ((⟨f, hfJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := Subtype.ext h2
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact hf1 (eq_one_of_mem_pPrimeCore_of_mul_self (x := ⟨f, hfJ⟩) h3 hf2)

theorem le_of_diagonalZ' (hs : Setting t J n e E D M) (hn : 9 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (n - 4)))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N : Subgroup X} (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N ⊔ conjBy N e₀) (hdiag : conjBy N e₀ ≠ N)
    (ψN : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin (n - 4))) : N ≤ Hn E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  set Ar := fixA M e₀ r with hArdef
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  obtain ⟨hNxC, hNxpc⟩ := isPComponent_conj hNC hNpc he₀r
  have hNxK : conjBy N e₀ ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNxC hNpc hNxpc (Ne.symm hdiag)
  set Y := N ⊔ conjBy N e₀ with hYdef
  have hYN : Y ≤ normalizer (N : Set X) := sup_le le_normalizer (fun z hz => (hNxK hz).1)
  have hArN : Ar ≤ normalizer (N : Set X) := hcov.trans hYN
  have hArM : Ar ≤ M :=
    ((GSLit.fixedLayer_le_inf _ (zpowers r)).trans inf_le_left).trans
      ((GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left)
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  have hArperf : ⁅Ar, Ar⁆ = Ar := UnbalancedCorr.commutator_eq_of_isPComponent hArle hArpc
  have hn9 := S.nine_le
  have hk6 : n - 4 ≠ 6 := by
    obtain ⟨b, hb⟩ := S.pair.2.1
    omega
  obtain ⟨ρ, hρ, hsurj, -, hρker⟩ := exists_permActionZ_of_diagonal (by omega) hk6 he₀r hArle
    hArpc χr hNC hNpc hcov hdiag ψN hArN
  have hYC : Y ≤ centralizer ({r} : Set X) := sup_le hNC hNxC
  have hYsub : (Y.subgroupOf (centralizer ({r} : Set X))).IsSubnormal := by
    rw [hYdef, subgroupOf_sup hNC hNxC]
    exact CFSG.GroupTheory.isSubnormal_sup hNpc.choose_spec.2.1 hNxpc.choose_spec.2.1
  have hOY : (pPrimeCore 2 ↥Y).map Y.subtype ≤ Hn E :=
    (pPrimeCore_map_le_of_isSubnormal hYC hYsub).trans hOr
  have hON : (pPrimeCore 2 ↥N).map N.subtype ≤ (pPrimeCore 2 ↥Y).map Y.subtype := by
    refine le_pPrimeCore_map ((map_subtype_le _).trans le_sup_left) (sup_le ?_ ?_) ?_
    · exact fun y hy => le_normalizer_pPrimeCore (le_normalizer hy)
    · exact fun y hy => le_normalizer_pPrimeCore (hNxK hy).1
    · rw [card_map_of_injective N.subtype_injective]
      exact pPrimeCore_coprime_card
  have hOYodd : Odd (Nat.card ↥((pPrimeCore 2 ↥Y).map Y.subtype)) := by
    rw [card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcc : (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom = N :=
    conjBy_conjBy_of_mul_self N he₀2
  have hcovx : Ar ≤ conjBy N e₀ ⊔ (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom := by
    rw [hcc, sup_comm]
    exact hcov
  have hdiagx : (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom ≠ conjBy N e₀ := by
    rw [hcc]
    exact Ne.symm hdiag
  let ψNx : ↥(conjBy N e₀) ⧸ Open.fusionZStar ↥(conjBy N e₀) ≃*
      alternatingGroup (Fin (n - 4)) :=
    (Sol78.fusionZStarQuotCongr (N.equivMapOfInjective (MulAut.conj e₀).toMonoidHom
      (MulAut.conj e₀).injective)).symm.trans ψN
  have hK : ∀ B : Subgroup X, B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) →
      IsPComponent 2 (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) →
      (∀ x ∈ B, ∀ z ∈ Ar, x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥Ar).map Ar.subtype) →
      B ≤ UnbalancedLayer.coreActionKernel N ∧
        B ≤ UnbalancedLayer.coreActionKernel (conjBy N e₀) := fun B hBC hBpc hBA =>
    ⟨le_coreActionKernel_of_commute_pumpZ (by omega) hk6 he₀r he₀o hArle hArpc χr hBC hBpc hBA
        hNC hNpc hcov hdiag ψN,
      le_coreActionKernel_of_commute_pumpZ (by omega) hk6 he₀r he₀o hArle hArpc χr hBC hBpc hBA
        hNxC hNxpc hcovx hdiagx ψNx⟩
  obtain ⟨f, -, -, hfF, -, -, hf1, -, -, -, -, -⟩ := exists_three_of_klein hd.Fk
  obtain ⟨a, ha, ha2, hfaY, hfaM⟩ :=
    exists_side_involution hs hn hd he₀H hNC hNpc hK f hfF
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hd.Fk).2 f hfF
  have haY : a ∈ Y := hcov ha
  have hfNY : f ∈ normalizer (Y : Set X) := by
    rw [show f = (f * a⁻¹) * a by group]
    exact mul_mem hfaY.1 (le_normalizer haY)
  have hNNx : N ≤ normalizer (conjBy N e₀ : Set X) := fun z hz =>
    (GSThmB.B5a.le_coreActionKernel_of_ne hNxC hNC hNxpc hNpc hdiag hz).1
  have haY' : a ∈ ((N ⊔ conjBy N e₀ : Subgroup X) : Set X) := haY
  rw [coe_mul_of_left_le_normalizer_right N (conjBy N e₀) hNNx] at haY'
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂⟩ := haY'
  set c : ↥N := ⟨a₁, ha₁⟩ with hcdef
  have hca : a * c * a⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥N).map N.subtype := by
    have hw := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem (hNxK ha₂))).2 a₁ ha₁
    rw [inv_inv] at hw
    have h1 := (mem_normalizer_iff.mp (le_normalizer_pPrimeCore
      (le_normalizer (mul_mem ha₁ ha₁))) _).mp hw
    rw [show a = a₁ * a₂ from ha₁₂.symm]
    rwa [show a₁ * a₁ * (a₁⁻¹ * a₂ * a₁ * a₂⁻¹) * (a₁ * a₁)⁻¹ =
      a₁ * a₂ * a₁ * (a₁ * a₂)⁻¹ * a₁⁻¹ by group] at h1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [inv_one, mul_one] at hfaM
    exact not_mem_coreActionKernel_of_mem_four hs hd hfF hf1 hfaM
  have hcZ : c ∉ Open.fusionZStar ↥N := by
    intro hcZ
    have h1 : ρ ⟨a₁, le_normalizer ha₁⟩ = 1 := by
      rw [hρ.apply_of_mem (by omega) c, (QuotientGroup.eq_one_iff c).mpr hcZ, map_one]
      rfl
    have h2 : ρ ⟨a₂, (hNxK ha₂).1⟩ = 1 := rhoZ_eq_one_of_mem_coreActionKernel hρ (by omega)
      (hNxK ha₂)
    have h3 : ρ ⟨a, hArN ha⟩ = 1 := by
      have e1 : (⟨a, hArN ha⟩ : ↥(normalizer (N : Set X))) =
          ⟨a₁, le_normalizer ha₁⟩ * ⟨a₂, (hNxK ha₂).1⟩ := Subtype.ext ha₁₂.symm
      rw [e1, map_mul, h1, h2, mul_one]
    exact ha1 (eq_one_of_mem_pPrimeCore_of_mul_self (hρker ⟨a, ha⟩ h3) ha2)
  have hcY : (c : X) ∈ Y := mem_sup_left c.2
  have hgN : f * a⁻¹ ∈ normalizer (((pPrimeCore 2 ↥Y).map Y.subtype : Subgroup X) : Set X) :=
    le_normalizer_pPrimeCore hfaY.1
  have hg1 : (f * a⁻¹) * c * (f * a⁻¹)⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hfaY)).2 (c : X)⁻¹
      (inv_mem hcY)
    rw [inv_inv, inv_inv] at h1
    have h2 := inv_mem h1
    rwa [show ((c : X) * (f * a⁻¹) * (c : X)⁻¹ * (f * a⁻¹)⁻¹)⁻¹ =
      (f * a⁻¹) * c * (f * a⁻¹)⁻¹ * (c : X)⁻¹ by group] at h2
  have hfc : f * c * f⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    have h1 := (mem_normalizer_iff.mp hgN _).mp (hON hca)
    have h2 := mul_mem h1 hg1
    rwa [show (f * a⁻¹) * (a * c * a⁻¹ * (c : X)⁻¹) * (f * a⁻¹)⁻¹ *
      ((f * a⁻¹) * c * (f * a⁻¹)⁻¹ * (c : X)⁻¹) = f * c * f⁻¹ * (c : X)⁻¹ by group] at h2
  have hfo : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hf2) hf1
  have hx : ∀ w ∈ zpowers f, w * c * w⁻¹ * (c : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have hk : f ^ k = 1 ∨ f ^ k = f := by
      rw [← zpow_mod_orderOf, hfo]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [Nat.cast_ofNat, h, zpow_zero]
      · right
        rw [Nat.cast_ofNat, h, zpow_one]
    rcases hk with h | h <;> rw [h]
    · simp
    · exact hfc
  obtain ⟨v, hv, hvf⟩ := exists_fixed_in_coset (isPGroup_zpowers_of_mul_self hf2) hOYodd
    (zpowers_le.mpr (le_normalizer_pPrimeCore hfNY))
    (le_normalizer_pPrimeCore (le_normalizer hcY)) hx
  have hcvC : (c : X) * v ∈ centralizer ({f} : Set X) := by
    have h1 := hvf f (mem_zpowers f)
    rw [mem_centralizer_singleton_iff]
    calc (c : X) * v * f = (f * ((c : X) * v) * f⁻¹) * f := by rw [h1]
      _ = f * ((c : X) * v) := by group
  have hcH : (c : X) ∈ Hn E := by
    have h3 := mul_mem (hFH f hfF hf1 hcvC) (inv_mem (hOY hv))
    rwa [mul_inv_cancel_right] at h3
  set πN : ↥N →* alternatingGroup (Fin (n - 4)) :=
    ψN.toMonoidHom.comp (QuotientGroup.mk' (Open.fusionZStar ↥N)) with hπNdef
  have hπρ : ∀ x : ↥N, ((πN x : alternatingGroup (Fin (n - 4))) : Perm (Fin (n - 4))) =
      ρ ⟨x, le_normalizer x.2⟩ := fun x => (hρ.apply_of_mem (by omega) x).symm
  set I := ((Hn E).subgroupOf N).map πN with hIdef
  have hInorm : I.Normal := by
    refine ⟨fun i hi σ => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hi
    obtain ⟨z, hz⟩ := hsurj σ
    have hzy : (z : X) * y * (z : X)⁻¹ ∈ N := (mem_normalizer_iff.mp (hArN z.2) y).mp y.2
    have hzH : (z : X) ∈ Hn E := hs.le (hArM z.2)
    refine ⟨⟨_, hzy⟩, mul_mem (mul_mem hzH hy) (inv_mem hzH), ?_⟩
    apply Subtype.ext
    have e1 : (⟨(z : X) * y * (z : X)⁻¹, le_normalizer hzy⟩ : ↥(normalizer (N : Set X))) =
        ⟨z, hArN z.2⟩ * ⟨y, le_normalizer y.2⟩ * (⟨z, hArN z.2⟩)⁻¹ := rfl
    rw [hπρ, e1, map_mul, map_mul, map_inv, hz, ← hπρ y]
    rfl
  have hIne : I ≠ ⊥ := by
    intro hI
    have h1 : πN c ∈ I := ⟨c, hcH, rfl⟩
    rw [hI, mem_bot] at h1
    apply hcZ
    change ψN ((c : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) = 1 at h1
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  have := alternatingGroup.isSimpleGroup (α := Fin (n - 4)) (by rw [Nat.card_fin]; omega)
  have hItop : I = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal I).resolve_left hIne
  exact le_of_map_fusionZStar_eq_top hN ψN
    ((pPrimeCore_le_of_isPComponent hNC hNpc).trans hOr) hItop

theorem false_of_diagonalZ' (hs : Setting t J n e E D M) (hn : 9 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (n - 4)))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N : Subgroup X} (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N ⊔ conjBy N e₀) (hdiag : conjBy N e₀ ≠ N)
    (ψN : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin (n - 4))) : False :=
  false_of_diagonal_of_le hs hd he₀H hArle hArpc hNC hNpc hcov hdiag
    (le_of_diagonalZ' hs hn hd he₀H hOr hFH χr hArle hArpc hNC hNpc hcov hdiag ψN)

end SwapP2

end CFSG.ComponentClassification.SolMax
