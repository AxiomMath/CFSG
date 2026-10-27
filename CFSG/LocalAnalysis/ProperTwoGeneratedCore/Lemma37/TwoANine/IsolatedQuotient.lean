module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Balance

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

section OddCoreQuotient

variable {K L : Type*} [Group K] [Group L] [Finite K]

omit [Finite K] in
theorem odd_card_comap_of_odd (f : K →* L) (hker : Odd (Nat.card f.ker)) {M : Subgroup L}
    (hM : Odd (Nat.card M)) : Odd (Nat.card (M.comap f)) := by
  set g := f.comp (M.comap f).subtype
  rw [← (g.ker).card_mul_index, Subgroup.index_ker]
  refine Odd.mul (hker.of_dvd_nat ?_) (hM.of_dvd_nat (Subgroup.card_dvd_of_le ?_))
  · rw [← MonoidHom.comap_ker]
    exact Subgroup.card_comap_dvd_of_injective _ _ (M.comap f).subtype_injective
  · rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_le f M

variable [Finite L]

theorem comap_pPrimeCore_eq (f : K →* L) (hker : Odd (Nat.card f.ker))
    (hsurj : Function.Surjective ((QuotientGroup.mk' (CFSG.pPrimeCore 2 L)).comp f)) :
    (CFSG.pPrimeCore 2 L).comap f = CFSG.pPrimeCore 2 K := by
  have hO : Odd (Nat.card (CFSG.pPrimeCore 2 L)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  refine le_antisymm (le_sSup ⟨Subgroup.Normal.comap inferInstance _,
    Nat.coprime_two_left.mpr (odd_card_comap_of_odd f hker hO)⟩) fun k hk => ?_
  set ψ := (QuotientGroup.mk' (CFSG.pPrimeCore 2 L)).comp f
  have hQ : ((CFSG.pPrimeCore 2 K).map ψ).comap (QuotientGroup.mk' (CFSG.pPrimeCore 2 L)) ≤
      CFSG.pPrimeCore 2 L := by
    refine le_sSup ⟨Subgroup.Normal.comap (Subgroup.Normal.map inferInstance _ hsurj) _,
      Nat.coprime_two_left.mpr (odd_card_comap_of_odd _ ?_ ?_)⟩
    · rwa [QuotientGroup.ker_mk']
    · exact (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card).of_dvd_nat
        (Subgroup.card_map_dvd _ _)
  exact hQ (Subgroup.mem_map_of_mem ψ hk)

theorem nonempty_mulEquiv_quotient_pPrimeCore (f : K →* L) (hker : Odd (Nat.card f.ker))
    (hsurj : Function.Surjective ((QuotientGroup.mk' (CFSG.pPrimeCore 2 L)).comp f)) :
    Nonempty (K ⧸ CFSG.pPrimeCore 2 K ≃* L ⧸ CFSG.pPrimeCore 2 L) := by
  have h : ((QuotientGroup.mk' (CFSG.pPrimeCore 2 L)).comp f).ker = CFSG.pPrimeCore 2 K := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_pPrimeCore_eq f hker hsurj]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)⟩

end OddCoreQuotient

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isCentralInvolution_map_mk {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {S : Subgroup X} {t : X} (ht : IsCentralInvolution S t) :
    IsCentralInvolution (S.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t) := by
  refine ⟨Subgroup.mem_map_of_mem _ ht.1, orderOf_mk_eq_two hN ht.2.1, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, ht.2.2 s hs]

@[expose] def centralizerMk (N : Subgroup X) [N.Normal] (t : X) :
    centralizer ({t} : Set X) →* centralizer ({QuotientGroup.mk' N t} : Set (X ⧸ N)) :=
  ((QuotientGroup.mk' N).comp (centralizer ({t} : Set X)).subtype).codRestrict _ fun c =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp c.2])

omit [Finite X] in
@[simp] theorem coe_centralizerMk_apply (N : Subgroup X) [N.Normal] (t : X)
    (c : centralizer ({t} : Set X)) : (centralizerMk N t c : X ⧸ N) = QuotientGroup.mk' N c :=
  rfl

omit [Finite X] in
theorem centralizerMk_surjective {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {t : X}
    (ht : orderOf t = 2) : Function.Surjective (centralizerMk N t) := by
  intro y
  have hy : (y : X ⧸ N) ∈ (centralizer ({t} : Set X)).map (QuotientGroup.mk' N) := by
    rw [map_centralizer_eq hN ht]
    exact y.2
  obtain ⟨c, hc, hcy⟩ := hy
  exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩

omit [Finite X] in
theorem odd_card_ker_centralizerMk {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) (t : X) :
    Odd (Nat.card (centralizerMk N t).ker) := by
  rw [← Subgroup.card_map_of_injective (centralizer ({t} : Set X)).subtype_injective]
  refine hN.of_dvd_nat (Subgroup.card_dvd_of_le ?_)
  rintro _ ⟨c, hc, rfl⟩
  have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
  rwa [coe_centralizerMk_apply, OneMemClass.coe_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h

theorem nonempty_escapingQuotient_mulEquiv_mk {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) {t : X} (ht : orderOf t = 2) :
    Nonempty (EscapingQuotient t ≃* EscapingQuotient (QuotientGroup.mk' N t)) :=
  nonempty_mulEquiv_quotient_pPrimeCore (centralizerMk N t) (odd_card_ker_centralizerMk hN t)
    ((QuotientGroup.mk'_surjective _).comp (centralizerMk_surjective hN ht))

theorem IsTwoANine.escapingQuotient_mk {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {t : X} (ht : orderOf t = 2) (hJ : IsTwoANine (EscapingQuotient t)) :
    IsTwoANine (EscapingQuotient (QuotientGroup.mk' N t)) :=
  hJ.of_mulEquiv (nonempty_escapingQuotient_mulEquiv_mk hN ht).some

omit [Finite X] in
theorem conj_eq_of_conj_mk_eq {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {S : Subgroup X} (hS : IsPGroup 2 S) {t : X} (htS : t ∈ S)
    (hbar : ∀ g : X ⧸ N, g⁻¹ * QuotientGroup.mk' N t * g ∈ S.map (QuotientGroup.mk' N) →
      g⁻¹ * QuotientGroup.mk' N t * g = QuotientGroup.mk' N t)
    {g : X} (hg : g⁻¹ * t * g ∈ S) : g⁻¹ * t * g = t := by
  have h := hbar (QuotientGroup.mk' N g) (by
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hg)
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact eq_of_mk_eq_of_isPGroup hN hS hg htS h

theorem conj_eq_of_quotient {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) (S : Sylow 2 X)
    {t : X} (ht : IsCentralInvolution (S : Subgroup X) t) (hJ : IsTwoANine (EscapingQuotient t))
    (IH : ∀ (S' : Sylow 2 (X ⧸ N)) (t' : X ⧸ N), IsCentralInvolution (S' : Subgroup (X ⧸ N)) t' →
      IsTwoANine (EscapingQuotient t') →
      ∀ g : X ⧸ N, g⁻¹ * t' * g ∈ (S' : Subgroup (X ⧸ N)) → g⁻¹ * t' * g = t')
    (g : X) (hg : g⁻¹ * t * g ∈ (S : Subgroup X)) : g⁻¹ * t * g = t := by
  refine conj_eq_of_conj_mk_eq hN S.isPGroup' ht.1 (fun g' hg' => ?_) hg
  refine IH (S.mapSurjective (QuotientGroup.mk'_surjective N)) _ ?_
    (hJ.escapingQuotient_mk hN ht.2.1) g' ?_
  · rw [Sylow.coe_mapSurjective]
    exact isCentralInvolution_map_mk hN ht
  · rwa [Sylow.coe_mapSurjective]

theorem odd_card_pPrimeCore_two : Odd (Nat.card (CFSG.pPrimeCore 2 X)) :=
  Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem card_quotient_lt {N : Subgroup X} (hN1 : N ≠ ⊥) : Nat.card (X ⧸ N) < Nat.card X := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN1
  have h2 : 0 < Nat.card (X ⧸ N) := Nat.card_pos
  nlinarith

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
