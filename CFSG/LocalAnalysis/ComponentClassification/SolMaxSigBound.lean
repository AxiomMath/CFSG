module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigBoundA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLiftField

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem perfectResidual_map_eq_top {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    [Group.IsPerfect Q] (f : G →* Q) (hf : Function.Surjective f) :
    (perfectResidual G).map f = ⊤ := by
  rw [(perfect_residual_transport f).1]
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  let eR : ↥f.range ≃* Q := (MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv
  have : Group.IsPerfect ↥f.range :=
    Group.IsPerfect.ofSurjective (f := eR.symm.toMonoidHom) eR.symm.surjective
  have htop : (⊤ : Subgroup ↥f.range) ≤ perfectResidual ↥f.range :=
    (perfect_residual_transport (MonoidHom.id ↥f.range)).2.2 ⊤
      (Group.IsPerfect.top_iff.mpr inferInstance)
  rw [top_le_iff.mp htop, ← MonoidHom.range_eq_map, range_subtype, hrange]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem le_add_four_of_pumped (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (htM : t ∈ normalizer (M : Set X)) (hJM : J ≤ M)
    {m : ℕ} (hm : Odd m) (hnm : n < m)
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) : m ≤ n + 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  by_contra hlt
  push Not at hlt
  have hm6 : n + 6 ≤ m := by
    obtain ⟨a, rfl⟩ := hm
    obtain ⟨b, rfl⟩ := S.pair.2.1
    omega
  obtain ⟨θ, τ, hτ2, hτc, hτJ, hτcard⟩ :=
    S.exists_perm_of_pumped hT13 hML hSch hMY hMpc htM hJM hnm eM
  set O := pPrimeCore 2 ↥M with hOdef
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set π : ↥M →* alternatingGroup (Fin m) := θ.toMonoidHom.comp (QuotientGroup.mk' O) with hπdef
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective O)
  have hπker : ∀ x, π x = 1 ↔ x ∈ O := by
    intro x
    change θ (x : ↥M ⧸ O) = 1 ↔ _
    rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff]
  have hπeq : ∀ x y, π x = π y → (x : ↥M ⧸ O) = (y : ↥M ⧸ O) := fun x y h => θ.injective h
  set c : MulAut ↥M := M.normalizerMonoidHom ⟨t, htM⟩ with hcdef
  have hcapp : ∀ x : ↥M, ((c x : ↥M) : X) = t * x * t⁻¹ := fun x => rfl
  have htt : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have hc2 : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc t * (t * (x : X) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  have hττ : τ * τ = 1 := by rw [← sq, ← hτ2, pow_orderOf_eq_one]
  obtain ⟨σ, hσA, hστ, hσ1, hσσ, hσfix, hσcard⟩ := exists_double_transposition hττ (by omega)
  set σ' : alternatingGroup (Fin m) := ⟨σ, hσA⟩ with hσ'def
  have hcommJ : ∀ x : ↥M, (x : X) ∈ J → π x * σ' = σ' * π x := by
    intro x hx
    apply Subtype.ext
    have hd : Perm.Disjoint ((π x : alternatingGroup (Fin m)) : Perm (Fin m)) σ := by
      intro ω
      by_cases h : τ ω = ω
      · exact Or.inr (hσfix ω h)
      · exact Or.inl (hτJ x hx ω h)
    exact hd.commute.eq
  obtain ⟨w₀, hw₀⟩ := hπs σ'
  have hw₀c : ((c w₀ : ↥M) : ↥M ⧸ O) = (w₀ : ↥M ⧸ O) := by
    apply hπeq
    apply Subtype.ext
    have h1 := hτc w₀
    change ((π (c w₀) : alternatingGroup (Fin m)) : Perm (Fin m)) =
      τ * ((π w₀ : alternatingGroup (Fin m)) : Perm (Fin m)) * τ⁻¹ at h1
    rw [h1, hw₀]
    change τ * σ * τ⁻¹ = σ
    rw [← hστ]
    group
  obtain ⟨w, hwc, hww⟩ := exists_fixed_of_mk_eq c hc2 hw₀c
  have hπw : π w = σ' := by
    change θ (w : ↥M ⧸ O) = σ'
    rw [hww]
    exact hw₀
  have hw2 : (w : ↥M ⧸ O) ^ 2 = 1 := by
    apply θ.injective
    rw [map_pow, map_one]
    change π w ^ 2 = 1
    rw [hπw, sq]
    exact Subtype.ext hσσ
  have hw1 : (w : ↥M ⧸ O) ≠ 1 := by
    intro h
    apply hσ1
    have h1 : π w = 1 := by
      change θ (w : ↥M ⧸ O) = 1
      rw [h, map_one]
    rw [hπw] at h1
    exact congrArg Subtype.val h1
  obtain ⟨k, hk2, hkimg⟩ := exists_involution_of_mk (N := O) hOodd hw2 hw1
  set u' : ↥M := w ^ k with hu'def
  have hu'c : c u' = u' := by rw [hu'def, map_pow, hwc]
  have hπu : π u' = σ' := by
    change θ (u' : ↥M ⧸ O) = σ'
    rw [hu'def, hkimg]
    exact hπw
  set u : X := (u' : X) with hudef
  have hu : orderOf u = 2 := by rw [hudef, Subgroup.orderOf_coe]; exact hk2
  have hut : u ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val hu'c
    rw [hcapp] at h1
    calc u * t = t * u * t⁻¹ * t := by rw [hudef, h1]
      _ = t * u := by group
  have hJn := S.centralizer_le_normalizer hT13 hML hSch hut
  have huJ : u ∈ UnbalancedLayer.coreActionKernel J := by
    refine ⟨hJn, fun j hj => ?_⟩
    have hjM := hJM hj
    set jM : ↥M := ⟨j, hjM⟩
    have hw : j⁻¹ * u⁻¹ * j * u ∈ J := by
      have h1 : u⁻¹ * j * u ∈ J := by
        have := (mem_normalizer_iff.mp (inv_mem hJn) j).mp hj
        rwa [inv_inv] at this
      have h2 : j⁻¹ * u⁻¹ * j * u = j⁻¹ * (u⁻¹ * j * u) := by group
      rw [h2]
      exact mul_mem (inv_mem hj) h1
    have hO : jM⁻¹ * u'⁻¹ * jM * u' ∈ O := by
      rw [← hπker, map_mul, map_mul, map_mul, map_inv, map_inv, hπu,
        mul_assoc _ _ σ', hcommJ jM hj]
      group
    have hwO : j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 ↥M).map M.subtype := ⟨_, hO, rfl⟩
    have hle : J ⊓ (pPrimeCore 2 ↥M).map M.subtype ≤ (pPrimeCore 2 ↥J).map J.subtype := by
      refine le_pPrimeCore_map inf_le_left ?_ ?_
      · intro g hg
        exact inf_mem_normalizer' (le_normalizer hg)
          (le_normalizer_pPrimeCore (le_normalizer (hJM hg)))
      · have h1 : Nat.card ↥(J ⊓ (pPrimeCore 2 ↥M).map M.subtype) ∣
            Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype) := card_dvd_of_le inf_le_right
        rw [card_map_of_injective M.subtype_injective] at h1
        exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    exact hle ⟨hw, hwO⟩
  set cu : MulAut ↥M := MulAut.conj u' with hcudef
  have hu'u' : u' * u' = 1 := by rw [← sq, ← hk2, pow_orderOf_eq_one]
  have hcu2 : ∀ x, cu (cu x) = x := by
    intro x
    change u' * (u' * x * u'⁻¹) * u'⁻¹ = x
    calc u' * (u' * x * u'⁻¹) * u'⁻¹ = (u' * u') * x * (u' * u')⁻¹ := by group
      _ = x := by rw [hu'u']; group
  set A' := fixAlt σ with hA'def
  set V' : Subgroup ↥M := A'.comap π ⊓ fixedSubgroup cu with hV'def
  let g : ↥V' →* ↥A' := (π.comp V'.subtype).codRestrict A' fun x => x.2.1
  have hg : Function.Surjective g := by
    rintro ⟨a, ha⟩
    obtain ⟨x₀, hx₀⟩ := hπs a
    have hac : a * σ' = σ' * a := mem_centralizer_singleton_iff.mp (fixAlt_le_centralizer hσA ha)
    have hx₀c : ((cu x₀ : ↥M) : ↥M ⧸ O) = (x₀ : ↥M ⧸ O) := by
      apply hπeq
      change π (u' * x₀ * u'⁻¹) = π x₀
      rw [map_mul, map_mul, map_inv, hπu, hx₀, ← hac]
      group
    obtain ⟨x, hxc, hxx⟩ := exists_fixed_of_mk_eq cu hcu2 hx₀c
    have hπx : π x = a := by
      change θ (x : ↥M ⧸ O) = a
      rw [hxx]
      exact hx₀
    refine ⟨⟨x, ?_, hxc⟩, Subtype.ext hπx⟩
    change π x ∈ A'
    rw [hπx]
    exact ha
  have hcardc : Nat.card ↥(σ.supportᶜ : Finset (Fin m)) = m - 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      hσcard]
  have : Nontrivial ↥(σ.supportᶜ : Finset (Fin m)) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have : IsSimpleGroup (alternatingGroup ↥(σ.supportᶜ : Finset (Fin m))) :=
    alternatingGroup.isSimpleGroup (by omega)
  have : IsSimpleGroup ↥A' := MulEquiv.isSimpleGroup (fixAltEquiv σ).symm
  have hA'na : ∃ a b : ↥A', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt_nonabelian_of_card (Ω := ↥(σ.supportᶜ : Finset (Fin m)))
      (by omega)
    refine ⟨fixAltEquiv σ a, fixAltEquiv σ b, fun h => hab ?_⟩
    apply (fixAltEquiv σ).injective
    rw [map_mul, map_mul, h]
  have hA'q := LocalCores.isQuasisimple_of_isSimpleGroup hA'na
  have : Group.IsPerfect ↥A' := hA'q.1.1
  have hA'card : Nat.card ↥A' = Nat.card (alternatingGroup (Fin (m - 4))) := by
    rw [← Nat.card_congr (fixAltEquiv σ).toEquiv, nat_card_alternatingGroup, hcardc,
      card_of_mulEquiv_alt (by omega) (MulEquiv.refl _)]
  have hAlt := (factorization_two_card_alt (n := n) (m := m - 4) (by omega) (by omega)).2
    S.pair.2.1 (by omega)
  have hA'even : Even (Nat.card ↥A') := by
    rw [hA'card]
    apply even_iff_two_dvd.mpr
    by_contra h2
    have := Nat.factorization_eq_zero_of_not_dvd h2
    omega
  set R := perfectResidual ↥V' with hRdef
  have hgR : R.map g = ⊤ := perfectResidual_map_eq_top g hg
  let fR : ↥R →* ↥A' := g.comp R.subtype
  have hfR : Function.Surjective fR := by
    intro a
    have ha : a ∈ R.map g := by rw [hgR]; exact mem_top a
    obtain ⟨r, hr, rfl⟩ := ha
    exact ⟨⟨r, hr⟩, rfl⟩
  have hfRk : Odd (Nat.card fR.ker) := by
    let h : fR.ker →* O := ((V'.subtype.comp R.subtype).comp fR.ker.subtype).codRestrict O
      fun k => by
        have h1 : fR (k : ↥R) = 1 := k.2
        exact (hπker _).mp (congrArg Subtype.val h1)
    have hh : Function.Injective h := fun k₁ k₂ h' => by
      have h'' := congrArg (fun x : O => (x : ↥M)) h'
      exact Subtype.ext (Subtype.ext (Subtype.ext h''))
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective h hh)
  have hRO := pPrimeCore_eq_ker fR hfR hfRk hA'even
  let eR : ↥R ⧸ pPrimeCore 2 ↥R ≃* ↥A' :=
    (QuotientGroup.quotientMulEquivOfEq hRO).trans
      (QuotientGroup.quotientKerEquivOfSurjective fR hfR)
  have hRq : IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R) :=
    LocalCores.isQuasisimple_of_mulEquiv eR.symm hA'q.1
  have hRperf : Group.IsPerfect ↥R := perfect_residual_characterization.2.2.1
  set L := (R.map V'.subtype).map M.subtype with hLdef
  let eL : ↥R ≃* ↥L := (R.equivMapOfInjective V'.subtype V'.subtype_injective).trans
    ((R.map V'.subtype).equivMapOfInjective M.subtype M.subtype_injective)
  have hLperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
    exact (Subgroup.isPerfect_iff).mp this
  have hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    LocalCores.isQuasisimple_of_mulEquiv (Sol78.coreQuotCongr eL) hRq
  have hLu : L ≤ centralizer ({u} : Set X) := by
    rintro _ ⟨_, ⟨r, -, rfl⟩, rfl⟩
    have h1 : cu (r : ↥M) = r := (r : ↥V').2.2
    have h2 := congrArg Subtype.val h1
    change u * ((r : ↥M) : X) * u⁻¹ = (r : ↥M) at h2
    rw [mem_centralizer_singleton_iff]
    calc ((r : ↥M) : X) * u = u * (r : ↥M) * u⁻¹ * u := by rw [h2]
      _ = u * (r : ↥M) := by group
  have hu2 : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨hJuJ, hJuu, hJuC, -⟩ := S.fixedLayer_facts hu2 hut huJ
  set Ju := GSLit.fixedLayer J (zpowers u) with hJudef
  have hJuM : Ju ≤ M := hJuJ.trans hJM
  have hJuL : Ju ≤ L := by
    have hJuV : Ju.subgroupOf M ≤ V' := by
      intro x hx
      have hxJ : (x : X) ∈ J := hJuJ hx
      have hxu : (x : X) ∈ centralizer ({u} : Set X) := hJuu hx
      refine ⟨?_, ?_⟩
      · change π x ∈ fixAlt σ
        rw [mem_fixAlt]
        intro ω hω
        rw [Finset.mem_compl, Perm.notMem_support]
        rw [Perm.mem_support] at hω
        by_contra hσω
        exact hω (hτJ x hxJ ω fun h => hσω (hσfix ω h))
      · apply Subtype.ext
        change u * (x : X) * u⁻¹ = x
        rw [← mem_centralizer_singleton_iff.mp hxu]
        group
    have hJup : Group.IsPerfect ↥(Ju.subgroupOf M) := by
      have : Group.IsPerfect ↥Ju := (Subgroup.isPerfect_iff).mpr
        (UnbalancedCorr.commutator_eq_of_isPComponent hJuC.1 hJuC.2)
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJuM).symm.toMonoidHom)
        (subgroupOfEquivOfLe hJuM).symm.surjective
    have h1 := HarrisLit.le_perfectResidual_map hJuV hJup
    intro x hx
    obtain ⟨r, hr, hrx⟩ := h1 (show (⟨x, hJuM hx⟩ : ↥M) ∈ Ju.subgroupOf M from hx)
    exact ⟨_, ⟨r, hr, rfl⟩, by rw [hrx]; rfl⟩
  have hkey := S.factorization_two_le hT13 hML hSch hu hut huJ hLu hLperf hLq hJuL
  have hJ := factorization_two_eq_of_coreQuot e
  have hdvd : Nat.card ↥A' ∣ Nat.card ↥L := by
    rw [← Nat.card_congr eL.toEquiv, ← Subgroup.card_top (G := ↥A'),
      ← (MonoidHom.range_eq_top.mpr hfR), MonoidHom.range_eq_map]
    have h3 := (⊤ : Subgroup ↥R).card_map_dvd fR
    rwa [Subgroup.card_top] at h3
  have h2 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvd 2
  rw [hA'card] at h2
  omega

end Sig36

end CFSG.ComponentClassification.SolMax
