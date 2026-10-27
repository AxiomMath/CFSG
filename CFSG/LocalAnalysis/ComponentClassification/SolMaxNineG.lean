module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem exists_four_in_fiveClosure (S : Sig36 X t J n e E D) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {s z : X}
    (hsH : s ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hs2 : IsPGroup 2 (zpowers s)) (hzH : z ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hz2 : z * z = 1) (hzK : z ∈ UnbalancedLayer.coreActionKernel M) (hsz : s * z = z * s)
    (h5 : 5 ≤ n - (ρ ⟨s, hHN hsH⟩).support.card) :
    ∃ e₁ e₂ : X, e₁ ∈ fiveClosure M s z ∧ e₂ ∈ fiveClosure M s z ∧ e₁ * e₁ = 1 ∧
      e₂ * e₂ = 1 ∧ e₁ * e₂ = e₂ * e₁ ∧ ∀ y : X, y ∈ centralizer ({e₁} : Set X) →
        y ∈ centralizer ({e₂} : Set X) →
          y ∈ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set σ := ρ ⟨s, hHN hsH⟩ with hσdef
  have hfix : 4 ≤ σ.supportᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨D', hD'sub, hD'⟩ := Finset.exists_subset_card_eq hfix
  have hcardD : Fintype.card ↥D' = 4 := by rw [Fintype.card_coe, hD']
  let ψ : alternatingGroup ↥D' ≃* alternatingGroup (Fin 4) :=
    (Fintype.equivFinOfCardEq hcardD).altCongrHom
  set V : Subgroup (alternatingGroup (Fin n)) :=
    (altFourKlein.map ψ.symm.toMonoidHom).map (alternatingGroup.ofSubtype D') with hVdef
  have hVsupp : ∀ v ∈ V, ∀ ω ∉ D', (v : Perm (Fin n)) ω = ω := by
    rintro _ ⟨τ, -, rfl⟩ ω hω
    have h1 := (alternatingGroup.mem_range_ofSubtype_iff D' (alternatingGroup.ofSubtype D' τ)).mp
      ⟨τ, rfl⟩
    by_contra hc
    exact hω (h1 (Equiv.Perm.mem_support.mpr hc))
  have hinj : Function.Injective
      ((alternatingGroup.ofSubtype D').comp ψ.symm.toMonoidHom) :=
    alternatingGroup.ofSubtype_injective.comp ψ.symm.injective
  have hVe : V ≃* altFourKlein := by
    rw [hVdef, Subgroup.map_map]
    exact (altFourKlein.equivMapOfInjective _ hinj).symm
  have hV4 : Nat.card V = 4 := by rw [Nat.card_congr hVe.toEquiv, card_altFourKlein]
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    have hτ' : τ * τ = 1 := hτ
    rw [← map_mul, ← map_mul, hτ', map_one, map_one]
  have hVfix : ∀ v ∈ V, v ∈ fixAlt σ := by
    intro v hv
    rw [mem_fixAlt]
    intro ω hω
    have h1 : ω ∈ D' := by
      by_contra h
      exact (Equiv.Perm.mem_support.mp hω) (hVsupp v hv ω h)
    exact hD'sub h1
  set V' : Subgroup (Perm (Fin n)) := V.map (alternatingGroup (Fin n)).subtype with hV'def
  have hV'4 : Nat.card V' = 4 := by
    rw [hV'def, card_map_of_injective (alternatingGroup (Fin n)).subtype_injective, hV4]
  have hV'2 : IsPGroup 2 V' := IsPGroup.of_card (n := 2) (by rw [hV'4]; norm_num)
  have h5N : fiveClosure M s z ≤ normalizer (M : Set X) :=
    ((fiveClosure_le M s z).trans (inf_le_left.trans inf_le_left)).trans le_normalizer
  set f : ↥(fiveClosure M s z) →* Perm (Fin n) := ρ.comp (inclusion h5N) with hfdef
  have hVr : V' ≤ f.range := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hρ.fixAlt_le_image_fiveClosure (by omega) (hHN hsH) hs2 (hHN hzH) hz2
      hsz hzK h5 v (hVfix v hv)
    exact ⟨⟨w, mem_subgroupOf.mp hw⟩, hwv⟩
  have hker : Odd (Nat.card f.ker) := by
    set O : Subgroup X := (pPrimeCore 2 ↥M).map M.subtype with hOdef
    have hOodd : Odd (Nat.card O) := by
      rw [hOdef, card_map_of_injective M.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hmem : ∀ w : f.ker, ((w : ↥(fiveClosure M s z)) : X) ∈ O := by
      intro w
      have hwM : ((w : ↥(fiveClosure M s z)) : X) ∈ M :=
        ((fiveClosure_le M s z).trans (inf_le_left.trans inf_le_left)) (w : ↥(fiveClosure M s z)).2
      have hw1 : ρ ⟨_, le_normalizer hwM⟩ = 1 := w.2
      exact mem_core_of_mem_coreActionKernel hρ (by omega) hwM
        (hρ.mem_coreActionKernel (le_normalizer hwM) hw1)
    let φ : f.ker →* O :=
      { toFun := fun w => ⟨_, hmem w⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := fun a b hab => by
      have h1 : ((a : ↥(fiveClosure M s z)) : X) = ((b : ↥(fiveClosure M s z)) : X) := by
        have := congrArg (fun o : O => (o : X)) hab
        exact this
      exact Subtype.ext (Subtype.ext h1)
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective φ hφ)
  obtain ⟨P, hPV, hPinj⟩ := exists_lift_two_subgroup' f hker V' hV'2 hVr
  have hPcard : Nat.card P = 4 := by
    have h1 : Function.Injective (f.comp P.subtype) := by
      intro a b hab
      have hab' : f ((a : ↥(fiveClosure M s z)) * (b : ↥(fiveClosure M s z))⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr hab
      have := hPinj _ (mul_mem a.2 (inv_mem b.2)) hab'
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have h2 : (f.comp P.subtype).range = V' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPV]
    rw [← hV'4, ← h2]
    exact Nat.card_congr (MonoidHom.ofInjective h1).toEquiv
  set E' : Subgroup X := P.map (fiveClosure M s z).subtype with hE'def
  have hE'4 : Nat.card E' = 4 := by
    rw [hE'def, card_map_of_injective (fiveClosure M s z).subtype_injective, hPcard]
  have hfP : ∀ p ∈ P, f p ∈ V' := fun p hp => hPV ▸ mem_map_of_mem f hp
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    have h1 : f (p * p) = 1 := by
      obtain ⟨v, hv, hfv⟩ := hfP p hp
      rw [map_mul, ← hfv, ← map_mul, hVsq v hv, map_one]
    have h2 := hPinj _ (mul_mem hp hp) h1
    change ((p * p : ↥(fiveClosure M s z)) : X) = 1
    rw [h2]
    rfl
  have hE'5 : E' ≤ fiveClosure M s z := map_subtype_le P
  have hE'M : E' ≤ M := hE'5.trans ((fiveClosure_le M s z).trans (inf_le_left.trans inf_le_left))
  have hE's : ∀ x : ↥M, (x : X) ∈ E' → ∀ ω ∉ D',
      ((θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
    rintro x ⟨p, hp, hpx⟩ ω hω
    obtain ⟨v, hv, hfv⟩ := hfP p hp
    have h1 : f p = ρ ⟨x, le_normalizer x.2⟩ := by
      rw [hfdef, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext hpx
    rw [← hρ.apply_of_mem (by omega) x, ← h1, ← hfv]
    exact hVsupp v hv ω hω
  obtain ⟨θJ, hθJ⟩ := exists_coreQuot_of_sup hJM hsup θ
  obtain ⟨ε, hε⟩ := exists_equiv_of_mulEquiv_alt (Fintype.card_fin n) (Fintype.card_fin n)
    (by omega) (e.symm.trans θJ)
  set DE : Finset (Fin n) := D.map ε.toEmbedding with hDEdef
  have hDE : DE.card = 4 := by rw [hDEdef, Finset.card_map, S.card]
  have hEs : ∀ x : ↥M, (x : X) ∈ E → ∀ ω ∉ DE,
      ((θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
    intro x hxE ω hω
    have hxJ : (x : X) ∈ J := S.le hxE
    have h1 : θ (x : ↥M ⧸ pPrimeCore 2 ↥M) = θJ ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := by
      rw [hθJ]
    have h2 : θJ ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) =
        (e.symm.trans θJ) (e ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) := by
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h1, h2, hε, Equiv.permCongr_apply]
    have hω' : ε.symm ω ∉ D := by
      intro h
      apply hω
      rw [hDEdef, Finset.mem_map]
      exact ⟨ε.symm ω, h, by simp⟩
    rw [S.supp ⟨x, hxJ⟩ hxE _ hω', Equiv.apply_symm_apply]
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein S.klein
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE2 x hx
  obtain ⟨m, hmM, hm⟩ := exists_conj_four_subgroup (by omega) θ hE'M (S.le.trans hJM) hE'4 hE4
    hE'sq hEsq hD' hDE hE's hEs
  have hNE : normalizer (E : Set X) ≤ H := normalizer_le_normalizer_signalizerCompletion_self E
  have hmemE : ∀ x : X, x ∈ E ↔ m⁻¹ * x * m ∈ E' := by
    intro x
    rw [← hm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : m⁻¹ * ((MulAut.conj m).toMonoidHom y) * m = y := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [h1]
      exact hy
    · intro hx
      refine ⟨m⁻¹ * x * m, hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hNE' : ∀ g ∈ normalizer (E' : Set X), g ∈ H := by
    intro g hg
    have h1 : m * g * m⁻¹ ∈ normalizer (E : Set X) := by
      rw [mem_normalizer_iff]
      intro x
      rw [hmemE x, hmemE (m * g * m⁻¹ * x * (m * g * m⁻¹)⁻¹)]
      have h2 : m⁻¹ * (m * g * m⁻¹ * x * (m * g * m⁻¹)⁻¹) * m = g * (m⁻¹ * x * m) * g⁻¹ := by
        group
      rw [h2]
      exact mem_normalizer_iff.mp hg _
    have h2 := mul_mem (mul_mem (inv_mem (hMH hmM)) (hNE h1)) (hMH hmM)
    rwa [show m⁻¹ * (m * g * m⁻¹) * m = g by group] at h2
  have hKl : IsKleinFour ↥E' := isKleinFour_of_card hE'4 (fun x => Subtype.ext (hE'sq x x.2))
  have : Nontrivial ↥E' := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE'4]; norm_num)
  have := Fintype.ofFinite ↥E'
  obtain ⟨x₁, hx₁⟩ := exists_ne (1 : ↥E')
  obtain ⟨x₂, -, hx₂⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, x₁} : Finset ↥E')) (t := Finset.univ)
    (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hE'4]
      exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx₂
  refine ⟨x₁, x₂, hE'5 x₁.2, hE'5 x₂.2, hE'sq x₁ x₁.2, hE'sq x₂ x₂.2, ?_, ?_⟩
  · exact congrArg Subtype.val (mul_comm_of_exponent_two hKl.exponent_two x₁ x₂)
  · intro y hy₁ hy₂
    apply hNE'
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro w hw
    by_cases hw1 : (⟨w, hw⟩ : ↥E') = 1
    · rw [show w = 1 from congrArg Subtype.val hw1, one_mul, mul_one]
    by_cases hwx₁ : (⟨w, hw⟩ : ↥E') = x₁
    · rw [show w = x₁ from congrArg Subtype.val hwx₁]
      exact (mem_centralizer_singleton_iff.mp hy₁).symm
    by_cases hwx₂ : (⟨w, hw⟩ : ↥E') = x₂
    · rw [show w = x₂ from congrArg Subtype.val hwx₂]
      exact (mem_centralizer_singleton_iff.mp hy₂).symm
    have h1 := IsKleinFour.eq_mul_of_ne_all hx₁ hx₂.1 (Ne.symm hx₂.2) hw1 hwx₁ hwx₂
    have h2 : w = (x₁ : X) * x₂ := congrArg Subtype.val h1
    rw [h2]
    have h3 := mem_centralizer_singleton_iff.mp hy₁
    have h4 := mem_centralizer_singleton_iff.mp hy₂
    calc (x₁ : X) * x₂ * y = x₁ * (x₂ * y) := by group
      _ = x₁ * (y * x₂) := by rw [← h4]
      _ = (x₁ * y) * x₂ := by group
      _ = (y * x₁) * x₂ := by rw [← h3]
      _ = y * (x₁ * x₂) := by group

end Sig36

end CFSG.ComponentClassification.SolMax
