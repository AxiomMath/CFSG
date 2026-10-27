module

public import CFSG.LocalAnalysis.RankThreeUC.FaithfulPrimeFieldKGroupModule
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteFaithfulInvariantSubspace
public import CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedRepresentationFaithful
public import CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedFixedKernel
public import CFSG.LinearAlgebra.CoprimeActions.CoprimeIrreducibleConstituentSeparates
public import CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.IrreducibleImageReduction

open CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary

open scoped commutatorElement

open CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary in
theorem exists_image {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ρ : Representation (ZMod p) G V}
    (hS : FaithfulPrimeFieldKGroupModule G p V ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r)
    (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule (ZMod p) V))
    (Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) (hQ1 : Q ≠ ⊥) (hQq : IsPGroup q Q) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (W : Type) (_ : AddCommGroup W)
      (_ : Module (AlgebraicClosure (ZMod p)) W) (_ : FiniteDimensional (AlgebraicClosure (ZMod p)) W)
      (_ : Nontrivial W) (τ : Representation (AlgebraicClosure (ZMod p)) H W),
      Function.Injective τ ∧ τ.IsIrreducible ∧ ∃ E D' : Subgroup H, E ≠ ⊥ ∧ IsPGroup q E ∧
        Nat.card D' = r ∧ ⁅D', E⁆ = E ∧ E ⊔ D' = ⊤ ∧
        (⨅ e ∈ D', LinearMap.ker (τ e - LinearMap.id)) = ⊥ ∧
        ((q : ℕ) : AlgebraicClosure (ZMod p)) ≠ 0 ∧ ((r : ℕ) : AlgebraicClosure (ZMod p)) ≠ 0 ∧
        ((Nat.card H : ℕ) : AlgebraicClosure (ZMod p)) ≠ 0 := by
  have core {K : Type} [Field K] {H0 : Type} [Group H0] [Finite H0] {U : Type}
      [AddCommGroup U] [Module K U] [FiniteDimensional K U] (τ0 : Representation K H0 U)
      (hfaith : Function.Injective τ0) (hcard : (Nat.card H0 : K) ≠ 0)
      {q r : ℕ} (hr : r.Prime) (Qh Dh : Subgroup H0) (hQ1 : Qh ≠ ⊥) (hQq : IsPGroup q Qh)
      (hDr : Nat.card Dh = r) (hcomm : ⁅Dh, Qh⁆ = Qh) (hsup : Qh ⊔ Dh = ⊤) (d : H0)
      (hd : Dh = Subgroup.zpowers d) (hker : LinearMap.ker (τ0 d - LinearMap.id) = ⊥) :
      ∃ (H : Type) (_ : Group H) (_ : Finite H) (W : Type) (_ : AddCommGroup W)
        (_ : Module K W) (_ : FiniteDimensional K W) (_ : Nontrivial W)
        (τ : Representation K H W),
        Function.Injective τ ∧ τ.IsIrreducible ∧ ∃ E D' : Subgroup H, E ≠ ⊥ ∧ IsPGroup q E ∧
          Nat.card D' = r ∧ ⁅D', E⁆ = E ∧ E ⊔ D' = ⊤ ∧
          (⨅ e ∈ D', LinearMap.ker (τ e - LinearMap.id)) = ⊥ ∧ Nat.card H ∣ Nat.card H0 := by
    classical
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ1
    have hx : τ0 (x : H0) ≠ 1 := fun h => hx1 (Subtype.ext (hfaith (by simpa using h)))
    obtain ⟨W, hW, hWn, hWirr, hWx⟩ :=
      CFSG.LinearAlgebra.CoprimeActions.CoprimeIrreducibleConstituentSeparates.exists_constituent τ0 hcard (x : H0) hx
    let σ := Representation.subrepresentation τ0 W hW
    have hWirr' : (faithful σ).IsIrreducible := (irreducible_iff σ).2 hWirr
    have hσd : LinearMap.ker (σ d - LinearMap.id) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      have h1 : τ0 d (w : U) - (w : U) = 0 := by
        have := congrArg Subtype.val hw
        simpa [σ, Representation.subrepresentation] using this
      have h2 : (w : U) ∈ LinearMap.ker (τ0 d - LinearMap.id) := by
        simpa using h1
      rw [hker] at h2
      exact Subtype.ext (by simpa using h2)
    let π := toImage σ
    have hfd : LinearMap.ker (faithful σ (π d) - LinearMap.id) = ⊥ := by
      simpa [π] using hσd
    have hπd : π d ≠ 1 := by
      intro h
      rw [h, map_one] at hfd
      have : LinearMap.ker ((1 : Module.End K W) - LinearMap.id) = ⊤ := by
        ext w; simp
      rw [this] at hfd
      exact top_ne_bot hfd
    have hinj : Function.Injective (π.domRestrict Dh) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      haveI : Fact (Nat.card Dh).Prime := ⟨hDr ▸ hr⟩
      rcases (MonoidHom.ker (π.domRestrict Dh)).eq_bot_or_eq_top_of_prime_card with h | h
      · exact h
      · exfalso
        apply hπd
        have : (⟨d, hd ▸ Subgroup.mem_zpowers d⟩ : Dh) ∈ MonoidHom.ker (π.domRestrict Dh) := by
          rw [h]; trivial
        exact (MonoidHom.mem_ker.1 this : (π.domRestrict Dh) _ = 1) |> fun h => by simpa using h
    refine ⟨imageGroup σ, inferInstance, ?_, W, inferInstance, inferInstance, ?_, hWn, faithful σ,
      faithful_injective σ, ?_, ?_⟩
    · exact Finite.of_surjective _ (toImage_surjective σ)
    · infer_instance
    · exact hWirr'
    · refine ⟨Qh.map π, Dh.map π, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Subgroup.ne_bot_iff_exists_ne_one]
        refine ⟨⟨π x, Subgroup.mem_map_of_mem _ x.2⟩, ?_⟩
        intro h
        apply hWx
        have h' : π x = 1 := by
          have := congrArg Subtype.val h
          exact this
        rw [← faithful_toImage σ, h', map_one]
      · have := hQq.of_surjective ((π.domRestrict Qh).rangeRestrict)
          (MonoidHom.rangeRestrict_surjective _)
        rwa [MonoidHom.domRestrict_range] at this
      · rw [← hDr]
        rw [← MonoidHom.domRestrict_range]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      · rw [← Subgroup.map_commutator, hcomm]
      · rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ (toImage_surjective σ)]
      · apply le_bot_iff.1
        rw [← hfd]
        exact iInf₂_le (π d) (Subgroup.mem_map_of_mem _ (hd ▸ Subgroup.mem_zpowers d))
      · exact Subgroup.card_dvd_of_surjective (toImage_surjective σ)
  have card_dvd {H0 : Type} [Group H0] [Finite H0] (Qh Dh : Subgroup H0)
      (hcomm : ⁅Dh, Qh⁆ = Qh) (hsup : Qh ⊔ Dh = ⊤) :
      Nat.card H0 ∣ Nat.card Qh * Nat.card Dh := by
    have hD : Dh ≤ Subgroup.normalizer Qh := by
      rw [Subgroup.le_normalizer_iff]
      intro a ha y hy
      have h1 : ⁅a, y⁆ ∈ Qh := by
        have := Subgroup.commutator_mem_commutator ha hy
        rwa [hcomm] at this
      have h2 : a * y * a⁻¹ = ⁅a, y⁆ * y := by simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact Qh.mul_mem h1 hy
    have hnorm : Qh.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
      exact sup_le Subgroup.le_normalizer hD
    have hsurj : Function.Surjective ((QuotientGroup.mk' Qh).comp Dh.subtype) := by
      intro a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Qh a
      have hy : y ∈ Qh ⊔ Dh := by rw [hsup]; trivial
      obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
      refine ⟨⟨v, hv⟩, ?_⟩
      simp [(QuotientGroup.eq_one_iff u).2 hu]
    have h1 : Nat.card (H0 ⧸ Qh) ∣ Nat.card Dh := Subgroup.card_dvd_of_surjective hsurj
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Qh, mul_comm]
    exact mul_dvd_mul_left _ h1
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact q.Prime := ⟨hq⟩
  let K := AlgebraicClosure (ZMod p)
  have hpne : ∀ n : ℕ, ¬ p ∣ n → (n : K) ≠ 0 := fun n hn h => hn ((CharP.cast_eq_zero_iff K p n).1 h)
  have hpq : ¬ p ∣ q := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hS.prime hq).1 h).symm
  have hpr : ¬ p ∣ r := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hS.prime hr).1 h).symm
  let H0 : Subgroup G := Q ⊔ D
  let ρ0 : Representation (ZMod p) H0 V := ρ.comp H0.subtype
  have hρ0 : Function.Injective ρ0 := hS.faithful.comp H0.subtype_injective
  obtain ⟨W0, hW0, hfin, hinj0⟩ := CFSG.GroupTheory.CoprimeActionSupport.FiniteFaithfulInvariantSubspace.exists_submodule ρ0 hρ0
  let ρ1 := Representation.subrepresentation ρ0 W0 hW0
  haveI : Nontrivial D := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD]; exact hr.one_lt
  obtain ⟨g, hg⟩ := exists_ne (1 : D)
  have hDg : D = Subgroup.zpowers (g : G) := by
    have h1 : Subgroup.zpowers g = ⊤ :=
      zpowers_eq_top_of_prime_card (hD ▸ rfl : Nat.card D = r) hg
    have := congrArg (Subgroup.map D.subtype) h1
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    simpa using this.symm
  have hgH : (g : G) ∈ H0 := le_sup_right (a := Q) g.2
  let d0 : H0 := ⟨g, hgH⟩
  let Qh : Subgroup H0 := Q.subgroupOf H0
  let Dh : Subgroup H0 := Subgroup.zpowers d0
  have hQmap : Qh.map H0.subtype = Q := Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hDmap : Dh.map H0.subtype = D := by
    rw [hDg]; exact MonoidHom.map_zpowers _ _
  have hinjS : Function.Injective (H0.subtype) := H0.subtype_injective
  have hQ1' : Qh ≠ ⊥ := by
    intro h
    apply hQ1
    rw [← hQmap, h]; simp
  have hQq' : IsPGroup q Qh := by
    refine hQq.of_injective (((H0.subtype).comp Qh.subtype).codRestrict Q ?_) ?_
    · intro x; exact x.2
    · intro a b h
      have h' : ((a : H0) : G) = ((b : H0) : G) := by
        have := congrArg Subtype.val h
        exact this
      exact Subtype.ext (Subtype.ext h')
  have hDr : Nat.card Dh = r := by
    rw [← hD, ← hDmap, Subgroup.card_map_of_injective hinjS]
  have hcomm : ⁅Dh, Qh⁆ = Qh := by
    apply Subgroup.map_injective hinjS
    rw [Subgroup.map_commutator, hQmap, hDmap, hQD]
  have hsup : Qh ⊔ Dh = ⊤ := by
    apply Subgroup.map_injective hinjS
    rw [Subgroup.map_sup, hQmap, hDmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hker0 : LinearMap.ker (ρ g - LinearMap.id) = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hgx : ρ g x = x := by simpa [sub_eq_zero] using hx
    let S : Subgroup G :=
      { carrier := {e | ρ e x = x}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at *
          rw [map_mul]; simp [ha, hb]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at *
          calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha]
            _ = x := by rw [← Module.End.mul_apply, ← map_mul]; simp }
    have hle : D ≤ S := by
      rw [hDg, Subgroup.zpowers_le]; exact hgx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro e he
    have := hle he
    simpa [S, sub_eq_zero] using this
  have hker1 : LinearMap.ker (ρ1 d0 - LinearMap.id) = ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.FiniteFaithfulInvariantSubspace.fixed_kernel_eq_bot ρ0 W0 hW0 d0 hker0
  have hker2 : LinearMap.ker (extend (K := K) ρ1 d0 - LinearMap.id) = ⊥ :=
    CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedFixedKernel.kernel_eq_bot ρ1 d0 hker1
  have hdvd := card_dvd Qh Dh hcomm hsup
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := q) (G := Qh)).1 hQq'
  have hcardH0 : ¬ p ∣ Nat.card H0 := by
    intro h
    have := h.trans hdvd
    rw [ha, hDr] at this
    rcases (Nat.Prime.dvd_mul hS.prime).1 this with h | h
    · exact hpq (hS.prime.dvd_of_dvd_pow h)
    · exact hpr h
  obtain ⟨H, i1, i2, W, i3, i4, i5, i6, τ, h1, h2, E, D', h3⟩ :=
    core (K := K) (extend (K := K) ρ1)
      (CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedRepresentationFaithful.faithful ρ1 hinj0) (hpne _ hcardH0) hr Qh Dh hQ1' hQq'
      hDr hcomm hsup d0 rfl hker2
  obtain ⟨hE, hEp, hD'r, hc, hs, hf, hdv⟩ := h3
  refine ⟨H, i1, i2, W, i3, i4, i5, i6, τ, h1, h2, E, D', hE, hEp, hD'r, hc, hs, hf,
    hpne _ hpq, hpne _ hpr, hpne _ (fun h => hcardH0 (h.trans hdv))⟩

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.IrreducibleImageReduction
