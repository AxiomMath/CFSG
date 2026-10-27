module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSABasic
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint
open scoped commutatorElement Pointwise

@[expose] def quotAutOfChar {Q : Type*} [Group Q] (R : Subgroup Q) [R.Characteristic] :
    MulAut Q →* MulAut (Q ⧸ R) where
  toFun σ := QuotientGroup.congr R R σ (UnbalancingLocal.map_mulAut_eq_of_characteristic R σ)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [QuotientGroup.congr_mk]
      rfl
  map_mul' σ τ := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, MulAut.mul_apply]

theorem quotAutOfChar_mk {Q : Type*} [Group Q] (R : Subgroup Q) [R.Characteristic]
    (σ : MulAut Q) (q : Q) : quotAutOfChar R σ (q : Q ⧸ R) = ((σ q : Q) : Q ⧸ R) :=
  rfl

variable {X : Type*} [Group X]

@[expose] def oddQuotAction (S : Subgroup X) :
    normalizer (S : Set X) →* MulAut (S ⧸ pPrimeCore 2 S) :=
  (quotAutOfChar (pPrimeCore 2 S)).comp S.normalizerMonoidHom

abbrev oddCoreIn (S : Subgroup X) : Subgroup X := (pPrimeCore 2 S).map S.subtype

theorem oddQuotAction_mk (S : Subgroup X) (g : normalizer (S : Set X)) (s : S) :
    oddQuotAction S g (s : S ⧸ pPrimeCore 2 S) =
      ((⟨(g : X) * s * (g : X)⁻¹, (mem_normalizer_iff.mp g.2 s).mp s.2⟩ : S) :
        S ⧸ pPrimeCore 2 S) := by
  change ((g • s : S) : S ⧸ pPrimeCore 2 S) = _
  congr 1

theorem oddQuotAction_eq_one_iff {S : Subgroup X} (g : normalizer (S : Set X)) :
    oddQuotAction S g = 1 ↔ ∀ s ∈ S, ⁅s, (g : X)⁆ ∈ oddCoreIn S := by
  have key : ∀ s : S, ((⟨(g : X) * s * (g : X)⁻¹, (mem_normalizer_iff.mp g.2 s).mp s.2⟩ : S) :
      S ⧸ pPrimeCore 2 S) = (s : S ⧸ pPrimeCore 2 S) ↔ ⁅(s : X), (g : X)⁆ ∈ oddCoreIn S := by
    intro s
    rw [QuotientGroup.eq]
    constructor
    · intro h
      refine ⟨_, (inferInstance : (pPrimeCore 2 S).Normal).conj_mem _ h s, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    · rintro ⟨o, ho, hos⟩
      have ho' : o ∈ pPrimeCore 2 S := ho
      have hos' : (o : X) = ⁅(s : X), (g : X)⁆ := hos
      have heq : (⟨(g : X) * s * (g : X)⁻¹, (mem_normalizer_iff.mp g.2 s).mp s.2⟩ : S)⁻¹ * s =
          s⁻¹ * o * s⁻¹⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hos', commutatorElement_def]
        group
      rw [heq]
      exact (inferInstance : (pPrimeCore 2 S).Normal).conj_mem o ho' s⁻¹
  constructor
  · intro h s hs
    have hq := congrArg (fun φ : MulAut (S ⧸ pPrimeCore 2 S) =>
      φ ((⟨s, hs⟩ : S) : S ⧸ pPrimeCore 2 S)) h
    simp only [MulAut.one_apply, oddQuotAction_mk] at hq
    exact (key ⟨s, hs⟩).mp hq
  · intro h
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H s =>
      rw [oddQuotAction_mk, MulAut.one_apply]
      exact (key s).mpr (h s s.2)

theorem conj_mem_oddCoreIn {S : Subgroup X} {g : X} (hg : g ∈ normalizer (S : Set X)) {o : X}
    (ho : o ∈ oddCoreIn S) : g * o * g⁻¹ ∈ oddCoreIn S := by
  obtain ⟨o', ho', rfl⟩ := ho
  have h1 := UnbalancingLocal.map_mulAut_eq_of_characteristic (pPrimeCore 2 S)
    (S.normalizerMonoidHom ⟨g, hg⟩)
  have h2 : S.normalizerMonoidHom ⟨g, hg⟩ o' ∈ pPrimeCore 2 S := by
    rw [← h1]
    exact ⟨o', ho', rfl⟩
  exact ⟨_, h2, rfl⟩

theorem normalizer_le_normalizer_oddCoreIn (S : Subgroup X) :
    normalizer (S : Set X) ≤ normalizer (oddCoreIn S : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_oddCoreIn hg hx, fun hx => ?_⟩
  have h := conj_mem_oddCoreIn (inv_mem hg) hx
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

theorem closure_insert_le_sup_zpowers (t : X) (E : Subgroup X) :
    closure (insert t (E : Set X)) ≤ E ⊔ zpowers t := by
  rw [closure_le]
  rintro x (rfl | hx)
  · exact mem_sup_right (mem_zpowers x)
  · exact mem_sup_left hx

theorem not_mem_of_orderOf_two_of_odd [Finite X] {E : Subgroup X} (hE : Odd (Nat.card E)) {t : X}
    (ht : orderOf t = 2) : t ∉ E := by
  intro htE
  have hd : orderOf (⟨t, htE⟩ : E) ∣ Nat.card E := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, ht] at hd
  exact (Nat.not_even_iff_odd.mpr hE) (even_iff_two_dvd.mpr hd)

theorem actsProperly_of_involution [Finite X] {S E : Subgroup X} {t : X} (ht : orderOf t = 2)
    (htE : t ∈ normalizer (E : Set X)) (hEodd : Odd (Nat.card E))
    (htS : t ∈ normalizer (S : Set X)) (hES : E ≤ normalizer (S : Set X))
    (htnt : ¬ ∀ s ∈ S, ⁅s, t⁆ ∈ oddCoreIn S)
    (hEnt : ∃ e ∈ E, ∃ s ∈ S, ⁅s, e⁆ ∉ oddCoreIn S) :
    ActsProperly t E S (oddCoreIn S) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have htnE : t ∉ E := not_mem_of_orderOf_two_of_odd hEodd ht
  have hcl : closure (insert t (E : Set X)) ≤ normalizer (S : Set X) := by
    rw [closure_le]
    rintro x (rfl | hx)
    · exact htS
    · exact hES hx
  refine ⟨le_inf hcl (hcl.trans (normalizer_le_normalizer_oddCoreIn S)), fun g hg htriv => ?_,
    hEnt⟩
  rcases (UnbalancedGS.AHelpers.mem_sup_zpowers_iff htE htnE (by rw [ht2]; exact one_mem E) g).mp
    (closure_insert_le_sup_zpowers t E hg) with hgE | ⟨e, he, rfl⟩
  · exact hgE
  · exfalso
    apply htnt
    have heS : e ∈ normalizer (S : Set X) := hES he
    have h1 : oddQuotAction S ⟨e * t, mul_mem heS htS⟩ = 1 :=
      (oddQuotAction_eq_one_iff _).mpr htriv
    have h2 : oddQuotAction S ⟨t, htS⟩ = (oddQuotAction S ⟨e, heS⟩)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← map_mul]
      have : (⟨t, htS⟩ : normalizer (S : Set X)) * ⟨e, heS⟩ =
          ⟨e, heS⟩⁻¹ * ⟨e * t, mul_mem heS htS⟩ * ⟨e, heS⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this, map_mul, map_mul, h1, mul_one, map_inv, inv_mul_cancel]
    have hodd : Odd (orderOf (oddQuotAction S ⟨e, heS⟩)) := by
      have hdvd : orderOf (oddQuotAction S ⟨e, heS⟩) ∣ orderOf e := by
        rw [← Subgroup.orderOf_mk e heS]
        exact orderOf_map_dvd _ _
      have heo : Odd (orderOf e) := by
        rw [← Subgroup.orderOf_mk e he]
        exact Odd.of_dvd_nat hEodd (orderOf_dvd_natCard _)
      exact Odd.of_dvd_nat heo hdvd
    have h2' : orderOf (oddQuotAction S ⟨t, htS⟩) ∣ 2 := by
      have h := orderOf_map_dvd (oddQuotAction S) (⟨t, htS⟩ : normalizer (S : Set X))
      rwa [Subgroup.orderOf_mk, ht] at h
    rw [h2, orderOf_inv] at h2'
    have h1' : orderOf (oddQuotAction S ⟨e, heS⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h1'
    rw [h1', inv_one] at h2
    exact (oddQuotAction_eq_one_iff ⟨t, htS⟩).mp h2

theorem ActsProperly.not_trivial_left [Finite X] {t : X} {E S B : Subgroup X}
    (h : ActsProperly t E S B) (ht : orderOf t = 2) (hEodd : Odd (Nat.card E)) :
    ¬ ∀ s ∈ S, ⁅s, t⁆ ∈ B :=
  fun htriv => not_mem_of_orderOf_two_of_odd hEodd ht
    (h.2.1 t (subset_closure (Set.mem_insert t _)) htriv)

theorem ActsProperly.exists_nontrivial {t : X} {E S B : Subgroup X} (h : ActsProperly t E S B) :
    ∃ e ∈ E, ∃ s ∈ S, ⁅s, e⁆ ∉ B :=
  h.2.2

theorem exists_centralizer_mem_nontrivial [Finite X] {S E : Subgroup X} {γ : X} (hγ : γ ^ 2 = 1)
    (hγE : γ ∈ normalizer (E : Set X)) (hEodd : Odd (Nat.card E))
    (hγS : γ ∈ normalizer (S : Set X)) (hES : E ≤ normalizer (S : Set X))
    (hγtriv : ∀ s ∈ S, ⁅s, γ⁆ ∈ oddCoreIn S)
    (hEnt : ∃ e ∈ E, ∃ s ∈ S, ⁅s, e⁆ ∉ oddCoreIn S) :
    ∃ e ∈ E ⊓ centralizer ({γ} : Set X), ∃ s ∈ S, ⁅s, e⁆ ∉ oddCoreIn S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : normalizer (S : Set X) →* MulAut (S ⧸ pPrimeCore 2 S) := oddQuotAction S with hρ
  have hργ : ρ ⟨γ, hγS⟩ = 1 := (oddQuotAction_eq_one_iff _).mpr hγtriv
  let ρE : E →* MulAut (S ⧸ pPrimeCore 2 S) := ρ.comp (inclusion hES)
  set N : Subgroup E := ρE.ker with hN
  have hA : IsPGroup 2 (zpowers γ) := fun a => ⟨1, by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hγ, one_zpow, Subgroup.coe_one]⟩
  let act : zpowers γ →* MulAut E :=
    E.normalizerMonoidHom.comp (inclusion (zpowers_le.mpr hγE))
  have hconj : ∀ (a : zpowers γ) (e : E), ((act a e : E) : X) = (a : X) * e * (a : X)⁻¹ :=
    fun _ _ => rfl
  have hρconj : ∀ (a : zpowers γ) (e : E), ρE (act a e) = ρE e := by
    intro a e
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.2
    have haS : (a : X) ∈ normalizer (S : Set X) := (zpowers_le.mpr hγS) a.2
    have hρa : ρ ⟨a, haS⟩ = 1 := by
      have : (⟨a, haS⟩ : normalizer (S : Set X)) = ⟨γ, hγS⟩ ^ k := by
        apply Subtype.ext
        rw [← hk]
        rfl
      rw [this, map_zpow, hργ, one_zpow]
    have : (inclusion hES (act a e)) = ⟨a, haS⟩ * inclusion hES e * ⟨a, haS⟩⁻¹ := by
      apply Subtype.ext
      rfl
    change ρ (inclusion hES (act a e)) = ρ (inclusion hES e)
    rw [this, map_mul, map_mul, map_inv, hρa, one_mul, inv_one, mul_one]
  have hNinv : ∀ (a : zpowers γ), ∀ n ∈ N, act a n ∈ N := by
    intro a n hn
    rw [hN, MonoidHom.mem_ker] at hn ⊢
    rw [hρconj, hn]
  have hcop : ¬ 2 ∣ Nat.card N := by
    intro h2
    have h1 : Nat.card N ∣ Nat.card E := card_subgroup_dvd_card N
    exact (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr (h2.trans h1))
  have hfix := Semidihedral.Principal.coprime_fixed_point_lifting 2 hA act N hNinv hcop
  obtain ⟨e₀, he₀, s₀, hs₀, hnt⟩ := hEnt
  have hρe₀ : ρE ⟨e₀, he₀⟩ ≠ 1 := by
    intro h1
    exact hnt ((oddQuotAction_eq_one_iff ⟨e₀, hES he₀⟩).mp h1 s₀ hs₀)
  have hq : (QuotientGroup.mk' N (⟨e₀, he₀⟩ : E)) ∈ {q : E ⧸ N | ∀ a : zpowers γ,
      Semidihedral.Principal.CoprimeFixedPoint.quotientAction act N hNinv a q = q} := by
    intro a
    change QuotientGroup.mk' N (act a ⟨e₀, he₀⟩) = QuotientGroup.mk' N ⟨e₀, he₀⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      MonoidHom.mem_ker, map_mul, map_inv, hρconj, inv_mul_cancel]
  rw [hfix] at hq
  obtain ⟨c, hc, hcq⟩ := hq
  have hcγ : (c : X) ∈ centralizer ({γ} : Set X) := by
    have h1 := congrArg Subtype.val (hc ⟨γ, mem_zpowers γ⟩)
    rw [hconj] at h1
    rw [mem_centralizer_singleton_iff]
    calc (c : X) * γ = (γ * c * γ⁻¹) * γ := by rw [h1]
      _ = γ * c := by group
  have hρc : ρE c ≠ 1 := by
    have h1 : c⁻¹ * ⟨e₀, he₀⟩ ∈ N := by
      rw [← QuotientGroup.eq]
      exact hcq
    rw [hN, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    rw [h1]
    exact hρe₀
  refine ⟨c, mem_inf.mpr ⟨c.2, hcγ⟩, ?_⟩
  by_contra hall
  apply hρc
  refine (oddQuotAction_eq_one_iff (S := S) ⟨(c : X), hES c.2⟩).mpr fun s hs => ?_
  by_contra h
  exact hall ⟨s, hs, h⟩

theorem actsTrivially_iff_of_cover {S T : Subgroup X} (hTS : T ≤ S)
    (hcov : (T : Set X) * (oddCoreIn S : Set X) = S)
    (hcore : oddCoreIn T = T ⊓ oddCoreIn S) {g : X} (hgS : g ∈ normalizer (S : Set X))
    (hgT : g ∈ normalizer (T : Set X)) :
    (∀ s ∈ S, ⁅s, g⁆ ∈ oddCoreIn S) ↔ ∀ t ∈ T, ⁅t, g⁆ ∈ oddCoreIn T := by
  have hcomm_mem : ∀ {A : Subgroup X}, g ∈ normalizer (A : Set X) → ∀ a ∈ A, ⁅a, g⁆ ∈ A := by
    intro A hgA a ha
    have h := (mem_normalizer_iff.mp hgA a⁻¹).mp (inv_mem ha)
    have heq : ⁅a, g⁆ = a * (g * a⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem ha h
  constructor
  · intro h t ht
    rw [hcore]
    exact mem_inf.mpr ⟨hcomm_mem hgT t ht, h t (hTS ht)⟩
  · intro h s hs
    rw [← SetLike.mem_coe, ← hcov] at hs
    obtain ⟨t, ht, o, ho, rfl⟩ := hs
    have hOS : oddCoreIn S ≤ S := map_subtype_le _
    have hon : (oddCoreIn S).subgroupOf S |>.Normal := by
      rw [normal_subgroupOf_iff hOS]
      intro x y hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      refine ⟨⟨y, hy⟩ * x' * ⟨y, hy⟩⁻¹, (inferInstance : (pPrimeCore 2 S).Normal).conj_mem x' hx'
        ⟨y, hy⟩, ?_⟩
      simp
    have h1 : ⁅o, g⁆ ∈ oddCoreIn S := by
      have heq : ⁅o, g⁆ = o * (g * o⁻¹ * g⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact mul_mem ho (conj_mem_oddCoreIn hgS (inv_mem ho))
    have h2 : ⁅t, g⁆ ∈ oddCoreIn S := by
      have := h t ht
      rw [hcore] at this
      exact (mem_inf.mp this).2
    have heq : ⁅t * o, g⁆ = t * ⁅o, g⁆ * t⁻¹ * ⁅t, g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem ((normal_subgroupOf_iff hOS).mp hon _ _ h1 (hTS ht)) h2

end CFSG.ComponentClassification.TBLit
