module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig23

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem exists_four_subgroup_of_surjective [Finite X] {K : Subgroup X} {n : ℕ} (hn : 4 ≤ n)
    (f : ↥K →* alternatingGroup (Fin n)) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) :
    ∃ E : Subgroup X, E ≤ K ∧ Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      ∃ D : Finset (Fin n), D.card = 4 ∧ ∀ x : K, (x : X) ∈ E → ∀ ω ∉ D,
        ((f x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hn) with hDdef
  have hD : D.card = 4 := by rw [hDdef, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcardD : Fintype.card ↥D = 4 := by rw [Fintype.card_coe, hD]
  let ψ : alternatingGroup ↥D ≃* alternatingGroup (Fin 4) :=
    (Fintype.equivFinOfCardEq hcardD).altCongrHom
  set V : Subgroup (alternatingGroup (Fin n)) :=
    (altFourKlein.map ψ.symm.toMonoidHom).map (alternatingGroup.ofSubtype D) with hVdef
  have hVsupp : ∀ σ ∈ V, ∀ ω ∉ D, (σ : Equiv.Perm (Fin n)) ω = ω := by
    rintro _ ⟨τ, -, rfl⟩ ω hω
    have h1 := (alternatingGroup.mem_range_ofSubtype_iff D (alternatingGroup.ofSubtype D τ)).mp
      ⟨τ, rfl⟩
    by_contra hc
    exact hω (h1 (Equiv.Perm.mem_support.mpr hc))
  have hinj : Function.Injective
      ((alternatingGroup.ofSubtype D).comp ψ.symm.toMonoidHom) :=
    alternatingGroup.ofSubtype_injective.comp ψ.symm.injective
  have hVe : V ≃* altFourKlein := by
    rw [hVdef, Subgroup.map_map]
    exact (altFourKlein.equivMapOfInjective _ hinj).symm
  have hV4 : Nat.card V = 4 := by rw [Nat.card_congr hVe.toEquiv, card_altFourKlein]
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hVsq : ∀ σ ∈ V, σ * σ = 1 := by
    rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    have hτ' : τ * τ = 1 := hτ
    rw [← map_mul, ← map_mul, hτ', map_one, map_one]
  obtain ⟨P, hPV, hPinj⟩ := exists_lift_two_subgroup f hf hker V hV2
  have hPcard : Nat.card P = 4 := by
    have h1 : Function.Injective (f.comp P.subtype) := by
      intro a b hab
      have hab' : f ((a : K) * (b : K)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr hab
      have := hPinj _ (mul_mem a.2 (inv_mem b.2)) hab'
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have h2 : (f.comp P.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPV]
    rw [← hV4, ← h2]
    exact Nat.card_congr (MonoidHom.ofInjective h1).toEquiv
  refine ⟨P.map K.subtype, map_subtype_le P, ?_, D, hD, fun x hx ω hω => ?_⟩
  · have hE4 : Nat.card (P.map K.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hPcard]
    have hEsq : ∀ g : P.map K.subtype, g * g = 1 := by
      rintro ⟨_, ⟨p, hp, rfl⟩⟩
      apply Subtype.ext
      have hfp : f p ∈ V := hPV ▸ mem_map_of_mem f hp
      have h1 : f (p * p) = 1 := by rw [map_mul, hVsq _ hfp]
      have := hPinj _ (mul_mem hp hp) h1
      change (p : X) * p = 1
      rw [← Subgroup.coe_mul, this]
      rfl
    have := isKleinFour_of_card hE4 hEsq
    have := isKleinFour_prod
    exact IsKleinFour.nonempty_mulEquiv
  · obtain ⟨p, hp, hpx⟩ := hx
    have hpx' : p = x := Subtype.ext hpx
    subst hpx'
    have hfp : f p ∈ V := hPV ▸ mem_map_of_mem f hp
    exact hVsupp _ hfp ω hω

theorem not_mem_of_mem_coreActionKernel [Finite X] {J : Subgroup X} {n : ℕ} (hn : 4 ≤ n)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {z : X} (hz : orderOf z = 2)
    (hzK : z ∈ UnbalancedLayer.coreActionKernel J) : z ∉ J := by
  intro hzJ
  set Z : J := ⟨z, hzJ⟩
  have hZc : QuotientGroup.mk' (pPrimeCore 2 J) Z ∈ center (J ⧸ pPrimeCore 2 J) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have h1 := hzK.2 j j.2
    have h2 : QuotientGroup.mk' (pPrimeCore 2 J) (j⁻¹ * Z⁻¹ * j * Z) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨w, hw, hwe⟩ := h1
      have : w = j⁻¹ * Z⁻¹ * j * Z := Subtype.ext (by simpa [Z] using hwe)
      rwa [← this]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc QuotientGroup.mk' (pPrimeCore 2 J) j * QuotientGroup.mk' (pPrimeCore 2 J) Z =
        QuotientGroup.mk' (pPrimeCore 2 J) Z * QuotientGroup.mk' (pPrimeCore 2 J) j *
          ((QuotientGroup.mk' (pPrimeCore 2 J) j)⁻¹ * (QuotientGroup.mk' (pPrimeCore 2 J) Z)⁻¹ *
            QuotientGroup.mk' (pPrimeCore 2 J) j * QuotientGroup.mk' (pPrimeCore 2 J) Z) := by
          group
      _ = _ := by rw [h2, mul_one]
  have hT1 : QuotientGroup.mk' (pPrimeCore 2 J) Z = 1 := by
    have h1 : e (QuotientGroup.mk' (pPrimeCore 2 J) Z) ∈ center (alternatingGroup (Fin n)) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨_, hZc, rfl⟩
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot] at h1
    exact (map_eq_one_iff _ e.injective).mp h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hT1
  have hdvd : orderOf Z ∣ Nat.card (pPrimeCore 2 J) := by
    rw [← Subgroup.orderOf_mk Z hT1]
    exact orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hz] at hdvd
  exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
    (even_iff_two_dvd.mpr hdvd)

theorem restrict_surjective_of_sup [Finite X] {J K : Subgroup X} {n : ℕ}
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (hKJ : K ≤ J)
    (hsup : K ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) :
    Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))).comp
        (inclusion hKJ)) ∧
      Odd (Nat.card ((e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))).comp
        (inclusion hKJ)).ker) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))).comp (inclusion hKJ)
    with hfdef
  refine ⟨?_, ?_⟩
  · have h1 : K.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
      have h2 : (K ⊔ (pPrimeCore 2 ↥J).map J.subtype).subgroupOf J = ⊤ := by
        rw [hsup]
        exact subgroupOf_self J
      rwa [subgroupOf_sup hKJ (map_subtype_le _), subgroupOf_map_subtype_self] at h2
    intro a
    obtain ⟨q, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) q
    have hy : y ∈ K.subgroupOf J ⊔ pPrimeCore 2 ↥J := by rw [h1]; exact mem_top y
    rw [← SetLike.mem_coe, mul_normal] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    change e (QuotientGroup.mk' _ (inclusion hKJ ⟨a, ha⟩)) = e (QuotientGroup.mk' _ (a * b))
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff b).mpr hb, mul_one]
    rfl
  · let g : f.ker →* pPrimeCore 2 ↥J := ((inclusion hKJ).comp f.ker.subtype).codRestrict _
      fun k => by
        have h1 : f k = 1 := k.2
        change e (QuotientGroup.mk' _ _) = 1 at h1
        rwa [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at h1
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : pPrimeCore 2 ↥J => ((x : ↥J) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (Subgroup.card_dvd_of_injective g hg)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem ofFour {E' : Subgroup X} {D' : Finset (Fin n)} (hE'J : E' ≤ J)
    (hE' : Nonempty (E' ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hD' : D'.card = 4) (hs : ∀ x : J, (x : X) ∈ E' → ∀ ω ∉ D',
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) :
    Sig36 X t J n e E' D' :=
  ⟨S.nonab, S.kProper, S.unbal, S.notU, S.pair, hE'J, hE', hD', hs⟩

theorem completion_eq_of_four (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    {E' : Subgroup X} {D' : Finset (Fin n)} (hE'J : E' ≤ J)
    (hE' : Nonempty (E' ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hD' : D'.card = 4) (hs : ∀ x : J, (x : X) ∈ E' → ∀ ω ∉ D',
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) :
    Sol78.signalizerCompletion E' E' = Sol78.signalizerCompletion E E := by
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein S.klein
  obtain ⟨hE'4, hE'2⟩ := card_sq_of_klein hE'
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE2 x hx
  have hE'sq : ∀ x ∈ E', x * x = 1 := fun x hx => by rw [← sq]; exact hE'2 x hx
  obtain ⟨j, hj, hjE⟩ := exists_conj_four_subgroup (by have := S.nine_le; omega) e S.le hE'J
    hE4 hE'4 hEsq hE'sq S.card hD' S.supp hs
  have h1 := signalizerCompletion_map_aut (MulAut.conj j) E E
  rw [hjE] at h1
  rw [← h1]
  exact mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer_completion h33 h35 hj)

theorem core_le_of_kernel (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35) {z : X}
    (hz : orderOf z = 2) (hzt : z ∈ centralizer ({t} : Set X))
    (hzK : z ∈ UnbalancedLayer.coreActionKernel J) :
    (pPrimeCore 2 (centralizer ({z} : Set X))).map (centralizer ({z} : Set X)).subtype ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hzJ := not_mem_of_mem_coreActionKernel (by have := S.nine_le; omega) e hz hzK
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ S.pair.1.2.1).mp S.pair.1.2.2.1).2.2
  obtain ⟨hJzJ, hJzz, -, -⟩ := S.fixedLayer_facts hz2 hzt hzK
  set Jz := GSLit.fixedLayer J (zpowers z) with hJzdef
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq (zpowers_le.mpr hzK) hz2
  obtain ⟨hf, hfk⟩ := restrict_surjective_of_sup e hJzJ hsup
  obtain ⟨E', hE'Jz, hE', D', hD', hs'⟩ :=
    exists_four_subgroup_of_surjective (by have := S.nine_le; omega) _ hf hfk
  have hE'J : E' ≤ J := hE'Jz.trans hJzJ
  have hs : ∀ x : J, (x : X) ∈ E' → ∀ ω ∉ D',
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω := by
    intro x hx ω hω
    exact hs' ⟨x, hE'Jz hx⟩ hx ω hω
  set S' := S.ofFour hE'J hE' hD' hs
  have hW := S.completion_eq_of_four h33 h35 hE'J hE' hD' hs
  have hzE' : z ∈ centralizer (E' : Set X) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hJzz (hE'Jz hx))
  have hzK' : z ∈ UnbalancedLayer.coreActionKernel J := hzK
  have hWz := S'.completion_eq_completion_self h33 hz hzE' hzK' hzJ
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hθ : SolAltLit.thetaFunctor E' z ≤ Sol78.signalizerCompletion E' E' := by
    rw [← hWz]
    exact le_iSup₂_of_le (f := fun (c : X) (_ : c ∈ E' ⊔ zpowers z) =>
      ⨆ (_ : c ≠ 1), SolAltLit.thetaFunctor E' c) z (mem_sup_right (mem_zpowers z))
      (le_iSup_of_le hz1 le_rfl)
  have hE'z : E' ≤ centralizer ({z} : Set X) := fun x hx => hJzz (hE'Jz hx)
  have h1 := oddCore_le_normalizer_of_theta S'.isPGroup hE'z hθ
    (normalizer_le_normalizer_signalizerCompletion_self E')
  rwa [hW] at h1

end Sig36

end CFSG.ComponentClassification.SolMax
