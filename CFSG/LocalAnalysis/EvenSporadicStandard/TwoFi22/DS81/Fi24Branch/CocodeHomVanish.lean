module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeTransferO2

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction

section XLevel

variable {V : Type*} [CommGroup V]

@[expose] def HomVanishX (T P : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∀ ψ : MulAut V → V,
    (∀ k₁ ∈ P, ∀ k₂ ∈ P, (ψ (k₁ * k₂))⁻¹ * (ψ k₁ * ψ k₂) ∈ U) →
    (∀ a ∈ T, ∀ k ∈ P, (ψ (a * k * a⁻¹))⁻¹ * a (ψ k) ∈ U) →
    ∀ k ∈ P, ψ k ∈ U

@[expose] def IsEquivQuot (T P : Subgroup (MulAut V)) (U : Subgroup V) (f : ↥P →* V ⧸ U) : Prop :=
  ∀ a ∈ T, ∀ p q : ↥P, (q : MulAut V) = a * p * a⁻¹ →
    ∀ v : V, f p = (v : V ⧸ U) → f q = ((a v : V) : V ⧸ U)

theorem HomVanishX.apply_hom {T P : Subgroup (MulAut V)} {U : Subgroup V}
    (hT : ∀ a ∈ T, ∀ k ∈ P, a * k * a⁻¹ ∈ P) (h : HomVanishX T P U) (f : ↥P →* V ⧸ U)
    (hf : IsEquivQuot T P U f) (p : ↥P) : f p = 1 := by
  classical
  let ψ : MulAut V → V := fun k => if hk : k ∈ P then (f ⟨k, hk⟩).out else 1
  have hψ : ∀ (k : MulAut V) (hk : k ∈ P), ((ψ k : V) : V ⧸ U) = f ⟨k, hk⟩ := by
    intro k hk
    simp only [ψ, dif_pos hk]
    exact QuotientGroup.out_eq' _
  have h1 : ∀ k₁ ∈ P, ∀ k₂ ∈ P, (ψ (k₁ * k₂))⁻¹ * (ψ k₁ * ψ k₂) ∈ U := by
    intro k₁ hk₁ k₂ hk₂
    have hk₁₂ : k₁ * k₂ ∈ P := P.mul_mem hk₁ hk₂
    have e : (((ψ (k₁ * k₂))⁻¹ * (ψ k₁ * ψ k₂) : V) : V ⧸ U) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, hψ _ hk₁₂,
        hψ _ hk₁, hψ _ hk₂]
      have e1 : (⟨k₁ * k₂, hk₁₂⟩ : ↥P) = ⟨k₁, hk₁⟩ * ⟨k₂, hk₂⟩ := rfl
      rw [e1, map_mul, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 e
  have h2 : ∀ a ∈ T, ∀ k ∈ P, (ψ (a * k * a⁻¹))⁻¹ * a (ψ k) ∈ U := by
    intro a ha k hk
    have hak : a * k * a⁻¹ ∈ P := hT a ha k hk
    have e1 := hf a ha ⟨k, hk⟩ ⟨a * k * a⁻¹, hak⟩ rfl (ψ k) (hψ k hk).symm
    have e : (((ψ (a * k * a⁻¹))⁻¹ * a (ψ k) : V) : V ⧸ U) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hψ _ hak, e1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 e
  have h3 := h ψ h1 h2 p p.2
  exact (hψ p p.2).symm.trans ((QuotientGroup.eq_one_iff _).2 h3)

end XLevel

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

theorem homVanish_of_homVanishX (hm : M24Out G E t) {z : G} (hz : z ∈ E) {A : Subgroup G}
    (hAC : A ≤ CNz E z)
    (h : ∀ Ū : Subgroup ↥E,
      (∀ g ∈ S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm)
        (zpowers (⟨z, hz⟩ : ↥E)), ∀ u ∈ Ū, g u ∈ Ū) → Nat.card ↥Ū = 2 ^ 7 →
      @HomVanishX ↥E (commGroupOfM24Out hm)
        ((A.subgroupOf (normalizer (E : Set G))).map (S44.actN E))
        (TwoFi22.O2In (S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm)
          (zpowers (⟨z, hz⟩ : ↥E)))) Ū) :
    HomVanish E z A := by
  letI := commGroupOfM24Out hm
  have hCE := hm.centralizer_eq
  obtain ⟨Tz, hTz⟩ : ∃ Tz : Subgroup (MulAut ↥E), Tz = S44.XE E ⊓
      @Quasithin.centSub ↥E (commGroupOfM24Out hm) (zpowers (⟨z, hz⟩ : ↥E)) := ⟨_, rfl⟩
  rw [← hTz] at h
  have hCNz : CNz E z = preS Tz := by rw [hTz]; exact CNz_eq_preS hm hz
  have hTzX : Tz ≤ S44.XE E := by rw [hTz]; exact inf_le_left
  have hPg : Pg E z = preS (TwoFi22.O2In Tz) := by rw [hTz]; exact Pg_eq_preS hm hz
  obtain ⟨Pb, hPb⟩ : ∃ Pb : Subgroup (MulAut ↥E), Pb = TwoFi22.O2In Tz := ⟨_, rfl⟩
  rw [← hPb] at h hPg
  have hPbX : Pb ≤ S44.XE E := by rw [hPb]; exact (O2In_le _).trans hTzX
  intro U hUE hUinv hUcard φ h1 h2 h3 h4 p hp
  rw [hPg] at h1 h3 h4 hp
  set Ub : Subgroup ↥E := U.subgroupOf E with hUb
  have hUbinv : ∀ g ∈ Tz, ∀ u ∈ Ub, g u ∈ Ub := by
    rw [hCNz] at hUinv
    exact (invUnder_preS_iff hTzX hUE).1 hUinv
  have hUbcard : Nat.card ↥Ub = 2 ^ 7 := by
    rw [← card_eq_card_subgroupOf hUE]
    exact hUcard
  have hAT : ∀ a (ha : a ∈ A) (haN : a ∈ normalizer (E : Set G)),
      S44.actN E ⟨a, haN⟩ ∈ Tz := by
    intro a ha haN
    have h5 := hAC ha
    rw [hCNz] at h5
    exact (mem_preS_iff_of_mem haN).1 h5
  let f₀ : ↥(preS Pb) →* ↥E ⧸ Ub :=
    MonoidHom.mk' (fun q => ((⟨φ q, h1 q q.2⟩ : ↥E) : ↥E ⧸ Ub)) (by
      intro a b
      show ((⟨φ ↑(a * b), h1 _ (a * b).2⟩ : ↥E) : ↥E ⧸ Ub) = _
      rw [← QuotientGroup.mk_mul]
      exact QuotientGroup.eq.2 (h3 a a.2 b b.2))
  have hker : (actPreS Pb).ker ≤ f₀.ker := by
    rw [ker_actPreS hCE Pb]
    intro q hq
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 (h2 q hq)
  have hsurj := actPreS_surjective hPbX
  let f : ↥Pb →* ↥E ⧸ Ub := (MonoidHom.liftOfSurjective (actPreS Pb) hsurj) ⟨f₀, hker⟩
  have hf : ∀ q, f (actPreS Pb q) = f₀ q := fun q =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨f₀, hker⟩ q
  have hequiv :
      IsEquivQuot ((A.subgroupOf (normalizer (E : Set G))).map (S44.actN E)) Pb Ub f := by
    intro ab hab pb qb hq v hv
    obtain ⟨y, hy, rfl⟩ := hab
    have hyA : (y : G) ∈ A := hy
    obtain ⟨p, rfl⟩ := hsurj pb
    have hyC : (y : G) ∈ CNz E z := hAC hyA
    have hpP : (p : G) ∈ Pg E z := by rw [hPg]; exact p.2
    have hyp : (y : G) * (p : G) * (y : G)⁻¹ ∈ preS Pb := by
      have h0 : (y : G) * (p : G) * (y : G)⁻¹ ∈ Pg E z := O2In_conj_mem hyC hpP
      rwa [hPg] at h0
    have hq' : qb = actPreS Pb ⟨(y : G) * (p : G) * (y : G)⁻¹, hyp⟩ := by
      apply Subtype.ext
      rw [hq]
      simp only [actPreS_apply]
      have e : (⟨(y : G) * (p : G) * (y : G)⁻¹, preS_le_normalizer Pb hyp⟩ :
          ↥(normalizer (E : Set G))) = y * ⟨(p : G), preS_le_normalizer Pb p.2⟩ * y⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    rw [hq', hf]
    rw [hf] at hv
    show ((⟨φ ((y : G) * (p : G) * (y : G)⁻¹), h1 _ hyp⟩ : ↥E) : ↥E ⧸ Ub) = _
    have e1 : ((⟨φ ((y : G) * (p : G) * (y : G)⁻¹), h1 _ hyp⟩ : ↥E) : ↥E ⧸ Ub) =
        ((S44.actN E y (⟨φ p, h1 p p.2⟩ : ↥E) : ↥E) : ↥E ⧸ Ub) :=
      QuotientGroup.eq.2 (h4 (y : G) hyA p p.2)
    have hv' : (⟨φ p, h1 p p.2⟩ : ↥E)⁻¹ * v ∈ Ub := QuotientGroup.eq.1 hv
    have hstab := hUbinv (S44.actN E y) (hAT _ hyA y.2) _ hv'
    have e2 : ((S44.actN E y (⟨φ p, h1 p p.2⟩ : ↥E) : ↥E) : ↥E ⧸ Ub) =
        ((S44.actN E y v : ↥E) : ↥E ⧸ Ub) := by
      apply QuotientGroup.eq.2
      rw [map_mul, map_inv] at hstab
      exact hstab
    exact e1.trans e2
  have hnorm : ∀ a ∈ (A.subgroupOf (normalizer (E : Set G))).map (S44.actN E), ∀ k ∈ Pb,
      a * k * a⁻¹ ∈ Pb := by
    rintro _ ⟨y, hy, rfl⟩ k hk
    rw [hPb] at hk ⊢
    exact O2In_conj_mem (hAT _ hy y.2) hk
  have hres := HomVanishX.apply_hom hnorm (h Ub hUbinv hUbcard) f hequiv
    (actPreS Pb ⟨p, hp⟩)
  rw [hf] at hres
  exact (QuotientGroup.eq_one_iff (⟨φ p, h1 p hp⟩ : ↥E)).1 hres

theorem homVanish_preS_of_le_stabSub (hm : M24Out G E t) {z : G} (hz : IsZ E t z)
    {Ab : Subgroup (MulAut ↥E)}
    (hAb : Ab ≤ S44.XE E ⊓ @Quasithin.stabSub ↥E (commGroupOfM24Out hm)
      (closure {(⟨t, hm.t_mem⟩ : ↥E), ⟨z, hz.1⟩}))
    (h : ∀ Ū : Subgroup ↥E,
      (∀ g ∈ S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm)
        (zpowers (⟨z, hz.1⟩ : ↥E)), ∀ u ∈ Ū, g u ∈ Ū) → Nat.card ↥Ū = 2 ^ 7 →
      @HomVanishX ↥E (commGroupOfM24Out hm) Ab
        (TwoFi22.O2In (S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm)
          (zpowers (⟨z, hz.1⟩ : ↥E)))) Ū) :
    HomVanish E z (preS Ab) := by
  have hJ : preS Ab ≤ Nrm E ⊓ Jg t z := by
    rw [Nrm_inf_Jg_eq_preS hm hm.t_mem hz.1]
    exact preS_mono hAb
  refine homVanish_of_homVanishX hm hz.1 (hJ.trans (Nrm_inf_Jg_le_CNz hm hz)) ?_
  intro Ū hinv hcard
  rw [map_actN_preS (hAb.trans inf_le_left)]
  exact h Ū hinv hcard

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
