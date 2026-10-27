module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

theorem eq_of_complements {E : Subgroup G} {z : G} {A U R S : Subgroup G}
    (hHV : HomVanish E z A) (hUE : U ≤ E) (hUinv : InvUnder (CNz E z) U)
    (hUcard : Nat.card ↥U = 2 ^ 7)
    (hPP : ∀ p ∈ Pg E z, ∀ q ∈ Pg E z, p * q * p⁻¹ * q⁻¹ ∈ U)
    (hRP : R ≤ Pg E z) (hSP : S ≤ Pg E z) (hUR : U ≤ R) (hUS : U ≤ S)
    (hRE : R ⊓ E = U) (hSE : S ⊓ E = U)
    (hRdec : ∀ p ∈ Pg E z, ∃ r ∈ R, ∃ e ∈ E, p = r * e)
    (hSdec : ∀ p ∈ Pg E z, ∃ s ∈ S, ∃ e ∈ E, p = s * e)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hAE : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E)
    (hAR : ∀ a ∈ A, ∀ x ∈ R, a * x * a⁻¹ ∈ R) (hAS : ∀ a ∈ A, ∀ x ∈ S, a * x * a⁻¹ ∈ S)
    (hAP : ∀ a ∈ A, ∀ p ∈ Pg E z, a * p * a⁻¹ ∈ Pg E z) :
    R = S := by
  classical
  have hRex : ∀ p : G, ∃ r : G, p ∈ Pg E z → r ∈ R ∧ ∃ e ∈ E, p = r * e := by
    intro p
    by_cases hp : p ∈ Pg E z
    · obtain ⟨r, hr, e, he, hpe⟩ := hRdec p hp
      exact ⟨r, fun _ => ⟨hr, e, he, hpe⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  have hSex : ∀ p : G, ∃ s : G, p ∈ Pg E z → s ∈ S ∧ ∃ e ∈ E, p = s * e := by
    intro p
    by_cases hp : p ∈ Pg E z
    · obtain ⟨s, hs, e, he, hpe⟩ := hSdec p hp
      exact ⟨s, fun _ => ⟨hs, e, he, hpe⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  let rOf : G → G := fun p => Classical.choose (hRex p)
  let sOf : G → G := fun p => Classical.choose (hSex p)
  have hrOf : ∀ p (hp : p ∈ Pg E z), rOf p ∈ R ∧ ∃ e ∈ E, p = rOf p * e :=
    fun p hp => Classical.choose_spec (hRex p) hp
  have hsOf : ∀ p (hp : p ∈ Pg E z), sOf p ∈ S ∧ ∃ e ∈ E, p = sOf p * e :=
    fun p hp => Classical.choose_spec (hSex p) hp
  let φ : G → G := fun p => if hp : p ∈ Pg E z then (rOf p)⁻¹ * (sOf p) else 1
  have hφ_in : ∀ p (hp : p ∈ Pg E z), φ p = (rOf p)⁻¹ * (sOf p) := by
    intro p hp
    simp only [φ, dif_pos hp]
  have hφ_out : ∀ p, p ∉ Pg E z → φ p = 1 := by
    intro p hp
    simp only [φ, dif_neg hp]
  have hnrmP : ∀ x ∈ Pg E z, ∀ y ∈ E, x * y * x⁻¹ ∈ E := by
    intro x hx y hy
    have hxN : x ∈ Nrm E := CNz_le_Nrm E z (Pg_le_CNz E z hx)
    exact ((mem_Nrm.mp hxN) y).mp hy
  have hφE : ∀ p ∈ Pg E z, φ p ∈ E := by
    intro p hp
    rw [hφ_in p hp]
    obtain ⟨ep, hep, hpep⟩ := (hrOf p hp).2
    obtain ⟨fp, hfp, hpfp⟩ := (hsOf p hp).2
    have h3 : rOf p * ep = sOf p * fp := by rw [← hpep, ← hpfp]
    have h4 : (rOf p)⁻¹ * sOf p * fp = ep := by
      calc (rOf p)⁻¹ * sOf p * fp = (rOf p)⁻¹ * (rOf p * ep) := by rw [h3]; group
        _ = ep := by group
    have hstep : (rOf p)⁻¹ * sOf p = ep * fp⁻¹ := by
      calc (rOf p)⁻¹ * sOf p = ((rOf p)⁻¹ * sOf p * fp) * fp⁻¹ := by group
        _ = ep * fp⁻¹ := by rw [h4]
    rw [hstep]
    exact E.mul_mem hep (E.inv_mem hfp)
  have hφU_E : ∀ e ∈ E, φ e ∈ U := by
    intro e he
    by_cases heP : e ∈ Pg E z
    · rw [hφ_in e heP]
      obtain ⟨e₁, he₁, hpe₁⟩ := (hrOf e heP).2
      obtain ⟨f₁, hf₁, hpf₁⟩ := (hsOf e heP).2
      have hrE : rOf e ∈ E := by
        have h : rOf e = e * e₁⁻¹ := by
          nth_rewrite 2 [hpe₁]
          group
        rw [h]; exact E.mul_mem he (E.inv_mem he₁)
      have hsE : sOf e ∈ E := by
        have h : sOf e = e * f₁⁻¹ := by
          nth_rewrite 2 [hpf₁]
          group
        rw [h]; exact E.mul_mem he (E.inv_mem hf₁)
      have hrU : rOf e ∈ U := by
        have hmem : rOf e ∈ R ⊓ E := ⟨(hrOf e heP).1, hrE⟩
        rwa [hRE] at hmem
      have hsU : sOf e ∈ U := by
        have hmem : sOf e ∈ S ⊓ E := ⟨(hsOf e heP).1, hsE⟩
        rwa [hSE] at hmem
      exact U.mul_mem (U.inv_mem hrU) hsU
    · rw [hφ_out e heP]
      exact U.one_mem
  have hD1R : ∀ p (hp : p ∈ Pg E z) (r : G), r ∈ R → r⁻¹ * p ∈ E →
      (rOf p)⁻¹ * r ∈ U := by
    intro p hp r hrR hrp
    obtain ⟨ep, hep, hpep⟩ := (hrOf p hp).2
    have h1 : (rOf p)⁻¹ * p = ep := by
      nth_rewrite 2 [hpep]
      group
    have h2 : p⁻¹ * r ∈ E := by
      have := E.inv_mem hrp
      simpa only [mul_inv_rev, inv_inv] using this
    have hmem : (rOf p)⁻¹ * r ∈ R ⊓ E := by
      refine ⟨R.mul_mem (R.inv_mem (hrOf p hp).1) hrR, ?_⟩
      have heq : (rOf p)⁻¹ * r = ((rOf p)⁻¹ * p) * (p⁻¹ * r) := by group
      rw [heq]
      exact E.mul_mem (by rw [h1]; exact hep) h2
    rwa [hRE] at hmem
  have hD1S : ∀ p (hp : p ∈ Pg E z) (s : G), s ∈ S → s⁻¹ * p ∈ E →
      (sOf p)⁻¹ * s ∈ U := by
    intro p hp s hsS hsp
    obtain ⟨fp, hfp, hpfp⟩ := (hsOf p hp).2
    have h1 : (sOf p)⁻¹ * p = fp := by
      nth_rewrite 2 [hpfp]
      group
    have h2 : p⁻¹ * s ∈ E := by
      have := E.inv_mem hsp
      simpa only [mul_inv_rev, inv_inv] using this
    have hmem : (sOf p)⁻¹ * s ∈ S ⊓ E := by
      refine ⟨S.mul_mem (S.inv_mem (hsOf p hp).1) hsS, ?_⟩
      have heq : (sOf p)⁻¹ * s = ((sOf p)⁻¹ * p) * (p⁻¹ * s) := by group
      rw [heq]
      exact E.mul_mem (by rw [h1]; exact hfp) h2
    rwa [hSE] at hmem
  have hD2 : ∀ p (hp : p ∈ Pg E z) (r s : G), r ∈ R → s ∈ S →
      r⁻¹ * p ∈ E → s⁻¹ * p ∈ E → (φ p)⁻¹ * (r⁻¹ * s) ∈ U := by
    intro p hp r s hrR hsS hrp hsp
    have hTE : r⁻¹ * s ∈ E := by
      have h1 : r⁻¹ * s = (r⁻¹ * p) * (p⁻¹ * s) := by group
      rw [h1]
      exact E.mul_mem hrp (by
        have := E.inv_mem hsp
        simpa only [mul_inv_rev, inv_inv] using this)
    obtain ⟨u, huU, hru⟩ : ∃ u ∈ U, rOf p = r * u⁻¹ :=
      ⟨(rOf p)⁻¹ * r, hD1R p hp r hrR hrp, by group⟩
    obtain ⟨v, hvU, hsv⟩ : ∃ v ∈ U, sOf p = s * v⁻¹ :=
      ⟨(sOf p)⁻¹ * s, hD1S p hp s hsS hsp, by group⟩
    have hφ : φ p = u * (r⁻¹ * s) * v⁻¹ := by
      rw [hφ_in p hp, hru, hsv]; group
    have hcomm : u * (r⁻¹ * s) = (r⁻¹ * s) * u := hEab u (hUE huU) (r⁻¹ * s) hTE
    have hz : u * v⁻¹ ∈ U := U.mul_mem huU (U.inv_mem hvU)
    have key : (φ p)⁻¹ * (r⁻¹ * s) = (u * v⁻¹)⁻¹ := by
      rw [hφ, hcomm]; group
    rw [key]
    exact U.inv_mem hz
  have hφmul : ∀ p ∈ Pg E z, ∀ q ∈ Pg E z,
      (φ (p * q))⁻¹ * (φ p * φ q) ∈ U := by
    intro p hp q hq
    have hpqP : p * q ∈ Pg E z := (Pg E z).mul_mem hp hq
    have hpqE : (rOf p * rOf q)⁻¹ * (p * q) ∈ E := by
      obtain ⟨ep, hep, hpep⟩ := (hrOf p hp).2
      obtain ⟨eq', heq, hpeq⟩ := (hrOf q hq).2
      have hstep : (rOf p * rOf q)⁻¹ * (p * q) = (rOf q)⁻¹ * ep * rOf q * eq' := by
        nth_rewrite 2 [hpep]
        nth_rewrite 2 [hpeq]
        group
      rw [hstep]
      exact E.mul_mem
        (by simpa only [inv_inv] using
          hnrmP (rOf q)⁻¹ ((Pg E z).inv_mem (hRP (hrOf q hq).1)) ep hep) heq
    have hpqE' : (sOf p * sOf q)⁻¹ * (p * q) ∈ E := by
      obtain ⟨fp, hfp, hpfp⟩ := (hsOf p hp).2
      obtain ⟨fq, hfq, hpfq⟩ := (hsOf q hq).2
      have hstep : (sOf p * sOf q)⁻¹ * (p * q) = (sOf q)⁻¹ * fp * sOf q * fq := by
        nth_rewrite 2 [hpfp]
        nth_rewrite 2 [hpfq]
        group
      rw [hstep]
      exact E.mul_mem
        (by simpa only [inv_inv] using
          hnrmP (sOf q)⁻¹ ((Pg E z).inv_mem (hSP (hsOf q hq).1)) fp hfp) hfq
    have hw := hD2 (p * q) hpqP (rOf p * rOf q) (sOf p * sOf q)
      (R.mul_mem (hrOf p hp).1 (hrOf q hq).1)
      (S.mul_mem (hsOf p hp).1 (hsOf q hq).1) hpqE hpqE'
    have hφpP : φ p ∈ Pg E z := by
      rw [hφ_in p hp]
      exact (Pg E z).mul_mem ((Pg E z).inv_mem (hRP (hrOf p hp).1)) (hSP (hsOf p hp).1)
    have hδU : (rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹ ∈ U := by
      have := hPP (rOf q)⁻¹ ((Pg E z).inv_mem (hRP (hrOf q hq).1)) (φ p) hφpP
      simpa only [inv_inv] using this
    have hkey : (rOf p * rOf q)⁻¹ * (sOf p * sOf q) =
        ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹) * (φ p * φ q) := by
      rw [hφ_in p hp, hφ_in q hq]; group
    rw [hkey] at hw
    have hφpE : φ p ∈ E := hφE p hp
    have hφqE : φ q ∈ E := hφE q hq
    have hδcomm : ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹) * (φ p * φ q) =
        (φ p * φ q) * ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹) :=
      hEab ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹) (hUE hδU)
        (φ p * φ q) (E.mul_mem hφpE hφqE)
    have heq : (φ (p * q))⁻¹ * (((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹) * (φ p * φ q)) =
        ((φ (p * q))⁻¹ * (φ p * φ q)) * ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹) := by
      rw [hδcomm]; group
    have hXδ : ((φ (p * q))⁻¹ * (φ p * φ q)) *
        ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹) ∈ U := by
      rwa [heq] at hw
    have hlast : (φ (p * q))⁻¹ * (φ p * φ q) =
        (((φ (p * q))⁻¹ * (φ p * φ q)) * ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹)) *
          ((rOf q)⁻¹ * φ p * rOf q * (φ p)⁻¹)⁻¹ := by group
    rw [hlast]
    exact U.mul_mem hXδ (U.inv_mem hδU)
  have hφconj : ∀ a ∈ A, ∀ p ∈ Pg E z,
      (φ (a * p * a⁻¹))⁻¹ * (a * φ p * a⁻¹) ∈ U := by
    intro a ha p hp
    have hapP : a * p * a⁻¹ ∈ Pg E z := hAP a ha p hp
    have hrE' : (a * rOf p * a⁻¹)⁻¹ * (a * p * a⁻¹) ∈ E := by
      obtain ⟨ep, hep, hpep⟩ := (hrOf p hp).2
      have hstep : (a * rOf p * a⁻¹)⁻¹ * (a * p * a⁻¹) = a * ep * a⁻¹ := by
        nth_rewrite 2 [hpep]
        group
      rw [hstep]
      exact hAE a ha ep hep
    have hsE' : (a * sOf p * a⁻¹)⁻¹ * (a * p * a⁻¹) ∈ E := by
      obtain ⟨fp, hfp, hpfp⟩ := (hsOf p hp).2
      have hstep : (a * sOf p * a⁻¹)⁻¹ * (a * p * a⁻¹) = a * fp * a⁻¹ := by
        nth_rewrite 2 [hpfp]
        group
      rw [hstep]
      exact hAE a ha fp hfp
    have hw := hD2 (a * p * a⁻¹) hapP (a * rOf p * a⁻¹) (a * sOf p * a⁻¹)
      (hAR a ha (rOf p) (hrOf p hp).1) (hAS a ha (sOf p) (hsOf p hp).1) hrE' hsE'
    have hval : (a * rOf p * a⁻¹)⁻¹ * (a * sOf p * a⁻¹) = a * φ p * a⁻¹ := by
      rw [hφ_in p hp]; group
    rwa [hval] at hw
  have hφU : ∀ p ∈ Pg E z, φ p ∈ U :=
    hHV U hUE hUinv hUcard φ hφE hφU_E hφmul hφconj
  apply le_antisymm
  · intro x hxR
    have hxP : x ∈ Pg E z := hRP hxR
    have hφxU : φ x ∈ U := hφU x hxP
    obtain ⟨ex, hex, hxex⟩ := (hrOf x hxP).2
    have hexU : (rOf x)⁻¹ * x ∈ U := by
      have hexRE : (rOf x)⁻¹ * x ∈ R ⊓ E := by
        refine ⟨R.mul_mem (R.inv_mem (hrOf x hxP).1) hxR, ?_⟩
        have : (rOf x)⁻¹ * x = ex := by
          nth_rewrite 2 [hxex]
          group
        rw [this]; exact hex
      rwa [hRE] at hexRE
    have hsxU : (sOf x)⁻¹ * x ∈ U := by
      have h1 : (sOf x)⁻¹ * x = (φ x)⁻¹ * ((rOf x)⁻¹ * x) := by
        rw [hφ_in x hxP]; group
      rw [h1]
      exact U.mul_mem (U.inv_mem hφxU) hexU
    have hxs : x = sOf x * ((sOf x)⁻¹ * x) := by group
    rw [hxs]
    exact S.mul_mem (hsOf x hxP).1 (hUS hsxU)
  · intro y hyS
    have hyP : y ∈ Pg E z := hSP hyS
    have hφyU : φ y ∈ U := hφU y hyP
    obtain ⟨fy, hfy, hyfy⟩ := (hsOf y hyP).2
    have hfyU : (sOf y)⁻¹ * y ∈ U := by
      have hfySE : (sOf y)⁻¹ * y ∈ S ⊓ E := by
        refine ⟨S.mul_mem (S.inv_mem (hsOf y hyP).1) hyS, ?_⟩
        have : (sOf y)⁻¹ * y = fy := by
          nth_rewrite 2 [hyfy]
          group
        rw [this]; exact hfy
      rwa [hSE] at hfySE
    have hryU : (rOf y)⁻¹ * y ∈ U := by
      have h1 : (rOf y)⁻¹ * y = φ y * ((sOf y)⁻¹ * y) := by
        rw [hφ_in y hyP]; group
      rw [h1]
      exact U.mul_mem hφyU hfyU
    have hyr : y = rOf y * ((rOf y)⁻¹ * y) := by group
    rw [hyr]
    exact R.mul_mem (hrOf y hyP).1 (hUR hryU)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
