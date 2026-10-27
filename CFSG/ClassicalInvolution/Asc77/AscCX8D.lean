module

public import CFSG.ClassicalInvolution.Asc77.AscCX8C

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Sylow

variable {G : Type} [Group G] [Finite G]

open CFSG.ClassicalInvolution.Disconnected.AschTight.S1916 in
theorem exists_conj_le_of_isSylow2In {P H : Subgroup G} (hP : IsSylow2In P H)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTH : T ≤ H) :
    ∃ c ∈ H, ∀ x ∈ T, c⁻¹ * x * c ∈ P := by
  obtain ⟨V, hV, hTV⟩ := IsSylow2In.exists_ge hT2 hTH
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥H) (sylowOf hV) (sylowOf hP)
  rw [coe_sylowOf, coe_sylowOf] at hx
  have hVx : conjSub (x : G) V ≤ H := by
    have := conjSub_mono (n := (x : G)) hV.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have h1 : (conjSub (x : G) V).subgroupOf H = P.subgroupOf H := by
    have e : (conjSub (x : G) V).subgroupOf H = conjSub x (V.subgroupOf H) := by
      ext y
      rw [Subgroup.mem_subgroupOf, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_subgroupOf]
      simp
    rw [e]
    exact hx
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rw [inf_eq_left.mpr hVx, inf_eq_left.mpr hP.1] at h2
  refine ⟨(x : G)⁻¹, H.inv_mem x.2, fun t ht => ?_⟩
  have h3 : (x : G) * t * (x : G)⁻¹ ∈ conjSub (x : G) V :=
    mem_conjSub_iff.mpr (by simpa [mul_assoc] using hTV ht)
  rw [h2] at h3
  simpa [mul_assoc] using h3

theorem not_conj_of_escape {S N : Subgroup G} {z : G}
    (hsc : ∀ n ∈ N, ∀ c : G, c * z * c⁻¹ = z → c * n * c⁻¹ ∈ S → c * n * c⁻¹ ∈ N)
    {e g : G} (he : e ∈ N) (hgS : g * e * g⁻¹ ∈ S) (hgN : g * e * g⁻¹ ∉ N) :
    ∀ h ∈ Subgroup.centralizer ({e} : Set G), h * z * h⁻¹ ≠ g⁻¹ * z * g := by
  intro h hh heq
  apply hgN
  have hhe : h * e = e * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hcz : (g * h) * z * (g * h)⁻¹ = z := by
    calc (g * h) * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [heq]
      _ = z := by group
  have hce : (g * h) * e * (g * h)⁻¹ = g * e * g⁻¹ := by
    calc (g * h) * e * (g * h)⁻¹ = g * (h * e) * h⁻¹ * g⁻¹ := by group
      _ = g * (e * h) * h⁻¹ * g⁻¹ := by rw [hhe]
      _ = g * e * g⁻¹ := by group
  have := hsc e he (g * h) hcz (by rw [hce]; exact hgS)
  rwa [hce] at this

theorem exists_placed {S : Sylow 2 G} {z : G} (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hz2 : z * z = 1) {N : Subgroup G} (hNS : N ≤ (S : Subgroup G))
    (hsc : ∀ n ∈ N, ∀ c : G, c * z * c⁻¹ = z → c * n * c⁻¹ ∈ (S : Subgroup G) →
      c * n * c⁻¹ ∈ N)
    {e₀ k : G} (he₀ : e₀ ∈ N) (hkS : k * e₀ * k⁻¹ ∈ (S : Subgroup G))
    (hkN : k * e₀ * k⁻¹ ∉ N) :
    ∃ e ∈ N, e ≠ 1 ∧ ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({e} : Set G) ∧
      (g * z * g⁻¹) * z = z * (g * z * g⁻¹) ∧
      ∀ h ∈ Subgroup.centralizer ({e} : Set G), h * z * h⁻¹ ≠ g * z * g⁻¹ := by
  classical
  have he₀1 : e₀ ≠ 1 := by
    rintro rfl
    apply hkN
    simp
  have he₀S : e₀ ∈ (S : Subgroup G) := hNS he₀
  have hE2 : IsPGroup 2 (Subgroup.zpowers e₀) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr he₀S)
  have hEC : Subgroup.zpowers e₀ ≤ Subgroup.centralizer ({e₀} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨P, hP, hEP⟩ := IsSylow2In.exists_ge hE2 hEC
  obtain ⟨c, -, hcP⟩ := C25W.exists_conj_ge_sylow (S := S) le_top hP.2.1 le_top
  have he₀P : e₀ ∈ P := hEP (Subgroup.mem_zpowers e₀)
  have hesS : c⁻¹ * e₀ * c ∈ (S : Subgroup G) := hcP e₀ he₀P
  have hzc : ∀ y ∈ P, y * (c * z * c⁻¹) = (c * z * c⁻¹) * y := by
    intro y hy
    have h1 := hzS _ (hcP y hy)
    calc y * (c * z * c⁻¹) = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
      _ = (c * z * c⁻¹) * y := by group
  by_cases hesN : c⁻¹ * e₀ * c ∈ N
  ·
    set es := c⁻¹ * e₀ * c with hes
    set gs := k * c with hgs
    have hgse : gs * es * gs⁻¹ = k * e₀ * k⁻¹ := by rw [hgs, hes]; group
    have hnc := not_conj_of_escape hsc hesN (by rw [hgse]; exact hkS) (by rw [hgse]; exact hkN)
    have hkz := hzS _ hkS
    have hts : (gs⁻¹ * z * gs) * es = es * (gs⁻¹ * z * gs) := by
      calc (gs⁻¹ * z * gs) * es = gs⁻¹ * (z * (gs * es * gs⁻¹)) * gs := by group
        _ = gs⁻¹ * ((gs * es * gs⁻¹) * z) * gs := by rw [hgse, hkz]
        _ = es * (gs⁻¹ * z * gs) := by group
    set u := c * (gs⁻¹ * z * gs) * c⁻¹ with hu
    have hue : u * e₀ = e₀ * u := by
      calc u * e₀ = c * ((gs⁻¹ * z * gs) * es) * c⁻¹ := by rw [hu, hes]; group
        _ = c * (es * (gs⁻¹ * z * gs)) * c⁻¹ := by rw [hts]
        _ = e₀ * u := by rw [hu, hes]; group
    have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
      refine isPGroup_zpowers_of_sq_eq_one ?_
      calc u * u = c * gs⁻¹ * (z * z) * gs * c⁻¹ := by rw [hu]; group
        _ = 1 := by rw [hz2]; group
    obtain ⟨h, hhC, hhP⟩ := exists_conj_le_of_isSylow2In hP hu2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hue))
    have hhe : h * e₀ = e₀ * h := Subgroup.mem_centralizer_singleton_iff.mp hhC
    set m := c⁻¹ * h * c with hm
    have hme : m * es = es * m := by
      calc m * es = c⁻¹ * (h * e₀) * c := by rw [hm, hes]; group
        _ = c⁻¹ * (e₀ * h) * c := by rw [hhe]
        _ = es * m := by rw [hm, hes]; group
    have ht'eq : (m⁻¹ * gs⁻¹) * z * (m⁻¹ * gs⁻¹)⁻¹ = c⁻¹ * (h⁻¹ * u * h) * c := by
      rw [hm, hu]
      group
    refine ⟨es, hesN, ?_, m⁻¹ * gs⁻¹, ?_, ?_, ?_⟩
    · intro h1
      apply he₀1
      calc e₀ = c * es * c⁻¹ := by rw [hes]; group
        _ = 1 := by rw [h1]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hmi : m⁻¹ * es = es * m⁻¹ := by
        calc m⁻¹ * es = m⁻¹ * (es * m) * m⁻¹ := by group
          _ = m⁻¹ * (m * es) * m⁻¹ := by rw [hme]
          _ = es * m⁻¹ := by group
      calc (m⁻¹ * gs⁻¹) * z * (m⁻¹ * gs⁻¹)⁻¹ * es =
          m⁻¹ * ((gs⁻¹ * z * gs) * (m * es)) := by group
        _ = m⁻¹ * ((gs⁻¹ * z * gs) * (es * m)) := by rw [hme]
        _ = m⁻¹ * (((gs⁻¹ * z * gs) * es) * m) := by group
        _ = m⁻¹ * ((es * (gs⁻¹ * z * gs)) * m) := by rw [hts]
        _ = (m⁻¹ * es) * ((gs⁻¹ * z * gs) * m) := by group
        _ = (es * m⁻¹) * ((gs⁻¹ * z * gs) * m) := by rw [hmi]
        _ = es * ((m⁻¹ * gs⁻¹) * z * (m⁻¹ * gs⁻¹)⁻¹) := by group
    · rw [ht'eq]
      exact (hzS _ (hcP _ (hhP u (Subgroup.mem_zpowers u))))
    · intro h' hh' heq
      apply hnc (m * h') (Subgroup.mul_mem _
        (Subgroup.mem_centralizer_singleton_iff.mpr hme) hh')
      calc m * h' * z * (m * h')⁻¹ = m * (h' * z * h'⁻¹) * m⁻¹ := by group
        _ = m * ((m⁻¹ * gs⁻¹) * z * (m⁻¹ * gs⁻¹)⁻¹) * m⁻¹ := by rw [heq]
        _ = gs⁻¹ * z * gs := by group
  ·
    have hnc := not_conj_of_escape hsc he₀ (g := c⁻¹) (by simpa using hesS)
      (by simpa using hesN)
    simp only [inv_inv] at hnc
    have hzC : z ∈ Subgroup.centralizer ({e₀} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzS e₀ he₀S).symm
    obtain ⟨h, hhC, hhP⟩ := exists_conj_le_of_isSylow2In hP (isPGroup_zpowers_of_sq_eq_one hz2)
      (Subgroup.zpowers_le.mpr hzC)
    have hhe : h * e₀ = e₀ * h := Subgroup.mem_centralizer_singleton_iff.mp hhC
    have hw := hzc _ (hhP z (Subgroup.mem_zpowers z))
    have hte : (c * z * c⁻¹) * e₀ = e₀ * (c * z * c⁻¹) := (hzc e₀ he₀P).symm
    refine ⟨e₀, he₀, he₀1, h * c, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hhe' : h⁻¹ * e₀ = e₀ * h⁻¹ := by
        calc h⁻¹ * e₀ = h⁻¹ * (e₀ * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * e₀) * h⁻¹ := by rw [hhe]
          _ = e₀ * h⁻¹ := by group
      calc h * c * z * (h * c)⁻¹ * e₀ = h * ((c * z * c⁻¹) * (h⁻¹ * e₀)) := by group
        _ = h * ((c * z * c⁻¹) * (e₀ * h⁻¹)) := by rw [hhe']
        _ = h * (((c * z * c⁻¹) * e₀) * h⁻¹) := by group
        _ = h * ((e₀ * (c * z * c⁻¹)) * h⁻¹) := by rw [hte]
        _ = (h * e₀) * ((c * z * c⁻¹) * h⁻¹) := by group
        _ = (e₀ * h) * ((c * z * c⁻¹) * h⁻¹) := by rw [hhe]
        _ = e₀ * (h * c * z * (h * c)⁻¹) := by group
    · calc h * c * z * (h * c)⁻¹ * z = h * ((c * z * c⁻¹) * (h⁻¹ * z * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * z * h) * (c * z * c⁻¹)) * h⁻¹ := by rw [← hw]
        _ = z * (h * c * z * (h * c)⁻¹) := by group
    · intro h' hh' heq
      apply hnc (h⁻¹ * h') (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhC) hh')
      calc h⁻¹ * h' * z * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * z * h'⁻¹) * h := by group
        _ = h⁻¹ * (h * c * z * (h * c)⁻¹) * h := by rw [heq]
        _ = c * z * c⁻¹ := by group

end Sylow

section CaseOne

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}



theorem false_of_mixedClosed (h6 : Layer6Twin p f) (hM6 : C25Y.Layer6Cen4 p f)
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {N : Subgroup G}
    (hNA : N ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hN1 : N ≠ ⊥)
    (hsc : ∀ n ∈ N, ∀ c : G, c * z * c⁻¹ = z → c * n * c⁻¹ ∈ (S : Subgroup G) →
      c * n * c⁻¹ ∈ N)
    (hbad : ∀ n ∈ N, n ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({n} : Set G)))
    (hgood : ∀ n ∈ N, n ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({n * z} : Set G))) :
    False := by
  by_cases hG : fusionStronglyClosed (N : Set G) S
  · exact false_of_stronglyClosed hyp hNA hN1 hG
  · unfold fusionStronglyClosed at hG
    push Not at hG
    obtain ⟨a, haN, g, hgS, hgN⟩ := hG
    obtain ⟨e, heN, -, g', htC, htz, hnc⟩ := exists_placed (S := S) hyp.hzS
      hyp.std.setting.hz.sq (hNA.trans inf_le_left) hsc haN (k := g⁻¹)
      (by simpa using hgS) (by simpa using hgN)
    obtain ⟨h, hhC, hh⟩ := goodFusion_of_placed h6 hM6 hyp hNA hsc hbad hgood heN htC htz
    exact hnc h hhC hh

end CaseOne

end CFSG.ClassicalInvolution.Asc77.CX
