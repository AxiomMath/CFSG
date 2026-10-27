module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Layer

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open Subgroup CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open scoped commutatorElement

theorem eq_one_of_sq_eq_one_of_odd_card {G : Type*} [Group G] (hG : Odd (Nat.card G)) {x : G}
    (hx : x ^ 2 = 1) : x = 1 := by
  have hcop : Nat.Coprime (orderOf x) (Nat.card G) :=
    (Nat.coprime_two_left.2 hG).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hx)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_natCard x))

section Layer

variable {G : Type*} [Group G]

theorem exists_inner_of_fixes_layer (x₀ : G)
    (hcentr : ∀ z ∈ centralizer ({x₀} : Set G) ⊓
        centralizer ((⁅centralizer ({x₀} : Set G), centralizer ({x₀} : Set G)⁆ : Subgroup G) :
          Set G), ∀ u ∈ centralizer ({x₀} : Set G), z * u = u * z)
    (hodd : ∀ z ∈ centralizer ({x₀} : Set G) ⊓
        centralizer ((⁅centralizer ({x₀} : Set G), centralizer ({x₀} : Set G)⁆ : Subgroup G) :
          Set G), z ^ 2 = 1 → z = 1)
    (R₀ : Subgroup G)
    (hR₀le : R₀ ≤ ⁅centralizer ({x₀} : Set G), centralizer ({x₀} : Set G)⁆)
    (hgen : ∀ X : Subgroup G, (∀ u ∈ R₀, u ^ 2 = 1 → u ∈ X) → R₀ ≤ X)
    (hinner : ∀ η : MulAut G, (∀ r ∈ R₀, η r = r) → ∃ c : G, MulAut.conj c = η)
    (η : MulAut G) (hηx : η x₀ = x₀)
    (hηR : ∀ r ∈ (⁅centralizer ({x₀} : Set G), centralizer ({x₀} : Set G)⁆ : Subgroup G),
      η r = r) :
    ∃ c ∈ centralizer ({x₀} : Set G) ⊓
      centralizer ((⁅centralizer ({x₀} : Set G), centralizer ({x₀} : Set G)⁆ : Subgroup G) :
        Set G), η = MulAut.conj c := by
  set DC : Subgroup G := centralizer ({x₀} : Set G) with hDC
  set RC : Subgroup G := ⁅DC, DC⁆ with hRC
  have hinv : ∀ u ∈ DC, u ^ 2 = 1 → η u = u := by
    intro u hu hu2
    obtain ⟨z, hz⟩ : ∃ z, z = η u * u⁻¹ := ⟨_, rfl⟩
    have hηu : η u ∈ DC := by
      rw [hDC, mem_centralizer_singleton_iff] at hu ⊢
      rw [← hηx, ← map_mul, ← map_mul, hu]
    have hzR : z ∈ DC ⊓ centralizer (RC : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hz ▸ mul_mem hηu (inv_mem hu),
        Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      have hconj : (MulAut.conj u⁻¹) x₀ = x₀ := by
        rw [MulAut.conj_apply, (mem_centralizer_singleton_iff.1 (inv_mem hu)),
          mul_inv_cancel_right]
      have hr' : u⁻¹ * r * u ∈ RC := by
        have := apply_mem_derivedCentralizer hconj hr
        rwa [MulAut.conj_apply, inv_inv] at this
      have h1 : η (u⁻¹ * r * u) = u⁻¹ * r * u := hηR _ hr'
      have h2 : η r = r := hηR r hr
      rw [map_mul, map_mul, map_inv] at h1
      have h3 : z * r * z⁻¹ = r := by
        calc z * r * z⁻¹ = η u * (u⁻¹ * r * u) * (η u)⁻¹ := by rw [hz]; group
          _ = η u * ((η u)⁻¹ * η r * η u) * (η u)⁻¹ := by rw [h1]
          _ = r := by rw [h2]; group
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    have hz2 : z ^ 2 = 1 := by
      have hzu : z * u = u * z := hcentr z hzR u hu
      have h1 : η u = z * u := by rw [hz, inv_mul_cancel_right]
      calc z ^ 2 = z ^ 2 * u ^ 2 := by rw [hu2, mul_one]
        _ = (z * u) ^ 2 := (Commute.mul_pow hzu 2).symm
        _ = η (u ^ 2) := by rw [map_pow, h1]
        _ = 1 := by rw [hu2, map_one]
    have hz1 : z = 1 := hodd z hzR hz2
    rw [hz] at hz1
    exact mul_inv_eq_one.1 hz1
  have hfixR₀ : ∀ r ∈ R₀, η r = r := fun r hr =>
    hgen (MonoidHom.eqLocus η.toMonoidHom (MonoidHom.id _))
      (fun u hu hu2 => hinv u (derivedCentralizer_le x₀ (hR₀le hu)) hu2) hr
  obtain ⟨c, hc⟩ := hinner η hfixR₀
  refine ⟨c, Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
    Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, hc.symm⟩
  · have h1 := hηx
    rw [← hc, MulAut.conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  · have h1 := hηR r hr
    rw [← hc, MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

end Layer

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem centralizer_layer_of_transport (ι : G →* H) (hι : Function.Injective ι) (c : MulAut H)
    (C : Subgroup G) (D : Subgroup H) (hC : C.map ι = D.map c.toMonoidHom)
    (hcentD : D ⊓ centralizer ((⁅D, D⁆ : Subgroup H) : Set H) = (center D).map D.subtype)
    (hZodd : Odd (Nat.card (center D))) :
    (⁅C, C⁆.map ι = ⁅D, D⁆.map c.toMonoidHom) ∧
    (∀ y ∈ C ⊓ centralizer ((⁅C, C⁆ : Subgroup G) : Set G),
      ∃ d ∈ D ⊓ centralizer ((⁅D, D⁆ : Subgroup H) : Set H), ι y = c d) ∧
    (∀ z ∈ C ⊓ centralizer ((⁅C, C⁆ : Subgroup G) : Set G), ∀ u ∈ C, z * u = u * z) ∧
    (∀ z ∈ C ⊓ centralizer ((⁅C, C⁆ : Subgroup G) : Set G), z ^ 2 = 1 → z = 1) := by
  have hR : ⁅C, C⁆.map ι = ⁅D, D⁆.map c.toMonoidHom := by
    rw [Subgroup.map_commutator, hC, Subgroup.map_commutator]
  have hdz : ∀ y ∈ C ⊓ centralizer ((⁅C, C⁆ : Subgroup G) : Set G),
      ∃ d ∈ D ⊓ centralizer ((⁅D, D⁆ : Subgroup H) : Set H), ι y = c d := by
    rintro y ⟨hyC, hyR⟩
    have h1 : ι y ∈ C.map ι := ⟨y, hyC, rfl⟩
    rw [hC] at h1
    obtain ⟨d, hdD, hdy⟩ := h1
    refine ⟨d, Subgroup.mem_inf.2 ⟨hdD, ?_⟩, hdy.symm⟩
    rw [mem_centralizer_iff]
    intro r hr
    have hr' : c.toMonoidHom r ∈ ⁅C, C⁆.map ι := by
      rw [hR]
      exact ⟨r, hr, rfl⟩
    obtain ⟨r', hr'R, hr'e⟩ := hr'
    have hc' := mem_centralizer_iff.1 hyR r' hr'R
    have hdy' : c d = ι y := hdy
    have hr'e' : ι r' = c r := hr'e
    apply c.injective
    rw [map_mul c r d, map_mul c d r, hdy', ← hr'e', ← map_mul ι, ← map_mul ι, hc']
  have hcentr : ∀ z ∈ C ⊓ centralizer ((⁅C, C⁆ : Subgroup G) : Set G), ∀ u ∈ C,
      z * u = u * z := by
    intro z hz u hu
    obtain ⟨d, hdDR, hdy⟩ := hdz z hz
    have hdZ : d ∈ (Subgroup.center D).map D.subtype := hcentD ▸ hdDR
    obtain ⟨zD, hzD, hzDd⟩ := hdZ
    have h1 : ι u ∈ C.map ι := ⟨u, hu, rfl⟩
    rw [hC] at h1
    obtain ⟨du, hduD, hdu⟩ := h1
    have hdu' : c du = ι u := hdu
    have hcomm : d * du = du * d := by
      have := Subgroup.mem_center_iff.1 hzD ⟨du, hduD⟩
      rw [← hzDd]
      exact (congrArg Subtype.val this).symm
    apply hι
    rw [map_mul, map_mul, hdy, ← hdu', ← map_mul c, ← map_mul c, hcomm]
  refine ⟨hR, hdz, hcentr, fun z hz hz2 => ?_⟩
  obtain ⟨d, hdDR, hdy⟩ := hdz z hz
  have hdZ : d ∈ (Subgroup.center D).map D.subtype := hcentD ▸ hdDR
  obtain ⟨zD, hzD, hzDd⟩ := hdZ
  have hd2 : d ^ 2 = 1 := by
    apply c.injective
    rw [map_pow, ← hdy, ← map_pow, hz2, map_one, map_one]
  have hz2' : (⟨zD, hzD⟩ : ↥(Subgroup.center D)) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [← hzDd] using hd2
  have hzD1 := eq_one_of_sq_eq_one_of_odd_card hZodd hz2'
  have hd1 : d = 1 := by
    rw [← hzDd]
    have : zD = 1 := congrArg Subtype.val hzD1
    rw [this]
    rfl
  apply hι
  rw [hdy, hd1, map_one, map_one]

end Transport

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
