module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Cent

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

theorem field_involution_facts {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    {x : PGammaL2 F} (hx2 : x * x = 1) (hxr : x.right ≠ 1) :
    orderOf x = 2 ∧ orderOf x.right = 2 ∧ Even f := by
  have hx1 : x ≠ 1 := fun h => hxr (by rw [h]; rfl)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hσσ : x.right * x.right = 1 := by
    have := congrArg SemidirectProduct.right hx2
    simpa using this
  refine ⟨hxo, orderOf_eq_prime (by rw [sq]; exact hσσ) hxr, ?_⟩
  exact even_of_right_ne_one hp hF x (k := 1) (by rw [pow_one, sq]; exact hx2) hxr

theorem conj_centralizer_l2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (R : Sylow 2 Y) (β : MulAut Y) (hβ : β ∉ linL2 e)
    (hβ2 : β * β = 1) :
    ∃ g : Y, ∀ r ∈ (R : Subgroup Y), (MulAut.conj g * β * (MulAut.conj g)⁻¹) r = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  set x := autEquiv e β with hx
  have hx2 : x * x = 1 := by rw [hx, ← map_mul, hβ2, map_one]
  have hxr : x.right ≠ 1 := hβ
  obtain ⟨hxo, hσ, hfe⟩ := field_involution_facts hp hF hx2 hxr
  obtain ⟨hsq, hq4, hn⟩ := model_hyps_of_even hp hp2 hf hF hfe
  obtain ⟨y₀, hy₀r, hy₀2, hy₀C⟩ := exists_field_central hodd hsq hn hp hp2 hF x.right hσ
  have hy₀r1 : y₀.right ≠ 1 := by rw [hy₀r]; exact hxr
  obtain ⟨hy₀o, -, -⟩ := field_involution_facts hp hF hy₀2 hy₀r1
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd x hxo hxr
  obtain ⟨C₀, hC₀⟩ := exists_conj_inr_of_involution hodd y₀ hy₀o hy₀r1
  set g : PGammaL2 F := SemidirectProduct.inl C * (SemidirectProduct.inl C₀)⁻¹ with hg
  have hxg : x = g * y₀ * g⁻¹ := by
    have h1 : x = SemidirectProduct.inl C * SemidirectProduct.inr x.right *
        (SemidirectProduct.inl C)⁻¹ := by rw [← hC]; group
    have h2 : SemidirectProduct.inr x.right = (SemidirectProduct.inl C₀)⁻¹ * y₀ *
        SemidirectProduct.inl C₀ := by rw [hC₀, hy₀r]
    rw [h1, h2, hg]
    group
  set φ := semilinearAction F g with hφ
  have hsurj : Function.Surjective φ.toMonoidHom := φ.surjective
  set S₁ : Sylow 2 (PSL2 F) := (stdSylow F hodd hsq hq4).mapSurjective hsurj with hS₁
  have hS₁mem : ∀ d, d ∈ (S₁ : Subgroup (PSL2 F)) ↔ φ.symm d ∈ stdT F := fun d => by
    rw [hS₁, Sylow.coe_mapSurjective, mem_map_equiv, coe_stdSylow]
  have hxS₁ : ∀ d ∈ (S₁ : Subgroup (PSL2 F)), x * incl F d = incl F d * x := by
    intro d hd
    have ht : incl F (φ.symm d) ∈ (stdT F).map (incl F) := ⟨_, (hS₁mem d).mp hd, rfl⟩
    have h1 : incl F d = g * incl F (φ.symm d) * g⁻¹ := by
      rw [conj_incl, ← hφ, MulEquiv.apply_symm_apply]
    rw [h1, hxg]
    have h2 := hy₀C _ ht
    calc g * y₀ * g⁻¹ * (g * incl F (φ.symm d) * g⁻¹)
        = g * (y₀ * incl F (φ.symm d)) * g⁻¹ := by group
      _ = g * (incl F (φ.symm d) * y₀) * g⁻¹ := by rw [h2]
      _ = g * incl F (φ.symm d) * g⁻¹ * (g * y₀ * g⁻¹) := by group
  have hesurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  set R₁ : Sylow 2 Y := S₁.mapSurjective hesurj with hR₁
  have hR₁fix : ∀ r ∈ (R₁ : Subgroup Y), β r = r := by
    intro r hr
    rw [hR₁, Sylow.coe_mapSurjective, mem_map_equiv, MulEquiv.symm_symm] at hr
    exact (apply_eq_iff_commute e β r).mpr (hxS₁ _ hr)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq Y R₁ R
  refine ⟨h, fun r hr => ?_⟩
  have hr' : h⁻¹ * r * h ∈ (R₁ : Subgroup Y) := by
    rw [← mem_smul_sylow_iff, hh]
    exact hr
  rw [MulAut.mul_apply, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, MulAut.conj_apply,
    inv_inv, hR₁fix _ hr']
  group

theorem field_inner_l2 {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (R : Sylow 2 Y)
    (β : MulAut Y) (hβ : β ∉ linL2 e) (hβ2 : β * β = 1)
    (hmap : (R : Subgroup Y).map β.toMonoidHom = R) :
    ∃ r₀ ∈ (R : Subgroup Y), r₀ * r₀ = 1 ∧ ∀ r ∈ (R : Subgroup Y), β r = r₀ * r * r₀⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  set x := autEquiv e β with hx
  have hx2 : x * x = 1 := by rw [hx, ← map_mul, hβ2, map_one]
  have hxr : x.right ≠ 1 := hβ
  obtain ⟨-, -, hfe⟩ := field_involution_facts hp hF hx2 hxr
  obtain ⟨hsq, hq4, hn⟩ := model_hyps_of_even hp hp2 hf hF hfe
  set D := sylowMap e R with hD
  obtain ⟨h, hh⟩ := exists_conj_stdT hodd hsq hq4 D
  have hβR : ∀ r ∈ (R : Subgroup Y), β r ∈ (R : Subgroup Y) := fun r hr => by
    rw [← hmap]
    exact mem_map_of_mem _ hr
  have hxD : ∀ d ∈ (D : Subgroup (PSL2 F)), ∃ d' ∈ (D : Subgroup (PSL2 F)),
      x * incl F d * x⁻¹ = incl F d' := by
    intro d hd
    have h1 : e.symm d ∈ (R : Subgroup Y) := by
      rw [← mem_sylowMap_iff e R, MulEquiv.apply_symm_apply]
      exact hd
    refine ⟨e (β (e.symm d)), (mem_sylowMap_iff e R _).mpr (hβR _ h1), ?_⟩
    rw [conj_incl, hx, ← semilinearAction_autEquiv_apply, MulEquiv.apply_symm_apply]
  set x' := (incl F h)⁻¹ * x * incl F h with hx'
  have hx'T : ∀ g ∈ (stdT F).map (incl F), x' * g * x'⁻¹ ∈ (stdT F).map (incl F) := by
    rintro _ ⟨t, ht, rfl⟩
    have hd : h * t * h⁻¹ ∈ (D : Subgroup (PSL2 F)) := by
      rw [hh, show h⁻¹ * (h * t * h⁻¹) * h = t by group]
      exact ht
    obtain ⟨d', hd', hxd'⟩ := hxD _ hd
    refine ⟨h⁻¹ * d' * h, (hh d').mp hd', ?_⟩
    rw [map_mul, map_mul, map_inv, ← hxd', map_mul, map_mul, map_inv, hx']
    group
  have hx'2 : x' * x' = 1 := by
    calc x' * x' = (incl F h)⁻¹ * (x * x) * incl F h := by rw [hx']; group
      _ = 1 := by rw [hx2, mul_one, inv_mul_cancel]
  have hx'r : x'.right = x.right := by rw [hx']; simp [incl_apply]
  have hT₀ : IsPGroup 2 ((stdT F).map (incl F)) := by
    rw [← coe_stdSylow hodd hsq hq4]
    exact (stdSylow F hodd hsq hq4).isPGroup'.map _
  have hx'p : IsPGroup 2 (zpowers x') :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [sq]; exact hx'2) (fun h1 => hxr (by
        rw [← hx'r, h1]; rfl)))
  have hle : zpowers x' ≤ normalizer (((stdT F).map (incl F) : Subgroup (PGammaL2 F)) :
      Set (PGammaL2 F)) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hx'T g hg, fun hg => ?_⟩
    have h1 := hx'T _ hg
    have hinv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
    rwa [hinv, show x' * (x' * g * x') * x' = g by
      calc x' * (x' * g * x') * x' = (x' * x') * g * (x' * x') := by group
        _ = g := by rw [hx'2, one_mul, mul_one]] at h1
  have hRp := IsPGroup.to_sup_of_normal_right' hx'p hT₀ hle
  obtain ⟨t, ht, w, -, hwC, hxtw⟩ := decomp_fieldInv hp hp2 hF hodd hsq hq4 hn
    (zpowers x' ⊔ (stdT F).map (incl F)) hRp le_sup_right x' (mem_sup_left (mem_zpowers x'))
    hx'2 (by rw [hx'r]; exact hxr)
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  have hwr : w.right = x.right := by
    have h1 : x'.right = (incl F t₀ * w).right := congrArg _ hxtw
    have h2 : (incl F t₀ * w).right = w.right := by simp [incl_apply]
    rw [← h2, ← h1, hx'r]
  have hσσ : x.right * x.right = 1 := by
    have := congrArg SemidirectProduct.right hx2
    simpa using this
  have hw2 : w * w = 1 := mul_self_of_centralizes_stdT hodd hsq hn w hwC (by rw [hwr]; exact hσσ)
  have htw : w * incl F t₀ = incl F t₀ * w := hwC _ ⟨t₀, ht₀, rfl⟩
  have ht2 : t₀ * t₀ = 1 := by
    apply incl_injective F
    rw [map_mul, map_one]
    have h1 : incl F t₀ * w * (incl F t₀ * w) = incl F t₀ * incl F t₀ * (w * w) := by
      calc incl F t₀ * w * (incl F t₀ * w) = incl F t₀ * (w * incl F t₀) * w := by group
        _ = incl F t₀ * (incl F t₀ * w) * w := by rw [htw]
        _ = incl F t₀ * incl F t₀ * (w * w) := by group
    rw [hw2, mul_one, ← hxtw, hx'2] at h1
    exact h1.symm
  have hr₀D : h * t₀ * h⁻¹ ∈ (D : Subgroup (PSL2 F)) := by
    rw [hh, show h⁻¹ * (h * t₀ * h⁻¹) * h = t₀ by group]
    exact ht₀
  have hr₀R : e.symm (h * t₀ * h⁻¹) ∈ (R : Subgroup Y) := by
    rw [← mem_sylowMap_iff e R, MulEquiv.apply_symm_apply]
    exact hr₀D
  refine ⟨e.symm (h * t₀ * h⁻¹), hr₀R, ?_, fun r hr => e.injective ?_⟩
  · apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, map_one]
    calc h * t₀ * h⁻¹ * (h * t₀ * h⁻¹) = h * (t₀ * t₀) * h⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  · have her : h⁻¹ * e r * h ∈ stdT F := (hh (e r)).mp ((mem_sylowMap_iff e R r).mpr hr)
    have hw' : w * incl F (h⁻¹ * e r * h) = incl F (h⁻¹ * e r * h) * w :=
      hwC _ ⟨_, her, rfl⟩
    apply incl_injective F
    have hxeq : x = incl F h * (incl F t₀ * w) * (incl F h)⁻¹ := by
      rw [← hxtw, hx']
      group
    rw [← semilinearAction_autEquiv_apply, ← hx, ← conj_incl, hxeq]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have hw'' : w * ((incl F h)⁻¹ * incl F (e r) * incl F h) =
        ((incl F h)⁻¹ * incl F (e r) * incl F h) * w := by
      simpa only [map_mul, map_inv] using hw'
    calc incl F h * (incl F t₀ * w) * (incl F h)⁻¹ * incl F (e r) *
          (incl F h * (incl F t₀ * w) * (incl F h)⁻¹)⁻¹
        = incl F h * incl F t₀ * (w * ((incl F h)⁻¹ * incl F (e r) * incl F h)) * w⁻¹ *
            (incl F t₀)⁻¹ * (incl F h)⁻¹ := by group
      _ = incl F h * incl F t₀ * (((incl F h)⁻¹ * incl F (e r) * incl F h) * w) * w⁻¹ *
            (incl F t₀)⁻¹ * (incl F h)⁻¹ := by rw [hw'']
      _ = _ := by group

end CFSG.ComponentClassification.FooteLit.Aut5L2
