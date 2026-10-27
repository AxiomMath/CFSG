module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04z
public import CFSG.ClassicalInvolution.Asc77.AscS24BKC
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF05

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem conj_z_of_mem_sup (hg0 : ∃ g₀ ∈ Subgroup.normalizer (W : Set G), g₀⁻¹ * z * g₀ = u)
    (hfus : ∀ {u₁ u₂ : G}, u₁ ∈ K ⊔ K' → u₁ ≠ 1 → u₁ ≠ z → u₁ * u₁ = 1 → u₂ ∈ K ⊔ K' → u₂ ≠ 1 →
      u₂ ≠ z → u₂ * u₂ = 1 → ∃ c : G, c * u₁ * c⁻¹ = u₂)
    {t : G} (ht : t ∈ K ⊔ K') (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : ∃ g : G, g * z * g⁻¹ = t := by
  by_cases htz : t = z
  · exact ⟨1, by rw [htz]; group⟩
  obtain ⟨g₀, -, hg₀⟩ := hg0
  obtain ⟨c, hc⟩ := hfus C.hd.hu.1 C.hd.hu.2.2.2.1
    C.hd.hu.2.2.2.2 C.hd.hu.2.2.1 ht ht1 htz ht2
  refine ⟨c * g₀⁻¹, ?_⟩
  rw [← hc, ← hg₀]
  group

include C in
theorem conj_z_of_coset (hg0 : ∃ g₀ ∈ Subgroup.normalizer (W : Set G), g₀⁻¹ * z * g₀ = u)
    (hfus : ∀ {u₁ u₂ : G}, u₁ ∈ K ⊔ K' → u₁ ≠ 1 → u₁ ≠ z → u₁ * u₁ = 1 → u₂ ∈ K ⊔ K' → u₂ ≠ 1 →
      u₂ ≠ z → u₂ * u₂ = 1 → ∃ c : G, c * u₁ * c⁻¹ = u₂)
    {a t₁ : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (ha2 : a * a ∈ W) (hmem : ∀ w ∈ W, a * w * (a * w) = 1 → a * w ∈ K ⊔ K')
    (ht : a⁻¹ * t₁ ∈ W ⊔ OCW W) (ht2 : t₁ * t₁ = 1) (ht1 : t₁ ≠ 1) :
    ∃ g : G, g * z * g⁻¹ = t₁ := by
  obtain ⟨w, hw, hw2, o, -, ho⟩ :=
    exists_conj_of_mem_coset (Thompson.isPGroup_of_mem_WSet C.hd.hW) ha ha2 ht ht2
  have hne : a * w ≠ 1 := by
    intro h; apply ht1; rw [← ho, h]; group
  obtain ⟨g, hg⟩ := C.conj_z_of_mem_sup hg0 hfus (hmem w hw hw2) hw2 hne
  exact ⟨o * g, by rw [← ho, ← hg]; group⟩

include C in
theorem kc_aux (hg0 : ∃ g₀ ∈ Subgroup.normalizer (W : Set G), g₀⁻¹ * z * g₀ = u)
    (hfus : ∀ {u₁ u₂ : G}, u₁ ∈ K ⊔ K' → u₁ ≠ 1 → u₁ ≠ z → u₁ * u₁ = 1 → u₂ ∈ K ⊔ K' → u₂ ≠ 1 →
      u₂ ≠ z → u₂ * u₂ = 1 → ∃ c : G, c * u₁ * c⁻¹ = u₂)
    {t : G} (htM : t ∈ MGrp Ω W) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    {a : G} (haM : a ∈ MGrp Ω W) (ha2 : a * a ∈ W)
    (hmem : ∀ w ∈ W, a * w * (a * w) = 1 → a * w ∈ K ⊔ K') {m : ↥(MGrp Ω W)}
    (e : piM Ω W m * piM Ω W ⟨a, haM⟩ * (piM Ω W m)⁻¹ = piM Ω W ⟨t, htM⟩) :
    ∃ g : G, g * z * g⁻¹ = t := by
  have hmN : (m : G) ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W m.2
  have haN : a ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W haM
  have htN : t ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W htM
  have ht₁N : (m : G)⁻¹ * t * m ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) htN) hmN
  have e' : Thompson.piG W (m : G) * Thompson.piG W a * (Thompson.piG W (m : G))⁻¹ =
      Thompson.piG W t := congrArg Subtype.val e
  have hpi : Thompson.piG W a = Thompson.piG W ((m : G)⁻¹ * t * m) := by
    rw [Thompson.piG_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) htN) hmN,
      Thompson.piG_mul (Subgroup.inv_mem _ hmN) htN, Thompson.piG_inv hmN, ← e']
    group
  have hmem' := (Thompson.piG_eq_iff haN ht₁N).mp hpi
  have ht₁2 : (m : G)⁻¹ * t * m * ((m : G)⁻¹ * t * m) = 1 := by
    calc (m : G)⁻¹ * t * m * ((m : G)⁻¹ * t * m) = (m : G)⁻¹ * (t * t) * m := by group
      _ = 1 := by rw [ht2]; group
  have ht₁1 : (m : G)⁻¹ * t * m ≠ 1 := by
    intro h; apply ht1
    calc t = (m : G) * ((m : G)⁻¹ * t * m) * (m : G)⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨g, hg⟩ := C.conj_z_of_coset hg0 hfus haN ha2 hmem hmem' ht₁2 ht₁1
  refine ⟨(m : G) * g, ?_⟩
  calc (m : G) * g * z * ((m : G) * g)⁻¹ = (m : G) * (g * z * g⁻¹) * (m : G)⁻¹ := by group
    _ = t := by rw [hg]; group

include C in
theorem kc (hg0 : ∃ g₀ ∈ Subgroup.normalizer (W : Set G), g₀⁻¹ * z * g₀ = u)
    (hfus : ∀ {u₁ u₂ : G}, u₁ ∈ K ⊔ K' → u₁ ≠ 1 → u₁ ≠ z → u₁ * u₁ = 1 → u₂ ∈ K ⊔ K' → u₂ ≠ 1 →
      u₂ ≠ z → u₂ * u₂ = 1 → ∃ c : G, c * u₁ * c⁻¹ = u₂)
    {t : G} (htS : t ∈ (S : Subgroup G)) (htM : t ∈ MGrp Ω W)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : ∃ g : G, g * z * g⁻¹ = t := by
  by_cases htW : t ∈ W
  · exact C.conj_z_of_mem_sup hg0 hfus (C.mem_sup_of_mul_self htW ht2) ht2 ht1
  have hW2 := Thompson.isPGroup_of_mem_WSet C.hd.hW
  have htN : t ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W htM
  set τ := piM Ω W ⟨t, htM⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : (⟨t, htM⟩ : ↥(MGrp Ω W)) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have h1 : Thompson.piG W t = 1 := congrArg Subtype.val h
    have h2 : t ∈ W ⊔ OCW W := (Thompson.piG_eq_one_iff htN).mp h1
    have ht2' : IsPGroup 2 (Subgroup.zpowers t) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr htS)
    exact htW (Thompson.mem_of_isPGroup_of_mem_sup_OCW hW2 ht2' h2)
  have hφ2 : C.D.φ τ * C.D.φ τ = 1 := by rw [← map_mul, hτ2, map_one]
  have hφ1 : C.D.φ τ ≠ 1 := fun h => hτ1 (C.D.φ.injective (h.trans (map_one _).symm))
  have hinv := T7C2.mem_invs4 _ hφ2 hφ1
  have hab : C.D.φ (T7D.imgQ C.D.F.ρ) ≠ C.D.φ (T7D.imgQ C.D.F.ρ') :=
    fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : C.D.φ (T7D.imgQ C.D.F.ρ) * C.D.φ (T7D.imgQ C.D.F.ρ') =
      C.D.φ (T7D.imgQ C.D.F.ρ') * C.D.φ (T7D.imgQ C.D.F.ρ) := by
    rw [← map_mul, ← map_mul, C.D.hcomm]
  have hrM : C.D.F.ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr
  have htM' : C.D.F.ρ'.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR C.D.F.ρ'.hr
  have hra : T7D.imgQ C.D.F.ρ = piM Ω W ⟨_, hrM⟩ := Subtype.ext rfl
  have hta : T7D.imgQ C.D.F.ρ' = piM Ω W ⟨_, htM'⟩ := Subtype.ext rfl
  have hrr : C.D.F.ρ.r * C.D.F.ρ.r ∈ W := by rw [C.r_mul_self]; exact C.hd.hzW
  have hrt : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r) ∈ W := by
    have e : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r) =
        C.D.F.ρ.r * C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ'.r) := by
      calc C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r)
          = C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ.r) * C.D.F.ρ'.r := by group
        _ = C.D.F.ρ.r * (C.D.F.ρ.r * C.D.F.ρ'.r) * C.D.F.ρ'.r := by rw [C.commute_r_t.eq]
        _ = C.D.F.ρ.r * C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ'.r) := by group
    rw [e, C.r_mul_self, C.t_mul_self]
    exact W.mul_mem C.hd.hzW C.hd.hzW
  rcases perm4_inv_conj _ hinv _ (C.φ_imgQ_mem _) _ (C.φ_imgQ_mem _) hab hcomm with
    ⟨σ, -, hσ⟩ | ⟨σ, -, hσ⟩
  · obtain ⟨m, hm⟩ := piM_surjective W (C.D.φ.symm σ)
    refine C.kc_aux hg0 hfus htM ht2 ht1 hrM hrr (fun w hw h => C.r_mul_mem_sup hw h) (m := m) ?_
    apply C.D.φ.injective
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply, ← hra]
    exact hσ
  · obtain ⟨m, hm⟩ := piM_surjective W (C.D.φ.symm σ)
    have hrtM : C.D.F.ρ.r * C.D.F.ρ'.r ∈ MGrp Ω W := Subgroup.mul_mem _ hrM htM'
    refine C.kc_aux hg0 hfus htM ht2 ht1 hrtM hrt (fun w hw h => C.rt_mul_mem_sup hw h) (m := m) ?_
    apply C.D.φ.injective
    have hprod : piM Ω W ⟨_, hrtM⟩ = T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ' := by
      rw [hra, hta, ← map_mul]; rfl
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply, hprod, map_mul]
    exact hσ

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
