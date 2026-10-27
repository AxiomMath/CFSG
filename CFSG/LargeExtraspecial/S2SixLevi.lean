module

public import CFSG.LargeExtraspecial.S2SixAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_zero_right eichler_conj
  eichler_add_smul_self)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

theorem timmesfeld_2_4_omega_of_add (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (perp q F))
    {φ : V → V} (hφ : ∀ x ∈ perp q F, φ x ∈ perp q F)
    (hadd : ∀ x ∈ perp q F, ∀ y ∈ perp q F, φ (x + y) = φ x + φ y)
    (hcomm : ∀ g ∈ omegaFix q hq F, ∀ x ∈ perp q F, φ (g x) = g (φ x)) :
    ∃ c : ZMod 2, ∀ x ∈ perp q F, φ x = c • x := by
  have h0 : φ 0 = 0 := by
    have h := hadd 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    rwa [add_zero, vec_add_self] at h
  have hsmul : ∀ (a : ZMod 2) (y : V), φ (a • y) = a • φ y := by
    intro a y
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul, zero_smul, h0]
    · rw [one_smul, one_smul]
  obtain ⟨p₀, hp₀F, hp₀0, hp₀⟩ := exists_singular_mem_perp (q := q) (F := F) (by omega)
  have hfix : ∀ p ∈ perp q F, p ≠ 0 → q p = 0 → φ p ∈ (ZMod 2) ∙ p := by
    intro p hpF hp0 hp
    refine fixed_mem_span_of_radFix hq hF h4 hpF hp0 hp (hφ p hpF) fun t ht => ?_
    rw [← hcomm t (radFix_le_omegaFix hq hp0 hp ht) p hpF, ht.1.2.1]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfix p₀ hp₀F hp₀0 hp₀)
  refine ⟨c, ?_⟩
  have hsing : ∀ s ∈ perp q F, q s = 0 → φ s = c • s := by
    intro s hsF hs
    by_cases hs0 : s = 0
    · rw [hs0, h0, smul_zero]
    obtain ⟨g, hg, hgs⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hp₀F hsF hp₀0 hs0 hp₀ hs
    rw [← hgs, hcomm g (radGen_le_omegaFix hq F hg) p₀ hp₀F, ← hc, map_smul]
  obtain ⟨p₁, hp₁F, hp₁, hpp₁⟩ := exists_hyperbolic_partner hq hF hp₀F hp₀0 hp₀
  intro x hx
  have hx₀ := sub_mem_perp_sup_span_pair hp₀F hp₁F hpp₁ hx
  set x₀ := x - polar q x p₁ • p₀ - polar q x p₀ • p₁ with hx₀def
  obtain ⟨hx₀F, hp₀x₀, hp₁x₀⟩ := mem_perp_sup_span_pair.mp hx₀
  have hφx₀ : φ x₀ = c • x₀ := by
    rcases zmod2_eq_zero_or_eq_one (q x₀) with h | h
    · exact hsing x₀ hx₀F h
    · have hs : q (x₀ + p₀ + p₁) = 0 := by
        rw [map_add_eq, map_add_eq, h, hp₀, hp₁, polar_add_left, polar_comm, hp₀x₀,
          polar_comm q x₀ p₁, hp₁x₀, hpp₁]
        decide
      have h1 := hsing _ (Submodule.add_mem _ (Submodule.add_mem _ hx₀F hp₀F) hp₁F) hs
      rw [hadd _ (Submodule.add_mem _ hx₀F hp₀F) _ hp₁F, hadd _ hx₀F _ hp₀F,
        hsing p₀ hp₀F hp₀, hsing p₁ hp₁F hp₁, smul_add, smul_add] at h1
      exact add_right_cancel (add_right_cancel h1)
  have hx' : x = x₀ + polar q x p₁ • p₀ + polar q x p₀ • p₁ := by
    rw [hx₀def]
    abel
  rw [hx', hadd _ (Submodule.add_mem _ hx₀F (Submodule.smul_mem _ _ hp₀F)) _
    (Submodule.smul_mem _ _ hp₁F), hadd _ hx₀F _ (Submodule.smul_mem _ _ hp₀F), hsmul, hsmul,
    hφx₀, hsing p₀ hp₀F hp₀, hsing p₁ hp₁F hp₁, smul_add, smul_add, smul_comm c (polar q x p₁),
    smul_comm c (polar q x p₀)]

variable {hq : q.polarBilin.Nondegenerate}

namespace IsAutOn

variable {F : Submodule (ZMod 2) V} {α : omegaGroup q hq → omegaGroup q hq}

theorem apply_eq_iff (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥)
    (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {a : V} (haF : a ∈ perp q F) (ha0 : a ≠ 0)
    (ha : q a = 0) (hαa : MapsRad F α a a) {g : omegaGroup q hq}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    (g : V ≃ₗ[ZMod 2] V) a = a ↔ (α g : V ≃ₗ[ZMod 2] V) a = a := by
  have h := hα.mapsRad_apply ha0 ha haF hαa hg
  have hgO : (g : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp g.2).1
  have hαgO : (α g : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp (α g).2).1
  have hgaF := apply_mem_perp hgO hg haF
  have hαgaF := apply_mem_perp hαgO (hα.mem g hg) haF
  have hga0 : (g : V ≃ₗ[ZMod 2] V) a ≠ 0 := fun h0 =>
    ha0 ((g : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
  have hαga0 : (α g : V ≃ₗ[ZMod 2] V) a ≠ 0 := fun h0 =>
    ha0 ((α g : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
  have hga : q ((g : V ≃ₗ[ZMod 2] V) a) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO, ha]
  have hαga : q ((α g : V ≃ₗ[ZMod 2] V) a) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hαgO, ha]
  constructor
  · intro hga'
    rw [hga'] at h
    exact (hα.eq_of_mapsRad' hF h4 haF hαgaF ha0 hαga0 ha hαga hαa h).symm
  · intro hαga'
    rw [hαga'] at h
    exact eq_of_mapsRad hF h4 hgaF haF hga0 ha0 hga ha h hαa

theorem restrict_levi (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥)
    (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {p p₁ : V} (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hαp : MapsRad F α p p) (hαp₁ : MapsRad F α p₁ p₁) :
    ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
        (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p, p₁})) := by
  intro g hg
  rw [mem_fixGroup_sup_span_pair, mem_fixGroup_sup_span_pair,
    hα.apply_eq_iff hF h4 hpF hp0 hp hαp hg, hα.apply_eq_iff hF h4 hp₁F hp₁0 hp₁ hαp₁ hg]
  exact ⟨fun h => ⟨hα.mem g hg, h.2⟩, fun h => ⟨hg, h.2⟩⟩

end IsAutOn

theorem MapsRad.restrict {F K : Submodule (ZMod 2) V} {α : omegaGroup q hq → omegaGroup q hq}
    {a b : V} (h : MapsRad F α a b) (hKF : fixGroup K ≤ fixGroup F)
    (hK : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K)) :
    MapsRad K α a b := by
  intro g hg
  have hgF := hKF hg
  have hαgK := (hK g hgF).mp hg
  have e := h g hgF
  constructor
  · intro hga
    exact ⟨(e.mp ⟨hga.1, hgF⟩).1, hαgK⟩
  · intro hαgb
    exact ⟨(e.mpr ⟨hαgb.1, hKF hαgK⟩).1, hg⟩

namespace IsAutOn

variable {F : Submodule (ZMod 2) V} {α : omegaGroup q hq → omegaGroup q hq}

theorem exists_radFix_map (hα : IsAutOn F α) {p p₁ : V} (hpF : p ∈ perp q F) (hp0 : p ≠ 0)
    (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) (hαp : MapsRad F α p p) :
    ∃ φ : V → V, (∀ v ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}),
        φ v ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁})) ∧
      (∀ v ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}),
        α ⟨eichler q p v, eichler_mem_omegaGroup hq p v⟩ =
          ⟨eichler q p (φ v), eichler_mem_omegaGroup hq p (φ v)⟩) ∧
      ∀ x ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}),
        ∀ y ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}), φ (x + y) = φ x + φ y := by
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  let E : V → omegaGroup q hq := fun v => ⟨eichler q p v, eichler_mem_omegaGroup hq p v⟩
  have hEL : ∀ v ∈ perp q K, (E v : V ≃ₗ[ZMod 2] V) ∈ radFix q F p := fun v hv =>
    (mem_radFix_iff hq hp0 hp hpF).mpr
      ⟨v, (mem_perp_sup_span_pair.mp hv).1, (mem_perp_sup_span_pair.mp hv).2.1, rfl⟩
  have hex : ∀ v : V, ∃ u : V, v ∈ perp q K →
      u ∈ perp q K ∧ (α (E v) : V ≃ₗ[ZMod 2] V) = eichler q p u := by
    intro v
    by_cases hv : v ∈ perp q K
    · obtain ⟨u, hu, hEu⟩ := exists_eq_eichler_perp hq hpF hp0 hp hpp₁
        ((hαp (E v) (hEL v hv).2).mp (hEL v hv))
      exact ⟨u, fun _ => ⟨hu, hEu⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose φ hφ using hex
  have hφK : ∀ v ∈ perp q K, φ v ∈ perp q K := fun v hv => (hφ v hv).1
  have hφE : ∀ v ∈ perp q K, α (E v) = E (φ v) := fun v hv => Subtype.ext (hφ v hv).2
  refine ⟨φ, hφK, hφE, fun x hx y hy => ?_⟩
  have hEmul : ∀ a b : V, polar q p a = 0 → polar q p b = 0 → E (a + b) = E a * E b :=
    fun a b ha hb => Subtype.ext (eichler_mul ha hb).symm
  have hpx := (mem_perp_sup_span_pair.mp hx).2.1
  have hpy := (mem_perp_sup_span_pair.mp hy).2.1
  have hpφx := (mem_perp_sup_span_pair.mp (hφK x hx)).2.1
  have hpφy := (mem_perp_sup_span_pair.mp (hφK y hy)).2.1
  have e : E (φ (x + y)) = E (φ x + φ y) := by
    rw [← hφE _ (Submodule.add_mem _ hx hy), hEmul x y hpx hpy,
      hα.map_mul _ _ (hEL x hx).2 (hEL y hy).2, hφE x hx, hφE y hy, hEmul _ _ hpφx hpφy]
  exact eq_of_eichler_eq hp hpp₁ (hφK _ (Submodule.add_mem _ hx hy))
    (Submodule.add_mem _ (hφK x hx) (hφK y hy)) (congrArg Subtype.val e)

theorem eq_self_of_forall_levi (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥) {m : ℕ}
    (hm : 3 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m) {p p₁ : V} (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1)
    (hαp : MapsRad F α p p)
    (hY : ∀ g : omegaGroup q hq,
      (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p, p₁}) → α g = g)
    (t : omegaGroup q hq) (ht : (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p) : α t = t := by
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  let E : V → omegaGroup q hq := fun v => ⟨eichler q p v, eichler_mem_omegaGroup hq p v⟩
  have hEF : ∀ v ∈ perp q K, (E v : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := fun v hv =>
    eichler_mem_fixGroup hpF (mem_perp_sup_span_pair.mp hv).1
  obtain ⟨φ, hφK, hφE, hadd⟩ := hα.exists_radFix_map hpF hp0 hp hpp₁ hαp
  replace hφE : ∀ v ∈ perp q K, α (E v) = E (φ v) := hφE
  have hcomm : ∀ g ∈ omegaFix q hq K, ∀ x ∈ perp q K, φ (g x) = g (φ x) := by
    intro g hg x hx
    obtain ⟨hgF', hgp, -⟩ := mem_omegaFix_sup_span_pair.mp hg
    set g' : omegaGroup q hq := ⟨g, hg.1⟩
    have hg'F : (g' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hgF'.2
    have hgO : g ∈ orthogonalGroup q := mem_orthogonalGroup_of_mem_omegaFix hg
    have hgx : g x ∈ perp q K := apply_mem_perp hgO hg.2 hx
    have hgφx : g (φ x) ∈ perp q K := apply_mem_perp hgO hg.2 (hφK x hx)
    have hconj : ∀ v : V, g' * E v * g'⁻¹ = E (g v) := fun v => Subtype.ext (by
      change g * eichler q p v * g⁻¹ = eichler q p (g v)
      rw [eichler_conj hgO, hgp])
    have hαg : α g' = g' := hY g' hg.2
    have e : E (φ (g x)) = E (g (φ x)) := by
      rw [← hφE _ hgx, ← hconj x,
        hα.map_mul _ _ (coe_mul_mem_fixGroup hg'F (hEF x hx)) (coe_inv_mem_fixGroup hg'F),
        hα.map_mul _ _ hg'F (hEF x hx), hα.map_inv hg'F, hαg, hφE x hx, hconj]
    exact eq_of_eichler_eq hp hpp₁ (hφK _ hgx) hgφx (congrArg Subtype.val e)
  obtain ⟨c, hc⟩ := timmesfeld_2_4_omega_of_add hq hK (by omega) hφK hadd hcomm
  have hc1 : c = 1 := by
    rcases zmod2_eq_zero_or_eq_one c with h0 | h1
    · exfalso
      obtain ⟨v, hvK, hv0⟩ : ∃ v ∈ perp q K, v ≠ 0 :=
        Submodule.exists_mem_ne_zero_of_ne_bot fun h => by
          rw [h, finrank_bot] at hKdim
          omega
      have hφv : φ v = 0 := by rw [hc v hvK, h0, zero_smul]
      have h1 : α (E v) = α 1 := by
        rw [hα.map_one, hφE v hvK, hφv]
        exact Subtype.ext (eichler_zero_right q p)
      have := hα.inj _ _ (hEF v hvK) (one_mem _) h1
      refine hv0 (eq_of_eichler_eq hp hpp₁ hvK (Submodule.zero_mem _) ?_)
      rw [eichler_zero_right]
      exact congrArg Subtype.val this
    · exact h1
  obtain ⟨u, hu, htu⟩ := exists_eq_eichler_perp hq hpF hp0 hp hpp₁ ht
  have htE : t = E u := Subtype.ext htu
  rw [htE, hφE u hu, hc u hu, hc1, one_smul]

end IsAutOn

end S2

end CFSG.LargeExtraspecial
