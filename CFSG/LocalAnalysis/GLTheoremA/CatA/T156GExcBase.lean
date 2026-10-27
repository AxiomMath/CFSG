module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Assembly CFSG.StandardType

theorem fix_of_conj_commute {R : Type} [Group R] {f : MulAut R} (hZ : Subgroup.center R = ⊥)
    {g : R} (hg : MulAut.conj g * f = f * MulAut.conj g) : f g = g := by
  have h1 : ∀ y : R, g * f y * g⁻¹ = f g * f y * (f g)⁻¹ := by
    intro y
    have h := congrArg (fun α : MulAut R => α y) hg
    simpa [MulAut.mul_apply, MulAut.conj_apply] using h
  have hcomm : ∀ y : R, ((f g)⁻¹ * g) * f y = f y * ((f g)⁻¹ * g) := by
    intro y
    calc (f g)⁻¹ * g * f y
        = (f g)⁻¹ * (g * f y * g⁻¹) * g := by group
      _ = (f g)⁻¹ * (f g * f y * (f g)⁻¹) * g := by rw [h1 y]
      _ = f y * ((f g)⁻¹ * g) := by group
  have hz : (f g)⁻¹ * g = 1 := by
    have hmem : (f g)⁻¹ * g ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨y, rfl⟩ := f.surjective u
      exact (hcomm y).symm
    rwa [hZ, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hz

theorem card_dvd_card_fixSub {R : Type} [Group R] {f : MulAut R}
    (hZ : Subgroup.center R = ⊥) {E : Subgroup (MulAut R)}
    (hE : ∀ φ ∈ E, φ ∈ Set.range (MulAut.conj : R →* MulAut R) ∧ φ * f = f * φ) :
    Nat.card E ∣ Nat.card (ggFixSub f) := by
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    intro x y hxy
    have h1 : x⁻¹ * y ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h2 := congrArg (fun α : MulAut R => α u) hxy
      simp only [MulAut.conj_apply] at h2
      calc u * (x⁻¹ * y) = x⁻¹ * (x * u * x⁻¹) * y := by group
        _ = x⁻¹ * (y * u * y⁻¹) * y := by rw [h2]
        _ = x⁻¹ * y * u := by group
    rw [hZ, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1)
  set E' : Subgroup R := E.comap (MulAut.conj : R →* MulAut R) with hE'
  have hmap : E'.map (MulAut.conj : R →* MulAut R) = E := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun φ hφ => ?_
    obtain ⟨⟨g, rfl⟩, -⟩ := hE φ hφ
    exact ⟨g, hφ, rfl⟩
  have hcard : Nat.card E = Nat.card E' := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective hinj
  have hle : E' ≤ ggFixSub f := by
    intro g hg
    rw [mem_ggFixSub]
    exact fix_of_conj_commute hZ (hE _ hg).2
  rw [hcard]
  exact Subgroup.card_dvd_of_le hle

theorem fixGeomP_of_inn' {p : ℕ} {R R₀ : Type} [Group R] [Group R₀] {I : Set (MulAut R)}
    {I₀ : Set (MulAut R₀)} {f : MulAut R} (hZ : Subgroup.center R = ⊥)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hpK : ∀ g ∈ ggFixSub f, g ^ p = 1 → g ∈ ggFixDer f)
    (hI₀ : ∀ r : R₀, MulAut.conj r ∈ I₀) (hZ₀ : Subgroup.center R₀ = ⊥)
    (θ₀ : ggFixDer f ≃* R₀) : FixGeomP p I f I₀ θ₀ := by
  have key : ∀ g : R, MulAut.conj g * f = f * MulAut.conj g → f g = g := by
    intro g hg
    have h1 : ∀ y : R, g * f y * g⁻¹ = f g * f y * (f g)⁻¹ := by
      intro y
      have h := congrArg (fun α : MulAut R => α y) hg
      simpa [MulAut.mul_apply, MulAut.conj_apply] using h
    have hcomm : ∀ y : R, ((f g)⁻¹ * g) * f y = f y * ((f g)⁻¹ * g) := by
      intro y
      calc (f g)⁻¹ * g * f y
          = (f g)⁻¹ * (g * f y * g⁻¹) * g := by group
        _ = (f g)⁻¹ * (f g * f y * (f g)⁻¹) * g := by rw [h1 y]
        _ = f y * ((f g)⁻¹ * g) := by group
    have hz : (f g)⁻¹ * g = 1 := by
      have hmem : (f g)⁻¹ * g ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro u
        obtain ⟨y, rfl⟩ := f.surjective u
        exact (hcomm y).symm
      rwa [hZ, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hz
  have hpow : ∀ g : R, (MulAut.conj g) ^ p = 1 → g ^ p = 1 := by
    intro g hg
    have hmem : g ^ p ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h : ((MulAut.conj g) ^ p) u = u := by rw [hg]; rfl
      rw [← map_pow, MulAut.conj_apply] at h
      calc u * g ^ p = (g ^ p * u * (g ^ p)⁻¹) * g ^ p := by rw [h]
        _ = g ^ p * u := by group
    rwa [hZ, Subgroup.mem_bot] at hmem
  have hmemK : ∀ φ ∈ I, φ ^ p = 1 → φ * f = f * φ →
      ∃ g, ∃ hg : g ∈ ggFixDer f, φ = MulAut.conj g := by
    intro φ hφI hφp hφ
    obtain ⟨g, rfl⟩ := hI φ hφI hφp
    refine ⟨g, hpK g (mem_ggFixSub.2 (key g hφ)) (hpow g hφp), rfl⟩
  refine ⟨fun φ hφI hφp hφ => ?_, fun φ hφI hφp hφ htriv => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hmemK φ hφI hφp hφ
    refine ⟨MulAut.conj (θ₀ ⟨g, hg⟩), hI₀ _, fun x hx => ?_⟩
    have h1 : (⟨MulAut.conj g x, ggFixDer_map_mem hφ hx⟩ : ggFixDer f) =
        ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  · obtain ⟨g, hg, rfl⟩ := hmemK φ hφI hφp hφ
    have hcomm : ∀ v : R₀, v * θ₀ ⟨g, hg⟩ = θ₀ ⟨g, hg⟩ * v := by
      intro v
      obtain ⟨x, rfl⟩ := MulEquiv.surjective θ₀ v
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have he : g * x.val * g⁻¹ = x.val := htriv x.val x.2
      have hxg : x.val * g = g * x.val := by
        simpa [mul_assoc] using (congrArg (fun t => t * g) he).symm
      exact hxg
    have h1 : θ₀ ⟨g, hg⟩ = 1 := by
      have hmem : θ₀ ⟨g, hg⟩ ∈ Subgroup.center R₀ := by
        rw [Subgroup.mem_center_iff]
        exact hcomm
      rwa [hZ₀, Subgroup.mem_bot] at hmem
    have h2 : (⟨g, hg⟩ : ggFixDer f) = 1 := θ₀.injective (by rw [h1, map_one])
    have hg1 : g = 1 := congrArg Subtype.val h2
    rw [hg1, map_one]

theorem pow_mem_ggFixDer_of_coprime {p : ℕ} {R : Type} [Group R] {f : MulAut R}
    (h : ∀ g ∈ ggFixSub f, ∃ m : ℕ, Nat.Coprime p m ∧ g ^ m ∈ ggFixDer f) :
    ∀ g ∈ ggFixSub f, g ^ p = 1 → g ∈ ggFixDer f := by
  intro g hg hgp
  obtain ⟨m, hm, hgm⟩ := h g hg
  have hb := Nat.gcd_eq_gcd_ab p m
  rw [hm, Nat.cast_one] at hb
  have hg1 : g = (g ^ p) ^ (Nat.gcdA p m) * (g ^ m) ^ (Nat.gcdB p m) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb, zpow_one]
  rw [hg1, hgp, one_zpow, one_mul]
  exact Subgroup.zpow_mem _ hgm _

theorem pow_mem_ggFixDer_of_eq {p : ℕ} {R : Type} [Group R] {f : MulAut R}
    (h : ggFixDer f = ggFixSub f) : ∀ g ∈ ggFixSub f, g ^ p = 1 → g ∈ ggFixDer f :=
  fun g hg _ => h ▸ hg

theorem center_eq_bot_of_simple_noncomm {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

section HasLabel


theorem fixAlt_of_hasLabel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} {f : MulAut R} (hZ : Subgroup.center R = ⊥)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hpK : ∀ g ∈ ggFixSub f, g ^ p = 1 → g ∈ ggFixDer f)
    {R₀ : Type} [Group R₀] {lab₀ : LargeEvenLabel} (hlab₀ : LargeEvenInLambda2 lab₀)
    (hs : IsSimpleGroup R₀) (hna : ∃ a b : R₀, a * b ≠ b * a) (hL : GGHasLabel lab₀ R₀)
    (he : Nonempty (ggFixDer f ≃* R₀)) : FixAlt p I f := by
  obtain ⟨e⟩ := he
  have hcan : CFSG.Assembly.LargeEvenRawDatum lab₀ fun R' _ _ _ => Nonempty (R₀ ≃* R') :=
    largeEvenRawDatumLegacy_to_canonical_carrier (T := fun R' _ => Nonempty (R₀ ≃* R')) hL
  have hinn := MI.canonRawInn hp hp2 hlab₀ _ hcan
  refine Or.inl ⟨lab₀, hlab₀, Canonical.largeEvenRawDatum_mono ?_ hinn⟩
  rintro R' _ I' F' ⟨⟨e'⟩, hRaw⟩
  haveI : IsSimpleGroup R' := e'.symm.isSimpleGroup
  have hna' : ∃ a b : R', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e' a, e' b, fun h => hab (e'.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨-, -, hconj, -⟩ := hRaw inferInstance hna'
  refine ⟨inferInstance, hna', e.trans e', ?_⟩
  exact fixGeomP_of_inn' hZ hI hpK hconj (center_eq_bot_of_simple_noncomm hna') _

end HasLabel

end CFSG.LocalAnalysis.GLTheoremA.T156

end
