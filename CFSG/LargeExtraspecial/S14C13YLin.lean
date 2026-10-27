module

public import CFSG.LargeExtraspecial.S2OrthOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

structure Half8 (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) (p p₁ : V) : Prop where
  dimV : finrank (ZMod 2) V = 8
  dimM : finrank (ZMod 2) M = 16
  ne_zero : p ≠ 0
  sing : q p = 0
  sing₁ : q p₁ = 0
  polar_eq : polar q p p₁ = 1
  compl : IsCompl (S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
    (S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)))

@[expose] def CompClosed (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) (p p₁ : V)
    (N : Submodule (ZMod 2) M) : Prop :=
  ∀ v ∈ N, ∀ x ∈ S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)),
    ∀ y ∈ S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)), v = x + y → x ∈ N

namespace Half8

variable {ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {p p₁ : V}

omit [FiniteDimensional (ZMod 2) M] in
theorem add_self (v : M) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_perp_bot (x : V) : x ∈ S2.perp q (⊥ : Submodule (ZMod 2) V) := by
  rw [S2.perp_bot]
  exact Submodule.mem_top

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_fixGroup_bot (g : V ≃ₗ[ZMod 2] V) : g ∈ S2.fixGroup (⊥ : Submodule (ZMod 2) V) := by
  rw [S2.fixGroup_bot]
  exact Subgroup.mem_top g

omit [FiniteDimensional (ZMod 2) M] in
theorem radDecomp (h : Half8 ρ p p₁) {N : Submodule (ZMod 2) M} (hN : CompClosed ρ p p₁ N) :
    S2.RadDecomp ρ ⊥ N p p₁ := by
  rw [S2.RadDecomp, S2.radFix_bot, S2.radFix_bot]
  refine ⟨le_antisymm (sup_le inf_le_left inf_le_left) fun v hv => ?_, ?_⟩
  · have hv' : v ∈ S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) ⊔
        S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)) := by
      rw [h.compl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv'
    have hxN := hN _ hv x hx y hy rfl
    have hyN : y ∈ N := by
      have := N.sub_mem hv hxN
      rwa [add_sub_cancel_left] at this
    exact Submodule.mem_sup.mpr ⟨x, Submodule.mem_inf.mpr ⟨hxN, hx⟩, y,
      Submodule.mem_inf.mpr ⟨hyN, hy⟩, rfl⟩
  · rw [eq_bot_iff]
    intro v hv
    have h1 := Submodule.mem_inf.mp hv
    have : v ∈ S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) ⊓
        S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)) :=
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp h1.1).2, (Submodule.mem_inf.mp h1.2).2⟩
    rwa [h.compl.inf_eq_bot] at this

omit [FiniteDimensional (ZMod 2) M] in
theorem map_mem_fixOf {φ : M →ₗ[ZMod 2] M} (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v))
    {L : Set (V ≃ₗ[ZMod 2] V)} {v : M} (hv : v ∈ S2.fixOf ρ L) : φ v ∈ S2.fixOf ρ L :=
  (S2.mem_fixOf ρ).mpr fun g hg => by rw [← hφ, (S2.mem_fixOf ρ).mp hv g hg]

omit [FiniteDimensional (ZMod 2) M] in
theorem compClosed_range (h : Half8 ρ p p₁) {φ : M →ₗ[ZMod 2] M}
    (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v)) : CompClosed ρ p p₁ (LinearMap.range φ) := by
  rintro _ ⟨w, rfl⟩ x hx y hy hxy
  have hw : w ∈ S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) ⊔
      S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [h.compl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.mp hw
  have hx'' := map_mem_fixOf hφ hx'
  have hy'' := map_mem_fixOf hφ hy'
  have hd : x - φ x' ∈ S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) ⊓
      S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)) := by
    refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hx hx'', ?_⟩
    have e : x - φ x' = φ y' - y := by
      rw [map_add] at hxy
      rw [sub_eq_sub_iff_add_eq_add, ← hxy, add_comm]
    rw [e]
    exact Submodule.sub_mem _ hy'' hy
  rw [h.compl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at hd
  rw [hd]
  exact ⟨x', rfl⟩

omit [FiniteDimensional (ZMod 2) M] in
theorem CompClosed.inf {N N' : Submodule (ZMod 2) M} (hN : CompClosed ρ p p₁ N)
    (hN' : CompClosed ρ p p₁ N') : CompClosed ρ p p₁ (N ⊓ N') :=
  fun v hv x hx y hy hxy => Submodule.mem_inf.mpr
    ⟨hN v (Submodule.mem_inf.mp hv).1 x hx y hy hxy,
      hN' v (Submodule.mem_inf.mp hv).2 x hx y hy hxy⟩

omit [FiniteDimensional (ZMod 2) M] in
theorem omegaInvariant_range {φ : M →ₗ[ZMod 2] M} (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v)) :
    S2.OmegaInvariant ρ ⊥ (LinearMap.range φ) := by
  rintro g - _ ⟨w, rfl⟩
  exact ⟨ρ g w, hφ g w⟩

omit [FiniteDimensional (ZMod 2) M] in
theorem omegaInvariant_inf {N N' : Submodule (ZMod 2) M} (hN : S2.OmegaInvariant ρ ⊥ N)
    (hN' : S2.OmegaInvariant ρ ⊥ N') : S2.OmegaInvariant ρ ⊥ (N ⊓ N') :=
  fun g hg v hv => Submodule.mem_inf.mpr
    ⟨hN g hg v (Submodule.mem_inf.mp hv).1, hN' g hg v (Submodule.mem_inf.mp hv).2⟩

theorem dvd_finrank (h : Half8 ρ p p₁) {N : Submodule (ZMod 2) M}
    (hN : S2.OmegaInvariant ρ ⊥ N) (hc : CompClosed ρ p p₁ N) : 8 ∣ finrank (ZMod 2) N := by
  have := S2.timmesfeld_2_1_b_dvd ρ 4 (bot_inf_eq _) (by norm_num)
    (by rw [S2.perp_bot, finrank_top]; exact h.dimV) hN (mem_perp_bot p) (mem_perp_bot p₁)
    h.ne_zero h.sing h.sing₁ h.polar_eq (h.radDecomp hc)
  simpa using this

omit [FiniteDimensional (ZMod 2) M] in
theorem comm_sub {A : M →ₗ[ZMod 2] M} (hA : ∀ g v, A (ρ g v) = ρ g (A v)) :
    ∀ g v, (A - LinearMap.id : M →ₗ[ZMod 2] M) (ρ g v) =
      ρ g ((A - LinearMap.id : M →ₗ[ZMod 2] M) v) := fun g v => by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, hA, map_sub]

omit [FiniteDimensional (ZMod 2) M] in
theorem apply_eq_of_mem_range {A : M →ₗ[ZMod 2] M} (hA2 : ∀ v, A (A v) = v) {u : M}
    (hu : u ∈ LinearMap.range (A - LinearMap.id)) : A u = u := by
  obtain ⟨w, rfl⟩ := hu
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hA2]
  rw [← sub_eq_zero, show w - A w - (A w - w) = (w - A w) + (w - A w) by abel]
  exact add_self _

theorem finrank_range (h : Half8 ρ p p₁) {A : M →ₗ[ZMod 2] M}
    (hA : ∀ g v, A (ρ g v) = ρ g (A v)) (hA2 : ∀ v, A (A v) = v) (hA1 : ∃ v, A v ≠ v) :
    finrank (ZMod 2) (LinearMap.range (A - LinearMap.id)) = 8 := by
  have hle : LinearMap.range (A - LinearMap.id) ≤ LinearMap.ker (A - LinearMap.id) :=
    fun u hu => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact apply_eq_of_mem_range hA2 hu
  have hrk := (LinearMap.finrank_range_add_finrank_ker (A - LinearMap.id)).trans h.dimM
  have hmono := Submodule.finrank_mono hle
  have h8 := h.dvd_finrank (omegaInvariant_range (comm_sub hA))
    (h.compClosed_range (comm_sub hA))
  have hpos : finrank (ZMod 2) (LinearMap.range (A - LinearMap.id)) ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hA1
    have hmem : (A - LinearMap.id : M →ₗ[ZMod 2] M) v ∈ LinearMap.range (A - LinearMap.id) :=
      ⟨v, rfl⟩
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hmem
    exact hv hmem
  omega

end Half8

end CFSG.LargeExtraspecial.S14
