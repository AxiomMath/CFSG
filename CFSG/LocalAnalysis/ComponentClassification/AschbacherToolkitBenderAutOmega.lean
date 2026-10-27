module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutBasic

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace Omega

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_smul_iff {α : MulAut G} {S : Sylow 2 G} {g : G} :
    g ∈ ((α • S : Sylow 2 G) : Subgroup G) ↔ α⁻¹ g ∈ (S : Subgroup G) := by
  rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

omit [Finite G] in
theorem mem_conj_smul_iff {x : G} {S : Sylow 2 G} {g : G} :
    g ∈ ((x • S : Sylow 2 G) : Subgroup G) ↔ x⁻¹ * g * x ∈ (S : Subgroup G) := by
  rw [Sylow.smul_def, mem_smul_iff, MulAut.inv_apply, MulAut.conj_symm_apply]

theorem smul_eq_of_mapsTo {α : MulAut G} {S : Sylow 2 G} (h : ∀ s ∈ (S : Subgroup G), α s ∈ S) :
    α • S = S := by
  have hle : ((α • S : Sylow 2 G) : Subgroup G) ≤ S := by
    intro g hg
    rw [mem_smul_iff] at hg
    have := h _ hg
    rwa [MulAut.apply_inv_self] at this
  have hcard : Nat.card ((α • S : Sylow 2 G) : Subgroup G) = Nat.card (S : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  exact Sylow.ext (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

omit [Finite G] in
theorem smul_conj_smul (α : MulAut G) (g : G) (S : Sylow 2 G) :
    α • (g • S) = α g • (α • S) := by
  rw [Sylow.smul_def, Sylow.smul_def, smul_smul, smul_smul]
  congr 1
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem eq_one_of_mem_of_mem {R S : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hne : S ≠ R) {x : G} (hxR : x ∈ (R : Subgroup G)) (hxS : x ∈ (S : Subgroup G)) : x = 1 := by
  set M := Subgroup.normalizer ((R : Subgroup G) : Set G) with hM
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  have hgM : g ∉ M := by
    intro hgM
    apply hne
    rw [← hg]
    exact (Sylow.smul_eq_iff_mem_normalizer).mpr hgM
  have hginv : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
  have hodd := hSE.2.2 g⁻¹ hginv
  rw [inv_inv] at hodd
  set D := M ⊓ M.map (MulAut.conj g).toMonoidHom with hD
  have hxM : x ∈ M := Subgroup.le_normalizer hxR
  have hxD : x ∈ D := by
    refine ⟨hxM, ?_⟩
    rw [← hg, mem_conj_smul_iff] at hxS
    refine ⟨g⁻¹ * x * g, Subgroup.le_normalizer hxS, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  have h2 : IsPGroup 2 ((R : Subgroup G) ⊓ D : Subgroup G) := R.isPGroup'.to_inf_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
  have hdvd : Nat.card ((R : Subgroup G) ⊓ D : Subgroup G) ∣ Nat.card D :=
    Subgroup.card_dvd_of_le inf_le_right
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hdvd
    have : 2 ∣ Nat.card D := (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  rw [hk0, pow_zero] at hk
  have hbot := (Subgroup.card_eq_one).mp hk
  have : x ∈ ((R : Subgroup G) ⊓ D : Subgroup G) := ⟨hxR, hxD⟩
  rw [hbot] at this
  exact this

theorem eq_one_of_mem_normalizer {R S : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hne : S ≠ R) {r : G} (hr : r ∈ (R : Subgroup G))
    (hrS : r ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) : r = 1 := by
  have h := R.isPGroup'.inf_normalizer_sylow S
  have hmem : r ∈ (R : Subgroup G) ⊓ Subgroup.normalizer (S : Set G) := ⟨hr, hrS⟩
  rw [h] at hmem
  exact eq_one_of_mem_of_mem hSE hne hmem.1 hmem.2

theorem exists_smul_eq {R : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hcard : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1) {S₀ S : Sylow 2 G}
    (h₀ : S₀ ≠ R) (hS : S ≠ R) : ∃ r ∈ (R : Subgroup G), r • S₀ = S := by
  classical
  let f : ↥(R : Subgroup G) → Sylow 2 G := fun r => (r : G) • S₀
  have hinj : Function.Injective f := by
    intro r r' h
    have h' : ((r : G)⁻¹ * r') • S₀ = S₀ := by
      rw [mul_smul]
      have h2 : (r' : G) • S₀ = (r : G) • S₀ := h.symm
      rw [h2, inv_smul_smul]
    have hn := (Sylow.smul_eq_iff_mem_normalizer).mp h'
    have h1 := eq_one_of_mem_normalizer hSE h₀
      ((R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem r.2) r'.2) hn
    apply Subtype.ext
    rw [inv_mul_eq_one] at h1
    exact h1
  have hrange : Set.range f ⊆ {S' : Sylow 2 G | S' ≠ R} := by
    rintro _ ⟨r, rfl⟩ hfr
    apply h₀
    have hR : (r : G)⁻¹ • R = R :=
      (Sylow.smul_eq_iff_mem_normalizer).mpr
        (Subgroup.le_normalizer ((R : Subgroup G).inv_mem r.2))
    calc S₀ = (r : G)⁻¹ • ((r : G) • S₀) := (inv_smul_smul _ _).symm
      _ = (r : G)⁻¹ • R := by rw [show (r : G) • S₀ = R from hfr]
      _ = R := hR
  have hcard_range : (Set.range f).ncard = Nat.card (R : Subgroup G) :=
    Set.ncard_range_of_injective hinj
  have hcard_compl : ({S' : Sylow 2 G | S' ≠ R} : Set (Sylow 2 G)).ncard =
      Nat.card (R : Subgroup G) := by
    have h1 : ({S' : Sylow 2 G | S' ≠ R} : Set (Sylow 2 G)) = Set.univ \ {R} := by
      ext S'
      simp
    rw [h1, Set.ncard_sdiff (by simp), Set.ncard_univ, Set.ncard_singleton, hcard]
    omega
  have heq : Set.range f = {S' : Sylow 2 G | S' ≠ R} :=
    Set.eq_of_subset_of_ncard_le hrange (by rw [hcard_range, hcard_compl]) (Set.toFinite _)
  have hSmem : S ∈ Set.range f := by
    rw [heq]
    exact hS
  obtain ⟨r, hr⟩ := hSmem
  exact ⟨r, r.2, hr⟩

omit [Finite G] in
theorem eq_one_of_forall_smul_eq [IsSimpleGroup G] (R : Sylow 2 G)
    (hR : Subgroup.normalizer ((R : Subgroup G) : Set G) ≠ ⊤) (α : MulAut G)
    (h : ∀ S : Sylow 2 G, α • S = S) : α = 1 := by
  ext g
  rw [MulAut.one_apply]
  set N := (Subgroup.normalizer ((R : Subgroup G) : Set G)).normalCore with hN
  have hu : g⁻¹ * α g ∈ N := by
    intro b
    have hS := h (b⁻¹ • R)
    have hgS := h (g • (b⁻¹ • R))
    rw [smul_conj_smul, hS] at hgS
    have h1 : (g⁻¹ * α g) • (b⁻¹ • R) = b⁻¹ • R := by
      rw [mul_smul, hgS, inv_smul_smul]
    have h2 : (b * (g⁻¹ * α g) * b⁻¹) • R = R := by
      rw [mul_smul, mul_smul, h1, smul_inv_smul]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h2
  have hNbot : N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
    · exact hb
    · exfalso
      apply hR
      rw [eq_top_iff, ← ht]
      exact Subgroup.normalCore_le _
  rw [hNbot, Subgroup.mem_bot, inv_mul_eq_one] at hu
  exact hu.symm

theorem eq_one_of_centralizes [IsSimpleGroup G] {R : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hcard : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1) {S₀ : Sylow 2 G}
    (h₀ : S₀ ≠ R) (α : MulAut G) (hR : α • R = R) (hS₀ : α • S₀ = S₀)
    (hc : ∀ r ∈ (R : Subgroup G), α r = r) : α = 1 := by
  apply eq_one_of_forall_smul_eq R hSE.1 α
  intro S
  by_cases hSR : S = R
  · rw [hSR, hR]
  obtain ⟨r, hr, rfl⟩ := exists_smul_eq hSE hcard h₀ hSR
  rw [smul_conj_smul, hc r hr, hS₀]

theorem exists_conj_adjust {R : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hcard : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1) {S₀ : Sylow 2 G}
    (h₀ : S₀ ≠ R) (α : MulAut G) (hR : α • R = R) :
    ∃ r ∈ (R : Subgroup G), ((MulAut.conj r)⁻¹ * α) • S₀ = S₀ := by
  have hαS₀ : α • S₀ ≠ R := by
    intro h
    apply h₀
    calc S₀ = α⁻¹ • (α • S₀) := (inv_smul_smul _ _).symm
      _ = α⁻¹ • R := by rw [h]
      _ = α⁻¹ • (α • R) := by rw [hR]
      _ = R := inv_smul_smul _ _
  obtain ⟨r, hr, hrS⟩ := exists_smul_eq hSE hcard h₀ hαS₀
  refine ⟨r, hr, ?_⟩
  rw [mul_smul, ← hrS, Sylow.smul_def, inv_smul_smul]

omit [Finite G] in
theorem conj_smul_self {R : Sylow 2 G} {r : G} (hr : r ∈ (R : Subgroup G)) :
    MulAut.conj r • R = R := by
  rw [← Sylow.smul_def]
  exact (Sylow.smul_eq_iff_mem_normalizer).mpr (Subgroup.le_normalizer hr)

omit [Finite G] in
theorem mem_normalizer_smul {α : MulAut G} {S : Sylow 2 G} {g : G}
    (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    α g ∈ Subgroup.normalizer (((α • S : Sylow 2 G) : Subgroup G) : Set G) := by
  have h1 : g • S = S := (Sylow.smul_eq_iff_mem_normalizer).mpr hg
  have h2 : α g • (α • S) = α • S := by rw [← smul_conj_smul, h1]
  exact (Sylow.smul_eq_iff_mem_normalizer).mp h2

omit [Finite G] in
theorem mem_normalizer_conj_smul_iff {x g : G} {S : Sylow 2 G} :
    g ∈ Subgroup.normalizer (((x • S : Sylow 2 G) : Subgroup G) : Set G) ↔
      x⁻¹ * g * x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  have e1 : g ∈ Subgroup.normalizer (((x • S : Sylow 2 G) : Subgroup G) : Set G) ↔
      g • (x • S) = x • S := Sylow.smul_eq_iff_mem_normalizer.symm
  have e2 : x⁻¹ * g * x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) ↔
      (x⁻¹ * g * x) • S = S := Sylow.smul_eq_iff_mem_normalizer.symm
  rw [e1, e2, mul_smul, mul_smul, inv_smul_eq_iff]

theorem mem_of_mem_normalizer_of_mem_normalizer {R S₀ : Sylow 2 G} {H : Subgroup G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (h₀ : S₀ ≠ R)
    (hNR : ∀ g ∈ Subgroup.normalizer ((R : Subgroup G) : Set G),
      ∃ r ∈ (R : Subgroup G), ∃ h ∈ H, g = r * h)
    (hH : H ≤ Subgroup.normalizer ((S₀ : Subgroup G) : Set G)) {g : G}
    (hg₁ : g ∈ Subgroup.normalizer ((R : Subgroup G) : Set G))
    (hg₂ : g ∈ Subgroup.normalizer ((S₀ : Subgroup G) : Set G)) : g ∈ H := by
  obtain ⟨r, hr, h, hh, rfl⟩ := hNR g hg₁
  have hrN : r ∈ Subgroup.normalizer ((S₀ : Subgroup G) : Set G) := by
    have := (Subgroup.normalizer _).mul_mem hg₂ ((Subgroup.normalizer _).inv_mem (hH hh))
    rwa [mul_inv_cancel_right] at this
  rw [eq_one_of_mem_normalizer hSE h₀ hr hrN, one_mul]
  exact hh

theorem exists_eq_conj_of_abelian [IsSimpleGroup G] {R : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hcard : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1)
    (hab : ∀ x ∈ (R : Subgroup G), ∀ y ∈ (R : Subgroup G), x * y = y * x) (α : MulAut G)
    (hc : ∀ r ∈ (R : Subgroup G), α r = r) : ∃ r ∈ (R : Subgroup G), α = MulAut.conj r := by
  have hcard2 : 1 < Nat.card (Sylow 2 G) := by
    rw [hcard]
    have : 0 < Nat.card (R : Subgroup G) := Nat.card_pos
    omega
  have : Nontrivial (Sylow 2 G) := Finite.one_lt_card_iff_nontrivial.mp hcard2
  obtain ⟨S₀, h₀⟩ := exists_ne R
  have hR : α • R = R := smul_eq_of_mapsTo fun s hs => by rw [hc s hs]; exact hs
  obtain ⟨r, hr, hrS⟩ := exists_conj_adjust hSE hcard h₀ α hR
  refine ⟨r, hr, ?_⟩
  have hone := eq_one_of_centralizes hSE hcard h₀ ((MulAut.conj r)⁻¹ * α)
    (by rw [mul_smul, hR, inv_smul_eq_iff, conj_smul_self hr]) hrS (fun x hx => by
      rw [MulAut.mul_apply, hc x hx, MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc,
        ← hab r hr x hx, inv_mul_cancel_left])
  rw [inv_mul_eq_one] at hone
  exact hone.symm

theorem autControlAt_of_abelian [IsSimpleGroup G] {R : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hcard : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1)
    (hab : (R : Subgroup G) ≤ sylowCenter (R : Subgroup G)) :
    AutControlAt (R : Subgroup G) := by
  intro α _ hz _ hout
  exfalso
  have hab' : ∀ x ∈ (R : Subgroup G), ∀ y ∈ (R : Subgroup G), x * y = y * x := by
    intro x hx y hy
    exact ((mem_sylowCenter.mp (hab hy)).2 x hx)
  obtain ⟨r, hr, hα⟩ := exists_eq_conj_of_abelian hSE hcard hab' α fun x hx => hz x (hab hx)
  exact hout r hr hα

end Omega

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
