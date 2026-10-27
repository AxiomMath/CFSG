module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.BaseCase

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Coset

variable {G : Type*} [Group G]

theorem exists_fixed_in_coset' {p : ℕ} [Fact p.Prime] {U V : Subgroup G} (hU : IsPGroup p ↥U)
    (hVp : ¬ p ∣ Nat.card ↥V) (hUV : U ≤ Subgroup.normalizer (V : Set G)) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx : ∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ V) :
    ∃ v ∈ V, ∀ u ∈ U, u * (x * v) * u⁻¹ = x * v := by
  classical
  let T : Type _ := {y : G // x⁻¹ * y ∈ V}
  have hclosed : ∀ (u : ↥U) (y : T), x⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) ∈ V := by
    intro u y
    have hw := hx u u.2
    have hv : (u : G) * (x⁻¹ * (y : G)) * (u : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hUV u.2) _).1 y.2
    have hxw : x⁻¹ * ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (V : Set G)).inv_mem hxV) _).1
        hw
      simpa [mul_assoc] using this
    have : x⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) =
        (x⁻¹ * ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x) *
          ((u : G) * (x⁻¹ * (y : G)) * (u : G)⁻¹) := by
      group
    rw [this]
    exact V.mul_mem hxw hv
  let inst : MulAction ↥U T :=
    { smul := fun u y => ⟨(u : G) * (y : G) * (u : G)⁻¹, hclosed u y⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : ↥U) : G) * (y : G) * ((1 : ↥U) : G)⁻¹ = (y : G)
        simp)
      mul_smul := fun u₁ u₂ y => Subtype.ext (by
        show ((u₁ * u₂ : ↥U) : G) * (y : G) * ((u₁ * u₂ : ↥U) : G)⁻¹ =
          (u₁ : G) * ((u₂ : G) * (y : G) * (u₂ : G)⁻¹) * (u₁ : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card T = Nat.card ↥V := by
    refine Nat.card_congr ⟨fun y => ⟨x⁻¹ * (y : G), y.2⟩, fun v => ⟨x * (v : G), by simp⟩,
      fun y => by apply Subtype.ext; simp, fun v => by apply Subtype.ext; simp⟩
  obtain ⟨y, hy⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card T (by rw [hcard]; exact hVp)
  refine ⟨x⁻¹ * (y : G), y.2, fun u hu => ?_⟩
  have h1 : (u : G) * (y : G) * (u : G)⁻¹ = (y : G) := by
    have := congrArg Subtype.val (hy ⟨u, hu⟩)
    exact this
  have : x * (x⁻¹ * (y : G)) = (y : G) := by group
  rw [this]
  exact h1

theorem exists_mul_mem_centralizer {p : ℕ} [Fact p.Prime] {d x : G} {V : Subgroup G}
    (hd : IsPGroup p (Subgroup.zpowers d)) (hVp : ¬ p ∣ Nat.card ↥V)
    (hdV : d ∈ Subgroup.normalizer (V : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hx : d * x * d⁻¹ * x⁻¹ ∈ V) :
    ∃ v ∈ V, x * v ∈ Subgroup.centralizer ({d} : Set G) := by
  let T : Subgroup G :=
    { carrier := {u | u ∈ Subgroup.normalizer (V : Set G) ∧ u * x * u⁻¹ * x⁻¹ ∈ V}
      mul_mem' := by
        rintro u₁ u₂ ⟨hn₁, h₁⟩ ⟨hn₂, h₂⟩
        refine ⟨Subgroup.mul_mem _ hn₁ hn₂, ?_⟩
        have e : u₁ * u₂ * x * (u₁ * u₂)⁻¹ * x⁻¹ =
            (u₁ * (u₂ * x * u₂⁻¹ * x⁻¹) * u₁⁻¹) * (u₁ * x * u₁⁻¹ * x⁻¹) := by group
        rw [e]
        exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 hn₁ _).1 h₂) h₁
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro u ⟨hn, h⟩
        refine ⟨Subgroup.inv_mem _ hn, ?_⟩
        have e : u⁻¹ * x * u⁻¹⁻¹ * x⁻¹ = u⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹ * u := by group
        rw [e]
        have h' := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) _).1 (V.inv_mem h)
        simpa using h' }
  have hdT : d ∈ T := ⟨hdV, hx⟩
  have hzT : Subgroup.zpowers d ≤ T := (Subgroup.zpowers_le).2 hdT
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := p) (U := Subgroup.zpowers d) hd hVp
    (fun u hu => (hzT hu).1) hxV (fun u hu => (hzT hu).2)
  refine ⟨v, hv, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hfix d (Subgroup.mem_zpowers d)
  calc x * v * d = (d * (x * v) * d⁻¹) * d := by rw [this]
    _ = d * (x * v) := by group

end Coset

section Quotient

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := Subgroup.mem_normalizer_iff.1 hA z
  have h2 := Subgroup.mem_normalizer_iff.1 hB z
  simp only [Subgroup.mem_inf]
  rw [h1, h2]

theorem barX_inf_centralizer {p : ℕ} (hp : p.Prime) {M L : Subgroup G} {d : G} (hdM : d ∈ M)
    (hLM : L ≤ M) (hdL : d ∈ Subgroup.normalizer (L : Set G))
    (hd : IsPGroup p (Subgroup.zpowers d)) :
    barX p M (L ⊓ Subgroup.centralizer ({d} : Set G)) =
      barX p M L ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxL, hxd⟩ := (Subgroup.mem_subgroupOf).1 hx
    refine ⟨⟨x, (Subgroup.mem_subgroupOf).2 hxL, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : (x : G) * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hxd
    have h2 : x * (⟨d, hdM⟩ : ↥M) = ⟨d, hdM⟩ * x := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  · rintro z ⟨⟨y, hy, rfl⟩, hz⟩
    have hylL : (y : G) ∈ L := (Subgroup.mem_subgroupOf).1 hy
    have hz' := Subgroup.mem_centralizer_singleton_iff.1 hz
    set N : Subgroup G := GLAPPrimeCoreOf p M with hN
    have hcomm : d * (y : G) * d⁻¹ * (y : G)⁻¹ ∈ N := by
      have h1 : (⟨d, hdM⟩ : ↥M) * y * (⟨d, hdM⟩ : ↥M)⁻¹ * y⁻¹ ∈ GLAPPrimeCore p ↥M := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        show QuotientGroup.mk' (GLAPPrimeCore p ↥M)
          ((⟨d, hdM⟩ : ↥M) * y * (⟨d, hdM⟩ : ↥M)⁻¹ * y⁻¹) = 1
        simp only [map_mul, map_inv]
        rw [← hz']
        group
      exact ⟨_, h1, rfl⟩
    have hcommL : d * (y : G) * d⁻¹ * (y : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.1 hdL _).1 hylL) (L.inv_mem hylL)
    have hVp : ¬ p ∣ Nat.card ↥(N ⊓ L) := fun h =>
      not_dvd_card_glaPPrimeCoreOf hp M (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hdV : d ∈ Subgroup.normalizer ((N ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_inf (le_normalizer_glaPPrimeCoreOf p M hdM) hdL
    have hyV : (y : G) ∈ Subgroup.normalizer ((N ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_inf (le_normalizer_glaPPrimeCoreOf p M y.2) (Subgroup.le_normalizer hylL)
    obtain ⟨v, hv, hvc⟩ := exists_mul_mem_centralizer hd hVp hdV hyV ⟨hcomm, hcommL⟩
    have hyvL : (y : G) * v ∈ L := L.mul_mem hylL hv.2
    have hyvM : (y : G) * v ∈ M := hLM hyvL
    refine ⟨⟨(y : G) * v, hyvM⟩, (Subgroup.mem_subgroupOf).2 ⟨hyvL, hvc⟩, ?_⟩
    have hvN : (⟨v, hLM hv.2⟩ : ↥M) ∈ GLAPPrimeCore p ↥M := by
      obtain ⟨v', hv', hv'v⟩ := hv.1
      have : v' = ⟨v, hLM hv.2⟩ := Subtype.ext hv'v
      exact this ▸ hv'
    have e : (⟨(y : G) * v, hyvM⟩ : ↥M) = y * ⟨v, hLM hv.2⟩ := rfl
    have hv1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨v, hLM hv.2⟩ : ↥M) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hvN
    rw [e, map_mul, hv1, mul_one]

end Quotient

end CFSG.LocalAnalysis.GLTheoremB
