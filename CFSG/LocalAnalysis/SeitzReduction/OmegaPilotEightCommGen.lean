module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrth
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2Diagonal

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open scoped MatrixGroups

section Subdirect

variable {G : Type*} [Group G]

theorem le_of_subdirect {A B H : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAs : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (h1 : ∀ a ∈ A, ∃ b ∈ B, a * b ∈ H) (h2 : ∀ b ∈ B, ∃ a ∈ A, a * b ∈ H)
    {a₁ : G} (ha₁A : a₁ ∈ A) (ha₁H : a₁ ∈ H) (ha₁ : a₁ ≠ 1) : A ≤ H ∧ B ≤ H := by
  set N : Subgroup A := H.subgroupOf A with hN
  have hnorm : N.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨b, hb, hab⟩ := h1 g g.2
    have hnb : (n : G) * b = b * n := hAB n n.2 b hb
    have h := H.mul_mem (H.mul_mem hab hn) (H.inv_mem hab)
    have he : (g : G) * b * n * ((g : G) * b)⁻¹ = (g : G) * n * (g : G)⁻¹ := by
      rw [_root_.mul_inv_rev, mul_assoc (g : G) b n, ← hnb]
      group
    simp only [coe_mul, coe_inv]
    rwa [he] at h⟩
  have hA : A ≤ H := by
    rcases hAs N hnorm with h | h
    · exfalso
      have h' : (⟨a₁, ha₁A⟩ : A) ∈ N := mem_subgroupOf.mpr ha₁H
      rw [h, mem_bot] at h'
      exact ha₁ (congrArg Subtype.val h')
    · intro a ha
      have h' : (⟨a, ha⟩ : A) ∈ N := h ▸ mem_top _
      exact mem_subgroupOf.mp h'
  refine ⟨hA, fun b hb => ?_⟩
  obtain ⟨a, ha, hab⟩ := h2 b hb
  have h := H.mul_mem (H.inv_mem (hA ha)) hab
  rwa [inv_mul_cancel_left] at h

theorem le_centralizer_of_subdirect {A B R U : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAs : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (hRU : R ≤ centralizer (U : Set G)) (h1 : ∀ a ∈ A, ∃ b ∈ B, a * b ∈ R)
    (h2 : ∀ b ∈ B, ∃ a ∈ A, a * b ∈ R) {x : G} (hxA : x ∈ A)
    (hxU : x ∈ normalizer (U : Set G)) {a₀ : G} (ha₀ : a₀ ∈ A) (hxa₀ : x * a₀ ≠ a₀ * x) :
    A ≤ centralizer (U : Set G) ∧ B ≤ centralizer (U : Set G) := by
  obtain ⟨b₀, hb₀, hab₀⟩ := h1 a₀ ha₀
  have hc : a₀ * b₀ ∈ centralizer (U : Set G) := hRU hab₀
  have hxc : x * (a₀ * b₀) * x⁻¹ ∈ centralizer (U : Set G) :=
    CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer hxU hc
  have hxb : x * b₀ = b₀ * x := hAB x hxA b₀ hb₀
  have hmem := (centralizer (U : Set G)).mul_mem hxc ((centralizer (U : Set G)).inv_mem hc)
  have he : x * (a₀ * b₀) * x⁻¹ * (a₀ * b₀)⁻¹ = x * a₀ * x⁻¹ * a₀⁻¹ := by
    have hxb' : b₀ * x⁻¹ = x⁻¹ * b₀ := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hxb, mul_assoc, mul_inv_cancel, mul_one]
    calc x * (a₀ * b₀) * x⁻¹ * (a₀ * b₀)⁻¹ = x * a₀ * (b₀ * x⁻¹) * b₀⁻¹ * a₀⁻¹ := by group
      _ = x * a₀ * (x⁻¹ * b₀) * b₀⁻¹ * a₀⁻¹ := by rw [hxb']
      _ = x * a₀ * x⁻¹ * a₀⁻¹ := by group
  rw [he] at hmem
  refine le_of_subdirect hAB hAs (fun a ha => ?_) (fun b hb => ?_)
    (A.mul_mem (A.mul_mem (A.mul_mem hxA ha₀) (A.inv_mem hxA)) (A.inv_mem ha₀)) hmem ?_
  · obtain ⟨b, hb, hab⟩ := h1 a ha
    exact ⟨b, hb, hRU hab⟩
  · obtain ⟨a, ha, hab⟩ := h2 b hb
    exact ⟨a, ha, hRU hab⟩
  · intro h1'
    apply hxa₀
    have h3 : x * a₀ * x⁻¹ = a₀ := by
      have := congrArg (· * a₀) h1'
      simpa using this
    calc x * a₀ = x * a₀ * x⁻¹ * x := by group
      _ = a₀ * x := by rw [h3]

theorem eq_top_of_prod_of_ne {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] [IsSimpleGroup Y₁]
    {H : Subgroup (Y₁ × Y₂)} (h1 : ∀ y₁, ∃ y₂, (y₁, y₂) ∈ H) (h2 : ∀ y₂, ∃ y₁, (y₁, y₂) ∈ H)
    {y : Y₁} (hy : (y, (1 : Y₂)) ∈ H) (hy1 : y ≠ 1) : H = ⊤ := by
  set H₁ : Subgroup Y₁ := H.comap (MonoidHom.inl Y₁ Y₂) with hH₁
  have hmem₁ : ∀ x : Y₁, x ∈ H₁ ↔ (x, (1 : Y₂)) ∈ H := fun x => Iff.rfl
  have hnorm : H₁.Normal := ⟨fun x hx g => by
    rw [hmem₁] at hx ⊢
    obtain ⟨g₂, hg⟩ := h1 g
    have h := H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    simpa using h⟩
  have hne : H₁ ≠ ⊥ := by
    intro hbot
    have h := (hmem₁ y).2 hy
    rw [hbot, mem_bot] at h
    exact hy1 h
  have htop : H₁ = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal H₁).resolve_left hne
  rw [eq_top_iff]
  rintro ⟨x₁, x₂⟩ -
  obtain ⟨y₁, hy₁⟩ := h2 x₂
  have h3 : (x₁ * y₁⁻¹, (1 : Y₂)) ∈ H := (hmem₁ _).1 (htop ▸ mem_top _)
  have h := H.mul_mem h3 hy₁
  simpa using h

end Subdirect

section FieldTwist

open CFSG.SeitzReduction.LinearPilot (upperUnit lowerUnit subfieldSL twistedSubfield)

variable {G : Type*} [Group G] {K F : Type*} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F]

theorem range_le_centralizer_of_fieldTwist (hq : 4 ≤ Nat.card K) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {t : G}
    (φ : SL(2, F) →* G)
    (hφt : ∀ A : SL(2, F), t * φ A * t⁻¹ = φ (SpecialLinearGroup.map σ.toRingHom A))
    {Y R : Subgroup G} (hφY : φ.range ≤ centralizer (Y : Set G))
    (hφR : ∀ A : SL(2, K), φ (SpecialLinearGroup.map ι A) ∈ centralizer (R : Set G))
    (hORTH : ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
      S ≤ centralizer ({t * φ (upperUnit 1)} : Set G) → S ≤ centralizer (Y : Set G) →
      φ (upperUnit 1) ∈ S → S ≤ centralizer (R : Set G)) :
    φ.range ≤ centralizer (R : Set G) := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hq
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq
  have hσι : ∀ c : K, σ.toRingHom (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution hσ1 hσσ
  have hFK : Nat.card F = Nat.card K ^ 2 := LinearPilot.natCard_eq_sq_of_trace_one ι hσσ hfix hω
  set z : G := φ (upperUnit 1) with hzdef
  set j : SL(2, K) →* G :=
    φ.comp ((MulAut.conj (upperUnit ω)).toMonoidHom.comp (SpecialLinearGroup.map ι)) with hjdef
  have hj : ∀ s, j s = φ (upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹) :=
    fun s => rfl
  have hfixed : ∀ s, (t * z) * j s * (t * z)⁻¹ = j s := by
    intro s
    set y := upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹ with hydef
    have hy : y ∈ twistedSubfield ι ω := (LinearPilot.mem_twistedSubfield ι).2 ⟨s, rfl⟩
    rw [hj]
    calc t * φ (upperUnit 1) * φ y * (t * φ (upperUnit 1))⁻¹ =
          t * φ (upperUnit 1 * y * (upperUnit 1)⁻¹) * t⁻¹ := by
            simp only [map_mul, map_inv]
            group
      _ = φ (SpecialLinearGroup.map σ.toRingHom (upperUnit 1 * y * (upperUnit 1)⁻¹)) := hφt _
      _ = φ (upperUnit 1 * SpecialLinearGroup.map σ.toRingHom y * upperUnit 1) := by
            congr 1
            rw [map_mul, map_mul, map_inv, LinearPilot.map_upperUnit, map_one,
              LinearPilot.upperUnit_one_inv]
      _ = φ y := by rw [LinearPilot.twistedSubfield_fixed ι σ.toRingHom hσι hω hy]
  have hSt : j.range ≤ centralizer ({t * z} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := hfixed s
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hjφ : j.range ≤ φ.range := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  have hzS : z ∈ j.range := ⟨upperUnit 1, by
    rw [hj, LinearPilot.map_upperUnit, map_one, LinearPilot.upperUnit_mul_comm,
      mul_inv_cancel_right]⟩
  have hS := hORTH j.range (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt (hjφ.trans hφY) hzS
  rw [MonoidHom.range_eq_map, ← LinearPilot.sup_twistedSubfield_eq_top_of_trace_one ι hq hFK hσι hω,
    Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    exact hφR A
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := (LinearPilot.mem_twistedSubfield ι).1 hy
    exact hS ⟨s, rfl⟩

end FieldTwist

section SwapTwist

variable {G : Type*} [Group G]

theorem range_le_centralizer_of_swapTwist {Y : Type*} [Group Y] [IsSimpleGroup Y]
    [Group.IsPerfect Y] {t : G} (ψ : Y × Y →* G) (hψt : ∀ x y : Y, t * ψ (x, y) * t⁻¹ = ψ (y, x))
    {u : Y} (hu2 : u * u = 1) {y₀ : Y} (hy₀ : u * y₀ ≠ y₀ * u) {T R : Subgroup G}
    (hψT : ψ.range ≤ centralizer (T : Set G)) (hψR : ∀ y : Y, ψ (y, y) ∈ centralizer (R : Set G))
    (hORTH : ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
      S ≤ centralizer ({t * ψ (u, u)} : Set G) → S ≤ centralizer (T : Set G) →
      ψ (u, u) ∈ S → S ≤ centralizer (R : Set G)) :
    ψ.range ≤ centralizer (R : Set G) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set θ : Y →* Y × Y := ((MulAut.conj u).toMonoidHom).prod (MonoidHom.id Y) with hθdef
  have hθ : ∀ y, θ y = (u * y * u⁻¹, y) := fun y => rfl
  set j : Y →* G := ψ.comp θ with hjdef
  have hj : ∀ y, j y = ψ (u * y * u⁻¹, y) := fun y => rfl
  have hfixed : ∀ y, (t * ψ (u, u)) * j y * (t * ψ (u, u))⁻¹ = j y := by
    intro y
    rw [hj]
    calc t * ψ (u, u) * ψ (u * y * u⁻¹, y) * (t * ψ (u, u))⁻¹ =
          t * ψ ((u, u) * (u * y * u⁻¹, y) * (u, u)⁻¹) * t⁻¹ := by
            simp only [map_mul, map_inv]
            group
      _ = t * ψ (u * (u * y * u⁻¹) * u⁻¹, u * y * u⁻¹) * t⁻¹ := rfl
      _ = ψ (u * y * u⁻¹, u * (u * y * u⁻¹) * u⁻¹) := hψt _ _
      _ = ψ (u * y * u⁻¹, y) := by
            congr 2
            rw [huinv, ← mul_assoc, ← mul_assoc, hu2, one_mul, mul_assoc, hu2, mul_one]
  have hSt : j.range ≤ centralizer ({t * ψ (u, u)} : Set G) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := hfixed y
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hjψ : j.range ≤ ψ.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  have hzS : ψ (u, u) ∈ j.range := ⟨u, by rw [hj, mul_inv_cancel_right]⟩
  have hS := hORTH j.range (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt (hjψ.trans hψT) hzS
  set H := (centralizer (R : Set G)).comap ψ with hH
  have hΔ : ∀ y : Y, (y, y) ∈ H := hψR
  have hΔ' : ∀ y : Y, (u * y * u⁻¹, y) ∈ H := fun y => hS ⟨y, rfl⟩
  have htop : H = ⊤ := by
    refine eq_top_of_prod_of_ne (fun y => ⟨y, hΔ y⟩) (fun y => ⟨y, hΔ y⟩)
      (y := u * y₀ * u⁻¹ * y₀⁻¹) ?_ ?_
    · have h := H.mul_mem (hΔ' y₀) (H.inv_mem (hΔ y₀))
      simpa using h
    · intro h1
      apply hy₀
      have h2 : u * y₀ * u⁻¹ = y₀ := by
        have := congrArg (· * y₀) h1
        simpa using this
      calc u * y₀ = u * y₀ * u⁻¹ * u := by group
        _ = y₀ * u := by rw [h2]
  rw [MonoidHom.range_eq_map, ← htop]
  exact map_comap_le _ _

end SwapTwist

end CFSG.SeitzReduction.OmegaPilot
