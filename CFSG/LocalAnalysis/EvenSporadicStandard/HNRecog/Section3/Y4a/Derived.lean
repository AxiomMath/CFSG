module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma y4aDerived_map_commutator_eq_top {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π) :
    (_root_.commutator ↥X).map π = ⊤ := by
  have hperf : _root_.commutator (alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (α := Fin 5) (by rw [Nat.card_fin])
  rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ]
  simpa [_root_.commutator_def] using hperf

private lemma y4aDerived_psi_surjective {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π) :
    Function.Surjective (π.comp (Subgroup.inclusion (derivedOf_le X))) := by
  intro σ
  have hσ : σ ∈ (_root_.commutator ↥X).map π := by
    rw [y4aDerived_map_commutator_eq_top π hπ]
    trivial
  obtain ⟨d, hd, hdσ⟩ := Subgroup.mem_map.mp hσ
  let l0 : ↥(derivedOf X) := ⟨(d : G), Subgroup.mem_map.mpr ⟨d, hd, by simp⟩⟩
  refine ⟨l0, ?_⟩
  have hincl : Subgroup.inclusion (derivedOf_le X) l0 = d := by
    apply Subtype.ext
    simp [l0]
  show π (Subgroup.inclusion (derivedOf_le X) l0) = σ
  rw [hincl, hdσ]

private lemma y4aDerived_pCore_le_ker {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π) :
    CFSG.pCore 2 ↥(derivedOf X) ≤
      (π.comp (Subgroup.inclusion (derivedOf_le X))).ker := by
  let ψ := π.comp (Subgroup.inclusion (derivedOf_le X))
  change CFSG.pCore 2 ↥(derivedOf X) ≤ ψ.ker
  have hψsurj : Function.Surjective ψ := y4aDerived_psi_surjective π hπ
  have hPnorm : (CFSG.pCore 2 ↥(derivedOf X)).Normal := inferInstance
  have hmap_normal : ((CFSG.pCore 2 ↥(derivedOf X)).map ψ).Normal :=
    Subgroup.Normal.map hPnorm ψ hψsurj
  have hmap_p : IsPGroup 2 ↥((CFSG.pCore 2 ↥(derivedOf X)).map ψ) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(derivedOf X))).map ψ
  haveI : ((CFSG.pCore 2 ↥(derivedOf X)).map ψ).Normal := hmap_normal
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((CFSG.pCore 2 ↥(derivedOf X)).map ψ) with hbot | htop
  · exact (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥(derivedOf X)) (f := ψ)).mp hbot
  · exfalso
    have htop2 : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) := htop ▸ hmap_p
    obtain ⟨n, hn⟩ := htop2.exists_card_eq
    rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hn
    norm_num at hn
    have hnle : n ≤ 6 := by
      by_contra h
      simp only [not_le] at h
      have hle : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hn] at hle
      norm_num at hle
    interval_cases n <;> norm_num at hn

private lemma y4aDerived_ker_le_pCore {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hK : Nat.card ↥π.ker = 64) :
    (π.comp (Subgroup.inclusion (derivedOf_le X))).ker ≤
      CFSG.pCore 2 ↥(derivedOf X) := by
  let ψ := π.comp (Subgroup.inclusion (derivedOf_le X))
  change ψ.ker ≤ CFSG.pCore 2 ↥(derivedOf X)
  have hker_p : IsPGroup 2 ↥ψ.ker := by
    have hπker_p : IsPGroup 2 ↥π.ker := IsPGroup.of_card (n := 6) (by rw [hK]; norm_num)
    have heq : ψ.ker = (π.ker).comap (Subgroup.inclusion (derivedOf_le X)) := by
      ext l
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker]
      rfl
    rw [heq]
    exact hπker_p.comap_of_injective _ (Subgroup.inclusion_injective _)
  exact le_sSup ⟨inferInstance, hker_p⟩

private lemma y4aDerived_ker_eq_pCore {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (hK : Nat.card ↥π.ker = 64) :
    (π.comp (Subgroup.inclusion (derivedOf_le X))).ker = CFSG.pCore 2 ↥(derivedOf X) :=
  le_antisymm (y4aDerived_ker_le_pCore π hK) (y4aDerived_pCore_le_ker π hπ)

private lemma y4aDerived_ker_iff {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (hK : Nat.card ↥π.ker = 64) :
    ∀ l : ↥(derivedOf X),
      (π.comp (Subgroup.inclusion (derivedOf_le X))) l = 1 ↔
        (l : G) ∈ CFSG.Open.pCoreOf 2 (derivedOf X) := by
  intro l
  let ψ := π.comp (Subgroup.inclusion (derivedOf_le X))
  have hker : ψ.ker = CFSG.pCore 2 ↥(derivedOf X) := y4aDerived_ker_eq_pCore π hπ hK
  change ψ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 (derivedOf X)
  rw [← MonoidHom.mem_ker, hker, CFSG.Open.pCoreOf, Subgroup.mem_map]
  constructor
  · intro hl
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l', hl', hl'eq⟩
    exact Subtype.ext hl'eq ▸ hl'

private lemma y4aDerived_card {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (hK : Nat.card ↥π.ker = 64)
    (hP : Nat.card ↥(CFSG.Open.pCoreOf 2 (derivedOf X)) = 16) :
    Nat.card ↥(derivedOf X) = 960 := by
  let ψ := π.comp (Subgroup.inclusion (derivedOf_le X))
  have hψsurj : Function.Surjective ψ := y4aDerived_psi_surjective π hπ
  have hker : ψ.ker = CFSG.pCore 2 ↥(derivedOf X) := y4aDerived_ker_eq_pCore π hπ hK
  have hPcard : Nat.card ↥(CFSG.pCore 2 ↥(derivedOf X)) = 16 := by
    have h1 : Nat.card ↥(CFSG.Open.pCoreOf 2 (derivedOf X)) =
        Nat.card ↥(CFSG.pCore 2 ↥(derivedOf X)) := by
      rw [CFSG.Open.pCoreOf,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective (derivedOf X))]
    rw [← h1, hP]
  have h := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψsurj
  rw [hker, hPcard, nat_card_alternatingGroup, Nat.card_fin] at h
  norm_num at h
  exact h.symm

private lemma y4aDerived_action {G : Type} [Group G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (hK : Nat.card ↥π.ker = 64)
    (hKab : ∀ k₁ ∈ π.ker, ∀ k₂ ∈ π.ker, k₁ * k₂ = k₂ * k₁) :
    ∀ x ∈ X, ∃ l ∈ derivedOf X, ∀ m ∈ CFSG.Open.pCoreOf 2 (derivedOf X),
      x * m * x⁻¹ = l * m * l⁻¹ := by
  let ψ := π.comp (Subgroup.inclusion (derivedOf_le X))
  have hψsurj : Function.Surjective ψ := y4aDerived_psi_surjective π hπ
  have hker_iff := y4aDerived_ker_iff π hπ hK
  intro x hx
  obtain ⟨l, hl⟩ := hψsurj (π ⟨x, hx⟩)
  refine ⟨(l : G), l.2, fun m hm => ?_⟩
  set k : ↥X := (Subgroup.inclusion (derivedOf_le X) l)⁻¹ * ⟨x, hx⟩ with hk
  have hk_ker : k ∈ π.ker := by
    rw [MonoidHom.mem_ker, hk]
    simp only [map_mul, map_inv]
    have hl' : π (Subgroup.inclusion (derivedOf_le X) l) = π ⟨x, hx⟩ := by
      show ψ l = π ⟨x, hx⟩
      exact hl
    rw [hl', inv_mul_cancel]
  have hmX' : m ∈ derivedOf X :=
    Subgroup.map_subtype_le (CFSG.pCore 2 ↥(derivedOf X)) hm
  have hmX : m ∈ X := derivedOf_le X hmX'
  have hm_ker : (⟨m, hmX⟩ : ↥X) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : ψ (⟨m, hmX'⟩ : ↥(derivedOf X)) = 1 := (hker_iff ⟨m, hmX'⟩).mpr hm
    have h2 : (⟨m, hmX⟩ : ↥X) = Subgroup.inclusion (derivedOf_le X) ⟨m, hmX'⟩ := by
      apply Subtype.ext
      simp
    rw [h2]
    show ψ (⟨m, hmX'⟩ : ↥(derivedOf X)) = 1
    exact h1
  have hk_comm := hKab k hk_ker ⟨m, hmX⟩ hm_ker
  have hk_commG : (k : G) * m = m * (k : G) := by
    simpa using congrArg Subtype.val hk_comm
  have hxlk : x = (l : G) * (k : G) := by
    have h1 : Subgroup.inclusion (derivedOf_le X) l * k = ⟨x, hx⟩ := by
      rw [hk]; group
    have h2 := congrArg Subtype.val h1
    simpa using h2.symm
  have hkm : (k : G) * m * (k : G)⁻¹ = m := by
    rw [hk_commG]; group
  calc x * m * x⁻¹ = ((l : G) * (k : G)) * m * ((l : G) * (k : G))⁻¹ := by rw [hxlk]
    _ = (l : G) * ((k : G) * m * (k : G)⁻¹) * (l : G)⁻¹ := by group
    _ = (l : G) * m * (l : G)⁻¹ := by rw [hkm]

theorem y4a_derived_of_hom {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (π : ↥X →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (hK : Nat.card ↥π.ker = 64) (hKab : ∀ k₁ ∈ π.ker, ∀ k₂ ∈ π.ker, k₁ * k₂ = k₂ * k₁)
    (hP : Nat.card ↥(CFSG.Open.pCoreOf 2 (derivedOf X)) = 16) :
    Nat.card ↥(derivedOf X) = 960 ∧
      (∀ x ∈ X, ∃ l ∈ derivedOf X, ∀ m ∈ CFSG.Open.pCoreOf 2 (derivedOf X),
        x * m * x⁻¹ = l * m * l⁻¹) ∧
      ∃ ψ : ↥(derivedOf X) →* alternatingGroup (Fin 5), Function.Surjective ψ ∧
        ∀ l : ↥(derivedOf X), ψ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 (derivedOf X) :=
  ⟨y4aDerived_card π hπ hK hP, y4aDerived_action π hπ hK hKab,
    π.comp (Subgroup.inclusion (derivedOf_le X)), y4aDerived_psi_surjective π hπ,
    y4aDerived_ker_iff π hπ hK⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
