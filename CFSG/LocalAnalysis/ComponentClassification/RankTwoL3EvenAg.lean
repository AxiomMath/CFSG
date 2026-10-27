module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenT

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial LinearFlag
  FieldFourCover CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {A : Subgroup G} {ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)}

omit [Finite F] [CharP F 2] in
theorem commute_torus_centerA (l : Fˣ) (γ : MulAut (projectiveSL 3 F))
    {z : MulAut (projectiveSL 3 F)} (hz : z ∈ centerA γ) :
    γ * MulAut.conj (projTorus F l) * γ⁻¹ * z = z * (γ * MulAut.conj (projTorus F l) * γ⁻¹) := by
  obtain ⟨z₀, hz₀, rfl⟩ := mem_centerA.1 hz
  have h := projTorus_mul_comm_of_mem_projCenterW l hz₀
  calc γ * MulAut.conj (projTorus F l) * γ⁻¹ * (γ * MulAut.conj z₀ * γ⁻¹)
      = γ * MulAut.conj (projTorus F l * z₀) * γ⁻¹ := by rw [map_mul]; group
    _ = γ * MulAut.conj (z₀ * projTorus F l) * γ⁻¹ := by rw [h]
    _ = γ * MulAut.conj z₀ * γ⁻¹ * (γ * MulAut.conj (projTorus F l) * γ⁻¹) := by
        rw [map_mul]; group

omit [Finite F] [CharP F 2] in
theorem conj_torus_mem_unipA (l : Fˣ) (γ : MulAut (projectiveSL 3 F))
    {s : MulAut (projectiveSL 3 F)} (hs : s ∈ unipA γ) :
    γ * MulAut.conj (projTorus F l) * γ⁻¹ * s * (γ * MulAut.conj (projTorus F l) * γ⁻¹)⁻¹ ∈
      unipA γ := by
  obtain ⟨u, hu, rfl⟩ := mem_unipA.1 hs
  refine mem_unipA.2 ⟨projTorus F l * u * (projTorus F l)⁻¹, projTorus_conj_mem l hu, ?_⟩
  rw [map_mul, map_mul, map_inv]
  group

omit [Finite F] [CharP F 2] in
theorem conj_mem_centerA_iff {γ : MulAut (projectiveSL 3 F)} {p : projectiveSL 3 F} :
    γ * MulAut.conj p * γ⁻¹ ∈ centerA γ ↔ p ∈ projCenterW F := by
  constructor
  · intro h
    obtain ⟨z, hz, hzp⟩ := mem_centerA.1 h
    rw [conj_injective_projectiveSL (mul_right_cancel (mul_left_cancel hzp))]
    exact hz
  · intro h
    exact mem_centerA.2 ⟨p, h, rfl⟩

omit [Finite F] [CharP F 2] in
theorem unipA_conj (y : projectiveSL 3 F) :
    unipA (MulAut.conj y) =
      ((projUnip F).map (MulAut.conj y : projectiveSL 3 F →* projectiveSL 3 F)).map (conjP F) := by
  ext s
  rw [mem_unipA]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, by rw [← conj_map_eq]; rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [← conj_map_eq]; rfl⟩

theorem exists_eq_unipA {m : ℕ} (hF : Nat.card F = 2 ^ m)
    {Q : Subgroup (MulAut (projectiveSL 3 F))} (hQ : Q ≤ innerP F)
    (hcard : Nat.card Q = Nat.card F * Nat.card F * Nat.card F) :
    ∃ δ : MulAut (projectiveSL 3 F), Q = unipA δ := by
  set Q' := Q.comap (conjP F) with hQ'
  have hmap : Q'.map (conjP F) = Q := map_comap_eq_self hQ
  have hcard' : Nat.card Q' = Nat.card (projUnip F) := by
    rw [card_projUnip, ← hcard, ← hmap, card_map_of_injective conj_injective_projectiveSL]
  have h2 : IsPGroup 2 Q' := by
    refine IsPGroup.of_card (n := 3 * m) ?_
    rw [hcard', card_projUnip, hF, ← pow_add, ← pow_add]
    ring_nf
  obtain ⟨y, hy⟩ := exists_eq_map_conj_projUnip h2 hcard'
  refine ⟨MulAut.conj y, ?_⟩
  rw [unipA_conj, ← hy, hmap]

omit [Finite F] [CharP F 2] in
theorem mem_centerA_iff {H : Type*} [Group H] {f : H →* MulAut (projectiveSL 3 F)}
    (hf : Function.Injective f) {δ : MulAut (projectiveSL 3 F)}
    (hr : ∀ s, s ∈ unipA δ ↔ ∃ x, f x = s) (x : H) :
    f x ∈ centerA δ ↔ ∀ y, x * y = y * x := by
  constructor
  · intro h y
    apply hf
    rw [map_mul, map_mul]
    exact commute_centerA_unipA h ((hr _).2 ⟨y, rfl⟩)
  · intro h
    have hx : f x ∈ unipA δ := (hr _).2 ⟨x, rfl⟩
    refine mem_centerA_of_commute hx ?_ ?_
    · obtain ⟨y, hy⟩ := (hr _).1 (mem_unipA.2 ⟨_, mem_projUnip.2 ⟨1, 0, 0, rfl⟩, rfl⟩)
      rw [← hy, ← map_mul, ← map_mul, h y]
    · obtain ⟨y, hy⟩ := (hr _).1 (mem_unipA.2 ⟨_, mem_projUnip.2 ⟨0, 1, 0, rfl⟩, rfl⟩)
      rw [← hy, ← map_mul, ← map_mul, h y]

theorem exists_eq_conj_torus_of_unipA {α δ : MulAut (projectiveSL 3 F)} (hα : Odd (orderOf α))
    (hZ : ∀ z ∈ centerA δ, α * z = z * α) {q : MulAut (projectiveSL 3 F)} (hq : q ∈ unipA δ)
    (hU : ⁅α, q⁆ ∉ centerA δ) :
    ∃ (ε : MulAut (projectiveSL 3 F)) (b : Fˣ), b ≠ 1 ∧
      α = ε * conjAut 3 F (torusGL b) * ε⁻¹ := by
  have hodd : Odd (orderOf (δ⁻¹ * α * δ)) := by
    have h := orderOf_injective (MulAut.conj δ⁻¹).toMonoidHom (MulAut.conj δ⁻¹).injective α
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    rwa [h]
  have hZ' : ∀ z ∈ projCenterW F, (δ⁻¹ * α * δ) z = z := by
    intro z hz
    have h1 := hZ _ (mem_centerA.2 ⟨z, hz, rfl⟩)
    have h2 : MulAut.conj ((δ⁻¹ * α * δ) z) = MulAut.conj z := by
      rw [conj_map_eq]
      calc δ⁻¹ * α * δ * MulAut.conj z * (δ⁻¹ * α * δ)⁻¹
          = δ⁻¹ * (α * (δ * MulAut.conj z * δ⁻¹)) * α⁻¹ * δ := by group
        _ = δ⁻¹ * ((δ * MulAut.conj z * δ⁻¹) * α) * α⁻¹ * δ := by rw [h1]
        _ = MulAut.conj z := by group
    exact conj_injective_projectiveSL h2
  obtain ⟨u, hu, rfl⟩ := mem_unipA.1 hq
  have hU' : ∃ u ∈ projUnip F, (δ⁻¹ * α * δ) u * u⁻¹ ∉ projCenterW F := by
    refine ⟨u, hu, fun h => hU (mem_centerA.2 ⟨_, h, ?_⟩)⟩
    rw [map_mul, map_inv, conj_map_eq, commutatorElement_def]
    group
  obtain ⟨v, b, hb, hv⟩ := exists_eq_conj_torus hodd hZ' hU'
  refine ⟨δ * MulAut.conj v, b, hb, ?_⟩
  calc α = δ * (δ⁻¹ * α * δ) * δ⁻¹ := by group
    _ = δ * MulAut.conj v * conjAut 3 F (torusGL b) * (δ * MulAut.conj v)⁻¹ := by
        rw [hv]; group

omit [Finite F] [CharP F 2] in
theorem exists_two_lift_of_isPGroup
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    {S : Subgroup (MulAut (projectiveSL 3 F))}
    (hS : S ≤ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range)
    (h2 : IsPGroup 2 S) :
    ∃ P : Subgroup G, ∃ hPA : P ≤ A, IsPGroup 2 P ∧
      (∀ p : G, ∀ hp : p ∈ P, ψ ⟨p, le_normalizer (hPA hp)⟩ ∈ S) ∧
      ∀ s ∈ S, ∃ p : G, ∃ hp : p ∈ P, ψ ⟨p, le_normalizer (hPA hp)⟩ = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Uh := liftIn ψ S with hUh
  let f : Uh →* S := (ψ.comp (Subgroup.inclusion (liftIn_le.trans le_normalizer))).codRestrict S
    fun x => (mem_liftIn.1 x.2).2
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨a, ha, has⟩ := hψ.exists_eq s (hS hs)
    exact ⟨⟨a, mem_liftIn.2 ⟨ha, has ▸ hs⟩⟩, Subtype.ext has⟩
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 Uh) := inferInstance
  have htop : ((Q₀.mapSurjective hf : Sylow 2 S) : Subgroup S) = ⊤ :=
    ((Q₀.mapSurjective hf).3 (h2.to_subgroup ⊤) le_top).symm
  set P := (Q₀ : Subgroup Uh).map Uh.subtype with hP
  have hPU : P ≤ Uh := map_subtype_le _
  have hPA : P ≤ A := hPU.trans liftIn_le
  refine ⟨P, hPA, Q₀.isPGroup'.map _, fun p hp => (mem_liftIn.1 (hPU hp)).2, fun s hs => ?_⟩
  have hmem : (⟨s, hs⟩ : S) ∈ ((Q₀.mapSurjective hf : Sylow 2 S) : Subgroup S) := by
    rw [htop]
    exact mem_top _
  obtain ⟨q, hq, hqs⟩ := hmem
  exact ⟨q, ⟨q, hq, rfl⟩, congrArg Subtype.val hqs⟩

omit [Finite G] [Finite F] [CharP F 2] in
theorem mem_of_psi_mem
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {S : Subgroup (MulAut (projectiveSL 3 F))} {P : Subgroup G} (hPA : P ≤ A) (hP2 : IsPGroup 2 P)
    (hSP : ∀ s ∈ S, ∃ p : G, ∃ hp : p ∈ P, ψ ⟨p, le_normalizer (hPA hp)⟩ = s)
    {x : G} (hxA : x ∈ A) {k : ℕ} (hxk : x ^ 2 ^ k = 1) (hxS : ψ ⟨x, le_normalizer hxA⟩ ∈ S) :
    x ∈ P := by
  obtain ⟨p, hp, hpx⟩ := hSP _ hxS
  obtain ⟨j, hj⟩ := exists_pow_eq_one_of_isPGroup hP2 hp
  have h1 : x ^ 2 ^ (k + j) = 1 := by rw [pow_add, pow_mul, hxk, one_pow]
  have h2 : p ^ 2 ^ (k + j) = 1 := by rw [add_comm, pow_add, pow_mul, hj, one_pow]
  rw [eq_of_psi_eq hψ hZ hxA (hPA hp) h1 h2 hpx.symm]
  exact hp

omit [Finite F] [CharP F 2] in
theorem mem_normalizer_of_conj_mem {H : Subgroup G} {y : G} (h : ∀ x ∈ H, y * x * y⁻¹ ∈ H) :
    y ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [card_map_of_injective (MulAut.conj y).injective]

omit [Finite F] [CharP F 2] in
theorem mem_normalizer_of_psi
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {S : Subgroup (MulAut (projectiveSL 3 F))} {P : Subgroup G} (hPA : P ≤ A) (hP2 : IsPGroup 2 P)
    (hPS : ∀ p : G, ∀ hp : p ∈ P, ψ ⟨p, le_normalizer (hPA hp)⟩ ∈ S)
    (hSP : ∀ s ∈ S, ∃ p : G, ∃ hp : p ∈ P, ψ ⟨p, le_normalizer (hPA hp)⟩ = s)
    {y : G} (hyN : y ∈ normalizer (A : Set G))
    (hy : ∀ s ∈ S, ψ ⟨y, hyN⟩ * s * (ψ ⟨y, hyN⟩)⁻¹ ∈ S) : y ∈ normalizer (P : Set G) := by
  refine mem_normalizer_of_conj_mem fun p hp => ?_
  have hmem : y * p * y⁻¹ ∈ A := (mem_normalizer_iff.1 hyN p).1 (hPA hp)
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hP2 hp
  refine mem_of_psi_mem hψ hZ hPA hP2 hSP hmem (k := k) ?_ ?_
  · rw [conj_pow, hk, mul_one, mul_inv_cancel]
  · have h1 : (⟨y * p * y⁻¹, le_normalizer hmem⟩ : normalizer (A : Set G)) =
        ⟨y, hyN⟩ * ⟨p, le_normalizer (hPA hp)⟩ * ⟨y, hyN⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hy _ (hPS p hp)

omit [Finite G] [Finite F] [CharP F 2] in
theorem injective_comp_inclusion
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    {H : Subgroup G} (hHN : H ≤ normalizer (A : Set G))
    (hHK : H ⊓ centralizer (A : Set G) = ⊥) :
    Function.Injective (ψ.comp (Subgroup.inclusion hHN)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (x : G) ∈ centralizer (A : Set G) := (hψ.eq_one_iff _).1 hx
  have h2 : (x : G) ∈ H ⊓ centralizer (A : Set G) := ⟨x.2, h1⟩
  rw [hHK, mem_bot] at h2
  exact Subtype.ext h2

theorem exists_conjAct_eq_torus (hA : standardComponentIsStandard A)
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {m : ℕ} (hm : 3 ≤ m) (hF : Nat.card F = 2 ^ m) {g : G}
    (hKey : Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) g : Subgroup G)))
    {t₀ : G} (ht₀K : t₀ ∈ rightConjugate (centralizer (A : Set G)) g)
    (ht₀N : t₀ ∈ normalizer (A : Set G)) (ht₀2 : t₀ * t₀ = 1) (ht₀1 : t₀ ≠ 1)
    (ht₀Z : ∀ z ∈ A ⊓ centralizer (A : Set G), t₀ * z = z * t₀)
    {γ : MulAut (projectiveSL 3 F)} (hγ : ψ ⟨t₀, ht₀N⟩ = γ * MulAut.conj (x0 F) * γ⁻¹)
    {l : Fˣ} (hl : (l : F) ^ 3 ≠ 1) {w : G} (hwA : w ∈ A)
    (hwψ : ψ ⟨w, le_normalizer hwA⟩ = γ * MulAut.conj (projTorus F l) * γ⁻¹)
    (hwodd : Odd (orderOf w)) (hwN : w ∈ normalizer (rightConjugate A g : Set G)) :
    ∃ (ε : MulAut (projectiveSL 3 F)) (b : Fˣ), b ≠ 1 ∧
      conjAct ψ g ⟨w, hwN⟩ = ε * conjAut 3 F (torusGL b) * ε⁻¹ := by
  have hψg := isActionHom_conjAct hψ g
  obtain ⟨P, hPA, hP2, hPS, hSP⟩ :=
    exists_two_lift_of_isPGroup hψ (unipA_le_innerP γ) (isPGroup_unipA hF γ)
  have htight := AS76b.tightlyEmbedded_rightConjugate (AS76b.tightlyEmbedded_centralizer hA) g
  have hPN : P ≤ normalizer (rightConjugate A g : Set G) := by
    intro p hp
    rw [← normalizer_rightConjugate_centralizer hA g]
    refine mem_normalizer_of_commute_of_mem htight ht₀K ht₀1 ht₀2 ?_
    refine commute_of_psi_commute hψ hZ ht₀N ht₀2 ht₀Z (hPA hp) ?_
    rw [hγ]
    exact (commute_centerA_unipA (mem_centerA.2 ⟨x0 F, x0_mem_projCenterW, rfl⟩)
      (hPS p hp)).symm
  have hPK : P ⊓ centralizer (A : Set G) = ⊥ :=
    two_subgroup_of_odd_eq_bot _ _ hP2.to_inf_left hZ (inf_le_inf_right _ hPA)
  have hPKg : P ⊓ centralizer (rightConjugate A g : Set G) = ⊥ := by
    rw [centralizer_rightConjugate_eq]
    exact two_subgroup_of_odd_eq_bot _ _ hP2.to_inf_left hKey (inf_le_inf_right _ hPA)
  set f₁ := ψ.comp (Subgroup.inclusion (hPA.trans le_normalizer)) with hf₁def
  set f₂ := (conjAct ψ g).comp (Subgroup.inclusion hPN) with hf₂def
  have hf₁ : Function.Injective f₁ := injective_comp_inclusion hψ _ hPK
  have hf₂ : Function.Injective f₂ := injective_comp_inclusion hψg _ hPKg
  have hr₁ : ∀ s, s ∈ unipA γ ↔ ∃ x : P, f₁ x = s := by
    intro s
    constructor
    · intro hs
      obtain ⟨p, hp, hps⟩ := hSP s hs
      exact ⟨⟨p, hp⟩, hps⟩
    · rintro ⟨x, rfl⟩
      exact hPS x x.2
  have hwP : w ∈ normalizer (P : Set G) := by
    refine mem_normalizer_of_psi hψ hZ hPA hP2 hPS hSP (le_normalizer hwA) fun s hs => ?_
    rw [hwψ]
    exact conj_torus_mem_unipA l γ hs
  set α := conjAct ψ g ⟨w, hwN⟩ with hα
  have hconjP : ∀ x : P, ∃ y : P, f₂ y = α * f₂ x * α⁻¹ ∧
      f₁ y = ψ ⟨w, le_normalizer hwA⟩ * f₁ x * (ψ ⟨w, le_normalizer hwA⟩)⁻¹ := by
    intro x
    have hy : w * x * w⁻¹ ∈ P := (mem_normalizer_iff.1 hwP x).1 x.2
    refine ⟨⟨w * x * w⁻¹, hy⟩, ?_, ?_⟩
    · have h1 : (⟨w * x * w⁻¹, hPN hy⟩ : normalizer (rightConjugate A g : Set G)) =
          ⟨w, hwN⟩ * ⟨x, hPN x.2⟩ * ⟨w, hwN⟩⁻¹ := rfl
      show conjAct ψ g ⟨w * x * w⁻¹, hPN hy⟩ = α * conjAct ψ g ⟨x, hPN x.2⟩ * α⁻¹
      rw [h1, map_mul, map_mul, map_inv]
    · have h1 : (⟨w * x * w⁻¹, le_normalizer (hPA hy)⟩ : normalizer (A : Set G)) =
          ⟨w, le_normalizer hwA⟩ * ⟨x, le_normalizer (hPA x.2)⟩ * ⟨w, le_normalizer hwA⟩⁻¹ := rfl
      show ψ ⟨w * x * w⁻¹, le_normalizer (hPA hy)⟩ =
        ψ ⟨w, le_normalizer hwA⟩ * ψ ⟨x, le_normalizer (hPA x.2)⟩ * (ψ ⟨w, le_normalizer hwA⟩)⁻¹
      rw [h1, map_mul, map_mul, map_inv]
  have hinn : ∀ x : P, f₂ x ∈ innerP F := by
    intro x
    obtain ⟨u, hu, hux⟩ := mem_unipA.1 ((hr₁ _).2 ⟨x, rfl⟩)
    obtain ⟨v, hv, v', hv', v'', hv'', huv⟩ := exists_commutator_mul_eq hl hu
    obtain ⟨x₁, hx₁⟩ := (hr₁ _).1 (mem_unipA.2 ⟨v, hv, rfl⟩)
    obtain ⟨x₂, hx₂⟩ := (hr₁ _).1 (mem_unipA.2 ⟨v', hv', rfl⟩)
    obtain ⟨x₃, hx₃⟩ := (hr₁ _).1 (mem_unipA.2 ⟨v'', hv'', rfl⟩)
    obtain ⟨y, hy₂, hy₁⟩ := hconjP x₁
    have hx : x = y * x₁⁻¹ * ⁅x₂, x₃⁆ := by
      apply hf₁
      rw [map_mul, map_mul, map_inv, map_commutatorElement, hy₁, hwψ, hx₁, hx₂, hx₃, hux, huv,
        map_mul, map_commutatorElement, map_commutatorElement]
      simp only [commutatorElement_def]
      group
    have hD : f₂ x ∈ linearAutGroup 3 F := by
      rw [hx, map_mul, map_mul, map_inv, map_commutatorElement, hy₂]
      refine mul_mem ?_ (commutatorElement_mem_linearAutGroup (by omega) hF _ _)
      rw [← commutatorElement_def]
      exact commutatorElement_mem_linearAutGroup (by omega) hF _ _
    obtain ⟨k, hk⟩ := hP2 x
    exact mem_inner_of_mem_linearAutGroup hD (k := k) (by rw [← map_pow, hk, map_one])
  have hcardP : Nat.card P = Nat.card F * Nat.card F * Nat.card F := by
    rw [← card_unipA γ]
    have hrange : f₁.range = unipA γ := by
      ext s
      rw [hr₁ s, MonoidHom.mem_range]
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hf₁).toEquiv
  have hQinn : f₂.range ≤ innerP F := by
    rintro _ ⟨x, rfl⟩
    exact hinn x
  have hQcard : Nat.card f₂.range = Nat.card F * Nat.card F * Nat.card F := by
    rw [← hcardP]
    exact (Nat.card_congr (MonoidHom.ofInjective hf₂).toEquiv).symm
  obtain ⟨δ, hδ⟩ := exists_eq_unipA hF hQinn hQcard
  have hr₂ : ∀ s, s ∈ unipA δ ↔ ∃ x : P, f₂ x = s := by
    intro s
    rw [← hδ, MonoidHom.mem_range]
  have hαodd : Odd (orderOf α) := by
    refine hwodd.of_dvd_nat ?_
    refine (orderOf_map_dvd (conjAct ψ g) _).trans ?_
    rw [Subgroup.orderOf_mk]
  have hZα : ∀ z ∈ centerA δ, α * z = z * α := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hr₂ z).1 (centerA_le_unipA δ hz)
    have hx1 := (mem_centerA_iff hf₁ hr₁ x).2 ((mem_centerA_iff hf₂ hr₂ x).1 hz)
    obtain ⟨y, hy₂, hy₁⟩ := hconjP x
    have hyx : y = x := by
      apply hf₁
      rw [hy₁, hwψ, commute_torus_centerA l γ hx1, mul_inv_cancel_right]
    rw [hyx] at hy₂
    calc α * f₂ x = α * f₂ x * α⁻¹ * α := by group
      _ = f₂ x * α := by rw [← hy₂]
  obtain ⟨x₁, hx₁⟩ := (hr₁ _).1 (mem_unipA.2 ⟨_, mem_projUnip.2 ⟨1, 0, 0, rfl⟩, rfl⟩)
  obtain ⟨y, hy₂, hy₁⟩ := hconjP x₁
  refine exists_eq_conj_torus_of_unipA hαodd hZα ((hr₂ _).2 ⟨x₁, rfl⟩) fun hc => ?_
  have hc' : f₂ (y * x₁⁻¹) ∈ centerA δ := by
    rw [map_mul, map_inv, hy₂, ← commutatorElement_def]
    exact hc
  have hc₁ := (mem_centerA_iff hf₁ hr₁ _).2 ((mem_centerA_iff hf₂ hr₂ _).1 hc')
  rw [map_mul, map_inv, hy₁, hwψ, hx₁, ← commutatorElement_def, commutatorElement_conj,
    ← map_commutatorElement, conj_mem_centerA_iff] at hc₁
  exact commutatorElement_projTorus_not_mem hl hc₁

omit [Finite G] [Finite F] [CharP F 2] in
theorem odd_card_rightConjugate_inf_centralizer {g : G}
    (hKey : Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) g⁻¹ : Subgroup G))) :
    Odd (Nat.card (rightConjugate A g ⊓ centralizer (A : Set G) : Subgroup G)) := by
  have h : rightConjugate A g ⊓ centralizer (A : Set G) =
      rightConjugate (A ⊓ rightConjugate (centralizer (A : Set G)) g⁻¹) g := by
    ext x
    simp only [mem_inf, mem_rightConjugate_iff, inv_inv]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa [mul_assoc] using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa [mul_assoc] using h2⟩
  rw [h, rightConjugate_card]
  exact hKey

theorem not_le_normalizer_of_torus [Group.IsPerfect (SL2 F)] (hA : standardComponentIsStandard A)
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    {g : G} (hg : g ∉ normalizer (A : Set G))
    (hKey : Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) g⁻¹ : Subgroup G)))
    {T R : Subgroup G} (hTK : T ≤ rightConjugate (centralizer (A : Set G)) g)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hR1 : R ≠ ⊥)
    (hRN : R ≤ normalizer (rightConjugate A g : Set G)) {w : G} (hwA : w ∈ A)
    (hwN : w ∈ normalizer (rightConjugate A g : Set G)) {ε : MulAut (projectiveSL 3 F)}
    {b : Fˣ} (hb : b ≠ 1)
    (hα : conjAct ψ g ⟨w, hwN⟩ = ε * conjAut 3 F (torusGL b) * ε⁻¹) :
    ¬ centralizer (zpowers w : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  intro hle
  have hψg := isActionHom_conjAct hψ g
  set Lg := leviLift (conjAct ψ g) (leviA ε) with hLg
  have hLgW : Lg ≤ centralizer (zpowers w : Set G) := by
    intro x hx
    have h := leviLift_le_centralizer hψg hwN (fun s hs => by
      rw [hα]
      exact commute_torus_leviA b ε hs) hx
    rw [mem_centralizer_zpowers_iff]
    exact (mem_centralizer_singleton_iff.1 h).symm
  have hLgT : Lg ≤ centralizer (T : Set G) := by
    intro x hx
    have hxA : x ∈ rightConjugate A g := leviLift_le hx
    rw [mem_centralizer_iff]
    intro t ht
    have htC : t ∈ centralizer (rightConjugate A g : Set G) := by
      rw [centralizer_rightConjugate_eq]
      exact hTK ht
    exact (mem_centralizer_iff.1 htC x hxA).symm
  have hLgR : Lg ≤ normalizer (R : Set G) := fun x hx => hle ⟨hLgW hx, hLgT hx⟩
  have hodd := odd_card_rightConjugate_inf_centralizer hKey
  have hRL : ∀ r ∈ R, ∀ x ∈ Lg, r * x = x * r := by
    intro r hr x hx
    have hxA : x ∈ rightConjugate A g := leviLift_le hx
    have h1 : ⁅x, r⁆ ∈ R := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (hLgR hx) r).1 hr) (inv_mem hr)
    have h2 : ⁅x, r⁆ ∈ rightConjugate A g := by
      rw [commutatorElement_def]
      have h3 := (mem_normalizer_iff.1 (hRN hr) x⁻¹).1 (inv_mem hxA)
      have h4 := mul_mem hxA h3
      simpa [mul_assoc] using h4
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hR.isPGroup h1
    have h5 := eq_one_of_odd_of_pow_two (odd_orderOf_of_mem hodd ⟨h2, hR.le h1⟩) hk
    rw [commutatorElement_eq_one_iff_mul_comm] at h5
    exact h5.symm
  have hRK : R ≤ rightConjugate (centralizer (A : Set G)) g := by
    intro r hr
    have hrN := hRN hr
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hR.isPGroup hr
    have hψk : (conjAct ψ g ⟨r, hrN⟩) ^ 2 ^ k = 1 := by
      rw [← psi_pow hrN]
      have h1 : (⟨r ^ 2 ^ k, pow_mem hrN _⟩ : normalizer (rightConjugate A g : Set G)) = 1 :=
        Subtype.ext hk
      rw [h1, map_one]
    have hc : conjAct ψ g ⟨r, hrN⟩ * (ε * conjAut 3 F (torusGL b) * ε⁻¹) =
        ε * conjAut 3 F (torusGL b) * ε⁻¹ * conjAct ψ g ⟨r, hrN⟩ := by
      rw [← hα, ← psi_mul hrN hwN, ← psi_mul hwN hrN]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.1 (hR.le hr) w hwA).symm
    have hL : ∀ s ∈ leviA ε, conjAct ψ g ⟨r, hrN⟩ * s = s * conjAct ψ g ⟨r, hrN⟩ := by
      intro s hs
      obtain ⟨x, hx, hxs⟩ := exists_mem_leviLift hψg (leviA_le_innerP ε) (commutator_leviA ε) hs
      rw [← hxs, ← psi_mul hrN (le_normalizer (leviLift_le hx)),
        ← psi_mul (le_normalizer (leviLift_le hx)) hrN]
      congr 1
      exact Subtype.ext (hRL r hr x hx)
    have h1 := eq_one_of_commute_leviA hb hψk hc hL
    rw [← centralizer_rightConjugate_eq]
    exact (hψg.eq_one_iff _).1 h1
  have hg' : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rwa [AS76b.normalizer_centralizer_eq hA]
  have hodd2 := (AS76b.tightlyEmbedded_centralizer hA).2 g hg'
  exact hR1 (two_subgroup_of_odd_eq_bot R _ hR.isPGroup hodd2 (le_inf hR.le hRK))

theorem not_le_normalizer [Group.IsPerfect (SL2 F)] (hA : standardComponentIsStandard A)
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {m : ℕ} (hm : 3 ≤ m) (hF : Nat.card F = 2 ^ m)
    (hKey : ∀ c : G, Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) c :
      Subgroup G)))
    {g : G} (hg : g ∉ normalizer (A : Set G)) {T R : Subgroup G}
    (hTK : T ≤ rightConjugate (centralizer (A : Set G)) g) (hTN : T ≤ normalizer (A : Set G))
    (hTAK : T ≤ A ⊔ centralizer (A : Set G)) (hTe : IsElemAbelian 2 T)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hR1 : R ≠ ⊥)
    (hRN : R ≤ normalizer (rightConjugate A g : Set G)) {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1)
    {γ : MulAut (projectiveSL 3 F)} {l : Fˣ} {w : G} (hwA : w ∈ A) (hl : (l : F) ^ 3 ≠ 1)
    (hγ : ψ ⟨t₀, hTN ht₀⟩ = γ * MulAut.conj (x0 F) * γ⁻¹)
    (hwψ : ψ ⟨w, le_normalizer hwA⟩ = γ * MulAut.conj (projTorus F l) * γ⁻¹)
    (hwodd : Odd (orderOf w)) (hwt₀ : w * t₀ = t₀ * w) :
    ¬ centralizer (zpowers w : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  have ht₀2 : t₀ * t₀ = 1 := by rw [← sq]; exact hTe.2 t₀ ht₀
  have htight := AS76b.tightlyEmbedded_rightConjugate (AS76b.tightlyEmbedded_centralizer hA) g
  have hwN : w ∈ normalizer (rightConjugate A g : Set G) := by
    rw [← normalizer_rightConjugate_centralizer hA g]
    exact mem_normalizer_of_commute_of_mem htight (hTK ht₀) ht₀1 ht₀2 hwt₀
  obtain ⟨ε, b, hb, hα⟩ := exists_conjAct_eq_torus hA hψ hZ hm hF (hKey g) (hTK ht₀) (hTN ht₀)
    ht₀2 ht₀1 (commute_of_mem_sup (hTAK ht₀)) hγ hl hwA hwψ hwodd hwN
  exact not_le_normalizer_of_torus hA hψ hg (hKey g⁻¹) hTK hR hR1 hRN hwA hwN hb hα

end CFSG.ComponentClassification.RankTwoL3Even
