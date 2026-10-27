module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.CoreSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeComponentCyclic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.QuasithinUnique

theorem exists_isPerfect_derivedSeries (N : Type*) [Group N] [Finite N] :
    ∃ n, Group.IsPerfect ↥(derivedSeries N n) := by
  classical
  have hanti : ∀ n, derivedSeries N (n + 1) ≤ derivedSeries N n := fun n => by
    rw [derivedSeries_succ]
    exact Subgroup.commutator_le_self _
  by_contra h
  push Not at h
  have hlt : ∀ n, Nat.card (derivedSeries N (n + 1)) < Nat.card (derivedSeries N n) := by
    intro n
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne (hanti n) fun heq => h n ?_)
    rw [Subgroup.isPerfect_iff, ← derivedSeries_succ, heq]
  have hle : ∀ n, Nat.card (derivedSeries N n) + n ≤ Nat.card N := by
    intro n
    induction n with
    | zero => simp [derivedSeries_zero]
    | succ n ih =>
      have := hlt n
      omega
  have h1 := hle (Nat.card N + 1)
  have h2 : 0 < Nat.card (derivedSeries N (Nat.card N + 1)) := Nat.card_pos
  omega

theorem isSolvable_quotient_derivedSeries (N : Type*) [Group N] (n : ℕ) :
    Group.IsSolvable (N ⧸ derivedSeries N n) := by
  refine ⟨⟨n, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (derivedSeries N n)) n,
    QuotientGroup.map_mk'_self]

theorem not_isPSolvable_derivedSeries {p : ℕ} [Fact p.Prime] {N : Type} [Group N] [Finite N]
    (hN : ¬ CFSG.HallHigman.IsPSolvable p N) (n : ℕ) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(derivedSeries N n) := fun h =>
  hN (OrdinaryProofs.PSolvableClosure.isPSolvable_of_normal (derivedSeries N n) h
    (isPSolvable_of_isSolvable' Fact.out (isSolvable_quotient_derivedSeries N n)))

theorem isPSolvable_of_isPSolvable_map {B : Type} [Group B] [Finite B] (O : Subgroup B)
    [O.Normal] (hO : ¬ 3 ∣ Nat.card O) (Q : Subgroup B)
    (h : CFSG.HallHigman.IsPSolvable 3 ↥(Q.map (QuotientGroup.mk' O))) :
    CFSG.HallHigman.IsPSolvable 3 ↥Q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : ↥Q →* ↥(Q.map (QuotientGroup.mk' O)) := (QuotientGroup.mk' O).subgroupMap Q with hρ
  have hρs : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ Q
  have hker3 : ¬ 3 ∣ Nat.card ρ.ker := by
    intro h3
    apply hO
    have hle : (ρ.ker).map Q.subtype ≤ O := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      have h1 := congrArg Subtype.val hx
      change QuotientGroup.mk' O (x : B) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective Q.subtype_injective] at this
    exact h3.trans this
  refine OrdinaryProofs.PSolvableClosure.isPSolvable_of_normal ρ.ker
    (MsideParabolicEscape.isPSolvable_three_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3)) ?_
  exact OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm h

theorem isSylowTwoOf_inf_of_normal {G : Type} [Group G] [Finite G] {T X N : Subgroup G}
    (hT : IsSylowTwoOf T X) (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    IsSylowTwoOf (T ⊓ N) N := by
  refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, ?_⟩
  have hTX : T ≤ X := hT.1
  have hNn : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have h1 : T.relIndex (N ⊔ T) = T.relIndex N := relIndex_sup_of_normal (J := X) hTX hNX
  have h2 : T.relIndex (N ⊔ T) ∣ T.relIndex X :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex T (N ⊔ T) X le_sup_right (sup_le hNX hTX))
  have h3 : (T ⊓ N).relIndex N = T.relIndex N := Subgroup.inf_relIndex_right T N
  intro h2N
  apply hT.2.2
  change 2 ∣ T.relIndex X
  change 2 ∣ (T ⊓ N).relIndex N at h2N
  rw [h3, ← h1] at h2N
  exact h2N.trans h2

theorem exists_mem_normalizer_of_isSylowTwoOf {G : Type} [Group G] [Finite G] {X N P : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hP : IsSylowTwoOf P N) {x : G} (hx : x ∈ X) :
    ∃ n ∈ N, n⁻¹ * x ∈ Subgroup.normalizer (P : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : P ≤ N := hP.1
  have hPx : P.map (MulAut.conj x).toMonoidHom ≤ N := by
    rw [← map_conj_eq_of_mem_normalizer' (hXN hx)]
    exact Subgroup.map_mono hPN
  have hcard : Nat.card P = 2 ^ (Nat.card N).factorization 2 := by
    rw [hP.card_eq]
    rfl
  let S₁ : Sylow 2 ↥N := Sylow.ofCard (P.subgroupOf N) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv, hcard])
  let S₂ : Sylow 2 ↥N := Sylow.ofCard ((P.map (MulAut.conj x).toMonoidHom).subgroupOf N) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPx).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj x).injective, hcard])
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq ↥N S₁ S₂
  refine ⟨n, n.2, ?_⟩
  have h : ((n • S₁ : Sylow 2 ↥N) : Subgroup ↥N) = (S₂ : Subgroup ↥N) := by rw [hn]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  change Subgroup.map (MulAut.conj n).toMonoidHom (P.subgroupOf N) =
    (P.map (MulAut.conj x).toMonoidHom).subgroupOf N at h
  have hle : P.map (MulAut.conj (n : G)).toMonoidHom ≤ P.map (MulAut.conj x).toMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem : (MulAut.conj n).toMonoidHom ⟨a, hPN ha⟩ ∈
        (P.map (MulAut.conj x).toMonoidHom).subgroupOf N := h ▸ ⟨⟨a, hPN ha⟩, ha, rfl⟩
    exact hmem
  have heq : P.map (MulAut.conj (n : G)).toMonoidHom = P.map (MulAut.conj x).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
        Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective])
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h1 := congrArg (Subgroup.map (MulAut.conj (n : G)⁻¹).toMonoidHom) heq
  rw [Subgroup.map_map, Subgroup.map_map] at h1
  have h2 : ((MulAut.conj (n : G)⁻¹).toMonoidHom.comp (MulAut.conj (n : G)).toMonoidHom) =
      MonoidHom.id G := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have h3 : ((MulAut.conj (n : G)⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom) =
      (MulAut.conj ((n : G)⁻¹ * x)).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [h2, Subgroup.map_id, h3] at h1
  have := congrArg (fun H : Subgroup G => (H : Set G)) h1
  simpa [Subgroup.coe_map] using this.symm

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
