module

public import CFSG.LieType.Ree.SmallReeCenterTrivial
public import CFSG.LieType.Ree.SmallReeCoordinateProduct

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace ReeTag

theorem G2_eq_one_or_eq_longest
    {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
    {w : WeylGroup G2.tag} (hw : w ∈ G2.relWeylRee) : w = 1 ∨ w = w₀ := by
  have hcard : Nat.card G2.relWeylRee = 2 := ree_fixed_Weyl_structure.2.2.1
  have h0 : w₀ ∈ G2.relWeylRee := longest_mem_relWeylRee hw₀
  have h10 : (1 : WeylGroup G2.tag) ≠ w₀ := by
    intro h
    have := hw₀ ((coxeterSystem G2.tag).simple ⟨0, by decide⟩)
    rw [← h, CoxeterSystem.length_one, CoxeterSystem.length_simple] at this
    omega
  by_contra hne
  push Not at hne
  have h3 : ({1, w₀, w} : Set (WeylGroup G2.tag)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, w₀, w, h10, Ne.symm hne.1, Ne.symm hne.2, rfl⟩
  have hsub : ({1, w₀, w} : Set (WeylGroup G2.tag)) ⊆
      (G2.relWeylRee : Set (WeylGroup G2.tag)) := by
    rintro x (rfl | rfl | rfl)
    · exact one_mem _
    · exact h0
    · exact hw
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq] at hle
  change 3 ≤ Nat.card G2.relWeylRee at hle
  omega

theorem subgroupOf_inf_eq {G : Type*} [Group G] (A B C : Subgroup G) :
    (A ⊓ B).subgroupOf C = A.subgroupOf C ⊓ B.subgroupOf C := by
  ext x
  simp [Subgroup.mem_subgroupOf]

section Coset

variable
    {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ} {w₀ : WeylGroup G2.tag}

theorem eq_one_of_mem_reeFixedPosUnipotent_of_mem_reeFixedTorus
    {u : ModGL G2.tag K}
    (hu : u ∈ G2.reeFixedPosUnipotent K a) (hh : u ∈ G2.reeFixedTorus K a) : u = 1 :=
  ((ree_fixed_Bruhat_decomposition G2 a K).2.2.1 u hh 1 (one_mem _) 1 (one_mem _) u hu
    (by rw [mul_one, one_mul])).1

omit [Finite K] [CharP K G2.prime] in
theorem smallReeCoord_one_zero_zero_ne_one
    : (smallReeCoord a K 1 0 0 : ModGL G2.tag K) ≠ 1 := by
  intro h
  rw [← smallReeCoord_zero (a := a)] at h
  rw [smallReeCoord_eq_smallReeP, smallReeCoord_eq_smallReeP] at h
  exact one_ne_zero (smallReeP_injective h).1

variable (hK : Nat.card K = 3 ^ (2 * a + 1))
variable
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)

include hw₀ in
theorem canonicalRep_longest_mem_reeGamma :
    canonicalRep (coxeterSystem G2.tag) K w₀ ∈ G2.reeGamma K a :=
  (Subgroup.mem_inf.1 (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀)).2

include hK hw₀ in
theorem canonicalRep_longest_not_mem_reeFixedBorel :
    canonicalRep (coxeterSystem G2.tag) K w₀ ∉ G2.reeFixedBorel K a := by
  intro hnB
  have hinf := reeFixedBorel_inf_map_conj (K := K) (a := a) hw₀
  rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hnB), inf_idem] at hinf
  have hu : (smallReeCoord a K 1 0 0 : ModGL G2.tag K) ∈ G2.reeFixedPosUnipotent K a := by
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 ((bijOn_smallReeCoord (a := a) hK).1
      (Set.mem_univ ((1 : K), (0 : K), (0 : K))))
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  have huH : (smallReeCoord a K 1 0 0 : ModGL G2.tag K) ∈ G2.reeFixedTorus K a := by
    rw [← hinf]
    exact reeFixedPosUnipotent_le_reeFixedBorel hu
  exact smallReeCoord_one_zero_zero_ne_one
    (eq_one_of_mem_reeFixedPosUnipotent_of_mem_reeFixedTorus hu huH)

include hw₀ in
theorem eq_of_mul_canonicalRep_inv_mul_mem
    {u u' : ModGL G2.tag K}
    (hu : u ∈ G2.reeFixedPosUnipotent K a) (hu' : u' ∈ G2.reeFixedPosUnipotent K a)
    (h : (u * canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ *
      (u' * canonicalRep (coxeterSystem G2.tag) K w₀) ∈ G2.reeFixedBorel K a) : u = u' := by
  set n := canonicalRep (coxeterSystem G2.tag) K w₀
  have hv : u⁻¹ * u' ∈ G2.reeFixedPosUnipotent K a := mul_mem (inv_mem hu) hu'
  have hconj : u⁻¹ * u' ∈ (G2.reeFixedBorel K a).map (MulAut.conj n).toMonoidHom := by
    refine ⟨n⁻¹ * (u⁻¹ * u') * n, ?_, ?_⟩
    · have e : (u * n)⁻¹ * (u' * n) = n⁻¹ * (u⁻¹ * u') * n := by group
      rwa [← e]
    · simp [MulAut.conj_apply, mul_assoc]
  have hH : u⁻¹ * u' ∈ G2.reeFixedTorus K a := by
    rw [← reeFixedBorel_inf_map_conj (K := K) (a := a) hw₀]
    exact Subgroup.mem_inf.2 ⟨reeFixedPosUnipotent_le_reeFixedBorel hv, hconj⟩
  have h1 := eq_one_of_mem_reeFixedPosUnipotent_of_mem_reeFixedTorus hv hH
  exact (inv_mul_eq_one.1 h1)

include hw₀ in
theorem exists_reeFixedPosUnipotent_mul_canonicalRep
    {g : ModGL G2.tag K}
    (hg : g ∈ G2.reeGamma K a) (hgB : g ∉ G2.reeFixedBorel K a) :
    ∃ u ∈ G2.reeFixedPosUnipotent K a,
      (u * canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ * g ∈ G2.reeFixedBorel K a := by
  set n := canonicalRep (coxeterSystem G2.tag) K w₀
  obtain ⟨hBHU, -, -, -, -, -, -, -, hcells, -⟩ := ree_fixed_Bruhat_decomposition G2 a K
  obtain ⟨-, -, hHN, -⟩ := ree_fixed_monomial_quotient G2 a K
  have hg' : g ∈ (G2.reeGamma K a : Set (ModGL G2.tag K)) := hg
  rw [hcells, Set.mem_iUnion] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := hg'
  change g ∈ G2.reeFixedBruhatCell K a w at hgw
  rcases G2_eq_one_or_eq_longest hw₀ hw with h | h
  · exfalso
    rw [h] at hgw
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hgw
    rw [canonicalRep_one, mul_one] at hgB
    exact hgB (mul_mem hb hb')
  rw [h] at hgw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hgw
  have hb2 : b ∈ (G2.reeFixedPosUnipotent K a : Set (ModGL G2.tag K)) *
      (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) := by
    rw [← (ree_fixed_Bruhat_decomposition G2 a K).2.1]
    exact hb
  obtain ⟨u, hu, h, hh, rfl⟩ := hb2
  have hnN : n ∈ G2.reeFixedMonomial K a := canonicalRep_longest_mem_reeFixedMonomial hw₀
  have hhN : h ∈ G2.reeFixedMonomial K a := reeFixedTorus_le_reeFixedMonomial G2 K a hh
  have hconj : n⁻¹ * h * n ∈ G2.reeFixedTorus K a := by
    have h1 := hHN.conj_mem ⟨h, hhN⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨n⁻¹, inv_mem hnN⟩
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  refine ⟨u, hu, ?_⟩
  have e : (u * n)⁻¹ * (u * h * n * b') = (n⁻¹ * h * n) * b' := by group
  rw [e]
  exact mul_mem (reeFixedTorus_le_reeFixedBorel hconj) hb'

end Coset

end ReeTag

theorem small_Ree_Borel_coset_Sylow_action
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (w₀ : WeylGroup ReeTag.G2.tag)
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) :
    ∃ hn : canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∈ ReeTag.G2.reeGamma K a,
      (QuotientGroup.mk (⟨_, hn⟩ : ReeTag.G2.reeGamma K a) : ReeTag.G2.reeGamma K a ⧸
          (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) ≠
        QuotientGroup.mk 1 ∧
      FaithfulSMul (ReeTag.G2.reeGamma K a) (ReeTag.G2.reeGamma K a ⧸
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) ∧
      MulAction.IsPretransitive (ReeTag.G2.reeGamma K a) (ReeTag.G2.reeGamma K a ⧸
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) ∧
      Set.BijOn (fun u : (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
          (ReeTag.G2.reeGamma K a) =>
          (u : ReeTag.G2.reeGamma K a) • (QuotientGroup.mk (⟨_, hn⟩ : ReeTag.G2.reeGamma K a) :
            ReeTag.G2.reeGamma K a ⧸
              (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)))
        Set.univ {ω | ω ≠ QuotientGroup.mk 1} ∧
      (∀ u v : (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a),
        ((v * u : (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)) :
            ReeTag.G2.reeGamma K a) •
          (QuotientGroup.mk (⟨_, hn⟩ : ReeTag.G2.reeGamma K a) : ReeTag.G2.reeGamma K a ⧸
            (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) =
        (v : ReeTag.G2.reeGamma K a) • ((u : ReeTag.G2.reeGamma K a) •
          (QuotientGroup.mk (⟨_, hn⟩ : ReeTag.G2.reeGamma K a) : ReeTag.G2.reeGamma K a ⧸
            (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)))) ∧
      (∀ ω ω' : ReeTag.G2.reeGamma K a ⧸
          (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a),
        ω ≠ QuotientGroup.mk 1 → ω' ≠ QuotientGroup.mk 1 →
          ∃! u : (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a),
            (u : ReeTag.G2.reeGamma K a) • ω = ω') ∧
      Nat.card (ReeTag.G2.reeGamma K a ⧸
          (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) =
        (3 ^ (2 * a + 1)) ^ 3 + 1 ∧
      Nat.card (ReeTag.G2.reeFixedBorel K a) = (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) ∧
      Nat.card (ReeTag.G2.reeGamma K a) =
        (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) * ((3 ^ (2 * a + 1)) ^ 3 + 1) ∧
      (∃ P : Sylow 3 (ReeTag.G2.reeGamma K a), (P : Subgroup (ReeTag.G2.reeGamma K a)) =
        (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)) ∧
      MulAction.stabilizer (ReeTag.G2.reeGamma K a)
          (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K a ⧸
            (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) =
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) ∧
      (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).subgroupOf
        ((ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a))).Normal ∧
      Subgroup.normalizer (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
          (ReeTag.G2.reeGamma K a) : Subgroup (ReeTag.G2.reeGamma K a)) :
            Set (ReeTag.G2.reeGamma K a)) =
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) ∧
      Subgroup.normalizer (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
          (ReeTag.G2.reeGamma K a) : Subgroup (ReeTag.G2.reeGamma K a)) :
            Set (ReeTag.G2.reeGamma K a)) ⊓
        Subgroup.normalizer ((((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
          (ReeTag.G2.reeGamma K a)).map (MulAut.conj (⟨_, hn⟩ :
            ReeTag.G2.reeGamma K a)).toMonoidHom : Subgroup (ReeTag.G2.reeGamma K a)) :
              Set (ReeTag.G2.reeGamma K a)) =
        (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  set B' := (ReeTag.G2.reeFixedBorel K a).subgroupOf Γ with hB'
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf Γ with hU'
  have hn := ReeTag.canonicalRep_longest_mem_reeGamma (K := K) (a := a) hw₀
  set n' : Γ := ⟨_, hn⟩ with hn'
  have hUΓ : ReeTag.G2.reeFixedPosUnipotent K a ≤ Γ := ReeTag.reeFixedPosUnipotent_le_reeGamma
  have hBΓ : ReeTag.G2.reeFixedBorel K a ≤ Γ := ReeTag.reeFixedBorel_le_reeGamma
  have hcoset : ∀ g g' : Γ, (QuotientGroup.mk g : Γ ⧸ B') = QuotientGroup.mk g' ↔
      ((g⁻¹ * g' : Γ) : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a := fun g g' => by
    rw [QuotientGroup.eq, hB', Subgroup.mem_subgroupOf]
  have hsmul : ∀ (u : U') (g : Γ), (u : Γ) • (QuotientGroup.mk g : Γ ⧸ B') =
      QuotientGroup.mk ((u : Γ) * g) := fun u g => by
    rw [MulAction.Quotient.smul_mk]
    rfl
  have hmaps : ∀ u : U', (u : Γ) • (QuotientGroup.mk n' : Γ ⧸ B') ≠ QuotientGroup.mk 1 := by
    intro u h
    rw [hsmul, hcoset] at h
    have hu : ((u : Γ) : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a := u.2
    apply ReeTag.canonicalRep_longest_not_mem_reeFixedBorel hK hw₀
    have h1 : (((u : Γ) * n')⁻¹ : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a := by
      simpa using h
    have h3 : (((u : Γ) : ModGL ReeTag.G2.tag K) * (n' : ModGL ReeTag.G2.tag K)) ∈
        ReeTag.G2.reeFixedBorel K a := by
      simpa using inv_mem h1
    have h2 := mul_mem (inv_mem (ReeTag.reeFixedPosUnipotent_le_reeFixedBorel hu)) h3
    simpa using h2
  have hinj : ∀ u u' : U', (u : Γ) • (QuotientGroup.mk n' : Γ ⧸ B') =
      (u' : Γ) • (QuotientGroup.mk n' : Γ ⧸ B') → u = u' := by
    intro u u' h
    rw [hsmul, hsmul, hcoset] at h
    have := ReeTag.eq_of_mul_canonicalRep_inv_mul_mem hw₀ u.2 u'.2 (by simpa using h)
    exact Subtype.ext (Subtype.ext this)
  have hsurj : ∀ ω : Γ ⧸ B', ω ≠ QuotientGroup.mk 1 →
      ∃ u : U', (u : Γ) • (QuotientGroup.mk n' : Γ ⧸ B') = ω := by
    intro ω hω
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    have hgB : (g : ModGL ReeTag.G2.tag K) ∉ ReeTag.G2.reeFixedBorel K a := by
      intro hgB
      apply hω
      rw [hcoset]
      simpa using hgB
    obtain ⟨u, hu, hub⟩ := ReeTag.exists_reeFixedPosUnipotent_mul_canonicalRep hw₀ g.2 hgB
    refine ⟨⟨⟨u, hUΓ hu⟩, hu⟩, ?_⟩
    rw [hsmul, hcoset]
    simpa using hub
  have hbij : Set.BijOn (fun u : U' => (u : Γ) • (QuotientGroup.mk n' : Γ ⧸ B')) Set.univ
      {ω | ω ≠ QuotientGroup.mk 1} :=
    ⟨fun u _ => hmaps u, fun u _ u' _ h => hinj u u' h, fun ω hω => by
      obtain ⟨u, hu⟩ := hsurj ω hω
      exact ⟨u, Set.mem_univ _, hu⟩⟩
  obtain ⟨-, hcardU⟩ := small_Ree_positive_fixed_coordinates a K hK
  have hcardU' : Nat.card U' = (3 ^ (2 * a + 1)) ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUΓ).toEquiv, hcardU]
  have hcardΩ : Nat.card (Γ ⧸ B') = (3 ^ (2 * a + 1)) ^ 3 + 1 := by
    have h1 : Nat.card ({ω | ω ≠ QuotientGroup.mk 1} : Set (Γ ⧸ B')) = Nat.card U' := by
      rw [← Nat.card_univ (α := U')]
      exact (Nat.card_congr (hbij.equiv _)).symm
    have h2 : ({ω | ω ≠ QuotientGroup.mk 1} : Set (Γ ⧸ B')) =
        Set.univ \ {QuotientGroup.mk 1} := by
      ext ω
      simp
    rw [h2, Nat.card_coe_set_eq, hcardU'] at h1
    rw [← Set.ncard_univ, ← Set.ncard_sdiff_singleton_add_one (Set.mem_univ _) (Set.toFinite _),
      h1]
  obtain ⟨φ, -⟩ := (small_Ree_positive_torus_action a K hK).1
  have hcardH : Nat.card (ReeTag.G2.reeFixedTorus K a) = 3 ^ (2 * a + 1) - 1 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_units, hK]
  have hcardB : Nat.card (ReeTag.G2.reeFixedBorel K a) =
      (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) := by
    obtain ⟨hBHU, -, huniq, -⟩ := ReeTag.ree_fixed_Bruhat_decomposition ReeTag.G2 a K
    have hb : Function.Bijective fun p : ReeTag.G2.reeFixedTorus K a ×
        ReeTag.G2.reeFixedPosUnipotent K a =>
        (⟨(p.1 : ModGL ReeTag.G2.tag K) * p.2, by
          have h : (p.1 : ModGL ReeTag.G2.tag K) * p.2 ∈
              (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)) *
                (ReeTag.G2.reeFixedPosUnipotent K a : Set (ModGL ReeTag.G2.tag K)) :=
            Set.mul_mem_mul p.1.2 p.2.2
          rw [← hBHU] at h
          exact h⟩ : ReeTag.G2.reeFixedBorel K a) := by
      refine ⟨fun p p' h => ?_, fun b => ?_⟩
      · have h' := congrArg Subtype.val h
        obtain ⟨e1, e2⟩ := huniq _ p.1.2 _ p'.1.2 _ p.2.2 _ p'.2.2 h'
        exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
      · have hb : (b : ModGL ReeTag.G2.tag K) ∈
            (ReeTag.G2.reeFixedTorus K a : Set (ModGL ReeTag.G2.tag K)) *
              (ReeTag.G2.reeFixedPosUnipotent K a : Set (ModGL ReeTag.G2.tag K)) := by
          rw [← hBHU]
          exact b.2
        obtain ⟨h, hh, u, hu, he⟩ := hb
        exact ⟨(⟨h, hh⟩, ⟨u, hu⟩), Subtype.ext he⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_prod, hcardH, hcardU, mul_comm]
  have hcardB' : Nat.card B' = (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBΓ).toEquiv, hcardB]
  have hcardΓ : Nat.card Γ =
      (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) * ((3 ^ (2 * a + 1)) ^ 3 + 1) := by
    rw [← B'.card_mul_index, hcardB', Subgroup.index, hcardΩ]
  obtain ⟨-, -, -, hBinf, -, hNU, -⟩ := ReeTag.ree_Borel_self_normalizers ReeTag.G2 a K w₀ hw₀
  have hNU' : Subgroup.normalizer (U' : Set Γ) = B' := by
    rw [hU', ← Subgroup.subgroupOf_normalizer_eq hUΓ, ← Subgroup.inf_subgroupOf_left, hNU]
  refine ⟨hn, fun h => hmaps 1 (by rw [OneMemClass.coe_one, one_smul]; exact h),
    (small_Ree_fixed_group_center_trivial a K hK).2.2, inferInstance, hbij,
    fun u v => by rw [Subgroup.coe_mul, mul_smul],
    fun ω ω' hω hω' => ?_, hcardΩ, hcardB, hcardΓ,
    (ReeTag.large_Ree_Sylow_opposition ReeTag.G2 a K w₀ hw₀).1,
    MulAction.stabilizer_quotient B', ?_, hNU', ?_⟩
  ·
    obtain ⟨u₁, rfl⟩ := hsurj ω hω
    obtain ⟨u₂, rfl⟩ := hsurj ω' hω'
    refine ⟨u₂ * u₁⁻¹, ?_, fun v hv => ?_⟩
    · dsimp only
      rw [← mul_smul, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    · dsimp only at hv
      rw [← mul_smul, ← Subgroup.coe_mul] at hv
      rw [← hinj _ _ hv, mul_inv_cancel_right]
  ·
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hU', Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (((g : B') : Γ) : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a := g.2
    have hN := ReeTag.reeFixedBorel_le_normalizer_reeFixedPosUnipotent hg
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.1 hN _).1 hx
  ·
    have hNV : Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) :
        Set Γ) = B'.map (MulAut.conj n').toMonoidHom := by
      rw [← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj n').bijective, hNU']
    rw [hNV, hNU', hB', map_conj_subgroupOf hBΓ, ← ReeTag.subgroupOf_inf_eq, hBinf]

end CFSG.LieType.Ree
