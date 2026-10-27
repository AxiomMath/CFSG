module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.SL3TorFinal
public import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM9Split

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor
open Multiplicative

variable {F : Type} [Field F]

theorem entry_of_mem_statedScalars {g : GL (Fin 3) F} (hg : g ∈ StatedScalars (Fin 3) F)
    (i j : Fin 3) :
    (g : Matrix (Fin 3) (Fin 3) F) i j = if i = j then (g : Matrix (Fin 3) (Fin 3) F) 0 0 else 0 := by
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hg
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, h]

theorem not_mem_statedScalars_of_diag {g : GL (Fin 3) F} {i j : Fin 3}
    (h : (g : Matrix (Fin 3) (Fin 3) F) i i ≠ (g : Matrix (Fin 3) (Fin 3) F) j j) :
    g ∉ StatedScalars (Fin 3) F := by
  intro hg
  apply h
  rw [entry_of_mem_statedScalars hg i i, entry_of_mem_statedScalars hg j j, if_pos rfl, if_pos rfl]

theorem not_mem_statedScalars_of_utri [Finite F] {g : GL (Fin 3) F} (hg : g ∈ utriG (K := F)) (hne : g ≠ 1) :
    g ∉ StatedScalars (Fin 3) F := by
  intro hs
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hs
  apply hne
  have h00 : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := ((mem_utriG _).1 hg 0 0).2 rfl
  rw [Matrix.GeneralLinearGroup.coe_scalar] at h00
  simp [Matrix.scalar_apply] at h00
  have hc : c = 1 := h00
  rw [hc, map_one]

theorem E0gen_entry_00 (ω : Fˣ) (hω3 : ω ^ 3 = 1) :
    ((E0hom (K := F) ω hω3 (ofAdd ((1 : ZMod 3), (0 : ZMod 3))) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 0 = (ω : F) := by
  simp [E0hom_apply, diagUnit_val, zetaU, show ZMod.val (1 : ZMod 3) = 1 from rfl]

theorem E0gen_entry_22 (ω : Fˣ) (hω3 : ω ^ 3 = 1) :
    ((E0hom (K := F) ω hω3 (ofAdd ((1 : ZMod 3), (0 : ZMod 3))) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  simp [E0hom_apply, diagUnit_val, zetaU, show ZMod.val (-(0 : ZMod 3)) = 0 from rfl]

theorem isPerfect_quot_of_iso {K : Type} [Group K]
    (ψ : (K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL 3 F)) :
    Group.IsPerfect (K ⧸ Subgroup.center K) := by
  haveI : Group.IsPerfect (StatedSL 3 F) := isPerfect_statedSL_of_three_le (by norm_num) F
  haveI : Group.IsPerfect (StatedProj (StatedSL 3 F)) :=
    Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)))
      (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective

theorem card_center_congr {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem map_commutator_eq_top {K : Type} [Group K]
    (hperf : Group.IsPerfect (K ⧸ Subgroup.center K)) :
    (commutator K).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
  have h1 : commutator (K ⧸ Subgroup.center K) = ⊤ := Group.IsPerfect.commutator_eq_top
  have hqtop : (⊤ : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [commutator_def, Subgroup.map_commutator, hqtop, ← commutator_def, h1]

theorem commutator_eq_top_of_center_le {K : Type} [Group K]
    (hperf : Group.IsPerfect (K ⧸ Subgroup.center K)) (h : Subgroup.center K ≤ commutator K) :
    commutator K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : QuotientGroup.mk' (Subgroup.center K) x ∈
      (commutator K).map (QuotientGroup.mk' (Subgroup.center K)) := by
    rw [map_commutator_eq_top hperf]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hx
  have hz : k⁻¹ * x ∈ Subgroup.center K := QuotientGroup.eq.1 hkx
  simpa using Subgroup.mul_mem _ hk (h hz)

theorem split_torus {K : Type} [Group K] [Finite K] [Finite F] [CharP F 2]
    {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (ψ : (K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL 3 F))
    (hZ : Nat.card (Subgroup.center K) = 3) (hZK : ¬ Subgroup.center K ≤ commutator K) :
    ∃ y : K, (∃ z : K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
      ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ y ∈ Subgroup.normalizer (U : Set K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect (K ⧸ Subgroup.center K) := isPerfect_quot_of_iso ψ
  have hmap : (commutator K).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ :=
    map_commutator_eq_top hperf
  have hsurj' : ∀ g : K ⧸ Subgroup.center K, ∃ x ∈ commutator K,
      QuotientGroup.mk' (Subgroup.center K) x = g := by
    intro g
    have hg : g ∈ (commutator K).map (QuotientGroup.mk' (Subgroup.center K)) := by
      rw [hmap]
      exact Subgroup.mem_top g
    exact Subgroup.mem_map.1 hg
  have hinter : commutator K ⊓ Subgroup.center K = ⊥ := by
    have hdvd : Nat.card ↥(commutator K ⊓ Subgroup.center K) ∣ 3 := by
      rw [← hZ]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : commutator K ⊓ Subgroup.center K = Subgroup.center K :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [h3, hZ]))
      apply hZK
      rw [← heq]
      exact inf_le_left
  obtain ⟨j, hj⟩ : ∃ j : commutator K ≃* (K ⧸ Subgroup.center K),
      ∀ x : commutator K, j x = QuotientGroup.mk' (Subgroup.center K) (x : K) := by
    refine ⟨MulEquiv.ofBijective ((QuotientGroup.mk' (Subgroup.center K)).comp
      (commutator K).subtype) ⟨?_, ?_⟩, fun x => rfl⟩
    · rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : K) ∈ Subgroup.center K := (QuotientGroup.eq_one_iff (x : K)).1 hx
      have hmem : (x : K) ∈ commutator K ⊓ Subgroup.center K := ⟨x.2, hx'⟩
      rw [hinter, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro g
      obtain ⟨x, hx, hxg⟩ := hsurj' g
      exact ⟨⟨x, hx⟩, hxg⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : StatedProj (StatedSL 3 F) ≃* commutator K,
      ∀ p, j (σ p) = ψ.symm p :=
    ⟨ψ.symm.trans j.symm, fun p => by simp⟩
  obtain ⟨χ, hχq⟩ : ∃ χ : ↥(StatedSL 3 F) →* K,
      ∀ g : ↥(StatedSL 3 F), QuotientGroup.mk' (Subgroup.center K) (χ g) =
        ψ.symm (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) g) :=
    ⟨(commutator K).subtype.comp (σ.toMonoidHom.comp
      (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)))),
      fun g => (hj (σ _)).symm.trans (hσ _)⟩
  obtain ⟨d0, hd0⟩ : ∃ d0 : GL (Fin 3) F,
      d0 = E0hom (K := F) ω hω3 (ofAdd ((1 : ZMod 3), (0 : ZMod 3))) := ⟨_, rfl⟩
  have hd0E : d0 ∈ E0G (K := F) ω hω3 := by
    rw [hd0]
    exact ⟨_, rfl⟩
  obtain ⟨dS, hdSval⟩ : ∃ dS : ↥(StatedSL 3 F), (dS : GL (Fin 3) F) = d0 :=
    ⟨⟨d0, E0G_le_statedSL hω3 hd0E⟩, rfl⟩
  have hdS3 : dS ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hdSval, E0G_pow_three hω3 d0 hd0E]
    rfl
  have hd0_notin : d0 ∉ StatedScalars (Fin 3) F := by
    apply not_mem_statedScalars_of_diag (i := 0) (j := 2)
    rw [hd0, E0gen_entry_00 ω hω3, E0gen_entry_22 ω hω3]
    intro h
    exact hω1 (Units.ext h)
  have hmkne : QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) dS ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hdSval] at h
    exact hd0_notin h
  have hyne : ψ.symm (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) dS)
      ≠ 1 := fun h => hmkne ((map_eq_one_iff _ ψ.symm.injective).1 h)
  have hy1 : χ dS ≠ 1 := by
    intro h
    apply hyne
    rw [← hχq dS, h, map_one]
  have hy3 : χ dS ^ 3 = 1 := by
    rw [← map_pow, hdS3, map_one]
  have hle : utriG (K := F) ≤ StatedSL 3 F := fun g hg => mem_statedSL_of_det (isUTri_det hg)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ↥(utriG (K := F)) →* K, ∀ x, Φ x = χ ⟨x, hle x.2⟩ :=
    ⟨χ.comp (Subgroup.inclusion hle), fun x => rfl⟩
  have hconj : ∀ g : ↥(StatedSL 3 F), (g : GL (Fin 3) F) ∈ E0G (K := F) ω hω3 →
      ∀ w ∈ Φ.range, χ g * w * (χ g)⁻¹ ∈ Φ.range := by
    rintro g hg _ ⟨x, rfl⟩
    have hx : (g : GL (Fin 3) F) * (x : GL (Fin 3) F) * (g : GL (Fin 3) F)⁻¹ ∈ utriG (K := F) :=
      (Subgroup.mem_set_normalizer_iff.1 (E0G_le_normalizer_utriG hω3 hg) (x : GL (Fin 3) F)).1 x.2
    refine ⟨⟨_, hx⟩, ?_⟩
    rw [hΦ, hΦ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  obtain ⟨u1, hu1mem, hu1ne1, -⟩ := involution_mem_utriG (K := F)
  have hu1ne : Φ ⟨u1, hu1mem⟩ ≠ 1 := by
    intro h
    rw [hΦ] at h
    have h2 := congrArg (QuotientGroup.mk' (Subgroup.center K)) h
    rw [hχq, map_one, map_eq_one_iff _ ψ.symm.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact not_mem_statedScalars_of_utri hu1mem hu1ne1 h2
  have hnc : ∃ z : K, z * χ dS ≠ χ dS * z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hyne
    rw [← hχq dS]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_center_iff.2 fun g => hcon g)
  have hUne : Φ.range ≠ ⊥ := by
    intro hbot
    apply hu1ne
    have hmem : Φ ⟨u1, hu1mem⟩ ∈ Φ.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hPG : IsPGroup 2 Φ.range :=
    (utriG_isPGroup (K := F)).of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hnorm : χ dS ∈ Subgroup.normalizer ((Φ.range : Subgroup K) : Set K) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj dS (by rw [hdSval]; exact hd0E) h hh
    · intro hh
      have hinv : ((dS⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) ∈ E0G (K := F) ω hω3 := by
        rw [Subgroup.coe_inv, hdSval]
        exact Subgroup.inv_mem _ hd0E
      have h2 := hconj (dS⁻¹) hinv _ hh
      rw [map_inv] at h2
      have key : (χ dS)⁻¹ * (χ dS * h * (χ dS)⁻¹) * (χ dS)⁻¹⁻¹ = h := by group
      rw [key] at h2
      exact h2
  exact ⟨χ dS, hnc, orderOf_eq_prime hy3 hy1, Φ.range, hUne, hPG, hnorm⟩

end CFSG.LocalAnalysis.GLTheoremA.SFM9Split
