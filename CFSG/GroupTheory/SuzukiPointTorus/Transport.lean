module

public import CFSG.GroupTheory.SuzukiPointTorus.Basic
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

namespace CFSG.GroupTheory

universe u v

variable {X : Type u} {Y : Type v} [Group X] [Finite X] [Group Y] [Finite Y]

private theorem surjective_toMonoidHom {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Function.Surjective e.toMonoidHom := by
  simpa only [MulEquiv.coe_toMonoidHom] using e.surjective

namespace SuzukiTorusData

private noncomputable def sylowEquiv (e : X ≃* Y) : Sylow 2 X ≃ Sylow 2 Y := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective e.toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom] using e.injective
  refine Equiv.ofBijective
    (Sylow.mapSurjective (f := e.toMonoidHom) (surjective_toMonoidHom e)) ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Sylow.ext
    have h := congrArg (fun R : Sylow 2 Y => (R : Subgroup Y).comap e.toMonoidHom) hPQ
    simpa only [Sylow.coe_mapSurjective,
      Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) hinj] using h
  · intro Q
    refine ⟨Sylow.mapSurjective (f := e.symm.toMonoidHom) (surjective_toMonoidHom e.symm) Q, ?_⟩
    apply Sylow.ext
    rw [Sylow.coe_mapSurjective, Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
      ext y
      simp
    rw [hcomp, Subgroup.map_id]

private theorem sylowEquiv_apply (e : X ≃* Y) (P : Sylow 2 X) :
    sylowEquiv e P =
      Sylow.mapSurjective (f := e.toMonoidHom) (surjective_toMonoidHom e) P := rfl

private theorem sylowEquiv_smul (e : X ≃* Y) (x : X) (P : Sylow 2 X) :
    sylowEquiv e (x • P) = e x • sylowEquiv e P := by
  apply Sylow.ext
  rw [sylowEquiv_apply, Sylow.coe_mapSurjective, Sylow.coe_subgroup_smul,
    Subgroup.pointwise_smul_def]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rw [sylowEquiv_apply, Sylow.coe_mapSurjective]
  change Subgroup.map e.toMonoidHom
      (Subgroup.map (MulAut.conj x).toMonoidHom (P : Subgroup X)) =
    Subgroup.map (MulAut.conj (e x)).toMonoidHom
      (Subgroup.map e.toMonoidHom (P : Subgroup X))
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

private noncomputable def sylowSubgroupEquiv (e : X ≃* Y) (P : Sylow 2 X) :
    P ≃* sylowEquiv e P :=
  (e.subgroupMap (P : Subgroup X)).trans
    (MulEquiv.subgroupCongr (by
      rw [sylowEquiv_apply, Sylow.coe_mapSurjective]
      rfl))
private theorem coe_sylowSubgroupEquiv (e : X ≃* Y) (P : Sylow 2 X) (u : P) :
    ((sylowSubgroupEquiv e P u : sylowEquiv e P) : Y) = e (u : X) := rfl

private theorem map_normalizer_inf (e : X ≃* Y) (U U' : Sylow 2 X) :
    (Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
        Subgroup.normalizer ((U' : Subgroup X) : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((sylowEquiv e U : Subgroup Y) : Set Y) ⊓
        Subgroup.normalizer ((sylowEquiv e U' : Subgroup Y) : Set Y) := by
  rw [Subgroup.map_inf _ _ _ e.injective]
  congr 1
  · simpa only [sylowEquiv_apply, Sylow.coe_mapSurjective] using
      Subgroup.map_equiv_normalizer_eq ((U : Subgroup X)) e
  · simpa only [sylowEquiv_apply, Sylow.coe_mapSurjective] using
      Subgroup.map_equiv_normalizer_eq ((U' : Subgroup X)) e

private theorem faithful_of_mulEquiv (e : X ≃* Y) {q : ℕ} (h : SuzukiTorusData Y q) :
    FaithfulSMul X (Sylow 2 X) := by
  refine faithfulSMul_iff.mpr ?_
  intro x hx
  apply e.injective
  rw [map_one]
  refine (faithfulSMul_iff.mp h.faithful) (e x) ?_
  intro Q
  obtain ⟨P, rfl⟩ := (sylowEquiv e).surjective Q
  rw [← sylowEquiv_smul, hx P]

private theorem card_points_of_mulEquiv (e : X ≃* Y) {q : ℕ}
    (h : SuzukiTorusData Y q) : Nat.card (Sylow 2 X) = q ^ 2 + 1 := by
  rw [Nat.card_congr (sylowEquiv e)]
  exact h.card_points

private theorem fixes_le_two_of_mulEquiv (e : X ≃* Y) {q : ℕ}
    (h : SuzukiTorusData Y q) :
    ∀ x : X, x ≠ 1 → Nat.card {P : Sylow 2 X // x • P = P} ≤ 2 := by
  intro x hx
  have hex : e x ≠ 1 := fun h1 => hx (e.injective (h1.trans (map_one e).symm))
  let f : {P : Sylow 2 X // x • P = P} ≃ {Q : Sylow 2 Y // e x • Q = Q} :=
    (sylowEquiv e).subtypeEquiv (fun P => by
      rw [← sylowEquiv_smul]
      exact (sylowEquiv e).injective.eq_iff.symm)
  exact (Nat.card_congr f).trans_le (h.fixes_le_two (e x) hex)

private theorem card_sylow_of_mulEquiv (e : X ≃* Y) {q : ℕ}
    (h : SuzukiTorusData Y q) : ∀ U : Sylow 2 X, Nat.card U = q ^ 2 := by
  intro U
  calc Nat.card U = Nat.card (sylowEquiv e U) := Nat.card_congr (sylowSubgroupEquiv e U).toEquiv
    _ = q ^ 2 := h.card_sylow (sylowEquiv e U)

private theorem regular_of_mulEquiv (e : X ≃* Y) {q : ℕ} (h : SuzukiTorusData Y q) :
    ∀ U V W : Sylow 2 X, V ≠ U → W ≠ U → ∃! u : U, (u : X) • V = W := by
  intro U V W hV hW
  let U' := sylowEquiv e U
  let V' := sylowEquiv e V
  let W' := sylowEquiv e W
  have hV' : V' ≠ U' := fun hh => hV ((sylowEquiv e).injective (by simpa [U', V'] using hh))
  have hW' : W' ≠ U' := fun hh => hW ((sylowEquiv e).injective (by simpa [U', W'] using hh))
  obtain ⟨u', hu', huniq'⟩ := h.regular U' V' W' hV' hW'
  let eU : U ≃* U' := sylowSubgroupEquiv e U
  refine ⟨eU.symm u', ?_, ?_⟩
  · apply (sylowEquiv e).injective
    rw [sylowEquiv_smul]
    have hcoe : e ((eU.symm u' : U) : X) = (u' : Y) := by
      have h := coe_sylowSubgroupEquiv e U (eU.symm u')
      rw [eU.apply_symm_apply] at h
      exact h.symm
    rw [hcoe, hu']
  · intro u hu
    apply eU.injective
    rw [eU.apply_symm_apply]
    apply huniq'
    have hcoe : ((eU u : U') : Y) = e (u : X) := coe_sylowSubgroupEquiv e U u
    rw [hcoe, ← sylowEquiv_smul, hu]

private theorem inf_normalizer_isCyclic_of_mulEquiv (e : X ≃* Y) {q : ℕ}
    (h : SuzukiTorusData Y q) :
    ∀ U U' : Sylow 2 X, U ≠ U' → IsCyclic
      ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
        Subgroup.normalizer ((U' : Subgroup X) : Set X)) := by
  intro U U' hne
  have hne' : sylowEquiv e U ≠ sylowEquiv e U' := fun hh =>
    hne ((sylowEquiv e).injective hh)
  haveI : IsCyclic ↥(Subgroup.normalizer ((sylowEquiv e U : Subgroup Y) : Set Y) ⊓
      Subgroup.normalizer ((sylowEquiv e U' : Subgroup Y) : Set Y)) :=
    h.inf_normalizer_isCyclic _ _ hne'
  let eN : ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((U' : Subgroup X) : Set X)) ≃*
      ↥(Subgroup.normalizer ((sylowEquiv e U : Subgroup Y) : Set Y) ⊓
        Subgroup.normalizer ((sylowEquiv e U' : Subgroup Y) : Set Y)) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_normalizer_inf e U U'))
  exact isCyclic_of_surjective eN.symm.toMonoidHom eN.symm.surjective

private theorem inf_normalizer_card_of_mulEquiv (e : X ≃* Y) {q : ℕ}
    (h : SuzukiTorusData Y q) :
    ∀ U U' : Sylow 2 X, U ≠ U' → Nat.card
      ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
        Subgroup.normalizer ((U' : Subgroup X) : Set X)) = q - 1 := by
  intro U U' hne
  have hne' : sylowEquiv e U ≠ sylowEquiv e U' := fun hh =>
    hne ((sylowEquiv e).injective hh)
  let eN : ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((U' : Subgroup X) : Set X)) ≃*
      ↥(Subgroup.normalizer ((sylowEquiv e U : Subgroup Y) : Set Y) ⊓
        Subgroup.normalizer ((sylowEquiv e U' : Subgroup Y) : Set Y)) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_normalizer_inf e U U'))
  calc Nat.card ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
        Subgroup.normalizer ((U' : Subgroup X) : Set X))
      = Nat.card ↥(Subgroup.normalizer ((sylowEquiv e U : Subgroup Y) : Set Y) ⊓
        Subgroup.normalizer ((sylowEquiv e U' : Subgroup Y) : Set Y)) :=
        Nat.card_congr eN.toEquiv
    _ = q - 1 := h.inf_normalizer_card _ _ hne'

private theorem inf_normalizer_free_of_mulEquiv (e : X ≃* Y) {q : ℕ}
    (h : SuzukiTorusData Y q) :
    ∀ (U U' : Sylow 2 X), U ≠ U' →
      ∀ hh ∈ Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
          Subgroup.normalizer ((U' : Subgroup X) : Set X),
        hh ≠ 1 → ∀ u : U, hh * (u : X) * hh⁻¹ = (u : X) → u = 1 := by
  intro U U' hne hh hhN hh1 u hu
  have hne' : sylowEquiv e U ≠ sylowEquiv e U' := fun h1 =>
    hne ((sylowEquiv e).injective h1)
  have hhN' : e hh ∈ Subgroup.normalizer ((sylowEquiv e U : Subgroup Y) : Set Y) ⊓
      Subgroup.normalizer ((sylowEquiv e U' : Subgroup Y) : Set Y) := by
    have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hhN
    rwa [map_normalizer_inf e U U'] at hmem
  have hh1' : e hh ≠ 1 := fun h1 => hh1 (e.injective (h1.trans (map_one e).symm))
  have hu' : e (u : X) ∈ (sylowEquiv e U : Subgroup Y) :=
    Subgroup.mem_map_of_mem e.toMonoidHom u.2
  have hfix' : e hh * e (u : X) * (e hh)⁻¹ = e (u : X) := by
    simpa only [map_mul, map_inv] using congrArg e hu
  have hres := h.inf_normalizer_free _ _ hne' (e hh) hhN' hh1'
    (⟨e (u : X), hu'⟩ : (sylowEquiv e U : Subgroup Y)) hfix'
  apply Subtype.ext
  apply e.injective
  simpa using congrArg Subtype.val hres

private theorem card_frattini_of_mulEquiv (e : X ≃* Y) {q : ℕ}
    (h : SuzukiTorusData Y q) :
    ∀ U : Sylow 2 X, Nat.card (↥U ⧸ frattini ↥U) = q := by
  intro U
  let f : U ≃* sylowEquiv e U := sylowSubgroupEquiv e U
  have hfr : (frattini U).map f.toMonoidHom = frattini (sylowEquiv e U) :=
    CFSG.RankThree.PartOne.Torsion37.frattini_map_mulEquiv f
  have hcardU : Nat.card U = Nat.card (sylowEquiv e U) := Nat.card_congr f.toEquiv
  have hcardFr : Nat.card (frattini U) = Nat.card (frattini (sylowEquiv e U)) := by
    rw [← Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective, hfr]
  calc Nat.card (↥U ⧸ frattini ↥U) = (frattini U).index :=
        (Subgroup.index_eq_card (frattini U)).symm
    _ = Nat.card U / Nat.card (frattini U) :=
        Subgroup.index_eq_card_div (H := frattini U)
    _ = Nat.card (sylowEquiv e U) / Nat.card (frattini (sylowEquiv e U)) := by
        rw [hcardU, hcardFr]
    _ = (frattini (sylowEquiv e U)).index :=
        (Subgroup.index_eq_card_div (H := frattini (sylowEquiv e U))).symm
    _ = Nat.card (↥(sylowEquiv e U) ⧸ frattini ↥(sylowEquiv e U)) :=
        Subgroup.index_eq_card (frattini (sylowEquiv e U))
    _ = q := h.card_frattini (sylowEquiv e U)

theorem of_mulEquiv (e : X ≃* Y) {q : ℕ} (h : SuzukiTorusData Y q) :
    SuzukiTorusData X q where
  faithful := faithful_of_mulEquiv e h
  card_points := card_points_of_mulEquiv e h
  fixes_le_two := fixes_le_two_of_mulEquiv e h
  card_sylow := card_sylow_of_mulEquiv e h
  regular := regular_of_mulEquiv e h
  inf_normalizer_isCyclic := inf_normalizer_isCyclic_of_mulEquiv e h
  inf_normalizer_card := inf_normalizer_card_of_mulEquiv e h
  inf_normalizer_free := inf_normalizer_free_of_mulEquiv e h
  card_frattini := card_frattini_of_mulEquiv e h

theorem inf_eq_bot_of_ne {q : ℕ} (h : SuzukiTorusData X q) {U V : Sylow 2 X}
    (hne : U ≠ V) : (U : Subgroup X) ⊓ (V : Subgroup X) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  have hxU : x ∈ (U : Subgroup X) := hx.1
  have hxV : x ∈ (V : Subgroup X) := hx.2
  have hfix : (⟨x, hxU⟩ : U) • V = V :=
    (Sylow.smul_eq_iff_mem_normalizer).mpr (Subgroup.le_normalizer hxV)
  obtain ⟨u, hu, huniq⟩ := h.regular U V V hne.symm hne.symm
  have hx1 : (⟨x, hxU⟩ : U) = 1 := by
    calc (⟨x, hxU⟩ : U) = u := huniq ⟨x, hxU⟩ hfix
      _ = 1 := (huniq 1 (by simp)).symm
  simpa using congrArg Subtype.val hx1

end SuzukiTorusData

end CFSG.GroupTheory

end
