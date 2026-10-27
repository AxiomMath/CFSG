module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

@[expose] def Rank3Concl (p : ℕ) (S : Type) [Group S] (E : Subgroup (MulAut S)) : Prop :=
  (∃ P : Subgroup S, IsElemAbelian p P ∧ Nat.card P = p ^ 6) ∧
    ∀ T : Subgroup (MulAut S), IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set (MulAut S)) →
      (⁅T, E⁆ : Subgroup (MulAut S)) = T → T = ⊥

@[expose] def IsRank3Small : TauCeti.LieTypeIndex → Prop
  | .A 2 q => q.card = 27
  | .twistedA 2 q => q.card = 27
  | .reeG2 m => m = 1
  | _ => False

@[expose] def IsRank3Handled (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d = .A 1 q) ∨ IsRank3Small d ∨
    ∃ q : TauCeti.PrimePower, d = .D 4 q ∧ q.p = 3

namespace KDRank3Aux

set_option linter.unusedSectionVars false

theorem rank3Concl_of_mulEquiv {p : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {E : Subgroup (MulAut S)}
    (h : Rank3Concl p S' (E.map (MulAut.congr e).toMonoidHom)) : Rank3Concl p S E := by
  refine ⟨?_, ?_⟩
  · obtain ⟨P', hP'el, hP'card⟩ := h.1
    refine ⟨P'.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hP'el e.symm.toMonoidHom,
      ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hP'card]
  · intro T hT hN hc
    set φ : MulAut S →* MulAut S' := (MulAut.congr e).toMonoidHom with hφ
    have hinj : Function.Injective φ := (MulAut.congr e).injective
    have hT' : IsPGroup 2 (T.map φ) := hT.map φ
    have hN' : E.map φ ≤ Subgroup.normalizer ((T.map φ : Subgroup (MulAut S')) : Set (MulAut S')) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨z, rfl⟩ := (MulAut.congr e).surjective y
      change φ z ∈ T.map φ ↔ φ x * φ z * (φ x)⁻¹ ∈ T.map φ
      rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hinj, Subgroup.mem_map_iff_mem hinj]
      exact Subgroup.mem_normalizer_iff.1 (hN hx) z
    have hc' : (⁅T.map φ, E.map φ⁆ : Subgroup (MulAut S')) = T.map φ := by
      rw [← Subgroup.map_commutator, hc]
    have hbot := h.2 (T.map φ) hT' hN' hc'
    rw [eq_bot_iff]
    intro t ht
    have h1 : φ t ∈ T.map φ := ⟨t, ht, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (hinj (by rw [h1, map_one]))


section StepA


theorem card_inf_inner_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hChev : IsChevSimple p S)
    (hrank : GLATwoLocalRank p S ≤ 3) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hnot : ¬ E ≤ inner S) :
    Nat.card ↥(E ⊓ inner S) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  set E₀ : Subgroup (MulAut S) := E ⊓ inner S with hE₀
  have hdvd : Nat.card E₀ ∣ p ^ 3 := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkE⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hk3 : k ≠ 3 := by
    rintro rfl
    apply hnot
    have : E₀ = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hkE])
    rw [← this]
    exact inf_le_right
  by_contra hne
  have hk2' : k ≠ 2 := fun h => hne (by rw [hkE, h])
  have hk2 : k ≤ 1 := by omega
  obtain ⟨C, hCE, hdis, -, hCcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i224_exists_complement hE (inf_le_left : E₀ ≤ E)
  have hC2 : p ^ 2 ∣ Nat.card C := by
    have h1 : p ^ 3 = p ^ k * Nat.card C := by rw [← hcard, hCcard, hkE]
    have h2 : p ^ k * p ^ (3 - k) = p ^ 3 := by rw [← pow_add]; congr 1; omega
    have h3 : Nat.card C = p ^ (3 - k) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k)
      rw [← h1, h2]
    rw [h3]
    exact pow_dvd_pow p (by omega)
  obtain ⟨D, hDcard, -, hDC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (H := ⊥) (L := C) (n := 2) (by simp) hC2 bot_le
  have hDE : D ≤ E := hDC.trans hCE
  have hDel : IsElemAbelian p D := isElemAbelian_mono hE hDE
  have hDI : D ⊓ inner S = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxD, hxI⟩
    have : x ∈ E₀ ⊓ C := ⟨⟨hDE hxD, hxI⟩, hDC hxD⟩
    rwa [hdis] at this
  obtain ⟨hp3, hD4⟩ := (kd76c_holds hp hp2 (kd76cLieP_holds p hp hp2)) S hs hna hChev D hDel
    hDcard hDI
  obtain ⟨i, hi, ⟨e⟩⟩ := hD4
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    have hD : ∃ q : TauCeti.PrimePower, dd = .D 4 q ∧ q.p = 3 := by
      cases dd with
      | D r q =>
        rcases r with _ | _ | _ | _ | _ | r
        · exact hi.elim
        · exact hi.elim
        · exact hi.elim
        · exact hi.elim
        · exact ⟨q, rfl, hi.1⟩
        · exact hi.elim
      | _ => exact hi.elim
    obtain ⟨q, rfl, hq3⟩ := hD
    have h4 := kdD4TwoLocal_holds S q hv hq3 ⟨e⟩
    have := q.exponent_pos
    subst hp3
    omega


end StepA

end KDRank3Aux

end CFSG.LocalAnalysis.GLTheoremA
