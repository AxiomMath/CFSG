module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporTools
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleChar2
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddUnitary

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def UniversalPairIn (S : Type*) [Group S] : Prop :=
  ∃ B₁ B₂ : Subgroup S, CFSG.Assembly.IsQuasisimple B₁ ∧ CFSG.Assembly.IsQuasisimple B₂ ∧
    ⁅B₁, B₂⁆ = ⊥ ∧
    (∃ V₁ : Subgroup S, V₁ ≤ B₁ ∧ CFSG.IsElementaryAbelian 2 V₁ ∧ Nat.card V₁ = 4) ∧
    (∃ V₂ : Subgroup S, V₂ ≤ B₂ ∧ CFSG.IsElementaryAbelian 2 V₂ ∧ Nat.card V₂ = 4) ∧
    (∀ t ∈ B₂, orderOf t = 2 → CFSG.Assembly.IsComponentOf B₁ (centralizer ({t} : Set S))) ∧
    (∀ s ∈ B₁, orderOf s = 2 → CFSG.Assembly.IsComponentOf B₂ (centralizer ({s} : Set S)))

theorem universalPairIn_map {S D : Type*} [Group S] [Group D] {ψ : S →* D}
    (hψ : Function.Injective ψ) (hψrange : ψ.range.Normal) (h : UniversalPairIn S) :
    UniversalPairIn D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B₁, B₂, hq₁, hq₂, hcomm, ⟨V₁, hV₁, hV₁e, hV₁c⟩, ⟨V₂, hV₂, hV₂e, hV₂c⟩, h₁, h₂⟩ := h
  have hfour : ∀ {B V : Subgroup S}, V ≤ B → CFSG.IsElementaryAbelian 2 V → Nat.card V = 4 →
      ∃ W : Subgroup D, W ≤ B.map ψ ∧ CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 :=
    fun {_ V} hVB _ hVc => ⟨V.map ψ, Subgroup.map_mono hVB, CFSG.IsElementaryAbelian.map ψ,
      by rw [Subgroup.card_map_of_injective hψ, hVc]⟩
  have hloc : ∀ {B B' : Subgroup S}, (∀ t ∈ B', orderOf t = 2 →
      CFSG.Assembly.IsComponentOf B (centralizer ({t} : Set S))) →
      ∀ t ∈ B'.map ψ, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf (B.map ψ) (centralizer ({t} : Set D)) := by
    intro B B' hB t ht ht2
    obtain ⟨w, hw, rfl⟩ := ht
    rw [orderOf_injective ψ hψ] at ht2
    have hc := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff hψ).2 (hB w hw ht2)
    rw [LocalAnalysis.ComponentInitial.map_centralizer_singleton_of_injective hψ] at hc
    exact LocalAnalysis.ComponentInitial.isComponentOf_of_normal_inf hψrange hc
  exact ⟨_, _, LocalAnalysis.ComponentInitial.isQuasisimple_map_of_injective hψ hq₁,
    LocalAnalysis.ComponentInitial.isQuasisimple_map_of_injective hψ hq₂,
    by rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot],
    hfour hV₁ hV₁e hV₁c, hfour hV₂ hV₂e hV₂c, hloc h₁, hloc h₂⟩

theorem exists_fourGroup_of_two_le_pRank {T : Type*} [Group T] [Finite T] {X : Subgroup T}
    (hX : 2 ≤ CFSG.Open.pRank 2 X) :
    ∃ V : Subgroup T, V ≤ X ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEX, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) X
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := 2)
    (by rw [hEcard]; exact pow_dvd_pow 2 hX)
  have hc : ∀ x ∈ W.map E.subtype, ∀ y ∈ W.map E.subtype, x * y = y * x := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact congrArg Subtype.val (hE.1.is_comm.comm x y)
  have hp : ∀ x ∈ W.map E.subtype, x ^ 2 = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact hE.2 x x.2
  refine ⟨W.map E.subtype, (map_subtype_le W).trans hEX,
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hp x x.2) }, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hW]
  norm_num

theorem universalPairIn_of_clean {T : Type} [Group T] [Finite T] {X Y : Subgroup T}
    (hXq : CFSG.IsQuasisimple X) (hYq : CFSG.IsQuasisimple Y) (hXr : 2 ≤ CFSG.Open.pRank 2 X)
    (hYr : 2 ≤ CFSG.Open.pRank 2 Y) (hXY : ⁅X, Y⁆ = ⊥)
    (hXc : ∀ y ∈ Y, orderOf y = 2 → IsTwoComponentIn X (centralizer ({y} : Set T)))
    (hYc : ∀ x ∈ X, orderOf x = 2 → IsTwoComponentIn Y (centralizer ({x} : Set T))) :
    UniversalPairIn T :=
  ⟨X, Y, (AssemblyBPredicates.isQuasisimple_iff_native X).2 hXq,
    (AssemblyBPredicates.isQuasisimple_iff_native Y).2 hYq, hXY,
    exists_fourGroup_of_two_le_pRank hXr, exists_fourGroup_of_two_le_pRank hYr,
    fun y hy hy2 => isComponentOf_of_isTwoComponentIn (hXc y hy hy2) hXq,
    fun x hx hx2 => isComponentOf_of_isTwoComponentIn (hYc x hx hx2) hYq⟩

theorem singleComponentCleanAt_of_not_universalPairIn {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (T : Type) [Group T] [Finite T], P T → ¬ UniversalPairIn T) :
    SingleComponentCleanAt P := by
  intro T _ _ _ hP X Y hXq hYq hXr hYr hXY hXc hYc
  exact h T hP (universalPairIn_of_clean hXq hYq hXr hYr hXY hXc hYc)

end CFSG.ComponentClassification.Sol76.Sig

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.ComponentClassification CFSG.Assembly.LowTwoRank CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem sol76_not_universalPairIn_PSL {T : Type} [Group T] {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel T .PSL n p f) : ¬ Sol76.Sig.UniversalPairIn T := by
  obtain ⟨⟨hp, hf, hn, -⟩, k, _, _, hk, ⟨e⟩⟩ := hm
  have : CharP k p := finite_field_prime_power_characteristic hp hf hk
  let e' : T ≃* ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let ψ : T →* ProjGenLinGroup (Fin n) k :=
    ProjectiveSpecialLinearGroup.toPGL.comp e'.toMonoidHom
  have hψ : Function.Injective ψ := ProjectiveSpecialLinearGroup.toPGL_injective.comp e'.injective
  have hψrange : ψ.range.Normal := by
    have h : ψ.range = (ProjectiveSpecialLinearGroup.toPGL (n := Fin n) (R := k)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e'.surjective, ← MonoidHom.range_eq_map]
    rw [h]
    exact range_toPGL_normal (Fin n) k
  exact fun hpair => odd_projective_linear_commuting_universal_pair_exclusion
    (Ring.two_ne_zero (by rw [ringChar.eq k p]; exact hp2)) hn
    (Sol76.Sig.universalPairIn_map hψ hψrange hpair)

theorem sol76_not_universalPairIn_PSU {T : Type} [Group T] {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel T .PSU n p f) : ¬ Sol76.Sig.UniversalPairIn T := by
  obtain ⟨⟨hpp, hf, hn, -⟩, k, _, _, hk, ⟨e⟩⟩ := hm
  have hU : UnitaryFieldData p f k := ⟨hpp, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  have hn1 : 1 ≤ n := by omega
  let ψ : T →* sesqProjUnitary hU (stdHermForm hU n) :=
    (EscapingNotOddUnitary.projEmbed hU n hn1).comp e.toMonoidHom
  have hψ : Function.Injective ψ :=
    (EscapingNotOddUnitary.projEmbed_injective hU n hn1).comp e.injective
  have hψrange : ψ.range.Normal := by
    have h' : ψ.range = (EscapingNotOddUnitary.toProj hU n).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
        EscapingNotOddUnitary.range_projEmbed]
    rw [h']
    exact EscapingNotOddUnitary.toProj_range_normal hU n
  exact fun hpair => odd_projective_unitary_commuting_universal_pair_exclusion hU hp2
    (V := Fin n → k) (by rw [Module.finrank_fin_fun]; omega) (stdHermForm_isSymm hU n)
    (stdHermForm_separatingLeft hU n) (Sol76.Sig.universalPairIn_map hψ hψrange hpair)

theorem sol76_not_universalPairIn_PSp {T : Type} [Group T] {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel T .PSp n p f) : ¬ Sol76.Sig.UniversalPairIn T := by
  obtain ⟨⟨hp, hf, hn, -⟩, k, _, _, hk, ⟨e⟩⟩ := hm
  have hr : 1 ≤ n := by omega
  let ψ : T →* sesqUnitaryGroup (pairedSympForm k n) ⧸
      ProjectiveSymplectic.spSigns (pairedSympForm k n) :=
    (EscapingNotOddSymplectic.projEquiv hr).toMonoidHom.comp e.toMonoidHom
  have hψ : Function.Injective ψ :=
    (EscapingNotOddSymplectic.projEquiv hr).injective.comp e.injective
  have hψrange : ψ.range.Normal := by
    rw [MonoidHom.range_eq_top.2 ((EscapingNotOddSymplectic.projEquiv hr).surjective.comp
      e.surjective)]
    infer_instance
  exact fun hpair =>
    ProjectiveSymplectic.odd_projective_symplectic_commuting_universal_pair_exclusion
    hp hp2 hf hk hr SymplecticFlag.finrank_standard SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate (Sol76.Sig.universalPairIn_map hψ hψrange hpair)

open CFSG.LieType.Universal.Spin (coe_quadOdd coe_quadPlus coe_quadMinus
  nondegenerate_polarBilin_quadOdd nondegenerate_polarBilin_quadPlus
  nondegenerate_polarBilin_quadMinus_of_finite)
open TauCeti.QuadraticMap (orthogonalGroup)

theorem sol76_not_universalPairIn_of_form {T : Type} [Group T] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hQ : ⇑Q = Q₀) (hnd : Q.polarBilin.Nondegenerate)
    (hι : 5 ≤ Fintype.card ι) (e : T ≃* StatedProj (StatedOmega Q₀)) :
    ¬ Sol76.Sig.UniversalPairIn T := by
  have hd : 5 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hι
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hQne := ProjectiveOrthogonal.exists_ne_zero_of_nondegenerate hnd
  let ψ : T →* orthogonalGroup Q ⧸ ProjectiveOrthogonal.orthSigns Q :=
    (EscapingNotOddOrthogonal.projEmbed hQ (ProjectiveOrthogonal.orthSigns Q)
      EscapingNotOddOrthogonal.mem_orthSigns_iff_scalar hQne).comp e.toMonoidHom
  have hψ : Function.Injective ψ := by
    change Function.Injective ((EscapingNotOddOrthogonal.projEmbed hQ
      (ProjectiveOrthogonal.orthSigns Q) EscapingNotOddOrthogonal.mem_orthSigns_iff_scalar
      hQne).comp e.toMonoidHom)
    rw [MonoidHom.coe_comp]
    exact (EscapingNotOddOrthogonal.projEmbed_injective
      EscapingNotOddOrthogonal.mem_orthSigns_iff_scalar hQne).comp e.injective
  have hψrange : ψ.range.Normal := by
    have h : ψ.range = (EscapingNotOddOrthogonal.projEmbed hQ (ProjectiveOrthogonal.orthSigns Q)
        EscapingNotOddOrthogonal.mem_orthSigns_iff_scalar hQne).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map]
    rw [h]
    exact EscapingNotOddOrthogonal.projEmbed_range_normal
      EscapingNotOddOrthogonal.mem_orthSigns_iff_scalar hQne
  exact fun hpair =>
    ProjectiveOrthogonal.odd_projective_orthogonal_commuting_universal_pair_exclusion hp hp2 hf hK
      hd hnd (Sol76.Sig.universalPairIn_map hψ hψrange hpair)

theorem sol76_not_universalPairIn_orthogonal {T : Type} [Group T] {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel T t n p f) : ¬ Sol76.Sig.UniversalPairIn T := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hpp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have : CharP K p := finite_field_prime_power_characteristic hpp hf hK
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
    exact sol76_not_universalPairIn_of_form hpp hp2 hf hK (coe_quadOdd n K)
      (nondegenerate_polarBilin_quadOdd n K h2)
      (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega) e
  · obtain ⟨⟨hpp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    exact sol76_not_universalPairIn_of_form hpp hp2 hf hK (coe_quadPlus n K)
      (nondegenerate_polarBilin_quadPlus n K)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) e
  · obtain ⟨⟨hpp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
    exact sol76_not_universalPairIn_of_form hpp hp2 hf hK (coe_quadMinus n K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) e

theorem sol76_not_universalPairIn_of_oddClassicalRep {T : Type} [Group T]
    (h : Sol76.Sig.OddClassicalRep T) : ¬ Sol76.Sig.UniversalPairIn T := by
  obtain ⟨t, n, p, f, hp2, hm⟩ := h
  rcases CFSG.Milestones.statedClassicalModel_tag_mem _ t n p f hm with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact sol76_not_universalPairIn_PSL hp2 hm
  · exact sol76_not_universalPairIn_PSU hp2 hm
  · exact sol76_not_universalPairIn_PSp hp2 hm
  · exact sol76_not_universalPairIn_orthogonal (Or.inl rfl) hp2 hm
  · exact sol76_not_universalPairIn_orthogonal (Or.inr (Or.inl rfl)) hp2 hm
  · exact sol76_not_universalPairIn_orthogonal (Or.inr (Or.inr rfl)) hp2 hm

end CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.ComponentClassification.Sol76.Sig

theorem singleComponentCleanAt_oddClassical :
    SingleComponentCleanAt (fun S _ => OddClassicalRep S) :=
  singleComponentCleanAt_of_not_universalPairIn fun _ _ _ h =>
    LocalAnalysis.ComponentInitial.sol76_not_universalPairIn_of_oddClassicalRep h

end CFSG.ComponentClassification.Sol76.Sig
