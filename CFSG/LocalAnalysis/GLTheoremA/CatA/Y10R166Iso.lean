module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F166
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem evenRank_eq_of_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) : evenRank X = evenRank Y :=
  le_antisymm (CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e)
    (CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e.symm)

theorem innerDiagMarking_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {B J : Subgroup Y} (h : InnerDiagMarking B J) :
    InnerDiagMarking (B.map e.symm.toMonoidHom) (J.map e.symm.toMonoidHom) := by
  let eJ : ↥J ≃* ↥(J.map e.symm.toMonoidHom) := e.symm.subgroupMap J
  have hcoe : ∀ x : ↥(J.map e.symm.toMonoidHom), ((eJ.symm x : ↥J) : Y) = e (x : X) := by
    intro x
    dsimp only [eJ]
    exact congrArg Subtype.val (MulEquiv.subgroupMap_symm_apply e.symm J x)
  refine glaMarking_congr eJ.symm (P' := fun _ _ _ I _ θ =>
    B ≤ Subgroup.normalizer (J : Set Y) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' : ↥J => (l' : Y) = b⁻¹ * l * b) φ) ?_ h
  intro lab R _ I F θ hθ
  obtain ⟨hN, hb⟩ := hθ
  refine ⟨(Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map e.symm.toMonoidHom), ?_⟩
  intro b hb'
  obtain ⟨b', hb'', rfl⟩ := Subgroup.mem_map.1 hb'
  obtain ⟨φ, hφ, hind⟩ := hb b' hb''
  refine ⟨φ, hφ, ?_⟩
  refine (CFSG.StandardType.largeEvenInduces_congr_equiv eJ.symm θ _ _
    (fun x x' => ?_) φ).2 hind
  rw [hcoe x', hcoe x]
  constructor
  · intro hxx
    simpa using congrArg e hxx
  · intro hxx
    simpa using congrArg e.symm hxx

theorem glaPLayer_inf_centralizer_mulEquiv {X Y : Type} [Group X] [Finite Y] [Group Y]
    (e : X ≃* Y) {q : ℕ} (hq : q.Prime) (J E : Subgroup Y) :
    GLAPLayer q (J.map e.symm.toMonoidHom ⊓
        Subgroup.centralizer ((E.map e.symm.toMonoidHom : Subgroup X) : Set X)) =
      (GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set Y))).map e.symm.toMonoidHom := by
  have harg : J.map e.symm.toMonoidHom ⊓
      Subgroup.centralizer ((E.map e.symm.toMonoidHom : Subgroup X) : Set X) =
      (J ⊓ Subgroup.centralizer (E : Set Y)).map e.symm.toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ e.symm.injective, Subgroup.coe_map, MulEquiv.coe_toMonoidHom,
      CFSG.Walter.map_centralizer_mulEquiv e.symm (E : Set Y)]
  rw [harg, glaPLayer_map hq e.symm.injective]

theorem concl166S_of_mulEquiv {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (e : K ≃* K') {p q : ℕ} {B' : Subgroup K'} {x' : K'} {J : Subgroup K'}
    (h : Concl166S K' p q B' x' J) :
    Concl166S K p q (B'.map e.symm.toMonoidHom) (e.symm x') (J.map e.symm.toMonoidHom) := by
  let eJ : ↥J ≃* ↥(J.map e.symm.toMonoidHom) := e.symm.subgroupMap J
  have hq1 : 1 < q := h.prime.one_lt
  refine
    { prime := h.prime
      odd := h.odd
      elem := (isElemAbelian_map_iff_of_injective e.symm.injective B').2 h.elem
      mem := Subgroup.mem_map_of_mem e.symm.toMonoidHom h.mem
      ne_one := fun h1 => h.ne_one (by simpa using congrArg e h1)
      rank_B := by
        rw [Subgroup.card_map_of_injective e.symm.injective, h.rank_B,
          evenRank_eq_of_mulEquiv e]
      rank_K := by
        rw [← CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hq1 e,
          h.rank_K, evenRank_eq_of_mulEquiv e]
      comp := ?_
      chev2 := (hasLabel_congr eJ (fun _ => True)).1 h.chev2
      shape := ?_
      m2 := ?_
      odd_center := ?_
      e3 := ?_
      dvd := ?_
      six := ?_
      idiag := innerDiagMarking_mulEquiv e h.idiag
      seven := ?_
      rank_inf := ?_
      eight := ?_
      su_case := ?_ }
  · have hcent : (Subgroup.centralizer ({x'} : Set K')).map e.symm.toMonoidHom =
        Subgroup.centralizer ({e.symm x'} : Set K) :=
      CFSG.Walter.map_centralizer_singleton_mulEquiv e.symm x'
    refine ⟨?_, ?_⟩
    · rw [← hcent]
      exact (isComponentOf_map_iff e.symm.injective).2 h.comp.1
    · rw [← hcent, glaLayer_map e.symm.injective, h.comp.2]
  · intro lab hlab
    obtain ⟨labJ, hl, hs⟩ := h.shape lab ((hasLabel_congr e (fun l => l = lab)).1 hlab)
    refine ⟨labJ, (hasLabel_congr eJ (fun l => l = labJ)).1 hl, ?_⟩
    have hz : (3 ∣ Nat.card (Subgroup.center K)) ↔
        (3 ∣ Nat.card (Subgroup.center K')) := by
      rw [card_center_congr e]
    simpa only [hz] using hs
  · rw [evenRank_eq_of_mulEquiv e, twoRank_congr eJ]
    exact h.m2
  · rw [card_center_congr eJ]
    exact h.odd_center
  · obtain ⟨E', hE'B, hE'A, hE'c, hxE, hlay⟩ := h.e3
    refine ⟨E'.map e.symm.toMonoidHom, Subgroup.map_mono hE'B,
      (isElemAbelian_map_iff_of_injective e.symm.injective E').2 hE'A, ?_,
      Subgroup.mem_map_of_mem e.symm.toMonoidHom hxE, ?_⟩
    · rw [Subgroup.card_map_of_injective e.symm.injective, hE'c]
    · rw [glaPLayer_inf_centralizer_mulEquiv e h.prime J E']
      intro h0
      exact hlay ((Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1 h0)
  · rw [card_quot_center_congr eJ]
    exact h.dvd
  · rcases h.six with ⟨hc, hm⟩ | ⟨h4, labJ, hl, ht, hr, hn⟩ | ⟨hJ, h3, lab, hl, hodd, hlab⟩
    · exact Or.inl ⟨(center_eq_bot_congr eJ).2 hc, (trivialMultiplier_congr eJ).1 hm⟩
    · exact Or.inr (Or.inl ⟨by rw [evenRank_eq_of_mulEquiv e]; exact h4, labJ,
        (hasLabel_congr eJ (fun l => l = labJ)).1 hl, ht, hr, hn⟩)
    · refine Or.inr (Or.inr ⟨?_, ?_, lab, (hasLabel_congr e (fun l => l = lab)).2 hl,
        hodd, hlab⟩)
      · rw [hJ, Subgroup.map_top_of_surjective _ e.symm.surjective]
      · rw [← card_center_congr e]
        exact h3
  · rcases h.seven with hs | hs
    · left
      refine (Subgroup.map_mono hs).trans (le_of_eq ?_)
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    · exact Or.inr ((hasLabel_congr e _).2 hs)
  · rw [← Subgroup.map_inf _ _ _ e.symm.injective,
      pRank_map_of_injective e.symm.injective, evenRank_eq_of_mulEquiv e]
    exact h.rank_inf
  · obtain ⟨S', hS'J, hS'2, hBS', hBC⟩ := h.eight
    refine ⟨S'.map e.symm.toMonoidHom, Subgroup.map_mono hS'J, hS'2.map _,
      (Subgroup.map_mono hBS').trans (Subgroup.le_normalizer_map e.symm.toMonoidHom), ?_⟩
    rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom,
      ← CFSG.Walter.map_centralizer_mulEquiv e.symm (S' : Set K'),
      ← Subgroup.map_inf _ _ _ e.symm.injective, hBC, MonoidHom.map_zpowers]
    rfl
  · intro h3 hlab
    have h3' : 3 ∣ Nat.card (Subgroup.center K') := by
      rwa [card_center_congr e]
    obtain ⟨lab, hl, hlt⟩ := hlab
    obtain ⟨hJ, hq, hc⟩ := h.su_case h3'
      ⟨lab, (hasLabel_congr e (fun l => l = lab)).1 hl, hlt⟩
    refine ⟨?_, hq, fun k => ?_⟩
    · rw [hJ, Subgroup.map_top_of_surjective _ e.symm.surjective]
    · simpa using congrArg e.symm (hc (e k))

theorem exists_concl166S_of_mulEquiv {K R : Type} [Group K] [Finite K] [Group R] [Finite R]
    (e : K ≃* R) {p : ℕ}
    (h : ∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) :
    ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J := by
  obtain ⟨q, B', x', J, hc⟩ := h
  exact ⟨q, _, _, _, concl166S_of_mulEquiv e hc⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
