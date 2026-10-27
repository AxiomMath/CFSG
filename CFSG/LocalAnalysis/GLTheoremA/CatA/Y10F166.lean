module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def TrivialMultiplierT (X : Type) [Group X] : Prop :=
  ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ → ∀ π : E →* X, Function.Surjective π →
    π.ker ≤ Subgroup.center E → π.ker = ⊥

structure Concl166S (K : Type) [Group K] [Finite K] (p q : ℕ) (B' : Subgroup K) (x' : K)
    (J : Subgroup K) : Prop where
  prime : q.Prime
  odd : q ≠ 2
  elem : IsElemAbelian q B'
  mem : x' ∈ B'
  ne_one : x' ≠ 1
  rank_B : Nat.card B' = q ^ evenRank K
  rank_K : GLATwoLocalRank q K = evenRank K
  comp : IsComponentOf J (Subgroup.centralizer ({x'} : Set K)) ∧
    GLALayer (Subgroup.centralizer ({x'} : Set K)) = J
  chev2 : HasLabel ↥J (fun _ => True)
  shape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
    ∃ labJ : GLALabel, HasLabel ↥J (fun l : GLALabel => l = labJ) ∧
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ
  m2 : evenRank K + 2 ≤ twoRank ↥J
  odd_center : Odd (Nat.card (Subgroup.center ↥J))
  e3 : ∃ E : Subgroup K, E ≤ B' ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 3 ∧ x' ∈ E ∧
    GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥
  dvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)
  six : (Subgroup.center ↥J = ⊥ ∧ TrivialMultiplierT ↥J) ∨
    (evenRank K = 4 ∧ ∃ labJ : GLALabel, HasLabel ↥J (fun l : GLALabel => l = labJ) ∧
      labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
    (J = ⊤ ∧ 3 ∣ Nat.card (Subgroup.center K) ∧ ∃ lab : GLALabel,
      HasLabel K (fun l : GLALabel => l = lab) ∧ Odd lab.n ∧
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6))
  idiag : InnerDiagMarking B' J
  seven : B' ≤ J ⊔ Subgroup.zpowers x' ∨ HasLabel K (fun l : GLALabel => l = ⟨.twA, 5, 2⟩)
  rank_inf : evenRank K ≤ CFSG.Open.pRank q (B' ⊓ J) + 2
  eight : ∃ S : Subgroup K, S ≤ J ∧ IsPGroup 2 S ∧ B' ≤ Subgroup.normalizer (S : Set K) ∧
    B' ⊓ Subgroup.centralizer (S : Set K) = Subgroup.zpowers x'
  su_case : 3 ∣ Nat.card (Subgroup.center K) →
    (∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
    J = ⊤ ∧ q = 3 ∧ ∀ k : K, k * x' = x' * k

@[expose] def I166Fact : Prop :=
  ∀ (K : Type) [Group K] [Finite K], HasLabel K (fun _ => True) →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧
        GLAHalfSplit16 p lab (Subgroup.center K = ⊥)) →
      (∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab) →
      4 ≤ evenRank K → GLATwoLocalRank p K + 1 = evenRank K →
      (p = 7 → ¬ HasLabel K (fun l : GLALabel => l = ⟨.E6, 0, 1⟩)) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J

variable {G : Type} [Group G] [Finite G]

theorem innerDiagMarking_of_map {K : Subgroup G} {B' J' : Subgroup K}
    (h : InnerDiagMarking B' J') : InnerDiagMarking (B'.map K.subtype) (J'.map K.subtype) := by
  have hι := K.subtype_injective
  let e : ↥(J'.map K.subtype) ≃* ↥J' := (Subgroup.equivMapOfInjective J' K.subtype hι).symm
  refine glaMarking_congr e (P' := fun _ _ _ I _ θ =>
      B' ≤ Subgroup.normalizer (J' : Set K) ∧
        ∀ b ∈ B', ∃ φ ∈ I, GLAInduces θ (fun l l' : ↥J' => (l' : K) = b⁻¹ * l * b) φ) ?_ h
  intro lab R _ I F θ hθ
  obtain ⟨hN, hb⟩ := hθ
  refine ⟨map_le_normalizer_map hN, ?_⟩
  intro b hb'
  obtain ⟨b'', hb'', rfl⟩ := Subgroup.mem_map.1 hb'
  obtain ⟨φ, hφ, hind⟩ := hb b'' hb''
  refine ⟨φ, hφ, ?_⟩
  intro l l' hll
  have hel : ∀ x : ↥(J'.map K.subtype), K.subtype ((e x : ↥J') : K) = (x : G) := by
    intro x
    have := (Subgroup.equivMapOfInjective J' K.subtype hι).apply_symm_apply x
    exact congrArg Subtype.val this
  have hrel : ((e l' : ↥J') : K) = b''⁻¹ * ((e l : ↥J') : K) * b'' := by
    apply hι
    rw [map_mul, map_mul, map_inv, hel, hel]
    exact hll
  have := hind (e l) (e l') hrel
  simpa [CFSG.StandardType.centerQuotCongr_mk] using this


theorem concl166_of_S {K : Subgroup G} {p q : ℕ} {B' : Subgroup K} {x' : K} {J' : Subgroup K}
    (h : Concl166S ↥K p q B' x' J') :
    Concl166 G p q K (B'.map K.subtype) (x' : G) (J'.map K.subtype) := by
  have hι := K.subtype_injective
  let eJ : ↥J' ≃* ↥(J'.map K.subtype) := Subgroup.equivMapOfInjective J' K.subtype hι
  refine
    { prime := h.prime
      odd := h.odd
      elem := (isElemAbelian_map_subtype_iff B').2 h.elem
      le := map_subtype_le B'
      mem := Subgroup.mem_map_of_mem _ h.mem
      ne_one := fun h1 => h.ne_one (Subtype.ext h1)
      rank_B := by rw [card_map_subtype]; exact h.rank_B
      rank_K := h.rank_K
      comp := ?_
      chev2 := (hasLabel_congr eJ _).1 h.chev2
      shape := ?_
      m2 := ?_
      odd_center := ?_
      e3 := ?_
      dvd := ?_
      six := ?_
      idiag := innerDiagMarking_of_map h.idiag
      seven := ?_
      rank_inf := ?_
      eight := ?_
      su_case := ?_ }
  · rw [← map_centralizer_singleton_subtype, isComponentOf_map_iff hι, glaLayer_map hι]
    obtain ⟨h1, h2⟩ := h.comp
    exact ⟨h1, by rw [h2]⟩
  · intro lab hlab
    obtain ⟨labJ, hl, hs⟩ := h.shape lab hlab
    exact ⟨labJ, (hasLabel_congr eJ _).1 hl, hs⟩
  · rw [twoRank_congr eJ]; exact h.m2
  · rw [card_center_congr eJ]; exact h.odd_center
  · obtain ⟨E', hE'B, hE', hE'c, hxE, hlay⟩ := h.e3
    refine ⟨E'.map K.subtype, Subgroup.map_mono hE'B, (isElemAbelian_map_subtype_iff E').2 hE',
      by rw [card_map_subtype]; exact hE'c, Subgroup.mem_map_of_mem _ hxE, ?_⟩
    rw [inf_centralizer_map, glaPLayer_map h.prime hι]
    exact fun h0 => hlay ((map_subtype_eq_bot_iff _).1 h0)
  · rw [card_quot_center_congr eJ]; exact h.dvd
  · rcases h.six with ⟨hc, hm⟩ | ⟨h4, labJ, hl, ht, hr, hn⟩ | ⟨hJ, h3, lab, hl, hodd, hlab⟩
    · exact Or.inl ⟨(center_eq_bot_congr eJ).2 hc, (trivialMultiplier_congr eJ).1 hm⟩
    · exact Or.inr (Or.inl ⟨h4, labJ, (hasLabel_congr eJ _).1 hl, ht, hr, hn⟩)
    · refine Or.inr (Or.inr ⟨?_, h3, lab, hl, hodd, hlab⟩)
      rw [hJ, Subgroup.map_top, Subgroup.range_subtype]
  · rcases h.seven with hs | hs
    · left
      refine (Subgroup.map_mono hs).trans (le_of_eq ?_)
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    · exact Or.inr hs
  · rw [← Subgroup.map_inf _ _ _ hι, pRank_map_subtype]; exact h.rank_inf
  · obtain ⟨S', hSJ, hS2, hBS, hBC⟩ := h.eight
    refine ⟨S'.map K.subtype, Subgroup.map_mono hSJ, (isPGroup_map_subtype_iff S').2 hS2,
      map_le_normalizer_map hBS, ?_⟩
    rw [inf_centralizer_map, hBC, MonoidHom.map_zpowers]
    rfl
  · intro h3 hlab
    obtain ⟨hJ, hq, hc⟩ := h.su_case h3 hlab
    refine ⟨by rw [hJ, Subgroup.map_top, Subgroup.range_subtype], hq, x'.2, fun k hk => ?_⟩
    exact congrArg Subtype.val (hc ⟨k, hk⟩)

theorem i166At_of_facts (h : I166Fact) : I166At G := by
  intro p hp hp2 K hK hHS hNS h4 hr h7
  obtain ⟨q, B', x', J', hc⟩ := h ↥K hK p hp hp2 hHS hNS h4 hr h7
  exact ⟨q, B'.map K.subtype, x', J'.map K.subtype, concl166_of_S hc⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
