module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFamily
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup

@[expose] def HasNoncyclicThree (Y : Type) [Group Y] : Prop :=
  ∃ P : Subgroup Y, IsPGroup 3 P ∧ ¬ IsCyclic P

theorem noncyclic_map {Y Z : Type} [Group Y] [Group Z] (f : Y →* Z)
    (hf : Function.Injective f) {P : Subgroup Y} (hc : ¬ IsCyclic P) : ¬ IsCyclic (P.map f) := by
  intro hc'
  exact hc (isCyclic_of_surjective (P.equivMapOfInjective f hf).symm.toMonoidHom
    (P.equivMapOfInjective f hf).symm.surjective)

theorem HasNoncyclicThree.of_injective {Y Z : Type} [Group Y] [Group Z] (f : Y →* Z)
    (hf : Function.Injective f) (h : HasNoncyclicThree Y) : HasNoncyclicThree Z := by
  obtain ⟨P, hP, hc⟩ := h
  exact ⟨P.map f, hP.map f, noncyclic_map f hf hc⟩

theorem HasNoncyclicThree.of_quotient {L : Type} [Group L] [Finite L] (N : Subgroup L)
    [N.Normal] (h : HasNoncyclicThree (L ⧸ N)) : HasNoncyclicThree L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ, hc⟩ := h
  set Q' := Q.comap (QuotientGroup.mk' N) with hQ'
  let φ : Q' →* Q := (QuotientGroup.mk' N).subgroupComap Q
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 Q') := inferInstance
  have htop : (S : Subgroup Q').map φ = ⊤ := by
    have h1 := (S.mapSurjective hφ).is_maximal' (hQ.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h1
    exact h1.symm
  have hSc : ¬ IsCyclic (S : Subgroup Q') := by
    intro hS
    have : IsCyclic ((S : Subgroup Q').map φ) :=
      isCyclic_of_surjective (φ.subgroupMap (S : Subgroup Q'))
        (φ.subgroupMap_surjective (S : Subgroup Q'))
    rw [htop] at this
    exact hc (isCyclic_of_surjective (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).surjective)
  exact HasNoncyclicThree.of_injective Q'.subtype Q'.subtype_injective ⟨S, S.isPGroup', hSc⟩

theorem base_invariant {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n)
    (h : Blueprint.LieModel Y .PSL 2 3 n) :
    Finite Y ∧ 360 ≤ Nat.card Y ∧ HasNoncyclicThree Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  have hcard := SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num) hF
  have h9 : 9 ≤ 3 ^ n := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos : 0 < Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    rw [hcard]
    refine Nat.mul_pos (by positivity) (Nat.div_pos ?_ (by norm_num))
    have : 81 ≤ (3 ^ n) ^ 2 := by nlinarith
    omega
  have hYcard : Nat.card Y = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Nat.card_congr e.toEquiv
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  refine ⟨hfin, ?_, ?_⟩
  · rw [hYcard, hcard]
    have h40 : 40 ≤ ((3 ^ n) ^ 2 - 1) / 2 := by
      have : 81 ≤ (3 ^ n) ^ 2 := by nlinarith
      omega
    calc 360 = 9 * 40 := by norm_num
      _ ≤ 3 ^ n * (((3 ^ n) ^ 2 - 1) / 2) := Nat.mul_le_mul h9 h40
  · have : Fintype F := Fintype.ofFinite F
    have : CharP F 3 := charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card, hF])
    refine HasNoncyclicThree.of_injective e.symm.toMonoidHom e.symm.injective
      ⟨(SectionRank.OddCover.pslU (K := F)).range, ?_, ?_⟩
    · intro x
      obtain ⟨t, ht⟩ := x.2
      refine ⟨1, Subtype.ext ?_⟩
      change (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3 = 1
      rw [← ht, ← map_pow, SectionRank.OddCover.multiplicative_pow_char_eq_one, map_one]
    · intro hcyc
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
        (α := (SectionRank.OddCover.pslU (K := F)).range)
      have hg3 : g ^ 3 = 1 := by
        obtain ⟨t, ht⟩ := g.2
        apply Subtype.ext
        change (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3 = 1
        rw [← ht, ← map_pow, SectionRank.OddCover.multiplicative_pow_char_eq_one, map_one]
      have h3 : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
      rw [hg, SectionRank.OddCover.card_range_pslU, hF] at h3
      omega

theorem blowup_data {X Y : Type} [Group X] [Group Y] (hb : IsBlowup X Y)
    (hY : HasNoncyclicThree Y) : ∃ α : MulAut X, orderOf α = 2 ∧
      Nat.card Y ≤ Nat.card (fixedPoints α) ∧
      ∃ P : Subgroup X, P ≤ fixedPoints α ∧ IsPGroup 3 P ∧ ¬ IsCyclic P := by
  obtain ⟨hfin, -, α, hα, L, -, ⟨e⟩⟩ := hb
  refine ⟨α, hα, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    calc Nat.card (↥L ⧸ Open.fusionZStar ↥L) ≤ Nat.card L :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ ≤ Nat.card (fixedPoints α) := Subgroup.card_le_card_group L
  · have hL : HasNoncyclicThree L :=
      HasNoncyclicThree.of_quotient (Open.fusionZStar ↥L)
        (HasNoncyclicThree.of_injective e.symm.toMonoidHom e.symm.injective hY)
    obtain ⟨Q, hQ, hcQ⟩ := hL
    set f := (fixedPoints α).subtype.comp L.subtype with hfdef
    have hf : Function.Injective f :=
      (fixedPoints α).subtype_injective.comp L.subtype_injective
    refine ⟨Q.map f, ?_, hQ.map f, noncyclic_map f hf hcQ⟩
    rintro x ⟨y, -, rfl⟩
    exact ((y : ↥L) : ↥(fixedPoints α)).2

theorem harrisF_invariant {Y : Type} [Group Y] (h : HarrisF 3 Y) :
    Finite Y ∧ 360 ≤ Nat.card Y ∧ HasNoncyclicThree Y := by
  induction h with
  | base hY =>
    obtain ⟨n, hn, hm⟩ := hY
    exact base_invariant (by simpa using hn) hm
  | blowup _ _ hb ih =>
    obtain ⟨-, h360, hnc⟩ := ih
    have hfin := hb.1
    obtain ⟨α, -, hcard, P, -, hP, hc⟩ := blowup_data hb hnc
    exact ⟨hfin, h360.trans (hcard.trans (Subgroup.card_le_card_group _)), P, hP, hc⟩

theorem harrisF_cases {X : Type} [Group X] (h : HarrisF 3 X) :
    (∃ n : ℕ, 2 ≤ n ∧ Blueprint.LieModel X .PSL 2 3 n) ∨
      ∃ α : MulAut X, orderOf α = 2 ∧ 360 ≤ Nat.card (fixedPoints α) ∧
        ∃ P : Subgroup X, P ≤ fixedPoints α ∧ IsPGroup 3 P ∧ ¬ IsCyclic P := by
  cases h with
  | base hY =>
    obtain ⟨n, hn, hm⟩ := hY
    exact Or.inl ⟨n, by simpa using hn, hm⟩
  | blowup hY _ hb =>
    obtain ⟨-, h360, hnc⟩ := harrisF_invariant hY
    obtain ⟨α, hα, hcard, P, hPα, hP, hc⟩ := blowup_data hb hnc
    exact Or.inr ⟨α, hα, h360.trans hcard, P, hPα, hP, hc⟩

end CFSG.ComponentClassification.HarrisLit.L33
