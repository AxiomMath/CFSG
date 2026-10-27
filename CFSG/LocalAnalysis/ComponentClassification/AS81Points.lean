module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem inf_eq_bot_of_mem_pointsIn {A R E : Subgroup G}
    (hKte : TightlyEmbedded (centralizer (A : Set G))) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {Q₁ Q₂ : Subgroup G} (h₁ : Q₁ ∈ pointsIn R E)
    (h₂ : Q₂ ∈ pointsIn R E) (hne : Q₁ ≠ Q₂) : Q₁ ⊓ Q₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ₁E, x₁, rfl⟩ := h₁
  obtain ⟨hQ₂E, x₂, rfl⟩ := h₂
  set K := centralizer (A : Set G)
  have hR₁ := AschbacherTheorem3.isSylowOf_rightConjugate hR x₁
  have hR₂ := AschbacherTheorem3.isSylowOf_rightConjugate hR x₂
  have hKx : rightConjugate (rightConjugate K (x₂ * x₁⁻¹)) x₁ = rightConjugate K x₂ := by
    rw [rightConjugate_mul, inv_mul_cancel_right]
  by_cases hy : x₂ * x₁⁻¹ ∈ normalizer (K : Set G)
  ·
    exfalso
    apply hne
    rw [(rightConjugate_eq_self_iff K _).mpr hy] at hKx
    have hN : rightConjugate R x₂ ≤ normalizer (rightConjugate R x₁ : Set G) := fun y hy' =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
        hE z (hQ₁E hz) y (hQ₂E hy'))
    have h2 := hR₁.isPGroup.to_sup_of_normal_left' hR₂.isPGroup hN
    have h1 := hR₁.eq_of_le le_sup_left (sup_le hR₁.le (hKx ▸ hR₂.le)) h2
    have h3 := hR₂.eq_of_le le_sup_right (sup_le (hKx.symm ▸ hR₁.le) hR₂.le) h2
    rw [← h1, h3]
  ·
    have hodd := hKte.2 _ hy
    have hodd' : Odd (Nat.card (rightConjugate K x₁ ⊓ rightConjugate K x₂ : Subgroup G)) := by
      rw [← hKx, ← AschbacherTheorem3.rightConjugate_inf, rightConjugate_card]
      exact hodd
    exact two_subgroup_of_odd_eq_bot _ _ (hR₁.isPGroup.to_le inf_le_left) hodd'
      (inf_le_inf hR₁.le hR₂.le)

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {n : G} (hH : n ∈ normalizer (H : Set G))
    (hK : n ∈ normalizer (K : Set G)) : n ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

omit [Finite G] in
theorem self_mem_pointsIn {R E : Subgroup G} (hRE : R ≤ E) : R ∈ pointsIn R E :=
  ⟨hRE, 1, (rightConjugate_one R).symm⟩

omit [Finite G] in
theorem rightConjugate_mem_pointsIn {R E Q : Subgroup G} (hQ : Q ∈ pointsIn R E) {n : G}
    (hn : n ∈ normalizer (E : Set G)) : rightConjugate Q n ∈ pointsIn R E := by
  obtain ⟨hQE, x, rfl⟩ := hQ
  refine ⟨fun y hy => ?_, x * n, rightConjugate_mul R x n⟩
  rw [mem_rightConjugate_iff] at hy
  have := (mem_normalizer_iff.mp ((normalizer (E : Set G)).inv_mem hn) _).mp (hQE hy)
  simpa [mul_assoc] using this

section Cover

variable {A R E : Subgroup G}

omit [Finite G] in
theorem eq_inf_sup_of_le_sup (hRA : R ≤ centralizer (A : Set G)) (hRE : R ≤ E)
    (hEAR : E ≤ A ⊔ R) : E = (E ⊓ A) ⊔ R := by
  refine le_antisymm (fun e he => ?_) (sup_le inf_le_left hRE)
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hRE hEAR he
  exact mul_mem (mem_sup_left ha) (mem_sup_right hr)

theorem card_eq_card_inf_mul (hRA : R ≤ centralizer (A : Set G)) (hRE : R ≤ E)
    (hEAR : E ≤ A ⊔ R) (hRA1 : R ⊓ A = ⊥) : Nat.card E = Nat.card (E ⊓ A : Subgroup G) * Nat.card R := by
  have hN : R ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := fun r hr =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hRA hr) x hx.2))
  have hinf : E ⊓ A ⊓ R = ⊥ := by
    rw [eq_bot_iff, ← hRA1]
    exact fun x hx => ⟨hx.2, hx.1.2⟩
  conv_lhs => rw [eq_inf_sup_of_le_sup hRA hRE hEAR]
  exact AschbacherTheorem3.card_sup_of_le_normalizer hN hinf

variable (hA : TightlyEmbedded (centralizer (A : Set G))) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
  (hE : IsElemAbelian 2 E) (hRE : R ≤ E) (hEAR : E ≤ A ⊔ R) (hRA1 : R ⊓ A = ⊥)
  (hpts : ∀ Q ∈ pointsIn R E, Q ≠ R → Q ⊓ A = ⊥)
  (htrans : ∀ h ∈ E ⊓ A, ∀ h' ∈ E ⊓ A, h ≠ 1 → h' ≠ 1 →
    ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G), n * h * n⁻¹ = h')

include hR hE hRE hEAR hRA1 in
theorem exists_mul_mem_of_mem_pointsIn (hA : TightlyEmbedded (centralizer (A : Set G))) {Q₀ : Subgroup G}
    (hQ₀ : Q₀ ∈ pointsIn R E) (hQ₀R : Q₀ ≠ R) (hQ₀A : Q₀ ⊓ A = ⊥) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) : ∃ h₀ ∈ E ⊓ A, h₀ ≠ 1 ∧ h₀ * r ∈ Q₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨hQ₀E, x, hx⟩ := hQ₀
  have hQ₀card : Nat.card Q₀ = Nat.card R := by rw [hx, rightConjugate_card]
  have hN : Q₀ ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := fun q hq =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy =>
      hcomm y hy.1 q (hQ₀E hq))
  have hinf : E ⊓ A ⊓ Q₀ = ⊥ := by
    rw [eq_bot_iff, ← hQ₀A]
    exact fun y hy => ⟨hy.2, hy.1.2⟩
  have hsup : E ⊓ A ⊔ Q₀ = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hQ₀E) ?_
    rw [AschbacherTheorem3.card_sup_of_le_normalizer hN hinf, hQ₀card,
      card_eq_card_inf_mul hRA hRE hEAR hRA1]
  have hrE : r ∈ ((E ⊓ A ⊔ Q₀ : Subgroup G) : Set G) := by
    rw [hsup]
    exact hRE hr
  have hN' : E ⊓ A ≤ normalizer (Q₀ : Set G) := fun h hh =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy =>
      hcomm y (hQ₀E hy) h hh.1)
  rw [coe_mul_of_left_le_normalizer_right _ _ hN', Set.mem_mul] at hrE
  obtain ⟨h₁, hh₁, q₀, hq₀, hrq⟩ := hrE
  refine ⟨h₁⁻¹, (E ⊓ A).inv_mem hh₁, fun h1 => hr1 ?_, ?_⟩
  ·
    have hh : h₁ = 1 := inv_eq_one.mp h1
    rw [hh, one_mul] at hrq
    have hQR := inf_eq_bot_of_mem_pointsIn hA hR hcomm ⟨hQ₀E, x, hx⟩ (self_mem_pointsIn hRE)
      hQ₀R
    have : r ∈ Q₀ ⊓ R := ⟨hrq ▸ hq₀, hr⟩
    rwa [hQR, mem_bot] at this
  · rw [← hrq, inv_mul_cancel_left]
    exact hq₀

include hA hR hE hRE hEAR hRA1 hpts htrans in
theorem exists_mem_rightConjugate_of_not_mem {Q₀ : Subgroup G} (hQ₀ : Q₀ ∈ pointsIn R E)
    (hQ₀R : Q₀ ≠ R) {e : G} (he : e ∈ E) (heA : e ∉ A) :
    e ∈ R ∨ ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      e ∈ rightConjugate Q₀ n⁻¹ := by
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨h, hh, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hRE hEAR he
  by_cases hh1 : h = 1
  · left
    rw [hh1, one_mul]
    exact hr
  right
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [mul_one] at heA
    exact heA hh.2
  obtain ⟨h₀, hh₀, hh₀1, hq⟩ :=
    exists_mul_mem_of_mem_pointsIn hR hE hRE hEAR hRA1 hA hQ₀ hQ₀R (hpts Q₀ hQ₀ hQ₀R) hr hr1
  obtain ⟨n, hn, hnh⟩ := htrans h₀ hh₀ h hh hh₀1 hh1
  refine ⟨n, hn, ?_⟩
  rw [mem_rightConjugate_iff, inv_inv]
  have hnr : n * r = r * n := (mem_centralizer_iff.mp (hRA hr) n hn.1)
  have : n⁻¹ * (h * r) * n = h₀ * r := by
    rw [← hnh]
    calc n⁻¹ * (n * h₀ * n⁻¹ * r) * n = h₀ * (n⁻¹ * r * n) := by group
      _ = h₀ * r := by
        rw [show n⁻¹ * r * n = r by
          rw [mul_assoc, ← hnr, inv_mul_cancel_left]]
  rw [this]
  exact hq

include hA hR hE hRE hEAR hRA1 hpts htrans in
theorem exists_eq_rightConjugate_of_mem_pointsIn {Q₀ : Subgroup G} (hQ₀ : Q₀ ∈ pointsIn R E)
    (hQ₀R : Q₀ ≠ R) {Q : Subgroup G} (hQ : Q ∈ pointsIn R E) (hQR : Q ≠ R) :
    ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G), Q = rightConjugate Q₀ n⁻¹ := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hQ1 : Q ≠ ⊥ := by
    obtain ⟨-, x, rfl⟩ := hQ
    intro h
    have h1 : Nat.card (rightConjugate R x) = 1 := by rw [h, card_bot]
    rw [rightConjugate_card] at h1
    exact AS76b.isSylowOf_ne_bot_of_even hR hA.1
      (Subgroup.card_eq_one.mp h1)
  obtain ⟨⟨e, heQ⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQ1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heA : e ∉ A := fun h => by
    have : e ∈ Q ⊓ A := ⟨heQ, h⟩
    rw [hpts Q hQ hQR, mem_bot] at this
    exact he1' this
  have hQR' := inf_eq_bot_of_mem_pointsIn hA hR hcomm hQ (self_mem_pointsIn hRE) hQR
  rcases exists_mem_rightConjugate_of_not_mem hA hR hE hRE hEAR hRA1 hpts htrans hQ₀ hQ₀R
    (hQ.1 heQ) heA with heR | ⟨n, hn, hen⟩
  · exfalso
    have : e ∈ Q ⊓ R := ⟨heQ, heR⟩
    rw [hQR', mem_bot] at this
    exact he1' this
  refine ⟨n, hn, ?_⟩
  have hnN : n⁻¹ ∈ normalizer (E : Set G) := by
    refine (normalizer (E : Set G)).inv_mem ?_
    rw [eq_inf_sup_of_le_sup hRA hRE hEAR]
    exact mem_normalizer_sup hn.2 (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) n hn.1).symm))
  by_contra hne
  have := inf_eq_bot_of_mem_pointsIn hA hR hcomm hQ (rightConjugate_mem_pointsIn hQ₀ hnN) hne
  have h' : e ∈ Q ⊓ rightConjugate Q₀ n⁻¹ := ⟨heQ, hen⟩
  rw [this, mem_bot] at h'
  exact he1' h'

include hA hR hE hRE hEAR hRA1 hpts htrans in
theorem card_pointsIn {Q₀ : Subgroup G} (hQ₀ : Q₀ ∈ pointsIn R E) (hQ₀R : Q₀ ≠ R)
    (hcard : Nat.card E = 64) (hR4 : Nat.card R = 4) : Nat.card (pointsIn R E) = 16 := by
  classical
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hHcard : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hRE hEAR hRA1
    rw [hcard, hR4] at this
    omega
  have hptA : ∀ Q ∈ pointsIn R E, Q ⊓ A = ⊥ := fun Q hQ => by
    by_cases hQR : Q = R
    · rw [hQR]
      exact hRA1
    · exact hpts Q hQ hQR
  have hptcard : ∀ Q ∈ pointsIn R E, Nat.card Q = 4 := fun Q hQ => by
    obtain ⟨-, x, rfl⟩ := hQ
    rw [rightConjugate_card, hR4]
  have hex : ∀ e ∈ E, e ∉ A → ∃ Q ∈ pointsIn R E, e ∈ Q := fun e he heA => by
    rcases exists_mem_rightConjugate_of_not_mem hA hR hE hRE hEAR hRA1 hpts htrans hQ₀ hQ₀R he
      heA with heR | ⟨n, hn, hen⟩
    · exact ⟨R, self_mem_pointsIn hRE, heR⟩
    · have hnN : n⁻¹ ∈ normalizer (E : Set G) := by
        refine (normalizer (E : Set G)).inv_mem ?_
        rw [eq_inf_sup_of_le_sup hRA hRE hEAR]
        exact mem_normalizer_sup hn.2 (Subgroup.centralizer_le_normalizer _
          (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) n hn.1).symm))
      exact ⟨_, rightConjugate_mem_pointsIn hQ₀ hnN, hen⟩
  set ptsF : Finset (Subgroup G) := (pointsIn R E).toFinite.toFinset
  set t : Subgroup G → Finset G := fun Q => ((Q : Set G).toFinite.toFinset).erase 1
  set SF : Finset G := (((E : Set G) \ (A : Set G))).toFinite.toFinset
  have hSF : SF = ptsF.biUnion t := by
    ext e
    simp only [SF, ptsF, t, Set.Finite.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe,
      Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · rintro ⟨he, heA⟩
      obtain ⟨Q, hQ, heQ⟩ := hex e he heA
      refine ⟨Q, hQ, fun h => heA (h ▸ A.one_mem), ?_⟩
      simpa using heQ
    · rintro ⟨Q, hQ, he1, heQ⟩
      refine ⟨hQ.1 heQ, fun heA => he1 ?_⟩
      have : e ∈ Q ⊓ A := ⟨heQ, heA⟩
      rwa [hptA Q hQ, mem_bot] at this
  have hdisj : (ptsF : Set (Subgroup G)).PairwiseDisjoint t := by
    intro Q₁ hQ₁ Q₂ hQ₂ hne
    simp only [ptsF, Set.Finite.coe_toFinset] at hQ₁ hQ₂
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    simp only [t, Finset.mem_erase, Set.Finite.mem_toFinset, SetLike.mem_coe] at he₁ he₂
    have hbot := inf_eq_bot_of_mem_pointsIn hA hR hcomm hQ₁ hQ₂ hne
    have : e ∈ Q₁ ⊓ Q₂ := ⟨he₁.2, he₂.2⟩
    rw [hbot, mem_bot] at this
    exact he₁.1 this
  have hcardSF : SF.card = 3 * ptsF.card := by
    rw [hSF, Finset.card_biUnion hdisj, Finset.sum_const_nat (m := 3), mul_comm]
    intro Q hQ
    simp only [ptsF, Set.Finite.mem_toFinset] at hQ
    simp only [t]
    rw [Finset.card_erase_of_mem (by simp), ← Set.ncard_eq_toFinset_card,
      (Nat.card_coe_set_eq _).symm.trans (hptcard Q hQ)]
  have hSFcard : SF.card = 48 := by
    simp only [SF]
    rw [← Set.ncard_eq_toFinset_card, ← Set.sdiff_inter_self_eq_sdiff,
      Set.ncard_sdiff Set.inter_subset_right]
    have h1 : (E : Set G).ncard = 64 := by rw [← Nat.card_coe_set_eq]; exact hcard
    have h2 : ((A : Set G) ∩ (E : Set G)).ncard = 16 := by
      rw [Set.inter_comm, ← Nat.card_coe_set_eq]
      exact hHcard
    rw [h1, h2]
  have hpts16 : ptsF.card = 16 := by omega
  rw [← hpts16, ← Set.ncard_eq_toFinset_card, Nat.card_coe_set_eq]

end Cover

end CFSG.ComponentClassification.AS81
