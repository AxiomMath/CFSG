module

public import CFSG.GH74.E2.Action
public import CFSG.GH74.E2.Local
public import CFSG.GH74.E2.CaseIINoComp

public section

namespace CFSG.GH74.E2

open Subgroup

section Abstract

variable {C : Type} [Group C] [Finite C]

theorem card_le_of_noComponent (hgen : Gen4 C) {Q : Subgroup C} (hQ : IsPGroup 2 Q)
    (hQn : Q.Normal) (hCQ : ∀ c : C, (∀ q ∈ Q, c * q = q * c) → c ∈ Q) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) {B : Subgroup C} (hB : ElemAb p B) : Nat.card B ≤ p := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨r, hcard, hF1⟩ :=
    exists_centralizer_index_pow hQ (fun b _ x hx => hQn.conj_mem x hx b) hp hp2 hB
  have hker : B ⊓ centralizer (Q : Set C) = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcB, hcC⟩
    have hcQ : c ∈ Q := hCQ c (fun q hq => (mem_centralizer_iff.1 hcC q hq).symm)
    have hodd : Odd p := hp.odd_of_ne_two hp2
    exact (Subgroup.mem_bot).2 (eq_one_of_pgroup_of_pow hQ hcQ hodd (hB.2 c hcB))
  have hrank : Group.rank Q ≤ 4 := Gen4.rank_le_four hgen hQ
  have hr1 : r ≤ 1 := (rank_bounds hp hp2 hF1 hrank).2.1 h5
  rw [hker, Subgroup.card_bot, mul_one] at hcard
  rw [hcard]
  calc p ^ r ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hr1
    _ = p := pow_one p

theorem rank_le_two_of_le_Q (hgen : Gen4 C) {Q K : Subgroup C} (hL : LocalK C Q K)
    (hcenter : Nat.card (center ↥K) ≤ 2)
    (hT2 : center ↥K = ⊥ → ∃ T : Subgroup ↥K, IsPGroup 2 T ∧ 2 ≤ Group.rank T)
    (hT3 : center ↥K ≠ ⊥ → ∃ T : Subgroup ↥K, IsPGroup 2 T ∧ 3 ≤ Group.rank T)
    {P : Subgroup C} (hPQ : P ≤ Q) : Group.rank P ≤ 2 := by
  obtain ⟨T, hT, hTr⟩ : ∃ T : Subgroup ↥K, IsPGroup 2 T ∧
      ((center ↥K = ⊥ → 2 ≤ Group.rank T) ∧ (center ↥K ≠ ⊥ → 3 ≤ Group.rank T)) := by
    by_cases hc : center ↥K = ⊥
    · obtain ⟨T, hT, hr⟩ := hT2 hc
      exact ⟨T, hT, fun _ => hr, fun h => absurd hc h⟩
    · obtain ⟨T, hT, hr⟩ := hT3 hc
      exact ⟨T, hT, fun h => absurd h hc, fun _ => hr⟩
  let T' : Subgroup C := T.map K.subtype
  have hT'2 : IsPGroup 2 T' := hT.map K.subtype
  have hrankT' : Group.rank T' = Group.rank T :=
    (Group.rank_congr (T.equivMapOfInjective K.subtype K.subtype_injective)).symm
  have hP2 : IsPGroup 2 P := hL.Q_pgroup.to_le hPQ
  have hcomm : ∀ q ∈ P, ∀ t ∈ T', q * t = t * q := by
    rintro q hq _ ⟨t, -, rfl⟩
    exact hL.commute q (hPQ hq) t t.2
  have hF2 := rank_sup_add_inf_ge P T' hP2 hT'2 hcomm
  have hsup : IsPGroup 2 ↥(P ⊔ T') := isPGroup_sup_of_commute P T' hP2 hT'2 hcomm
  have h4 : Group.rank ↥(P ⊔ T') ≤ 4 := Gen4.rank_le_four hgen hsup
  have hinj : Nat.card ↥(P ⊓ T') ≤ Nat.card (center ↥K) := by
    let f : ↥(P ⊓ T') → center ↥K := fun x =>
      ⟨⟨x.1, by
        obtain ⟨y, -, hy⟩ := x.2.2
        rw [← hy]; exact y.2⟩, by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact (hL.commute x.1 (hPQ x.2.1) k k.2).symm⟩
    refine Nat.card_le_card_of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z => ((z : ↥K) : C)) (Subtype.ext_iff.1 hxy)
  by_cases hc : center ↥K = ⊥
  · have hbot : Nat.card ↥(P ⊓ T') ≤ 1 := by
      calc Nat.card ↥(P ⊓ T') ≤ Nat.card (center ↥K) := hinj
        _ = 1 := by rw [hc, Subgroup.card_bot]
    have hsub : Subsingleton ↥(P ⊓ T') := by
      have := Nat.card_pos (α := ↥(P ⊓ T'))
      exact (Nat.card_eq_one_iff_unique.1 (by omega)).1
    rw [Group.rank_eq_zero_iff.2 hsub] at hF2
    have := hTr.1 hc
    omega
  · have h1 : Group.rank ↥(P ⊓ T') ≤ 1 := rank_le_one_of_card_le_two (hinj.trans hcenter)
    have := hTr.2 hc
    omega

theorem rank_Q_le_two (hgen : Gen4 C) {Q K : Subgroup C} (hL : LocalK C Q K)
    (hcenter : Nat.card (center ↥K) ≤ 2)
    (hT2 : center ↥K = ⊥ → ∃ T : Subgroup ↥K, IsPGroup 2 T ∧ 2 ≤ Group.rank T)
    (hT3 : center ↥K ≠ ⊥ → ∃ T : Subgroup ↥K, IsPGroup 2 T ∧ 3 ≤ Group.rank T) :
    Group.rank Q ≤ 2 :=
  rank_le_two_of_le_Q hgen hL hcenter hT2 hT3 le_rfl

theorem card_le_of_localK (hgen : Gen4 C) {Q K : Subgroup C} (hL : LocalK C Q K)
    (hcenter : Nat.card (center ↥K) ≤ 2)
    (hT2 : center ↥K = ⊥ → ∃ T : Subgroup ↥K, IsPGroup 2 T ∧ 2 ≤ Group.rank T)
    (hT3 : center ↥K ≠ ⊥ → ∃ T : Subgroup ↥K, IsPGroup 2 T ∧ 3 ≤ Group.rank T)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (haut : ∀ R : Subgroup (MulAut ↥K), ElemAb p R → Nat.card R ≤ p)
    {B : Subgroup C} (hB : ElemAb p B) : Nat.card B ≤ p := by
  have hp2 : p ≠ 2 := by omega
  have hQ2 := rank_Q_le_two hgen hL hcenter hT2 hT3
  obtain ⟨r, hcard, hF1⟩ := exists_centralizer_index_pow hL.Q_pgroup
    (fun b _ x hx => hL.Q_normal.conj_mem x hx b) hp hp2 hB
  have hr0 : r = 0 := by
    have h3 := three_le_orderOf_two_zmod hp h5
    by_contra hne
    have : 1 ≤ r := Nat.one_le_iff_ne_zero.2 hne
    nlinarith
  set BQ : Subgroup C := B ⊓ centralizer (Q : Set C) with hBQdef
  have hBQ : Nat.card B = Nat.card BQ := by rw [hcard, hr0]; simp
  have hnormK : BQ ≤ normalizer (K : Set C) := by
    have := hL.K_normal
    exact Subgroup.le_normalizer_of_normal
  let φ : BQ →* MulAut ↥K := conjAction BQ K hnormK
  have hφapp : ∀ (b : BQ) (k : K), ((φ b k : K) : C) = (b : C) * k * (b : C)⁻¹ := fun _ _ => rfl
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hcK : ∀ k ∈ K, (b : C) * k = k * b := by
      intro k hk
      have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : K) : C)) hb
      have h3 : ((φ b ⟨k, hk⟩ : K) : C) = (b : C) * k * (b : C)⁻¹ := rfl
      simp only [h3] at h2
      change (b : C) * k * (b : C)⁻¹ = k at h2
      calc (b : C) * k = ((b : C) * k * (b : C)⁻¹) * b := by group
        _ = k * b := by rw [h2]
    have hcQ : ∀ q ∈ Q, (b : C) * q = q * b := fun q hq =>
      (mem_centralizer_iff.1 b.2.2 q hq).symm
    have hbQ : (b : C) ∈ Q := hL.self_centralizing b hcQ hcK
    have hodd : Odd p := hp.odd_of_ne_two hp2
    apply Subtype.ext
    exact eq_one_of_pgroup_of_pow hL.Q_pgroup hbQ hodd (hB.2 b b.2.1)
  have hRel : ElemAb p φ.range := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hB.1 a a.2.1 b b.2.1)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hB.2 a a.2.1)
      rw [this, map_one]
  have hRcard : Nat.card φ.range = Nat.card BQ :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  calc Nat.card B = Nat.card BQ := hBQ
    _ = Nat.card φ.range := hRcard.symm
    _ ≤ p := haut _ hRel

end Abstract

end CFSG.GH74.E2
