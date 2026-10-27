module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open scoped commutatorElement
open scoped Pointwise

theorem card_le_pow_factorization {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    {W H : Subgroup K} (hHW : H ≤ W) (hH : IsPGroup q H) :
    Nat.card H ≤ q ^ (Nat.card W).factorization q := by
  haveI := Fact.mk hq
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hdvd : Nat.card H ∣ Nat.card W := Subgroup.card_dvd_of_le hHW
  have hWne : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have hk2 : q ^ k ∣ Nat.card W := by rw [← hk]; exact hdvd
  have hk' := (Nat.Prime.pow_dvd_iff_le_factorization hq hWne).mp hk2
  rw [hk]
  exact Nat.pow_le_pow_right hq.pos hk'

def sylowOfCard {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime) (Q : Subgroup K)
    (hQ : IsPGroup q Q) (hcard : Nat.card Q = q ^ (Nat.card K).factorization q) : Sylow q K :=
  Sylow.mk Q hQ (fun {R} hR hle => by
    have h1 := card_le_pow_factorization hq (le_top : R ≤ ⊤) hR
    rw [Subgroup.card_top] at h1
    apply (Subgroup.eq_of_le_of_card_ge hle _).symm
    rw [hcard]
    exact h1)

theorem card_inf_normal {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (W : Subgroup K) [W.Normal] (Q : Subgroup K) (hQ : IsPGroup q Q)
    (hcard : Nat.card Q = q ^ (Nat.card K).factorization q) :
    Nat.card (Q ⊓ W : Subgroup K) = q ^ (Nat.card W).factorization q := by
  haveI := Fact.mk hq
  obtain ⟨PW⟩ : Nonempty (Sylow q W) := Sylow.nonempty
  let R : Subgroup K := PW.toSubgroup.map W.subtype
  have hR : IsPGroup q R := PW.isPGroup'.map W.subtype
  have hRcard : Nat.card R = q ^ (Nat.card W).factorization q := by
    rw [← Sylow.card_eq_multiplicity PW]
    exact Nat.card_congr (Subgroup.equivMapOfInjective PW.toSubgroup W.subtype
      W.subtype_injective).symm.toEquiv
  obtain ⟨Q', hRQ'⟩ := IsPGroup.exists_le_sylow hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K (sylowOfCard hq Q hQ hcard) Q'
  have hset : ∀ x : K, x ∈ (Q' : Subgroup K) ↔ ∃ y ∈ Q, g * y * g⁻¹ = x := by
    intro x
    have h1 : (Q' : Set K) = MulAut.conj g • (Q : Set K) := by
      rw [← hg, Sylow.coe_smul]
      rfl
    have h2 : x ∈ (Q' : Set K) ↔ x ∈ MulAut.conj g • (Q : Set K) := by rw [h1]
    rw [Set.mem_smul_set] at h2
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := h2.mp hx
      exact ⟨y, hy, by simpa [MulAut.conj_apply] using hyx⟩
    · rintro ⟨y, hy, rfl⟩
      exact h2.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
  let e : (Q ⊓ W : Subgroup K) ≃ (Q' ⊓ W : Subgroup K) :=
    { toFun := fun y => ⟨g * y * g⁻¹, by
        refine ⟨(hset _).mpr ⟨y, y.2.1, rfl⟩, ?_⟩
        exact Subgroup.Normal.conj_mem inferInstance _ y.2.2 g⟩
      invFun := fun x => ⟨g⁻¹ * x * g, by
        obtain ⟨hx1, hx2⟩ := x.2
        obtain ⟨y, hy, hyx⟩ := (hset _).mp hx1
        have : g⁻¹ * (x : K) * g = y := by
          rw [← hyx]; group
        refine ⟨?_, ?_⟩
        · rw [this]; exact hy
        · have := Subgroup.Normal.conj_mem inferInstance _ hx2 g⁻¹
          simpa using this⟩
      left_inv := fun y => by
        apply Subtype.ext
        simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, Subgroup.coe_mul]
        group
      right_inv := fun x => by
        apply Subtype.ext
        simp only
        group }
  have hQW : Nat.card (Q ⊓ W : Subgroup K) = Nat.card (Q' ⊓ W : Subgroup K) :=
    Nat.card_congr e
  rw [hQW]
  have hQ'W : IsPGroup q (Q' ⊓ W : Subgroup K) := Q'.isPGroup'.to_le inf_le_left
  have hRW : R ≤ W := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  apply le_antisymm
  · exact card_le_pow_factorization hq inf_le_right hQ'W
  · rw [← hRcard]
    exact Subgroup.card_le_of_le (le_inf hRQ' hRW)



theorem sylow_map_quotient {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (W : Subgroup K) [W.Normal] (Q : Subgroup K) (hQ : IsPGroup q Q)
    (hcard : Nat.card Q = q ^ (Nat.card K).factorization q) :
    IsPGroup q (Q.map (QuotientGroup.mk' W)) ∧
      Nat.card (Q.map (QuotientGroup.mk' W)) = q ^ (Nat.card (K ⧸ W)).factorization q := by
  refine ⟨hQ.map (QuotientGroup.mk' W), ?_⟩
  let f : Q →* (K ⧸ W) := (QuotientGroup.mk' W).comp Q.subtype
  have hker : f.ker = (Q ⊓ W : Subgroup K).subgroupOf Q := by
    ext x
    simp [f, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f.range = Q.map (QuotientGroup.mk' W) := by
    rw [MonoidHom.range_eq_map]
    ext y
    simp [f, Subgroup.mem_map]
  have hQidx : Nat.card Q = Nat.card (Q ⊓ W : Subgroup K) * Nat.card (Q.map (QuotientGroup.mk' W)) := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hrange, hker] at h1
    rw [← h1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓ W ≤ Q)).toEquiv
  have hKq : Nat.card K = Nat.card (K ⧸ W) * Nat.card W :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup W
  have hinf := card_inf_normal hq W Q hQ hcard
  have hWne : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have hQne : Nat.card (K ⧸ W) ≠ 0 := Nat.card_pos.ne'
  have hKne : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hfact : (Nat.card K).factorization q =
      (Nat.card (K ⧸ W)).factorization q + (Nat.card W).factorization q := by
    rw [hKq, Nat.factorization_mul hQne hWne]
    rfl
  rw [hcard, hinf, hfact] at hQidx
  have hpos : q ^ (Nat.card W).factorization q ≠ 0 := (pow_pos hq.pos _).ne'
  have h2 : q ^ (Nat.card W).factorization q * Nat.card (Q.map (QuotientGroup.mk' W)) =
      q ^ (Nat.card W).factorization q * q ^ (Nat.card (K ⧸ W)).factorization q := by
    rw [← hQidx, pow_add, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) h2
end CFSG.LocalAnalysis.GLTheoremA.H248
