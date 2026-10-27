module

public import CFSG.ClassicalInvolution.Phan.Coherent
public import CFSG.Timmesfeld.RankTwo.LevisSpin

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open CFSG.Timmesfeld (edgeD)

@[expose] def edgeSrc : Fin 3 → Fin 4 := ![0, 1, 1]

@[expose] def edgeTgt : Fin 3 → Fin 4 := ![1, 2, 3]

theorem edgeD_iff (i j : Fin 4) : edgeD 4 i j ↔ ∃ e, edgeSrc e = i ∧ edgeTgt e = j := by
  revert i j
  decide

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
structure PhanFamilyD4 (Y : Type) [Group Y] where
  ι : Fin 4 → (Su K p f 2 →* Y)
  θ : Fin 3 → (Su K p f 3 →* Y)
  left : ∀ e, (θ e).comp (embSUid (unitaryInvolution K p f) 2) = ι (edgeSrc e)
  right : ∀ e, (θ e).comp (embSUid (unitaryInvolution K p f) 0) = ι (edgeTgt e)
  comm : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → ∀ a b, ι i a * ι j b = ι j b * ι i a

theorem exists_family (hK : Nat.card K = (p ^ f) ^ 2) {X : Type} [Group X]
    (U : Fin 4 → Subgroup X)
    (hcomm : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, edgeD 4 i j → ∃ W, UnitaryBlockStandardPair K p f W (U i) (U j)) :
    ∃ F : PhanFamilyD4 K p f X, (∀ i, (F.ι i).range = U i) ∧
      (∀ i, Function.Injective (F.ι i)) ∧
      ∀ e, (F.θ e).ker ≤ Subgroup.center (Su K p f 3) := by
  classical
  obtain ⟨W01, h01⟩ := hpair 0 1 (by decide)
  obtain ⟨W12, h12⟩ := hpair 1 2 (by decide)
  obtain ⟨W13, h13⟩ := hpair 1 3 (by decide)
  let u : ℕ → Subgroup X := fun i => if h : i < 4 then U ⟨i, h⟩ else ⊥
  let w : ℕ → Subgroup X := fun i => if i = 0 then W01 else W12
  have hu0 : u 0 = U 0 := by simp [u]
  have hu1 : u 1 = U 1 := by simp [u]
  have hu2 : u 2 = U 2 := by simp [u]
  have hw0 : w 0 = W01 := by simp [w]
  have hw1 : w 1 = W12 := by simp [w]
  obtain ⟨θ, hθ⟩ := coherent_chain hK (autExtends hK) u w 2
    (fun i hi => by
      interval_cases i
      · rw [hw0, hu0, hu1]; exact h01
      · rw [hw1, hu1, hu2]; exact h12)
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [hu0, show (0 + 2 : ℕ) = 2 from rfl, hu2]
      exact hcomm 0 2 (by decide) (by decide) (by decide))
  obtain ⟨hk0, hr0, h12_0, h23_0, hc0⟩ := hθ 0 (by omega)
  obtain ⟨hk1, hr1, h12_1, h23_1, -⟩ := hθ 1 (by omega)
  have hc0' := hc0 (by omega)
  obtain ⟨θ', hr', hk', h12', h23'⟩ := pair_normalize h13
  obtain ⟨θ₂, hk₂, hr₂, hb12₂, hb23₂, hcomp₂⟩ := exists_glue hK (autExtends hK) (θ₁ := θ 0)
    (θ₂ := θ') hk0 hk' (by rw [h23_0, hu1, h12'])
    (by
      rw [h12_0, hu0]
      intro x hx y hy
      rw [h23'] at hy
      exact hcomm 0 3 (by decide) (by decide) (by decide) x hx y hy)
  have hb12₂' : (B12 K p f).map θ₂ = U 1 := by rw [hb12₂, h12']
  have hb23₂' : (B23 K p f).map θ₂ = U 3 := by rw [hb23₂, h23']
  have hu1' : (B23 K p f).map (θ 0) = U 1 := by rw [h23_0, hu1]
  have hu0' : (B12 K p f).map (θ 0) = U 0 := by rw [h12_0, hu0]
  have hu1'' : (B12 K p f).map (θ 1) = U 1 := by rw [h12_1, hu1]
  have hu2' : (B23 K p f).map (θ 1) = U 2 := by rw [h23_1, hu2]
  obtain ⟨hi00, hr00, hi01, hr01⟩ := pair_block_inj hK hk0 hu0' hu1'
  obtain ⟨-, -, hi12, hr12⟩ := pair_block_inj hK hk1 hu1'' hu2'
  obtain ⟨-, -, hi23, hr23⟩ := pair_block_inj hK hk₂ hb12₂' hb23₂'
  let F : PhanFamilyD4 K p f X :=
    { ι := ![(θ 0).comp (embSUid (unitaryInvolution K p f) 2),
        (θ 0).comp (embSUid (unitaryInvolution K p f) 0),
        (θ 1).comp (embSUid (unitaryInvolution K p f) 0),
        θ₂.comp (embSUid (unitaryInvolution K p f) 0)]
      θ := ![θ 0, θ 1, θ₂]
      left := fun e => by
        fin_cases e
        · rfl
        · exact hc0'
        · exact hcomp₂
      right := fun e => by
        fin_cases e <;> rfl
      comm := fun i j hij h1 h2 a b => by
        have hrng : ∀ k : Fin 4, ∀ x, x ∈ (![(θ 0).comp (embSUid (unitaryInvolution K p f) 2),
            (θ 0).comp (embSUid (unitaryInvolution K p f) 0),
            (θ 1).comp (embSUid (unitaryInvolution K p f) 0),
            θ₂.comp (embSUid (unitaryInvolution K p f) 0)] k).range → x ∈ U k := by
          intro k x hx
          fin_cases k
          · exact hr00 ▸ hx
          · exact hr01 ▸ hx
          · exact hr12 ▸ hx
          · exact hr23 ▸ hx
        exact hcomm i j hij h1 h2 _ (hrng i _ ⟨a, rfl⟩) _ (hrng j _ ⟨b, rfl⟩) }
  refine ⟨F, fun i => ?_, fun i => ?_, fun e => ?_⟩
  · fin_cases i
    · exact hr00
    · exact hr01
    · exact hr12
    · exact hr23
  · fin_cases i
    · exact hi00
    · exact hi01
    · exact hi12
    · exact hi23
  · fin_cases e
    · exact hk0
    · exact hk1
    · exact hk₂

end CFSG.ClassicalInvolution.PhanD4
