module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCAff
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ConeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Lin

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflB reflRows)

theorem bmulVec_reflRows_n0 (ε : Eps) : ((List.range 64).all fun x =>
    bmulVec 6 6 (reflRows ε (n0 ε)) x == reflB ε (n0 ε) x) = true := by
  cases ε <;> decide

theorem reflB_n0_qf (ε : Eps) : ((List.range 64).all fun x =>
    qfB ε (reflB ε (n0 ε) x) == qfB ε x) = true := by
  cases ε <;> decide

theorem dickC_refl_n0 (ε : Eps) :
    dickC ((List.range 6).map fun j => bmulVec 6 6 (reflRows ε (n0 ε)) (2 ^ j)) = true := by
  cases ε <;> decide

theorem qfV_refl_n0 (ε : Eps) (v : V6) :
    qfV ε (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v) = qfV ε v := by
  have h := reflB_n0_qf ε
  have h' := bmulVec_reflRows_n0 ε
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h h'
  rw [qfV, qfV, vecBits_mulVec, h' _ (vecBits_lt v), h _ (vecBits_lt v)]

theorem colsF_refl_n0 (ε : Eps) :
    colsF (fun v => toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v) =
      (List.range 6).map fun j => bmulVec 6 6 (reflRows ε (n0 ε)) (2 ^ j) := by
  have : colsF (fun v : V6 => v) = (List.range 6).map fun j => 2 ^ j :=
    List.map_congr_left fun j hj => vecBits_basisVec j (List.mem_range.1 hj)
  rw [colsF_mulVec (reflRows ε (n0 ε)) (fun v => v), this, List.map_map]
  rfl

variable {G : Type*} [Group G] {ε : Eps} {L U Q P H₀ : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G}

theorem card_range_linP_ge (hR : RadicalData ε L U Q P a ψ p)
    (hcent : ∀ l ∈ L, (∀ q ∈ Q, l * q = q * l) → l ∈ Q) :
    oBound ε / 2 ≤ Nat.card (hR.linHom.comp (inclusion hR.P_le_normalizer)).range := by
  set f := hR.linHom.comp (inclusion hR.P_le_normalizer)
  have hmemQ : ∀ x : f.ker, ((x : P) : G) ∈ Q := by
    intro x
    refine hcent _ (hR.P_le_L (x : P).2) fun q hq => ?_
    obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
    have h1 : lin ψ ((x : P) : G) v = v := by
      have := congrArg (fun σ : Equiv.Perm V6 => σ v) (MonoidHom.mem_ker.1 x.2)
      exact this
    rw [hR.lin_eq_iff (hR.P_le_normalizer (x : P).2)] at h1
    calc ((x : P) : G) * ψ v = ((x : P) : G) * ψ v * ((x : P) : G)⁻¹ * (x : P) := by group
      _ = ψ v * (x : P) := by rw [h1]
  have hker : Nat.card f.ker ≤ 64 := by
    have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hR.card_Q]; norm_num)
    rw [← hR.card_Q]
    exact Nat.card_le_card_of_injective (fun x => (⟨((x : P) : G), hmemQ x⟩ : Q))
      fun x y h => by
        have e := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext e)
  have h := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hR.card_P] at h
  by_contra hlt
  rw [not_le] at hlt
  have h1 : Nat.card f.ker * Nat.card f.range ≤ 64 * Nat.card f.range :=
    Nat.mul_le_mul_right _ hker
  have h2 : 64 * Nat.card f.range < 64 * (oBound ε / 2) :=
    Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
  omega

theorem inducesOrth_of_refl (hR : RadicalData ε L U Q P a ψ p)
    (hcent : ∀ l ∈ L, (∀ q ∈ Q, l * q = q * l) → l ∈ Q) (hLH : L ≤ H₀) {x₀ : G}
    (hx₀ : x₀ ∈ H₀) (hsq : x₀ * x₀ = 1)
    (hact : ∀ v, x₀ * ψ v * x₀⁻¹ = ψ (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v)) :
    SplitC.InducesOrth ε H₀ Q ψ := by
  have hinv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hsq
  have hfw : ∀ y ∈ Q, x₀ * y * x₀⁻¹ ∈ Q := fun y hy => by
    obtain ⟨v, rfl⟩ := hR.mem_ψ y hy
    rw [hact]
    exact hR.ψ_mem _
  have hx₀N : x₀ ∈ normalizer (Q : Set G) := mem_normalizer_iff.2 fun y => ⟨hfw y, fun hy => by
    have := hfw _ hy
    rwa [hinv, show x₀ * (x₀ * y * x₀) * x₀ = x₀ * x₀ * y * (x₀ * x₀) by group, hsq, one_mul,
      mul_one] at this⟩
  have hlin₀ : ∀ v, lin ψ x₀ v = toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v := fun v =>
    (hR.lin_eq_iff hx₀N v _).2 (hact v)
  set N := normalizer (Q : Set G)
  set φ := hR.linHom
  set K : Subgroup G := P ⊔ zpowers x₀ with hKdef
  have hKN : K ≤ N := sup_le hR.P_le_normalizer (zpowers_le.2 hx₀N)
  have hKH : K ≤ H₀ := sup_le (hR.P_le_L.trans hLH) (zpowers_le.2 hx₀)
  set I := (K.subgroupOf N).map φ
  set IP := (φ.comp (inclusion hR.P_le_normalizer)).range
  have hIPI : IP ≤ I := by
    rintro _ ⟨x, rfl⟩
    exact ⟨inclusion hR.P_le_normalizer x, mem_subgroupOf.2 (mem_sup_left x.2), rfl⟩
  have hr : φ ⟨x₀, hx₀N⟩ ∈ I :=
    ⟨⟨x₀, hx₀N⟩, mem_subgroupOf.2 (mem_sup_right (mem_zpowers x₀)), rfl⟩
  have hrIP : φ ⟨x₀, hx₀N⟩ ∉ IP := by
    rintro ⟨x, hx⟩
    have h1 := hR.dickC_colsF_lin x.2
    have h2 : lin ψ (x : G) = fun v => toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v := funext fun v => by
      have := congrArg (fun σ : Equiv.Perm V6 => σ v) hx
      change lin ψ (x : G) v = lin ψ x₀ v at this
      rw [this, hlin₀]
    rw [h2, colsF_refl_n0, dickC_refl_n0] at h1
    exact absurd h1 (by decide)
  have hIO : I ≤ orthGroup ε := by
    have hM : K ≤ ((orthGroup ε).comap φ).map N.subtype := by
      refine sup_le (fun x hx => ⟨⟨x, hR.P_le_normalizer hx⟩, ?_, rfl⟩) (zpowers_le.2
        ⟨⟨x₀, hx₀N⟩, ?_, rfl⟩)
      · exact ⟨hR.linHom_mem_linGroup _, fun v => hR.qfV_lin hx v⟩
      · exact ⟨hR.linHom_mem_linGroup _, fun v => by
          change qfV ε (lin ψ x₀ v) = qfV ε v
          rw [hlin₀, qfV_refl_n0]⟩
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨k', hk', e⟩ := hM (mem_subgroupOf.1 hk)
    have : k' = k := Subtype.ext e
    rw [← this]
    exact hk'
  have hcard2 : 2 * Nat.card IP ≤ Nat.card I := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hIPI
    have hpos : 0 < Nat.card I := Nat.card_pos
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · omega
      · exact absurd (Subgroup.eq_of_le_of_card_ge hIPI (by omega) ▸ hr) hrIP
    · calc 2 * Nat.card IP ≤ k * Nat.card IP := Nat.mul_le_mul_right _ hk2
        _ = Nat.card I := by rw [hk, mul_comm]
  have hIP : oBound ε / 2 ≤ Nat.card IP := card_range_linP_ge hR hcent
  have hO := card_orthGroup_le ε
  have heq : I = orthGroup ε := Subgroup.eq_of_le_of_card_ge hIO (by
    have : 2 * (oBound ε / 2) = oBound ε := by cases ε <;> rfl
    omega)
  intro σ hσ
  rw [← heq] at hσ
  obtain ⟨k, hk, rfl⟩ := hσ
  exact ⟨k, hKH (mem_subgroupOf.1 hk), k.2, fun v => rfl⟩

end CFSG.EvenSmallLie.OmegaEight.SplitIn
