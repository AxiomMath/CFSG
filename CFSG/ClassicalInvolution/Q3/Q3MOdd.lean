module

public import CFSG.ClassicalInvolution.Q3.Q3MProd
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.M

open CFSG.Open CFSG.ClassicalInvolution

section Product

variable {C : Type*} [Group C]

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup C}
    (h : A ≤ Subgroup.normalizer (B : Set C)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  set M : Subgroup C := A ⊔ B with hM
  have hAM : A ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMn : M ≤ Subgroup.normalizer (B : Set C) := sup_le h Subgroup.le_normalizer
  have hBn : (B.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBM).mpr hMn
  have hsup : (A.subgroupOf M) ⊔ (B.subgroupOf M) = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAM,
      Subgroup.map_subgroupOf_eq_of_le hBM, Subgroup.map_top, Subgroup.range_subtype]
  have h1 := Subgroup.relIndex_sup_right (A.subgroupOf M) (B.subgroupOf M)
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 : (B.subgroupOf M).relIndex (A.subgroupOf M) = B.relIndex A :=
    Subgroup.relIndex_subgroupOf hAM
  rw [h2] at h1
  have h3 := (B.subgroupOf M).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, h1] at h3
  have h4 := card_eq_mul_relIndex (inf_le_right : B ⊓ A ≤ A)
  rw [Subgroup.inf_relIndex_right] at h4
  rw [inf_comm]
  calc Nat.card ↥M * Nat.card ↥(B ⊓ A)
      = (B.relIndex A * Nat.card B) * Nat.card ↥(B ⊓ A) := by rw [h3]
    _ = (Nat.card ↥(B ⊓ A) * B.relIndex A) * Nat.card B := by ring
    _ = Nat.card A * Nat.card B := by rw [h4]

end Product

section Subnormal

variable {C : Type*} [Group C]

theorem mem_normalizer_sup {A B : Subgroup C} {m : C}
    (hA : m ∈ Subgroup.normalizer (A : Set C)) (hB : m ∈ Subgroup.normalizer (B : Set C)) :
    m ∈ Subgroup.normalizer ((A ⊔ B : Subgroup C) : Set C) := by
  have key : ∀ m : C, m ∈ Subgroup.normalizer (A : Set C) →
      m ∈ Subgroup.normalizer (B : Set C) → ∀ x ∈ A ⊔ B, m * x * m⁻¹ ∈ A ⊔ B := by
    intro m hA hB x hx
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj m).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hA hB x, fun hx => ?_⟩
  have := key m⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hx
  simpa [mul_assoc] using this

theorem isSubnormal_sup_of_le_normalizer {L K T : Subgroup C} (hL : IsSubnormal L K)
    (hK : K ≤ Subgroup.normalizer (T : Set C)) : IsSubnormal (L ⊔ T) (K ⊔ T) := by
  induction hL with
  | refl H => exact IsSubnormal.refl _
  | @step H M K hHM hN hMK ih =>
    have hMK' : M ≤ K := isSubnormal_le hMK
    have hMT : M ≤ Subgroup.normalizer (T : Set C) := hMK'.trans hK
    have hMH : M ≤ Subgroup.normalizer (H : Set C) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hN
    have hle : H ⊔ T ≤ M ⊔ T := sup_le_sup_right hHM T
    refine IsSubnormal.step hle ?_ (ih hK)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    refine sup_le (fun m hm => mem_normalizer_sup (hMH hm) (hMT hm)) ?_
    exact le_sup_right.trans Subgroup.le_normalizer

end Subnormal

section OddCore

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem oddCoreIn_top_eq_bot (hO : classicalInvolutionOddCore X = ⊥) :
    Balance.oddCoreIn (⊤ : Subgroup X) = ⊥ := by
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant
    (Subgroup.topEquiv (G := X)).symm
  have h2 : componentClassificationOddCore X = ⊥ := hO
  rw [h2, Subgroup.map_bot] at h1
  unfold Balance.oddCoreIn
  rw [← h1, Subgroup.map_bot]

theorem eq_bot_of_isSubnormal_odd (hO : classicalInvolutionOddCore X = ⊥) {S : Subgroup X}
    (hS : IsSubnormal S ⊤) (hodd : Odd (Nat.card S)) : S = ⊥ :=
  le_bot_iff.mp
    ((Balance.le_oddCoreIn_of_isSubnormal hS hodd).trans (oddCoreIn_top_eq_bot hO).le)

theorem eq_of_odd_index_central (hO : classicalInvolutionOddCore X = ⊥) {K Z : Subgroup X}
    (hK : IsSubnormal K ⊤) (hZK : Z ≤ K) (hcen : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)
    (h2 : ∀ z ∈ Z, ∃ j : ℕ, z ^ (2 ^ j) = 1) (hodd : Odd (Z.relIndex K)) : K ≤ Z := by
  set N' : Subgroup K := Z.subgroupOf K with hN'
  have hcenN : ∀ n ∈ N', ∀ g : K, g * n = n * g := fun n hn g =>
    Subtype.ext (hcen g g.2 n (Subgroup.mem_subgroupOf.mp hn))
  have hNn : N'.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by rw [hcenN n hn g]; group
    rw [this]; exact hn⟩
  have hZ2 : IsPGroup 2 Z := fun z => by
    obtain ⟨j, hj⟩ := h2 z z.2
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
  have hNcard : Nat.card N' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hNcard, hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  obtain ⟨H, hcomp⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHn : H.Normal := ⟨fun h hh g => by
    have hg : g ∈ N' ⊔ H := by rw [hcomp.sup_eq_top]; exact Subgroup.mem_top g
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have : a * b * h * (a * b)⁻¹ = b * h * b⁻¹ := by
      have e : a * b * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ := by group
      rw [e, ← hcenN a ha (b * h * b⁻¹)]
      group
    rw [this]
    exact H.mul_mem (H.mul_mem hb hh) (H.inv_mem hb)⟩
  have hHcard : N'.index = Nat.card H := hcomp.symm.index_eq_card
  have hH1 : H.map K.subtype = ⊥ := by
    apply eq_bot_of_isSubnormal_odd hO
    · have hsn : IsSubnormal (H.map K.subtype) K := by
        refine isSubnormal_of_normal_subgroupOf (Subgroup.map_subtype_le H) ?_
        have hcm : (H.map K.subtype).subgroupOf K = H :=
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective H
        rw [hcm]
        exact hHn
      exact isSubnormal_trans hsn hK
    · rw [Subgroup.card_map_of_injective K.subtype_injective, ← hHcard]
      exact hodd
  have hHbot : H = ⊥ := (Subgroup.map_eq_bot_iff_of_injective H K.subtype_injective).mp hH1
  have hidx : N'.index = 1 := by rw [hHcard, hHbot, Subgroup.card_bot]
  have hNtop : N' = ⊤ := Subgroup.index_eq_one.mp hidx
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ N' := by rw [hNtop]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end OddCore

end CFSG.ClassicalInvolution.Q3.M
