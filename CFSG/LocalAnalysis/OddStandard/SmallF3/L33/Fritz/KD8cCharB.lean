module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cCharA

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c
open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace Conf

namespace T2

namespace Lift

variable {K : Conf S T₁} {T : K.T2} (W : T.Lift)

@[expose] noncomputable def cX : Fin 3 → X := ![K.ι MC.w₂, W.Q, K.ι MC.w₂ * W.Q]

theorem cX_mem (c : Fin 3) : W.cX c ∈ T.P := by
  have hW := T.S1_le K.w₂_mem_S1
  match c with
  | 0 => exact hW
  | 1 => exact W.Q_mem
  | 2 => exact mul_mem hW W.Q_mem

theorem cases4 {g : X} (hg : g ∈ T.P) : g ∈ K.R1 ∨ ∃ c : Fin 3, (W.cX c)⁻¹ * g ∈ K.R1 := by
  have hQN := K.normR1_of_mem (inv_mem (T.le_NR W.Q_mem))
  rcases W.cases g hg with h | h
  · rcases K.mem_S1_cases h with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨0, h'⟩
  · rcases K.mem_S1_cases h with h' | h'
    · refine Or.inr ⟨1, ?_⟩
      have := hQN _ h'
      rw [show W.Q⁻¹ * (g * W.Q⁻¹) * W.Q⁻¹⁻¹ = W.Q⁻¹ * g by group] at this
      exact this
    · refine Or.inr ⟨2, ?_⟩
      have := hQN _ h'
      rw [show W.Q⁻¹ * ((K.ι MC.w₂)⁻¹ * (g * W.Q⁻¹)) * W.Q⁻¹⁻¹ =
        (K.ι MC.w₂ * W.Q)⁻¹ * g by group] at this
      exact this

theorem comm_cX (r : MC) (c : Fin 3) :
    K.ι r * W.cX c * (K.ι r)⁻¹ * (W.cX c)⁻¹ = K.ι (fc W.j c r) := by
  match c with
  | 0 => simp [cX, fc, map_mul, map_inv]
  | 1 =>
    rw [show K.ι r * W.cX 1 * (K.ι r)⁻¹ * (W.cX 1)⁻¹ = K.ι r * (W.Q * K.ι r⁻¹ * W.Q⁻¹) by
      simp [cX, map_inv, mul_assoc], W.hQ]
    simp [fc, map_mul]
  | 2 =>
    rw [show K.ι r * W.cX 2 * (K.ι r)⁻¹ * (W.cX 2)⁻¹ =
      K.ι r * K.ι MC.w₂ * (W.Q * K.ι r⁻¹ * W.Q⁻¹) * (K.ι MC.w₂)⁻¹ by
      simp [cX, map_inv, mul_assoc], W.hQ]
    simp [fc, map_mul, map_inv, mul_assoc]

@[expose] noncomputable def Mc (c : Fin 3) : Set X :=
  K.ι '' ↑(Finset.univ.filter fun r : MC => inR1 r = true ∧ inZ (fc W.j c r) = true)

theorem ncard_Mc (c : Fin 3) : (W.Mc c).ncard ≤ 32 := by
  rw [Mc, Set.ncard_image_of_injective _ K.ι_injective, Set.ncard_coe_finset]
  exact card_M W.j W.hj3 W.hj4 c

theorem mem_Mc {b : X} (hb : b ∈ K.R1) {c : Fin 3} (hc : b * W.cX c * b⁻¹ * (W.cX c)⁻¹ ∈ K.Zx) :
    b ∈ W.Mc c := by
  obtain ⟨r, hr, rfl⟩ := K.mem_R1.mp hb
  refine ⟨r, ?_, rfl⟩
  rw [Finset.mem_coe, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hr, ?_⟩
  rw [W.comm_cX, K.mem_Zx_iff] at hc
  exact hc

include W in
theorem R1_char {y : X} (hy : y ∈ normalizer (T.P : Set X)) : y ∈ K.NR := by
  classical
  set A := K.R1.map (MulAut.conj y).toMonoidHom with hA
  suffices hAR : A = K.R1 from Sec7.mem_normalizer_of_map_eq hAR
  by_contra hne
  have hAP : A ≤ T.P := by
    rintro _ ⟨r, hr, rfl⟩
    exact (mem_normalizer_iff.mp hy r).mp (T.R1_le_P hr)
  have hAcard : Nat.card A = 128 := by
    rw [hA, card_map_of_injective (MulAut.conj y).injective, K.card_R1]
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K.Zx := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := W.conj_Zx' hy (K.comm_R1' ha hb)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert this using 1
    group
  have hnle : ¬ A ≤ K.R1 := fun h => hne (eq_of_le_of_card_ge h (by rw [hAcard, K.card_R1]))
  obtain ⟨a, haA, haR⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨c, hc⟩ := (W.cases4 (hAP haA)).resolve_left haR
  have hBM : ((A ⊓ K.R1 : Subgroup X) : Set X) ⊆ W.Mc c := fun b hb =>
    W.mem_Mc hb.2 ((T.comm_coset_iff hb.2 (W.cX_mem c) hc).mp (hAab b hb.1 a haA))
  have h4 : Nat.card A ≤ 4 * Nat.card (A ⊓ K.R1 : Subgroup X) := by
    refine card_le_mul_of_cosets ![1, W.cX 0, W.cX 1, W.cX 2] fun g hg => ?_
    rcases W.cases4 (hAP hg) with h | ⟨c', h⟩
    · exact ⟨0, by simpa using h⟩
    · match c' with
      | 0 => exact ⟨1, h⟩
      | 1 => exact ⟨2, h⟩
      | 2 => exact ⟨3, h⟩
  have hBc : Nat.card (A ⊓ K.R1 : Subgroup X) = ((A ⊓ K.R1 : Subgroup X) : Set X).ncard :=
    (Nat.card_coe_set_eq _).symm
  have hfin : (W.Mc c).Finite := Set.toFinite _
  have hBeq : ((A ⊓ K.R1 : Subgroup X) : Set X) = W.Mc c :=
    Set.eq_of_subset_of_ncard_le hBM (by have := W.ncard_Mc c; omega) hfin
  have h2 : Nat.card A ≤ 2 * Nat.card (A ⊓ K.R1 : Subgroup X) := by
    refine card_le_mul_of_cosets ![1, W.cX c] fun g hg => ?_
    rcases W.cases4 (hAP hg) with h | ⟨c', h⟩
    · exact ⟨0, by simpa using h⟩
    · by_cases hcc : c = c'
      · exact ⟨1, by rw [hcc]; exact h⟩
      · exfalso
        obtain ⟨r, hr, hrc, hrc'⟩ := sep_M W.j W.hj3 W.hj4 c c' hcc
        have hrM : K.ι r ∈ W.Mc c := ⟨r, by simp [hr, hrc], rfl⟩
        rw [← hBeq] at hrM
        have := (T.comm_coset_iff hrM.2 (W.cX_mem c') h).mp (hAab _ hrM.1 g hg)
        rw [W.comm_cX, K.mem_Zx_iff, hrc'] at this
        exact absurd this (by decide)
  have := W.ncard_Mc c
  rw [← hBeq, ← hBc] at this
  omega

include W in
theorem maximal_X {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hle : T.P ≤ Q) : Q = T.P := by
  by_contra hne
  obtain ⟨g, hgQ, hgN, hgP⟩ : ∃ g ∈ Q, g ∈ normalizer (T.P : Set X) ∧ g ∉ T.P := by
    set I := T.P.subgroupOf Q with hI
    have hIne : I ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm (fun x hx => ?_) hle
      have : (⟨x, hx⟩ : Q) ∈ I := by rw [htop]; trivial
      exact this
    have hnil : Group.IsNilpotent Q := hQ.isNilpotent
    have hlt : I < normalizer (I : Set Q) :=
      Group.normalizerCondition_of_isNilpotent I (lt_of_le_of_ne le_top hIne)
    obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨x, x.2, ?_, fun h => hxI h⟩
    have hxsub : x ∈ (normalizer (T.P : Set X)).subgroupOf Q := by
      rw [subgroupOf_normalizer_eq hle]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  have hmax := T.maximal (T.P ⊔ zpowers g) (hQ.to_le (sup_le hle (zpowers_le.mpr hgQ)))
    le_sup_left (sup_le T.le_NR (zpowers_le.mpr (W.R1_char hgN)))
  exact hgP (hmax ▸ mem_sup_right (mem_zpowers g))

include W in
@[expose] noncomputable def sylow : Sylow 2 X where
  toSubgroup := T.P
  isPGroup' := T.isPGroup
  is_maximal' hQ hle := W.maximal_X hQ hle

end Lift

end T2

end Conf

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
