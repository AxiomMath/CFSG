module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56

theorem card_le_of_rank1_data {G : Type*} [Group G] [Finite G] {Q U D Z : Subgroup G} {x : G}
    {q : ℕ} (hQ : Q = U ⊔ D) (hDc : ∀ u ∈ U, ∀ d ∈ D, u * d = d * u) (hUD : U ⊓ D = Z)
    (hUZ : Nat.card U = Nat.card Z * q ^ 2) (hDD : D ⊓ conjSubgroup D x = ⊥)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hD1 : D ≤ conjSubgroup Q x)
    (hD2 : conjSubgroup D x ≤ Q) (hidx : (Q ⊓ conjSubgroup Q x).relIndex Q = q) :
    Nat.card D ≤ q := by
  have hDQ : D ≤ Q := hQ ▸ le_sup_right
  have h1 : Nat.card Q * Nat.card Z = Nat.card U * Nat.card D := by
    have := C5.card_sup_mul_card_inf_of_le_normalizer (A := U) (B := D)
      (C5.le_normalizer_of_commute hDc)
    rw [← hQ, hUD] at this
    exact this
  have h2 : Nat.card Q = Nat.card (Q ⊓ conjSubgroup Q x : Subgroup G) * q := by
    rw [← hidx]
    exact C5.card_eq_card_mul_relIndex inf_le_left
  have hcommDDx : D ≤ normalizer ((conjSubgroup D x : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute fun a ha b hb => hQab a (hDQ ha) b (hD2 hb)
  have h3 : Nat.card (D ⊔ conjSubgroup D x : Subgroup G) = Nat.card D * Nat.card D := by
    have := C5.card_sup_mul_card_inf_of_le_normalizer hcommDDx
    rw [hDD, C5.card_conjSubgroup] at this
    simpa using this
  have h4 : D ⊔ conjSubgroup D x ≤ Q ⊓ conjSubgroup Q x :=
    sup_le (le_inf hDQ hD1) (le_inf hD2 (C5.conjSubgroup_mono hDQ x))
  have h5 : Nat.card (D ⊔ conjSubgroup D x : Subgroup G) ≤
      Nat.card (Q ⊓ conjSubgroup Q x : Subgroup G) := Subgroup.card_le_of_le h4
  have hz : 0 < Nat.card Z := Nat.card_pos
  have hq : 0 < q := by
    rw [← hidx]
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := (Q ⊓ conjSubgroup Q x).subgroupOf Q))
  have hd : 0 < Nat.card D := Nat.card_pos
  have hQc : Nat.card Q = q ^ 2 * Nat.card D := by
    have : Nat.card Q * Nat.card Z = (q ^ 2 * Nat.card D) * Nat.card Z := by
      rw [h1, hUZ]; ring
    exact Nat.eq_of_mul_eq_mul_right hz this
  have hm : Nat.card (Q ⊓ conjSubgroup Q x : Subgroup G) = q * Nat.card D := by
    have : Nat.card (Q ⊓ conjSubgroup Q x : Subgroup G) * q = (q * Nat.card D) * q := by
      rw [← h2, hQc]; ring
    exact Nat.eq_of_mul_eq_mul_right hq this
  rw [h3, hm] at h5
  exact Nat.le_of_mul_le_mul_right h5 hd

section

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem relIndex_blockZ_isAltType3 (h : IsAltType L 3) :
    (blockU L ⊓ centralizer (L : Set G)).relIndex (blockU L) = 4 := by
  obtain ⟨α, -, -, β, hβs, hβk, -⟩ := h
  have e : (blockU L ⊓ centralizer (L : Set G)).relIndex (blockU L) = β.ker.index := by
    rw [hβk]
    rfl
  have h1 : Nat.card (↥(blockU L) ⧸ β.ker) = Nat.card (Multiplicative (evenWeight 3)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv
  have h4 : Nat.card (Multiplicative (evenWeight 3)) = 4 := by
    rw [Nat.card_congr (Multiplicative.ofAdd (α := evenWeight 3)).symm]
    have h : Nat.card (evenWeight 3) = Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} := by
      apply Nat.card_congr
      exact (Equiv.subtypeEquivRight (fun x => by simp [evenWeight, AddMonoidHom.mem_ker]))
    rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  rw [e, Subgroup.index, h1, h4]

theorem c61_single_bound (hN : NaturalModuleStructure)
    (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) :
    (IsAltType L 3 → Nat.card (blockD S L) ≤ 2 ^ 1) ∧
      ∀ n : ℕ, 1 < n → IsLin2Type L n → Nat.card (blockD S L) ≤ 2 ^ n := by
  have hLsh := isShort hcs
  obtain ⟨M₀, hSM, hMT, h2⟩ := exists_index_two hcs
  obtain ⟨q, W, hq2, hidxQ, hidxW, hZ, hcent, hcomm, hmain, hUeq⟩ :=
    single_rank1 hN hcs hj hL hSM hMT h2
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have hxinvS : x₀⁻¹ ∉ S := fun h => hx₀S (by simpa using inv_mem h)
  obtain ⟨hidx, o1, -, o3, -, o5, -, -, o8, -, -, o11⟩ := hmain x₀ hx₀ hx₀S
  obtain ⟨-, -, -, -, -, -, -, -, o8', -, -, -⟩ := hmain x₀⁻¹ (inv_mem hx₀) hxinvS
  set Q := baum S ⊓ centralizer (blockU L : Set G) with hQdef
  set D := Q ⊓ centralizer (L : Set G) with hDdef
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hUQ : blockU L ≤ Q := by
    rw [o1]
    exact le_sup_left
  have hD : Nat.card (blockD S L) ≤ q := by
    have hblockD : blockD S L = D := by
      show S ⊓ centralizer ((conjJoin S L : Subgroup G) : Set G) = _
      rw [hj]
      exact o11
    rw [hblockD]
    have hUD : blockU L ⊓ D = blockZ L := by
      refine le_antisymm (fun g hg => ⟨hg.1, hg.2.2⟩) fun g hg => ⟨hg.1, hUQ hg.1, hg.2⟩
    have hUZ : Nat.card (blockU L) = Nat.card (blockZ L) * q ^ 2 := by
      have := C5.card_eq_card_mul_relIndex (inf_le_left : blockU L ⊓ centralizer (L : Set G) ≤
        blockU L)
      rw [hZ] at this
      exact this
    have hD2 : conjSubgroup D x₀ ≤ Q := by
      have hDle : D ≤ conjSubgroup Q x₀⁻¹ := by
        rw [o8']
        exact le_sup_left
      have := C5.conjSubgroup_mono hDle x₀
      rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
    exact card_le_of_rank1_data (x := x₀) o1 (fun u hu d hd =>
      Subgroup.mem_centralizer_iff.mp hd.2 u (hUL hu)) hUD hUZ o3 o5.1
      (by rw [o8]; exact le_sup_left) hD2 hidx
  refine ⟨fun h3 => ?_, fun n hn hlin => ?_⟩
  · have h4 := relIndex_blockZ_isAltType3 (G := G) (L := L) h3
    have hq : q = 2 := by
      have : q ^ 2 = 2 ^ 2 := hZ.symm.trans (h4.trans (by norm_num))
      exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) this
    rw [hq] at hD
    exact hD
  · have h1 := relIndex_blockZ_isLin2Type (G := G) (L := L) hlin
    have hq : q = 2 ^ n :=
      Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hZ.symm.trans h1 :
        (fun m : ℕ => m ^ 2) q = (fun m : ℕ => m ^ 2) (2 ^ n))
    rw [hq] at hD
    exact hD

theorem c61SingleTail (hN : NaturalModuleStructure)
    (h : C61SingleAlternatives) : C61SingleTail := by
  intro G _ _ T M H S L hcs hj hL h5
  exact ⟨c61_single_bound hN hcs hj hL, h G T M H S L hcs hj hL h5⟩

end

end C56

end CFSG.QuasithinUnique
