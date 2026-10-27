module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.GroupTheory.SubnormalJoin
import CFSG.RankThree.PartTwo.Late.Uniqueness

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.AS76b (oUpperTwo)
open Subgroup

namespace SymThreeDetermined

theorem perm3_conj_inv (a t : Equiv.Perm (Fin 3)) (ha : a ^ 3 = 1) (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    t * a * t⁻¹ = a⁻¹ := by
  revert a t
  decide

theorem perm3_cube_mul (a b : Equiv.Perm (Fin 3)) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a * b) ^ 3 = 1 := by
  revert a b
  decide

theorem perm3_cube_or (x : Equiv.Perm (Fin 3)) :
    x ^ 3 = 1 ∨ (x * (Equiv.swap 0 1)⁻¹) ^ 3 = 1 := by
  revert x
  decide

variable {Y : Type} [Group Y] [Finite Y]

theorem involution_facts {T : Subgroup Y} (e : ↥T ≃* Equiv.Perm (Fin 3)) :
    ((e.symm (Equiv.swap 0 1) : ↥T) : Y) ^ 2 = 1 ∧ ((e.symm (Equiv.swap 0 1) : ↥T) : Y) ≠ 1 := by
  refine ⟨?_, ?_⟩
  · have h : (e.symm (Equiv.swap 0 1)) ^ 2 = 1 := by
      rw [← map_pow, show (Equiv.swap (0 : Fin 3) 1) ^ 2 = 1 by decide, map_one]
    simpa using congrArg Subtype.val h
  · intro h
    have h1 : e.symm (Equiv.swap 0 1) = 1 := Subtype.ext (by simpa using h)
    have := congrArg e h1
    simp only [MulEquiv.apply_symm_apply, map_one] at this
    exact absurd this (by decide)

theorem mem_oUpperTwo_of_cube {T : Subgroup Y} {x : Y} (hx : x ∈ T) (h3 : x ^ 3 = 1) :
    x ∈ oUpperTwo T := by
  refine subset_closure ⟨hx, ?_⟩
  have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h <;> rw [h] <;> decide

theorem cube_of_mem_oUpperTwo {T : Subgroup Y} (e : ↥T ≃* Equiv.Perm (Fin 3)) {x : Y}
    (hx : x ∈ oUpperTwo T) : x ∈ T ∧ x ^ 3 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxT, hodd⟩ := hx
    refine ⟨hxT, ?_⟩
    have hT6 : Nat.card T = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hdvd : orderOf (⟨x, hxT⟩ : ↥T) ∣ 6 := hT6 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    have h3 : orderOf x ∣ 3 := by
      have hco : Nat.Coprime (orderOf x) 2 := (Nat.coprime_two_left.mpr hodd).symm
      exact hco.dvd_of_dvd_mul_left (by simpa [show (6 : ℕ) = 2 * 3 by rfl, mul_comm] using hdvd)
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  | one => exact ⟨T.one_mem, one_pow 3⟩
  | mul x y _ _ hx hy =>
    refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
    have h := perm3_cube_mul (e ⟨x, hx.1⟩) (e ⟨y, hy.1⟩)
      (by rw [← map_pow, show (⟨x, hx.1⟩ : ↥T) ^ 3 = 1 from Subtype.ext (by simpa using hx.2),
        map_one])
      (by rw [← map_pow, show (⟨y, hy.1⟩ : ↥T) ^ 3 = 1 from Subtype.ext (by simpa using hy.2),
        map_one])
    rw [← map_mul, ← map_pow] at h
    have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    simpa using this
  | inv x _ hx => exact ⟨T.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem conj_eq_inv {T : Subgroup Y} (e : ↥T ≃* Equiv.Perm (Fin 3)) {t a : Y} (htT : t ∈ T)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (ha : a ∈ oUpperTwo T) : t * a * t⁻¹ = a⁻¹ := by
  obtain ⟨haT, ha3⟩ := cube_of_mem_oUpperTwo e ha
  have h := perm3_conj_inv (e ⟨a, haT⟩) (e ⟨t, htT⟩)
    (by rw [← map_pow, show (⟨a, haT⟩ : ↥T) ^ 3 = 1 from Subtype.ext (by simpa using ha3),
      map_one])
    (by rw [← map_pow, show (⟨t, htT⟩ : ↥T) ^ 2 = 1 from Subtype.ext (by simpa using ht2),
      map_one])
    (fun h1 => ht1 (by
      have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
      simpa using this))
  rw [← map_mul, ← map_inv, ← map_mul, ← map_inv] at h
  have := congrArg Subtype.val (e.injective h)
  simpa using this

theorem mem_or_mul_mem {T : Subgroup Y} (e : ↥T ≃* Equiv.Perm (Fin 3)) {x : Y} (hx : x ∈ T) :
    x ∈ oUpperTwo T ∨ x * ((e.symm (Equiv.swap 0 1) : ↥T) : Y)⁻¹ ∈ oUpperTwo T := by
  rcases perm3_cube_or (e ⟨x, hx⟩) with h | h
  · left
    refine mem_oUpperTwo_of_cube hx ?_
    rw [← map_pow] at h
    have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    simpa using this
  · right
    refine mem_oUpperTwo_of_cube (T.mul_mem hx (T.inv_mem (e.symm _).2)) ?_
    have h' : e ((⟨x, hx⟩ * (e.symm (Equiv.swap 0 1))⁻¹) ^ 3) = 1 := by
      rw [map_pow, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h
    have := congrArg Subtype.val (e.injective (h'.trans (map_one e).symm))
    simpa using this

end SymThreeDetermined

open SymThreeDetermined in
theorem eq_of_oUpperTwo_eq_symThree {Y : Type} [Group Y] [Finite Y] (hO : CFSG.pCore 2 Y = ⊥)
    {T₁ T₂ : Subgroup Y} (hs₁ : T₁.IsSubnormal) (hs₂ : T₂.IsSubnormal)
    (e₁ : ↥T₁ ≃* Equiv.Perm (Fin 3)) (e₂ : ↥T₂ ≃* Equiv.Perm (Fin 3))
    (h : oUpperTwo T₁ = oUpperTwo T₂) : T₁ = T₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t₁ : Y := ((e₁.symm (Equiv.swap 0 1) : ↥T₁) : Y) with ht₁def
  set t₂ : Y := ((e₂.symm (Equiv.swap 0 1) : ↥T₂) : Y) with ht₂def
  have ht₁T : t₁ ∈ T₁ := (e₁.symm _).2
  have ht₂T : t₂ ∈ T₂ := (e₂.symm _).2
  obtain ⟨ht₁2, ht₁1⟩ := involution_facts e₁
  obtain ⟨ht₂2, ht₂1⟩ := involution_facts e₂
  have ht₁i : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_left (by rw [← sq, ht₁2])
  have ht₂i : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_left (by rw [← sq, ht₂2])
  set A := oUpperTwo T₁ with hA
  have hAT₁ : A ≤ T₁ := oUpperTwo_le_self T₁
  have hAT₂ : A ≤ T₂ := h ▸ oUpperTwo_le_self T₂
  have hinv₁ : ∀ a ∈ A, t₁ * a * t₁⁻¹ = a⁻¹ := fun a ha => conj_eq_inv e₁ ht₁T ht₁2 ht₁1 ha
  have hinv₂ : ∀ a ∈ A, t₂ * a * t₂⁻¹ = a⁻¹ := fun a ha =>
    conj_eq_inv e₂ ht₂T ht₂2 ht₂1 (h ▸ ha)
  set s := t₁ * t₂ with hs
  have hsA : ∀ a ∈ A, s * a * s⁻¹ = a := by
    intro a ha
    have h1 := hinv₂ a ha
    have h2 := hinv₁ a⁻¹ (A.inv_mem ha)
    calc s * a * s⁻¹ = t₁ * (t₂ * a * t₂⁻¹) * t₁⁻¹ := by rw [hs]; group
      _ = a := by rw [h1, h2, inv_inv]
  have ht₁sq : t₁ * t₁ = 1 := by rw [← sq, ht₁2]
  have ht₂sq : t₂ * t₂ = 1 := by rw [← sq, ht₂2]
  have hts₁ : t₁ * s * t₁⁻¹ = s⁻¹ := by
    rw [hs, mul_inv_rev, ht₁i, ht₂i]
    calc t₁ * (t₁ * t₂) * t₁ = (t₁ * t₁) * (t₂ * t₁) := by simp only [mul_assoc]
      _ = t₂ * t₁ := by rw [ht₁sq, one_mul]
  have hts₂ : t₂ * s * t₂⁻¹ = s⁻¹ := by
    rw [hs, mul_inv_rev, ht₁i, ht₂i]
    calc t₂ * (t₁ * t₂) * t₂ = t₂ * t₁ * (t₂ * t₂) := by simp only [mul_assoc]
      _ = t₂ * t₁ := by rw [ht₂sq, mul_one]
  obtain ⟨a₂, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  set s₂ := s ^ m with hs₂def
  have hs₂pow : s₂ ^ (2 ^ a₂) = 1 := by
    rw [hs₂def, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hnorm_of : ∀ g : Y, (g * s * g⁻¹ = s ∨ g * s * g⁻¹ = s⁻¹) →
      g ∈ normalizer ((zpowers s₂ : Subgroup Y) : Set Y) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (g * s₂ * g⁻¹) = zpowers s₂
    rw [hs₂def, ← conj_pow]
    rcases hg with hg | hg
    · rw [hg]
    · rw [hg, inv_pow, zpowers_inv]
  have hAs : ∀ a ∈ A, a * s * a⁻¹ = s := by
    intro a ha
    have h1 := hsA a ha
    calc a * s * a⁻¹ = (s * a * s⁻¹) * s * a⁻¹ := by rw [h1]
      _ = s := by group
  have hle₁ : T₁ ≤ normalizer ((zpowers s₂ : Subgroup Y) : Set Y) := by
    intro x hx
    rcases mem_or_mul_mem e₁ hx with hxA | hxA
    · exact hnorm_of x (Or.inl (hAs x hxA))
    · have h1 := hnorm_of _ (Or.inl (hAs _ hxA))
      have h2 := hnorm_of t₁ (Or.inr hts₁)
      have : x = (x * t₁⁻¹) * t₁ := by group
      rw [this]
      exact mul_mem h1 h2
  have hle₂ : T₂ ≤ normalizer ((zpowers s₂ : Subgroup Y) : Set Y) := by
    intro x hx
    rcases mem_or_mul_mem e₂ hx with hxA | hxA
    · exact hnorm_of x (Or.inl (hAs x (h ▸ hxA)))
    · have h1 := hnorm_of _ (Or.inl (hAs _ (h ▸ hxA)))
      have h2 := hnorm_of t₂ (Or.inr hts₂)
      have : x = (x * t₂⁻¹) * t₂ := by group
      rw [this]
      exact mul_mem h1 h2
  have hsW : s ∈ T₁ ⊔ T₂ := mul_mem (mem_sup_left ht₁T) (mem_sup_right ht₂T)
  have hs₂W : zpowers s₂ ≤ T₁ ⊔ T₂ := (zpowers_le).mpr (pow_mem hsW m)
  have hWsn : (T₁ ⊔ T₂).IsSubnormal := CFSG.GroupTheory.isSubnormal_sup hs₁ hs₂
  have hZsn : (zpowers s₂).IsSubnormal := by
    refine IsSubnormal.step _ _ hs₂W hWsn ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (sup_le hle₁ hle₂ g.2) n).mp hn
  have hs₂one : s₂ = 1 := by
    have hP : IsPGroup 2 (zpowers s₂) := by
      rintro ⟨y, n, rfl⟩
      refine ⟨a₂, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs₂pow, one_zpow]
    have hcore := CFSG.RankThree.PartTwo.Late.pCoreOf_le_pCore_of_isSubnormal 2 hZsn
    have hself : zpowers s₂ ≤ CFSG.Open.pCoreOf 2 (zpowers s₂) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl (le_normalizer) hP
    have hmem : s₂ ∈ CFSG.Open.pCore 2 Y := hcore (hself (mem_zpowers s₂))
    have : CFSG.Open.pCore 2 Y = ⊥ := hO
    rw [this] at hmem
    exact (mem_bot).mp hmem
  have hsodd : Odd (orderOf s) := by
    have hd : orderOf s ∣ m := orderOf_dvd_of_pow_eq_one hs₂one
    exact Odd.of_dvd_nat hm hd
  have key : ∀ H : Subgroup Y, H.IsSubnormal → t₁ ∈ H → s ∈ H := by
    intro H hH
    induction hH with
    | top => exact fun _ => mem_top s
    | step H K hHK hK hN ih =>
      intro ht
      have hsK := ih (hHK ht)
      have hc : s * t₁ * s⁻¹ ∈ H := by
        have := hN.conj_mem ⟨t₁, hHK ht⟩ (mem_subgroupOf.mpr ht) ⟨s, hsK⟩
        simpa [mem_subgroupOf] using this
      have hsq : s ^ 2 ∈ H := by
        have h1 : s * t₁ * s⁻¹ * t₁⁻¹ = s ^ 2 := by
          have : t₁ * s⁻¹ * t₁⁻¹ = s := by
            rw [show t₁ * s⁻¹ * t₁⁻¹ = (t₁ * s * t₁⁻¹)⁻¹ by group, hts₁, inv_inv]
          calc s * t₁ * s⁻¹ * t₁⁻¹ = s * (t₁ * s⁻¹ * t₁⁻¹) := by group
            _ = s ^ 2 := by rw [this, sq]
        rw [← h1]
        exact H.mul_mem hc (H.inv_mem ht)
      obtain ⟨k, hk⟩ := hsodd
      have : s = (s ^ 2) ^ (k + 1) := by
        rw [← pow_mul, show 2 * (k + 1) = orderOf s + 1 by omega, pow_succ, pow_orderOf_eq_one,
          one_mul]
      rw [this]
      exact pow_mem hsq _
  have hsT₁ : s ∈ T₁ := key T₁ hs₁ ht₁T
  have ht₂T₁ : t₂ ∈ T₁ := by
    have : t₂ = t₁⁻¹ * s := by rw [hs]; group
    rw [this]
    exact T₁.mul_mem (T₁.inv_mem ht₁T) hsT₁
  have hle : T₂ ≤ T₁ := by
    intro x hx
    rcases mem_or_mul_mem e₂ hx with hxA | hxA
    · exact hAT₁ (h ▸ hxA)
    · have : x = (x * t₂⁻¹) * t₂ := by group
      rw [this]
      exact T₁.mul_mem (hAT₁ (h ▸ hxA)) ht₂T₁
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv]

@[expose] def SubnormalSUThreeTwoDetermined : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.pCore 2 Y = ⊥ → ∀ T₁ T₂ : Subgroup Y,
    T₁.IsSubnormal → T₂.IsSubnormal → IsSymThreeOrSUThreeTwo ↥T₁ → IsSymThreeOrSUThreeTwo ↥T₂ →
    IsEmpty (↥T₁ ≃* Equiv.Perm (Fin 3)) → oUpperTwo T₁ = oUpperTwo T₂ → T₁ = T₂

theorem eq_of_oUpperTwo_eq_of_shape (hD : SubnormalSUThreeTwoDetermined) {Y : Type} [Group Y]
    [Finite Y] (hO : CFSG.pCore 2 Y = ⊥) {T₁ T₂ : Subgroup Y} (hs₁ : T₁.IsSubnormal)
    (hs₂ : T₂.IsSubnormal) (hb₁ : IsSymThreeOrSUThreeTwo ↥T₁) (hb₂ : IsSymThreeOrSUThreeTwo ↥T₂)
    (h : oUpperTwo T₁ = oUpperTwo T₂) : T₁ = T₂ := by
  by_cases h₁ : Nonempty (↥T₁ ≃* Equiv.Perm (Fin 3))
  · by_cases h₂ : Nonempty (↥T₂ ≃* Equiv.Perm (Fin 3))
    · exact eq_of_oUpperTwo_eq_symThree hO hs₁ hs₂ h₁.some h₂.some h
    · exact (hD Y hO T₂ T₁ hs₂ hs₁ hb₂ hb₁ (not_nonempty_iff.mp h₂) h.symm).symm
  · exact hD Y hO T₁ T₂ hs₁ hs₂ hb₁ hb₂ (not_nonempty_iff.mp h₁) h

end CFSG.AGLEmbedding
