module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreNonabBase
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def ModFix (Y : Type) [Group Y] (a : Y) : Prop :=
  ∀ (I : Type) [Group I] [Finite I], (∀ x y : I, x * y = y * x) → Nontrivial I →
    (∀ x : I, x * x = 1) → ∀ ρ : Y →* MulAut I, ∃ x : I, x ≠ 1 ∧ ρ a x = x

section Ind

variable {Y : Type} [Group Y] {a : Y}

theorem ActInv.sup {I : Type} [Group I] {ρ : Y →* MulAut I} {J K : Subgroup I} (hJ : ActInv ρ J)
    (hK : ActInv ρ K) : ActInv ρ (J ⊔ K) := by
  intro y x hx
  have : (J ⊔ K).map (ρ y).toMonoidHom ≤ J ⊔ K := by
    rw [Subgroup.map_sup, (hJ.map_eq y), (hK.map_eq y)]
  exact this ⟨x, hx, rfl⟩

theorem abel_base (hmod : ModFix Y a) {I : Type} [Group I] [Finite I]
    (hcomm : ∀ x y : I, x * y = y * x) (h2 : 2 ∣ Nat.card I) (ρ : Y →* MulAut I)
    (hmin : ∀ K : Subgroup I, K.Normal → ActInv ρ K → K = ⊥ ∨ K = ⊤)
    (J : Subgroup I) (hJ : ActInv ρ J) (hC : ∀ x : I, ρ a x = x → x ∈ J) : J = ⊤ := by
  have hnorm : ∀ K : Subgroup I, K.Normal := fun K =>
    ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]; exact hn⟩
  let Ω : Subgroup I :=
    { carrier := {x | x * x = 1}
      mul_mem' := fun {x y} hx hy => by
        change x * x = 1 at hx
        change y * y = 1 at hy
        change (x * y) * (x * y) = 1
        calc (x * y) * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hcomm y x]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx, hy, one_mul]
      one_mem' := mul_one 1
      inv_mem' := fun {x} hx => by
        change x * x = 1 at hx
        change x⁻¹ * x⁻¹ = 1
        rw [← mul_inv_rev, hx, inv_one] }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hx1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx; omega
  have hΩne : Ω ≠ ⊥ := by
    intro h
    have : x ∈ Ω := hxx
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this
  have hΩinv : ActInv ρ Ω := by
    intro y z hz
    change ρ y z * ρ y z = 1
    rw [← map_mul]
    have : z * z = 1 := hz
    rw [this, map_one]
  have hΩtop : Ω = ⊤ := (hmin Ω (hnorm Ω) hΩinv).resolve_left hΩne
  have hsq : ∀ z : I, z * z = 1 := fun z => by
    have : z ∈ Ω := by rw [hΩtop]; trivial
    exact this
  haveI : Nontrivial I := ⟨⟨x, 1, hx1⟩⟩
  obtain ⟨v, hv1, hv⟩ := hmod I hcomm inferInstance hsq ρ
  have hJne : J ≠ ⊥ := by
    intro h
    have := hC v hv
    rw [h, Subgroup.mem_bot] at this
    exact hv1 this
  exact (hmin J (hnorm J) hJ).resolve_left hJne

theorem core_odd (hCat : CFSG.AGLEmbedding.CatalogOuterSolvable) [Finite Y]
    (hY : IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y)) (ha : orderOf a = 3) (hmod : ModFix Y a) :
    ∀ (n : ℕ) (I : Type) [Group I] [Finite I], Nat.card I = n → CFSG.Open.IsKGroup I →
      ¬ 3 ∣ n → ∀ (ρ : Y →* MulAut I) (J : Subgroup I), ActInv ρ J →
        (∀ x : I, ρ a x = x → x ∈ J) → ¬ 2 ∣ J.index := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I _ _ hn hK h3 ρ J hJ hC
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  by_cases h2 : 2 ∣ Nat.card I
  swap
  · intro hd
    exact h2 (hd.trans (Subgroup.index_dvd_card J))
  by_cases hproper : ∃ K : Subgroup I, K.Normal ∧ ActInv ρ K ∧ K ≠ ⊥ ∧ K ≠ ⊤
  · obtain ⟨K, hKn, hKinv, hKbot, hKtop⟩ := hproper
    have hKdvd : Nat.card K ∣ Nat.card I := Subgroup.card_subgroup_dvd_card K
    have hKcard : Nat.card K < n := by
      rw [← hn]
      refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hKdvd) fun h => hKtop ?_
      exact (Subgroup.card_eq_iff_eq_top K).1 h
    have hK2 : 2 ≤ Nat.card K := by
      have h1 : Nat.card K ≠ 1 := fun h => hKbot (Subgroup.card_eq_one.1 h)
      have := Nat.card_pos (α := K)
      omega
    have hQcard : Nat.card (I ⧸ K) < n := by
      have e : Nat.card (I ⧸ K) * Nat.card K = Nat.card I := Subgroup.index_mul_card K
      have hpos : 0 < Nat.card (I ⧸ K) := Nat.card_pos
      rw [← hn, ← e]
      nlinarith
    have h3K : ¬ 3 ∣ Nat.card K := fun h => h3 (hn ▸ h.trans hKdvd)
    have h3Q : ¬ 3 ∣ Nat.card (I ⧸ K) := fun h =>
      h3 (hn ▸ h.trans (Subgroup.index_dvd_card K))
    have hsub : ¬ 2 ∣ J.relIndex K := by
      have := ih (Nat.card K) hKcard K rfl (CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hK K)
        h3K (actSub ρ K hKinv) (J.subgroupOf K)
        (fun y x hx => by
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          have := hJ y _ hx
          exact this)
        (fun x hx => by
          rw [Subgroup.mem_subgroupOf]
          apply hC
          exact congrArg Subtype.val hx)
      exact this
    have hquot : ¬ 2 ∣ ((J ⊔ K).map (QuotientGroup.mk' K)).index := by
      refine ih (Nat.card (I ⧸ K)) hQcard (I ⧸ K) rfl
        (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hK K) h3Q (actQuot ρ K hKinv)
        ((J ⊔ K).map (QuotientGroup.mk' K)) ?_ ?_
      · rintro y _ ⟨x, hx, rfl⟩
        exact ⟨ρ y x, (hJ.sup hKinv) y x hx, rfl⟩
      · intro x hx
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨x', hx'1, hx'2⟩ := exists_fixed_of_mk_fixed hKinv ha3 h3K x hx
        exact ⟨x', (le_sup_left : J ≤ J ⊔ K) (hC x' hx'2), hx'1⟩
    exact not_two_dvd_index_of_sub_quot J K hsub hquot
  · have hmin : ∀ K : Subgroup I, K.Normal → ActInv ρ K → K = ⊥ ∨ K = ⊤ := by
      intro K hKn hKinv
      by_contra h
      push Not at h
      exact hproper ⟨K, hKn, hKinv, h.1, h.2⟩
    by_cases hab : ∀ x y : I, x * y = y * x
    · have := abel_base hmod hab h2 ρ hmin J hJ hC
      rw [this, Subgroup.index_top]
      omega
    · push Not at hab
      have := nonab_base hCat hY ha hK (hn ▸ h3) ρ hab hmin J hJ hC
      rw [this, Subgroup.index_top]
      omega

end Ind

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
