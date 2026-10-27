module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.ZStarForm
public import CFSG.ClassicalInvolution.LBalance.Glauberman.ConjTools

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open SemidirectProduct CFSG.ABGLocalTools

instance instFiniteSemidirectProduct {N H : Type*} [Group N] [Group H] [Finite N] [Finite H]
    {φ : H →* MulAut N} : Finite (N ⋊[φ] H) :=
  Finite.of_equiv (N × H) SemidirectProduct.equivProd.symm

section Setup

variable {G : Type*} [Group G] (S : Subgroup G) (A : Subgroup (MulAut G))

abbrev AutExt := G ⋊[A.subtype] A

@[expose] def hSub (B : Subgroup A) : Subgroup (AutExt A) := B.comap rightHom

@[expose] def tSub (hA : ∀ α ∈ A, ∀ s ∈ S, α s = s) (B : Subgroup A) : Subgroup (AutExt A) where
  carrier := {q | q.left ∈ S ∧ q.right ∈ B}
  one_mem' := ⟨S.one_mem, B.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · rw [mul_left]
      have : (A.subtype a.right) b.left = b.left := hA _ a.right.2 _ hb1
      rw [this]
      exact S.mul_mem ha1 hb1
    · rw [mul_right]
      exact B.mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · rw [inv_left]
      have : (A.subtype a.right⁻¹) a.left⁻¹ = a.left⁻¹ := hA _ (a.right⁻¹).2 _ (S.inv_mem ha1)
      rw [this]
      exact S.inv_mem ha1
    · rw [inv_right]
      exact B.inv_mem ha2

variable {S A}

theorem mem_hSub {B : Subgroup A} {q : AutExt A} : q ∈ hSub A B ↔ q.right ∈ B := Iff.rfl

theorem mem_tSub {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} {B : Subgroup A} {q : AutExt A} :
    q ∈ tSub S A hA B ↔ q.left ∈ S ∧ q.right ∈ B := Iff.rfl

theorem tSub_le_hSub {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} (B : Subgroup A) :
    tSub S A hA B ≤ hSub A B := fun _ hq => hq.2

theorem inr_mul_inl (a : A) (g : G) :
    (inr a : AutExt A) * inl g = inl ((a : MulAut G) g) * inr a := by
  have h := inl_aut (φ := A.subtype) a g
  have h2 : (inl ((A.subtype a) g) : AutExt A) * inr a = inr a * inl g := by
    rw [h, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  exact h2.symm

theorem inr_comm_inl {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} (a : A) {s : G} (hs : s ∈ S) :
    (inr a : AutExt A) * inl s = inl s * inr a := by
  rw [inr_mul_inl, hA _ a.2 _ hs]

theorem inl_inr_decomp (q : AutExt A) : q = inl q.left * inr q.right :=
  (inl_left_mul_inr_right q).symm

theorem card_hSub [Finite G] (B : Subgroup A) :
    Nat.card (hSub A B) = Nat.card G * Nat.card B := by
  have : Nat.card (hSub A B) = Nat.card (G × B) := Nat.card_congr
    { toFun := fun q => (q.1.left, ⟨q.1.right, q.2⟩)
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun q => rfl
      right_inv := fun x => rfl }
  rw [this, Nat.card_prod]

theorem card_tSub [Finite G] {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} (B : Subgroup A) :
    Nat.card (tSub S A hA B) = Nat.card S * Nat.card B := by
  have : Nat.card (tSub S A hA B) = Nat.card (S × B) := Nat.card_congr
    { toFun := fun q => (⟨q.1.left, q.2.1⟩, ⟨q.1.right, q.2.2⟩)
      invFun := fun x => ⟨⟨x.1.1, x.2.1⟩, x.1.2, x.2.2⟩
      left_inv := fun q => rfl
      right_inv := fun x => rfl }
  rw [this, Nat.card_prod]

theorem isSylowOf_tSub [Finite G] {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} (hSp : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) {B : Subgroup A} (hB : IsPGroup 2 B) :
    IsSylowOf 2 (tSub S A hA B) (hSub A B) := by
  rw [isSylowOf_iff]
  refine ⟨tSub_le_hSub B, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hSp
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hB
    exact IsPGroup.iff_card.2 ⟨a + b, by rw [card_tSub, ha, hb, pow_add]⟩
  · have h1 := Subgroup.relIndex_mul_card (tSub S A hA B) (hSub A B)
    rw [inf_eq_left.2 (tSub_le_hSub B), card_tSub, card_hSub] at h1
    have h2 : Nat.card S * S.index = Nat.card G := Subgroup.card_mul_index S
    have hpos : 0 < Nat.card S * Nat.card B := Nat.mul_pos Nat.card_pos Nat.card_pos
    have h3 : (tSub S A hA B).relIndex (hSub A B) = S.index := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, ← h2]
      ring
    rw [h3]
    exact hSi

end Setup

section ZStarStep

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {A : Subgroup (MulAut G)}

omit [Finite G] in
theorem conj_inl_inr_inl (x : G) (τ : A) :
    (inl x : AutExt A) * inr τ * (inl x)⁻¹ * (inr τ)⁻¹ = inl (x * (τ : MulAut G) x⁻¹) := by
  have h := inl_aut (φ := A.subtype) τ x⁻¹
  have h2 : (inr τ : AutExt A) * inl x⁻¹ * (inr τ)⁻¹ = inl ((τ : MulAut G) x⁻¹) := by
    rw [← map_inv]
    exact h.symm
  calc (inl x : AutExt A) * inr τ * (inl x)⁻¹ * (inr τ)⁻¹
      = inl x * ((inr τ : AutExt A) * inl x⁻¹ * (inr τ)⁻¹) := by rw [← map_inv]; group
    _ = inl (x * (τ : MulAut G) x⁻¹) := by rw [h2, ← map_mul]

theorem exists_conj_not_normalizer
    (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hA : ∀ α ∈ A, ∀ s ∈ S, α s = s)
    {B : Subgroup A} (hB : IsPGroup 2 B) {τ : A} (hτB : τ ∈ B) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) :
    ∃ g ∈ hSub A B, cj g (Subgroup.zpowers (inr τ : AutExt A)) ≤ tSub S A hA B ∧
      g ∉ Subgroup.normalizer (Subgroup.zpowers (inr τ : AutExt A) : Set (AutExt A)) := by
  by_contra hcon
  push Not at hcon
  set H := hSub A B with hH
  set T := tSub S A hA B with hT
  set τ' : AutExt A := inr τ with hτ'
  set P := Subgroup.zpowers τ' with hP
  have hTH : IsSylowOf 2 T H := isSylowOf_tSub hSp hSi hB
  have hτ'T : τ' ∈ T := ⟨by simp [hτ'], by simpa [hτ'] using hτB⟩
  have hτ'1 : τ' ≠ 1 := fun h => hτ1 (inr_injective (h.trans (map_one inr).symm))
  have hτ'2 : τ' * τ' = 1 := by rw [hτ', ← map_mul, hτ2, map_one]
  have hsq : τ' ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hτ'2]
  have hiso : ∀ g ∈ H, g⁻¹ * τ' * g ∈ T → g⁻¹ * τ' * g = τ' := by
    intro g hg hgT
    have hcj : cj g P ≤ T := by
      intro y hy
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (mem_cj.1 hy)
      have e : (g⁻¹ * τ' * g) ^ i = g⁻¹ * τ' ^ i * g := by
        have := conj_zpow (a := g⁻¹) (b := τ') (i := i)
        simpa using this
      have : y = (g⁻¹ * τ' * g) ^ i := by
        rw [e, hi]
        group
      rw [this]
      exact T.zpow_mem hgT i
    have hgN := hcon g hg hcj
    have h1 : g⁻¹ * τ' * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgN) τ').1 (Subgroup.mem_zpowers τ')
      simpa using this
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h1
    have hmod : τ' ^ i = τ' ^ (i % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod i 2]
      rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one i with h0 | h0
    · exfalso
      rw [hmod, h0, zpow_zero] at hi
      apply hτ'1
      have := congrArg (fun x => g * x * g⁻¹) hi
      simpa [mul_assoc] using this.symm
    · rw [hmod, h0, zpow_one] at hi
      exact hi.symm
  obtain ⟨N, hNH, hNn, hNodd, hNc⟩ :=
    exists_oddNormal_of_isolated_in_sylow H T hTH τ' hτ'T hτ'1 hτ'2 hiso
  have hinlH : ∀ y : G, (inl y : AutExt A) ∈ H := fun y => by
    show (inl y : AutExt A).right ∈ B
    rw [right_inl]
    exact B.one_mem
  set NG : Subgroup G := N.comap inl with hNG
  have hNGn : NG.Normal := by
    refine ⟨fun n hn y => ?_⟩
    have := (Subgroup.normal_subgroupOf_iff hNH).1 hNn (inl n) (inl y) hn (hinlH y)
    simpa [hNG, map_mul, map_inv] using this
  have hNGodd : Odd (Nat.card NG) := by
    have hle : NG.map inl ≤ N := by
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective inl_injective] at h1
    exact Odd.of_dvd_nat hNodd h1
  have hNG1 : NG = ⊥ := hG NG hNGn hNGodd
  apply hτ1
  refine Subtype.ext (MulEquiv.ext fun y => ?_)
  have h1 := hNc (inl y⁻¹) (hinlH _)
  rw [conj_inl_inr_inl] at h1
  have h2 : y⁻¹ * (τ : MulAut G) y⁻¹⁻¹ ∈ NG := h1
  rw [hNG1, Subgroup.mem_bot] at h2
  have h3 : (τ : MulAut G) y = y := by
    simpa using (mul_eq_one_iff_eq_inv.1 h2).symm
  exact h3

end ZStarStep

end CFSG.ClassicalInvolution.GlaubermanAut
