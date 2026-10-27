module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapBoundary
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_not_le_of_isPGroup {P Y : Subgroup G} (hP : IsPGroup 2 P)
    (hYP : Y ≤ P) (hne : ¬ P ≤ Y) : ∃ a ∈ P, a ∈ normalizer (Y : Set G) ∧ a ∉ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := Y.subgroupOf P with hI
  have hIlt : I < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : P) ∈ I := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := P) I hIlt
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : (x : G) ∈ normalizer (Y : Set G) := by
    have : x ∈ (normalizer (Y : Set G)).subgroupOf P := by
      rw [subgroupOf_normalizer_eq hYP]
      exact hxN
    exact mem_subgroupOf.mp this
  exact ⟨x, x.2, hxN', fun hx => hxI (mem_subgroupOf.mpr hx)⟩

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {f : ℕ}

theorem S₀_le_normalizer_W
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) :
    U₁ ⊔ T ≤ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  rw [← hE.sup_V_eq]
  intro x hx
  exact mem_normalizer_sup (hE.S₀_le_normalizer hx) (hE.S₀_le_normalizer_V h hF hf e hx)

theorem rightConjugate_V_eq_or
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {n : G}
    (hn : n ∈ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G))
    {X : Subgroup G} (hX₀ : X = U₁ ∨ X = gmsV L T) :
    rightConjugate X n = U₁ ∨ rightConjugate X n = gmsV L T := by
  obtain ⟨hVc, hVel, -, -, -⟩ := hX.vFacts h hF
  have hXW : X ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := by
    rcases hX₀ with rfl | rfl
    · exact le_sup_left
    · exact hE.V_le
  have hWS : U₁ ⊔ (T ⊓ centralizer (L : Set G)) ≤ U₁ ⊔ T := sup_le_sup_left inf_le_left _
  have hle : rightConjugate X n ≤ U₁ ⊔ T := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := (mem_normalizer_iff.mp (inv_mem hn) _).mp (hXW hx)
    exact hWS (by simpa [mul_assoc] using h1)
  have hel : IsElemAbelian 2 X := by
    rcases hX₀ with rfl | rfl
    · exact hE.elem
    · exact hVel
  have hc : Nat.card X = (2 ^ f) ^ 2 := by
    rcases hX₀ with rfl | rfl
    · exact hE.card
    · rw [hVc, hq, sq]
  exact hE.eq_or_eq_of_card h hF hf e hX hq hle (isElemAbelian_map _ hel)
    (by rw [rightConjugate_card, hc])

omit [Finite G] in
theorem ne_V (hE : Sec4Elem L T U₁ (2 ^ f)) : U₁ ≠ gmsV L T := by
  intro h1
  have h2 := hE.inf_V
  rw [← h1, inf_idem] at h2
  exact (ne_of_gt hE.lt) h2

theorem swap_of_not_mem
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {n : G}
    (hn : n ∈ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G))
    (hnV : n ∉ normalizer (gmsV L T : Set G)) :
    rightConjugate (gmsV L T) n = U₁ ∧ rightConjugate U₁ n = gmsV L T := by
  have hV : rightConjugate (gmsV L T) n = U₁ :=
    (hE.rightConjugate_V_eq_or h hF hf e hX hq hn (Or.inr rfl)).resolve_right
      fun h1 => hnV ((rightConjugate_eq_self_iff _ _).mp h1)
  exact ⟨hV, (hE.rightConjugate_V_eq_or h hF hf e hX hq hn (Or.inl rfl)).resolve_left
    fun h1 => hE.ne_V (map_injective (MulAut.conj n⁻¹).injective (h1.trans hV.symm))⟩

theorem card_le_two_mul_inf_normalizer
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {X : Subgroup G}
    (hXW : X ≤ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G)) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ normalizer (gmsV L T : Set G) : Subgroup G) := by
  refine card_le_two_mul_of_mul_mem fun x₁ hx₁ x₂ hx₂ h₁ h₂ =>
    mem_inf.mpr ⟨mul_mem hx₁ hx₂, ?_⟩
  have h₁' : x₁ ∉ normalizer (gmsV L T : Set G) := fun h' => h₁ (mem_inf.mpr ⟨hx₁, h'⟩)
  have h₂' : x₂ ∉ normalizer (gmsV L T : Set G) := fun h' => h₂ (mem_inf.mpr ⟨hx₂, h'⟩)
  obtain ⟨hV₁, -⟩ := hE.swap_of_not_mem h hF hf e hX hq (hXW hx₁) h₁'
  obtain ⟨-, hU₂⟩ := hE.swap_of_not_mem h hF hf e hX hq (hXW hx₂) h₂'
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hV₁, hU₂]

theorem eq_or_eq_of_card_of_le
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {Y : Subgroup G}
    (hY : IsPGroup 2 Y) (hS₀Y : U₁ ⊔ T ≤ Y)
    (hYW : Y ≤ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G))
    {E : Subgroup G} (hEY : E ≤ Y) (hEel : IsElemAbelian 2 E)
    (hcard : (2 ^ f) ^ 2 ≤ Nat.card E) : E = U₁ ∨ E = gmsV L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀ := h.isElemAbelian_T₀ hF
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEel.2 x hx
  have hYV : Y ⊓ normalizer (gmsV L T : Set G) = U₁ ⊔ T :=
    hE.sylow.eq_of_le (le_inf hS₀Y (hE.S₀_le_normalizer_V h hF hf e)) inf_le_right
      (hY.to_le inf_le_left)
  by_cases hES : E ≤ U₁ ⊔ T
  · exact hE.eq_or_eq_of_card h hF hf e hX hq hES hEel hcard
  exfalso
  obtain ⟨x, hxE, hxS⟩ := IsConcreteLE.not_le_iff_exists.mp hES
  have hxV : x ∉ normalizer (gmsV L T : Set G) := fun h1 => by
    rw [← hYV] at hxS
    exact hxS (mem_inf.mpr ⟨hEY hxE, h1⟩)
  obtain ⟨hV₁, hU₁⟩ := hE.swap_of_not_mem h hF hf e hX hq (hYW (hEY hxE)) hxV
  have hcomm : ∀ y ∈ E, x * y * x⁻¹ = y := fun y hy => by
    have h1 : x * y = y * x := congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hxE⟩ ⟨y, hy⟩)
    rw [h1, mul_inv_cancel_right]
  have hEW : E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ gmsA L T := by
    rcases hE.le_or_le hT₀ (inf_le_right : E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ _)
        (fun y hy => hE2 y (mem_inf.mp hy).1) with hU | hV
    · intro y hy
      have hyU := hU hy
      have hyV : y ∈ gmsV L T := by
        rw [← hU₁, mem_rightConjugate_iff, hcomm y (mem_inf.mp hy).1]
        exact hyU
      rw [← hE.inf_V]
      exact mem_inf.mpr ⟨hyU, hyV⟩
    · intro y hy
      have hyV := hV hy
      have hyU : y ∈ U₁ := by
        rw [← hV₁, mem_rightConjugate_iff, hcomm y (mem_inf.mp hy).1]
        exact hyV
      rw [← hE.inf_V]
      exact mem_inf.mpr ⟨hyU, hyV⟩
  have h1 := hE.card_le_two_mul_inf_normalizer h hF hf e hX hq (hEY.trans hYW)
  have h2 : E ⊓ normalizer (gmsV L T : Set G) ≤ E ⊓ (U₁ ⊔ T) :=
    le_inf inf_le_left ((inf_le_inf_right _ hEY).trans_eq hYV)
  have h3 := hE.card_le_two_mul h hf e (inf_le_right : E ⊓ (U₁ ⊔ T) ≤ U₁ ⊔ T)
    (fun y hy => hE2 y (mem_inf.mp hy).1)
  have h4 : E ⊓ (U₁ ⊔ T) ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ gmsA L T :=
    fun y hy => hEW (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1, (mem_inf.mp hy).2⟩)
  have h5 := card_le_of_le h4
  have h6 := card_le_of_le h2
  rw [(hX.sylow h).1] at h5
  have hq8 : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  have h8 : 8 * 2 ^ f ≤ (2 ^ f) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ hq8
  omega

theorem le_normalizer_W
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hS₀P : U₁ ⊔ T ≤ P) :
    P ≤ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨hVc, hVel, -, -, -⟩ := hX.vFacts h hF
  have hVS : gmsV L T ≤ U₁ ⊔ T :=
    (sup_le (inf_le_left.trans inf_le_left) inf_le_left).trans le_sup_right
  have hYp : IsPGroup 2
      (P ⊓ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) :
        Subgroup G) := hP.to_le inf_le_left
  have hS₀Y : U₁ ⊔ T ≤
      P ⊓ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) :=
    le_inf hS₀P (hE.S₀_le_normalizer_W h hF hf e)
  by_contra hne
  obtain ⟨a, haP, haN, haY⟩ := exists_mem_normalizer_of_not_le_of_isPGroup hP inf_le_left
    fun h1 => hne (h1.trans inf_le_right)
  have hconj : ∀ X : Subgroup G,
      X ≤ P ⊓ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) →
      rightConjugate X a ≤
        P ⊓ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
    intro X hXY x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := (mem_normalizer_iff.mp (inv_mem haN) _).mp (hXY hx)
    have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [h2] at h1
  have hU := hE.eq_or_eq_of_card_of_le h hF hf e hX hq hYp hS₀Y inf_le_right
    (hconj _ (le_sup_left.trans hS₀Y)) (isElemAbelian_map _ hE.elem)
    (by rw [rightConjugate_card, hE.card])
  have hV := hE.eq_or_eq_of_card_of_le h hF hf e hX hq hYp hS₀Y inf_le_right
    (hconj _ (hVS.trans hS₀Y)) (isElemAbelian_map _ hVel)
    (by rw [rightConjugate_card, hVc, hq, sq])
  have hinj : ∀ X₁ X₂ : Subgroup G, rightConjugate X₁ a = rightConjugate X₂ a → X₁ = X₂ :=
    fun X₁ X₂ h1 => map_injective (MulAut.conj a⁻¹).injective h1
  have hW : rightConjugate (U₁ ⊔ gmsV L T) a = U₁ ⊔ gmsV L T := by
    have hsup : rightConjugate (U₁ ⊔ gmsV L T) a =
        rightConjugate U₁ a ⊔ rightConjugate (gmsV L T) a := Subgroup.map_sup _ _ _
    rw [hsup]
    rcases hU with hU | hU <;> rcases hV with hV | hV
    · exact absurd (hinj _ _ (hU.trans hV.symm)) hE.ne_V
    · rw [hU, hV]
    · rw [hU, hV, sup_comm]
    · exact absurd (hinj _ _ (hU.trans hV.symm)) hE.ne_V
  rw [hE.sup_V_eq, rightConjugate_eq_self_iff] at hW
  exact haY (mem_inf.mpr ⟨haP, hW⟩)

end Sec4Elem

end CFSG.ComponentClassification.GMS78
