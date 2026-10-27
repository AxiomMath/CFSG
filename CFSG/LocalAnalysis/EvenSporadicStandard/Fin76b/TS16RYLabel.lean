module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem ELabelling.exists_mulEquiv {Γ Δ : Type*} [Group Γ] [Group Δ] {E' : Subgroup Γ}
    {F' : Subgroup Δ} {t : Γ} {u : Δ} {mulE : ℕ → ℕ → ℕ} {tI : ℕ} {elt : ℕ → Γ} {elt' : ℕ → Δ}
    (h : ELabelling E' t mulE tI elt) (h' : ELabelling F' u mulE tI elt') :
    ∃ e : ↥E' ≃* ↥F', (∀ k (hk : k < 32), e ⟨elt k, h.mem k hk⟩ = ⟨elt' k, h'.mem k hk⟩) ∧
      ∃ (ht : t ∈ E') (hu : u ∈ F'), e ⟨t, ht⟩ = ⟨u, hu⟩ := by
  have hex : ∀ x : ↥E', ∃ k < 32, elt k = (x : Γ) := fun x => h.surj x.1 x.2
  choose kOf hk1 hk2 using hex
  have hkmul : ∀ x y : ↥E', kOf (x * y) = mulE (kOf x) (kOf y) := by
    intro x y
    apply h.inj (kOf (x * y)) (hk1 (x * y)) (mulE (kOf x) (kOf y))
      (h.lt (kOf x) (hk1 x) (kOf y) (hk1 y))
    rw [hk2, h.mul (kOf x) (hk1 x) (kOf y) (hk1 y), hk2 x, hk2 y, Subgroup.coe_mul]
  let f : ↥E' → ↥F' := fun x => ⟨elt' (kOf x), h'.mem (kOf x) (hk1 x)⟩
  have hf : ∀ x y : ↥E', f (x * y) = f x * f y := by
    intro x y
    apply Subtype.ext
    show elt' (kOf (x * y)) = elt' (kOf x) * elt' (kOf y)
    rw [hkmul x y, h'.mul (kOf x) (hk1 x) (kOf y) (hk1 y)]
  let ψ : ↥E' →* ↥F' := MonoidHom.mk' f hf
  have hψ : ∀ x : ↥E', (ψ x : Δ) = elt' (kOf x) := fun x => rfl
  have hkk : ∀ k (hk : k < 32), kOf ⟨elt k, h.mem k hk⟩ = k := fun k hk =>
    h.inj (kOf ⟨elt k, h.mem k hk⟩) (hk1 ⟨elt k, h.mem k hk⟩) k hk
      (hk2 ⟨elt k, h.mem k hk⟩)
  have hψe : ∀ k (hk : k < 32), ψ ⟨elt k, h.mem k hk⟩ = ⟨elt' k, h'.mem k hk⟩ := by
    intro k hk
    apply Subtype.ext
    show elt' (kOf ⟨elt k, h.mem k hk⟩) = elt' k
    rw [hkk k hk]
  have hbij : Function.Bijective ψ := by
    constructor
    · intro x y hxy
      have h1 : elt' (kOf x) = elt' (kOf y) :=
        (hψ x).symm.trans ((congrArg Subtype.val hxy).trans (hψ y))
      have h2 : kOf x = kOf y := h'.inj (kOf x) (hk1 x) (kOf y) (hk1 y) h1
      apply Subtype.ext
      rw [← hk2 x, ← hk2 y, h2]
    · intro y
      obtain ⟨k, hk, hky⟩ := h'.surj y.1 y.2
      exact ⟨⟨elt k, h.mem k hk⟩, (hψe k hk).trans (Subtype.ext hky)⟩
  have ht : t ∈ E' := by
    rw [← h.at_tI]
    exact h.mem tI h.tI_lt
  have hu : u ∈ F' := by
    rw [← h'.at_tI]
    exact h'.mem tI h'.tI_lt
  refine ⟨MulEquiv.ofBijective ψ hbij, fun k hk => hψe k hk, ht, hu, ?_⟩
  have hT : (⟨t, ht⟩ : ↥E') = ⟨elt tI, h.mem tI h.tI_lt⟩ := Subtype.ext h.at_tI.symm
  have hU : (⟨u, hu⟩ : ↥F') = ⟨elt' tI, h'.mem tI h'.tI_lt⟩ := Subtype.ext h'.at_tI.symm
  show ψ ⟨t, ht⟩ = ⟨u, hu⟩
  rw [hT, hψe tI h.tI_lt, hU]

theorem ELabelling.subgroupOf {Γ : Type*} [Group Γ] {M E' : Subgroup Γ} {t : Γ}
    {mulE : ℕ → ℕ → ℕ} {tI : ℕ} {elt : ℕ → Γ} (h : ELabelling E' t mulE tI elt)
    (hEM : E' ≤ M) (htM : t ∈ M) :
    ∃ elt' : ℕ → ↥M, ELabelling (E'.subgroupOf M) (⟨t, htM⟩ : ↥M) mulE tI elt' ∧
      ∀ k < 32, ((elt' k : ↥M) : Γ) = elt k := by
  have hM : ∀ k < 32, elt k ∈ M := fun k hk => hEM (h.mem k hk)
  let elt' : ℕ → ↥M := fun k => if hk : k < 32 then ⟨elt k, hM k hk⟩ else 1
  have hval : ∀ k (hk : k < 32), elt' k = ⟨elt k, hM k hk⟩ := fun k hk => dif_pos hk
  have hcoe : ∀ k < 32, ((elt' k : ↥M) : Γ) = elt k := fun k hk =>
    congrArg Subtype.val (hval k hk)
  refine ⟨elt', ⟨?_, ?_, ?_, ?_, ?_, ?_, h.tI_lt, ?_⟩, hcoe⟩
  · intro k hk
    rw [Subgroup.mem_subgroupOf, hcoe k hk]
    exact h.mem k hk
  · intro e he
    obtain ⟨k, hk, hke⟩ := h.surj e.1 (Subgroup.mem_subgroupOf.1 he)
    refine ⟨k, hk, ?_⟩
    apply Subtype.ext
    rw [hcoe k hk]
    exact hke
  · intro a ha b hb hab
    apply h.inj a ha b hb
    calc elt a = ((elt' a : ↥M) : Γ) := (hcoe a ha).symm
      _ = ((elt' b : ↥M) : Γ) := congrArg Subtype.val hab
      _ = elt b := hcoe b hb
  · exact h.lt
  · intro a ha b hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, hcoe _ (h.lt a ha b hb), hcoe a ha, hcoe b hb]
    exact h.mul a ha b hb
  · exact Subtype.ext ((hcoe 0 (by norm_num)).trans h.one)
  · exact Subtype.ext ((hcoe tI h.tI_lt).trans h.at_tI)

end CFSG.EvenSporadicStandard.Fin76b
