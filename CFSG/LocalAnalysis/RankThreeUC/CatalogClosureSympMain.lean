module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSympAvg

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace SpClosure

open Subgroup

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

theorem exists_fixed_ne_zero [Finite K] [CharP K 2] [FiniteDimensional K V]
    (S : Subgroup (isom B)) (hS : IsPGroup 2 S)
    (M : Submodule K V) (hM : M ≠ ⊥) (hMS : ∀ s ∈ S, ∀ x ∈ M, s • x ∈ M) :
    ∃ x ∈ M, x ≠ 0 ∧ ∀ s ∈ S, s • x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M' : SubMulAction S V := ⟨(M : Set V), fun s x hx => hMS s s.2 x hx⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite M' := inferInstance
  have hmod := hS.card_modEq_card_fixedPoints M'
  have hcardM : 2 ∣ Nat.card M' := by
    have h1 : Nat.card M' = Nat.card M :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
    have := Fintype.ofFinite K
    have := Fintype.ofFinite M
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    rw [h1, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := M), hf,
      ← pow_mul]
    exact dvd_pow_self 2
      (Nat.mul_ne_zero f.ne_zero (Nat.one_le_iff_ne_zero.1 (Submodule.one_le_finrank_iff.2 hM)))
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints S M') := by
    have := (Nat.modEq_zero_iff_dvd.2 hcardM).symm.trans hmod
    exact Nat.modEq_zero_iff_dvd.1 this.symm
  let z₀ : MulAction.fixedPoints S M' := ⟨⟨0, M.zero_mem⟩, fun s => Subtype.ext (smul_zero _)⟩
  have : Nonempty (MulAction.fixedPoints S M') := ⟨z₀⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints S M') := Nat.card_pos
  have hgt : 1 < Nat.card (MulAction.fixedPoints S M') := by
    obtain ⟨k, hk⟩ := hfix
    omega
  have : Nontrivial (MulAction.fixedPoints S M') := Finite.one_lt_card_iff_nontrivial.1 hgt
  obtain ⟨t, ht⟩ := exists_ne z₀
  refine ⟨t.1.1, t.1.2, fun h0 => ht (Subtype.ext (Subtype.ext h0)), fun s hs => ?_⟩
  have := t.2 ⟨s, hs⟩
  exact congrArg Subtype.val this

@[expose] def fixSub (S : Subgroup (isom B)) : Submodule K V where
  carrier := {x | ∀ s ∈ S, s • x = x}
  add_mem' {a b} ha hb := fun s hs => by rw [smul_add, ha s hs, hb s hs]
  zero_mem' := fun s _ => smul_zero s
  smul_mem' c x hx := fun s hs => by rw [smul_smul_K, hx s hs]

theorem smul_mem_fixSub {S E : Subgroup (isom B)} (hEN : E ≤ normalizer (S : Set (isom B)))
    {e : isom B} (he : e ∈ E) {x : V} (hx : x ∈ fixSub S) : e • x ∈ fixSub S := by
  intro s hs
  have hn := (mem_normalizer_iff.1 (hEN (E.inv_mem he)) s).1 hs
  simp only [inv_inv] at hn
  have h1 : e⁻¹ * s * e ∈ S := hn
  calc s • e • x = e • ((e⁻¹ * s * e) • x) := by simp [mul_smul]
    _ = e • x := by rw [hx _ h1]

theorem smul_mem_orth_fixSub {S : Subgroup (isom B)} {s : isom B} (hs : s ∈ S) {y : V}
    (hy : y ∈ B.orthogonal (fixSub S)) : s • y ∈ B.orthogonal (fixSub S) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy ⊢
  intro f hf
  rw [← B_inv_smul, hf _ (S.inv_mem hs)]
  exact hy f hf

theorem twoLocalClosure_eq_top_isom [Finite K] [CharP K 2] [FiniteDimensional K V]
    [IsSimpleGroup (isom B)] (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (β₀ : LinearMap.BilinForm K V) (hβ₀ : ∀ x y, β₀ x y + β₀ y x = B x y)
    (E S₀ : Subgroup (isom B)) (hE : Odd (Nat.card E)) (hS₀ : S₀ ≠ ⊥) (hS₀2 : IsPGroup 2 S₀)
    (hEN : E ≤ normalizer (S₀ : Set (isom B))) : twoLocalClosure E = ⊤ := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (isom B) := Finite.of_injective (fun g : isom B => ((g : V ≃ₗ[K] V) : V → V))
    (fun a b h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  have : Finite E := inferInstance
  set F := fixSub S₀ with hF
  set W := F ⊓ B.orthogonal F with hWdef
  have hFE : ∀ e ∈ E, ∀ x ∈ F, e • x ∈ F := fun e he x hx => smul_mem_fixSub hEN he hx
  have hFpE : ∀ e ∈ E, ∀ x ∈ B.orthogonal F, e • x ∈ B.orthogonal F := fun e he x hx =>
    (smul_mem_orth_iff (le_stab_of_invariant hFE he) x).2 hx
  have hWE : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W := fun e he x hx =>
    ⟨hFE e he x hx.1, hFpE e he x hx.2⟩
  have hWiso : W ≤ B.orthogonal W := fun w hw =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 (fun n hn =>
      LinearMap.BilinForm.mem_orthogonal_iff.1 hw.2 n hn.1)
  have hW0 : W ≠ ⊥ := by
    have hFp : B.orthogonal F ≠ ⊥ := by
      intro hbot
      apply hS₀
      have hxF : ∀ x, x ∈ F := fun x => by
        rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl F]
        refine LinearMap.BilinForm.mem_orthogonal_iff.2 (fun n hn => ?_)
        rw [hbot, Submodule.mem_bot] at hn
        rw [hn, map_zero, LinearMap.zero_apply]
      rw [Subgroup.eq_bot_iff_forall]
      intro s hs
      refine isom_ext fun x => ?_
      rw [one_smul]
      exact hxF x s hs
    obtain ⟨x, hxp, hx0, hxfix⟩ := exists_fixed_ne_zero S₀ hS₀2 (B.orthogonal F) hFp
      (fun s hs y hy => smul_mem_orth_fixSub hs hy)
    intro hWbot
    have : x ∈ W := ⟨hxfix, hxp⟩
    rw [hWbot] at this
    exact hx0 ((Submodule.mem_bot K).1 this)
  obtain ⟨X, hXc, hXiso, hXE⟩ := exists_isotropic_compl hB hnd β₀ hβ₀ E hE hWiso hWE
  have hX0 : X ≠ ⊥ := by
    intro hXbot
    have htop : B.orthogonal W = ⊤ := by
      have := hXc.sup_eq_top
      rwa [hXbot, bot_sup_eq] at this
    apply hW0
    rw [Submodule.eq_bot_iff]
    intro w hw
    apply hnd.1 w
    intro y
    exact LinearMap.BilinForm.mem_orthogonal_iff.1
      (htop ▸ Submodule.mem_top : y ∈ B.orthogonal W) w hw
  have hWC := stab_le_twoLocalClosure hB hnd hW0 hWiso (le_stab_of_invariant hWE)
  have hXC := stab_le_twoLocalClosure hB hnd hX0 hXiso (le_stab_of_invariant hXE)
  obtain ⟨v₀, -, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  exact eq_top_of_tv_mem hB hnd hv₀ (fun v c => tv_mem_of_stab_le hB hWiso hXc hWC hXC v c)

end SpClosure

end CFSG.LocalAnalysis.RankThreeUC
