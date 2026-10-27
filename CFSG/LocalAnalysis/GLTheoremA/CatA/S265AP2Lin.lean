module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp2
import TauCeti.RepresentationTheory.Unipotent.PowerOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LieType.SeitzGeneration.HyperBlocks (sumOp)
open CFSG.RankThree.PartOne.LIT (restrictAction restrictAction_apply)
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]

omit [FiniteDimensional F V] [Fintype A] in
private theorem exists_ne_one_mem_hyperplane (h9 : Nat.card A = 9) (D : Hyperplane A 3) :
    ∃ a : ↥A, a ∈ D.1 ∧ a ≠ 1 := by
  have hcard : Nat.card D.1 * D.1.index = 9 := by rw [Subgroup.card_mul_index, h9]
  rw [D.2] at hcard
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp fun h : D.1 = ⊥ => by
    rw [h, Subgroup.card_bot] at hcard
    omega
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem finrank_blockSpace_le_two_of_card_nine (h9 : Nat.card A = 9)
    (hfix : ∀ a : ↥A, a ≠ 1 → Module.finrank F (fixedByEnd (a : V ≃ₗ[F] V)) ≤ 2)
    (D : Hyperplane A 3) : Module.finrank F (blockSpace A D.1) ≤ 2 := by
  obtain ⟨a, haD, ha1⟩ := exists_ne_one_mem_hyperplane A h9 D
  have hle : blockSpace A D.1 ≤ fixedByEnd (a : V ≃ₗ[F] V) := fun v hv =>
    mem_fixedByEnd.mpr (((mem_blockSpace A).mp hv).1 a haD)
  exact (Submodule.finrank_mono hle).trans (hfix a ha1)

private theorem finrank_fixedSpaceOf_add_finrank_blockSpace_le (hpF : ((3 : ℕ) : F) ≠ 0)
    (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hfix : ∀ a : ↥A, a ≠ 1 → Module.finrank F (fixedByEnd (a : V ≃ₗ[F] V)) ≤ 2)
    (D : Hyperplane A 3) :
    Module.finrank F (fixedSpaceOf A) + Module.finrank F (blockSpace A D.1) ≤ 2 := by
  obtain ⟨a, haD, ha1⟩ := exists_ne_one_mem_hyperplane A h9 D
  have hinf : fixedSpaceOf A ⊓ blockSpace A D.1 = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ (blockSpace_le_commutatorSpaceOf A D.1)).trans
      (fixedSpaceOf_inf_commutatorSpaceOf A Nat.prime_three hpF hA).le)
  have hsup : fixedSpaceOf A ⊔ blockSpace A D.1 ≤ fixedByEnd (a : V ≃ₗ[F] V) :=
    sup_le (fun v hv => mem_fixedByEnd.mpr ((mem_fixedSpaceOf A).mp hv a))
      (fun v hv => mem_fixedByEnd.mpr (((mem_blockSpace A).mp hv).1 a haD))
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpaceOf A) (blockSpace A D.1)
  rw [hinf, finrank_bot] at h1
  have h2 := Submodule.finrank_mono hsup
  have h3 := hfix a ha1
  omega

theorem fixedSpaceOf_eq_bot_of_card_nine (hpF : ((3 : ℕ) : F) ≠ 0)
    {B : LinearMap.BilinForm F V} (halt : B.IsAlt) (hB : InvariantBilin A B)
    (hBn : B.Nondegenerate) (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hfix : ∀ a : ↥A, a ≠ 1 → Module.finrank F (fixedByEnd (a : V ≃ₗ[F] V)) ≤ 2) :
    fixedSpaceOf A = ⊥ := by
  by_contra hne
  have hpos : 0 < Module.finrank F (fixedSpaceOf A) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)
  have hblk : ∀ D : Hyperplane A 3, blockSpace A D.1 = ⊥ := by
    intro D
    have hle := finrank_fixedSpaceOf_add_finrank_blockSpace_le A hpF hA h9 hfix D
    have halt' : (LinearMap.BilinForm.restrict B (blockSpace A D.1)).IsAlt := fun w => by
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      exact halt _
    obtain ⟨k, hk⟩ := halt'.even_finrank
      (blockSpace_nondegenerate A Nat.prime_three hpF hA halt hB hBn D)
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hcomm : commutatorSpaceOf A = ⊥ := by
    rw [← iSup_blockSpace_eq_commutatorSpaceOf A Nat.prime_three hpF hA]
    exact iSup_eq_bot.mpr hblk
  have htop : fixedSpaceOf A = ⊤ := by
    have h := isCompl_fixedSpaceOf_commutatorSpaceOf A Nat.prime_three hpF hA
    rw [hcomm] at h
    exact eq_top_of_isCompl_bot h
  have hA1 : ∀ a : ↥A, a = 1 := fun a => Subtype.ext <| LinearEquiv.ext fun v => by
    have hv : v ∈ fixedSpaceOf A := by rw [htop]; exact Submodule.mem_top
    rw [(mem_fixedSpaceOf A).mp hv a]
    rfl
  haveI : Subsingleton ↥A := ⟨fun a b => (hA1 a).trans (hA1 b).symm⟩
  have h1 : Nat.card ↥A = 1 := Nat.card_unique
  omega

omit [FiniteDimensional F V] in
private theorem projBlock_mem_of_invariant (hpF : ((3 : ℕ) : F) ≠ 0) (hA : IsElemAbelian 3 A)
    (D : Hyperplane A 3) {W : Submodule F V} (hWA : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) {v : V}
    (hv : v ∈ W) : projBlock A Nat.prime_three hpF hA D v ∈ W := by
  rw [projBlock_apply_eq]
  refine W.sub_mem (W.smul_mem _ ?_) (W.smul_mem _ ?_) <;>
  · rw [sumOp, LinearMap.sum_apply]
    exact W.sum_mem fun e _ => by
      rw [actionEnd_apply]
      exact hWA _ (e : ↥A).2 v hv

private theorem eq_zero_of_mem_isotropic_of_mem_blockSpace (hpF : ((3 : ℕ) : F) ≠ 0)
    (hF : ∀ x : F, x ^ 3 = 1 → x = 1) {B : LinearMap.BilinForm F V} (halt : B.IsAlt)
    (hB : InvariantBilin A B) (hBn : B.Nondegenerate) (hA : IsElemAbelian 3 A)
    (D : Hyperplane A 3) (hD : Module.finrank F (blockSpace A D.1) ≤ 2) {W : Submodule F V}
    (hW : ∀ v ∈ W, ∀ w ∈ W, B v w = 0) (hWA : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) {u : V}
    (huW : u ∈ W) (huD : u ∈ blockSpace A D.1) : u = 0 := by
  by_contra hu0
  have huS : u ∈ W ⊓ blockSpace A D.1 := Submodule.mem_inf.mpr ⟨huW, huD⟩
  have hSlt : W ⊓ blockSpace A D.1 < blockSpace A D.1 := by
    refine lt_of_le_of_ne inf_le_right fun hSeq => hu0 ?_
    have h0 := (blockSpace_nondegenerate A Nat.prime_three hpF hA halt hB hBn D).1 ⟨u, huD⟩
      fun w => by
        rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
        have hw : (w : V) ∈ W ⊓ blockSpace A D.1 := by rw [hSeq]; exact w.2
        exact hW u huW w (Submodule.mem_inf.mp hw).1
    exact congrArg Subtype.val h0
  have hS1 : Module.finrank F ↥(W ⊓ blockSpace A D.1) = 1 := by
    have h1 := Submodule.finrank_lt_finrank_of_lt hSlt
    have h2 : Module.finrank F ↥(W ⊓ blockSpace A D.1) ≠ 0 := fun h =>
      hu0 ((Submodule.eq_bot_iff _).mp (Submodule.finrank_eq_zero.mp h) u huS)
    omega
  obtain ⟨x, hxD⟩ : ∃ x : ↥A, x ∉ D.1 := by
    by_contra hall
    have hDtop : D.1 = ⊤ := eq_top_iff.mpr fun x _ => not_not.mp (not_exists.mp hall x)
    have h := D.2
    rw [hDtop, Subgroup.index_top] at h
    omega
  have hxS : (x : V ≃ₗ[F] V) u ∈ W ⊓ blockSpace A D.1 :=
    Submodule.mem_inf.mpr ⟨hWA _ x.2 u huW, blockSpace_invariant A Nat.prime_three hpF hA huD⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u, huS⟩ : ↥(W ⊓ blockSpace A D.1))
    fun h => hu0 (congrArg Subtype.val h)).mp hS1 ⟨_, hxS⟩
  have hxu : (x : V ≃ₗ[F] V) u = c • u := (congrArg Subtype.val hc).symm
  have hpow : ∀ n : ℕ, ((x : V ≃ₗ[F] V) ^ n) u = c ^ n • u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' (x : V ≃ₗ[F] V) n, LinearEquiv.mul_apply, ih, map_smul, hxu, smul_smul,
        ← pow_succ c n]
  have hc3 : c ^ 3 = 1 := by
    have h := hpow 3
    rw [hA.2 _ x.2] at h
    have h' : (c ^ 3 - 1) • u = 0 := by
      rw [sub_smul, one_smul, ← h]
      simp
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hu0)
  refine hu0 (eq_zero_of_fixed_mem_blockSpace A Nat.prime_three hpF hA hxD huD ?_)
  rw [hxu, hF c hc3, one_smul]

theorem eq_bot_of_isotropic_of_invariant (hpF : ((3 : ℕ) : F) ≠ 0)
    (hF : ∀ x : F, x ^ 3 = 1 → x = 1) {B : LinearMap.BilinForm F V} (halt : B.IsAlt)
    (hB : InvariantBilin A B) (hBn : B.Nondegenerate) (hA : IsElemAbelian 3 A)
    (hfixA : fixedSpaceOf A = ⊥)
    (hblk : ∀ D : Hyperplane A 3, Module.finrank F (blockSpace A D.1) ≤ 2)
    (W : Submodule F V) (hW : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hWA : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) : W = ⊥ := by
  have htop : (⨆ D : Hyperplane A 3, blockSpace A D.1) = ⊤ := by
    have h := isCompl_fixedSpaceOf_commutatorSpaceOf A Nat.prime_three hpF hA
    rw [hfixA] at h
    rw [iSup_blockSpace_eq_commutatorSpaceOf A Nat.prime_three hpF hA]
    exact eq_top_of_bot_isCompl h
  refine (Submodule.eq_bot_iff W).mpr fun v hv => ?_
  by_contra hv0
  obtain ⟨D, hD⟩ : ∃ D : Hyperplane A 3, projBlock A Nat.prime_three hpF hA D v ≠ 0 := by
    by_contra hall
    refine hv0 (hBn.2 v fun w => ?_)
    have hw : w ∈ ⨆ D : Hyperplane A 3, blockSpace A D.1 := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction (fun D : Hyperplane A 3 => blockSpace A D.1)
      (motive := fun w => B w v = 0) hw (fun D u hu => ?_) (by simp) (fun x y hx hy => ?_)
    · exact blockSpace_ker_orthogonal A Nat.prime_three hpF hA B hB D hu
        (LinearMap.mem_ker.mpr (not_not.mp (not_exists.mp hall D)))
    · rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  exact hD (eq_zero_of_mem_isotropic_of_mem_blockSpace A hpF hF halt hB hBn hA D (hblk D) hW hWA
    (projBlock_mem_of_invariant A hpF hA D hWA hv)
    (projBlock_apply_mem A Nat.prime_three hpF hA D v))

omit [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] in
private theorem natCast_three_ne_zero_of_charTwo {K : Type*} [Field K] [CharP K 2] :
    ((3 : ℕ) : K) ≠ 0 := fun h => by
  have h2 := (CharP.cast_eq_zero_iff K 2 3).mp h
  omega

theorem eq_bot_of_normalized_two_subgroup [CharP F 2] (hF : ∀ x : F, x ^ 3 = 1 → x = 1)
    {B : LinearMap.BilinForm F V} (halt : B.IsAlt) (hB : InvariantBilin A B)
    (hBn : B.Nondegenerate) (hA : IsElemAbelian 3 A) (hfixA : fixedSpaceOf A = ⊥)
    (hblk : ∀ D : Hyperplane A 3, Module.finrank F (blockSpace A D.1) ≤ 2)
    {T : Subgroup (V ≃ₗ[F] V)} (hT : IsPGroup 2 T)
    (hTB : ∀ t ∈ T, ∀ u v : V, B (t u) (t v) = B u v)
    (hAT : A ≤ Subgroup.normalizer (T : Set (V ≃ₗ[F] V))) : T = ⊥ := by
  have hpF : ((3 : ℕ) : F) ≠ 0 := natCast_three_ne_zero_of_charTwo
  let U : Submodule F V := ⨅ t : ↥T, fixedByEnd (t : V ≃ₗ[F] V)
  have hmemU : ∀ u : V, u ∈ U ↔ ∀ t ∈ T, t u = u := fun u => by
    simp only [U, Submodule.mem_iInf, mem_fixedByEnd, Subtype.forall]
  have hconj : ∀ a ∈ A, ∀ t ∈ T, a⁻¹ * t * a ∈ T := fun a ha t ht => by
    have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hAT ha)) t).mp ht
    rwa [inv_inv] at h
  have hUA : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := fun a ha u hu => by
    rw [hmemU] at hu ⊢
    intro t ht
    have h2 : (a * (a⁻¹ * t * a)) u = a u := by rw [LinearEquiv.mul_apply, hu _ (hconj a ha t ht)]
    rwa [mul_assoc a⁻¹ t a, mul_inv_cancel_left, LinearEquiv.mul_apply] at h2
  have hUperpA : ∀ a ∈ A, ∀ m ∈ B.orthogonal U, a m ∈ B.orthogonal U := fun a ha m hm => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm ⊢
    intro n hn
    have h2 : B (a (a⁻¹ n)) (a m) = B (a⁻¹ n) m := hB ⟨a, ha⟩ (a⁻¹ n) m
    have h3 : a (a⁻¹ n) = n := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [h3] at h2
    rw [h2]
    exact hm _ (hUA _ (A.inv_mem ha) n hn)
  have hR : U ⊓ B.orthogonal U = ⊥ :=
    eq_bot_of_isotropic_of_invariant A hpF hF halt hB hBn hA hfixA hblk _
      (fun v hv w hw => (LinearMap.BilinForm.mem_orthogonal_iff.mp (Submodule.mem_inf.mp hw).2) v
        (Submodule.mem_inf.mp hv).1)
      (fun a ha w hw => Submodule.mem_inf.mpr
        ⟨hUA a ha w (Submodule.mem_inf.mp hw).1, hUperpA a ha w (Submodule.mem_inf.mp hw).2⟩)
  have hcompl : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate halt.isRefl
      (LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B halt.isRefl
        (disjoint_iff.mpr hR))
  have hUperpT : ∀ t : ↥T, ∀ m ∈ B.orthogonal U, T.subtype t m ∈ B.orthogonal U := by
    intro t m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm ⊢
    intro n hn
    have h1 : (t : V ≃ₗ[F] V) n = n := (hmemU n).mp hn t t.2
    calc B n (T.subtype t m) = B ((t : V ≃ₗ[F] V) n) ((t : V ≃ₗ[F] V) m) := by rw [h1]; rfl
      _ = B n m := hTB t t.2 n m
      _ = 0 := hm n hn
  have hperp : B.orthogonal U = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(B.orthogonal U) := Submodule.nontrivial_iff_ne_bot.mpr hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let ρ : Representation F ↥T ↥(B.orthogonal U) :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
        (restrictAction T.subtype (B.orthogonal U) hUperpT)
    obtain ⟨w, hw0, hwfix⟩ := Representation.exists_common_fixed_vector_of_isPGroup 2 hT ρ
    refine hw0 (Subtype.ext ?_)
    have hwU : (w : V) ∈ U := (hmemU w).mpr fun t ht => by
      have h : ((restrictAction T.subtype (B.orthogonal U) hUperpT ⟨t, ht⟩ w :
          ↥(B.orthogonal U)) : V) = w := congrArg Subtype.val (hwfix ⟨t, ht⟩)
      rwa [restrictAction_apply] at h
    have hwR : (w : V) ∈ U ⊓ B.orthogonal U := Submodule.mem_inf.mpr ⟨hwU, w.2⟩
    rw [hR] at hwR
    exact (Submodule.mem_bot F).mp hwR
  have hU : U = ⊤ := by
    rw [hperp] at hcompl
    exact eq_top_of_isCompl_bot hcompl
  refine (Subgroup.eq_bot_iff_forall T).mpr fun t ht => LinearEquiv.ext fun v => ?_
  have hv : v ∈ U := by rw [hU]; exact Submodule.mem_top
  exact (hmemU v).mp hv t ht

end CFSG.LocalAnalysis.GLTheoremA.S265A
