module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.RankThree.Chevalley (even_Chevalley_pinned_root_SL2_maps)
open CFSG.LieType.Steinberg (Adjoint.f4Datum)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2FieldPieceModelNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Checks

theorem iform_self_check_q2p : ∀ γ ∈ rootFinset .F4, iform γ γ = 2 ∨ iform γ γ = 4 := by
  decide +kernel

theorem psiF4_iform_check :
    (∀ γ ∈ rootFinset .F4, iform γ γ = 2 → iform (psiF4 γ) (psiF4 γ) = 4) ∧
      ∀ γ ∈ rootFinset .F4, ∀ δ ∈ rootFinset .F4,
        iform γ δ = 0 → iform (psiF4 γ) (psiF4 δ) = 0 := by
  decide +kernel

theorem iform_self_eq_two_or_four_q2p {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    iform γ γ = 2 ∨ iform γ γ = 4 :=
  iform_self_check_q2p γ (mem_rootFinset.2 hγ)

end Checks

section Coroot

variable {K : Type} [Field K]

@[expose] def q2pCoroot (γ : Fin (Tag.rank .F4) → ℤ) (c : Kˣ) : Fin (Tag.rank .F4) → Kˣ :=
  fun i => c ^ corootPair γ (Pi.single i 1)

theorem q2pCoroot_zpow (γ : Fin (Tag.rank .F4) → ℤ) (c : Kˣ) (n : ℤ) :
    q2pCoroot γ (c ^ n) = q2pCoroot γ c ^ n := by
  funext i
  simp only [q2pCoroot, Pi.pow_apply, ← zpow_mul, mul_comm]

theorem corootPair_eq_sum_q2p {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (v : Fin (Tag.rank .F4) → ℤ) :
    corootPair γ v = ∑ i, v i * corootPair γ (Pi.single i 1) := by
  have hpos := iform_self_pos_of_isRoot hγ
  refine Int.eq_of_mul_eq_mul_right hpos.ne' ?_
  rw [corootPair_mul hγ, Finset.sum_mul, iform_eq_sum_mul_iform_single γ v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, corootPair_mul hγ]
  ring

theorem rootChar_q2pCoroot {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (c : Kˣ)
    (v : Fin (Tag.rank .F4) → ℤ) : rootChar (q2pCoroot γ c) v = c ^ corootPair γ v := by
  rw [rootChar, corootPair_eq_sum_q2p hγ v, ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [q2pCoroot, ← zpow_mul, mul_comm]

theorem mem_rootCharKernel_q2pCoroot {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ) (h0 : iform γ δ = 0) (c : Kˣ) : δ ∈ rootCharKernel (q2pCoroot γ c) := by
  refine ⟨hδ, ?_⟩
  rw [rootChar_q2pCoroot hγ, corootPair, h0, mul_zero, Int.zero_ediv, zpow_zero]

theorem rootSpan_orthRoots_le_centralizer_q2pCoroot {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) {S : Set (Fin (Tag.rank .F4) → ℤ)} (hS : S ⊆ orthRoots γ) (c : Kˣ) :
    rootSpan .F4 K S ≤ centralizer {rootDiagUnit .F4 (q2pCoroot γ c)} :=
  rootSpan_le_centralizer _ fun _ hδ =>
    mem_rootCharKernel_q2pCoroot hγ (hS hδ).1 (hS hδ).2 c

end Coroot

section SL2

variable {k : Type} [Field k] {K₂ : Type} [Field K₂]

theorem eq_one_of_ne_zero_of_natCard_eq_two_q2p [Finite k] (hk : Nat.card k = 2) {x : k}
    (hx : x ≠ 0) : x = 1 := by
  have := Fintype.ofFinite k
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hk, show 2 - 1 = 1 from rfl, pow_one] at h

theorem pow_three_eq_one_of_natCard_eq_four_q2p [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ 2)
    (l : K₂ˣ) : l ^ 3 = 1 := by
  have := Fintype.ofFinite K₂
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h := FiniteField.pow_card_sub_one_eq_one (l : K₂) l.ne_zero
  rwa [← Nat.card_eq_fintype_card, hK₂] at h

theorem exists_inv_mul_map_mul_eq_HSL_q2p [Finite k] [Finite K₂] [CharP K₂ 2]
    (hk : Nat.card k = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : k →+* K₂) {A : SL2 k}
    (hA : orderOf A = 3) :
    ∃ P : SL2 K₂, ∃ l : K₂ˣ, 3 ≤ orderOf l ∧
      P⁻¹ * Matrix.SpecialLinearGroup.map ι A * P = HSL l := by
  have : CharP k 2 := charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hk]; rfl)
  have hc := apply_one_zero_ne_zero_of_orderOf_eq (A := A) (by rw [hA, hk])
  have htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) k) = 1 := by
    refine eq_one_of_ne_zero_of_natCard_eq_two_q2p hk fun ht => ?_
    have hA2 : A ^ 2 = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [sq_eq_trace_smul_sub_one, ht, zero_smul, zero_sub, Matrix.neg_apply,
        CharTwo.neg_eq, Matrix.SpecialLinearGroup.coe_one]
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hA2
    omega
  obtain ⟨l, hl⟩ := exists_three_le_orderOf (K := K₂) (by rw [hK₂]; norm_num)
  have hl3 : (l : K₂) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_three_eq_one_of_natCard_eq_four_q2p hK₂ l, Units.val_one]
  obtain ⟨hl1, hl2⟩ := ne_one_and_sq_ne_one_of_three_le_orderOf hl
  have hq : (l : K₂) ^ 2 - (1 : K₂) * l + 1 = 0 := by
    have h1 : ((l : K₂) - 1) * ((l : K₂) ^ 2 + l + 1) = 0 := by linear_combination hl3
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h)) hl1
    · linear_combination h + (-(l : K₂)) * (CharTwo.two_eq_zero : (2 : K₂) = 0)
  have hll : (l : K₂) ≠ ((l⁻¹ : K₂ˣ) : K₂) := by
    intro h
    refine hl2 (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    conv_lhs => rhs; rw [h]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc' :
      ((Matrix.SpecialLinearGroup.map ι A : SL2 K₂) : Matrix (Fin 2) (Fin 2) K₂) 1 0 ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (_root_.map_ne_zero _).2 hc
  have htr' : Matrix.trace ((Matrix.SpecialLinearGroup.map ι A : SL2 K₂) :
      Matrix (Fin 2) (Fin 2) K₂) = 1 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.trace_fin_two,
      Matrix.map_apply, Matrix.map_apply, ← map_add, ← Matrix.trace_fin_two, htr, map_one]
  obtain ⟨P, hP⟩ := exists_inv_mul_mul_eq_HSL _ hc' l (by rw [htr']; exact hq) hll
  exact ⟨P, l, hl, hP⟩

end SL2

section RootSL2

variable {K : Type} [Field K]

theorem rootSL2_HSL_eq_q2pCoroot [CharP K 2] {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (c : Kˣ) :
    CFSG.LieType.Chevalley.rootSL2 .F4 K γ (HSL c) = rootDiagUnit .F4 (q2pCoroot γ c) := by
  obtain ⟨-, -, -, -, -, -, hv, -⟩ := even_Chevalley_pinned_root_SL2_maps .F4 K hγ
  obtain ⟨hh, hr⟩ := hv c
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun δ hδ => ?_)
  · change (rootTorusSL2 .F4 K γ c : Module.End K (RootModule .F4 K)) (hVec .F4 K j) =
      rootDiag (q2pCoroot γ c) (hVec .F4 K j)
    rw [hh, rootDiag_hVec]
  · change (rootTorusSL2 .F4 K γ c : Module.End K (RootModule .F4 K)) (rootVec .F4 K δ) =
      rootDiag (q2pCoroot γ c) (rootVec .F4 K δ)
    rw [hr δ hδ, rootDiag_rootVec _ hδ, rootChar_q2pCoroot hγ]
    rfl

variable {k : Type} [Field k] {K₂ : Type} [Field K₂]

theorem exists_conj_baseChangeGL_eq_q2pCoroot [Finite k] [Finite K₂] [CharP K₂ 2]
    (hk : Nat.card k = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : k →+* K₂)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) {x : ModGL .F4 k}
    (hxJ : x ∈ rootSubgroup .F4 k γ ⊔ rootSubgroup .F4 k (-γ)) (hx : orderOf x = 3) :
    ∃ n ∈ rootSubgroup .F4 K₂ γ ⊔ rootSubgroup .F4 K₂ (-γ), ∃ l : K₂ˣ, 3 ≤ orderOf l ∧
      n⁻¹ * baseChangeGL ι x * n = rootDiagUnit .F4 (q2pCoroot γ l) := by
  have : CharP k 2 := charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hk]; rfl)
  obtain ⟨hinj, hrange, -, -, -, -, -, hbase, -⟩ := even_Chevalley_pinned_root_SL2_maps .F4 k hγ
  obtain ⟨-, hrange₂, -⟩ := even_Chevalley_pinned_root_SL2_maps .F4 K₂ hγ
  rw [← hrange] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  have hA : orderOf A = 3 := by rw [← hx, orderOf_injective _ hinj]
  obtain ⟨P, l, hl, hP⟩ := exists_inv_mul_map_mul_eq_HSL_q2p hk hK₂ ι hA
  refine ⟨CFSG.LieType.Chevalley.rootSL2 .F4 K₂ γ P, hrange₂ ▸ ⟨P, rfl⟩, l, hl, ?_⟩
  rw [hbase K₂ ι A, ← map_inv, ← map_mul, ← map_mul, hP, rootSL2_HSL_eq_q2pCoroot hγ]

end RootSL2

section Commute

variable {K : Type} [Field K]

theorem commute_of_iform_eq_zero_q2p [Finite K] [CharP K 2] {γ δ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) (hδ : IsRoot .F4 δ) (h0 : iform γ δ = 0) {x y : ModGL .F4 K}
    (hx : x ∈ rootSubgroup .F4 K γ) (hy : y ∈ rootSubgroup .F4 K δ) : Commute x y := by
  rcases iform_self_eq_two_or_four_q2p hδ with hδs | hδl
  · rcases iform_self_eq_two_or_four_q2p hγ with hγs | hγl
    · have : CharP K ReeTag.F4.prime := ‹CharP K 2›
      set X : adjointGroup .F4 K := ⟨x, rootSubgroup_le_adjointGroup γ hx⟩ with hXdef
      set Y : adjointGroup .F4 K := ⟨y, rootSubgroup_le_adjointGroup δ hy⟩ with hYdef
      have hX : X ∈ (Adjoint.f4Datum K).rootGroup γ :=
        (mem_rootGroup_iff_pinnedX hγ).2 (mem_rootSubgroup.1 hx)
      have hY : Y ∈ (Adjoint.f4Datum K).rootGroup δ :=
        (mem_rootGroup_iff_pinnedX hδ).2 (mem_rootSubgroup.1 hy)
      have hφX : graphAutF4 K X ∈ (Adjoint.f4Datum K).rootGroup (psiF4 γ) := by
        rw [← map_graphAutF4_rootGroup hγ]
        exact ⟨X, hX, rfl⟩
      have hφY : graphAutF4 K Y ∈ (Adjoint.f4Datum K).rootGroup (psiF4 δ) := by
        rw [← map_graphAutF4_rootGroup hδ]
        exact ⟨Y, hY, rfl⟩
      obtain ⟨c, hc⟩ := (mem_rootGroup_iff_pinnedX (isRoot_psiF4 hγ)).1 hφX
      obtain ⟨d, hd⟩ := (mem_rootGroup_iff_pinnedX (isRoot_psiF4 hδ)).1 hφY
      have hl : iform (psiF4 δ) (psiF4 δ) = 4 := psiF4_iform_check.1 δ (mem_rootFinset.2 hδ) hδs
      have h0' : iform (psiF4 γ) (psiF4 δ) = 0 :=
        psiF4_iform_check.2 γ (mem_rootFinset.2 hγ) δ (mem_rootFinset.2 hδ) h0
      have hcomm : Commute ((graphAutF4 K X : adjointGroup .F4 K) : ModGL .F4 K)
          ((graphAutF4 K Y : adjointGroup .F4 K) : ModGL .F4 K) := by
        rw [← hc, ← hd]
        exact commute_of_iform_eq_zero_of_long (isRoot_psiF4 hγ) (isRoot_psiF4 hδ) hl h0'
          (mem_rootSubgroup.2 ⟨c, rfl⟩) (mem_rootSubgroup.2 ⟨d, rfl⟩)
      have hcomm' : Commute (graphAutF4 K X) (graphAutF4 K Y) := Subtype.ext hcomm.eq
      have hXY := hcomm'.map (graphAutF4 K).symm
      simp only [MulEquiv.symm_apply_apply] at hXY
      exact congrArg Subtype.val hXY.eq
    · exact (commute_of_iform_eq_zero_of_long hδ hγ hγl (by rw [iform_comm]; exact h0) hy hx).symm
  · exact commute_of_iform_eq_zero_of_long hγ hδ hδl h0 hx hy

theorem rootSubgroup_le_centralizer_q2p [Finite K] [CharP K 2] {γ δ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) (hδ : IsRoot .F4 δ) (h0 : iform γ δ = 0) :
    rootSubgroup .F4 K γ ≤ centralizer (rootSubgroup .F4 K δ : Set (ModGL .F4 K)) :=
  fun _ hx => mem_centralizer_iff.2 fun _ hy =>
    (commute_of_iform_eq_zero_q2p hδ hγ (by rw [iform_comm]; exact h0) hy hx).eq

theorem rootPair_le_centralizer_rootPair_q2p [Finite K] [CharP K 2]
    {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (hδ : IsRoot .F4 δ)
    (h0 : iform γ δ = 0) :
    rootSubgroup .F4 K γ ⊔ rootSubgroup .F4 K (-γ) ≤
      centralizer ((rootSubgroup .F4 K δ ⊔ rootSubgroup .F4 K (-δ) : Subgroup (ModGL .F4 K)) :
        Set (ModGL .F4 K)) := by
  have hn : ∀ {a b : Fin (Tag.rank .F4) → ℤ}, iform a b = 0 → iform (-a) b = 0 := fun h => by
    rw [iform_comm, iform_neg_right_amalgam, iform_comm, h, neg_zero]
  have hn' : ∀ {a b : Fin (Tag.rank .F4) → ℤ}, iform a b = 0 → iform a (-b) = 0 := fun h => by
    rw [iform_neg_right_amalgam, h, neg_zero]
  rw [le_centralizer_iff]
  refine sup_le ?_ ?_ <;> rw [← le_centralizer_iff] <;> refine sup_le ?_ ?_
  · exact rootSubgroup_le_centralizer_q2p hγ hδ h0
  · exact rootSubgroup_le_centralizer_q2p (IsRoot.neg hγ) hδ (hn h0)
  · exact rootSubgroup_le_centralizer_q2p hγ (IsRoot.neg hδ) (hn' h0)
  · exact rootSubgroup_le_centralizer_q2p (IsRoot.neg hγ) (IsRoot.neg hδ) (hn (hn' h0))

end Commute

section TorusGen

@[expose] def Q2pTorusGen (Γ : Fin 3 → Fin (Tag.rank .F4) → ℤ) (j : Fin (Tag.rank .F4))
    (m : Fin (Tag.rank .F4) → Fin 3 → ℤ) : Prop :=
  ∀ i l : Fin (Tag.rank .F4), i ≠ j →
    (∑ k, m i k * corootPair (Γ k) (Pi.single l 1) - if i = l then 1 else 0) % 3 = 0

variable {K : Type} [Field K]

theorem zpow_eq_zpow_of_emod_q2p {G : Type*} [Group G] {c : G} (hc : c ^ 3 = 1) {a b : ℤ}
    (h : (a - b) % 3 = 0) : c ^ a = c ^ b := by
  obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
  have hc3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc
  rw [show a = b + 3 * t by omega, zpow_add, zpow_mul, hc3, one_zpow, mul_one]

theorem mulSingle_eq_prod_q2pCoroot {Γ : Fin 3 → Fin (Tag.rank .F4) → ℤ}
    {j : Fin (Tag.rank .F4)} {m : Fin (Tag.rank .F4) → Fin 3 → ℤ} (hm : Q2pTorusGen Γ j m)
    {c : Kˣ} (hc : c ^ 3 = 1) {i : Fin (Tag.rank .F4)} (hij : i ≠ j) :
    Pi.mulSingle i c = ∏ k, q2pCoroot (Γ k) (c ^ m i k) := by
  funext l
  rw [Finset.prod_apply]
  simp only [q2pCoroot, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  have h := hm i l hij
  rw [zpow_eq_zpow_of_emod_q2p hc h]
  by_cases hil : i = l
  · subst hil
    rw [ite_eq_left rfl, zpow_one, Pi.mulSingle_eq_same]
  · rw [ite_eq_right hil, zpow_zero, Pi.mulSingle_eq_of_ne (Ne.symm hil)]

theorem mem_of_q2pTorusGen (hc3 : ∀ c : Kˣ, c ^ 3 = 1) {Γ : Fin 3 → Fin (Tag.rank .F4) → ℤ}
    {j : Fin (Tag.rank .F4)} {m : Fin (Tag.rank .F4) → Fin 3 → ℤ} (hm : Q2pTorusGen Γ j m)
    {H : Subgroup (Fin (Tag.rank .F4) → Kˣ)} (hH : ∀ k c, q2pCoroot (Γ k) c ∈ H)
    {b : Fin (Tag.rank .F4) → Kˣ} (hb : b j = 1) : b ∈ H := by
  rw [← Finset.univ_prod_mulSingle b]
  refine Subgroup.prod_mem _ fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    rw [hb, Pi.mulSingle_one]
    exact one_mem H
  · rw [mulSingle_eq_prod_q2pCoroot hm (hc3 _) hij]
    exact Subgroup.prod_mem _ fun k _ => hH k _

end TorusGen

section Model

theorem rootDiagUnitHom_apply_q2p {K : Type} [Field K] (b : Fin (Tag.rank .F4) → Kˣ) :
    rootDiagUnitHom .F4 K b = rootDiagUnit .F4 b :=
  rfl

theorem rootPair_le_rootSpan_orthRoots_q2p {K : Type} [Field K] {θ δ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) (h0 : iform θ δ = 0) :
    rootSubgroup .F4 K δ ⊔ rootSubgroup .F4 K (-δ) ≤ rootSpan .F4 K (orthRoots θ) :=
  sup_le (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots θ) => rootSubgroup .F4 K α) δ ⟨hδ, h0⟩
      le_rfl)
    (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots θ) => rootSubgroup .F4 K α) (-δ)
      ⟨IsRoot.neg hδ, by rw [iform_neg_right_amalgam, h0, neg_zero]⟩ le_rfl)

theorem rootPair_le_adjointGroup_q2p {K : Type} [Field K] (δ : Fin (Tag.rank .F4) → ℤ) :
    rootSubgroup .F4 K δ ⊔ rootSubgroup .F4 K (-δ) ≤ adjointGroup .F4 K :=
  sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)

theorem map_baseChangeGL_rootPair_le_q2p {k K₂ : Type} [Field k] [Field K₂] (ι : k →+* K₂)
    (γ : Fin (Tag.rank .F4) → ℤ) :
    (rootSubgroup .F4 k γ ⊔ rootSubgroup .F4 k (-γ)).map (baseChangeGL ι) ≤
      rootSubgroup .F4 K₂ γ ⊔ rootSubgroup .F4 K₂ (-γ) := by
  have hU : ∀ α : Fin (Tag.rank .F4) → ℤ,
      (rootSubgroup .F4 k α).map (baseChangeGL ι) ≤ rootSubgroup .F4 K₂ α := by
    intro α
    rw [rootSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    rw [baseChangeGL_pinnedX]
    exact subset_closure ⟨ι c, rfl⟩
  rw [Subgroup.map_sup]
  exact sup_le_sup (hU _) (hU _)

theorem rootSpan_amalgamRoots_le_centralizer_rootPair_q2p {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : Fin (Tag.rank .F4) → ℤ} {j : Fin (Tag.rank .F4)} (hγ : IsRoot .F4 γ)
    (hj : iform γ (Pi.single j 1) = 0) :
    rootSpan .F4 K (amalgamRoots {j}) ≤
      centralizer ((rootSubgroup .F4 K γ ⊔ rootSubgroup .F4 K (-γ) : Subgroup (ModGL .F4 K)) :
        Set (ModGL .F4 K)) := by
  refine iSup₂_le fun α hα => ?_
  have hαr : IsRoot .F4 α := isRoot_of_mem_amalgamRoots hα
  obtain ⟨j', hj', hα'⟩ := hα
  rw [Finset.mem_singleton] at hj'
  subst hj'
  have h0 : iform α γ = 0 := by
    rcases hα' with rfl | rfl
    · rw [iform_comm]
      exact hj
    · rw [iform_comm, iform_neg_right_amalgam, hj, neg_zero]
  exact le_sup_left.trans (rootPair_le_centralizer_rootPair_q2p hαr hγ h0)

theorem perfectCore_rootSpan_orthRoots_inf_centralizer_eq {k K₂ : Type} [Field k] [Field K₂]
    [Finite k] [Finite K₂] [CharP K₂ 2] (hk : Nat.card k = 2) (hK₂ : Nat.card K₂ = 2 ^ 2)
    (ι : k →+* K₂) {θ γ₁ γ₂ : Fin (Tag.rank .F4) → ℤ} {j : Fin (Tag.rank .F4)}
    {m : Fin (Tag.rank .F4) → Fin 3 → ℤ} (hθ : IsRoot .F4 θ) (hγ₁ : IsRoot .F4 γ₁)
    (hγ₂ : IsRoot .F4 γ₂) (h12 : iform γ₁ γ₂ = 0) (hθ₁ : iform θ γ₁ = 0) (hθ₂ : iform θ γ₂ = 0)
    (hjθ : iform θ (Pi.single j 1) = 0) (hj₁ : iform γ₁ (Pi.single j 1) = 0)
    (hj₂ : iform γ₂ (Pi.single j 1) = 0) (hm : Q2pTorusGen ![θ, γ₁, γ₂] j m)
    {W₁ W₂ : Subgroup (ModGL .F4 k)}
    (hW₁ : W₁ ≤ rootSubgroup .F4 k γ₁ ⊔ rootSubgroup .F4 k (-γ₁))
    (hW₂ : W₂ ≤ rootSubgroup .F4 k γ₂ ⊔ rootSubgroup .F4 k (-γ₂))
    (hc₁ : IsCyclic W₁) (hc₂ : IsCyclic W₂) (h3₁ : Nat.card W₁ = 3) (h3₂ : Nat.card W₂ = 3) :
    perfectCore (rootSpan .F4 K₂ (orthRoots θ) ⊓
      centralizer (((W₁ ⊔ W₂).map (baseChangeGL ι) : Subgroup (ModGL .F4 K₂)) :
        Set (ModGL .F4 K₂))) =
      rootSpan .F4 K₂ (amalgamRoots {j}) := by
  have : Finite (ModGL .F4 K₂) := finite_modGL
  have hK₂4 : 4 ≤ Nat.card K₂ := by rw [hK₂]; norm_num
  have hc3 : ∀ c : K₂ˣ, c ^ 3 = 1 := pow_three_eq_one_of_natCard_eq_four_q2p hK₂
  set J₁ := rootSubgroup .F4 K₂ γ₁ ⊔ rootSubgroup .F4 K₂ (-γ₁) with hJ₁
  set J₂ := rootSubgroup .F4 K₂ γ₂ ⊔ rootSubgroup .F4 K₂ (-γ₂) with hJ₂
  have hWJ : (W₁ ⊔ W₂).map (baseChangeGL ι) ≤ J₁ ⊔ J₂ := by
    rw [Subgroup.map_sup]
    exact sup_le_sup ((Subgroup.map_mono hW₁).trans (map_baseChangeGL_rootPair_le_q2p ι γ₁))
      ((Subgroup.map_mono hW₂).trans (map_baseChangeGL_rootPair_le_q2p ι γ₂))
  have hKJ : rootSpan .F4 K₂ (amalgamRoots {j}) ≤
      centralizer ((J₁ ⊔ J₂ : Subgroup (ModGL .F4 K₂)) : Set (ModGL .F4 K₂)) := by
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_ <;> rw [← le_centralizer_iff]
    · exact rootSpan_amalgamRoots_le_centralizer_rootPair_q2p hγ₁ hj₁
    · exact rootSpan_amalgamRoots_le_centralizer_rootPair_q2p hγ₂ hj₂
  refine le_antisymm ?_ (le_perfectCore_of_perfect (le_inf ?_ (hKJ.trans (centralizer_le hWJ)))
    (commutator_rootSpan_amalgamRoots_eq_of_four_le hK₂4 {j}))
  swap
  · exact rootSpan_amalgamRoots_le_orthRoots fun j' hj' => by
      rw [Finset.mem_singleton] at hj'
      subst hj'
      exact hjθ
  set H := rootSpan .F4 K₂ (orthRoots θ) ⊓
    centralizer (((W₁ ⊔ W₂).map (baseChangeGL ι) : Subgroup (ModGL .F4 K₂)) :
      Set (ModGL .F4 K₂)) with hH
  set P := perfectCore H with hPdef
  have hPperf : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect H
  have hPH : P ≤ H := perfectCore_le H
  have hPθ : P ≤ rootSpan .F4 K₂ (orthRoots θ) := hPH.trans inf_le_left
  have hPC : P ≤ adjointGroup .F4 K₂ := hPθ.trans (rootSpan_le_adjointGroup K₂ _)
  obtain ⟨x₁, hx₁W, hW₁eq⟩ := exists_eq_zpowers_of_isCyclic hc₁
  obtain ⟨x₂, hx₂W, hW₂eq⟩ := exists_eq_zpowers_of_isCyclic hc₂
  have ho₁ : orderOf x₁ = 3 := by rw [← Nat.card_zpowers, ← hW₁eq, h3₁]
  have ho₂ : orderOf x₂ = 3 := by rw [← Nat.card_zpowers, ← hW₂eq, h3₂]
  have hPx₁ : ∀ g ∈ P, baseChangeGL ι x₁ * g = g * baseChangeGL ι x₁ := fun g hg =>
    mem_centralizer_iff.1 (hPH hg).2 _ ⟨x₁, mem_sup_left hx₁W, rfl⟩
  have hPx₂ : ∀ g ∈ P, baseChangeGL ι x₂ * g = g * baseChangeGL ι x₂ := fun g hg =>
    mem_centralizer_iff.1 (hPH hg).2 _ ⟨x₂, mem_sup_right hx₂W, rfl⟩
  obtain ⟨n₁, hn₁J, l₁, hl₁, hn₁⟩ :=
    exists_conj_baseChangeGL_eq_q2pCoroot hk hK₂ ι hγ₁ (hW₁ hx₁W) ho₁
  obtain ⟨n₂, hn₂J, l₂, hl₂, hn₂⟩ :=
    exists_conj_baseChangeGL_eq_q2pCoroot hk hK₂ ι hγ₂ (hW₂ hx₂W) ho₂
  have hA : n₂ * rootDiagUnit .F4 (q2pCoroot γ₁ l₁) = rootDiagUnit .F4 (q2pCoroot γ₁ l₁) * n₂ :=
    mem_centralizer_singleton_iff.1 (rootSpan_orthRoots_le_centralizer_q2pCoroot hγ₁ subset_rfl l₁
      (rootPair_le_rootSpan_orthRoots_q2p hγ₂ h12 hn₂J))
  have hB : n₁ * baseChangeGL ι x₂ = baseChangeGL ι x₂ * n₁ := by
    have hx₂J : baseChangeGL ι x₂ ∈ J₂ :=
      map_baseChangeGL_rootPair_le_q2p ι γ₂ ⟨x₂, hW₂ hx₂W, rfl⟩
    exact (mem_centralizer_iff.1 (rootPair_le_centralizer_rootPair_q2p hγ₁ hγ₂ h12 hn₁J) _
      hx₂J).symm
  set n := n₁ * n₂ with hn
  have hnC : n ∈ adjointGroup .F4 K₂ :=
    mul_mem (rootPair_le_adjointGroup_q2p γ₁ hn₁J) (rootPair_le_adjointGroup_q2p γ₂ hn₂J)
  have hc₁' : n⁻¹ * baseChangeGL ι x₁ * n = rootDiagUnit .F4 (q2pCoroot γ₁ l₁) := by
    calc n⁻¹ * baseChangeGL ι x₁ * n = n₂⁻¹ * (n₁⁻¹ * baseChangeGL ι x₁ * n₁) * n₂ := by
          rw [hn]; group
      _ = rootDiagUnit .F4 (q2pCoroot γ₁ l₁) := by
          rw [hn₁, mul_assoc, ← hA, inv_mul_cancel_left]
  have hc₂' : n⁻¹ * baseChangeGL ι x₂ * n = rootDiagUnit .F4 (q2pCoroot γ₂ l₂) := by
    calc n⁻¹ * baseChangeGL ι x₂ * n = n₂⁻¹ * (n₁⁻¹ * (baseChangeGL ι x₂ * n₁)) * n₂ := by
          rw [hn]; group
      _ = rootDiagUnit .F4 (q2pCoroot γ₂ l₂) := by rw [← hB, inv_mul_cancel_left, hn₂]
  have hθn : ∀ c : K₂ˣ, n * rootDiagUnit .F4 (q2pCoroot θ c) =
      rootDiagUnit .F4 (q2pCoroot θ c) * n := fun c =>
    mem_centralizer_singleton_iff.1 (mul_mem
      (rootSpan_orthRoots_le_centralizer_q2pCoroot hθ subset_rfl c
        (rootPair_le_rootSpan_orthRoots_q2p hγ₁ hθ₁ hn₁J))
      (rootSpan_orthRoots_le_centralizer_q2pCoroot hθ subset_rfl c
        (rootPair_le_rootSpan_orthRoots_q2p hγ₂ hθ₂ hn₂J)))
  have hθP : ∀ g ∈ P, ∀ c : K₂ˣ, g * rootDiagUnit .F4 (q2pCoroot θ c) =
      rootDiagUnit .F4 (q2pCoroot θ c) * g := fun g hg c =>
    mem_centralizer_singleton_iff.1
      (rootSpan_orthRoots_le_centralizer_q2pCoroot hθ subset_rfl c (hPθ hg))
  have hcard : Nat.card K₂ˣ = 3 := by rw [Nat.card_units, hK₂]; norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hgen : ∀ l : K₂ˣ, 3 ≤ orderOf l → ∀ c : K₂ˣ, c ∈ zpowers l := fun l hl _ =>
    mem_zpowers_of_prime_card hcard (ne_one_and_sq_ne_one_of_three_le_orderOf hl).1
  set P' := P.map (MulAut.conj n⁻¹).toMonoidHom with hP'
  have hP'perf : ⁅P', P'⁆ = P' := by rw [hP', ← map_commutator, hPperf]
  have hP'le : P' ≤ adjointGroup .F4 K₂ ⊓
      centralizer (leviTorusOf K₂ ⊤ {j} : Set (ModGL .F4 K₂)) := by
    rintro _ ⟨g, hg, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hnC) (hPC hg)) hnC, ?_⟩
    have hcomm : ∀ y : ModGL .F4 K₂, Commute y g → Commute y n → Commute y (n⁻¹ * g * n) :=
      fun y h1 h2 => (h2.inv_right.mul_right h1).mul_right h2
    have hconj : ∀ x : ModGL .F4 K₂, Commute x g → Commute (n⁻¹ * x * n) (n⁻¹ * g * n) :=
      fun x h => by
        have h' := h.map (MulAut.conj n⁻¹)
        simp only [MulAut.conj_apply, inv_inv] at h'
        exact h'
    have hH : ∀ (a : Fin 3) (c : K₂ˣ), q2pCoroot (![θ, γ₁, γ₂] a) c ∈
        (centralizer {n⁻¹ * g * n}).comap (rootDiagUnitHom .F4 K₂) := by
      intro a c
      rw [mem_comap, mem_centralizer_singleton_iff]
      fin_cases a
      · show rootDiagUnit .F4 (q2pCoroot θ c) * (n⁻¹ * g * n) =
          n⁻¹ * g * n * rootDiagUnit .F4 (q2pCoroot θ c)
        exact (hcomm _ (show Commute g _ from hθP g hg c).symm
          (show Commute n _ from hθn c).symm).eq
      · show rootDiagUnit .F4 (q2pCoroot γ₁ c) * (n⁻¹ * g * n) =
          n⁻¹ * g * n * rootDiagUnit .F4 (q2pCoroot γ₁ c)
        obtain ⟨z, rfl⟩ := mem_zpowers_iff.1 (hgen l₁ hl₁ c)
        rw [q2pCoroot_zpow, ← rootDiagUnitHom_apply_q2p, map_zpow, rootDiagUnitHom_apply_q2p,
          ← hc₁']
        exact (Commute.zpow_left (hconj _ (hPx₁ g hg)) z).eq
      · show rootDiagUnit .F4 (q2pCoroot γ₂ c) * (n⁻¹ * g * n) =
          n⁻¹ * g * n * rootDiagUnit .F4 (q2pCoroot γ₂ c)
        obtain ⟨z, rfl⟩ := mem_zpowers_iff.1 (hgen l₂ hl₂ c)
        rw [q2pCoroot_zpow, ← rootDiagUnitHom_apply_q2p, map_zpow, rootDiagUnitHom_apply_q2p,
          ← hc₂']
        exact (Commute.zpow_left (hconj _ (hPx₂ g hg)) z).eq
    rw [mem_centralizer_iff]
    intro t ht
    obtain ⟨b, hb, rfl⟩ := mem_leviTorusOf.1 ht
    have hbH := mem_of_q2pTorusGen hc3 hm hH (hb.1 j (Finset.mem_singleton_self j))
    exact mem_centralizer_singleton_iff.1 (mem_comap.1 hbH)
  have hP'K : P' ≤ rootSpan .F4 K₂ (amalgamRoots {j}) := by
    have hA3 : 3 ≤ Nat.card (⊤ : Subgroup K₂ˣ) := by
      rw [Subgroup.card_top, Nat.card_units]
      omega
    have h := perfectCore_le_rootSpan_amalgamRoots_of_le hA3
      (J := {j}) (by rw [Finset.card_singleton]; norm_num) hP'le
    rwa [CFSG.Quasithin.perfectCore_eq_self_of_perfect hP'perf] at h
  intro g hg
  have hg' : n⁻¹ * g * n ∈ rootSpan .F4 K₂ (amalgamRoots {j}) :=
    hP'K ⟨g, hg, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hy := mem_centralizer_iff.1 (hKJ hg') n (mul_mem (mem_sup_left hn₁J) (mem_sup_right hn₂J))
  have hgg : g = n⁻¹ * g * n := by
    calc g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      _ = n⁻¹ * g * n * n * n⁻¹ := by rw [hy]
      _ = n⁻¹ * g * n := by group
  rw [hgg]
  exact hg'

end Model

end CFSG.SeitzReduction.F4Pilot
