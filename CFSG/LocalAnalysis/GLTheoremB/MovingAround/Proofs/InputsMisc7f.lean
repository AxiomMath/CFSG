module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7e
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Weight

variable {τ : Tag} {K : Type} [Field K]

theorem coord_eq_zero_of_commute_diag {M g : ModGL τ K} (χ : Label τ → K)
    (hg : ∀ b, (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) = χ b • Finsupp.single b 1)
    (hMg : M * g = g * M) {a b : Label τ} (hab : χ a ≠ χ b) :
    (M : Module.End K (RootModule τ K)) (Finsupp.single b 1) a = 0 := by
  have hdiag : ∀ v : RootModule τ K, (g : Module.End K (RootModule τ K)) v a = χ a * v a := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
    | single c r =>
      have hs : Finsupp.single c r = r • Finsupp.single c (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, hg, smul_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
        smul_eq_mul]
      by_cases hca : c = a
      · subst hca
        rw [Finsupp.single_eq_same]
        ring
      · rw [Finsupp.single_apply, if_neg hca, mul_zero, mul_zero, mul_zero]
  have h1 := congrArg (fun f : ModGL τ K => (f : Module.End K (RootModule τ K))
    (Finsupp.single b 1) a) hMg
  simp only [Units.val_mul, Module.End.mul_apply] at h1
  rw [hg, map_smul, Finsupp.smul_apply, smul_eq_mul, hdiag] at h1
  have h2 : (χ a - χ b) * (M : Module.End K (RootModule τ K)) (Finsupp.single b 1) a = 0 := by
    rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) hab
  · exact h

@[expose] def diagChar (a : Fin τ.rank → Kˣ) : Label τ → K
  | .inl _ => 1
  | .inr α => ((rootChar a α.1 : Kˣ) : K)

theorem rootDiagUnit_apply_single (a : Fin τ.rank → Kˣ) (b : Label τ) :
    (rootDiagUnit τ a : Module.End K (RootModule τ K)) (Finsupp.single b 1) =
      diagChar a b • Finsupp.single b 1 := by
  rcases b with i | α
  · change rootDiag a (Finsupp.single (Sum.inl i) 1) = _
    rw [rootDiag_single_inl]
    simp [diagChar]
  · change rootDiag a (Finsupp.single (Sum.inr α) 1) = _
    rw [rootDiag_single_inr]
    rfl

end Weight

section Support

variable {τ : Tag} {K : Type} [Field K]

@[expose] def SupportedBy (r : Label τ → Label τ → Prop) (A : Module.End K (RootModule τ K)) : Prop :=
  ∀ a b : Label τ, A (Finsupp.single b 1) a ≠ 0 → r a b

theorem SupportedBy.mul {r s : Label τ → Label τ → Prop} {A B : Module.End K (RootModule τ K)}
    (hA : SupportedBy r A) (hB : SupportedBy s B) :
    SupportedBy (fun a b => ∃ x, r a x ∧ s x b) (A * B) := fun a b hab => by
  rw [Module.End.mul_apply, ← Finsupp.sum_single (B (Finsupp.single b 1)), Finsupp.sum,
    map_sum, Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  exact ⟨c, hA a c (right_ne_zero_of_mul hc'), hB c b (Finsupp.mem_support_iff.mp hc)⟩

theorem SupportedBy.mono {r s : Label τ → Label τ → Prop} {A : Module.End K (RootModule τ K)}
    (hA : SupportedBy r A) (h : ∀ a b, r a b → s a b) : SupportedBy s A := fun a b hab =>
  h a b (hA a b hab)

@[expose] def wRel (w : WeylGroup τ) : Label τ → Label τ → Prop
  | a, .inl _ => a.isLeft
  | a, .inr β => a = .inr ⟨w • β.1, CFSG.LieType.Chevalley.IsRoot.smul β.2 w⟩

theorem wRel_comp {w w' : WeylGroup τ} {a b x : Label τ} (h₁ : wRel w a x) (h₂ : wRel w' x b) :
    wRel (w * w') a b := by
  rcases b with j | β
  · rcases x with i | γ
    · exact h₁
    · exact absurd h₂ (by simp [wRel])
  · simp only [wRel] at h₂
    subst h₂
    simp only [wRel] at h₁ ⊢
    rw [h₁]
    congr 2
    rw [mul_smul]

@[expose] def IsSupp (w : WeylGroup τ) (A : Module.End K (RootModule τ K)) : Prop :=
  SupportedBy (wRel w) A

theorem IsSupp.mul {w w' : WeylGroup τ} {A B : Module.End K (RootModule τ K)} (hA : IsSupp w A)
    (hB : IsSupp w' B) : IsSupp (w * w') (A * B) :=
  (SupportedBy.mul hA hB).mono fun _ _ ⟨_, h₁, h₂⟩ => wRel_comp h₁ h₂

theorem isSupp_one : IsSupp (1 : WeylGroup τ) (1 : Module.End K (RootModule τ K)) := by
  intro a b hab
  rw [Module.End.one_apply, Finsupp.single_apply] at hab
  have hba : b = a := by
    by_contra h
    exact hab (if_neg h)
  subst hba
  rcases b with j | β
  · rfl
  · simp only [wRel, one_smul]

theorem IsSupp.of_mapsRootLines {w : WeylGroup τ} {g : ModGL τ K}
    (hg : MapsRootLines g w)
    (hh : ∀ j (a : Label τ), (g : Module.End K (RootModule τ K)) (hVec τ K j) a ≠ 0 → a.isLeft) :
    IsSupp w (g : Module.End K (RootModule τ K)) := by
  intro a b hab
  rcases b with j | ⟨β, hβ⟩
  · exact hh j a hab
  · obtain ⟨c, hc⟩ := hg β hβ
    rw [← rootVec_eq_single_of_isRoot hβ, hc,
      rootVec_eq_single_of_isRoot (CFSG.LieType.Chevalley.IsRoot.smul hβ w),
      Finsupp.smul_apply, Finsupp.single_apply] at hab
    by_contra h
    exact hab (by rw [if_neg (Ne.symm h), smul_zero])

theorem isSupp_weylElt (i : Fin τ.rank)
    (t : Kˣ) : IsSupp (simple τ i) (weylElt τ K i t : Module.End K (RootModule τ K)) := by
  refine IsSupp.of_mapsRootLines (fun β hβ => ?_) fun j a hab => ?_
  · refine ⟨((-1) ^ stringDown τ i β : Kˣ) * t ^ (-∑ j, τ.cartan i j * β j), ?_⟩
    rw [weylElt_rootVec i t hβ, simple_smul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one]
  · rw [weylElt_hVec, hVec, hVec, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.single_apply, Finsupp.single_apply] at hab
    by_contra h
    rcases a with k | γ
    · exact h rfl
    · exact hab (by simp)

theorem weylElt_inv_eq (i : Fin τ.rank)
    (t : Kˣ) : (weylElt τ K i t)⁻¹ = weylElt τ K i (-t) := by
  refine Units.ext ?_
  rw [coe_weylElt_inv, coe_weylElt]
  congr 3
  simp

theorem isSupp_list_prod
    (ω : List (Fin τ.rank)) (t : Kˣ) :
    IsSupp ((coxeterSystem τ).wordProd ω)
      (((ω.map fun i => weylElt τ K i t).prod : ModGL τ K) : Module.End K (RootModule τ K)) := by
  induction ω with
  | nil => simpa using (isSupp_one (K := K) (τ := τ))
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, (coxeterSystem τ).wordProd_cons, Units.val_mul]
    exact (isSupp_weylElt i t).mul ih

theorem isSupp_canonicalRep
    (w : WeylGroup τ) :
    IsSupp w (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K)) ∧
      IsSupp w⁻¹ (((canonicalRep (coxeterSystem τ) K w)⁻¹ : ModGL τ K) :
        Module.End K (RootModule τ K)) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  refine ⟨isSupp_list_prod ω 1, ?_⟩
  have h : ((ω.map fun i => weylElt τ K i 1).prod)⁻¹ =
      (ω.reverse.map fun i => weylElt τ K i (-1)).prod := by
    rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
    congr 2
    exact List.map_congr_left fun i _ => by simp [weylElt_inv_eq]
  rw [h, ← (coxeterSystem τ).wordProd_reverse]
  exact isSupp_list_prod ω.reverse (-1)

end Support

section Graded

variable {τ : Tag} {K : Type} [Field K]

@[expose] def IsGraded (A : Module.End K (RootModule τ K)) : Prop :=
  ∀ a b : Label τ, A (Finsupp.single b 1) a ≠ 0 → a.weight = b.weight

open Classical in
@[expose] def wtPos (a : Label τ) : ℕ :=
  (Finset.univ.filter fun x : Label τ => a.weight < x.weight).card

theorem wtPos_le_of_weight_le {a b : Label τ} (h : b.weight ≤ a.weight) : wtPos a ≤ wtPos b := by
  classical
  unfold wtPos
  exact Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact lt_of_le_of_lt h hx

theorem weight_le_of_wtPos_le {a b : Label τ} (h : wtPos a ≤ wtPos b) : b.weight ≤ a.weight := by
  classical
  by_contra h''
  have h' : a.weight < b.weight := lt_of_not_ge h''
  have : wtPos b < wtPos a := by
    unfold wtPos
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).2 ⟨b, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact h'.trans hx
    · simpa using h'
    · simp
  omega

theorem raisesPos_wtPos_of_isGraded {A : Module.End K (RootModule τ K)} (hA : IsGraded A) :
    RaisesPos wtPos 0 A := fun a b hab => by
  rw [add_zero]
  exact wtPos_le_of_weight_le (hA a b hab).ge

theorem raisesPos_wtPos_of_isUpperTriangular
    {A : Module.End K (RootModule τ K)} (hA : IsUpperTriangular τ K A) :
    RaisesPos wtPos 0 A := fun a b hab => by
  rw [add_zero]
  by_cases hab' : a = b
  · rw [hab']
  · rcases Label.precedes_or_precedes hab' with h | h
    · refine wtPos_le_of_weight_le ?_
      rcases h with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    · exact absurd (hA a b h) hab

theorem height_single' (i : Fin τ.rank) : height (Pi.single i (1 : ℤ)) = 1 := by
  simp [height, Pi.single_apply]

@[expose] def IsRL (A : Module.End K (RootModule τ K)) : Prop := IsSupp (1 : WeylGroup τ) A

theorem IsRL.isGraded {A : Module.End K (RootModule τ K)} (hA : IsRL A) : IsGraded A := by
  intro a b hab
  have h := hA a b hab
  rcases b with j | β
  · rcases a with i | α
    · rfl
    · exact absurd h (by simp [wRel])
  · simp only [wRel, one_smul] at h
    rw [h]

theorem mem_borelGroup_of_isGraded {c : ModGL τ K} (hcC : c ∈ adjointGroup τ K)
    (hc : IsGraded (c : Module.End K (RootModule τ K))) : c ∈ borelGroup τ K := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hc' : c ∈ (adjointGroup τ K : Set (ModGL τ K)) := hcC
  rw [adjointGroup_eq_iUnion_bruhatCell, Set.mem_iUnion] at hc'
  obtain ⟨w, hw⟩ := hc'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hup : ∀ x ∈ borelGroup τ K, RaisesPos wtPos 0 (x : Module.End K (RootModule τ K)) :=
    fun x hx => raisesPos_wtPos_of_isUpperTriangular (hTB.2.2.2.2.2.2.2.2.2.1 x hx)
  have hneq : n = b⁻¹ * (b * n * b') * b'⁻¹ := by group
  have hnR : RaisesPos wtPos 0 (n : Module.End K (RootModule τ K)) := by
    rw [hneq, Units.val_mul, Units.val_mul]
    exact ((hup _ (inv_mem hb)).mul (raisesPos_wtPos_of_isGraded hc)).mul (hup _ (inv_mem hb'))
  have hw1 : w = 1 := by
    by_contra hw1
    obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition τ).2.2.2 w hw1
    obtain ⟨u, hu⟩ := mapsRootLines_canonicalRep (R := K) w (Pi.single i 1) (isRoot_single τ i)
    have hcoord : (n : Module.End K (RootModule τ K))
        (Finsupp.single (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩) 1)
        (Sum.inr ⟨w • Pi.single i 1, hroot⟩) ≠ 0 := by
      rw [← rootVec_eq_single_of_isRoot (isRoot_single τ i), hn, hu,
        rootVec_eq_single_of_isRoot hroot, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
      exact u.ne_zero
    have h1 := weight_le_of_wtPos_le (by simpa using hnR _ _ hcoord)
    simp only [Label.weight, height_single'] at h1
    omega
  rw [hn, hw1, canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem mem_torusGroup_of_isRL {c : ModGL τ K} (hcC : c ∈ adjointGroup τ K)
    (hc : IsRL (c : Module.End K (RootModule τ K))) : c ∈ torusGroup τ K := by
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element τ
  set n₀ := canonicalRep (coxeterSystem τ) K w₀ with hn₀
  have hn₀C : n₀ ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w₀
  have hB : c ∈ borelGroup τ K := mem_borelGroup_of_isGraded hcC hc.isGraded
  have hc'C : n₀⁻¹ * c * n₀ ∈ adjointGroup τ K := mul_mem (mul_mem (inv_mem hn₀C) hcC) hn₀C
  obtain ⟨h₁, h₂⟩ := isSupp_canonicalRep (K := K) w₀
  have hc'RL : IsRL ((n₀⁻¹ * c * n₀ : ModGL τ K) : Module.End K (RootModule τ K)) := by
    have := (h₂.mul hc).mul h₁
    rw [show w₀⁻¹ * 1 * w₀ = 1 by group] at this
    simpa only [IsRL, Units.val_mul] using this
  have hB' := mem_borelGroup_of_isGraded hc'C hc'RL.isGraded
  have hBm : c ∈ (borelGroup τ K).map (MulAut.conj n₀).toMonoidHom :=
    ⟨_, hB', by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [(opposite_Borel_intersection τ K w₀ hmax).2.1] at hBm
  rw [← (opposite_Borel_intersection τ K w₀ hmax).2.2.1]
  exact ⟨hB, hBm⟩

end Graded

section Separation

variable {τ : Tag} {K : Type} [Field K]

theorem prod_zpow_eq_zpow_sum' {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι) (x : G)
    (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem rootChar_cartan_row (ω : Kˣ) (j : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    rootChar (fun k => ω ^ τ.cartan j k) α = ω ^ (∑ k, τ.cartan j k * α k) := by
  unfold rootChar
  rw [← prod_zpow_eq_zpow_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul]

theorem isRL_of_commute {ι : Type*} {M : ModGL τ K}
    (D : ι → Fin τ.rank → Kˣ)
    (hM : ∀ k, M * rootDiagUnit τ (D k) = rootDiagUnit τ (D k) * M)
    (hsep : ∀ α β, IsRoot τ α → IsRoot τ β → α ≠ β → ∃ k, rootChar (D k) α ≠ rootChar (D k) β)
    (hne : ∀ α, IsRoot τ α → ∃ k, rootChar (D k) α ≠ 1) :
    IsRL (M : Module.End K (RootModule τ K)) := by
  intro a b hab
  have key : ∀ k, diagChar (D k) a = diagChar (D k) b := by
    intro k
    by_contra h
    exact hab (coord_eq_zero_of_commute_diag (diagChar (D k)) (rootDiagUnit_apply_single (D k))
      (hM k) h)
  rcases a with i | ⟨α, hα⟩ <;> rcases b with j | ⟨β, hβ⟩
  · rfl
  · exfalso
    obtain ⟨k, hk⟩ := hne β hβ
    have h := key k
    simp only [diagChar] at h
    exact hk (Units.val_eq_one.1 h.symm)
  · exfalso
    obtain ⟨k, hk⟩ := hne α hα
    have h := key k
    simp only [diagChar] at h
    exact hk (Units.val_eq_one.1 h)
  · by_cases hαβ : α = β
    · subst hαβ
      simp [wRel]
    · exfalso
      obtain ⟨k, hk⟩ := hsep α β hα hβ hαβ
      have h := key k
      simp only [diagChar] at h
      exact hk (Units.val_injective h)

theorem sep_of_mod_three {ω : Kˣ} (hω : orderOf ω = 3)
    (hsep : ∀ α β, IsRoot τ α → IsRoot τ β →
      (∀ j, (∑ k, τ.cartan j k * α k) % 3 = (∑ k, τ.cartan j k * β k) % 3) → α = β)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαβ : α ≠ β) :
    ∃ j, rootChar (fun k => ω ^ τ.cartan j k) α ≠ rootChar (fun k => ω ^ τ.cartan j k) β := by
  by_contra h
  push Not at h
  refine hαβ (hsep α β hα hβ fun j => ?_)
  have h1 := h j
  rw [rootChar_cartan_row, rootChar_cartan_row, zpow_eq_zpow_iff_modEq, hω] at h1
  exact h1

theorem ne_of_mod_three {ω : Kˣ} (hω : orderOf ω = 3) {α : Fin τ.rank → ℤ}
    (hne : ∃ j, (∑ k, τ.cartan j k * α k) % 3 ≠ 0) :
    ∃ j, rootChar (fun k => ω ^ τ.cartan j k) α ≠ 1 := by
  obtain ⟨j, hj⟩ := hne
  refine ⟨j, fun h => hj ?_⟩
  rw [rootChar_cartan_row, ← zpow_zero ω, zpow_eq_zpow_iff_modEq, hω] at h
  exact h

end Separation

section Torus

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def torus3 (ω : Kˣ) (hω : ω ^ 3 = 1) : Subgroup (adjointGroup τ K) :=
  (CFSG.RankThree.CentralCover.chevTorus τ ω hω).range

theorem isPGroup_torus3 (ω : Kˣ) (hω : ω ^ 3 = 1) : IsPGroup 3 (torus3 (τ := τ) ω hω) := by
  rintro ⟨y, a, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have ha : a ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((3 : ℕ) : ZMod 3) = 0 from by decide, zero_mul]
  rw [SubmonoidClass.coe_pow, pow_one, ← map_pow, ha, map_one]
  rfl

theorem torusElt_mem_torus3 (ω : Kˣ) (hω : ω ^ 3 = 1) (j : Fin τ.rank) :
    (⟨torusElt τ K j ω, torusElt_mem_adjointGroup j ω⟩ : adjointGroup τ K) ∈ torus3 ω hω := by
  refine ⟨Multiplicative.ofAdd ((1 : ZMod 3) • Pi.single j 1), Subtype.ext ?_⟩
  change ((CFSG.LieType.Chevalley.torusCoordHom τ K
    (CFSG.RankThree.CentralCover.chevTorusExp τ ω hω
      (Multiplicative.ofAdd ((1 : ZMod 3) • Pi.single j 1))) : torusGroup τ K) : ModGL τ K) = _
  rw [CFSG.RankThree.CentralCover.chevTorusExp_smul_single, coe_torusCoordHom_mulSingle,
    CFSG.RankThree.CentralCover.zmodPowHom_apply]
  simp [ZMod.val_one]

@[expose] def ConjInto {G : Type*} [Group G] (n : G) (H : Subgroup G) : Prop :=
  ∀ x ∈ H, n * x * n⁻¹ ∈ H

theorem ConjInto.mul {G : Type*} [Group G] {n n' : G} {H : Subgroup G} (h : ConjInto n H)
    (h' : ConjInto n' H) : ConjInto (n * n') H := fun x hx => by
  have := h _ (h' x hx)
  simpa [mul_assoc] using this

theorem ConjInto.pow {G : Type*} [Group G] {n : G} {H : Subgroup G} (h : ConjInto n H) (k : ℕ) :
    ConjInto (n ^ k) H := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => rw [pow_succ]; exact ih.mul h

theorem mem_normalizer_of_conjInto {G : Type*} [Group G] {n : G} {H : Subgroup G} (h : ConjInto n H)
    (hn : n ^ 3 = 1) : n ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := (h.pow 2) _ hx
  have e : n ^ 2 * (n * x * n⁻¹) * (n ^ 2)⁻¹ = x := by
    have hn' : n ^ 2 * n = 1 := by rw [← pow_succ, hn]
    have hinv : n⁻¹ = n ^ 2 := (eq_inv_of_mul_eq_one_left hn').symm
    rw [hinv]
    calc n ^ 2 * (n * x * n ^ 2) * (n ^ 2)⁻¹ = (n ^ 2 * n) * x * (n ^ 2 * (n ^ 2)⁻¹) := by group
      _ = x := by rw [hn', mul_inv_cancel]; group
  rwa [e] at this

theorem conjInto_weylElement (ω : Kˣ) (hω : ω ^ 3 = 1) (i : Fin τ.rank) :
    ConjInto (weylElement τ K i) (torus3 (τ := τ) ω hω) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨_, (CFSG.RankThree.CentralCover.weylElt_conj_chevTorus ω hω i
    (Multiplicative.toAdd a)).symm⟩

@[expose] def SignedLines (g : ModGL τ K) (w : WeylGroup τ) : Prop :=
  ∀ α, IsRoot τ α → (g : Module.End K (RootModule τ K)) (rootVec τ K α) = rootVec τ K (w • α) ∨
    (g : Module.End K (RootModule τ K)) (rootVec τ K α) = -rootVec τ K (w • α)

theorem SignedLines.mul {g g' : ModGL τ K} {w w' : WeylGroup τ} (h : SignedLines g w)
    (h' : SignedLines g' w') : SignedLines (g * g') (w * w') := by
  intro α hα
  have h₁ := h (w' • α) (CFSG.LieType.Chevalley.IsRoot.smul hα w')
  rw [mul_smul]
  rcases h' α hα with e | e <;> rcases h₁ with e' | e' <;>
    simp [Units.val_mul, Module.End.mul_apply, e, e']

theorem signedLines_weylElt (i : Fin τ.rank) : SignedLines (weylElt τ K i 1) (simple τ i) := by
  intro α hα
  rw [weylElt_rootVec i 1 hα, simple_smul, one_zpow, Units.val_one, mul_one]
  rcases neg_one_pow_eq_or K (stringDown τ i α) with h | h <;> rw [h] <;> simp

theorem SignedLines.pow {g : ModGL τ K} {w : WeylGroup τ} (h : SignedLines g w) (k : ℕ) :
    SignedLines (g ^ k) (w ^ k) := by
  induction k with
  | zero =>
    intro α _
    left
    simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem sq_eq_one_of_signedLines {g : ModGL τ K} (h : SignedLines g 1)
    (hh : ∀ j, (g : Module.End K (RootModule τ K)) (hVec τ K j) = hVec τ K j) : g ^ 2 = 1 := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_)
  · rw [pow_two, Units.val_mul, Module.End.mul_apply, hh, hh, Units.val_one, Module.End.one_apply]
  · rw [pow_two, Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply]
    rcases h α hα with e | e <;> rw [one_smul] at e <;> simp [e]

end Torus

theorem exists_conj_fix_of_isPGroup {G : Type*} [Group G] {p : ℕ} (S : Sylow p G)
    [MulAction.IsPretransitive G (Sylow p G)] {R : Subgroup G} (hR : IsPGroup p R) {α : MulAut G}
    (hα : ∀ x ∈ (S : Subgroup G), α x = x) :
    ∃ g : G, ∀ x ∈ R, (MulAut.conj g * α * (MulAut.conj g)⁻¹) x = x := by
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  refine ⟨g, fun x hx => ?_⟩
  have hxP : x ∈ (P : Subgroup G) := hRP hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
  have hfix := hα _ hxP
  simp only [MulAut.mul_apply, MulAut.smul_def, map_inv, MulAut.conj_apply, MulAut.inv_apply,
    MulAut.conj_symm_apply] at hfix ⊢
  rw [hfix]
  group

theorem IsSupp.pow {τ : Tag} {K : Type} [Field K] {w : WeylGroup τ}
    {A : Module.End K (RootModule τ K)} (h : IsSupp w A) (k : ℕ) : IsSupp (w ^ k) (A ^ k) := by
  induction k with
  | zero => simpa using (isSupp_one (K := K) (τ := τ))
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem mapsRootLines_of_signedLines {τ : Tag} {K : Type} [Field K] {g : ModGL τ K}
    {w : WeylGroup τ} (h : SignedLines g w) : MapsRootLines g w := fun α hα => by
  rcases h α hα with e | e
  · exact ⟨1, by rw [e, Units.val_one, one_smul]⟩
  · exact ⟨-1, by rw [e, Units.val_neg, Units.val_one, neg_one_smul]⟩

theorem rootChar_smul_eq_of_commute {τ : Tag} {K : Type} [Field K]
    {v : Fin τ.rank → Kˣ} {n : ModGL τ K} {w : WeylGroup τ}
    (hn : MapsRootLines n w) (hc : rootDiagUnit τ v * n = n * rootDiagUnit τ v) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) : rootChar v (w • β) = rootChar v β := by
  obtain ⟨c, hcβ⟩ := hn β hβ
  have hwβ := CFSG.LieType.Chevalley.IsRoot.smul hβ w
  have h := congrArg (fun f : ModGL τ K => (f : Module.End K (RootModule τ K)) (rootVec τ K β)) hc
  simp only [Units.val_mul, Module.End.mul_apply] at h
  change rootDiag v ((n : Module.End K (RootModule τ K)) (rootVec τ K β)) =
    (n : Module.End K (RootModule τ K)) (rootDiag v (rootVec τ K β)) at h
  rw [hcβ, map_smul, rootDiag_rootVec v hwβ, rootDiag_rootVec v hβ, map_smul, hcβ, smul_smul,
    smul_smul] at h
  have h2 := congrArg (fun x : RootModule τ K => x (Sum.inr ⟨w • β, hwβ⟩)) h
  simp only [rootVec_eq_single_of_isRoot hwβ, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] at h2
  have hc0 : ((c : Kˣ) : K) ≠ 0 := c.ne_zero
  apply Units.val_injective
  rw [mul_comm] at h2
  exact mul_right_cancel₀ hc0 h2

section E6

open CFSG.HardMathSupport.Timmesfeld.CrossChar

local instance e6NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def wE6 : WeylGroup Tag.E6 :=
  simple Tag.E6 0 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 5

theorem wE6_smul (v : Fin Tag.E6.rank → ℤ) :
    wE6 • v = reflect Tag.E6 0 (reflect Tag.E6 2 (reflect Tag.E6 4 (reflect Tag.E6 5 v))) := by
  simp only [wE6, mul_smul, simple_smul]

theorem wE6_pow_three : wE6 ^ 3 = 1 := by
  refine ext_single fun i => ?_
  rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, wE6_smul, wE6_smul, wE6_smul, one_smul]
  fin_cases i <;> decide

theorem wE6_smul_e0 : wE6 • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1 := by
  rw [wE6_smul]; decide

theorem wE6_smul_e2 : wE6 • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) =
    -Pi.single 0 1 - Pi.single 2 1 := by
  rw [wE6_smul]; decide

theorem wE6_smul_e4 : wE6 • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1 := by
  rw [wE6_smul]; decide

theorem wE6_smul_e3 : wE6 • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) =
    Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 := by
  rw [wE6_smul]; decide

theorem e6_sep_check : ∀ m m' : Fin 72,
    (∀ j : Fin 6, (∑ k, Tag.E6.cartan j k * CFSG.RankThree.E6.e6RootVec m k) % 3 =
      (∑ k, Tag.E6.cartan j k * CFSG.RankThree.E6.e6RootVec m' k) % 3) → m = m' := by
  decide +kernel

theorem e6_ne_check : ∀ m : Fin 72, ∃ j : Fin 6,
    (∑ k, Tag.E6.cartan j k * CFSG.RankThree.E6.e6RootVec m k) % 3 ≠ 0 := by
  decide +kernel

theorem e6_sep (α β : Fin Tag.E6.rank → ℤ) (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (h : ∀ j, (∑ k, Tag.E6.cartan j k * α k) % 3 = (∑ k, Tag.E6.cartan j k * β k) % 3) : α = β := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.1 hα
  obtain ⟨m', rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.1 hβ
  rw [e6_sep_check m m' h]

theorem e6_ne (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot Tag.E6 α) :
    ∃ j, (∑ k, Tag.E6.cartan j k * α k) % 3 ≠ 0 := by
  obtain ⟨m, rfl⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.1 hα
  exact e6_ne_check m

variable {K : Type} [Field K]

@[expose] noncomputable def gE6 (K : Type) [Field K] : adjointGroup Tag.E6 K :=
  weylElement Tag.E6 K 0 * weylElement Tag.E6 K 2 * weylElement Tag.E6 K 4 * weylElement Tag.E6 K 5

theorem coe_gE6 : ((gE6 K : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
    weylElt Tag.E6 K 0 1 * weylElt Tag.E6 K 2 1 * weylElt Tag.E6 K 4 1 * weylElt Tag.E6 K 5 1 :=
  rfl

theorem signedLines_gE6 : SignedLines ((gE6 K : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) wE6 := by
  rw [coe_gE6, wE6]
  exact (((signedLines_weylElt 0).mul (signedLines_weylElt 2)).mul
    (signedLines_weylElt 4)).mul (signedLines_weylElt 5)

theorem isSupp_gE6 :
    IsSupp wE6 (((gE6 K : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) := by
  rw [coe_gE6, wE6, Units.val_mul, Units.val_mul, Units.val_mul]
  exact (((isSupp_weylElt 0 1).mul (isSupp_weylElt 2 1)).mul (isSupp_weylElt 4 1)).mul
    (isSupp_weylElt 5 1)

theorem gE6_pow_six : gE6 K ^ 6 = 1 := by
  have h3C : ((gE6 K ^ 3 : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K :=
    (gE6 K ^ 3).2
  have hRL : IsRL (((gE6 K ^ 3 : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) := by
    have := isSupp_gE6 (K := K) |>.pow 3
    rw [wE6_pow_three] at this
    simpa [IsRL, Units.val_pow_eq_pow_val] using this
  have hT := mem_torusGroup_of_isRL h3C hRL
  have hS : SignedLines ((gE6 K ^ 3 : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) 1 := by
    have := (signedLines_gE6 (K := K)).pow 3
    rw [wE6_pow_three] at this
    simpa using this
  have hsq := sq_eq_one_of_signedLines hS (torusGroup_le_diagonalGroup hT).1
  apply Subtype.ext
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, Subgroup.coe_pow, hsq]
  rfl

theorem e6_cartanChar_eq (μ a b : Kˣ) :
    cartanChar (τ := Tag.E6) ![μ * a * b ^ 2, a ^ 2 * b ^ 3, μ * a ^ 2 * b ^ 4, a ^ 3 * b ^ 6,
      μ ^ 2 * a ^ 2 * b ^ 4, a * b ^ 2] = ![μ, a, μ, μ ^ (-3 : ℤ) * b, μ ^ 4, μ ^ (-2 : ℤ)] := by
  set c : Fin 6 → Kˣ := ![μ * a * b ^ 2, a ^ 2 * b ^ 3, μ * a ^ 2 * b ^ 4, a ^ 3 * b ^ 6,
      μ ^ 2 * a ^ 2 * b ^ 4, a * b ^ 2] with hc
  have h0 : cartanChar (τ := Tag.E6) c 0 = μ := by
    change (∏ j : Fin 6, c j ^ (Tag.E6.cartan : Matrix (Fin 6) (Fin 6) ℤ) j 0) = μ
    rw [Fin.prod_univ_six]
    change c 0 ^ (2:ℤ) * c 1 ^ (0:ℤ) * c 2 ^ (-1:ℤ) * c 3 ^ (0:ℤ) * c 4 ^ (0:ℤ) * c 5 ^ (0:ℤ) = μ
    apply Additive.ofMul.injective
    simp [hc]; module
  have h1 : cartanChar (τ := Tag.E6) c 1 = a := by
    change (∏ j : Fin 6, c j ^ (Tag.E6.cartan : Matrix (Fin 6) (Fin 6) ℤ) j 1) = a
    rw [Fin.prod_univ_six]
    change c 0 ^ (0:ℤ) * c 1 ^ (2:ℤ) * c 2 ^ (0:ℤ) * c 3 ^ (-1:ℤ) * c 4 ^ (0:ℤ) * c 5 ^ (0:ℤ) = a
    apply Additive.ofMul.injective
    simp [hc]; module
  have h2 : cartanChar (τ := Tag.E6) c 2 = μ := by
    change (∏ j : Fin 6, c j ^ (Tag.E6.cartan : Matrix (Fin 6) (Fin 6) ℤ) j 2) = μ
    rw [Fin.prod_univ_six]
    change c 0 ^ (-1:ℤ) * c 1 ^ (0:ℤ) * c 2 ^ (2:ℤ) * c 3 ^ (-1:ℤ) * c 4 ^ (0:ℤ) * c 5 ^ (0:ℤ) = μ
    apply Additive.ofMul.injective
    simp [hc]; module
  have h3 : cartanChar (τ := Tag.E6) c 3 = μ ^ (-3 : ℤ) * b := by
    change (∏ j : Fin 6, c j ^ (Tag.E6.cartan : Matrix (Fin 6) (Fin 6) ℤ) j 3) = _
    rw [Fin.prod_univ_six]
    change c 0 ^ (0:ℤ) * c 1 ^ (-1:ℤ) * c 2 ^ (-1:ℤ) * c 3 ^ (2:ℤ) * c 4 ^ (-1:ℤ) * c 5 ^ (0:ℤ) = _
    apply Additive.ofMul.injective
    simp [hc]; module
  have h4 : cartanChar (τ := Tag.E6) c 4 = μ ^ 4 := by
    change (∏ j : Fin 6, c j ^ (Tag.E6.cartan : Matrix (Fin 6) (Fin 6) ℤ) j 4) = _
    rw [Fin.prod_univ_six]
    change c 0 ^ (0:ℤ) * c 1 ^ (0:ℤ) * c 2 ^ (0:ℤ) * c 3 ^ (-1:ℤ) * c 4 ^ (2:ℤ) * c 5 ^ (-1:ℤ) = _
    apply Additive.ofMul.injective
    simp [hc]; module
  have h5 : cartanChar (τ := Tag.E6) c 5 = μ ^ (-2 : ℤ) := by
    change (∏ j : Fin 6, c j ^ (Tag.E6.cartan : Matrix (Fin 6) (Fin 6) ℤ) j 5) = _
    rw [Fin.prod_univ_six]
    change c 0 ^ (0:ℤ) * c 1 ^ (0:ℤ) * c 2 ^ (0:ℤ) * c 3 ^ (0:ℤ) * c 4 ^ (-1:ℤ) * c 5 ^ (2:ℤ) = _
    apply Additive.ofMul.injective
    simp [hc]; module
  funext l
  fin_cases l
  exacts [h0, h1, h2, h3, h4, h5]

theorem isRL_rootDiagUnit {τ : Tag} {K : Type} [Field K] (u : Fin τ.rank → Kˣ) :
    IsRL (rootDiagUnit τ u : Module.End K (RootModule τ K)) := by
  intro a b hab
  rw [rootDiagUnit_apply_single, Finsupp.smul_apply, Finsupp.single_apply] at hab
  have hba : b = a := by
    by_contra h
    exact hab (by rw [if_neg h, smul_zero])
  subst hba
  rcases b with j | β
  · rfl
  · simp only [wRel, one_smul]

theorem rootChar_single' {τ : Tag} {K : Type} [Field K] (v : Fin τ.rank → Kˣ) (k : Fin τ.rank) :
    rootChar v (Pi.single k 1) = v k := by
  have := rootChar_nsmul_single v k 1
  rwa [one_smul, pow_one] at this

end E6

section E6Main

open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

local instance e6NeZeroRank'' : NeZero Tag.E6.rank := ⟨by decide⟩

theorem mE6_pow_three {K : Type} [Field K] : (gE6 K ^ 4) ^ 3 = 1 := by
  rw [← pow_mul, show 4 * 3 = 6 * 2 from rfl, pow_mul, gE6_pow_six, one_pow]

theorem mapsRootLines_mE6 {K : Type} [Field K] :
    MapsRootLines ((gE6 K ^ 4 : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) wE6 := by
  have h := mapsRootLines_of_signedLines ((signedLines_gE6 (K := K)).pow 4)
  rw [show wE6 ^ 4 = wE6 by rw [pow_succ, wE6_pow_three, one_mul]] at h
  simpa only [Subgroup.coe_pow] using h

theorem conjInto_gE6 {K : Type} [Field K] (ω : Kˣ) (hω : ω ^ 3 = 1) :
    ConjInto (gE6 K) (torus3 (τ := Tag.E6) ω hω) :=
  (((conjInto_weylElement ω hω 0).mul (conjInto_weylElement ω hω 2)).mul
    (conjInto_weylElement ω hω 4)).mul (conjInto_weylElement ω hω 5)

theorem rootChar_neg' {τ : Tag} {K : Type} [Field K] (v : Fin τ.rank → Kˣ) (x : Fin τ.rank → ℤ) :
    rootChar v (-x) = (rootChar v x)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem e6InndiagSylowThree_holds : InputsMisc7e.E6InndiagSylowThree := by
  intro K _ _ h3 S α hα _ hfix
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  obtain ⟨ω, hωo⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hω3 : ω ^ 3 = 1 := by rw [← hωo]; exact pow_orderOf_eq_one ω
  set T := torus3 (τ := Tag.E6) (K := K) ω hω3 with hT
  set m := gE6 K ^ 4 with hm
  have hm3 : m ^ 3 = 1 := mE6_pow_three
  have hmN : m ∈ Subgroup.normalizer (T : Set (adjointGroup Tag.E6 K)) :=
    mem_normalizer_of_conjInto ((conjInto_gE6 ω hω3).pow 4) hm3
  have hZ : IsPGroup 3 (Subgroup.zpowers m) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubmonoidClass.coe_pow]
    change (m ^ k) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm3, one_zpow]
  have hR : IsPGroup 3 ↥(T ⊔ Subgroup.zpowers m) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_torus3 ω hω3) hZ (Subgroup.zpowers_le.2 hmN)
  obtain ⟨c, hc⟩ := exists_conj_fix_of_isPGroup S hR hfix
  have hcI : MulAut.conj c ∈ e6Inndiag K := innerAut_le_e6Inndiag K ⟨c, rfl⟩
  have hα'I : MulAut.conj c * α * (MulAut.conj c)⁻¹ ∈ e6Inndiag K :=
    mul_mem (mul_mem hcI hα) (inv_mem hcI)
  rw [← range_e6InndiagConj] at hα'I
  obtain ⟨ĝ, hĝ⟩ := hα'I
  have hcomm : ∀ x ∈ T ⊔ Subgroup.zpowers m,
      (ĝ : ModGL Tag.E6 K) * ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * ĝ := by
    intro x hx
    have h1 := congrArg Subtype.val (hc x hx)
    rw [← hĝ, e6InndiagConj_apply] at h1
    calc (ĝ : ModGL Tag.E6 K) * (x : ModGL Tag.E6 K)
        = ((ĝ : ModGL Tag.E6 K) * x * (ĝ : ModGL Tag.E6 K)⁻¹) * ĝ := by group
      _ = x * ĝ := by rw [h1]
  have hRL : IsRL ((ĝ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) := by
    refine isRL_of_commute (fun j k => ω ^ Tag.E6.cartan j k) (fun j => ?_)
      (fun α β hα hβ hαβ => sep_of_mod_three hωo e6_sep hα hβ hαβ)
      (fun α hα => ne_of_mod_three hωo (e6_ne α hα))
    have h := hcomm _ (Subgroup.mem_sup_left (torusElt_mem_torus3 ω hω3 j))
    change (ĝ : ModGL Tag.E6 K) * torusElt Tag.E6 K j ω = torusElt Tag.E6 K j ω * ĝ at h
    rwa [torusElt_eq_rootDiagUnit] at h
  have hDN : (rootDiagUnitHom Tag.E6 K).range ≤
      Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) := by
    rintro _ ⟨u, rfl⟩
    exact (root_diagonal_conjugation Tag.E6 K u).2.2
  have hĝmem : (ĝ : ModGL Tag.E6 K) ∈
      ((rootDiagUnitHom Tag.E6 K).range ⊔ adjointGroup Tag.E6 K : Subgroup (ModGL Tag.E6 K)) := by
    rw [sup_comm]
    exact ĝ.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDN] at hĝmem
  obtain ⟨d, ⟨u, rfl⟩, c', hc'C, hdc⟩ := hĝmem
  change rootDiagUnit Tag.E6 u * c' = (ĝ : ModGL Tag.E6 K) at hdc
  have hc'eq : c' = rootDiagUnit Tag.E6 u⁻¹ * (ĝ : ModGL Tag.E6 K) := by
    rw [← hdc, ← rootDiagUnit_inv, inv_mul_cancel_left]
  have hc'RL : IsRL (c' : Module.End K (RootModule Tag.E6 K)) := by
    have := (isRL_rootDiagUnit (K := K) u⁻¹).mul hRL
    rw [one_mul] at this
    rw [hc'eq, Units.val_mul]
    exact this
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_torusGroup_of_isRL hc'C hc'RL)
  set v := u * l with hv
  have hĝv : (ĝ : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 v := by
    rw [← hdc, hl, hv, rootDiagUnit_mul]
  have hvm : rootDiagUnit Tag.E6 v * ((m : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (m : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 v := by
    rw [← hĝv]
    exact hcomm m (Subgroup.mem_sup_right (Subgroup.mem_zpowers m))
  have inv : ∀ k, rootChar v (wE6 • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) = v k := fun k => by
    rw [rootChar_smul_eq_of_commute mapsRootLines_mE6 hvm (isRoot_single _ k), rootChar_single']
  have e0 := inv 0
  rw [wE6_smul_e0, rootChar_single'] at e0
  have e2 := inv 2
  rw [wE6_smul_e2, rootChar_sub, rootChar_neg', rootChar_single', rootChar_single'] at e2
  have e4 := inv 4
  rw [wE6_smul_e4, rootChar_single'] at e4
  have e3 := inv 3
  rw [wE6_smul_e3, rootChar_add, rootChar_add, rootChar_add, rootChar_single', rootChar_single',
    rootChar_single', rootChar_single'] at e3
  set μ := v 0 with hμ
  have hμ3 : μ ^ 3 = 1 := by
    rw [e0] at e2
    have : μ⁻¹ * μ⁻¹ * μ⁻¹ = 1 := by rw [e2, mul_inv_cancel]
    rw [← mul_inv, ← mul_inv, inv_eq_one] at this
    rw [pow_three, ← mul_assoc]
    exact this
  have hv4 : v 4 = μ := by
    rw [e0] at e3
    have h1 : μ * μ * v 4 = 1 := by
      refine mul_left_cancel (a := v 3) ?_
      rw [mul_one]
      calc v 3 * (μ * μ * v 4) = μ * μ * v 3 * v 4 := by ac_rfl
        _ = v 3 := e3
    calc v 4 = μ ^ 3 * v 4 := by rw [hμ3, one_mul]
      _ = μ * (μ * μ * v 4) := by rw [pow_three]; ac_rfl
      _ = μ := by rw [h1, mul_one]
  have hveq : v = ![μ, v 1, μ, v 3, μ, μ] := by
    funext k
    fin_cases k
    · rfl
    · rfl
    · exact e0
    · rfl
    · exact hv4
    · exact e4.trans hv4
  set t : Fin Tag.E6.rank → Kˣ := ![μ * v 1 * v 3 ^ 2, v 1 ^ 2 * v 3 ^ 3, μ * v 1 ^ 2 * v 3 ^ 4,
    v 1 ^ 3 * v 3 ^ 6, μ ^ 2 * v 1 ^ 2 * v 3 ^ 4, v 1 * v 3 ^ 2] with ht
  have hcart : cartanChar t = v := by
    have h := e6_cartanChar_eq (K := K) μ (v 1) (v 3)
    have hμ'3 : μ ^ (-3 : ℤ) = 1 := by rw [zpow_neg, zpow_ofNat, hμ3, inv_one]
    have hμ4 : μ ^ 4 = μ := by rw [pow_succ, hμ3, one_mul]
    have hμ'2 : μ ^ (-2 : ℤ) = μ := by
      rw [zpow_neg, zpow_ofNat, inv_eq_iff_eq_inv]
      calc μ ^ 2 = μ ^ 3 * μ⁻¹ := by group
        _ = μ⁻¹ := by rw [hμ3, one_mul]
    rw [hμ'3, one_mul, hμ4, hμ'2, ← hveq] at h
    exact h
  have hmemT : ((List.finRange Tag.E6.rank).map fun j => torusElt Tag.E6 K j (t j)).prod ∈
      adjointGroup Tag.E6 K := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact torusElt_mem_adjointGroup j _
  rw [list_prod_torusElt_eq_rootDiagUnit, hcart, ← hĝv] at hmemT
  have hĝC : (ĝ : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K := hmemT
  have hα' : MulAut.conj c * α * (MulAut.conj c)⁻¹ =
      MulAut.conj (⟨ĝ, hĝC⟩ : adjointGroup Tag.E6 K) := by
    rw [← hĝ]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [e6InndiagConj_apply, MulAut.conj_apply]
    rfl
  have e : α = (MulAut.conj c)⁻¹ * (MulAut.conj c * α * (MulAut.conj c)⁻¹) * MulAut.conj c := by
    group
  rw [e, hα']
  exact mul_mem (mul_mem (inv_mem ⟨c, rfl⟩) ⟨_, rfl⟩) ⟨c, rfl⟩

end E6Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f
