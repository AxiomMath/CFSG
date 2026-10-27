module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoNonCubeFrame
public import CFSG.LieType.SeitzGeneration.UnitaryNonCubeMixing
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.LieType.SeitzGeneration.TwoNonCube

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LieType.SeitzGeneration.ONExt
  CFSG.LieType.SeitzGeneration.UnitaryTwo

section ON

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.SeitzGeneration.Nonsplit CFSG.LieType.BorelTits

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem linearIndependent_of_isON {σ : K ≃+* K} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ι → Fin n → K} (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0) :
    LinearIndependent K c := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrArg (herm σ (c j)) hg
  rw [herm_sum_right] at this
  simpa [herm_smul_right, hc] using this

theorem exists_ON_family (hU : UnitaryFieldData ℓ f K) (W : Submodule K (Fin n → K))
    (hW : ((idForm hU n).domRestrict₁₂ W W).SeparatingLeft) :
    ∃ (d : ℕ) (b : Fin d → Fin n → K),
      (∀ i j, herm (unitaryInvolution K ℓ f) (b i) (b j) = if i = j then 1 else 0) ∧
        Submodule.span K (Set.range b) = W := by
  have hB : (idForm hU n).IsSymm := idForm_isSymm hU n
  obtain ⟨b, hb⟩ := hU.exists_orthonormal_basis (hB.domRestrict W) hW
  refine ⟨Module.finrank K W, fun i => (b i : Fin n → K), fun i j => ?_, ?_⟩
  · have := hb i j
    rw [LinearMap.domRestrict₁₂_apply, idForm_eq_herm] at this
    exact this
  · have h1 : Submodule.span K (Set.range fun i => (b i : Fin n → K)) =
        (Submodule.span K (Set.range b)).map W.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_ON_family_with (hU : UnitaryFieldData ℓ f K) (W : Submodule K (Fin n → K))
    (hW : ((idForm hU n).domRestrict₁₂ W W).SeparatingLeft) {u : Fin n → K} (hu : u ∈ W)
    (hu1 : herm (unitaryInvolution K ℓ f) u u = 1) :
    ∃ (d : ℕ) (b : Option (Fin d) → Fin n → K),
      (∀ i j, herm (unitaryInvolution K ℓ f) (b i) (b j) = if i = j then 1 else 0) ∧
        b none = u ∧ Submodule.span K (Set.range b) = W ∧ d + 1 = Module.finrank K W := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution hU
  set W' : Submodule K (Fin n → K) := W ⊓ LinearMap.ker (hermL σ₀ u) with hW'
  have hW'mem : ∀ z, z ∈ W' ↔ z ∈ W ∧ herm σ₀ u z = 0 := fun z => by
    rw [hW', Submodule.mem_inf, LinearMap.mem_ker, hermL_apply]
  have hdecomp : ∀ w ∈ W, w - herm σ₀ u w • u ∈ W' := fun w hw => by
    rw [hW'mem]
    refine ⟨W.sub_mem hw (W.smul_mem _ hu), ?_⟩
    rw [herm_sub_right, herm_smul_right, hu1, mul_one, sub_self]
  have hW'sep : ((idForm hU n).domRestrict₁₂ W' W').SeparatingLeft := by
    intro z hz
    have hzW : (z : Fin n → K) ∈ W := ((hW'mem _).1 z.2).1
    have hzu : herm σ₀ u z = 0 := ((hW'mem _).1 z.2).2
    have hzu' : herm σ₀ (z : Fin n → K) u = 0 := herm_eq_zero_comm σ₀ hσ.invol hzu
    have h0 : (⟨(z : Fin n → K), hzW⟩ : W) = 0 := by
      apply hW
      intro w
      rw [LinearMap.domRestrict₁₂_apply]
      show idForm hU n (z : Fin n → K) (w : Fin n → K) = 0
      rw [idForm_eq_herm]
      have h1 := hz ⟨_, hdecomp _ w.2⟩
      rw [LinearMap.domRestrict₁₂_apply] at h1
      change idForm hU n (z : Fin n → K) ((w : Fin n → K) - herm σ₀ u w • u) = 0 at h1
      rw [idForm_eq_herm, herm_sub_right, herm_smul_right, hzu', mul_zero, sub_zero] at h1
      exact h1
    apply Subtype.ext
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨d, b', hb', hspan'⟩ := exists_ON_family hU W' hW'sep
  have hb'mem : ∀ i, b' i ∈ W' := fun i => hspan' ▸ Submodule.subset_span ⟨i, rfl⟩
  let b : Option (Fin d) → Fin n → K := fun o => o.elim u (fun i => b' i)
  have hb : ∀ i j, herm σ₀ (b i) (b j) = if i = j then 1 else 0 := by
    rintro (i | i) (j | j)
    · simpa [b] using hu1
    · have := ((hW'mem _).1 (hb'mem j)).2
      simp [b, this]
    · have := herm_eq_zero_comm σ₀ hσ.invol ((hW'mem _).1 (hb'mem i)).2
      simp [b, this]
    · simp [b, hb' i j]
  have hspan : Submodule.span K (Set.range b) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨o, rfl⟩
      cases o with
      | none => exact hu
      | some i => exact ((hW'mem _).1 (hb'mem i)).1
    · intro w hw
      have h1 : w = herm σ₀ u w • u + (w - herm σ₀ u w • u) := by abel
      rw [h1]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)) ?_
      have h2 : (w - herm σ₀ u w • u) ∈ Submodule.span K (Set.range b') := by
        rw [hspan']
        exact hdecomp w hw
      exact Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩
        exact ⟨some i, rfl⟩) h2
  refine ⟨d, b, hb, rfl, hspan, ?_⟩
  have := finrank_span_eq_card (linearIndependent_of_isON hb)
  rw [hspan, Fintype.card_option, Fintype.card_fin] at this
  omega

@[expose] def GoodBlock (σ : K ≃+* K) (W : Submodule K (Fin n → K)) : Prop :=
  (∃ (m : ℕ) (x : Fin m → Fin n → K), IsON σ x ∧ Submodule.span K (Set.range x) = W ∧ 3 ≤ m) ∧
  ∀ u ∈ W, herm σ u u = 1 → ∃ (d : ℕ) (b : Option (Fin d) → Fin n → K),
    (∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) ∧ b none = u ∧
      Submodule.span K (Set.range b) = W ∧ 2 ≤ d

theorem goodBlock_of_sep (hU : UnitaryFieldData ℓ f K) (W : Submodule K (Fin n → K))
    (hW : ((idForm hU n).domRestrict₁₂ W W).SeparatingLeft) (hdim : 3 ≤ Module.finrank K W) :
    GoodBlock (unitaryInvolution K ℓ f) W := by
  refine ⟨?_, ?_⟩
  · obtain ⟨d, b, hb, hspan⟩ := exists_ON_family hU W hW
    refine ⟨d, b, hb, hspan, ?_⟩
    have := finrank_span_eq_card (linearIndependent_of_isON hb)
    rw [hspan, Fintype.card_fin] at this
    omega
  · intro u hu hu1
    obtain ⟨d, b, hb, hnone, hspan, hd⟩ := exists_ON_family_with hU W hW hu hu1
    exact ⟨d, b, hb, hnone, hspan, by omega⟩

end ON

section Blocks

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {ω : K} {H : Subgroup (SUid σ n)}
  {Y : Matrix (Fin n) (Fin n) K}

theorem exists_isotropic_pairing_of_ON (hσ : IsUnitaryInvolution σ) {W : Submodule K (Fin n → K)}
    (hW : ∃ (m : ℕ) (x : Fin m → Fin n → K), IsON σ x ∧ Submodule.span K (Set.range x) = W ∧
      3 ≤ m) {w : Fin n → K} (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ w₀ ∈ W, herm σ w₀ w₀ = 0 ∧ herm σ w w₀ ≠ 0 := by
  obtain ⟨m, x, hx, hspan, hm3⟩ := hW
  obtain ⟨c', rfl⟩ := (mem_span_range_iff x w).1 (hspan ▸ hw)
  have hc' : c' ≠ 0 := fun h => hw0 (by rw [h, map_zero])
  obtain ⟨a₀, ha₀0, ha₀⟩ := exists_isotropic_ne_zero hσ (by omega : 2 ≤ m)
  obtain ⟨d, hdi, -, hcd⟩ := exists_cno hσ ha₀0 ha₀ hc'
  refine ⟨orthoEmb x d, hspan ▸ orthoEmb_mem_span x d, ?_, ?_⟩
  · rw [herm_orthoEmb hx]
    exact hdi
  · rw [herm_orthoEmb hx]
    exact hcd

theorem span_range_sum_elim {α β : Type*} (a : α → Fin n → K) (b : β → Fin n → K) :
    Submodule.span K (Set.range (Sum.elim a b)) =
      Submodule.span K (Set.range a) ⊔ Submodule.span K (Set.range b) := by
  rw [Set.Sum.elim_range, Submodule.span_union]

theorem allCenters_sup_two (hK : Field4 σ ω)
    (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    (hH : ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    {A B : Submodule K (Fin n → K)} (hAB : ∀ a ∈ A, ∀ b ∈ B, herm σ a b = 0)
    {la lb : K} (hla : σ la * la = 1) (hlb : σ lb * lb = 1)
    (hYA : ∀ a ∈ A, Y *ᵥ a = la • a) (hYB : ∀ b ∈ B, Y *ᵥ b = lb • b)
    (hA : GoodBlock σ A) (hB : GoodBlock σ B)
    (hmix : ∃ a ∈ A, ∃ b ∈ B, a ≠ 0 ∧ b ≠ 0 ∧ IsCenter H (a + b)) :
    AllCenters H (A ⊔ B) ∧ HasONBasis σ (A ⊔ B) := by
  classical
  have hσ := hK.invol.invol
  obtain ⟨⟨m₁, x, hx, hxA, hm₁⟩, hAext⟩ := hA
  obtain ⟨⟨m₂, y, hy, hyB, hm₂⟩, hBext⟩ := hB
  have hxA' : ∀ i, x i ∈ A := fun i => hxA ▸ Submodule.subset_span ⟨i, rfl⟩
  have hyB' : ∀ j, y j ∈ B := fun j => hyB ▸ Submodule.subset_span ⟨j, rfl⟩
  have cA : ∀ v ∈ A, herm σ v v = 0 → IsCenter H v := fun v hv hvi =>
    NonCube.isCenter_of_eigen_matrix hσ hH hY hvi hla (hYA v hv)
  have cB : ∀ v ∈ B, herm σ v v = 0 → IsCenter H v := fun v hv hvi =>
    NonCube.isCenter_of_eigen_matrix hσ hH hY hvi hlb (hYB v hv)
  have B3 : Blocks3 σ H x y :=
    ⟨hx, hy, fun i j => hAB _ (hxA' i) _ (hyB' j), hm₁, hm₂,
      fun c hc => cA _ (hxA ▸ orthoEmb_mem_span x c) (by rw [herm_orthoEmb hx]; exact hc),
      fun d hd => cB _ (hyB ▸ orthoEmb_mem_span y d) (by rw [herm_orthoEmb hy]; exact hd)⟩
  obtain ⟨a₀, ha₀, b₀, hb₀, ha0, hb0, hC₀⟩ := hmix
  obtain ⟨c₀, rfl⟩ := (mem_span_range_iff x a₀).1 (hxA ▸ ha₀)
  obtain ⟨d₀, rfl⟩ := (mem_span_range_iff y b₀).1 (hyB ▸ hb₀)
  obtain ⟨c, d, hc1, hd1, hC⟩ := exists_unit_center hK B3
    ⟨c₀, d₀, fun h => ha0 (by rw [h, map_zero]), fun h => hb0 (by rw [h, map_zero]), hC₀⟩
  have hw₁A : orthoEmb x c ∈ A := hxA ▸ orthoEmb_mem_span x c
  have hw₂B : orthoEmb y d ∈ B := hyB ▸ orthoEmb_mem_span y d
  have hw₁1 : herm σ (orthoEmb x c) (orthoEmb x c) = 1 := by rw [herm_orthoEmb hx]; exact hc1
  have hw₂1 : herm σ (orthoEmb y d) (orthoEmb y d) = 1 := by rw [herm_orthoEmb hy]; exact hd1
  obtain ⟨dA, bA, hbA, hbA0, hbAspan, hdA⟩ := hAext _ hw₁A hw₁1
  obtain ⟨dB, bB, hbB, hbB0, hbBspan, hdB⟩ := hBext _ hw₂B hw₂1
  have hbA' : ∀ o, bA o ∈ A := fun o => hbAspan ▸ Submodule.subset_span ⟨o, rfl⟩
  have hbB' : ∀ o, bB o ∈ B := fun o => hbBspan ▸ Submodule.subset_span ⟨o, rfl⟩
  have hC' : IsCenter H (bA none + bB none) := by rw [hbA0, hbB0]; exact hC
  let cf : Option (Fin dA) ⊕ Option (Fin dB) → Fin n → K := Sum.elim bA bB
  have hcf : ∀ i j, herm σ (cf i) (cf j) = if i = j then 1 else 0 := by
    rintro (i | i) (j | j)
    · simp [cf, hbA i j]
    · simp [cf, hAB _ (hbA' i) _ (hbB' j)]
    · simp [cf, herm_eq_zero_comm σ hσ (hAB _ (hbA' j) _ (hbB' i))]
    · simp [cf, hbB i j]
  have hAA : ∀ o o' : Option (Fin dA), o ≠ o' → IsCenter H (bA o + bA o') := by
    intro o o' hoo
    refine cA _ (A.add_mem (hbA' o) (hbA' o')) ?_
    simp only [herm_add_left, herm_add_right, herm_self_of_isON hbA,
      herm_eq_zero_of_isON hbA hoo, herm_eq_zero_of_isON hbA hoo.symm]
    linear_combination hK.two
  have hBB : ∀ o o' : Option (Fin dB), o ≠ o' → IsCenter H (bB o + bB o') := by
    intro o o' hoo
    refine cB _ (B.add_mem (hbB' o) (hbB' o')) ?_
    simp only [herm_add_left, herm_add_right, herm_self_of_isON hbB,
      herm_eq_zero_of_isON hbB hoo, herm_eq_zero_of_isON hbB hoo.symm]
    linear_combination hK.two
  have hAB' : ∀ o : Option (Fin dA), IsCenter H (bA o + bB none) := by
    intro o
    cases o with
    | none => exact hC'
    | some s =>
      have hOn : IsON σ ![bA none, bA (some s)] :=
        isON_two hσ (herm_self_of_isON hbA _) (herm_self_of_isON hbA _)
          (herm_eq_zero_of_isON hbA (by simp))
      have hg := swap2_mem hK hY hH hOn (l := la) (hYA _ (hbA' _)) (hYA _ (hbA' _))
      have := hC'.map hg
      rwa [smul_add, swap2_smul_fst, swap2_smul_of_orth hK hOn (hAB _ (hbA' _) _ (hbB' _))
        (hAB _ (hbA' _) _ (hbB' _))] at this
  have hBA' : ∀ o : Option (Fin dB), IsCenter H (bA none + bB o) := by
    intro o
    cases o with
    | none => exact hC'
    | some s =>
      have hOn : IsON σ ![bB none, bB (some s)] :=
        isON_two hσ (herm_self_of_isON hbB _) (herm_self_of_isON hbB _)
          (herm_eq_zero_of_isON hbB (by simp))
      have hg := swap2_mem hK hY hH hOn (l := lb) (hYB _ (hbB' _)) (hYB _ (hbB' _))
      have := hC'.map hg
      rwa [smul_add, swap2_smul_fst, swap2_smul_of_orth hK hOn
        (herm_eq_zero_comm σ hσ (hAB _ (hbA' _) _ (hbB' _)))
        (herm_eq_zero_comm σ hσ (hAB _ (hbA' _) _ (hbB' _)))] at this
  have hdA' : 0 < dA := by omega
  have hdA'' : 1 < dA := by omega
  have hdB' : 0 < dB := by omega
  let τ : Fin 5 → Option (Fin dA) ⊕ Option (Fin dB) :=
    ![Sum.inl none, Sum.inl (some ⟨0, hdA'⟩), Sum.inl (some ⟨1, hdA''⟩), Sum.inr none,
      Sum.inr (some ⟨0, hdB'⟩)]
  have hτ : Function.Injective τ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert hij; simp [τ])
  let x5 : Fin 5 → Fin n → K := fun s => cf (τ s)
  have hx5 : IsON σ x5 := isON_comp_inj hcf hτ
  have hP : ∀ i j : Fin 4, i ≠ j → IsCenter H (x5 i.castSucc + x5 j.castSucc) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hAA none (some ⟨0, hdA'⟩) (by simp)
    · exact hAA none (some ⟨1, hdA''⟩) (by simp)
    · exact hAB' none
    · exact hAA (some ⟨0, hdA'⟩) none (by simp)
    · exact absurd rfl hij
    · exact hAA (some ⟨0, hdA'⟩) (some ⟨1, hdA''⟩) (by simp)
    · exact hAB' (some ⟨0, hdA'⟩)
    · exact hAA (some ⟨1, hdA''⟩) none (by simp)
    · exact hAA (some ⟨1, hdA''⟩) (some ⟨0, hdA'⟩) (by simp)
    · exact absurd rfl hij
    · exact hAB' (some ⟨1, hdA''⟩)
    · have := hAB' none
      rwa [add_comm] at this
    · have := hAB' (some ⟨0, hdA'⟩)
      rwa [add_comm] at this
    · have := hAB' (some ⟨1, hdA''⟩)
      rwa [add_comm] at this
    · exact absurd rfl hij
  have hD : ∀ h : IsON σ ![x5 0, x5 1, x5 2], dft3 hK h ∈ H := fun h =>
    dft3_mem hK hY hH h (l := la) (hYA _ (hbA' none)) (hYA _ (hbA' (some ⟨0, hdA'⟩)))
      (hYA _ (hbA' (some ⟨1, hdA''⟩)))
  have hS : ∀ (i : Fin 4) (h : IsON σ ![x5 i.castSucc, x5 4]) (t : K) (ht : t ≠ 0),
      scale2 hK h ht ∈ H := by
    intro i h t ht
    have h4 : Y *ᵥ x5 4 = lb • x5 4 := hYB _ (hbB' (some ⟨0, hdB'⟩))
    fin_cases i
    · exact scale2_mem hK hY hH h (lu := la) (lv := lb) (hYA _ (hbA' none)) h4 ht
    · exact scale2_mem hK hY hH h (lu := la) (lv := lb) (hYA _ (hbA' (some ⟨0, hdA'⟩))) h4 ht
    · exact scale2_mem hK hY hH h (lu := la) (lv := lb) (hYA _ (hbA' (some ⟨1, hdA''⟩))) h4 ht
    · exact scale2_mem hK hY hH h (lu := lb) (lv := lb) (hYB _ (hbB' none)) h4 ht
  have hblk := allCenters_blk4 hK hx5 hP hD hS
  let S₀ : Finset (Option (Fin dA) ⊕ Option (Fin dB)) :=
    Finset.univ.image (fun s : Fin 4 => τ s.castSucc)
  have hinj : Function.Injective (fun s : Fin 4 => τ s.castSucc) := fun a b h =>
    Fin.castSucc_injective 4 (hτ h)
  have hS₀card : S₀.card = 4 := by
    rw [show S₀ = Finset.univ.image (fun s : Fin 4 => τ s.castSucc) from rfl,
      Finset.card_image_of_injective _ hinj]
    simp
  have hS₀span : spanS cf S₀ = Submodule.span K (Set.range (blk4 x5)) := by
    unfold spanS
    congr 1
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨τ s.castSucc, Finset.mem_coe.2 (Finset.mem_image.2 ⟨s, Finset.mem_univ _, rfl⟩), rfl⟩
  have hpt : ∀ j, j ∉ S₀ → ∃ u ∈ spanS cf S₀, herm σ u u = 1 ∧ IsCenter H (u + cf j) := by
    rintro (o | o) -
    · refine ⟨bB none, Submodule.subset_span ⟨Sum.inr none, ?_, rfl⟩,
        herm_self_of_isON hbB _, ?_⟩
      · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨3, Finset.mem_univ _, rfl⟩)
      · have := hAB' o
        rwa [add_comm] at this
    · refine ⟨bA none, Submodule.subset_span ⟨Sum.inl none, ?_, rfl⟩,
        herm_self_of_isON hbA _, hBA' o⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩)
  have hgrow := allCenters_grow hK hcf (S₀ := S₀) (by omega) (by rw [hS₀span]; exact hblk) hpt
    Finset.univ
  rw [Finset.union_eq_right.2 (Finset.subset_univ _)] at hgrow
  have hall : spanS cf Finset.univ = A ⊔ B := by
    rw [spanS, Finset.coe_univ, Set.image_univ, span_range_sum_elim, hbAspan, hbBspan]
  have hcard : 4 ≤ Fintype.card (Option (Fin dA) ⊕ Option (Fin dB)) := by
    simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
    omega
  refine ⟨hall ▸ hgrow, ?_⟩
  have := hasONBasis_of_family hσ hcf hcard
  rwa [span_range_sum_elim, hbAspan, hbBspan] at this

theorem allCenters_sup_one (hK : Field4 σ ω)
    (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    (hH : ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    {W C : Submodule K (Fin n → K)} (hWC : ∀ w ∈ W, ∀ c ∈ C, herm σ w c = 0)
    (hW : HasONBasis σ W) (hWA : AllCenters H W) {lc : K} (hlc : σ lc * lc = 1)
    (hYC : ∀ c ∈ C, Y *ᵥ c = lc • c) (hC : GoodBlock σ C)
    (hmix : ∃ w ∈ W, ∃ c ∈ C, w ≠ 0 ∧ c ≠ 0 ∧ IsCenter H (w + c)) :
    AllCenters H (W ⊔ C) ∧ HasONBasis σ (W ⊔ C) := by
  classical
  have hσ := hK.invol.invol
  obtain ⟨m₁, x, hx, hxW, hm₁'⟩ := hW
  have hm₁ : 4 ≤ m₁ := by
    rcases hm₁' with h | ⟨-, s, hs0, hs⟩
    · exact h
    · exact absurd (hK.norm_one s hs0) hs
  obtain ⟨⟨m₂, y, hy, hyC, hm₂⟩, hCext⟩ := hC
  have hxW' : ∀ i, x i ∈ W := fun i => hxW ▸ Submodule.subset_span ⟨i, rfl⟩
  have hyC' : ∀ j, y j ∈ C := fun j => hyC ▸ Submodule.subset_span ⟨j, rfl⟩
  have cC : ∀ v ∈ C, herm σ v v = 0 → IsCenter H v := fun v hv hvi =>
    NonCube.isCenter_of_eigen_matrix hσ hH hY hvi hlc (hYC v hv)
  have B3 : Blocks3 σ H x y :=
    ⟨hx, hy, fun i j => hWC _ (hxW' i) _ (hyC' j), by omega, hm₂,
      fun c hc => hWA _ (hxW ▸ orthoEmb_mem_span x c) (by rw [herm_orthoEmb hx]; exact hc),
      fun d hd => cC _ (hyC ▸ orthoEmb_mem_span y d) (by rw [herm_orthoEmb hy]; exact hd)⟩
  obtain ⟨w₀, hw₀, c₀', hc₀', hw0, hc0, hC₀⟩ := hmix
  obtain ⟨a₀, rfl⟩ := (mem_span_range_iff x w₀).1 (hxW ▸ hw₀)
  obtain ⟨b₀, rfl⟩ := (mem_span_range_iff y c₀').1 (hyC ▸ hc₀')
  obtain ⟨c, d, hc1, hd1, hC1⟩ := exists_unit_center hK B3
    ⟨a₀, b₀, fun h => hw0 (by rw [h, map_zero]), fun h => hc0 (by rw [h, map_zero]), hC₀⟩
  have hw₁W : orthoEmb x c ∈ W := hxW ▸ orthoEmb_mem_span x c
  have hw₂C : orthoEmb y d ∈ C := hyC ▸ orthoEmb_mem_span y d
  have hw₁1 : herm σ (orthoEmb x c) (orthoEmb x c) = 1 := by rw [herm_orthoEmb hx]; exact hc1
  have hw₂1 : herm σ (orthoEmb y d) (orthoEmb y d) = 1 := by rw [herm_orthoEmb hy]; exact hd1
  obtain ⟨dC, bC, hbC, hbC0, hbCspan, hdC⟩ := hCext _ hw₂C hw₂1
  have hbC' : ∀ o, bC o ∈ C := fun o => hbCspan ▸ Submodule.subset_span ⟨o, rfl⟩
  have hC1' : IsCenter H (orthoEmb x c + bC none) := by rw [hbC0]; exact hC1
  let cf : Fin m₁ ⊕ Option (Fin dC) → Fin n → K := Sum.elim x bC
  have hcf : ∀ i j, herm σ (cf i) (cf j) = if i = j then 1 else 0 := by
    rintro (i | i) (j | j)
    · simp [cf, hx i j]
    · simp [cf, hWC _ (hxW' i) _ (hbC' j)]
    · simp [cf, herm_eq_zero_comm σ hσ (hWC _ (hxW' j) _ (hbC' i))]
    · simp [cf, hbC i j]
  have hWC' : ∀ o : Option (Fin dC), IsCenter H (orthoEmb x c + bC o) := by
    intro o
    cases o with
    | none => exact hC1'
    | some s =>
      have hOn : IsON σ ![bC none, bC (some s)] :=
        isON_two hσ (herm_self_of_isON hbC _) (herm_self_of_isON hbC _)
          (herm_eq_zero_of_isON hbC (by simp))
      have hg := swap2_mem hK hY hH hOn (l := lc) (hYC _ (hbC' _)) (hYC _ (hbC' _))
      have := hC1'.map hg
      rwa [smul_add, swap2_smul_fst, swap2_smul_of_orth hK hOn
        (herm_eq_zero_comm σ hσ (hWC _ hw₁W _ (hbC' _)))
        (herm_eq_zero_comm σ hσ (hWC _ hw₁W _ (hbC' _)))] at this
  let S₀ : Finset (Fin m₁ ⊕ Option (Fin dC)) := Finset.univ.image Sum.inl
  have hS₀card : S₀.card = m₁ := by
    rw [show S₀ = Finset.univ.image Sum.inl from rfl,
      Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  have hS₀span : spanS cf S₀ = W := by
    rw [← hxW]
    unfold spanS
    congr 1
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Sum.inl i, Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩), rfl⟩
  have hpt : ∀ j, j ∉ S₀ → ∃ u ∈ spanS cf S₀, herm σ u u = 1 ∧ IsCenter H (u + cf j) := by
    rintro (i | o) hj
    · exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩) hj
    · exact ⟨orthoEmb x c, by rw [hS₀span]; exact hw₁W, hw₁1, hWC' o⟩
  have hgrow := allCenters_grow hK hcf (S₀ := S₀) (by omega) (by rw [hS₀span]; exact hWA) hpt
    Finset.univ
  rw [Finset.union_eq_right.2 (Finset.subset_univ _)] at hgrow
  have hall : spanS cf Finset.univ = W ⊔ C := by
    rw [spanS, Finset.coe_univ, Set.image_univ, span_range_sum_elim, hxW, hbCspan]
  have hcard : 4 ≤ Fintype.card (Fin m₁ ⊕ Option (Fin dC)) := by
    simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
    omega
  refine ⟨hall ▸ hgrow, ?_⟩
  have := hasONBasis_of_family hσ hcf hcard
  rwa [span_range_sum_elim, hxW, hbCspan] at this

end Blocks

end CFSG.LieType.SeitzGeneration.TwoNonCube
