module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.GF2Type.SmithTypeE.L9Cent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.GF2Type.SmithTypeE CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

section Gram

variable {τ : Tag}

theorem iform_add_left' (x y z : Fin τ.rank → ℤ) :
    iform (x + y) z = iform x z + iform y z := by
  simp only [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem iform_add_right' (x y z : Fin τ.rank → ℤ) :
    iform x (y + z) = iform x y + iform x z := by
  simp only [iform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem iform_neg_right' (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem iform_comm' (x y : Fin τ.rank → ℤ) :
    iform x y = iform y x := by
  unfold iform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_symm]
  ring

end Gram

section FrameGram

variable {τ : Tag} {L : Type} [Field L]
  {ν : ℕ} {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem iform_sigma_next (h : IsSLFrame ρ σ) {κ : ℤ}
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) {a b c : Fin ν} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : iform (σ a b) (σ b c) = -κ := by
  have h1 := hnorm a c hac
  rw [← h.add a b c, iform_add_left', iform_add_right', iform_add_right', hnorm a b hab,
    hnorm b c hbc, iform_comm' (σ b c) (σ a b)] at h1
  linarith

theorem iform_sigma_prev (h : IsSLFrame ρ σ) {κ : ℤ}
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) {a b c : Fin ν} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : iform (σ a b) (σ c b) = κ := by
  have h1 := iform_sigma_next h hnorm hab hbc hac
  rw [h.neg b c, iform_neg_right', h1]
  ring

theorem iform_sigma_disjoint (h : IsSLFrame ρ σ) {κ : ℤ}
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) {i j k l : Fin ν} (hij : i ≠ j)
    (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    iform (σ i j) (σ k l) = 0 := by
  have e : σ k l = σ k j + σ j l := (h.add k j l).symm
  rw [e, iform_add_right', iform_sigma_prev h hnorm hij hjk hik,
    iform_sigma_next h hnorm hij hjl hil]
  ring

theorem sigma_injective (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) {i j k l : Fin ν} (hij : i ≠ j)
    (hkl : k ≠ l) (he : σ i j = σ k l) : i = k ∧ j = l := by
  by_contra hno
  have hself : iform (σ i j) (σ k l) = 2 * κ := by rw [← he]; exact hnorm i j hij
  by_cases hik : i = k
  · have hjl : j ≠ l := fun hjl => hno ⟨hik, hjl⟩
    obtain rfl := hik
    have e : σ i l = σ i j + σ j l := (h.add i j l).symm
    have h1 : iform (σ i j) (σ i l) = κ := by
      rw [e, iform_add_right', hnorm i j hij, iform_sigma_next h hnorm hij hjl hkl]; ring
    rw [h1] at hself; apply hκ; linarith
  · by_cases hjl : j = l
    · obtain rfl := hjl
      have h1 : iform (σ i j) (σ k j) = κ := iform_sigma_prev h hnorm hij hkl.symm hik
      rw [h1] at hself; apply hκ; linarith
    · by_cases hjk : j = k
      · obtain rfl := hjk
        by_cases hil : i = l
        · obtain rfl := hil
          have h2 : σ j i = -σ i j := h.neg i j
          rw [h2, iform_neg_right', hnorm i j hij] at hself
          apply hκ; linarith
        · have h1 : iform (σ i j) (σ j l) = -κ := iform_sigma_next h hnorm hij hkl hil
          rw [h1] at hself; apply hκ; linarith
      · by_cases hil : i = l
        · obtain rfl := hil
          have h1 : iform (σ k i) (σ i j) = -κ := iform_sigma_next h hnorm hkl hij (Ne.symm hjk)
          rw [iform_comm' (σ i j) (σ k i), h1] at hself
          apply hκ; linarith
        · have h1 := iform_sigma_disjoint h hnorm hij hkl hik hil hjk hjl
          rw [h1] at hself; apply hκ; linarith

theorem ncard_frameRoots (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) :
    (frameRoots σ).ncard = ν * (ν - 1) := by
  classical
  have himg : frameRoots σ = (fun p : Fin ν × Fin ν => σ p.1 p.2) ''
      ((Finset.univ : Finset (Fin ν)).offDiag : Set (Fin ν × Fin ν)) := by
    ext r
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨(i, j), by simp [hij], rfl⟩
    · rintro ⟨⟨i, j⟩, hp, rfl⟩
      simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.coe_univ, Set.mem_univ, true_and]
        at hp
      exact ⟨i, j, hp, rfl⟩
  have hinj : Set.InjOn (fun p : Fin ν × Fin ν => σ p.1 p.2)
      ((Finset.univ : Finset (Fin ν)).offDiag : Set (Fin ν × Fin ν)) := by
    rintro ⟨i, j⟩ hp ⟨k, l⟩ hq hpq
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.coe_univ, Set.mem_univ, true_and]
      at hp hq
    have := sigma_injective h hκ hnorm hp hq hpq
    exact Prod.ext this.1 this.2
  rw [himg, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset, Finset.offDiag_card,
    Finset.card_univ, Fintype.card_fin, Nat.mul_sub, mul_one]

end FrameGram

section Block

open CFSG.ClassicalInvolution.Models.SymplecticPairs (inclMat)

variable {K : Type} [Field K] {m n : ℕ}

theorem slEmbed_transvection (e : Fin m → Fin n) (he : Function.Injective e) {a c : Fin m}
    (hac : a ≠ c) (t : K) :
    slEmbed e he (Matrix.SpecialLinearGroup.transvection hac t) =
      Matrix.SpecialLinearGroup.transvection (he.ne hac) t := by
  apply Subtype.ext
  change slEmbedMat e ((Matrix.SpecialLinearGroup.transvection hac t : SL(m, K)) :
      Matrix (Fin m) (Fin m) K) = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  unfold slEmbedMat
  congr 1
  ext k l
  simp only [Matrix.mul_apply, Matrix.single_apply, inclMat, Matrix.transpose_apply,
    Matrix.of_apply, mul_ite, ite_mul, one_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply]
  rw [Finset.sum_eq_single c]
  · simp only [Finset.mem_univ, if_true]
    by_cases hl : l = e c
    · rw [if_pos hl, Finset.sum_eq_single a]
      · simp [hl, eq_comm]
      · intro x _ hx
        simp [hx.symm]
      · simp
    · have : ¬ (e a = k ∧ e c = l) := fun h => hl h.2.symm
      rw [if_neg hl, if_neg this]
  · intro j _ hj
    simp [hj.symm]
  · simp

end Block

section BlockFrame

variable {τ : Tag} {L : Type} [Field L]
  {ν m : ℕ} {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem isSLFrame_block (h : IsSLFrame ρ σ) (e : Fin m → Fin ν) (he : Function.Injective e) :
    IsSLFrame (ρ.comp (slEmbed e he)) (fun a b => σ (e a) (e b)) where
  isRoot a b hab := h.isRoot (e a) (e b) (he.ne hab)
  neg a b := h.neg (e a) (e b)
  add a b c := h.add (e a) (e b) (e c)
  transv a b hab := by
    obtain ⟨ε, hε⟩ := h.transv (e a) (e b) (he.ne hab)
    refine ⟨ε, fun t => ?_⟩
    simp only [MonoidHom.comp_apply, slEmbed_transvection]
    exact hε t
  range := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation
        (n := m) (K := L), MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨_, ⟨a, b, hab, t, rfl⟩, rfl⟩
      obtain ⟨ε, hε⟩ := h.transv (e a) (e b) (he.ne hab)
      simp only [MonoidHom.comp_apply, slEmbed_transvection]
      rw [hε t]
      have hr : σ (e a) (e b) ∈ frameRoots (fun a b => σ (e a) (e b)) := ⟨a, b, hab, rfl⟩
      have hle : rootSubgroup τ L (σ (e a) (e b)) ≤
          rootSpan τ L (frameRoots fun a b => σ (e a) (e b)) :=
        le_iSup₂_of_le (f := fun α (_ : α ∈ frameRoots fun a b => σ (e a) (e b)) =>
          rootSubgroup τ L α) (σ (e a) (e b)) hr le_rfl
      exact hle (Subgroup.subset_closure (Set.mem_range_self _))
    · refine iSup₂_le fun r hr => ?_
      obtain ⟨a, b, hab, rfl⟩ := hr
      obtain ⟨ε, hε⟩ := h.transv (e a) (e b) (he.ne hab)
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe]
      refine MonoidHom.mem_range.2 ⟨Matrix.SpecialLinearGroup.transvection hab ((ε⁻¹ : Lˣ) * c), ?_⟩
      simp only [MonoidHom.comp_apply, slEmbed_transvection]
      rw [hε]
      congr 1
      simp

end BlockFrame

section BlockCentralizer

variable
  {τ : Tag} {L : Type} [Field L] {ν m : ℕ} {ρ : SL(ν, L) →* ModGL τ L}
  {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem conjDiagn_one'' (A : SL(m, L)) : conjDiagn (fun _ : Fin m => (1 : Lˣ)) A = A := by
  apply Subtype.ext
  rw [coe_conjDiagn]
  simp [diagGLn]

theorem commute_frame (h : IsSLFrame ρ σ) (hν : 0 < ν) (b : Fin τ.rank → Lˣ)
    (hb : ∀ a c, rootChar b (σ a c) = 1) (A : SL(ν, L)) :
    rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ A := by
  have h1 := h.torus ⟨0, hν⟩ b A
  have h2 : (fun i : Fin ν => rootChar b (σ i ⟨0, hν⟩)) = fun _ => (1 : Lˣ) :=
    funext fun i => hb i ⟨0, hν⟩
  rw [h2, conjDiagn_one''] at h1
  exact h1

theorem commute_block (h : IsSLFrame ρ σ) (e : Fin m → Fin ν) (he : Function.Injective e)
    (hm : 0 < m) (b : Fin τ.rank → Lˣ) (hb : ∀ a c, rootChar b (σ (e a) (e c)) = 1)
    (A : SL(m, L)) :
    rootDiagUnit τ b * ρ (slEmbed e he A) * (rootDiagUnit τ b)⁻¹ = ρ (slEmbed e he A) :=
  commute_frame (isSLFrame_block h e he) hm b hb A

end BlockCentralizer

section Class

variable {τ : Tag} {L : Type} [Field L]
  {ν : ℕ} {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem sigma_self (h : IsSLFrame ρ σ) (i : Fin ν) : σ i i = 0 := by
  have h1 := h.add i i i
  exact add_eq_left.1 h1

theorem rootChar_sigma (h : IsSLFrame ρ σ) (b : Fin τ.rank → Lˣ) (i j k : Fin ν) :
    rootChar b (σ i j) = rootChar b (σ i k) * (rootChar b (σ j k))⁻¹ := by
  rw [h.eq_sub i j k, rootChar_sub]

theorem exists_class_of_connected (h : IsSLFrame ρ σ) {κ : ℤ}
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) (b : Fin τ.rank → Lˣ)
    {C : Set (Fin τ.rank → ℤ)} (hCσ : ∀ γ ∈ C, ∃ i j, i ≠ j ∧ γ = σ i j)
    (hCb : ∀ γ ∈ C, rootChar b γ = 1)
    (hconn : ∀ x ∈ C, ∀ y ∈ C,
      Relation.ReflTransGen (fun a c => a ∈ C ∧ c ∈ C ∧ iform a c ≠ 0) x y)
    {c₀ : Fin τ.rank → ℤ} (hc₀ : c₀ ∈ C) :
    ∃ k₀ : Fin ν, ∀ γ ∈ C, ∃ i j, i ≠ j ∧ γ = σ i j ∧ rootChar b (σ i k₀) = 1 ∧
      rootChar b (σ j k₀) = 1 := by
  obtain ⟨i₀, j₀, hne₀, rfl⟩ := hCσ c₀ hc₀
  refine ⟨i₀, fun γ hγ => ?_⟩
  have key : ∀ y, Relation.ReflTransGen (fun a c => a ∈ C ∧ c ∈ C ∧ iform a c ≠ 0) (σ i₀ j₀) y →
      ∃ i j, i ≠ j ∧ y = σ i j ∧ rootChar b (σ i i₀) = 1 ∧ rootChar b (σ j i₀) = 1 := by
    intro y hy
    induction hy with
    | refl =>
      refine ⟨i₀, j₀, hne₀, rfl, ?_, ?_⟩
      · rw [sigma_self h, rootChar_zero]
      · have h1 := hCb _ hc₀
        have h2 := rootChar_sigma h b j₀ i₀ j₀
        rw [sigma_self h, rootChar_zero, h1, inv_one, mul_one] at h2
        exact h2
    | tail _ hstep ih =>
      rename_i x y
      obtain ⟨hxC, hyC, hxy⟩ := hstep
      obtain ⟨k, l, hkl, rfl, hk, hl⟩ := ih
      obtain ⟨k', l', hkl', rfl⟩ := hCσ _ hyC
      have hyb := hCb _ hyC
      rw [rootChar_sigma h b k' l' i₀] at hyb
      have heq : rootChar b (σ k' i₀) = rootChar b (σ l' i₀) := mul_inv_eq_one.1 hyb
      have hshare : k = k' ∨ k = l' ∨ l = k' ∨ l = l' := by
        by_contra hno
        push Not at hno
        exact hxy (iform_sigma_disjoint h hnorm hkl hkl' hno.1 hno.2.1 hno.2.2.1 hno.2.2.2)
      have hone : rootChar b (σ k' i₀) = 1 ∨ rootChar b (σ l' i₀) = 1 := by
        rcases hshare with h1 | h1 | h1 | h1
        · left; rw [← h1]; exact hk
        · right; rw [← h1]; exact hk
        · left; rw [← h1]; exact hl
        · right; rw [← h1]; exact hl
      refine ⟨k', l', hkl', rfl, ?_, ?_⟩
      · rcases hone with h1 | h1
        · exact h1
        · rw [heq]; exact h1
      · rcases hone with h1 | h1
        · rw [← heq]; exact h1
        · exact h1
  exact key γ (hconn _ hc₀ γ hγ)

theorem finrank_span_class_le (h : IsSLFrame ρ σ) (X : Finset (Fin ν)) {k₀ : Fin ν} (hk : k₀ ∈ X)
    {C : Set (Fin τ.rank → ℤ)} (hC : ∀ γ ∈ C, ∃ i j, i ∈ X ∧ j ∈ X ∧ γ = σ i j) :
    Module.finrank ℚ (Submodule.span ℚ
      ((fun γ : Fin τ.rank → ℤ => fun i => ((γ i : ℤ) : ℚ)) '' C)) ≤ X.card - 1 := by
  classical
  set f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun γ i => ((γ i : ℤ) : ℚ) with hf
  set S : Finset (Fin τ.rank → ℚ) := (X.erase k₀).image fun i => f (σ i k₀) with hS
  have hmem : ∀ i ∈ X, f (σ i k₀) ∈ Submodule.span ℚ (S : Set (Fin τ.rank → ℚ)) := by
    intro i hi
    by_cases hik : i = k₀
    · subst hik
      rw [sigma_self h]
      have : f 0 = 0 := by funext j; simp [hf]
      rw [this]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span (Finset.mem_image.2 ⟨i, Finset.mem_erase.2 ⟨hik, hi⟩, rfl⟩)
  have hle : Submodule.span ℚ (f '' C) ≤ Submodule.span ℚ (S : Set (Fin τ.rank → ℚ)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨i, j, hi, hj, rfl⟩ := hC γ hγ
    have e : f (σ i j) = f (σ i k₀) - f (σ j k₀) := by
      rw [h.eq_sub i j k₀]
      funext t
      simp [hf]
    rw [SetLike.mem_coe, e]
    exact Submodule.sub_mem _ (hmem i hi) (hmem j hj)
  calc Module.finrank ℚ (Submodule.span ℚ (f '' C))
      ≤ Module.finrank ℚ (Submodule.span ℚ (S : Set (Fin τ.rank → ℚ))) :=
        Submodule.finrank_mono hle
    _ ≤ S.card := finrank_span_finset_le_card S
    _ ≤ (X.erase k₀).card := Finset.card_image_le
    _ = X.card - 1 := Finset.card_erase_of_mem hk

end Class

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
