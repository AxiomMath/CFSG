module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 (weylMatrix)

section Sign


theorem canonicalRep_rootVec_sign {τ : Tag} {L : Type} [Field L] (w : WeylGroup τ)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ ε : L, (ε = 1 ∨ ε = -1) ∧
      (canonicalRep (coxeterSystem τ) L w : Module.End L (RootModule τ L)) (rootVec τ L β) =
        ε • rootVec τ L (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  clear hω
  induction ω with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨ε * ((-1) ^ stringDown τ i ((coxeterSystem τ).wordProd ω • β) *
      (((1 : Lˣ) ^ (-∑ j, τ.cartan i j * ((coxeterSystem τ).wordProd ω • β) j) : Lˣ) : L)),
      ?_, ?_⟩
    · rw [one_zpow, Units.val_one, mul_one]
      rcases hε with rfl | rfl <;>
        rcases neg_one_pow_eq_or L (stringDown τ i ((coxeterSystem τ).wordProd ω • β)) with
          h' | h' <;> rw [h'] <;> simp
    · have e : (coxeterSystem τ).wordProd (i :: ω) • β =
          reflect τ i ((coxeterSystem τ).wordProd ω • β) := by
        rw [CoxeterSystem.wordProd_cons, mul_smul]
        exact simple_smul i _
      rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
        weylElt_rootVec i 1 (IsRoot.smul hβ _), smul_smul]

end Sign

section HTermA2

private theorem fd_iform_self
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have hd : Tag.E6.symmetrizer j j = 1 := by fin_cases j <;> rfl
  rw [hj, hd, mul_one]

private theorem fd_iform_cast {L : Type} [Field L] {γ γ' : Fin Tag.E6.rank → ℤ} {s t : L}
    (h : ∀ i, s * (γ i : L) + t * (γ' i : L) = 0) (δ : Fin Tag.E6.rank → ℤ) :
    s * (iform γ δ : L) + t * (iform γ' δ : L) = 0 := by
  simp only [iform, Int.cast_sum, Int.cast_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  linear_combination ((Tag.E6.symmetrizedCartan i j : L) * (δ j : L)) * h i

theorem finrank_ker_weylMatrix_sub_one_of_a2
    {L : Type} [Field L] (h3 : (3 : L) ≠ 0)
    {w : WeylGroup Tag.E6} (_hw3 : w ^ 3 = 1) {γ₁ γ₂ : Fin Tag.E6.rank → ℤ}
    (hγ : IsA2Pair (τ := Tag.E6) γ₁ γ₂) (h₁ : w • γ₁ = γ₁) (h₂ : w • γ₂ = γ₂)
    (hN : ∀ j : Fin Tag.E6.rank, ∃ m n : ℤ, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + w • w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        m • γ₁ + n • γ₂) :
    Module.finrank L (LinearMap.ker
      (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → L)) - 1)) = 2 := by
  classical
  set M := (weylMatrix w).map (Int.cast : ℤ → L) with hM
  let cv : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → L := fun v i => (v i : L)
  have hMc : ∀ v, M.mulVec (cv v) = cv (w • v) := by
    intro v
    funext i
    rw [← CFSG.RankThree.E6.weylMatrix_mulVec w v]
    simp only [cv, hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
  set u₁ := cv γ₁ with hu₁
  set u₂ := cv γ₂ with hu₂
  have h11 : iform γ₁ γ₁ = 2 := fd_iform_self hγ.isRoot_fst
  have h22 : iform γ₂ γ₂ = 2 := fd_iform_self hγ.isRoot_snd
  have h12 : iform γ₁ γ₂ = -1 := by
    have := hγ.two_iform
    rw [h11] at this
    omega
  have h21 : iform γ₂ γ₁ = -1 := by rw [iform_comm, h12]
  have hli : LinearIndependent L ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hi : ∀ i, s * (γ₁ i : L) + t * (γ₂ i : L) = 0 := fun i => by
      have := congrFun hst i
      simpa [hu₁, hu₂, cv] using this
    have e1 := fd_iform_cast hi γ₁
    have e2 := fd_iform_cast hi γ₂
    rw [h11, h21] at e1
    rw [h12, h22] at e2
    push_cast at e1 e2
    have hs : (3 : L) * s = 0 := by linear_combination 2 * e1 + e2
    have hs0 : s = 0 := (mul_eq_zero.1 hs).resolve_left h3
    refine ⟨hs0, ?_⟩
    rw [hs0] at e1
    linear_combination -e1
  set F := LinearMap.ker (Matrix.toLin' M - 1) with hF
  have hmemF : ∀ d, d ∈ F ↔ M.mulVec d = d := fun d => by
    rw [hF, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      Matrix.toLin'_apply]
  have hle1 : Submodule.span L (Set.range ![u₁, u₂]) ≤ F := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact (hmemF _).2 (show M.mulVec u₁ = u₁ by rw [hu₁, hMc, h₁])
    · exact (hmemF _).2 (show M.mulVec u₂ = u₂ by rw [hu₂, hMc, h₂])
  have hle2 : F ≤ Submodule.span L (Set.range ![u₁, u₂]) := by
    intro d hd
    have hd' := (hmemF d).1 hd
    choose m n hmn using hN
    have hMM : M * M = (weylMatrix (w * w)).map (Int.cast : ℤ → L) := by
      rw [CFSG.RankThree.E6.weylMatrix_mul, hM]
      exact (Matrix.map_mul (f := Int.castRingHom L)).symm
    have hcol : ∀ i j, (1 + M + M * M) i j = (m j : L) * (γ₁ i : L) + (n j : L) * (γ₂ i : L) := by
      intro i j
      rw [hMM]
      have h := congrFun (hmn j) i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
      simp only [Matrix.add_apply, Matrix.one_apply, hM, Matrix.map_apply,
        CFSG.RankThree.E6.weylMatrix_apply, mul_smul]
      have h' := congrArg (Int.cast : ℤ → L) h
      rw [Int.cast_add, Int.cast_add, Pi.single_apply, Int.cast_add, Int.cast_mul,
        Int.cast_mul] at h'
      simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at h'
      exact h'
    have h3d : (3 : L) • d = (∑ j, (m j : L) * d j) • u₁ + (∑ j, (n j : L) * d j) • u₂ := by
      have hN3 : (1 + M + M * M).mulVec d = (3 : L) • d := by
        rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hd',
          hd']
        funext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [← hN3]
      funext i
      simp only [Matrix.mulVec, dotProduct, hcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu₁,
        hu₂, cv, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![(3 : L)⁻¹ * ∑ j, (m j : L) * d j, (3 : L)⁻¹ * ∑ j, (n j : L) * d j], ?_⟩
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [mul_smul, mul_smul, ← smul_add, ← h3d, smul_smul, inv_mul_cancel₀ h3, one_smul]
  rw [le_antisymm hle2 hle1, finrank_span_eq_card hli, Fintype.card_fin]

end HTermA2

section Holonomy


private theorem fd_eq_one_of_smul_rootVec {τ : Tag} {L : Type} [Field L] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) {t : L} (h : t • rootVec τ L β = rootVec τ L β) : t = 1 := by
  rw [FourGroupChevalley.rootVec_eq_single hβ] at h
  have := congrArg (fun v : RootModule τ L => v (Sum.inr ⟨β, hβ⟩)) h
  simpa using this

private theorem fd_rootVec_eq_smul {τ : Tag} {L : Type} [Field L] {β β' : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβ' : IsRoot τ β') {t : L} (h : rootVec τ L β = t • rootVec τ L β') :
    β' = β ∧ t = 1 := by
  classical
  by_cases hb : β' = β
  · subst hb
    exact ⟨rfl, fd_eq_one_of_smul_rootVec hβ h.symm⟩
  · exfalso
    rw [FourGroupChevalley.rootVec_eq_single hβ, FourGroupChevalley.rootVec_eq_single hβ'] at h
    have := congrArg (fun v : RootModule τ L => v (Sum.inr ⟨β, hβ⟩)) h
    simp [Finsupp.single_apply, hb] at this

private theorem fd_eq_one_of_sq_cube {L : Type} [Field L] {z : L} (h2 : z ^ 2 = 1)
    (h3 : z ^ 3 = 1) : z = 1 := by
  have h : z ^ 3 = z ^ 2 * z := by ring
  rw [h2, one_mul, h3] at h
  exact h.symm

private theorem fd_rootChar_zsmul {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (k : ℤ)
    (v : Fin τ.rank → ℤ) : rootChar a (k • v) = rootChar a v ^ k := by
  unfold rootChar
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]

theorem rootVec_fixed_of_a2Norm {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {w : WeylGroup Tag.E6} {y : ModGL Tag.E6 L}
    (hy : y = rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w) (hy3 : y ^ 3 = 1)
    {γ₁ γ₂ : Fin Tag.E6.rank → ℤ} (hγ : IsA2Pair (τ := Tag.E6) γ₁ γ₂)
    (h₁ : w • γ₁ = γ₁) (h₂ : w • γ₂ = γ₂)
    (hμ : ∃ μ : Fin Tag.E6.rank → ℤ, 2 • γ₁ + γ₂ = μ + w • μ + w • w • μ)
    {γ γ' : Fin Tag.E6.rank → ℤ} (hγa : γ ∈ a2Roots γ₁ γ₂) (hγ'a : γ' ∈ a2Roots γ₁ γ₂)
    (hfix : (y : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L γ) = rootVec Tag.E6 L γ) :
    (y : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L γ') = rootVec Tag.E6 L γ' := by
  set Y : Module.End L (RootModule Tag.E6 L) := (y : Module.End L (RootModule Tag.E6 L))
    with hY
  have hsign : ∀ β, IsRoot Tag.E6 β → ∃ ε : L, (ε = 1 ∨ ε = -1) ∧
      Y (rootVec Tag.E6 L β) = (ε * (rootChar a (w • β) : L)) • rootVec Tag.E6 L (w • β) := by
    intro β hβ
    obtain ⟨ε, hε, h⟩ := canonicalRep_rootVec_sign (L := L) w hβ
    refine ⟨ε, hε, ?_⟩
    rw [hY, hy, Units.val_mul, Module.End.mul_apply, h, map_smul]
    change ε • rootDiag a (rootVec Tag.E6 L (w • β)) = _
    rw [rootDiag_rootVec a (IsRoot.smul hβ w), smul_smul]
  have hY3 : ∀ v, Y (Y (Y v)) = v := by
    intro v
    have h := congrArg (fun g : ModGL Tag.E6 L => (g : Module.End L (RootModule Tag.E6 L)) v) hy3
    simpa [pow_three, Units.val_mul, Module.End.mul_apply] using h
  have hε2 : ∀ ε : L, (ε = 1 ∨ ε = -1) → ε ^ 2 = 1 := by
    rintro ε (rfl | rfl) <;> norm_num
  have hroot : ∀ μ, IsRoot Tag.E6 μ → ((rootChar a (μ + w • μ + w • w • μ) : Lˣ) : L) ^ 2 = 1 := by
    intro μ hμr
    obtain ⟨ε₀, hε₀, e₀⟩ := hsign μ hμr
    obtain ⟨ε₁, hε₁, e₁⟩ := hsign (w • μ) (IsRoot.smul hμr w)
    obtain ⟨ε₂, hε₂, e₂⟩ := hsign (w • w • μ) (IsRoot.smul (IsRoot.smul hμr w) w)
    have h3 := hY3 (rootVec Tag.E6 L μ)
    rw [e₀, map_smul, map_smul, e₁, map_smul, e₂, ← mul_smul, ← mul_smul] at h3
    obtain ⟨hw3μ, hc⟩ := fd_rootVec_eq_smul hμr
      (IsRoot.smul (IsRoot.smul (IsRoot.smul hμr w) w) w) h3.symm
    rw [hw3μ] at hc
    have hX : ((rootChar a (μ + w • μ + w • w • μ) : Lˣ) : L) =
        (rootChar a μ : L) * (rootChar a (w • μ) : L) * (rootChar a (w • w • μ) : L) := by
      rw [rootChar_add, rootChar_add, Units.val_mul, Units.val_mul]
    have hP : (ε₀ * ε₁ * ε₂) ^ 2 = 1 := by
      rw [mul_pow, mul_pow, hε2 _ hε₀, hε2 _ hε₁, hε2 _ hε₂]
      ring
    rw [hX]
    calc ((rootChar a μ : L) * (rootChar a (w • μ) : L) * (rootChar a (w • w • μ) : L)) ^ 2 =
        (ε₀ * ε₁ * ε₂) ^ 2 *
          ((rootChar a μ : L) * (rootChar a (w • μ) : L) * (rootChar a (w • w • μ) : L)) ^ 2 := by
          rw [hP, one_mul]
      _ = ((ε₀ * (rootChar a (w • μ) : L)) * (ε₁ * (rootChar a (w • w • μ) : L)) *
          (ε₂ * (rootChar a μ : L))) ^ 2 := by ring
      _ = 1 := by rw [hc, one_pow]
  set g : (Fin Tag.E6.rank → ℤ) → Lˣ := fun μ => rootChar a (μ + w • μ + w • w • μ) with hg
  have hg_add : ∀ μ ν, g (μ + ν) = g μ * g ν := by
    intro μ ν
    simp only [hg, smul_add]
    rw [← rootChar_add]
    congr 1
    abel
  have hg_zero : g 0 = 1 := by
    simp only [hg, smul_zero, add_zero]
    exact rootChar_zero a
  have hg_zsmul : ∀ (k : ℤ) μ, g (k • μ) = g μ ^ k := by
    intro k μ
    simp only [hg, smul_comm w k, ← smul_add]
    exact fd_rootChar_zsmul a k _
  have hall : ∀ μ, g μ ^ 2 = 1 := by
    intro μ
    have hdec : μ = ∑ j, μ j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdec]
    refine Finset.sum_induction _ (fun v => g v ^ 2 = 1) (fun u v hu hv => ?_) ?_ fun j _ => ?_
    · rw [hg_add, mul_pow, hu, hv, one_mul]
    · rw [hg_zero, one_pow]
    · have hj : g (Pi.single j 1) ^ 2 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact hroot _ (IsRoot.basis j))
      rw [hg_zsmul, sq, ← mul_zpow, ← sq, hj, one_zpow]
  have heig : ∀ β, IsRoot Tag.E6 β → w • β = β → ∃ ε : L, ε ^ 2 = 1 ∧
      Y (rootVec Tag.E6 L β) = (ε * (rootChar a β : L)) • rootVec Tag.E6 L β := by
    intro β hβ hwβ
    obtain ⟨ε, hε, h⟩ := hsign β hβ
    rw [hwβ] at h
    exact ⟨ε, hε2 ε hε, h⟩
  have hcube : ∀ β, IsRoot Tag.E6 β → ∀ c : L,
      Y (rootVec Tag.E6 L β) = c • rootVec Tag.E6 L β → c ^ 3 = 1 := by
    intro β hβ c hc
    have h := hY3 (rootVec Tag.E6 L β)
    simp only [hc, map_smul, smul_smul] at h
    have := fd_eq_one_of_smul_rootVec hβ h
    linear_combination this
  have hfixiff : ∀ β, IsRoot Tag.E6 β → ∀ c : L,
      Y (rootVec Tag.E6 L β) = c • rootVec Tag.E6 L β →
        (Y (rootVec Tag.E6 L β) = rootVec Tag.E6 L β ↔ c = 1) := by
    intro β hβ c hc
    rw [hc]
    exact ⟨fd_eq_one_of_smul_rootVec hβ, fun h => by rw [h, one_smul]⟩
  have hXn : ∀ β, (rootChar a (-β) : L) * (rootChar a β : L) = 1 := fun β => by
    rw [← Units.val_mul, ← rootChar_add, neg_add_cancel, rootChar_zero, Units.val_one]
  have hC : ∀ (ε ε' : L) (β : Fin Tag.E6.rank → ℤ), ε ^ 2 = 1 → ε' ^ 2 = 1 →
      (ε * (rootChar a β : L)) ^ 3 = 1 → (ε' * (rootChar a (-β) : L)) ^ 3 = 1 →
        (ε' * (rootChar a (-β) : L)) * (ε * (rootChar a β : L)) = 1 := by
    intro ε ε' β h h' hc hd
    refine fd_eq_one_of_sq_cube ?_ ?_
    · calc ((ε' * (rootChar a (-β) : L)) * (ε * (rootChar a β : L))) ^ 2 =
          ε' ^ 2 * ε ^ 2 * ((rootChar a (-β) : L) * (rootChar a β : L)) ^ 2 := by ring
        _ = 1 := by rw [h, h', hXn]; ring
    · calc ((ε' * (rootChar a (-β) : L)) * (ε * (rootChar a β : L))) ^ 3 =
          (ε' * (rootChar a (-β) : L)) ^ 3 * (ε * (rootChar a β : L)) ^ 3 := by ring
        _ = 1 := by rw [hc, hd, one_mul]
  have hr₁ := hγ.isRoot_fst
  have hr₂ := hγ.isRoot_snd
  have hr₃ := hγ.isRoot_add
  have hw₃ : w • (γ₁ + γ₂) = γ₁ + γ₂ := by rw [smul_add, h₁, h₂]
  have hwn : ∀ β : Fin Tag.E6.rank → ℤ, w • β = β → w • -β = -β := fun β h => by rw [smul_neg, h]
  obtain ⟨ε₁, hε₁, e₁⟩ := heig γ₁ hr₁ h₁
  obtain ⟨ε₂, hε₂, e₂⟩ := heig γ₂ hr₂ h₂
  obtain ⟨ε₃, hε₃, e₃⟩ := heig (γ₁ + γ₂) hr₃ hw₃
  obtain ⟨ε₄, hε₄, e₄⟩ := heig (-γ₁) (IsRoot.neg hr₁) (hwn _ h₁)
  obtain ⟨ε₅, hε₅, e₅⟩ := heig (-γ₂) (IsRoot.neg hr₂) (hwn _ h₂)
  obtain ⟨ε₆, hε₆, e₆⟩ := heig (-(γ₁ + γ₂)) (IsRoot.neg hr₃) (hwn _ hw₃)
  have c₁ := hcube _ hr₁ _ e₁
  have c₂ := hcube _ hr₂ _ e₂
  have c₃ := hcube _ hr₃ _ e₃
  have d₁ := hC _ _ _ hε₁ hε₄ c₁ (hcube _ (IsRoot.neg hr₁) _ e₄)
  have d₂ := hC _ _ _ hε₂ hε₅ c₂ (hcube _ (IsRoot.neg hr₂) _ e₅)
  have d₃ := hC _ _ _ hε₃ hε₆ c₃ (hcube _ (IsRoot.neg hr₃) _ e₆)
  have hX₃ : (rootChar a (γ₁ + γ₂) : L) = (rootChar a γ₁ : L) * (rootChar a γ₂ : L) := by
    rw [rootChar_add, Units.val_mul]
  obtain ⟨μ, hμe⟩ := hμ
  have hn2 : ((rootChar a γ₁ : L) * (rootChar a γ₁ : L) * (rootChar a γ₂ : L)) ^ 2 = 1 := by
    have h' : ((g μ : Lˣ) : L) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hall μ, Units.val_one]
    have e : ((g μ : Lˣ) : L) =
        (rootChar a γ₁ : L) * (rootChar a γ₁ : L) * (rootChar a γ₂ : L) := by
      simp only [hg]
      rw [← hμe, rootChar_add, two_nsmul, rootChar_add, Units.val_mul, Units.val_mul]
    rw [← e]
    exact h'
  have hA : (ε₁ * (rootChar a γ₁ : L)) ^ 2 * (ε₂ * (rootChar a γ₂ : L)) = 1 := by
    refine fd_eq_one_of_sq_cube ?_ ?_
    · calc ((ε₁ * (rootChar a γ₁ : L)) ^ 2 * (ε₂ * (rootChar a γ₂ : L))) ^ 2 =
          (ε₁ ^ 2) ^ 2 * ε₂ ^ 2 *
            ((rootChar a γ₁ : L) * (rootChar a γ₁ : L) * (rootChar a γ₂ : L)) ^ 2 := by ring
        _ = 1 := by rw [hε₁, hε₂, hn2]; ring
    · calc ((ε₁ * (rootChar a γ₁ : L)) ^ 2 * (ε₂ * (rootChar a γ₂ : L))) ^ 3 =
          ((ε₁ * (rootChar a γ₁ : L)) ^ 3) ^ 2 * (ε₂ * (rootChar a γ₂ : L)) ^ 3 := by ring
        _ = 1 := by rw [c₁, c₂]; ring
  have hc₂ : ε₂ * (rootChar a γ₂ : L) = ε₁ * (rootChar a γ₁ : L) := by
    linear_combination (-(ε₂ * (rootChar a γ₂ : L))) * c₁ + (ε₁ * (rootChar a γ₁ : L)) * hA
  have hB : ε₃ * (rootChar a (γ₁ + γ₂) : L) =
      (ε₁ * (rootChar a γ₁ : L)) * (ε₂ * (rootChar a γ₂ : L)) := by
    have hrel : ε₃ * (rootChar a (γ₁ + γ₂) : L) =
        (ε₃ * ε₁ * ε₂) * ((ε₁ * (rootChar a γ₁ : L)) * (ε₂ * (rootChar a γ₂ : L))) := by
      rw [hX₃]
      linear_combination (-(ε₃ * (rootChar a γ₁ : L) * (rootChar a γ₂ : L) * ε₂ ^ 2)) * hε₁ -
        (ε₃ * (rootChar a γ₁ : L) * (rootChar a γ₂ : L)) * hε₂
    have hs2 : (ε₃ * ε₁ * ε₂) ^ 2 = 1 := by
      rw [mul_pow, mul_pow, hε₃, hε₁, hε₂]
      ring
    have hs3 : (ε₃ * ε₁ * ε₂) ^ 3 = 1 := by
      have h := c₃
      rw [hrel] at h
      linear_combination h - (ε₃ * ε₁ * ε₂) ^ 3 * (ε₂ * (rootChar a γ₂ : L)) ^ 3 * c₁ -
        (ε₃ * ε₁ * ε₂) ^ 3 * c₂
    rw [hrel, fd_eq_one_of_sq_cube hs2 hs3, one_mul]
  have hone : ε₁ * (rootChar a γ₁ : L) = 1 := by
    simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγa
    rcases hγa with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hfixiff _ hr₁ _ e₁).1 hfix
    · have h := (hfixiff _ (IsRoot.neg hr₁) _ e₄).1 hfix
      rw [h, one_mul] at d₁
      exact d₁
    · rw [← hc₂]
      exact (hfixiff _ hr₂ _ e₂).1 hfix
    · have h := (hfixiff _ (IsRoot.neg hr₂) _ e₅).1 hfix
      rw [h, one_mul, hc₂] at d₂
      exact d₂
    · have h := (hfixiff _ hr₃ _ e₃).1 hfix
      rw [hB, hc₂] at h
      exact fd_eq_one_of_sq_cube (by rw [sq]; exact h) c₁
    · have h := (hfixiff _ (IsRoot.neg hr₃) _ e₆).1 hfix
      rw [h, one_mul, hB, hc₂] at d₃
      exact fd_eq_one_of_sq_cube (by rw [sq]; exact d₃) c₁
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ'a
  rcases hγ'a with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hfixiff _ hr₁ _ e₁).2 hone
  · exact (hfixiff _ (IsRoot.neg hr₁) _ e₄).2 (by rw [hone, mul_one] at d₁; exact d₁)
  · exact (hfixiff _ hr₂ _ e₂).2 (by rw [hc₂, hone])
  · exact (hfixiff _ (IsRoot.neg hr₂) _ e₅).2 (by rw [hc₂, hone, mul_one] at d₂; exact d₂)
  · exact (hfixiff _ hr₃ _ e₃).2 (by rw [hB, hc₂, hone, one_mul])
  · exact (hfixiff _ (IsRoot.neg hr₃) _ e₆).2
      (by rw [hB, hc₂, hone, one_mul, mul_one] at d₃; exact d₃)

end Holonomy

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
