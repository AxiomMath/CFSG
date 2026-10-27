module

public import CFSG.LieType.SeitzGeneration.SpF2.Quad
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.LieType.SeitzGeneration.SpF2

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

section Aux

theorem spForm_self' (x : Fin r ⊕ Fin r → K) : spForm r K x x = 0 :=
  spForm_isAlt.self_eq_zero x

theorem spForm_swap_two [CharP K 2] (x y : Fin r ⊕ Fin r → K) :
    spForm r K y x = spForm r K x y := by
  have h := spForm_isAlt (r := r) (K := K) (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [spForm_isAlt.self_eq_zero x, spForm_isAlt.self_eq_zero y, zero_add, add_zero] at h
  rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]

theorem eq_zero_or_eq_one_of_card_two {k : Subfield K} (hk : Nat.card k = 2) {c : K}
    (hc : c ∈ k) : c = 0 ∨ c = 1 := by
  classical
  by_contra hne
  push Not at hne
  let g : Fin 3 → k := ![0, 1, ⟨c, hc⟩]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [g, Subtype.ext_iff, eq_comm (a := c)]
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hk] at this
  omega

theorem twistQuad_add_smul [CharP K 2] (z u v : Fin r ⊕ Fin r → K) (α β : K) :
    twistQuad z (α • u + β • v) =
      α ^ 2 * twistQuad z u + β ^ 2 * twistQuad z v + α * β * spForm r K u v := by
  rw [twistQuad_add, twistQuad_smul, twistQuad_smul]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

end Aux

theorem exists_eigen [CharP K 2] [Finite K] {k : Subfield K}
    (hk : Nat.card k = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p)
    {X : Subgroup (StatedSp r K)} {a a'' b : Fin r ⊕ Fin r → K}
    (haa : spForm r K a a'' = 0) (hab : spForm r K a b ≠ 0)
    (hlam : spForm r K a'' b / spForm r K a b ∉ k)
    (ha : spTransvection a 1 ∈ X) (ha'' : spTransvection a'' 1 ∈ X)
    (hb : spTransvection b 1 ∈ X) (μ : K) (hμ : μ ≠ 0) :
    ∃ y ∈ X, spEnd y (a + a'') = μ • (a + a'') := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set γ := spForm r K a b with hγdef
  set lam := spForm r K a'' b / γ with hlamdef
  have hlamγ : spForm r K a'' b = lam * γ := by rw [hlamdef, div_mul_cancel₀ _ hab]
  have hlam1 : 1 + lam ≠ 0 := by
    intro h
    apply hlam
    have : lam = 1 := by linear_combination h - h2
    rw [this]
    exact k.one_mem
  set f : Fin r ⊕ Fin r → K := γ⁻¹ • b with hfdef
  set r₀ : Fin r ⊕ Fin r → K := a'' + lam • a with hr₀def
  have hba : spForm r K b a = γ := spForm_swap_two a b
  have hba'' : spForm r K b a'' = lam * γ := by rw [spForm_swap_two, hlamγ]
  have ha''a : spForm r K a'' a = 0 := by rw [spForm_swap_two, haa]
  have hframe : Frame a f r₀ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hfdef, map_smul, smul_eq_mul, ← hγdef, inv_mul_cancel₀ hab]
    · rw [hr₀def, map_add, map_smul, haa, spForm_self', smul_zero, add_zero]
    · simp only [hfdef, hr₀def, map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, hba,
        hba'']
      linear_combination (γ⁻¹ * lam * γ) * h2
  have ha_eq : a = (1 : K) • a + (0 : K) • f + (0 : K) • r₀ := by simp
  have ha''_eq : a'' = lam • a + (0 : K) • f + (1 : K) • r₀ := by
    rw [zero_smul, add_zero, one_smul, hr₀def, add_comm a'' _, ← add_assoc, ← add_smul]
    have : lam + lam = 0 := by linear_combination lam * h2
    rw [this, zero_smul, zero_add]
  have hb_eq : b = (0 : K) • a + γ • f + (0 : K) • r₀ := by
    rw [zero_smul, zero_smul, zero_add, add_zero, hfdef, smul_smul, mul_inv_cancel₀ hab, one_smul]
  have hspan : ∀ α β ρ : K, α • a + β • f + ρ • r₀ ∈ tripleSpan a f r₀ := by
    intro α β ρ
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_) <;> simp
  have ha_mem : a ∈ tripleSpan a f r₀ := by
    have := hspan 1 0 0
    rwa [← ha_eq] at this
  have ha''_mem : a'' ∈ tripleSpan a f r₀ := by
    have := hspan lam 0 1
    rwa [← ha''_eq] at this
  have hb_mem : b ∈ tripleSpan a f r₀ := by
    have := hspan 0 γ 0
    rwa [← hb_eq] at this
  have hr₀a : spForm r K a r₀ = 0 := hframe.er
  have hr₀a'' : spForm r K a'' r₀ = 0 := by
    rw [hr₀def, map_add, map_smul, spForm_self', ha''a, smul_zero, add_zero]
  have hr₀b : spForm r K b r₀ = 0 := by
    have : b = γ • f := by rw [hfdef, smul_smul, mul_inv_cancel₀ hab, one_smul]
    rw [this, map_smul, LinearMap.smul_apply, hframe.fr, smul_zero]
  set Y : Subgroup (StatedSp r K) := Subgroup.closure
    {spTransvection a 1, spTransvection a'' 1, spTransvection b 1} with hYdef
  have hYX : Y ≤ X := by
    rw [hYdef, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact ha
    · exact ha''
    · exact hb
  have hTa : spTransvection a 1 ∈ tripleStab a f r₀ := spTransvection_mem_tripleStab ha_mem hr₀a 1
  have hTa'' : spTransvection a'' 1 ∈ tripleStab a f r₀ :=
    spTransvection_mem_tripleStab ha''_mem hr₀a'' 1
  have hTb : spTransvection b 1 ∈ tripleStab a f r₀ := spTransvection_mem_tripleStab hb_mem hr₀b 1
  have hYS : Y ≤ tripleStab a f r₀ := by
    rw [hYdef, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact hTa
    · exact hTa''
    · exact hTb
  set π := quotHom hframe with hπdef
  set M : Subgroup (SpecialLinearGroup (Fin 2) K) :=
    (Y.subgroupOf (tripleStab a f r₀)).map π with hMdef
  have hmemM : ∀ (g : StatedSp r K) (hgY : g ∈ Y) (m : SpecialLinearGroup (Fin 2) K),
      quotMat a f g = (m : Matrix (Fin 2) (Fin 2) K) → m ∈ M := by
    intro g hgY m hm
    refine ⟨⟨g, hYS hgY⟩, Subgroup.mem_subgroupOf.mpr hgY, ?_⟩
    apply Subtype.ext
    rw [hπdef, quotHom_coe]
    exact hm
  have hu1 : u2 (1 : K) ∈ M := by
    refine hmemM _ (Subgroup.subset_closure (Set.mem_insert _ _)) _ ?_
    rw [show spTransvection a 1 = spTransvection ((1 : K) • a + (0 : K) • f + (0 : K) • r₀) 1 by
      rw [← ha_eq], quotMat_spTransvection hframe, u2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
  have hulam : u2 (lam ^ 2) ∈ M := by
    refine hmemM _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) _ ?_
    rw [show spTransvection a'' 1 = spTransvection (lam • a + (0 : K) • f + (1 : K) • r₀) 1 by
      rw [← ha''_eq], quotMat_spTransvection hframe, u2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
  have hlγ : l2 (γ ^ 2) ∈ M := by
    refine hmemM _ (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))) _ ?_
    rw [show spTransvection b 1 = spTransvection ((0 : K) • a + γ • f + (0 : K) • r₀) 1 by
      rw [← hb_eq], quotMat_spTransvection hframe, l2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
  have hlam2 : lam ^ 2 / 1 ∉ k := by
    rw [div_one]
    intro h
    exact hlam (mem_subfield_of_sq_mem k h)
  have hM : M = ⊤ := by
    refine sl2_eq_top_of_root_groups hp hp2 hK one_ne_zero hlam2 (pow_ne_zero 2 hab) ?_ hlγ
    intro c₁ hc₁ c₂ hc₂
    rcases eq_zero_or_eq_one_of_card_two hk hc₁ with rfl | rfl <;>
      rcases eq_zero_or_eq_one_of_card_two hk hc₂ with rfl | rfl
    · rw [show (0 : K) * 1 + 0 * lam ^ 2 = 0 by ring, u2_zero]; exact M.one_mem
    · rw [show (0 : K) * 1 + 1 * lam ^ 2 = lam ^ 2 by ring]; exact hulam
    · rw [show (1 : K) * 1 + 0 * lam ^ 2 = 1 by ring]; exact hu1
    · rw [show (1 : K) * 1 + 1 * lam ^ 2 = 1 + lam ^ 2 by ring, u2_add]
      exact M.mul_mem hu1 hulam
  let d : SpecialLinearGroup (Fin 2) K :=
    ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two, hμ]⟩
  have hd : d ∈ M := by rw [hM]; exact Subgroup.mem_top d
  obtain ⟨⟨y, hyS⟩, hy'Y, hy'd⟩ := Subgroup.mem_map.mp hd
  have hyY : y ∈ Y := Subgroup.mem_subgroupOf.mp hy'Y
  have hyX : y ∈ X := hYX hyY
  have hmat : quotMat a f y = !![μ, 0; 0, μ⁻¹] := by
    have h := congrArg (fun m : SpecialLinearGroup (Fin 2) K => (m : Matrix (Fin 2) (Fin 2) K)) hy'd
    simp only [hπdef, quotHom_coe] at h
    exact h
  have hy00 : spForm r K (spEnd y a) f = μ := by
    have := congrFun (congrFun hmat 0) 0
    simpa [quotMat] using this
  have hy10 : spForm r K a (spEnd y a) = 0 := by
    have := congrFun (congrFun hmat 1) 0
    simpa [quotMat] using this
  have hyr₀ : spEnd y r₀ = r₀ := hyS.1
  have hya_mem : spEnd y a ∈ tripleSpan a f r₀ := by
    rw [← hyS.2]
    exact Submodule.mem_map_of_mem ha_mem
  obtain ⟨c, hc⟩ := hframe.decomp hya_mem
  rw [hy00, hy10, zero_smul, add_zero] at hc
  refine ⟨y, hyX, ?_⟩
  have ha''r : a'' = r₀ + lam • a := by
    rw [hr₀def, add_assoc, ← add_smul]
    have : lam + lam = 0 := by linear_combination lam * h2
    rw [this, zero_smul, add_zero]
  by_cases hr₀ : r₀ = 0
  ·
    rw [hr₀, smul_zero, add_zero] at hc
    rw [ha''r, hr₀, zero_add, map_add, map_smul, hc, smul_comm lam μ a, ← smul_add]
  ·
    obtain ⟨sa, hsa⟩ := isSquare_of_charTwo' (1 + stdQuad a)
    obtain ⟨sb, hsb⟩ := isSquare_of_charTwo' (1 + stdQuad b)
    obtain ⟨sa'', hsa''⟩ := isSquare_of_charTwo' (1 + stdQuad a'')
    obtain ⟨z, hz1, hz2, hz3⟩ := hframe.exists_spForm_eq hr₀ sa (γ⁻¹ * sb) (sa'' + lam * sa)
    have hza : spForm r K a z = sa := hz1
    have hzb : spForm r K b z = sb := by
      have : b = γ • f := by rw [hfdef, smul_smul, mul_inv_cancel₀ hab, one_smul]
      rw [this, map_smul, LinearMap.smul_apply, hz2, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ hab, one_mul]
    have hza'' : spForm r K a'' z = sa'' := by
      rw [ha''r, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hz3, hza,
        smul_eq_mul]
      linear_combination (lam * sa) * h2
    have hQa : twistQuad z a = 1 := by
      rw [twistQuad, hza]; linear_combination hsa.symm + stdQuad a * h2
    have hQb : twistQuad z b = 1 := by
      rw [twistQuad, hzb]; linear_combination hsb.symm + stdQuad b * h2
    have hQa'' : twistQuad z a'' = 1 := by
      rw [twistQuad, hza'']; linear_combination hsa''.symm + stdQuad a'' * h2
    have hQY : ∀ g ∈ Y, ∀ x, twistQuad z (spEnd g x) = twistQuad z x := by
      rw [hYdef]
      refine twistQuad_closure ?_
      intro g hg x
      rcases hg with rfl | rfl | rfl
      · exact twistQuad_spTransvection hQa x
      · exact twistQuad_spTransvection hQa'' x
      · exact twistQuad_spTransvection hQb x
    have hsum : a + a'' = (1 + lam) • a + (1 : K) • r₀ := by
      rw [ha''r]; module
    have hQr₀ : twistQuad z r₀ = 1 + lam ^ 2 := by
      rw [hr₀def, show a'' + lam • a = (1 : K) • a'' + lam • a by rw [one_smul],
        twistQuad_add_smul, hQa'', hQa, ha''a]
      ring
    have hQsum : twistQuad z (a + a'') = 0 := by
      rw [twistQuad_add, hQa, hQa'', haa]
      linear_combination h2
    have himg : spEnd y (a + a'') =
        ((1 + lam) * μ) • a + ((1 + lam) * c + 1) • r₀ := by
      rw [hsum, map_add, map_smul, map_smul, hc, hyr₀]; module
    have hQimg := hQY y hyY (a + a'')
    rw [himg, hQsum, twistQuad_add_smul, hQa, hQr₀, hr₀a] at hQimg
    set β := (1 + lam) * c + 1 with hβ
    have hsq : (1 + lam) ^ 2 * (μ + β) ^ 2 = 0 := by
      linear_combination hQimg + (μ * β * (1 + lam) ^ 2 + β ^ 2 * lam) * h2
    have hμβ : β = μ := by
      have h1 : (μ + β) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hsq with h | h
        · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hlam1
        · exact h
      have h3 : μ + β = 0 := pow_eq_zero_iff two_ne_zero |>.mp h1
      linear_combination h3 - μ * h2
    rw [himg, hμβ, hsum]; module
end CFSG.LieType.SeitzGeneration.SpF2
