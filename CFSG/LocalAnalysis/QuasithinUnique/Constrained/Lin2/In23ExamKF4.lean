module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKElem
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatRee
public import CFSG.LieType.Ree.LargeReeInvolutionCoordinates
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog
open scoped commutatorElement

namespace F4Exam

@[expose] def wE1 : Word := [(28, [[0]]), (30, [[1]])]

@[expose] def wE2 : Word := [(36, [[0]]), (39, [[1]])]

@[expose] def wU : Word := [(24, [[]]), (33, [[]])]

@[expose] def wUinv : Word := [(33, [[]]), (24, [[]])]

@[expose] def wE3 : Word := wU ++ wE1 ++ wUinv

@[expose] def wZ : Word := [(44, [[0]]), (47, [[1]])]

@[expose] def coordsOne : List Poly := List.replicate 24 []

@[expose] def coordsE12 : List Poly :=
  [[], [], [], [], [[0]], [], [[1]], [], [], [], [], [], [[0]], [], [], [[1]], [], [], [], [], [], [],
    [], []]

@[expose] def coordsE21 : List Poly :=
  [[], [], [], [], [[0]], [], [[1]], [], [], [], [], [], [[0]], [], [], [[1]], [], [[0, 0]], [],
    [[0, 1]], [[0, 1]], [[1, 1]], [[0, 0, 1]], [[0, 0, 1]]]

@[expose] def coordsE13 : List Poly :=
  [[], [], [], [], [], [[0]], [], [[1]], [[1]], [], [], [[0]], [[0]], [[1]], [[1]], [[1]], [[0, 0]],
    [[0, 0]], [[0, 0]], [], [], [], [], []]

@[expose] def coordsE31 : List Poly :=
  [[], [], [], [], [], [[0]], [], [[1]], [[1]], [], [], [[0]], [[0]], [[1]], [[1]], [[1]], [[0, 0]],
    [], [[0, 0]], [], [[0, 1]], [[1, 1]], [], [[0, 0, 1]]]

@[expose] def coordsE23 : List Poly :=
  [[], [], [], [], [[0]], [[0]], [[1]], [[1]], [[1]], [], [], [[0]], [], [[1]], [[1]], [], [[0, 0]],
    [], [[0, 0]], [[0, 1]], [], [[1, 1]], [[0, 0, 1]], [[0, 0, 1]]]

@[expose] def coordsE32 : List Poly :=
  [[], [], [], [], [[0]], [[0]], [[1]], [[1]], [[1]], [], [], [[0]], [], [[1]], [[1]], [], [[0, 0]],
    [[0, 0]], [[0, 0]], [], [], [], [], [[0, 0, 1]]]

theorem collect_e12 : collectCheck 6000 (wE1 ++ wE2) coordsE12 = true := by decide +kernel

theorem collect_e21 : collectCheck 6000 (wE2 ++ wE1) coordsE21 = true := by decide +kernel

theorem collect_e13 : collectCheck 6000 (wE1 ++ wE3) coordsE13 = true := by decide +kernel

theorem collect_e31 : collectCheck 6000 (wE3 ++ wE1) coordsE31 = true := by decide +kernel

theorem collect_e23 : collectCheck 6000 (wE2 ++ wE3) coordsE23 = true := by decide +kernel

theorem collect_e32 : collectCheck 6000 (wE3 ++ wE2) coordsE32 = true := by decide +kernel

theorem collect_e11 : collectCheck 6000 (wE1 ++ wE1) coordsOne = true := by decide +kernel

theorem collect_e22 : collectCheck 6000 (wE2 ++ wE2) coordsOne = true := by decide +kernel

theorem collect_zz : collectCheck 6000 (wZ ++ wZ) coordsOne = true := by decide +kernel

theorem coordsOne_getD (i : ℕ) : coordsOne.getD i [] = [] := by
  unfold coordsOne
  rcases lt_or_ge i 24 with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by simpa using h)]

section Elements

variable {F : Type} [Field F]

noncomputable abbrev rootX
    (k : ℕ) (c : F) : ModGL F4.tag F :=
  pinnedX F4.tag F (orbitCertRoot F4.tag k) c

@[expose] def xv (c s : F) : ℕ → F := fun i => if i = 0 then c else s

@[expose] noncomputable def uA
    (F : Type) [Field F] : ModGL F4.tag F := rootX 24 1 * rootX 33 1

@[expose] noncomputable def e1
    (c s : F) : ModGL F4.tag F := rootX 28 c * rootX 30 s

@[expose] noncomputable def e2
    (c s : F) : ModGL F4.tag F := rootX 36 c * rootX 39 s

@[expose] noncomputable def e3
    (c s : F) : ModGL F4.tag F := uA F * e1 c s * (uA F)⁻¹

@[expose] noncomputable def ez
    (c s : F) : ModGL F4.tag F := rootX 44 c * rootX 47 s

theorem wordEval_e1
    (c s : F) : wordEval F (xv c s) wE1 = e1 c s := by
  simp [wordEval, wE1, e1, rootX, xv, polyEval, monoEval]

theorem wordEval_e2
    (c s : F) : wordEval F (xv c s) wE2 = e2 c s := by
  simp [wordEval, wE2, e2, rootX, xv, polyEval, monoEval]

theorem wordEval_ez
    (c s : F) : wordEval F (xv c s) wZ = ez c s := by
  simp [wordEval, wZ, ez, rootX, xv, polyEval, monoEval]

end Elements

section Group

variable {F : Type} [Field F] [CharP F 2]

theorem rootX_mul_self
    (k : ℕ) (x : F) : rootX k x * rootX k x = 1 := by
  rw [rootX, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem rootX_inv
    (k : ℕ) (x : F) : (rootX k x)⁻¹ = rootX k x :=
  inv_eq_of_mul_eq_one_right (rootX_mul_self k x)

theorem uA_inv
    : (uA F)⁻¹ = rootX 33 1 * rootX 24 1 := by
  rw [uA, mul_inv_rev, rootX_inv 33 1, rootX_inv 24 1]

theorem wordEval_e3
    (c s : F) : wordEval F (xv c s) wE3 = e3 c s := by
  rw [wE3, wordEval_append, wordEval_append, wordEval_e1, e3, uA_inv, uA]
  simp [wordEval, wU, wUinv, rootX, polyEval, monoEval, mul_assoc]

theorem eq_zero_of_wordEval_eq
    {n n' : ℕ} {w w' : Word} {T T' : List Poly}
    (h : collectCheck n w T = true) (h' : collectCheck n' w' T' = true)
    (hd : polyAdd (T.getD 17 []) (T'.getD 17 []) = [[0, 0]]) (x : ℕ → F)
    (heq : wordEval F x w = wordEval F x w') : x 0 * x 0 = 0 := by
  have h1 : polyEval x (T.getD 17 []) = polyEval x (T'.getD 17 []) :=
    (wordEval_eq_iff h h' x).1 heq ⟨17, by norm_num⟩
  have h2 : polyEval x (polyAdd (T.getD 17 []) (T'.getD 17 [])) = 0 := by
    rw [polyEval_polyAdd, h1, CharTwo.add_self_eq_zero]
  rw [hd] at h2
  simpa [polyEval, monoEval] using h2

theorem e1_sq
    (c s : F) : e1 c s * e1 c s = 1 := by
  have h := (wordEval_eq_one_iff collect_e11 (xv c s)).2 (fun i => by
    rw [coordsOne_getD]; rfl)
  rwa [wordEval_append, wordEval_e1] at h

theorem e2_sq
    (c s : F) : e2 c s * e2 c s = 1 := by
  have h := (wordEval_eq_one_iff collect_e22 (xv c s)).2 (fun i => by
    rw [coordsOne_getD]; rfl)
  rwa [wordEval_append, wordEval_e2] at h

theorem ez_sq
    (c s : F) : ez c s * ez c s = 1 := by
  have h := (wordEval_eq_one_iff collect_zz (xv c s)).2 (fun i => by
    rw [coordsOne_getD]; rfl)
  rwa [wordEval_append, wordEval_ez] at h

theorem e3_sq
    (c s : F) : e3 c s * e3 c s = 1 := by
  have h := e1_sq c s
  calc e3 c s * e3 c s = uA F * (e1 c s * e1 c s) * (uA F)⁻¹ := by unfold e3; group
    _ = 1 := by rw [h]; group

theorem e12_ne
    {c : F} (hc : c ≠ 0) (s : F) : e1 c s * e2 c s ≠ e2 c s * e1 c s := by
  intro h
  have h' : wordEval F (xv c s) (wE1 ++ wE2) = wordEval F (xv c s) (wE2 ++ wE1) := by
    rw [wordEval_append, wordEval_append, wordEval_e1, wordEval_e2]; exact h
  have := eq_zero_of_wordEval_eq collect_e12 collect_e21 (by decide +kernel) (xv c s) h'
  exact hc (mul_self_eq_zero.mp (by simpa [xv] using this))

theorem e13_ne
    {c : F} (hc : c ≠ 0) (s : F) : e1 c s * e3 c s ≠ e3 c s * e1 c s := by
  intro h
  have h' : wordEval F (xv c s) (wE1 ++ wE3) = wordEval F (xv c s) (wE3 ++ wE1) := by
    rw [wordEval_append, wordEval_append, wordEval_e1, wordEval_e3]; exact h
  have := eq_zero_of_wordEval_eq collect_e13 collect_e31 (by decide +kernel) (xv c s) h'
  exact hc (mul_self_eq_zero.mp (by simpa [xv] using this))

theorem e23_ne
    {c : F} (hc : c ≠ 0) (s : F) : e2 c s * e3 c s ≠ e3 c s * e2 c s := by
  intro h
  have h' : wordEval F (xv c s) (wE2 ++ wE3) = wordEval F (xv c s) (wE3 ++ wE2) := by
    rw [wordEval_append, wordEval_append, wordEval_e2, wordEval_e3]; exact h
  have := eq_zero_of_wordEval_eq collect_e23 collect_e32 (by decide +kernel) (xv c s) h'
  exact hc (mul_self_eq_zero.mp (by simpa [xv] using this))

end Group

section Ree

variable {a : ℕ} {F : Type} [Field F] [Finite F] [CharP F F4.prime]

theorem uA_mem
    (hF : Nat.card F = 2 ^ (2 * a + 1)) : uA F ∈ F4.reeFixedPosUnipotent F a := by
  have r0 : stdTwoRoot 0 = orbitCertRoot F4.tag 24 := by decide +kernel
  have r1 : stdTwoRoot 1 = orbitCertRoot F4.tag 33 := by decide +kernel
  have h : uA F = stdTwoG a 1 := by
    rw [uA, stdTwoG, r0, r1, largeReeSigma_one]
  rw [h]
  exact reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ (stdTwoG_mem hF 1)

theorem f4_core
    (hF : Nat.card F = 2 ^ (2 * a + 1)) {R₁ A₁ A₁' : Subgroup (ModGL F4.tag F)}
    (hRΓ : R₁ ≤ F4.reeGamma F a)
    (hnorm : ∀ u ∈ F4.reeFixedPosUnipotent F a, ∀ r ∈ R₁, u * r * u⁻¹ ∈ R₁)
    (hstrong : ∀ r ∈ R₁, r * r = 1 → ∀ g ∈ F4.reeGamma F a,
      g * r * g⁻¹ ∈ F4.reeFixedPosUnipotent F a → g * r * g⁻¹ ∈ R₁)
    (hA : ∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x) (hA' : ∀ x ∈ A₁', ∀ y ∈ A₁', x * y = y * x)
    (hel : ∀ e ∈ R₁, e * e = 1 → e ∈ A₁ ∨ e ∈ A₁')
    {c : F} (hc : c ≠ 0) (hz : ez c (largeReeSigma a c) ∈ R₁) : False := by
  have : CharP F 2 := inferInstanceAs (CharP F F4.prime)
  set s : F := largeReeSigma a c with hs
  obtain ⟨WA, WB, hWA, hWB, hA44, hA47, hB44, hB47⟩ := K1.ree_weyl_witnesses
  have hnA : (canonicalRep (coxeterSystem F4.tag) F WA : ModGL F4.tag F) ∈ F4.reeGamma F a :=
    (canonicalRep_mem_reeFixedMonomial F4 F a hWA).2
  have hnB : (canonicalRep (coxeterSystem F4.tag) F WB : ModGL F4.tag F) ∈ F4.reeGamma F a :=
    (canonicalRep_mem_reeFixedMonomial F4 F a hWB).2
  have hzΓ : ez c s ∈ F4.reeGamma F a := hRΓ hz
  have he1 : e1 c s ∈ R₁ := by
    have hconj : (canonicalRep (coxeterSystem F4.tag) F WA : ModGL F4.tag F) * ez c s *
        (canonicalRep (coxeterSystem F4.tag) F WA : ModGL F4.tag F)⁻¹ = e1 c s :=
      K1.canonicalRep_conj_pair hA44 hA47 c s
    have hmem : (canonicalRep (coxeterSystem F4.tag) F WA : ModGL F4.tag F) * ez c s *
        (canonicalRep (coxeterSystem F4.tag) F WA : ModGL F4.tag F)⁻¹ ∈
          F4.reeFixedPosUnipotent F a := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hnA hzΓ) (inv_mem hnA)⟩
      rw [hconj]
      exact mul_mem (K1.ree4Root_mem_posUnipotent (i := 28) ⟨by norm_num, by norm_num⟩ _)
        (K1.ree4Root_mem_posUnipotent (i := 30) ⟨by norm_num, by norm_num⟩ _)
    have := hstrong _ hz (ez_sq c s) _ hnA hmem
    rwa [hconj] at this
  have he2 : e2 c s ∈ R₁ := by
    have hconj : (canonicalRep (coxeterSystem F4.tag) F WB : ModGL F4.tag F) * ez c s *
        (canonicalRep (coxeterSystem F4.tag) F WB : ModGL F4.tag F)⁻¹ = e2 c s :=
      K1.canonicalRep_conj_pair hB44 hB47 c s
    have hmem : (canonicalRep (coxeterSystem F4.tag) F WB : ModGL F4.tag F) * ez c s *
        (canonicalRep (coxeterSystem F4.tag) F WB : ModGL F4.tag F)⁻¹ ∈
          F4.reeFixedPosUnipotent F a := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hnB hzΓ) (inv_mem hnB)⟩
      rw [hconj]
      exact mul_mem (K1.ree4Root_mem_posUnipotent (i := 36) ⟨by norm_num, by norm_num⟩ _)
        (K1.ree4Root_mem_posUnipotent (i := 39) ⟨by norm_num, by norm_num⟩ _)
    have := hstrong _ hz (ez_sq c s) _ hnB hmem
    rwa [hconj] at this
  have he3 : e3 c s ∈ R₁ := hnorm (uA F) (uA_mem hF) _ he1
  exact three_noncommuting hA hA' (hel _ he1 (e1_sq c s)) (hel _ he2 (e2_sq c s))
    (hel _ he3 (e3_sq c s)) (e12_ne hc s) (e13_ne hc s) (e23_ne hc s)

theorem f4_false
    (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1))
    (R₀ A₀ A₀' : Subgroup (F4.reeGamma F a))
    (hRU : R₀ ≤ (F4.reeFixedPosUnipotent F a).subgroupOf (F4.reeGamma F a))
    (hU : IsSylowTwoOf ((F4.reeFixedPosUnipotent F a).subgroupOf (F4.reeGamma F a)) ⊤)
    (hnorm : ∀ n ∈ Subgroup.normalizer
      (((F4.reeFixedPosUnipotent F a).subgroupOf (F4.reeGamma F a) : Subgroup _) : Set _),
        ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀)
    (hne : R₀ ≠ ⊥) (hA : IsElemAbelian 2 A₀) (hA' : IsElemAbelian 2 A₀')
    (hel : ∀ e ∈ R₀, e * e = 1 → e ∈ A₀ ∨ e ∈ A₀')
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : F4.reeGamma F a,
      g * r * g⁻¹ ∈ (F4.reeFixedPosUnipotent F a).subgroupOf (F4.reeGamma F a) →
        g * r * g⁻¹ ∈ R₀) : False := by
  classical
  have : CharP F 2 := inferInstanceAs (CharP F F4.prime)
  have hQ2 : IsPGroup 2 ↥((F4.reeFixedPosUnipotent F a).subgroupOf (F4.reeGamma F a)) := hU.2.1
  obtain ⟨z, hzR, hz1, hzc⟩ := K1.exists_ne_one_mem_centralizer hQ2 hRU
    (fun x hx q hq => by
      have := hnorm q⁻¹ (Subgroup.le_normalizer (Subgroup.inv_mem _ hq)) x hx
      simpa using this) hne
  obtain ⟨-, hcenter, -, -⟩ := large_Ree_Sylow_center a ha F hF
  have hzP : (z : ModGL F4.tag F) ∈ F4.reeFixedPosUnipotent F a :=
    Subgroup.mem_subgroupOf.mp (hRU hzR)
  have hmem : (z : ModGL F4.tag F) ∈ ((Subgroup.center (F4.reeFixedPosUnipotent F a)).map
      (F4.reeFixedPosUnipotent F a).subtype : Set (ModGL F4.tag F)) := by
    refine ⟨⟨z, hzP⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    have h := congrArg Subtype.val (hzc ⟨g, (Subgroup.mem_inf.1 g.2).2⟩ g.2)
    exact Subtype.ext h
  obtain ⟨c, hc⟩ := hcenter.subset hmem
  have r44 : K1.ree4Root 44 = largeReeAlpha44 := orbitCertRoot_largeRee.2.2.2.2.2.1
  have r47 : K1.ree4Root 47 = largeReeAlpha47 := orbitCertRoot_largeRee.2.2.2.2.2.2
  have hc' : ez c (largeReeSigma a c) = (z : ModGL F4.tag F) := by
    have h : pinnedX F4.tag F (K1.ree4Root 44) c *
        pinnedX F4.tag F (K1.ree4Root 47) (c ^ (2 * 2 ^ a)) = (z : ModGL F4.tag F) := by
      rw [r44, r47]
      exact hc
    exact h
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    have h0 : largeReeSigma a (0 : F) = 0 := largeReeSigma_zero
    have h1 : (z : ModGL F4.tag F) = 1 := by
      rw [← hc', h0]
      simp [ez, rootX, pinnedX_zero]
    exact h1
  let ι : F4.reeGamma F a →* ModGL F4.tag F := (F4.reeGamma F a).subtype
  have hnorm₁ : ∀ u ∈ F4.reeFixedPosUnipotent F a, ∀ r ∈ R₀.map ι, u * r * u⁻¹ ∈ R₀.map ι := by
    intro u hu r hr
    obtain ⟨x, hx, rfl⟩ := hr
    have huΓ : u ∈ F4.reeGamma F a := (Subgroup.mem_inf.1 hu).2
    have hn' : (⟨u, huΓ⟩ : F4.reeGamma F a) ∈ Subgroup.normalizer
        (((F4.reeFixedPosUnipotent F a).subgroupOf (F4.reeGamma F a) : Subgroup _) : Set _) :=
      Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mpr hu)
    exact ⟨⟨u, huΓ⟩ * x * ⟨u, huΓ⟩⁻¹, hnorm _ hn' x hx, rfl⟩
  have hstrong₁ : ∀ r ∈ R₀.map ι, r * r = 1 → ∀ g ∈ F4.reeGamma F a,
      g * r * g⁻¹ ∈ F4.reeFixedPosUnipotent F a → g * r * g⁻¹ ∈ R₀.map ι := by
    intro r hr hrr g hg hgU
    obtain ⟨x, hx, rfl⟩ := hr
    have hxx : x * x = 1 := Subtype.ext hrr
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hstrong x hx hxx ⟨g, hg⟩ hgU, rfl⟩
  have hel₁ : ∀ e ∈ R₀.map ι, e * e = 1 → e ∈ A₀.map ι ∨ e ∈ A₀'.map ι := by
    intro e he hee
    obtain ⟨x, hx, rfl⟩ := he
    have hxx : x * x = 1 := Subtype.ext hee
    rcases hel x hx hxx with h | h
    · exact Or.inl ⟨x, h, rfl⟩
    · exact Or.inr ⟨x, h, rfl⟩
  have hcomm : ∀ {B : Subgroup (F4.reeGamma F a)}, IsElemAbelian 2 B →
      ∀ x ∈ B.map ι, ∀ y ∈ B.map ι, x * y = y * x := by
    intro B hB x hx y hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg (fun w : B => ((w : F4.reeGamma F a) : ModGL F4.tag F)) this
  have hRΓ : R₀.map ι ≤ F4.reeGamma F a := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hz₁ : ez c (largeReeSigma a c) ∈ R₀.map ι := by
    rw [hc']
    exact ⟨z, hzR, rfl⟩
  exact f4_core hF hRΓ hnorm₁ hstrong₁ (hcomm hA) (hcomm hA') hel₁ hc0 hz₁

end Ree

end F4Exam

theorem examExcludes_f4
    : ExamExcludes FamF4 := by
  rintro G _ _ K B B' P R m h ⟨f, -, hf3, hmodel⟩
  obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier _ 2 f hmodel
  obtain ⟨-, a, hfa, hmodel'⟩ := hmodel
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel'
  have : Fintype F := Fintype.ofFinite F
  have : CharP F F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hF]
    rfl)
  obtain ⟨E⟩ := hiso a F hfa hF ⟨e⟩
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := hfa ▸ hF
  have ha : 1 ≤ a := by omega
  have : Finite (ModGL F4.tag F) := finite_modGL
  let θ : ↥K →* F4.reeGamma F a := E.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    intro x hx
    have hx' : E (QuotientGroup.mk x) = 1 := hx
    rwa [map_eq_one_iff E E.injective, QuotientGroup.eq_one_iff] at hx'
  obtain ⟨⟨S, hS⟩, -, -, -⟩ := large_Ree_Sylow_center a ha F hF'
  have hU : IsSylowTwoOf ((F4.reeFixedPosUnipotent F a).subgroupOf (F4.reeGamma F a)) ⊤ := by
    rw [← hS]
    exact CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  obtain ⟨R₀, A₀, A₀', hRU, hnorm, hne, hA, hA', hel, hstrong⟩ :=
    h.toAbs.exists_RprimeE θ hθsurj hker _ hU
  exact F4Exam.f4_false ha hF' R₀ A₀ A₀' hRU hU hnorm hne hA hA' hel hstrong

end CFSG.QuasithinUnique.Lin2
