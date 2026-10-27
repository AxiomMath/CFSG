module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLineData
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.SeitzPlane
  CFSG.HardMathSupport.Lang.TwE6Step3 CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (rootSpan_commute_of_orth)
open scoped Matrix

set_option linter.unusedSectionVars false

theorem twLine_map_conj_inv_map {G : Type*} [Group G] (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [← map_conj_mul_aux, inv_mul_cancel]
  ext x
  simp [Subgroup.mem_map, MulAut.conj_apply]

section Split

variable
  {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem twLine_rootSpan_mono {S T : Set (Fin Tag.E6.rank → ℤ)} (h : S ⊆ T) :
    rootSpan Tag.E6 Ω S ≤ rootSpan Tag.E6 Ω T :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (h hα) le_rfl

theorem twLine_weylElt_mem_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)} {i : Fin Tag.E6.rank}
    (h1 : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ S)
    (h2 : (-Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ S) (u : Ωˣ) :
    weylElt Tag.E6 Ω i u ∈ rootSpan Tag.E6 Ω S := by
  have hx : ∀ c, xUnit Tag.E6 Ω i c ∈ rootSpan Tag.E6 Ω S := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan h1 c
  have hy : ∀ c, yUnit Tag.E6 Ω i c ∈ rootSpan Tag.E6 Ω S := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan h2 c
  rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem twLine_torusElt_mem_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)} {i : Fin Tag.E6.rank}
    (h1 : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ S)
    (h2 : (-Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ S) (u : Ωˣ) :
    torusElt Tag.E6 Ω i u ∈ rootSpan Tag.E6 Ω S :=
  mul_mem (twLine_weylElt_mem_rootSpan h1 h2 u) (twLine_weylElt_mem_rootSpan h1 h2 (-1))

theorem tw6ThetaConj_one_apply (g : ModGL Tag.E6 Ω) : tw6ThetaConj Ω Fr 1 g = tw6Theta Ω Fr g := by
  rw [tw6ThetaConj_apply, canonicalRep_one, inv_one, one_mul, mul_one, one_mul, mul_one]

theorem tw6Theta_mem_torusGroup [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {h : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω) :
    tw6Theta Ω Fr h ∈ torusGroup Tag.E6 Ω := by
  rw [← tw6ThetaConj_one_apply]
  exact tw6ThetaConj_mem_torusGroup hFr 1 hh

theorem tw6Theta_mem_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)} (hSr : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hS : ∀ α ∈ S, -(e6T3W • α) ∈ S) {g : ModGL Tag.E6 Ω} (hg : g ∈ rootSpan Tag.E6 Ω S) :
    tw6Theta Ω Fr g ∈ rootSpan Tag.E6 Ω S :=
  map_mem_rootSpan (tw6Theta Ω Fr) (fun β => -(e6T3W • β)) (fun γ hγ c => by
    obtain ⟨ε, -, hε⟩ := exists_tw6Theta_pinnedX (Ω := Ω) (Fr := Fr) (hSr γ hγ)
    exact ⟨ε * Fr c, hε c⟩) hS hg

theorem twLine_inv_conj_mem_torusGroup_sup (x : WeylGroup Tag.E6)
    {S T : Set (Fin Tag.E6.rank → ℤ)} (hT : ∀ γ ∈ T, IsRoot Tag.E6 γ ∧ x⁻¹ • γ ∈ S)
    {m : ModGL Tag.E6 Ω} (hm : m ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω T) :
    (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ * m * canonicalRep (coxeterSystem Tag.E6) Ω x ∈
      torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S := by
  have hle : (torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω T).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹).toMonoidHom ≤
        torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      simpa [MulAut.conj_apply] using canonicalRep_inv_conj_mem_torusGroup x ht
    · rintro _ ⟨g, hg, rfl⟩
      simpa [MulAut.conj_apply] using canonicalRep_inv_conj_mem_rootSpan x hT hg
  have h := hle ⟨m, hm, rfl⟩
  simpa [MulAut.conj_apply] using h

theorem twLine_inv_conj_mem_rootSpan_of_image {S T : Set (Fin Tag.E6.rank → ℤ)}
    (hSr : ∀ α ∈ S, IsRoot Tag.E6 α) {x : WeylGroup Tag.E6} (hx : (x • ·) '' S = T)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ rootSpan Tag.E6 Ω T) :
    (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ * g * canonicalRep (coxeterSystem Tag.E6) Ω x ∈
      rootSpan Tag.E6 Ω S := by
  refine canonicalRep_inv_conj_mem_rootSpan x (fun γ hγ => ?_) hg
  rw [← hx] at hγ
  obtain ⟨α, hα, rfl⟩ := hγ
  exact ⟨CFSG.LieType.Chevalley.IsRoot.smul (hSr α hα) x, by simpa using hα⟩

theorem twLine_conj_mem_rootSpan_of_image {S T : Set (Fin Tag.E6.rank → ℤ)}
    (hSr : ∀ α ∈ S, IsRoot Tag.E6 α) {x : WeylGroup Tag.E6} (hx : (x • ·) '' S = T)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ rootSpan Tag.E6 Ω S) :
    canonicalRep (coxeterSystem Tag.E6) Ω x * g * (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ ∈
      rootSpan Tag.E6 Ω T := by
  rw [← hx]
  exact CFSG.HardMathSupport.Lang.TwE6Step3.canonicalRep_conj_mem_rootSpan x
    (fun γ hγ => ⟨hSr γ hγ, Set.mem_image_of_mem _ hγ⟩) hg

theorem twLine_conj_e6T3W_mem {S T : Set (Fin Tag.E6.rank → ℤ)}
    (hSu : ∀ α ∈ S, e6T3W • α ∈ S) {x : WeylGroup Tag.E6} (hx : (x • ·) '' S = T) :
    ∀ β ∈ T, (x * e6T3W * x⁻¹) • β ∈ T := by
  intro β hβ
  rw [← hx] at hβ ⊢
  obtain ⟨α, hα, rfl⟩ := hβ
  exact ⟨e6T3W • α, hSu α hα, by simp [mul_smul]⟩

theorem twLine_lang [IsAlgClosed Ω] {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSr : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hSu : ∀ α ∈ S, e6T3W • α ∈ S) {x : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hx : (x • ·) '' S = parabolicRoots Tag.E6 J) :
    ∀ s ∈ torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω S,
      ∃ t ∈ torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω S, t⁻¹ * tw6Theta Ω Fr t = s := by
  intro s hs
  obtain ⟨hsH, hsS⟩ := Subgroup.mem_inf.1 hs
  have hs' : canonicalRep (coxeterSystem Tag.E6) Ω x * s *
      (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ ∈
        torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 J) :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer x) s).1 hsH,
      twLine_conj_mem_rootSpan_of_image hSr hx hsS⟩
  obtain ⟨t', ht', ht'e⟩ := exists_lang_torusGroup_inf_rootSpan hq hFr x
    (twLine_conj_e6T3W_mem hSu hx) _ hs'
  obtain ⟨ht'H, ht'S⟩ := Subgroup.mem_inf.1 ht'
  refine ⟨_, Subgroup.mem_inf.2 ⟨canonicalRep_inv_conj_mem_torusGroup x ht'H,
    twLine_inv_conj_mem_rootSpan_of_image hSr hx ht'S⟩, ?_⟩
  rw [tw6Theta_inv_conj]
  set n := canonicalRep (coxeterSystem Tag.E6) Ω x
  calc (n⁻¹ * t' * n)⁻¹ * (n⁻¹ * tw6ThetaConj Ω Fr x t' * n) =
      n⁻¹ * (t'⁻¹ * tw6ThetaConj Ω Fr x t') * n := by group
    _ = n⁻¹ * (n * s * n⁻¹) * n := by rw [ht'e]
    _ = s := by group

theorem twLine_mem_torusGroup_of_commute {S : Set (Fin Tag.E6.rank → ℤ)}
    (hSr : ∀ α ∈ S, IsRoot Tag.E6 α) {x : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hx : (x • ·) '' S = parabolicRoots Tag.E6 J) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ rootSpan Tag.E6 Ω S) (hc : ∀ h ∈ rootSpan Tag.E6 Ω S, g * h = h * g) :
    g ∈ torusGroup Tag.E6 Ω := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω x with hn
  have hgS : n * g * n⁻¹ ∈ subsystemGroup Tag.E6 Ω J := by
    rw [subsystemGroup_eq_rootSpan]
    exact twLine_conj_mem_rootSpan_of_image hSr hx hg
  have hcen : (⟨_, hgS⟩ : subsystemGroup Tag.E6 Ω J) ∈
      Subgroup.center (subsystemGroup Tag.E6 Ω J) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    have hh : n⁻¹ * (h : ModGL Tag.E6 Ω) * n ∈ rootSpan Tag.E6 Ω S := by
      refine twLine_inv_conj_mem_rootSpan_of_image hSr hx ?_
      rw [← subsystemGroup_eq_rootSpan]
      exact h.2
    have hgh := hc _ hh
    change (h : ModGL Tag.E6 Ω) * (n * g * n⁻¹) = n * g * n⁻¹ * h
    calc (h : ModGL Tag.E6 Ω) * (n * g * n⁻¹) = n * ((n⁻¹ * h * n) * g) * n⁻¹ := by group
      _ = n * (g * (n⁻¹ * h * n)) * n⁻¹ := by rw [hgh]
      _ = n * g * n⁻¹ * h := by group
  have h3 := mem_supportedTorus_of_mem_center hcen
  rw [← subsystemGroup_inf_torusGroup_eq_supportedTorus] at h3
  have h4 := canonicalRep_inv_conj_mem_torusGroup x (Subgroup.mem_inf.1 h3).2
  have e : n⁻¹ * (n * g * n⁻¹) * n = g := by group
  rw [← hn, e] at h4
  exact h4

theorem twLine_cochar (k : Fin 6) (s : Ωˣ) :
    (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl (twLineBlk k)))⁻¹ *
        torusElt Tag.E6 Ω (twLineNode k) s *
        canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl (twLineBlk k)) =
      rootDiagUnit Tag.E6 (fun m => s ^ twLineCocharA m k) := by
  have h1 : (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl (twLineBlk k)))⁻¹ *
      rootDiagUnit Tag.E6 (fun j => s ^ Tag.E6.cartan (twLineNode k) j) *
      canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl (twLineBlk k)) =
        rootDiagUnit Tag.E6 (weylTuple (twE6FrameWeyl (twLineBlk k))⁻¹
          (fun j => s ^ Tag.E6.cartan (twLineNode k) j)) := by
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (K := Ω)
      (fun j => s ^ Tag.E6.cartan (twLineNode k) j)
      (weylTuple (twE6FrameWeyl (twLineBlk k))⁻¹ (fun j => s ^ Tag.E6.cartan (twLineNode k) j))
      (twE6FrameWeyl (twLineBlk k))).2 (fun v => by rw [rootChar_weylTuple, inv_inv])
    rw [this]
    group
  rw [torusElt_eq_rootDiagUnit, h1]
  congr 1
  funext m
  simp only [weylTuple, inv_inv]
  rw [twLineCocharA_apply k m, twE6FrameWeyl,
    ← CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  simp only [rootChar, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum]

theorem twLine_cochar_mem (k : Fin 6) (s : Ωˣ) :
    rootDiagUnit Tag.E6 (fun m => s ^ twLineCocharA m k) ∈
      (torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS 0)) ⊔
        (torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS 1 ∪ twE6FrameS 2)) := by
  rw [← twLine_cochar]
  have hmem : ∀ i : Fin 3, ∀ j ∈ CFSG.RankThree.E6.support13, ∀ s : Ωˣ,
      (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl i))⁻¹ * torusElt Tag.E6 Ω j s *
          canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl i) ∈
        torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS i) := by
    intro i j hj s
    have ht : torusElt Tag.E6 Ω j s ∈ torusGroup Tag.E6 Ω ⊓
        rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 CFSG.RankThree.E6.support13) := by
      rw [torusGroup_inf_rootSpan_parabolicRoots, supportedTorus_eq_subsystemTorus]
      exact torusElt_mem_subsystemTorus hj s
    obtain ⟨htH, htS⟩ := Subgroup.mem_inf.1 ht
    exact Subgroup.mem_inf.2 ⟨canonicalRep_inv_conj_mem_torusGroup _ htH,
      twLine_inv_conj_mem_rootSpan_of_image (fun α hα => twE6FrameS_root i hα)
        (twE6FrameS_conj i) htS⟩
  have hnode : twLineNode k ∈ CFSG.RankThree.E6.support13 := by
    rw [mem_support13]
    fin_cases k <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hle : ∀ i : Fin 3, torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS i) ≤
      (torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS 0)) ⊔
        (torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS 1 ∪ twE6FrameS 2)) := by
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_of_le_right (inf_le_inf_left _ (twLine_rootSpan_mono Set.subset_union_left))
    · exact le_sup_of_le_right (inf_le_inf_left _ (twLine_rootSpan_mono Set.subset_union_right))
  exact hle _ (hmem _ _ hnode s)

theorem twLine_torusGroup_le [IsAlgClosed Ω] :
    torusGroup Tag.E6 Ω ≤ (torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS 0)) ⊔
      (torusGroup Tag.E6 Ω ⊓ rootSpan Tag.E6 Ω (twE6FrameS 1 ∪ twE6FrameS 2)) := by
  intro h hh
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨s, hs⟩ := monoHom_surjective_of_det_ne_zero (L := Ω) twLineCocharA
    twLineCocharA_det_ne_zero b
  have hb : b = (fun m : Fin Tag.E6.rank => s 0 ^ twLineCocharA m 0) *
      (fun m : Fin Tag.E6.rank => s 1 ^ twLineCocharA m 1) *
      (fun m : Fin Tag.E6.rank => s 2 ^ twLineCocharA m 2) *
      (fun m : Fin Tag.E6.rank => s 3 ^ twLineCocharA m 3) *
      (fun m : Fin Tag.E6.rank => s 4 ^ twLineCocharA m 4) *
      (fun m : Fin Tag.E6.rank => s 5 ^ twLineCocharA m 5) := by
    rw [← hs]
    funext m
    simp only [monoHom_apply, Fin.prod_univ_six]
    rfl
  rw [hb, rootDiagUnit_mul, rootDiagUnit_mul, rootDiagUnit_mul, rootDiagUnit_mul,
    rootDiagUnit_mul]
  have hk := fun k : Fin 6 => twLine_cochar_mem (Ω := Ω) k (s k)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hk 0) (hk 1)) (hk 2)) (hk 3)) (hk 4)) (hk 5)

theorem twLine_torusGroup_comm :
    ∀ a ∈ torusGroup Tag.E6 Ω, ∀ b ∈ torusGroup Tag.E6 Ω, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
  obtain ⟨b', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hb
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem twLine_iUnion_frame :
    (⋃ i, twE6FrameS i) = twE6FrameS 0 ∪ (twE6FrameS 1 ∪ twE6FrameS 2) := by
  ext α
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · rintro (h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

theorem twLine_frame12_root : ∀ α ∈ twE6FrameS 1 ∪ twE6FrameS 2, IsRoot Tag.E6 α := by
  rintro α (h | h)
  exacts [twE6FrameS_root 1 h, twE6FrameS_root 2 h]

theorem twLine_frame12_stable :
    ∀ α ∈ twE6FrameS 1 ∪ twE6FrameS 2, e6T3W • α ∈ twE6FrameS 1 ∪ twE6FrameS 2 := by
  rintro α (h | h)
  exacts [Or.inl (twE6FrameS_stable 1 h), Or.inr (twE6FrameS_stable 2 h)]

theorem twLine_frame12_neg_stable :
    ∀ α ∈ twE6FrameS 1 ∪ twE6FrameS 2, -(e6T3W • α) ∈ twE6FrameS 1 ∪ twE6FrameS 2 := by
  rintro α (h | h)
  exacts [Or.inl (twE6FrameS_neg_stable h), Or.inr (twE6FrameS_neg_stable h)]

theorem twLineYW_image_frame12 :
    (twLineYW • ·) '' (twE6FrameS 1 ∪ twE6FrameS 2) = parabolicRoots Tag.E6 supportA2A2 := by
  rw [Set.image_union, twLineYW_image_one, twLineYW_image_two, parabolicRoots_supportA2A2]

theorem twLine_image_inv {S T : Set (Fin Tag.E6.rank → ℤ)} {x : WeylGroup Tag.E6}
    (hx : (x • ·) '' S = T) : (fun α => x⁻¹ • α) '' T = S := by
  rw [← hx, Set.image_image]
  simp

theorem twLine_frame_commute :
    ∀ a ∈ rootSpan Tag.E6 Ω (twE6FrameS 0), ∀ b ∈ rootSpan Tag.E6 Ω (twE6FrameS 1 ∪ twE6FrameS 2),
      a * b = b * a :=
  rootSpan_commute_of_orth (Or.inr (Or.inl rfl)) (fun α hα => twE6FrameS_root 0 hα)
    twLine_frame12_root (by
      rintro α hα β (hβ | hβ)
      exacts [twE6FrameS_orth (by decide) α hα β hβ, twE6FrameS_orth (by decide) α hα β hβ])

theorem twLine_fixed_split [IsAlgClosed Ω] {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    {m : ModGL Tag.E6 Ω}
    (hm : m ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (⋃ i, twE6FrameS i))
    (hθm : tw6Theta Ω Fr m = m) :
    ∃ t ∈ torusGroup Tag.E6 Ω, tw6Theta Ω Fr t = t ∧
      ∃ p₀ ∈ rootSpan Tag.E6 Ω (twE6FrameS 0), tw6Theta Ω Fr p₀ = p₀ ∧
      ∃ p₁ ∈ rootSpan Tag.E6 Ω (twE6FrameS 1), tw6Theta Ω Fr p₁ = p₁ ∧
      ∃ p₂ ∈ rootSpan Tag.E6 Ω (twE6FrameS 2), tw6Theta Ω Fr p₂ = p₂ ∧
        m = t * p₀ * p₁ * p₂ := by
  have hm' : m ∈ torusGroup Tag.E6 Ω ⊔ (rootSpan Tag.E6 Ω (twE6FrameS 0) ⊔
      rootSpan Tag.E6 Ω (twE6FrameS 1 ∪ twE6FrameS 2)) := by
    rw [twLine_iUnion_frame, rootSpan_union'] at hm
    exact hm
  have hQ₁₂ : rootSpan Tag.E6 Ω (twE6FrameS 0) ⊓ rootSpan Tag.E6 Ω (twE6FrameS 1 ∪ twE6FrameS 2) ≤
      torusGroup Tag.E6 Ω := by
    intro g hg
    obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
    exact twLine_mem_torusGroup_of_commute (fun α hα => twE6FrameS_root 0 hα)
      (twE6FrameS_conj 0) hg₁ (fun h hh => (twLine_frame_commute h hh g hg₂).symm)
  obtain ⟨t, htH, htθ, g₁, hg₁, hg₁θ, g₂, hg₂, hg₂θ, rfl⟩ := exists_fixed_split₂ (tw6Theta Ω Fr)
    twLine_torusGroup_comm
    (torusGroup_le_normalizer_rootSpan_e6 fun α hα => twE6FrameS_root 0 hα)
    (torusGroup_le_normalizer_rootSpan_e6 twLine_frame12_root)
    twLine_frame_commute
    (fun h hh => tw6Theta_mem_torusGroup hFr hh)
    (fun g hg => tw6Theta_mem_rootSpan (fun α hα => twE6FrameS_root 0 hα)
      (fun α hα => twE6FrameS_neg_stable hα) hg)
    (fun g hg => tw6Theta_mem_rootSpan twLine_frame12_root twLine_frame12_neg_stable hg)
    hQ₁₂ (fun g hg => twLine_torusGroup_le (Subgroup.mem_inf.1 hg).1)
    (twLine_lang hq hFr (fun α hα => twE6FrameS_root 0 hα) (fun α hα => twE6FrameS_stable 0 hα)
      (twE6FrameS_conj 0))
    (twLine_lang hq hFr twLine_frame12_root twLine_frame12_stable twLineYW_image_frame12) hm' hθm
  have hsplit := twoA2Split_of_blocks (L := Ω) (Fr := Fr) hq hFr (w := twLineYW)
    (twLine_conj_e6T3W_mem (fun α hα => twE6FrameS_stable 1 hα) twLineYW_image_one)
    (twLine_conj_e6T3W_mem (fun α hα => twE6FrameS_stable 2 hα) twLineYW_image_two)
  rw [twLine_image_inv twLineYW_image_one, twLine_image_inv twLineYW_image_two] at hsplit
  obtain ⟨t', ht'H, ht'θ, a₁, ha₁, ha₁θ, a₂, ha₂, ha₂θ, hg₂e⟩ :=
    hsplit g₂ (Subgroup.mem_sup_right hg₂) hg₂θ
  refine ⟨t * t', mul_mem htH ht'H, by rw [map_mul, htθ, ht'θ], t'⁻¹ * g₁ * t', ?_, ?_, a₁, ha₁,
    ha₁θ, a₂, ha₂, ha₂θ, ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan_e6
      (fun α hα => twE6FrameS_root 0 hα) (inv_mem ht'H)) g₁).1 hg₁
    simpa using h
  · simp only [map_mul, map_inv, ht'θ, hg₁θ]
  · rw [hg₂e]
    group

end Split

section Diag

variable
  {Ω : Type} [Field Ω] {ω : Ωˣ}

theorem twLine_zpow_congr (h3 : ω ^ 3 = 1) {a b : ℤ} (h : (3 : ℤ) ∣ a - b) : ω ^ a = ω ^ b := by
  obtain ⟨k, hk⟩ := h
  have e : a = b + 3 * k := by omega
  have h3' : ω ^ (3 : ℤ) = 1 := by exact_mod_cast h3
  rw [e, zpow_add, zpow_mul, h3', one_zpow, mul_one]

theorem twLine_rootChar_single (a : Fin Tag.E6.rank → Ωˣ) (j : Fin Tag.E6.rank) :
    rootChar a (Pi.single j 1) = a j := by
  simpa using rootChar_nsmul_single a j 1

theorem twLine_conj_frame (h3 : ω ^ 3 = 1) :
    rootDiagUnit Tag.E6 (e6LineChar ω) =
      canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) * rootDiagUnit Tag.E6 (twLineChar ω) *
        (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹ := by
  refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ _).2
    (rootChar_smul_eq_rootChar_of_forall_isRoot fun α hα => ?_)
  rw [rootChar_e6LineChar, rootChar_twLineChar, twE6FrameWeyl,
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  exact twLine_zpow_congr h3 (twLineExp_frame α (mem_rootFinset.2 hα))

theorem twLine_conj_weyl (h3 : ω ^ 3 = 1) :
    rootDiagUnit Tag.E6 (twLineChar ω) =
      canonicalRep (coxeterSystem Tag.E6) Ω twLineWeyl * rootDiagUnit Tag.E6 (twLineChar ω) *
        (canonicalRep (coxeterSystem Tag.E6) Ω twLineWeyl)⁻¹ := by
  refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ _).2
    (rootChar_smul_eq_of_forall_isRoot fun α hα => ?_)
  rw [rootChar_twLineChar, rootChar_twLineChar, twLineWeyl_smul]
  exact twLine_zpow_congr h3 (twLineExp_twLineWeyl α (mem_rootFinset.2 hα))

theorem twLine_single_mem_rootFinset (i : Fin Tag.E6.rank) :
    (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset .E6 := by
  revert i
  decide +kernel

theorem tw6Theta_twLine_diag {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3q : 3 ∣ q + 1)
    (h3 : ω ^ 3 = 1) :
    tw6Theta Ω Fr (rootDiagUnit Tag.E6 (twLineChar ω)) = rootDiagUnit Tag.E6 (twLineChar ω) := by
  obtain ⟨b', hb', hchar⟩ := tw6ThetaConj_rootDiagUnit hFr 1 (twLineChar ω)
  rw [tw6ThetaConj_one_apply] at hb'
  rw [hb']
  congr 1
  funext i
  rw [← twLine_rootChar_single b' i, hchar, ← twLine_rootChar_single (twLineChar ω) i]
  simp only [one_mul, inv_one, mul_one]
  set β : Fin Tag.E6.rank → ℤ := e6T3W⁻¹ • Pi.single i 1 with hβ
  have hβr : β ∈ rootFinset .E6 := mem_rootFinset.2 (CFSG.LieType.Chevalley.IsRoot.smul
    (mem_rootFinset.1 (twLine_single_mem_rootFinset i)) _)
  have huβ : toMat Tag.E6.rank e6T3MList *ᵥ β = Pi.single i 1 := by
    rw [← weylMatrix_e6T3W, weylMatrix_mulVec, hβ, smul_inv_smul]
  have h1 := twLineExp_e6T3 β hβr
  rw [huβ] at h1
  have hneg : twLineExp (-β) = -twLineExp β := by
    simp only [twLineExp, Pi.neg_apply]
    ring
  rw [rootChar_twLineChar, rootChar_twLineChar, hneg, ← zpow_natCast, ← zpow_mul]
  refine twLine_zpow_congr h3 ?_
  have h2 : (3 : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast h3q
  have e : -twLineExp β * (q : ℤ) - twLineExp (Pi.single i 1) =
      -(twLineExp β * ((q : ℤ) + 1)) - (twLineExp (Pi.single i 1) - twLineExp β) := by ring
  rw [e]
  exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_right h2 _)) h1

theorem twLine_diag_eq_torusElt (h3 : ω ^ 3 = 1) :
    rootDiagUnit Tag.E6 (twLineChar ω) = torusElt Tag.E6 Ω 2 ω * torusElt Tag.E6 Ω 3 (ω ^ 2) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  have hc : ∀ j : Fin Tag.E6.rank, (3 : ℤ) ∣ twLineExp (Pi.single j 1) -
      (Tag.E6.cartan 2 j + 2 * Tag.E6.cartan 3 j) := by
    decide +kernel
  rw [Pi.mul_apply, ← twLine_rootChar_single (twLineChar ω) j, rootChar_twLineChar,
    ← zpow_natCast, ← zpow_mul, ← zpow_add]
  exact twLine_zpow_congr h3 (by simpa [mul_comm] using hc j)

theorem twLine_diag_mem_rootSpan_zero (h3 : ω ^ 3 = 1) :
    rootDiagUnit Tag.E6 (twLineChar ω) ∈ rootSpan Tag.E6 Ω (twE6FrameS 0) := by
  obtain ⟨h1, h2, h3', h4⟩ := single_mem_twE6FrameS_zero
  rw [twLine_diag_eq_torusElt h3]
  exact mul_mem (twLine_torusElt_mem_rootSpan h1 h2 ω) (twLine_torusElt_mem_rootSpan h3' h4 _)

theorem twLine_weyl_map (i : Fin 3) :
    (rootSpan Tag.E6 Ω (twE6FrameS i)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω twLineWeyl)).toMonoidHom =
      rootSpan Tag.E6 Ω (twE6FrameS (i + 1)) := by
  rw [(canonical_weyl_root_transport Tag.E6 Ω).1 _ _ (fun α hα => twE6FrameS_root i hα),
    twLineWeyl_image]

theorem twLine_diag_mem_rootSpan (h3 : ω ^ 3 = 1) (i : Fin 3) :
    rootDiagUnit Tag.E6 (twLineChar ω) ∈ rootSpan Tag.E6 Ω (twE6FrameS i) := by
  have hstep : ∀ j : Fin 3, rootDiagUnit Tag.E6 (twLineChar ω) ∈ rootSpan Tag.E6 Ω (twE6FrameS j) →
      rootDiagUnit Tag.E6 (twLineChar ω) ∈ rootSpan Tag.E6 Ω (twE6FrameS (j + 1)) := by
    intro j hj
    rw [← twLine_weyl_map j]
    refine ⟨_, hj, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (twLine_conj_weyl h3).symm
  have h0 := twLine_diag_mem_rootSpan_zero (Ω := Ω) h3
  have h1 := hstep 0 h0
  have h2 := hstep 1 h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem twLine_frame_subset_kernel (h3 : ω ^ 3 = 1) (i : Fin 3) :
    twE6FrameS i ⊆ rootCharKernel (twLineChar ω) := by
  intro α hα
  have h : ∀ j : Fin 3, ∀ β ∈ twE6FrameL j, (3 : ℤ) ∣ twLineExp β := by decide +kernel
  refine ⟨twE6FrameS_root i hα, ?_⟩
  rw [rootChar_twLineChar, ← zpow_zero ω]
  exact twLine_zpow_congr h3 (by simpa using h i α hα)

theorem twLine_diag_commute (h3 : ω ^ 3 = 1) (i : Fin 3) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ rootSpan Tag.E6 Ω (twE6FrameS i)) :
    rootDiagUnit Tag.E6 (twLineChar ω) * g = g * rootDiagUnit Tag.E6 (twLineChar ω) := by
  have hg' : g ∈ toralCentralizer Tag.E6 Ω (twLineChar ω) :=
    toralRootGroup_le _ (Subgroup.mem_sup_right
      (twLine_rootSpan_mono (twLine_frame_subset_kernel h3 i) hg))
  have h := (mem_toralCentralizer.1 hg').2
  calc rootDiagUnit Tag.E6 (twLineChar ω) * g =
      rootDiagUnit Tag.E6 (twLineChar ω) * g * (rootDiagUnit Tag.E6 (twLineChar ω))⁻¹ *
        rootDiagUnit Tag.E6 (twLineChar ω) := by group
    _ = g * rootDiagUnit Tag.E6 (twLineChar ω) := by rw [h]

theorem twLineChar_pow_three (h3 : ω ^ 3 = 1) : twLineChar ω ^ 3 = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← twLine_rootChar_single (twLineChar ω) i, rootChar_twLineChar,
    ← zpow_natCast, ← zpow_mul, ← zpow_zero ω]
  exact twLine_zpow_congr h3 ⟨twLineExp (Pi.single i 1), by push_cast; ring⟩

theorem twLine_diag_pow_three (h3 : ω ^ 3 = 1) :
    rootDiagUnit Tag.E6 (twLineChar ω) ^ 3 = 1 := by
  have h := map_pow (rootDiagUnitHom Tag.E6 Ω) (twLineChar ω) 3
  change rootDiagUnit Tag.E6 (twLineChar ω ^ 3) = rootDiagUnit Tag.E6 (twLineChar ω) ^ 3 at h
  rw [← h, twLineChar_pow_three h3]
  exact map_one (rootDiagUnitHom Tag.E6 Ω)

theorem twLine_diag_ne_one (h1 : ω ≠ 1) : rootDiagUnit Tag.E6 (twLineChar ω) ≠ 1 := by
  intro h
  have h' : rootDiagUnit Tag.E6 (twLineChar ω) = rootDiagUnit Tag.E6 1 := by
    rw [h]
    exact (map_one (rootDiagUnitHom Tag.E6 Ω)).symm
  have := congrFun (rootDiagUnit_injective h') 1
  exact h1 this

theorem twLine_diag_finrank (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    Module.finrank Ω (LinearMap.ker
      (((rootDiagUnit Tag.E6 (twLineChar ω) : ModGL Tag.E6 Ω) :
        Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24 := by
  have e : rootDiagUnit Tag.E6 (twLineChar ω) =
      (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹ *
        rootDiagUnit Tag.E6 (e6LineChar ω) *
          (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹⁻¹ := by
    rw [twLine_conj_frame h3]
    group
  rw [e, finrank_ker_conj_sub_one]
  exact e6Line_finrank_fixed_aux h3 h1

end Diag

section Shift

variable
  {Ω : Type} [Field Ω] {ω : Ωˣ}

theorem twLine_frame_map (i : Fin 3) :
    (rootSpan Tag.E6 Ω (twE6FrameS i)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))).toMonoidHom =
      e6LineFactor Ω i := by
  rw [(canonical_weyl_root_transport Tag.E6 Ω).1 _ _ (fun α hα => twE6FrameS_root i hα),
    twE6FrameWeyl_zero_image]
  rfl

theorem twLine_conj_mem_toralCentralizer (h3 : ω ^ 3 = 1) {m : ModGL Tag.E6 Ω}
    (hm : m ∈ adjointGroup Tag.E6 Ω)
    (hmd : rootDiagUnit Tag.E6 (twLineChar ω) * m = m * rootDiagUnit Tag.E6 (twLineChar ω)) :
    canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) * m *
        (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹ ∈
      toralCentralizer Tag.E6 Ω (e6LineChar ω) := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) with hn
  set d := rootDiagUnit Tag.E6 (twLineChar ω) with hd
  rw [mem_toralCentralizer, twLine_conj_frame h3]
  refine ⟨mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ Ω _) hm)
    (inv_mem (canonicalRep_mem_adjointGroup _ Ω _)), ?_⟩
  calc n * d * n⁻¹ * (n * m * n⁻¹) * (n * d * n⁻¹)⁻¹ = n * (d * m) * d⁻¹ * n⁻¹ := by group
    _ = n * (m * d) * d⁻¹ * n⁻¹ := by rw [hmd]
    _ = n * m * n⁻¹ := by group

theorem twLine_conj_shift (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {m : ModGL Tag.E6 Ω}
    (hm : m ∈ adjointGroup Tag.E6 Ω)
    (hmd : rootDiagUnit Tag.E6 (twLineChar ω) * m = m * rootDiagUnit Tag.E6 (twLineChar ω)) :
    ∃ k : Fin 3, ∀ i : Fin 3, (rootSpan Tag.E6 Ω (twE6FrameS i)).map (MulAut.conj m).toMonoidHom =
      rootSpan Tag.E6 Ω (twE6FrameS (i + k)) := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) with hn
  obtain ⟨k, hk⟩ := e6LineFactor_conj_centralizer h3 h1
    (twLine_conj_mem_toralCentralizer h3 hm hmd)
  refine ⟨k, fun i => ?_⟩
  have e : m = n⁻¹ * (n * m * n⁻¹) * n := by group
  rw [e, map_conj_mul_aux, map_conj_mul_aux, twLine_frame_map, hk, ← twLine_frame_map,
    twLine_map_conj_inv_map]

theorem twLine_frame_map_conj {m : ModGL Tag.E6 Ω}
    (hsh : ∀ i : Fin 3, (rootSpan Tag.E6 Ω (twE6FrameS i)).map (MulAut.conj m).toMonoidHom =
      rootSpan Tag.E6 Ω (twE6FrameS i)) (i : Fin 3) :
    (e6LineFactor Ω i).map (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) *
        m * (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹)).toMonoidHom =
      e6LineFactor Ω i := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) with hn
  rw [← twLine_frame_map, map_conj_mul_aux, map_conj_mul_aux, ← map_conj_mul_aux _ n⁻¹ n,
    inv_mul_cancel]
  have h1 : (rootSpan Tag.E6 Ω (twE6FrameS i)).map (MulAut.conj (1 : ModGL Tag.E6 Ω)).toMonoidHom =
      rootSpan Tag.E6 Ω (twE6FrameS i) := by
    ext x
    simp [Subgroup.mem_map, MulAut.conj_apply]
  rw [h1, hsh i]

theorem twLine_shift_zero (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (hnc : ∃ a ∈ rootSpan Tag.E6 Ω (twE6FrameS 0), ∃ b ∈ rootSpan Tag.E6 Ω (twE6FrameS 0),
      a * b ≠ b * a) {m : ModGL Tag.E6 Ω} (hm : m ∈ adjointGroup Tag.E6 Ω)
    (hmd : rootDiagUnit Tag.E6 (twLineChar ω) * m = m * rootDiagUnit Tag.E6 (twLineChar ω))
    (hsh : ∀ i : Fin 3, (rootSpan Tag.E6 Ω (twE6FrameS i)).map (MulAut.conj m).toMonoidHom =
      rootSpan Tag.E6 Ω (twE6FrameS i)) :
    m ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (⋃ i, twE6FrameS i) := by
  obtain ⟨m₁, hm₁, j, hj, hje⟩ := e6Line_centralizer_mul h3 h1
    (twLine_conj_mem_toralCentralizer h3 hm hmd)
  have hnorm : (e6LineFactor Ω 0).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω e6LineWeyl ^ j)).toMonoidHom =
        e6LineFactor Ω 0 := by
    have e : canonicalRep (coxeterSystem Tag.E6) Ω e6LineWeyl ^ j =
        m₁⁻¹ * (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) * m *
          (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹) := by
      rw [hje, inv_mul_cancel_left]
    rw [e, map_conj_mul_aux, twLine_frame_map_conj hsh 0]
    exact map_conj_eq_of_mem_normalizer_aux (inv_mem (e6LineFactor_normalizer h3 h1 0 hm₁))
  have hdist : ∀ k : Fin 3, k ≠ 0 → e6LineFactor Ω k ≠ e6LineFactor Ω 0 := by
    intro k hk he
    have he' : rootSpan Tag.E6 Ω (twE6FrameS k) = rootSpan Tag.E6 Ω (twE6FrameS 0) := by
      rw [← twLine_map_conj_inv_map (rootSpan Tag.E6 Ω (twE6FrameS k))
          (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0)),
        ← twLine_map_conj_inv_map (rootSpan Tag.E6 Ω (twE6FrameS 0))
          (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0)),
        twLine_frame_map, twLine_frame_map, he]
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    rw [← he'] at hb
    exact hab (rootSpan_commute_of_orth (Or.inr (Or.inl rfl)) (fun α hα => twE6FrameS_root 0 hα)
      (fun α hα => twE6FrameS_root k hα) (twE6FrameS_orth hk.symm) a ha b hb)
  have hj0 : j = 0 := by
    interval_cases j
    · rfl
    · exfalso
      rw [pow_one, e6LineFactor_conj] at hnorm
      exact hdist 1 (by decide) (by simpa using hnorm)
    · exfalso
      rw [pow_two, map_conj_mul_aux, e6LineFactor_conj, e6LineFactor_conj] at hnorm
      exact hdist 2 (by decide) (by simpa using hnorm)
  rw [hj0, pow_zero, mul_one] at hje
  have hm₁' : m₁ ∈ torusGroup Tag.E6 Ω ⊔
      rootSpan Tag.E6 Ω (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
    have e : toralRootGroup Tag.E6 Ω (e6LineChar ω) =
        torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (rootCharKernel (e6LineChar ω)) := rfl
    rw [e, e6Line_kernel h3 h1] at hm₁
    exact hm₁
  have h := twLine_inv_conj_mem_torusGroup_sup (twE6FrameWeyl 0) (S := ⋃ i, twE6FrameS i)
    (fun γ hγ => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hγ
      rw [← twE6FrameWeyl_zero_image i] at hi
      obtain ⟨α, hα, rfl⟩ := hi
      exact ⟨CFSG.LieType.Chevalley.IsRoot.smul (twE6FrameS_root i hα) _,
        Set.mem_iUnion.2 ⟨i, by simpa using hα⟩⟩) hm₁'
  rw [← hje] at h
  have e : (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹ *
      (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) * m *
        (canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0))⁻¹) *
      canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl 0) = m := by group
  rwa [e] at h

end Shift

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
