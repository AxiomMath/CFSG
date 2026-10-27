module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriRed
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTriD4Conj
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GTri

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section Equiv


theorem triRecipe_equiv_of {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm n) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hH : MarkChev.twistedH TwistTag.D4.tag.cartan (IsRoot TwistTag.D4.tag) K
      TwistTag.D4.perm n = graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (twistedH_eq_commutator K TwistTag.D4 n σ.toRingHom hσ).trans
      (even_triality_exact_automorphism_normal_form hn K hK σ hσ).2.2.2.2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hroot : ∀ S : (Fin TwistTag.D4.tag.rank → ℤ) → Prop, S = IsRoot TwistTag.D4.tag →
      Nonempty (LargeEvenCenterQuot (MarkChev.twistedH TwistTag.D4.tag.cartan S K
        TwistTag.D4.perm n) ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro S hS
    subst hS
    rw [hH]
    exact ⟨centerQuotEquivOfBot hZ⟩
  have h := hroot (LargeEvenIsRoot TwistTag.D4.tag.cartan) (largeEvenIsRoot_eq_isRoot TwistTag.D4.tag)
  rw [← largeEvenTwistedH_eq TwistTag.D4.tag.cartan K TwistTag.D4.perm n] at h
  exact h

theorem triRecipe_equiv {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) :
    ∃ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) ∧
      Nonempty (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm n) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hK3 : Nat.card K = 2 ^ (n * 3) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK3
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  exact ⟨σ, hσ, triRecipe_equiv_of hn hK σ hσ⟩

theorem tri_congr_conj {G H : Type} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext t
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem tri_not_inner_of_not_mem {R Y : Type} [Group R] [Group Y] (e : R ≃* Y) {u : MulAut R}
    {I : Set (MulAut R)} (hI : ∀ g : R, (MulAut.conj g : MulAut R) ∈ I) (hu : u ∉ I) :
    MulAut.congr e u ∉ (MulAut.conj : Y →* MulAut Y).range := by
  rintro ⟨y, hy⟩
  apply hu
  have h1 : MulAut.congr e.symm (MulAut.congr e u) = u := by
    ext t
    simp [MulAut.congr_apply]
  rw [← hy, tri_congr_conj] at h1
  rw [← h1]
  exact hI _

theorem tri_inn_mem_idImage {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]
    (H : Subgroup (LargeEvenChevGL A K)) (g : LargeEvenCenterQuot H) :
    (MulAut.conj g : MulAut (LargeEvenCenterQuot H)) ∈ LargeEvenChevIDImage A K H :=
  Subgroup.subset_closure (Or.inl ⟨g, rfl⟩)



theorem triFieldTD4_of_rig (hRig : GGLabelRigidInput) : TriFieldTD4 := by
  intro S _ _ α J labK labJ hT hcen hlabK hfld hα hlabJ hJ
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam', hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ0
  subst hlab
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [hT] at hraw
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  have hn : 1 ≤ lab'.n := hlam'.1
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  by_cases hn1 : lab'.n = 1
  · exact fieldRel_of_canon_n_one 3 lab' labJ (by rw [hcanK]; exact hn1)
  have hn2 : 2 ≤ lab'.n := by omega
  obtain ⟨σ, hσ, ⟨eR⟩⟩ := triRecipe_equiv hn hK
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e := eS.trans θ
  let eY := e.trans eR
  have hkey : ∀ s : S, (i * f) (e s) = e (α s) := fun s => hind s (α s) rfl
  have hαe : MulAut.congr e α = i * f := by
    ext r
    have h := hkey (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hnotI : i * f ∉ LargeEvenChevIDImage TwistTag.D4.tag.cartan K
      (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm lab'.n) :=
    fun h => hout ⟨i * f, h, hind⟩
  have hφ3 : MulAut.congr eY α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hcongr0 : MulAut.congr eY α = MulAut.congr eR (MulAut.congr e α) := MulEquiv.ext fun x => rfl
  have hcongr : MulAut.congr eY α = MulAut.congr eR (i * f) := by rw [hcongr0, hαe]
  have hφout : MulAut.congr eY α ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rw [hcongr]
    exact tri_not_inner_of_not_mem eR (tri_inn_mem_idImage _ K _) hnotI
  have hfix : (fixSubgroup α).map eY.toMonoidHom = fixSubgroup (MulAut.congr eY α) :=
    Y10F.fixSubgroup_map_congr eY α
  let eC : ↥(fixSubgroup α) ≃* ↥(fixSubgroup (MulAut.congr eY α)) :=
    (Subgroup.equivMapOfInjective _ eY.toMonoidHom eY.injective).trans (MulEquiv.subgroupCongr hfix)
  have hnJ : (canonLabel labJ).n = lab'.n :=
    triOuter_canon_n hRig hn2 hK σ hσ _ hφ3 hφout eC hJ hlabJ
  refine Or.inl ?_
  rw [hcanK, hnJ]

theorem triFieldTD4_holds : TriFieldTD4 :=
  triFieldTD4_of_rig CFSG.StandardType.ggLabelRigidInput_holds

end Equiv

end CFSG.LocalAnalysis.GLTheoremA.Y10GTri
