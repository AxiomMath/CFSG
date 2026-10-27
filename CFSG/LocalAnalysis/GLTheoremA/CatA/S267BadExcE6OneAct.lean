module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHR2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActData
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRTypes
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.NoOffE6Three

section Act

variable {Ω : Type} [Group Ω] {S : Subgroup Ω}

theorem card_inf_comap_eq {M : Type*} [Group M] (Γ : Ω →* M) {B : Subgroup Ω} {U : Subgroup M}
    (hU : U ≤ B.map Γ) : Nat.card ↥(B ⊓ U.comap Γ) = Nat.card U * Nat.card ↥(B ⊓ Γ.ker) := by
  have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ (B ⊓ U.comap Γ)
  have h1 : (B ⊓ U.comap Γ).map Γ = U := by
    refine le_antisymm ?_ fun u hu => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · obtain ⟨x, hx, rfl⟩ := hU hu
      exact ⟨x, ⟨hx, hu⟩, rfl⟩
  have h2 : B ⊓ U.comap Γ ⊓ Γ.ker = B ⊓ Γ.ker := by
    refine le_antisymm (inf_le_inf_right _ inf_le_left) fun x hx => ⟨⟨hx.1, ?_⟩, hx.2⟩
    change Γ x ∈ U
    rw [MonoidHom.mem_ker.1 hx.2]
    exact one_mem U
  rw [h1, h2] at h
  exact h.symm

end Act

section Diag

variable {τ : Tag} {K : Type} [Field K]

theorem map_rootSpan_subgroupOf_rootDiagAut (a : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) :
    ((rootSpan τ K S).subgroupOf (adjointGroup τ K)).map (rootDiagAut τ K a).toMonoidHom =
      (rootSpan τ K S).subgroupOf (adjointGroup τ K) := by
  have hS' : (rootSpan τ K S).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = rootSpan τ K S :=
    map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a (hS α hα)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    change ((rootDiagAut τ K a y : ↥(adjointGroup τ K)) : ModGL τ K) ∈ _
    rw [coe_rootDiagAut, ← hS']
    exact ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf, ← hS'] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, rootSpan_le_adjointGroup K _ hy⟩, Subgroup.mem_subgroupOf.2 hy, Subtype.ext ?_⟩
    change ((rootDiagAut τ K a ⟨y, _⟩ : ↥(adjointGroup τ K)) : ModGL τ K) = x
    rw [coe_rootDiagAut]
    exact hyx

end Diag

section Core

variable {K : Type} [Field K]

theorem ofAdd_smul_eq_pow (s : ZMod 3) (v : Fin Tag.E6.rank → ZMod 3) :
    Multiplicative.ofAdd (s • v) = Multiplicative.ofAdd v ^ s.val := by
  rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

@[expose] noncomputable def diagHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ModGL .E6 K :=
  (rootDiagUnitHom .E6 K).comp (zetaHom ζ hζ)

theorem coe_diag3_apply (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (z : Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (g : adjointGroup .E6 K) :
    ((diag3 ζ hζ z g : adjointGroup .E6 K) : ModGL .E6 K) =
      diagHom ζ hζ z * (g : ModGL .E6 K) * (diagHom ζ hζ z)⁻¹ :=
  rfl

theorem diag3_eq_rootDiagAut (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (z : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    diag3 (K := K) ζ hζ z = rootDiagAut .E6 K (zetaHom ζ hζ z) :=
  rfl

theorem zetaHom_single (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (j : Fin Tag.E6.rank) :
    zetaHom ζ hζ (Multiplicative.ofAdd (Pi.single j 1)) = Pi.mulSingle j ζ := by
  funext i
  rw [zetaHom_apply, CFSG.StandardType.TableBExc.E6Three.zetaVec_apply]
  by_cases hi : i = j
  · subst hi
    rw [Pi.single_eq_same, Pi.mulSingle_eq_same]
    exact pow_one ζ
  · rw [Pi.single_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi, ZMod.val_zero, pow_zero]

theorem fix_iff_commute {Ω : Type} [Group Ω] {B : Subgroup Ω} (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (Γ : Ω →* MulAut (adjointGroup .E6 K)) {T : Set (Multiplicative (Fin Tag.E6.rank → ZMod 3))}
    {W : Subgroup (Multiplicative (Fin Tag.E6.rank → ZMod 3))} (hTW : T ⊆ W)
    (hWT : W ≤ Subgroup.closure T) (hTB : ∀ t ∈ T, diag3 ζ hζ t ∈ B.map Γ)
    (g : adjointGroup .E6 K) :
    (∀ x : ↥B, (x : Ω) ∈ B ⊓ (W.map (diag3 ζ hζ)).comap Γ → Γ x g = g) ↔
      ∀ t ∈ T, diagHom ζ hζ t * (g : ModGL .E6 K) = (g : ModGL .E6 K) * diagHom ζ hζ t := by
  constructor
  · intro h t ht
    obtain ⟨x, hx, hxt⟩ := hTB t ht
    have h1 := congrArg Subtype.val (h ⟨x, hx⟩ ⟨hx, ⟨t, hTW ht, hxt.symm⟩⟩)
    rw [hxt, coe_diag3_apply] at h1
    calc diagHom ζ hζ t * (g : ModGL .E6 K)
        = diagHom ζ hζ t * (g : ModGL .E6 K) * (diagHom ζ hζ t)⁻¹ * diagHom ζ hζ t := by group
      _ = (g : ModGL .E6 K) * diagHom ζ hζ t := by rw [h1]
  · intro h x hx
    obtain ⟨z, hz, hzx⟩ := hx.2
    have hzc : z ∈ (Subgroup.centralizer {(g : ModGL .E6 K)}).comap (diagHom ζ hζ) :=
      (Subgroup.closure_le ((Subgroup.centralizer {(g : ModGL .E6 K)}).comap
        (diagHom ζ hζ))).2 (fun t ht => Subgroup.mem_comap.2
          (Subgroup.mem_centralizer_singleton_iff.2 (h t ht))) (hWT hz)
    have hzc' : diagHom ζ hζ z * (g : ModGL .E6 K) = (g : ModGL .E6 K) * diagHom ζ hζ z :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hzc)
    apply Subtype.ext
    rw [← hzx, coe_diag3_apply, hzc', mul_inv_cancel_right]

theorem actData_of_diagAct {Ω : Type} [Group Ω] {B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (σ : K ≃+* K)
    (Γ : Ω →* MulAut (adjointGroup .E6 K)) (hBker : Nat.card ↥(B ⊓ Γ.ker) = 3)
    (hB4 : 3 ^ 4 ≤ Nat.card B)
    (hBV : ∀ x ∈ B, ∃ z, ∃ k : ℕ, Γ x = diag3 ζ hζ z * entrywiseAdjointAut .E6 σ ^ k)
    (hd₁ : diag3 ζ hζ (Multiplicative.ofAdd (Pi.single (highNode .E6) 1)) ∈ B.map Γ)
    {y : Fin Tag.E6.rank → ZMod 3} (hy1 : y (highNode .E6) = 0) (hy0 : y ≠ 0)
    (hdy : diag3 ζ hζ (Multiplicative.ofAdd y) ∈ B.map Γ)
    (hJ₂q : CFSG.Open.IsQuasisimple ↥(rootSpan Tag.E6 K
      (rootCharKernel (Pi.mulSingle (highNode .E6) ζ) ∩
        rootCharKernel (zetaHom ζ hζ (Multiplicative.ofAdd y)))))
    {i₂ : Fin Tag.E6.rank}
    (he₂ : (Pi.single i₂ 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel (Pi.mulSingle (highNode .E6) ζ) ∩
        rootCharKernel (zetaHom ζ hζ (Multiplicative.ofAdd y)) ∧
      (-Pi.single i₂ 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel (Pi.mulSingle (highNode .E6) ζ) ∩
        rootCharKernel (zetaHom ζ hζ (Multiplicative.ofAdd y))) :
    ModelGen.ActData 3 B (fun x => Γ x) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  set j₀ := highNode .E6 with hj₀
  set e₁ : Fin Tag.E6.rank → ZMod 3 := Pi.single j₀ 1 with he₁
  set ρ := diagHom (K := K) ζ hζ with hρ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hζo] at h'
    norm_num at h'
  have hζ1 : ζ ≠ 1 := fun h => hζ2 (by rw [h, one_pow])
  have hk : ∀ γ, IsRoot .E6 γ → |γ (highNode .E6)| ≤ 2 := fun γ hγ =>
    abs_coeff_highNode_le_two (Or.inl rfl) hγ
  have hρe₁ : ρ (Multiplicative.ofAdd e₁) = rootDiagUnit .E6 (Pi.mulSingle j₀ ζ) := by
    change rootDiagUnit .E6 (zetaHom ζ hζ (Multiplicative.ofAdd e₁)) = _
    rw [he₁, zetaHom_single]
  have hker₁ : rootCharKernel (Pi.mulSingle j₀ ζ) = perpRoots .E6 :=
    rootCharKernel_mulSingle hζ1 hζ2 hk
  set P₂ : Multiplicative (ZMod 3 × ZMod 3) →* Multiplicative (Fin Tag.E6.rank → ZMod 3) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mk' (fun s => s.1 • e₁ + s.2 • y) (fun s t => by
      simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel)) with hP₂
  have hP₂apply : ∀ s, P₂ s = Multiplicative.ofAdd ((Multiplicative.toAdd s).1 • e₁ +
      (Multiplicative.toAdd s).2 • y) := fun s => rfl
  have hP₂inj : Function.Injective P₂ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    rw [hP₂apply] at hs
    have h0 : (Multiplicative.toAdd s).1 • e₁ + (Multiplicative.toAdd s).2 • y = 0 :=
      congrArg Multiplicative.toAdd hs
    have h1 : (Multiplicative.toAdd s).1 = 0 := by
      have := congrFun h0 j₀
      simpa [he₁, hy1] using this
    rw [h1, zero_smul, zero_add, smul_eq_zero] at h0
    have h2 : (Multiplicative.toAdd s).2 = 0 := h0.resolve_right hy0
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Prod.ext h1 h2
  set W₁ : Subgroup (Multiplicative (Fin Tag.E6.rank → ZMod 3)) :=
    Subgroup.zpowers (Multiplicative.ofAdd e₁) with hW₁
  set W₂ : Subgroup (Multiplicative (Fin Tag.E6.rank → ZMod 3)) := P₂.range with hW₂
  have he₁W₂ : Multiplicative.ofAdd e₁ ∈ W₂ := ⟨Multiplicative.ofAdd (1, 0), by
    rw [hP₂apply]
    simp⟩
  have hyW₂ : Multiplicative.ofAdd y ∈ W₂ := ⟨Multiplicative.ofAdd (0, 1), by
    rw [hP₂apply]
    simp⟩
  have hW₁₂ : W₁ ≤ W₂ := (Subgroup.zpowers_le).2 he₁W₂
  have hW₂cl : W₂ ≤ Subgroup.closure {Multiplicative.ofAdd e₁, Multiplicative.ofAdd y} := by
    rintro _ ⟨s, rfl⟩
    rw [hP₂apply, ofAdd_add, ofAdd_smul_eq_pow, ofAdd_smul_eq_pow]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  have hW₁cl : W₁ ≤ Subgroup.closure {Multiplicative.ofAdd e₁} := by
    rw [hW₁, Subgroup.zpowers_eq_closure]
  have he₁ne : e₁ ≠ 0 := fun h => by
    have := congrFun h j₀
    simp [he₁] at this
  have hW₁c : Nat.card W₁ = 3 := by
    rw [hW₁, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, toAdd_ofAdd]
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    · intro h
      exact he₁ne (congrArg Multiplicative.toAdd h)
  have hW₂c : Nat.card W₂ = 9 := by
    rw [hW₂, card_range_of_injective' hP₂inj, card_multiplicative_prod]
    norm_num
  set U₁ := W₁.map (diag3 ζ hζ) with hU₁
  set U₂ := W₂.map (diag3 ζ hζ) with hU₂
  have hT₁ : ∀ t ∈ ({Multiplicative.ofAdd e₁} : Set _), diag3 ζ hζ t ∈ B.map Γ := by
    rintro t rfl
    exact hd₁
  have hT₂ : ∀ t ∈ ({Multiplicative.ofAdd e₁, Multiplicative.ofAdd y} : Set _),
      diag3 ζ hζ t ∈ B.map Γ := by
    rintro t (rfl | rfl)
    · exact hd₁
    · exact hdy
  have hU₁B : U₁ ≤ B.map Γ := Subgroup.map_le_iff_le_comap.2 (hW₁cl.trans
    ((Subgroup.closure_le _).2 fun t ht => hT₁ t ht))
  have hU₂B : U₂ ≤ B.map Γ := Subgroup.map_le_iff_le_comap.2 (hW₂cl.trans
    ((Subgroup.closure_le _).2 fun t ht => hT₂ t ht))
  have hdinj := diag3_injective (K := K) hζo hζ
  have hU₁c : Nat.card U₁ = 3 := by rw [hU₁, Subgroup.card_map_of_injective hdinj, hW₁c]
  have hU₂c : Nat.card U₂ = 9 := by rw [hU₂, Subgroup.card_map_of_injective hdinj, hW₂c]
  have hB₀ : Nat.card ↥(B ⊓ Γ.ker) = 3 := hBker
  set D := B ⊓ U₁.comap Γ with hD
  set E := B ⊓ U₂.comap Γ with hE
  have hDc : Nat.card D = 3 ^ 2 := by rw [hD, card_inf_comap_eq Γ hU₁B, hU₁c, hB₀]; norm_num
  have hEc : Nat.card E = 3 ^ 3 := by rw [hE, card_inf_comap_eq Γ hU₂B, hU₂c, hB₀]; norm_num
  have hDE : D ≤ E := inf_le_inf_left _ (Subgroup.comap_mono (Subgroup.map_mono hW₁₂))
  set α : ↥B → MulAut ↥(adjointGroup .E6 K) := fun x => Γ x with hα
  have hfixD : ∀ g : ↥(adjointGroup .E6 K), g ∈ ModelGen.actFix α D ↔
      ρ (Multiplicative.ofAdd e₁) * (g : ModGL .E6 K) =
        (g : ModGL .E6 K) * ρ (Multiplicative.ofAdd e₁) := by
    intro g
    have h := fix_iff_commute (B := B) ζ hζ Γ (T := {Multiplicative.ofAdd e₁}) (W := W₁)
      (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers _)) hW₁cl hT₁ g
    simp only [Set.mem_singleton_iff, forall_eq] at h
    exact h
  have hfixE : ∀ g : ↥(adjointGroup .E6 K), g ∈ ModelGen.actFix α E ↔
      (ρ (Multiplicative.ofAdd e₁) * (g : ModGL .E6 K) =
        (g : ModGL .E6 K) * ρ (Multiplicative.ofAdd e₁)) ∧
      (ρ (Multiplicative.ofAdd y) * (g : ModGL .E6 K) =
        (g : ModGL .E6 K) * ρ (Multiplicative.ofAdd y)) := by
    intro g
    have h := fix_iff_commute (B := B) ζ hζ Γ
      (T := {Multiplicative.ofAdd e₁, Multiplicative.ofAdd y}) (W := W₂)
      (by rintro t (rfl | rfl); exacts [he₁W₂, hyW₂]) hW₂cl hT₂ g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
    exact h
  set J : Subgroup ↥(adjointGroup .E6 K) := (rootSpan .E6 K (perpRoots .E6)).subgroupOf (adjointGroup .E6 K) with hJ
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).symm
      (isQuasisimple_perpLevi_E6 hK2)
  have hi₁ : (3 : Fin Tag.E6.rank) ≠ j₀ := by decide
  have he₃ : (Pi.single (3 : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) ∈ perpRoots .E6 :=
    ⟨IsRoot.basis _, Pi.single_eq_of_ne' hi₁ 1⟩
  have he₃' : (-Pi.single (3 : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) ∈ perpRoots .E6 :=
    ⟨IsRoot.neg (IsRoot.basis _), by rw [Pi.neg_apply, Pi.single_eq_of_ne' hi₁ 1, neg_zero]⟩
  have hpJ : 3 ∣ Nat.card ↥J := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).toEquiv]
    exact dvd_card_rootSpan Nat.prime_three (by norm_num) hζo he₃ he₃'
  have hJfix : J ≤ ModelGen.actFix α D := by
    intro j hj
    rw [hfixD, hρe₁]
    exact (commute_of_mem_toralCentralizer (rootSpan_perpRoots_le_toralCentralizer ζ
      (Subgroup.mem_subgroupOf.1 hj))).symm
  have hJn : (J.subgroupOf (ModelGen.actFix α D)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := (hfixD g).1 g.2
    rw [hρe₁] at h1
    have hg : ((g : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈ toralCentralizer .E6 K (Pi.mulSingle j₀ ζ) :=
      mem_toralCentralizer_of_commute (g : ↥(adjointGroup .E6 K)).2 h1.symm
    have hN := (Subgroup.mem_normalizer_iff.1 (toralCentralizer_mulSingle_le_normalizer hζ1 hζ2 hk
      hg) ((n : ↥(adjointGroup .E6 K)) : ModGL .E6 K)).1 (Subgroup.mem_subgroupOf.1 hn)
    rw [Subgroup.mem_subgroupOf]
    simpa using hN
  have hJcomp : GLAPComponent 3 (ModelGen.actFix α D) J :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hJq hpJ hJfix hJn
  have hJB : ∀ x : ↥B, J.map (α x).toMonoidHom = J := by
    intro x
    obtain ⟨z, k, hz⟩ := hBV x x.2
    change J.map (Γ x).toMonoidHom = J
    have hcomp : (diag3 ζ hζ z * entrywiseAdjointAut .E6 σ ^ k).toMonoidHom =
        (diag3 ζ hζ z).toMonoidHom.comp (entrywiseAdjointAut .E6 σ ^ k).toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [hz, hcomp, ← Subgroup.map_map, ← entrywiseAdjointAut_pow, map_perpJ_entrywiseAdjointAut,
      diag3_eq_rootDiagAut]
    exact map_rootSpan_subgroupOf_rootDiagAut _ fun _ hα => hα.1
  have hJD : ∀ x : ↥B, (∀ j ∈ J, j * (α x j)⁻¹ ∈ GLAPPrimeCoreOf 3 J) → (x : Ω) ∈ D := by
    intro x hx
    obtain ⟨z, k, hz⟩ := hBV x x.2
    have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf
      Nat.prime_three hJq hpJ (Γ x).toMonoidHom fun j hj => by
        have h2 := (GLAPPrimeCoreOf 3 J).inv_mem (hx j hj)
        rwa [_root_.mul_inv_rev, inv_inv] at h2
    have hroot : ∀ i, i ≠ j₀ → ∀ c : K,
        (rootChar (zetaHom ζ hζ z) (Pi.single i 1) : K) * (σ ^ k) c = c := by
      intro i hi c
      have hjmem : pinnedX .E6 K (Pi.single i 1) c ∈ adjointGroup .E6 K := by
        rw [pinnedX_single]
        exact xUnit_mem_adjointGroup i c
      have hjJ : (⟨_, hjmem⟩ : ↥(adjointGroup .E6 K)) ∈ J := by
        rw [hJ, Subgroup.mem_subgroupOf]
        exact pinnedX_mem_rootSpan (S := perpRoots .E6) (α := Pi.single i 1)
          ⟨IsRoot.basis i, Pi.single_eq_of_ne' hi 1⟩ c
      have h : ((Γ x ⟨_, hjmem⟩ : ↥(adjointGroup .E6 K)) : ModGL .E6 K) = pinnedX .E6 K (Pi.single i 1) c :=
        congrArg Subtype.val (hfix _ hjJ)
      rw [hz, MulAut.mul_apply, coe_diag3_apply, ← entrywiseAdjointAut_pow,
        coe_entrywiseAdjointAut] at h
      change rootDiagUnit .E6 (zetaHom ζ hζ z) *
        (Units.map (entrywiseHom (σ ^ k).toRingHom) (pinnedX .E6 K (Pi.single i 1) c)) *
          (rootDiagUnit .E6 (zetaHom ζ hζ z))⁻¹ = pinnedX .E6 K (Pi.single i 1) c at h
      have he : Units.map (entrywiseHom (σ ^ k).toRingHom) (pinnedX .E6 K (Pi.single i 1) c) =
          pinnedX .E6 K (Pi.single i 1) ((σ ^ k) c) :=
        Units.ext (entrywise_pinnedX (σ ^ k).toRingHom (Pi.single i 1) c)
      rw [he, rootDiagUnit_conj_pinnedX _ (IsRoot.basis i)] at h
      exact pinnedX_injective (R := K) (τ := .E6) (Pi.single i 1) h
    have hi₃ : (3 : Fin Tag.E6.rank) ≠ j₀ := by decide
    have hσk : σ ^ k = 1 := by
      ext c
      have h1 := hroot 3 hi₃ 1
      rw [map_one, mul_one] at h1
      have h2 := hroot 3 hi₃ c
      rw [h1, one_mul] at h2
      exact h2
    have hcoord : ∀ i, i ≠ j₀ → Multiplicative.toAdd z i = 0 := by
      intro i hi
      have h' := hroot i hi 1
      rw [map_one, mul_one, rootChar_single] at h'
      have h'' : ζ ^ (Multiplicative.toAdd z i).val = 1 := Units.ext h'
      have hdvd := orderOf_dvd_of_pow_eq_one h''
      rw [hζo] at hdvd
      exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
    have hzW : z ∈ W₁ := by
      have hz' : z = Multiplicative.ofAdd e₁ ^ (Multiplicative.toAdd z j₀).val := by
        rw [← ofAdd_smul_eq_pow]
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd]
        funext i
        by_cases hi : i = j₀
        · subst hi
          simp [he₁]
        · rw [hcoord i hi]
          simp [he₁, Pi.single_eq_of_ne hi]
      rw [hz']
      exact pow_mem (Subgroup.mem_zpowers _) _
    have hΓx : Γ x = diag3 ζ hζ z := by
      rw [hz, ← entrywiseAdjointAut_pow, hσk]
      rw [show entrywiseAdjointAut .E6 (1 : K ≃+* K) = 1 from
        map_one (entrywiseAdjointAutHom (τ := .E6) (K := K)), mul_one]
    exact ⟨x.2, ⟨z, hzW, hΓx.symm⟩⟩
  set S₂ := rootCharKernel (Pi.mulSingle j₀ ζ) ∩
    rootCharKernel (zetaHom ζ hζ (Multiplicative.ofAdd y)) with hS₂
  set J₂ : Subgroup ↥(adjointGroup .E6 K) := (rootSpan .E6 K S₂).subgroupOf (adjointGroup .E6 K) with hJ₂
  have hJE : Nat.card D = 3 ^ 2 → GLAPLayer 3 (J ⊓ ModelGen.actFix α E) ≠ ⊥ := by
    intro _
    have hJ₂q' : CFSG.Open.IsQuasisimple ↥J₂ :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).symm hJ₂q
    have hpJ₂ : 3 ∣ Nat.card ↥J₂ := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).toEquiv]
      exact dvd_card_rootSpan Nat.prime_three (by norm_num) hζo he₂.1 he₂.2
    have hS₂perp : S₂ ⊆ perpRoots .E6 := fun γ hγ => hker₁ ▸ hγ.1
    have hJ₂J : J₂ ≤ J := fun x hx =>
      Subgroup.mem_subgroupOf.2 (rootSpan_mono hS₂perp (Subgroup.mem_subgroupOf.1 hx))
    have hJ₂fix : J₂ ≤ ModelGen.actFix α E := by
      intro j hj
      rw [hfixE]
      have hj' := Subgroup.mem_subgroupOf.1 hj
      refine ⟨?_, ?_⟩
      · rw [hρe₁]
        exact (Subgroup.mem_centralizer_singleton_iff.1
          (rootSpan_le_centralizer _ Set.inter_subset_left hj')).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.1
          (rootSpan_le_centralizer _ Set.inter_subset_right hj')).symm
    have hJ₂n : (J₂.subgroupOf (ModelGen.actFix α E)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨h1, h2⟩ := (hfixE g).1 g.2
      rw [hρe₁] at h1
      have hg : ((g : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈ toralCentralizer .E6 K (Pi.mulSingle j₀ ζ) ⊓
          toralCentralizer .E6 K (zetaHom ζ hζ (Multiplicative.ofAdd y)) :=
        ⟨mem_toralCentralizer_of_commute (g : ↥(adjointGroup .E6 K)).2 h1.symm,
          mem_toralCentralizer_of_commute (g : ↥(adjointGroup .E6 K)).2 h2.symm⟩
      have hN := (Subgroup.mem_normalizer_iff.1 (toralCentralizer_inf_le_normalizer _ _ hg)
        ((n : ↥(adjointGroup .E6 K)) : ModGL .E6 K)).1 (Subgroup.mem_subgroupOf.1 hn)
      rw [Subgroup.mem_subgroupOf]
      simpa using hN
    have hJ₂comp : GLAPComponent 3 (ModelGen.actFix α E) J₂ :=
      CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hJ₂q' hpJ₂
        hJ₂fix hJ₂n
    have hJ₂c : GLAPComponent 3 (J ⊓ ModelGen.actFix α E) J₂ :=
      glaPComponent_of_le Nat.prime_three hJ₂comp (le_inf hJ₂J hJ₂fix) inf_le_right
    intro hbot
    have hle : J₂ ≤ GLAPLayer 3 (J ⊓ ModelGen.actFix α E) := le_sSup hJ₂c
    rw [hbot, le_bot_iff] at hle
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ₂c hle
  have htmem : rootDiagUnit .E6 (Pi.mulSingle j₀ (-1 : Kˣ)) ∈ adjointGroup .E6 K :=
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
      (rootDiagUnit_mulSingle_mem_torusGroup (sum_highRoot_mul_cartan (Or.inl rfl)) _)
  set t : ↥(adjointGroup .E6 K) := ⟨_, htmem⟩ with ht
  have ht1 : t ≠ 1 := by
    intro h1
    have h := congrArg (fun g : ↥(adjointGroup .E6 K) => (g : ModGL .E6 K)) h1
    change rootDiagUnit .E6 (Pi.mulSingle j₀ (-1 : Kˣ)) = 1 at h
    rw [← rootDiagUnit_one (τ := .E6) (K := K)] at h
    have h' := congrFun (rootDiagUnit_injective h) j₀
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h'
    exact hK2 ((neg_one_eq_one_iff (R := K)).1 (by simpa using congrArg Units.val h'))
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    change rootDiagUnit .E6 (Pi.mulSingle j₀ (-1 : Kˣ)) ^ 2 = 1
    rw [rootDiagUnit_pow_hr, ← rootDiagUnit_one (τ := .E6) (K := K)]
    congr 1
    rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]
  have htJ : J ≤ Subgroup.centralizer ({t} : Set ↥(adjointGroup .E6 K)) := by
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (j : ModGL .E6 K) * rootDiagUnit .E6 (Pi.mulSingle j₀ (-1 : Kˣ)) =
      rootDiagUnit .E6 (Pi.mulSingle j₀ (-1 : Kˣ)) * (j : ModGL .E6 K)
    exact commute_of_mem_toralCentralizer
      (rootSpan_perpRoots_le_toralCentralizer (-1 : Kˣ) (Subgroup.mem_subgroupOf.1 hj))
  have htD : ∀ x : ↥B, (x : Ω) ∈ D → α x t = t := by
    intro x hxD
    obtain ⟨z, -, hz⟩ := hxD.2
    replace hz := hz.symm
    apply Subtype.ext
    change ((Γ x t : ↥(adjointGroup .E6 K)) : ModGL .E6 K) = rootDiagUnit .E6 (Pi.mulSingle j₀ (-1 : Kˣ))
    rw [hz, coe_diag3_apply]
    change rootDiagUnit .E6 (zetaHom ζ hζ z) * rootDiagUnit .E6 (Pi.mulSingle j₀ (-1 : Kˣ)) *
      (rootDiagUnit .E6 (zetaHom ζ hζ z))⁻¹ = _
    rw [← rootDiagUnit_mul, mul_comm, rootDiagUnit_mul, mul_inv_cancel_right]
  have hDBc : 3 ^ 2 * Nat.card D ≤ Nat.card B := by
    rw [hDc]
    have h4 := hB4
    norm_num at h4 ⊢
    exact h4
  exact ⟨D, E, J, t, inf_le_left, inf_le_left, hDE, hDc.ge, hDBc, fun _ => hEc, hJcomp, hJB, hJD,
    hJE, ht1, ht2, htJ, htD⟩

@[expose] def yHyp : Fin Tag.E6.rank → ZMod 3 := ![2, 0, 2, 0, 0, 0]

theorem yHyp_mem_hypE6 : yHyp ∈ CFSG.StandardType.NoOffRest.hypE6 :=
  CFSG.StandardType.NoOffRest.mem_hypE6.2 (by decide)

@[expose] def yHypKerCheck : Bool :=
  (List.range Tag.E6.rootCertificate.roots.length).all fun m =>
    decide (Tag.E6.rootCertificate.root m 1 = 0 →
      (Tag.E6.rootCertificate.root m 0 + Tag.E6.rootCertificate.root m 2) % 3 = 0 →
        Tag.E6.rootCertificate.root m 0 = 0 ∧ Tag.E6.rootCertificate.root m 2 = 0)

theorem yHypKerCheck_eq : yHypKerCheck = true := by decide +kernel

theorem eq_zero_of_yHyp {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (h1 : γ 1 = 0)
    (h3 : (γ 0 + γ 2) % 3 = 0) : γ 0 = 0 ∧ γ 2 = 0 := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq Tag.E6.rootCertificate_check hγ
  have h := yHypKerCheck_eq
  simp only [yHypKerCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h m hm h1 h3

theorem rootChar_zetaHom_yHyp (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (zetaHom ζ hζ (Multiplicative.ofAdd yHyp)) γ = ζ ^ (2 * (γ 0 + γ 2)) := by
  unfold rootChar
  change (∏ i : Fin 6, (zetaHom ζ hζ (Multiplicative.ofAdd yHyp)) i ^ γ i) = _
  rw [Fin.prod_univ_six]
  change (ζ ^ 2) ^ γ 0 * (ζ ^ 0) ^ γ 1 * (ζ ^ 2) ^ γ 2 * (ζ ^ 0) ^ γ 3 * (ζ ^ 0) ^ γ 4 *
    (ζ ^ 0) ^ γ 5 = _
  rw [pow_zero, one_zpow, one_zpow, one_zpow, one_zpow, mul_one, mul_one, mul_one, mul_one,
    ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_add]
  rfl

theorem rootCharKernel_inter_yHyp {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    rootCharKernel (Pi.mulSingle (highNode .E6) ζ) ∩
        rootCharKernel (zetaHom ζ hζ (Multiplicative.ofAdd yHyp)) =
      leviRootsOff .E6 {0, 1, 2} := by
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hζo] at h'
    norm_num at h'
  have hζ1 : ζ ≠ 1 := fun h => hζ2 (by rw [h, one_pow])
  ext γ
  constructor
  · rintro ⟨⟨hγ, h1⟩, ⟨-, h2⟩⟩
    rw [rootChar_mulSingle] at h1
    have hγ1 : γ 1 = 0 :=
      eq_zero_of_zpow_eq_one hζ1 hζ2 (abs_coeff_highNode_le_two (Or.inl rfl) hγ) h1
    rw [rootChar_zetaHom_yHyp, ← orderOf_dvd_iff_zpow_eq_one, hζo] at h2
    have h3 : (γ 0 + γ 2) % 3 = 0 := by omega
    obtain ⟨h0, h2'⟩ := eq_zero_of_yHyp hγ hγ1 h3
    refine ⟨hγ, fun i hi => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h0
    · exact hγ1
    · exact h2'
  · rintro ⟨hγ, h0⟩
    have g0 : γ 0 = 0 := h0 0 (by simp)
    have g1 : γ 1 = 0 := h0 1 (by simp)
    have g2 : γ 2 = 0 := h0 2 (by simp)
    refine ⟨⟨hγ, ?_⟩, ⟨hγ, ?_⟩⟩
    · rw [rootChar_mulSingle]
      change ζ ^ γ 1 = 1
      rw [g1, zpow_zero]
    · rw [rootChar_zetaHom_yHyp, g0, g2]
      simp

private def parA3 : Fin Tag.E6.rank → Fin Tag.E6.rank := ![0, 0, 0, 3, 3, 4]
private def depA3 : Fin Tag.E6.rank → ℕ := ![0, 0, 0, 0, 1, 2]

theorem isQuasisimple_rootSpan_leviRootsOff_E6_A3 (hK2 : ringChar K ≠ 2) :
    CFSG.Open.IsQuasisimple ↥(rootSpan Tag.E6 K (leviRootsOff .E6 {0, 1, 2})) :=
  isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) _ (i₀ := (3 : Fin Tag.E6.rank))
    (i₁ := (4 : Fin Tag.E6.rank)) (by decide) (by decide) (by decide) parA3 depA3 (by decide)

theorem actData_of_diagAct_yHyp {Ω : Type} [Group Ω] {B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (σ : K ≃+* K)
    (Γ : Ω →* MulAut (adjointGroup .E6 K)) (hBker : Nat.card ↥(B ⊓ Γ.ker) = 3)
    (hB4 : 3 ^ 4 ≤ Nat.card B)
    (hBV : ∀ x ∈ B, ∃ z, ∃ k : ℕ, Γ x = diag3 ζ hζ z * entrywiseAdjointAut .E6 σ ^ k)
    (hd₁ : diag3 ζ hζ (Multiplicative.ofAdd (Pi.single (highNode .E6) 1)) ∈ B.map Γ)
    (hdy : diag3 ζ hζ (Multiplicative.ofAdd yHyp) ∈ B.map Γ) :
    ModelGen.ActData 3 B (fun x => Γ x) := by
  have hker := rootCharKernel_inter_yHyp (K := K) hζo hζ
  have h3 : (Pi.single (3 : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) ∈ leviRootsOff .E6 {0, 1, 2} :=
    ⟨IsRoot.basis _, by decide⟩
  have h3' : (-Pi.single (3 : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) ∈
      leviRootsOff .E6 {0, 1, 2} :=
    ⟨IsRoot.neg (IsRoot.basis _), by decide⟩
  refine actData_of_diagAct hK2 hζo hζ σ Γ hBker hB4 hBV hd₁ (y := yHyp) (by decide) (by decide)
    hdy ?_ (i₂ := 3) ?_
  · rw [hker]
    exact isQuasisimple_rootSpan_leviRootsOff_E6_A3 hK2
  · rw [hker]
    exact ⟨h3, h3'⟩

end Core

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

end
