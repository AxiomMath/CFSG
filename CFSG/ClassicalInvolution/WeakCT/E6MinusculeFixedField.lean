module

public import CFSG.ClassicalInvolution.WeakCT.OriginalULift
public import CFSG.LocalAnalysis.StandardType.PhanEMinFrob
public import CFSG.LieType.Steinberg.BruhatTwist
public import CFSG.LocalAnalysis.StandardType.PhanEFrobDescent
import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6Torus
import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6Cover

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
open scoped MatrixGroups commutatorElement

theorem e6OrdinaryIsTwist (f : ℕ) :
    CFSG.LieType.Steinberg.IsTwist (e6Datum GGL) (e6Data_valid.nm GGL)
      (e6Data_valid.torus GGL) (Equiv.refl _)
      (minBC e6Data_valid (ggFrobT f)) where
  cartan_perm := by intro i j; rfl
  divisible_perm := by intro i hi; simp at hi
  map_rootGroup := by
    intro γ hγ x hx
    have h := map_rootGroup_minBC_le e6Data_valid (ggFrobT f) γ
      (Subgroup.mem_map_of_mem (minBC e6Data_valid (ggFrobT f)) hx)
    simpa [CFSG.LieType.Steinberg.permVec] using h
  map_n := by
    intro i
    simpa using minBC_nm e6Data_valid (ggFrobT f) i
  map_torus := by
    intro i h hi
    exact map_torus_minBC_le e6Data_valid (ggFrobT f) i
      (Subgroup.mem_map_of_mem (minBC e6Data_valid (ggFrobT f)) hi)

theorem exists_fixed_normal_form {f : ℕ} {g : e6Data_valid.minGroup GGL}
    (hfix : minBC e6Data_valid (ggFrobT f) g = g) :
    ∃ (w : (CFSG.LieType.RootSystem.coxeterMatrix (e6Datum GGL).isFiniteType).Group)
      (b : e6Data_valid.minGroup GGL)
      (u : e6Data_valid.minGroup GGL),
      b ∈ CFSG.LieType.Steinberg.borel (D := e6Datum GGL) (e6Data_valid.torus GGL) ∧
      u ∈ CFSG.LieType.Steinberg.inversionUnipotent (D := e6Datum GGL) w ∧
      minBC e6Data_valid (ggFrobT f) b = b ∧
      minBC e6Data_valid (ggFrobT f) u = u ∧
      g = b * CFSG.LieType.Steinberg.nrep (e6Datum_isCTGroupDatum (k := GGL)) w * u := by
  have hσ := e6OrdinaryIsTwist f
  obtain ⟨w, -, b, hb, hbσ, u, hu, huσ, rfl⟩ :=
    hσ.fixed_normalForm (hct := e6Datum_isCTGroupDatum (k := GGL))
      (hext := e6Datum_steinbergExtras (k := GGL))
      (hBU := e6Datum_bruhatExtras GGL) hfix
  exact ⟨w, b, u, hb, hu, hbσ, huσ, rfl⟩

theorem fixed_rootGroup_mem_range {f : ℕ} (hf : 1 ≤ f)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ (e6Datum GGL).roots)
    {x : e6Data_valid.minGroup GGL}
    (hx : x ∈ (e6Datum GGL).rootGroup γ)
    (hfix : minBC e6Data_valid (ggFrobT f) x = x) :
    x ∈ (minBC e6Data_valid (ggRatEmb f)).range := by
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup GGL).1 hx
  have hfixc : e6Data_valid.xm GGL γ (ggFrobT f c) = e6Data_valid.xm GGL γ c := by
    simpa only [CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm] using hfix
  have hceq : ggFrobT f c = c := e6Data_valid.xm_injective GGL
    ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 GGL).1 hγ) hfixc
  have hc : c ∈ Set.range (ggRatEmb f) := by
    rw [ggRatEmb_range hf]
    simpa [ggFrobT_apply] using hceq
  obtain ⟨a, rfl⟩ := hc
  exact ⟨e6Data_valid.xm (GaloisField 2 f) γ a, by
    rw [CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm]⟩

theorem fixed_torus_mem_range {f : ℕ} (hf : 1 ≤ f)
    {t : e6Data_valid.minGroup GGL}
    (ht : t ∈ ⨆ i, e6Data_valid.torus GGL i)
    (hfix : minBC e6Data_valid (ggFrobT f) t = t) :
    t ∈ (minBC e6Data_valid (ggRatEmb f)).range := by
  have ht' : t ∈ (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid GGL).range := by
    rwa [CFSG.LieType.Steinberg.Minuscule.range_minTorus_e6_eq_iSup]
  obtain ⟨u, rfl⟩ := ht'
  have hmap := CFSG.LieType.SemisimpleCentralizers.HeldLang.minBC_minTorus
    (k := GGL) (k' := GGL) (ι := ggFrobT f) u
  have hfixeq : (fun i => Units.map (ggFrobT f).toMonoidHom (u i)) = u := by
    apply CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus_injective e6Data_valid GGL
    exact hmap.symm.trans hfix
  have hu : ∀ i, Units.map (ggFrobT f).toMonoidHom (u i) = u i :=
    fun i => congrFun hfixeq i
  have h_exists : ∀ i, ∃ a : (GaloisField 2 f)ˣ,
      Units.map (ggRatEmb f).toMonoidHom a = u i := by
    intro i
    have hc : ((u i : GGL) ^ 2 ^ f = (u i : GGL)) := by
      have h := congrArg (fun z : GGLˣ => (z : GGL)) (hu i)
      simpa [ggFrobT_apply] using h
    have hmem : (u i : GGL) ∈ Set.range (ggRatEmb f) := by
      rw [ggRatEmb_range hf]
      exact hc
    let a : GaloisField 2 f := Classical.choose hmem
    have ha : ggRatEmb f a = (u i : GGL) := Classical.choose_spec hmem
    have ha0 : a ≠ 0 := by
      intro h0
      exact (u i).ne_zero (by rw [← ha, h0, map_zero])
    exact ⟨Units.mk0 a ha0, by
      ext
      exact ha⟩
  choose v hv using h_exists
  refine ⟨CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid (GaloisField 2 f) v, ?_⟩
  rw [CFSG.LieType.SemisimpleCentralizers.HeldLang.minBC_minTorus]
  congr 1
  funext i
  exact hv i

theorem fixed_posUnipotent_mem_range {f : ℕ} (hf : 1 ≤ f)
    {u : e6Data_valid.minGroup GGL}
    (hu : u ∈ CFSG.LieType.Steinberg.posUnipotent (e6Datum GGL))
    (hfix : minBC e6Data_valid (ggFrobT f) u = u) :
    u ∈ (minBC e6Data_valid (ggRatEmb f)).range := by
  let hct := e6Datum_isCTGroupDatum (k := GGL)
  let hext := e6Datum_steinbergExtras (k := GGL)
  let σ := minBC e6Data_valid (ggFrobT f)
  have hφX : ∀ γ ∈ (e6Datum GGL).roots,
      ((e6Datum GGL).rootGroup γ).map σ ≤ (e6Datum GGL).rootGroup γ := by
    intro γ hγ
    have h := map_rootGroup_minBC_le e6Data_valid (ggFrobT f) γ
    simpa [σ, CFSG.LieType.Steinberg.permVec] using h
  obtain ⟨l, hnd, hl, hs, hinj⟩ :=
    (CFSG.LieType.Steinberg.isSteinberg_of hct hext).exists_posList
  have hr : ∀ γ ∈ l, γ ∈ (e6Datum GGL).roots := fun γ hγ => ((hl γ).1 hγ).1.1
  have hle : CFSG.LieType.Steinberg.posUnipotent (e6Datum GGL) ≤
      ⨆ v ∈ l, (e6Datum GGL).rootGroup v := by
    refine iSup₂_le fun γ hγ => ?_
    by_cases hind : (CFSG.LieType.Steinberg.RootSystem.ofCartan (e6Datum GGL).isFiniteType
        (e6Datum GGL).divisible).IsIndiv γ
    · exact le_iSup₂_of_le γ ((hl γ).2 ⟨hγ, hind⟩) le_rfl
    · obtain ⟨δ, hδ, hδ', rfl⟩ :=
        (CFSG.LieType.Steinberg.RootSystem.ofCartan (e6Datum GGL).isFiniteType
          (e6Datum GGL).divisible).exists_eq_two_smul hγ.1 hind
      exact (hext.two_smul_le δ hδ hγ.1).trans (le_iSup₂_of_le δ ((hl δ).2 ⟨
        (CFSG.LieType.Steinberg.RootSystem.ofCartan (e6Datum GGL).isFiniteType
          (e6Datum GGL).divisible).mem_pos_of_two_smul_mem_pos hγ hδ,
        hδ'⟩) le_rfl)
  have hc : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ (e6Datum GGL).rootGroup a,
      ∀ y ∈ (e6Datum GGL).rootGroup b,
      ⁅x, y⁆ ∈ ⨆ c ∈ l, ⨆ (_ : min (ht a) (ht b) < ht c),
        (e6Datum GGL).rootGroup c := by
    intro a ha b hb hab x hx y hy
    have hxy := hext.commutator_mem a (hr a ha) b (hr b hb)
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan (e6Datum GGL).isFiniteType
        (e6Datum GGL).divisible).linIndepPair_of_mem_pos ((hl a).1 ha).1
        ((hl a).1 ha).2 ((hl b).1 hb).1 ((hl b).1 hb).2 hab) x hx y hy
    have hle' : (⨆ ε ∈ CFSG.LieType.Steinberg.openCone (e6Datum GGL).roots a b,
        (e6Datum GGL).rootGroup ε) ≤
        ⨆ c ∈ l, ⨆ (_ : min (ht a) (ht b) < ht c), (e6Datum GGL).rootGroup c := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨c, hc, hlt, hcε⟩ :=
        (CFSG.LieType.Steinberg.RootSystem.ofCartan (e6Datum GGL).isFiniteType
          (e6Datum GGL).divisible).exists_of_mem_openCone_pos
          ((hl a).1 ha).1 ((hl a).1 ha).2 ((hl b).1 hb).1 ((hl b).1 hb).2 hab hε
      have hcL : c ∈ l := (hl c).2 hc
      have hle : (e6Datum GGL).rootGroup ε ≤ (e6Datum GGL).rootGroup c := by
        rcases hcε with rfl | rfl
        · exact le_rfl
        · exact hext.two_smul_le c (hr c hcL) hε.1
      exact hle.trans (le_iSup₂_of_le c hcL (le_iSup_of_le hlt le_rfl))
    exact hle' hxy
  obtain ⟨fac, hfac, rfl⟩ := CFSG.LieType.Steinberg.exists_prod_eq_of_commutator_mem
    (e6Datum GGL).rootGroup (fun γ => ht γ) hnd hs hc u (hle hu)
  have hfixf : ∀ γ ∈ l, σ (fac γ) = fac γ := by
    refine hinj (fun γ => σ (fac γ)) fac (fun γ hγ => ?_) hfac ?_
    · exact hφX γ (hr γ hγ) (Subgroup.mem_map_of_mem σ (hfac γ hγ))
    · rw [show (fun γ => σ (fac γ)) = σ ∘ fac from rfl, ← List.map_map, ← map_list_prod]
      exact hfix
  refine Subgroup.list_prod_mem (minBC e6Data_valid (ggRatEmb f)).range (fun x hx => ?_)
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  exact fixed_rootGroup_mem_range hf (hr γ hγ) (hfac γ hγ) (hfixf γ hγ)

theorem fixed_nrep_mem_range {f : ℕ}
    (w : (CFSG.LieType.RootSystem.coxeterMatrix (e6Datum GGL).isFiniteType).Group) :
    CFSG.LieType.Steinberg.nrep (e6Datum_isCTGroupDatum (k := GGL)) w ∈
      (minBC e6Data_valid (ggRatEmb f)).range := by
  obtain ⟨ω, hω, rfl⟩ :=
    (CFSG.LieType.RootSystem.coxeterMatrix (e6Datum GGL).isFiniteType).toCoxeterSystem.exists_isReduced w
  have hword : ∀ ω : List (Fin (e6Datum GGL).rank),
      (List.map (minBC e6Data_valid (ggRatEmb f))
        (List.map (e6Data_valid.nm (GaloisField 2 f)) ω)).prod =
      (List.map (e6Data_valid.nm GGL) ω).prod := by
    intro ω
    induction ω with
    | nil => simp
    | cons i ω ih =>
        simp only [List.map_cons, List.prod_cons, ih,
          minBC_nm e6Data_valid (ggRatEmb f) i]
  refine ⟨CFSG.LieType.Steinberg.nrep
    (e6Datum_isCTGroupDatum (k := GaloisField 2 f)) ((CFSG.LieType.RootSystem.coxeterMatrix (e6Datum GGL).isFiniteType).toCoxeterSystem.wordProd ω), ?_⟩
  rw [CFSG.LieType.Steinberg.nrep_wordProd (hct := e6Datum_isCTGroupDatum (k := GGL)) hω]
  rw [CFSG.LieType.Steinberg.nrep_wordProd (hct := e6Datum_isCTGroupDatum (k := GaloisField 2 f)) hω]
  rw [map_list_prod]
  exact hword ω

theorem fixed_mem_minBC_range {f : ℕ} (hf : 1 ≤ f)
    {g : e6Data_valid.minGroup GGL}
    (hfix : minBC e6Data_valid (ggFrobT f) g = g) :
    g ∈ (minBC e6Data_valid (ggRatEmb f)).range := by
  obtain ⟨w, b, u, hb, hu, hbσ, huσ, rfl⟩ := exists_fixed_normal_form hfix
  have hσ := e6OrdinaryIsTwist f
  obtain ⟨t, ht, htσ, v, hv, hvσ, rfl⟩ :=
    hσ.fixed_borel (hct := e6Datum_isCTGroupDatum (k := GGL))
      (hext := e6Datum_steinbergExtras (k := GGL)) hb hbσ
  have ht_range := fixed_torus_mem_range hf ht htσ
  have hv_range := fixed_posUnipotent_mem_range hf hv hvσ
  have hn_range := fixed_nrep_mem_range (f := f) w
  have hu_range := fixed_posUnipotent_mem_range hf
    (CFSG.LieType.Steinberg.inversionUnipotent_le_posUnipotent w hu) huσ
  exact mul_mem (mul_mem (mul_mem ht_range hv_range) hn_range) hu_range

end CFSG.StandardType.GGFinModel
