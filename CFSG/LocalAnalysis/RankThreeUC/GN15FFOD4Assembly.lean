module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLink
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Section
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Split
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Fam
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4NatFam
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4OutTheta
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusTypes

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin CFSG.Open
open CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped Pointwise

theorem ffOffenderInvertsOddD4_of_natural_classification
    (hclass : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ L E : Subgroup (MulAut V), CFSG.QuasithinUnique.Setup.X1.IsIrrOn L → Group.IsPerfect L →
        (∃ f : ℕ, StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 f) →
        E ≤ Subgroup.normalizer (L : Set (MulAut V)) → E ≠ ⊥ → CFSG.Quasithin.IsElemAbelian2 E →
        CFSG.Quasithin.IsQuadratic E →
        Nat.card V ≤ Nat.card E * Nat.card (CFSG.Quasithin.fixV E) →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
          (χ : L ≃* orthElementaryGroup (quadPlus 4 K)) (φ : Additive V ≃+ (Fin 4 ⊕ Fin 4 → K)),
          ∀ (l : L) (v : V), φ (Additive.ofMul ((l : MulAut V) v)) =
            (χ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (Additive.ofMul v))) :
    FFOffenderInvertsOddD4 := by
  refine ffOffenderInvertsOddD4_of_swap ?_
  intro G _ _ W _ _ _ ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK y hy hinv r e hr hr2 hord hyr
    hnn hF hyX
  obtain ⟨⟨f, hmodel⟩, rfl⟩ := hF
  have hLq : CFSG.IsQuasisimple ↥L := ((CFSG.isComponent_iff_open L).mpr hL).1
  have hLbot : L ≠ ⊥ := by
    rintro rfl
    have hs : IsSimpleGroup
        (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := hL.2.2.2
    have := hs.toNontrivial
    have : Subsingleton ↥(⊥ : Subgroup G) := inferInstance
    have : Subsingleton
        (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := inferInstance
    exact not_subsingleton _ ‹_›
  have hcen : cenOn ρ L ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    apply hρ
    rw [map_one]
    ext v
    exact hl.2 v Submodule.mem_top
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    rw [hcen]
    exact fun h => hLbot (le_bot_iff.mp h)
  have hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := by
    intro a _ hfix
    apply hρ
    rw [map_one]
    ext v
    exact hfix v
  have hb : IsBestOffenderOn ρ A ⊤ :=
    (isBestOffender_iff_on ρ A hfaith).mp ⟨hAel, hAb⟩
  obtain ⟨I, W', hW'c, hW'f, Lb, Eb, p, ψ, hIinv, hIL, hpsurj, hker, hpe, hψ, hW'2, hirr, hLbq,
    hEb0, hEbel, hEbq, hEbN, hoff⟩ :=
    FFO.D4.exists_irrSection_retained (X := G) ρ L A hLq hAel hAN hLA hKnt hb
  let : CommGroup W' := hW'c
  let : Finite W' := hW'f
  have : Finite ↥L := Subtype.finite
  have hLbne : Lb ≠ ⊥ := by
    rintro hbot
    have hsub : Subsingleton (↥Lb ⧸ Subgroup.center ↥Lb) := by
      rw [hbot]
      infer_instance
    have := hLbq.2.1.toNontrivial
    exact not_subsingleton _ ‹Subsingleton _›
  have hRange : (Lb.subtype.comp ψ).range = Lb := by
    apply le_antisymm
    · rintro _ ⟨l, rfl⟩
      exact (ψ l).2
    · intro x hx
      obtain ⟨l, hl⟩ := hψ ⟨x, hx⟩
      exact ⟨l, congrArg Subtype.val hl⟩
  obtain ⟨-, ⟨eQ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hLq
      (Lb.subtype.comp ψ) (by rw [hRange]; exact hLbne)
  have hmodel' : ∃ f : ℕ,
      StatedClassicalModel ((Lb.subtype.comp ψ).range ⧸
        Subgroup.center ↥((Lb.subtype.comp ψ).range)) .POmegaPlus 4 2 f :=
    ⟨f, CFSG.SectionRank.statedClassicalModel_of_mulEquiv eQ hmodel⟩
  obtain ⟨K, hKf, hKfin, hKchar, χ, φ, hχφ⟩ :=
    hclass W' hW'2 (Lb.subtype.comp ψ).range Eb
      (by rw [hRange]; exact hirr)
      (by rw [hRange]; exact hLbq.1)
      hmodel'
      (by rw [hRange]; exact hEbN)
      hEb0 hEbel hEbq hoff
  let : Field K := hKf
  let : Finite K := hKfin
  let : CharP K 2 := hKchar
  let Lr : Subgroup (MulAut W') := (Lb.subtype.comp ψ).range
  let ψr : ↥L →* Lr := (Lb.subtype.comp ψ).rangeRestrict
  let ψ' : ↥L →* orthElementaryGroup (quadPlus 4 K) := χ.toMonoidHom.comp ψr
  have hψr : Function.Surjective ψr := MonoidHom.rangeRestrict_surjective _
  have hψ' : Function.Surjective ψ' := χ.surjective.comp hψr
  have htop : ψ.ker ≠ ⊤ := by
    intro htop
    have h1 : ψ = 1 := MonoidHom.ker_eq_top_iff.mp htop
    apply hLbne
    rw [← hRange]
    rw [h1]
    simp
  have hkerψ_center : ψ.ker ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (MonoidHom.normal_ker ψ) with h | h
    · exact absurd h htop
    · exact h
  have hψc : ∀ l : ↥L, ψ' l = 1 → ∀ l' : ↥L, l * l' = l' * l := by
    intro l hl l'
    have h1 : ψr l = 1 := χ.injective (by simpa [ψ'] using hl)
    have h2 : ψ l = 1 := by
      apply Subtype.ext
      show ((ψr l : Lr) : MulAut W') = ((1 : ↥Lb) : MulAut W')
      rw [h1]
      rfl
    exact (Subgroup.mem_center_iff.mp (hkerψ_center (MonoidHom.mem_ker.mpr h2)) l').symm
  have hZorth : Subgroup.center (orthElementaryGroup (quadPlus 4 K)) = ⊥ :=
    (CFSG.AGLEmbedding.LeviBlock.isQuasisimple_plusElementary (K := K) (m := 4)
      (by norm_num)).2
  have hkerZ : ψ'.ker = Subgroup.center ↥L := by
    apply le_antisymm
    · intro x hx
      have hx1 : ψ' x = 1 := MonoidHom.mem_ker.mp hx
      have h1 : ψr x = 1 := χ.injective (by simpa [ψ'] using hx1)
      have h2 : ψ x = 1 := by
        apply Subtype.ext
        show ((ψr x : Lr) : MulAut W') = ((1 : ↥Lb) : MulAut W')
        rw [h1]
        rfl
      exact hkerψ_center (MonoidHom.mem_ker.mpr h2)
    · intro x hx
      have hcent : χ (ψr x) ∈ Subgroup.center (orthElementaryGroup (quadPlus 4 K)) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨w, rfl⟩ := χ.surjective z
        obtain ⟨lz, rfl⟩ := hψr w
        have hx' : ∀ l' : ↥L, x * l' = l' * x :=
          fun l' => (Subgroup.mem_center_iff.mp hx l').symm
        calc χ (ψr lz) * χ (ψr x) = χ (ψr lz * ψr x) := by simp only [map_mul]
          _ = χ (ψr (lz * x)) := by simp only [map_mul]
          _ = χ (ψr (x * lz)) := by rw [hx' lz]
          _ = χ (ψr x * ψr lz) := by simp only [map_mul]
          _ = χ (ψr x) * χ (ψr lz) := by simp only [map_mul]
      rw [hZorth, Subgroup.mem_bot] at hcent
      have h1 : ψr x = 1 := χ.injective (by simpa using hcent)
      rw [MonoidHom.mem_ker]
      show χ (ψr x) = 1
      rw [h1, map_one]
  let p' : I →+ (Fin 4 ⊕ Fin 4 → K) := φ.toAddMonoidHom.comp p
  have hp' : Function.Surjective p' := φ.surjective.comp hpsurj
  have hpe' : ∀ (l : ↥L) (v w : I), (w : W) = ρ l v →
      p' w = (ψ' l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (p' v) := by
    intro l v w hw
    have h1 := hpe l v w hw
    have h2 : φ (p w) = φ (Additive.ofMul ((ψ l : MulAut W') (Additive.toMul (p v)))) :=
      congrArg φ h1
    show φ (p w) = (χ (ψr l) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (p v))
    rw [h2]
    exact hχφ (ψr l) (Additive.toMul (p v))
  have hker' : ∀ v : I, p' v = 0 → ∀ l ∈ L, ρ l v = v := by
    intro v hv l hl
    have hv0 : φ (p v) = 0 := by simpa [p'] using hv
    have hp0 : p v = 0 := φ.injective (by rw [hv0, map_zero])
    exact hker v hp0 l hl
  have hpinj' : Function.Injective p' :=
    FFO.D4.injective_of_natural ρ L I hIinv hIL ψ' hψ' hψc p' hp' hpe' hker'
  have hpinj : Function.Injective p := by
    intro u v huv
    apply hpinj'
    show φ (p u) = φ (p v)
    rw [huv]
  have hp_bij : Function.Bijective p := ⟨hpinj, hpsurj⟩
  have hIne : I ≠ ⊥ := by
    intro hbot
    have : Nontrivial W' := hirr.1
    have : Subsingleton I := by rw [hbot]; infer_instance
    obtain ⟨w, hw⟩ := exists_ne (1 : W')
    obtain ⟨v, hv⟩ := hpsurj (Additive.ofMul w)
    have hv0 : v = 0 := Subsingleton.elim v 0
    rw [hv0, map_zero] at hv
    exact hw (Additive.ofMul.injective (by simpa using hv.symm))
  have hsimple : FFO.D4.IsSimpleL ρ L I := by
    refine ⟨hIne, hIinv, ?_⟩
    intro S' hS'le hS'inv
    let T : Subgroup W' :=
      { carrier := {w | ∃ (s : W) (hs : s ∈ S'), Additive.toMul (p ⟨s, hS'le hs⟩) = w}
        one_mem' := ⟨0, S'.zero_mem, by
          rw [show (⟨0, hS'le S'.zero_mem⟩ : I) = 0 from rfl, map_zero]
          rfl⟩
        mul_mem' := by
          rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
          refine ⟨s + t, S'.add_mem hs ht, ?_⟩
          rw [show (⟨s + t, hS'le (S'.add_mem hs ht)⟩ : I) = ⟨s, hS'le hs⟩ + ⟨t, hS'le ht⟩ from
            Subtype.ext rfl, map_add, toMul_add]
        inv_mem' := by
          rintro _ ⟨s, hs, rfl⟩
          refine ⟨-s, S'.neg_mem hs, ?_⟩
          rw [show (⟨-s, hS'le (S'.neg_mem hs)⟩ : I) = -⟨s, hS'le hs⟩ from Subtype.ext rfl, map_neg,
            toMul_neg] }
    have hT : ∀ g ∈ Lb, ∀ w ∈ T, (g : MulAut W') w ∈ T := by
      rintro g hg w ⟨s, hs, rfl⟩
      obtain ⟨l, hl⟩ := hψ ⟨g, hg⟩
      have hgl : (g : MulAut W') = ((ψ l : ↥Lb) : MulAut W') := (congrArg Subtype.val hl).symm
      have hmem : ρ (l : G) s ∈ S' := hS'inv l l.2 s hs
      refine ⟨ρ (l : G) s, hmem, ?_⟩
      have hwl := hpe l ⟨s, hS'le hs⟩ ⟨ρ (l : G) s, hS'le hmem⟩ rfl
      rw [hgl]
      show Additive.toMul (p ⟨ρ (l : G) s, hS'le hmem⟩) =
        ((ψ l : ↥Lb) : MulAut W') (Additive.toMul (p ⟨s, hS'le hs⟩))
      rw [hwl, toMul_ofMul]
    rcases hirr.2 T hT with hTbot | hTtop
    · left
      rw [eq_bot_iff]
      intro s hs
      have hmem : Additive.toMul (p ⟨s, hS'le hs⟩) ∈ T := ⟨s, hs, rfl⟩
      rw [hTbot, Subgroup.mem_bot] at hmem
      have hp0 : p ⟨s, hS'le hs⟩ = 0 :=
        Additive.toMul.injective (by simpa using hmem)
      rw [Submodule.mem_bot]
      have hzero : (⟨s, hS'le hs⟩ : I) = 0 := hpinj (by rw [hp0]; exact (map_zero p).symm)
      simpa using congrArg Subtype.val hzero
    · right
      apply le_antisymm hS'le
      intro v hv
      have hmem : Additive.toMul (p ⟨v, hv⟩) ∈ T := by rw [hTtop]; exact Subgroup.mem_top _
      obtain ⟨s, hs, heq⟩ := hmem
      have hps : p ⟨s, hS'le hs⟩ = p ⟨v, hv⟩ := Additive.toMul.injective heq
      have hsv : (⟨s, hS'le hs⟩ : I) = ⟨v, hv⟩ := hpinj hps
      have hsv' : s = v := Subtype.ext_iff.mp hsv
      rwa [hsv'] at hs
  let θ₀ : (↥L ⧸ Subgroup.center ↥L) ≃* orthElementaryGroup (quadPlus 4 K) :=
    QuotientGroup.liftEquiv (Subgroup.center ↥L) hψ' hkerZ.symm
  have hθ₀_mk : ∀ x : ↥L, θ₀ (QuotientGroup.mk' (Subgroup.center ↥L) x) = ψ' x :=
    fun x => QuotientGroup.liftEquiv_mk (Subgroup.center ↥L) hψ' hkerZ.symm x
  obtain ⟨ν, hν⟩ := FFO.D4.exists_familyTransport_sylowFamilyOn_natPerm (K := K)
  let θ : (↥L ⧸ Subgroup.center ↥L) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    θ₀.trans ν
  have hS₁ : ∀ h : ↥L, ∀ v ∈ (I : Set W), (FFO.D4.permRep ρ L) h v ∈ (I : Set W) := by
    intro h v hv
    exact hIinv h h.2 v hv
  let e : (↥(I : Set W)) → (↥(Set.univ : Set (Fin 4 ⊕ Fin 4 → K))) :=
    fun v => ⟨φ (p ⟨v.1, v.2⟩), Set.mem_univ _⟩
  have he : Function.Bijective e := by
    constructor
    · intro u v huv
      have h1 : φ (p ⟨u.1, u.2⟩) = φ (p ⟨v.1, v.2⟩) := congrArg Subtype.val huv
      have h2 : p ⟨u.1, u.2⟩ = p ⟨v.1, v.2⟩ := φ.injective h1
      have h3 : (⟨u.1, u.2⟩ : I) = ⟨v.1, v.2⟩ := hpinj h2
      exact Subtype.ext (Subtype.ext_iff.mp h3)
    · intro z
      obtain ⟨v, hv⟩ := hpsurj (φ.symm (z : Fin 4 ⊕ Fin 4 → K))
      refine ⟨⟨v.1, v.2⟩, ?_⟩
      apply Subtype.ext
      show φ (p v) = (z : Fin 4 ⊕ Fin 4 → K)
      rw [hv, AddEquiv.apply_symm_apply]
  have heq : ∀ (h : ↥L) (v w : ↥(I : Set W)), (w : W) = (FFO.D4.permRep ρ L) h v →
      (e w : Fin 4 ⊕ Fin 4 → K) = FFO.D4.natPerm (ψ' h) (e v) := by
    intro h v w hw
    have h1 := hpe h ⟨v.1, v.2⟩ ⟨w.1, w.2⟩ (by simpa [FFO.D4.permRep] using hw)
    show φ (p ⟨w.1, w.2⟩) =
      (χ (ψr h) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (p ⟨v.1, v.2⟩))
    rw [h1]
    show φ (Additive.ofMul ((ψ h : MulAut W') (Additive.toMul (p ⟨v.1, v.2⟩)))) =
      (χ (ψr h) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
        (φ (Additive.ofMul (Additive.toMul (p ⟨v.1, v.2⟩))))
    exact hχφ (ψr h) (Additive.toMul (p ⟨v.1, v.2⟩))
  have hmod : FFO.D4.sylowFamilyOn (FFO.D4.permRep ρ L) (I : Set W) =
      Subgroup.comap ψ' '' FFO.D4.sylowFamilyOn FFO.D4.natPerm
        (Set.univ : Set (Fin 4 ⊕ Fin 4 → K)) :=
    FFO.D4.sylowFamilyOn_eq_comap (FFO.D4.permRep ρ L) FFO.D4.natPerm (I : Set W) Set.univ hS₁ ψ'
      hψ' e he heq
  have hstep : ∀ U : Subgroup (orthElementaryGroup (quadPlus 4 K)),
      (Subgroup.comap ψ' U).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
        Subgroup.comap θ₀.toMonoidHom U := by
    intro U
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show θ₀ (QuotientGroup.mk' (Subgroup.center ↥L) x) ∈ U
      rw [hθ₀_mk x]
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) y
      refine ⟨x, ?_, rfl⟩
      show ψ' x ∈ U
      rwa [← hθ₀_mk x]
  have hmap_comap : ∀ U : Subgroup (orthElementaryGroup (quadPlus 4 K)),
      Subgroup.comap θ₀.toMonoidHom U = U.map θ₀.symm.toMonoidHom := by
    intro U
    ext x
    constructor
    · intro hx
      exact ⟨θ₀ x, hx, θ₀.symm_apply_apply x⟩
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
  have hcomp : θ.symm.toMonoidHom.comp ν.toMonoidHom = θ₀.symm.toMonoidHom := by
    ext x
    simp [θ]
  have hfam : FFO.D4.famBar ρ L I =
      (familyTransport θ).symm (projectivePointFamily (coordinateQuadPlus 4 K)) := by
    have h1 : FFO.D4.famBar ρ L I =
        (fun U => Subgroup.comap θ₀.toMonoidHom U) ''
          FFO.D4.sylowFamilyOn FFO.D4.natPerm (Set.univ : Set (Fin 4 ⊕ Fin 4 → K)) := by
      rw [FFO.D4.famBar, FFO.D4.modFamily, hmod, Set.image_image]
      exact Set.image_congr (fun U _ => hstep U)
    have h2 : (fun U => Subgroup.comap θ₀.toMonoidHom U) ''
          FFO.D4.sylowFamilyOn FFO.D4.natPerm (Set.univ : Set (Fin 4 ⊕ Fin 4 → K)) =
        (familyTransport θ).symm
          (familyTransport ν (FFO.D4.sylowFamilyOn FFO.D4.natPerm Set.univ)) := by
      rw [familyTransport_apply, familyTransport_symm_apply, Set.image_image]
      refine Set.image_congr (fun U _ => ?_)
      rw [Subgroup.map_map, hcomp]
      exact hmap_comap U
    rw [h1, h2, hν]
  have : Group.IsPerfect ↥L := hLq.1
  let α : MulAut (↥L ⧸ Subgroup.center ↥L) := actionOnQuot L ⟨y, hy⟩
  let β : MulAut (↥L ⧸ Subgroup.center ↥L) := actionOnQuot L ⟨a, hAN ha⟩
  have hgy : y ^ 3 ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hy 3
  have hα : α ^ 3 ∈ Inn (↥L ⧸ Subgroup.center ↥L) := by
    have hpow : α ^ 3 = actionOnQuot L ⟨y ^ 3, hgy⟩ := by
      rw [show α = actionOnQuot L ⟨y, hy⟩ from rfl, ← map_pow]
      congr 1
    rw [hpow]
    exact (actionOnQuot_mem_inner_iff L hgy).mpr hyr
  have hαN : α ∉ Inn (↥L ⧸ Subgroup.center ↥L) := by
    intro h
    exact hyX ((actionOnQuot_mem_inner_iff L hy).mp h)
  have hβ : β * α * β⁻¹ = α⁻¹ := by
    have h1 : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) * ⟨y, hy⟩ * ⟨a, hAN ha⟩⁻¹ =
        ⟨y, hy⟩⁻¹ := by
      apply Subtype.ext
      simpa using hinv
    have h2 : β * α * β⁻¹ =
        actionOnQuot L (⟨a, hAN ha⟩ * ⟨y, hy⟩ * ⟨a, hAN ha⟩⁻¹) := by
      rw [show β = actionOnQuot L ⟨a, hAN ha⟩ from rfl,
        show α = actionOnQuot L ⟨y, hy⟩ from rfl, ← map_inv, ← map_mul, ← map_mul]
    rw [h2, h1]
    show actionOnQuot L ⟨y, hy⟩⁻¹ = α⁻¹
    rw [show α = actionOnQuot L ⟨y, hy⟩ from rfl, map_inv]
  obtain ⟨P, Q, R, hPQ, hQR, hPR, hPerm, hInn, hβP, hβQ, hβR, hαcyc, hcomm, hfamMem⟩ :=
    FFO.D4.outer_action_of_inverted_of_mulEquiv θ hα hαN hβ
  have hFmem : FFO.D4.famBar ρ L I ∈
      ({P, Q, R} : Set (Set (Subgroup (↥L ⧸ Subgroup.center ↥L)))) := by
    rw [hfam]
    exact hfamMem
  have hex : ∃ k : ℕ, (k = 0 ∨ k = 1) ∧
      α ^ k • FFO.D4.famBar ρ L I ∈
        ({Q, R} : Set (Set (Subgroup (↥L ⧸ Subgroup.center ↥L)))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hFmem
    rcases hFmem with hP | hQ | hR
    · refine ⟨1, Or.inr rfl, ?_⟩
      rw [pow_one, hP]
      rcases hαcyc with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; simp
      · rw [h1]; simp
    · refine ⟨0, Or.inl rfl, ?_⟩
      simp only [pow_zero, one_smul, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl hQ
    · refine ⟨0, Or.inl rfl, ?_⟩
      simp only [pow_zero, one_smul, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr hR
  obtain ⟨k, hk01, hΨmem⟩ := hex
  let Ψ : Set (Subgroup (↥L ⧸ Subgroup.center ↥L)) := α ^ k • FFO.D4.famBar ρ L I
  have hΨdef : Ψ = α ^ k • FFO.D4.famBar ρ L I := rfl
  have hβΨ : β • Ψ ≠ Ψ := by
    rw [hΨdef]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hΨmem
    rcases hΨmem with h | h
    · rw [h, hβQ]
      exact fun hh => hQR hh.symm
    · rw [h, hβR]
      exact fun hh => hQR hh
  have hyg : y ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hy k
  let I' : Submodule (ZMod 2) W := I.map (ρ (y ^ k))
  have hsimple' : FFO.D4.IsSimpleL ρ L I' := FFO.D4.isSimpleL_map ρ L hyg hsimple
  have hfamI' : FFO.D4.famBar ρ L I' = Ψ := by
    rw [show I' = I.map (ρ (y ^ k)) from rfl, FFO.D4.famBar_map ρ L hyg I]
    have hpow : actionOnQuot L ⟨y ^ k, hyg⟩ = α ^ k := by
      rw [show α = actionOnQuot L ⟨y, hy⟩ from rfl, ← map_pow]
      congr 1
    rw [hpow]
  let M₁ : Submodule (ZMod 2) W := FFO.D4.famSum ρ L Ψ
  have hle : I' ≤ M₁ := by
    have h1 : I' ≤ FFO.D4.famSum ρ L (FFO.D4.famBar ρ L I') := FFO.D4.le_famSum ρ L hsimple'
    rwa [hfamI'] at h1
  have hcard_le : Nat.card I ≤ Nat.card M₁ := by
    have hinj : Function.Injective
        (fun v : I => (⟨ρ (y ^ k) (v : W),
          hle (Submodule.mem_map.mpr ⟨v, v.2, rfl⟩)⟩ : M₁)) := by
      intro u v huv
      apply Subtype.ext
      have h1 : ρ (y ^ k) (u : W) = ρ (y ^ k) (v : W) := congrArg Subtype.val huv
      have h2 := congrArg (fun w => ρ ((y ^ k)⁻¹) w) h1
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using h2
    exact Nat.card_le_card_of_injective _ hinj
  have hcardI : Nat.card I = Nat.card K ^ 8 := by
    have e1 : I ≃ Additive W' := Equiv.ofBijective p hp_bij
    have e2 : Additive W' ≃ (Fin 4 ⊕ Fin 4 → K) := φ.toEquiv
    rw [Nat.card_congr e1, Nat.card_congr e2]
    simp [Nat.card_fun]
  have hK2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hcardM : 2 < Nat.card M₁ := by
    have h1 : 2 ^ 8 ≤ Nat.card M₁ := by
      calc 2 ^ 8 ≤ Nat.card K ^ 8 := Nat.pow_le_pow_left hK2 8
        _ = Nat.card I := hcardI.symm
        _ ≤ Nat.card M₁ := hcard_le
    omega
  have hmapa : M₁.map (ρ a) = FFO.D4.famSum ρ L (β • Ψ) := by
    rw [show M₁ = FFO.D4.famSum ρ L Ψ from rfl]
    exact FFO.D4.map_famSum ρ L (hAN ha) Ψ
  have hdisj : Disjoint M₁ (M₁.map (ρ a)) := by
    rw [hmapa]
    exact FFO.D4.famSum_disjoint ρ L (Ψ := Ψ) (Ψ' := β • Ψ) hβΨ.symm
  have hfinal : ∀ b ∈ A, M₁.map (ρ b) = M₁ ∨ M₁.map (ρ b) = M₁.map (ρ a) := by
    intro b hb
    let γ : MulAut (↥L ⧸ Subgroup.center ↥L) := actionOnQuot L ⟨b, hAN hb⟩
    have hγβ : γ * β = β * γ := by
      let : IsMulCommutative ↥A := hAel.toIsMulCommutative
      let : CommGroup ↥A := IsMulCommutative.instCommGroup
      have hab : a * b = b * a :=
        congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) (⟨b, hb⟩ : ↥A))
      have h1 : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) * ⟨b, hAN hb⟩ =
          ⟨b, hAN hb⟩ * ⟨a, hAN ha⟩ := by
        apply Subtype.ext
        exact hab
      calc γ * β = actionOnQuot L (⟨b, hAN hb⟩ * ⟨a, hAN ha⟩) := (map_mul _ _ _).symm
        _ = actionOnQuot L (⟨a, hAN ha⟩ * ⟨b, hAN hb⟩) := by rw [h1]
        _ = β * γ := map_mul _ _ _
    have hγmap : M₁.map (ρ b) = FFO.D4.famSum ρ L (γ • Ψ) := by
      rw [show M₁ = FFO.D4.famSum ρ L Ψ from rfl]
      exact FFO.D4.map_famSum ρ L (hAN hb) Ψ
    have hkey : γ • Ψ = Ψ ∨ γ • Ψ = β • Ψ := by
      rw [hΨdef]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hΨmem
      rcases hcomm γ hγβ with ⟨-, hQ, hR⟩ | ⟨-, hQ, hR⟩
      · rcases hΨmem with h | h
        · left; rw [h, hQ]
        · left; rw [h, hR]
      · rcases hΨmem with h | h
        · right; rw [h, hQ, hβQ]
        · right; rw [h, hR, hβR]
    rcases hkey with hkey | hkey
    · left
      rw [hγmap, hkey]
    · right
      rw [hγmap, hmapa, hkey]
  exact ⟨M₁, hdisj, hcardM, hfinal⟩


end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
