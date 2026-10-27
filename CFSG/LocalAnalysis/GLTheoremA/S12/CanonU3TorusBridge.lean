module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusCore
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Bridge
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

section ConjAutMul

variable {Γ : Type} [Group Γ]

theorem conjAut_mul (L : Subgroup Γ) {g h : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ)) (hh : h ∈ Subgroup.normalizer (L : Set Γ)) :
    conjAut L g hg * conjAut L h hh = conjAut L (h * g) (Subgroup.mul_mem _ hh hg) := by
  ext l
  rw [MulAut.mul_apply ↥L]
  rw [coe_conjAut, coe_conjAut, coe_conjAut]
  group

theorem map_fixSubgroup_conjAut (L : Subgroup Γ) {y : Γ}
    (hy : y ∈ Subgroup.normalizer (L : Set Γ)) :
    (fixSubgroup (conjAut L y hy)).map L.subtype =
      L ⊓ Subgroup.centralizer ({y} : Set Γ) := by
  rw [CanonInn.fixSubgroup_conjAut_eq L hy]
  exact Subgroup.map_subgroupOf_eq_of_le inf_le_left

theorem map_conjAut_subgroupOf_eq_self {L K : Subgroup Γ} {g : Γ}
    (hgL : g ∈ Subgroup.normalizer (L : Set Γ))
    (hgK : g ∈ Subgroup.normalizer (K : Set Γ)) (hKL : K ≤ L) :
    (K.subgroupOf L).map (conjAut L g hgL).toMonoidHom = K.subgroupOf L := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change ((conjAut L g hgL k : ↥L) : Γ) ∈ K
    rw [coe_conjAut]
    exact (Subgroup.mem_normalizer_iff''.1 hgK (k : Γ)).1 hk
  · intro hx
    refine ⟨(conjAut L g hgL).symm x, ?_, by simp⟩
    change ((((conjAut L g hgL).symm x : ↥L) : Γ)) ∈ K
    have hval : (((conjAut L g hgL).symm x : ↥L) : Γ) = g * (x : Γ) * g⁻¹ := by
      have h1 : (conjAut L g hgL) ((conjAut L g hgL).symm x) = x := by simp
      have h2 := congrArg Subtype.val h1
      rw [coe_conjAut] at h2
      calc (((conjAut L g hgL).symm x : ↥L) : Γ)
          = g * (g⁻¹ * (((conjAut L g hgL).symm x : ↥L) : Γ) * g) * g⁻¹ := by group
        _ = g * (x : Γ) * g⁻¹ := by rw [h2]
    rw [hval]
    exact (Subgroup.mem_normalizer_iff.1 hgK (x : Γ)).1 (Subgroup.mem_subgroupOf.1 hx)

theorem map_centerQuotAut_conjAut_subgroupOf {L K : Subgroup Γ} {g : Γ}
    (hgL : g ∈ Subgroup.normalizer (L : Set Γ))
    (hgK : g ∈ Subgroup.normalizer (K : Set Γ)) (hKL : K ≤ L) :
    ((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map
        (centerQuotAut ↥L (conjAut L g hgL)).toMonoidHom =
      (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  let π : ↥L →* (↥L ⧸ Subgroup.center ↥L) := QuotientGroup.mk' (Subgroup.center ↥L)
  let α := conjAut L g hgL
  let β := centerQuotAut ↥L α
  let KL := K.subgroupOf L
  have hpoint : β.toMonoidHom.comp π = π.comp α.toMonoidHom := by
    ext k
    exact centerQuotAut_mk ↥L α k
  calc (KL.map π).map β.toMonoidHom
      = KL.map (β.toMonoidHom.comp π) := Subgroup.map_map KL β.toMonoidHom π
    _ = KL.map (π.comp α.toMonoidHom) := by rw [hpoint]
    _ = (KL.map α.toMonoidHom).map π := (Subgroup.map_map KL π α.toMonoidHom).symm
    _ = KL.map π := by
        rw [map_conjAut_subgroupOf_eq_self hgL hgK hKL]

theorem conjAut_pow' (L : Subgroup Γ) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ)) (k : ℕ) :
    (conjAut L g hg) ^ k = conjAut L (g ^ k) (Subgroup.pow_mem _ hg k) := by
  unfold conjAut
  rw [← map_pow]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_pow, inv_pow]

theorem commute_centerQuotAut_conjAut (L : Subgroup Γ) {g h : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ))
    (hh : h ∈ Subgroup.normalizer (L : Set Γ)) (hcomm : Commute g h) :
    Commute (centerQuotAut ↥L (conjAut L g hg))
      (centerQuotAut ↥L (conjAut L h hh)) := by
  show centerQuotAut ↥L (conjAut L g hg) * centerQuotAut ↥L (conjAut L h hh) =
    centerQuotAut ↥L (conjAut L h hh) * centerQuotAut ↥L (conjAut L g hg)
  calc centerQuotAut ↥L (conjAut L g hg) * centerQuotAut ↥L (conjAut L h hh)
      = centerQuotAut ↥L (conjAut L g hg * conjAut L h hh) :=
        (map_mul (centerQuotAut ↥L) _ _).symm
    _ = centerQuotAut ↥L (conjAut L (h * g) (Subgroup.mul_mem _ hh hg)) := by
        rw [conjAut_mul L hg hh]
    _ = centerQuotAut ↥L (conjAut L (g * h) (Subgroup.mul_mem _ hg hh)) := by
        congr 1
        ext l
        rw [coe_conjAut, coe_conjAut, hcomm.eq.symm]
    _ = centerQuotAut ↥L (conjAut L h hh * conjAut L g hg) := by
        rw [conjAut_mul L hh hg]
    _ = centerQuotAut ↥L (conjAut L h hh) * centerQuotAut ↥L (conjAut L g hg) :=
        map_mul (centerQuotAut ↥L) _ _

theorem centerQuotAut_conjAut_mul_pow (L : Subgroup Γ) {g h : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ))
    (hh : h ∈ Subgroup.normalizer (L : Set Γ)) (hcomm : Commute g h) (k : ℕ) :
    centerQuotAut ↥L (conjAut L (g * h ^ k) (Subgroup.mul_mem _ hg (Subgroup.pow_mem _ hh k))) =
      centerQuotAut ↥L (conjAut L g hg) * (centerQuotAut ↥L (conjAut L h hh)) ^ k := by
  rw [← map_pow (centerQuotAut ↥L), conjAut_pow']
  rw [← map_mul]
  congr 1
  rw [conjAut_mul L hg (Subgroup.pow_mem _ hh k)]
  ext l
  rw [coe_conjAut, coe_conjAut]
  rw [show h ^ k * g = g * h ^ k from (hcomm.pow_right k).eq.symm]

end ConjAutMul

section FixedPreimage

variable {X : Type} [Group X]

theorem fixedPreimage_centerQuotAut_eq_comap (α : MulAut X)
    (hinv : (Subgroup.center X).map α.toMonoidHom = Subgroup.center X) :
    fixedPreimage (Subgroup.center X) α hinv =
      (fixSubgroup (centerQuotAut X α)).comap (QuotientGroup.mk' (Subgroup.center X)) := by
  let Z : Subgroup X := Subgroup.center X
  have hβα : centerQuotAut X α = onQuotient Z α hinv := by
    ext y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    change (QuotientGroup.mk' Z) (α l) = (onQuotient Z α hinv) ((QuotientGroup.mk' Z) l)
    rw [onQuotient_mk]
  ext l
  rw [Subgroup.mem_comap, mem_fixSubgroup, hβα]
  exact Iff.rfl

end FixedPreimage

section SolvableDescent

variable {Γ : Type} [Group Γ]

theorem isSolvable_of_le_fixedPreimage {X : Type} [Group X] (Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ Subgroup.center X) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z)
    {P : Subgroup X} (hP : P ≤ fixedPreimage Z ψ hinv)
    (hsol : IsSolvable ↥(P ⊓ fixSubgroup ψ)) : IsSolvable ↥P := by
  let d := displacement Z ψ hinv hZ
  let incl : P →* fixedPreimage Z ψ hinv := Subgroup.inclusion hP
  let f : P →* Z := d.comp incl
  have hker : f.ker = (P ⊓ fixSubgroup ψ).subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      rw [mem_fixSubgroup]
      exact (displacement_eq_one_iff Z ψ hinv hZ (incl x)).1 hx
    · rintro ⟨-, hx⟩
      exact (displacement_eq_one_iff Z ψ hinv hZ (incl x)).2 hx
  haveI : Group.IsSolvable ↥f.ker := by
    rw [hker]
    let e := Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ fixSubgroup ψ ≤ P)
    exact @Group.isSolvable_of_surjective (↥(P ⊓ fixSubgroup ψ))
      (↥((P ⊓ fixSubgroup ψ).subgroupOf P)) _ _ e.symm.toMonoidHom e.symm.surjective hsol
  haveI : IsMulCommutative Z :=
    isMulCommutative_iff.mpr fun a b => by
      have ha : (a : X) ∈ Subgroup.center X := hZ a.2
      exact Subtype.ext (Subgroup.mem_center_iff.1 ha (b : X)).symm
  haveI : Group.IsSolvable Z := Group.instIsSolvableOfIsMulCommutative
  haveI : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_isSolvable_injective (f := f.range.subtype) f.range.subtype_injective
  have hker_le : f.rangeRestrict.ker ≤ (f.ker.subtype).range := by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]
  exact solvable_of_ker_le_range f.ker.subtype f.rangeRestrict hker_le

end SolvableDescent

section TorusBridge

variable {Γ : Type} [Group Γ]
variable {L K : Subgroup Γ} {g y : Γ}

theorem isSolvable_fixSubgroup_of_isSolvable_centralizer
    (hgL : g ∈ Subgroup.normalizer (L : Set Γ)) (hKL : K ≤ L)
    (hsol : IsSolvable ↥(K ⊓ Subgroup.centralizer ({g} : Set Γ))) :
    IsSolvable ↥(((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⊓
      fixSubgroup (centerQuotAut ↥L (conjAut L g hgL))) := by
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let π : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  let α : MulAut ↥L := conjAut L g hgL
  let β : MulAut (↥L ⧸ Z) := centerQuotAut ↥L α
  let hinv : Z.map α.toMonoidHom = Z := Subgroup.map_center_eq α
  have hβα : β = onQuotient Z α hinv := by
    ext y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    change (QuotientGroup.mk' Z) (α l) = (onQuotient Z α hinv) ((QuotientGroup.mk' Z) l)
    rw [onQuotient_mk]
  have hpre : fixedPreimage Z α hinv = (fixSubgroup β).comap π := by
    ext l
    rw [Subgroup.mem_comap, mem_fixSubgroup, hβα]
    exact Iff.rfl
  let P : Subgroup ↥L := (K.subgroupOf L) ⊓ fixedPreimage Z α hinv
  have hPfix : P ⊓ fixSubgroup α =
      (K ⊓ Subgroup.centralizer ({g} : Set Γ)).subgroupOf L := by
    ext x
    dsimp only [P]
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [CanonInn.mem_fixSubgroup_conjAut L hgL x]
    constructor
    · rintro ⟨⟨hxK, -⟩, hxC⟩
      exact ⟨hxK, hxC⟩
    · rintro ⟨hxK, hxC⟩
      refine ⟨⟨hxK, ?_⟩, hxC⟩
      exact fixed_le_fixedPreimage Z α hinv ((CanonInn.mem_fixSubgroup_conjAut L hgL x).2 hxC)
  have hPle : P ≤ fixedPreimage Z α hinv := inf_le_right
  have hPsol : IsSolvable ↥P := by
    refine isSolvable_of_le_fixedPreimage Z (le_refl Z) α hinv hPle ?_
    rw [hPfix]
    haveI : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer ({g} : Set Γ)) := hsol
    let e := Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKL :
      K ⊓ Subgroup.centralizer ({g} : Set Γ) ≤ L)
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hmapP : P.map π =
      (K.subgroupOf L).map π ⊓ fixSubgroup β := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ (K.subgroupOf L) ⊓ fixedPreimage Z α hinv := hx
      refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
      have hxFP : x ∈ fixedPreimage Z α hinv := hx'.2
      rw [hpre] at hxFP
      exact Subgroup.mem_comap.1 hxFP
    · rintro ⟨hyJ, hyfix⟩
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hyJ
      have hkFP : k ∈ fixedPreimage Z α hinv := by
        rw [hpre]
        exact Subgroup.mem_comap.2 hyfix
      exact ⟨k, ⟨hk, hkFP⟩, rfl⟩
  haveI : Group.IsSolvable ↥P := hPsol
  have hsurj : IsSolvable ↥(P.map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap P) (π.subgroupMap_surjective P)
  rwa [hmapP] at hsurj

theorem exists_map_centerQuotAut_ne_of_not_mem_centralizer
    (hgL : g ∈ Subgroup.normalizer (L : Set Γ)) (hKL : K ≤ L)
    (hK : CFSG.Open.IsQuasisimple ↥K)
    (hgK : g ∈ Subgroup.normalizer (K : Set Γ))
    (hgC : g ∉ Subgroup.centralizer (K : Set Γ)) :
    ∃ j ∈ (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)),
      centerQuotAut ↥L (conjAut L g hgL) j ≠ j := by
  by_contra h
  push Not at h
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let π : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  let α : MulAut ↥L := conjAut L g hgL
  let β : MulAut (↥L ⧸ Z) := centerQuotAut ↥L α
  let hinv : Z.map α.toMonoidHom = Z := Subgroup.map_center_eq α
  have hpre : fixedPreimage Z α hinv = (fixSubgroup β).comap π := by
    exact fixedPreimage_centerQuotAut_eq_comap α hinv
  have hKFP : K.subgroupOf L ≤ fixedPreimage Z α hinv := by
    intro l hl
    rw [hpre]
    exact Subgroup.mem_comap.2 (h (π l) ⟨l, hl, rfl⟩)
  let incl : ↥(K.subgroupOf L) →* fixedPreimage Z α hinv := Subgroup.inclusion hKFP
  let φ : ↥(K.subgroupOf L) →* Z := (displacement Z α hinv (le_refl Z)).comp incl
  haveI : Group.IsPerfect ↥(K.subgroupOf L) := by
    haveI : Group.IsPerfect ↥K := ⟨hK.1⟩
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.surjective
  haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  haveI : IsMulCommutative φ.range :=
    isMulCommutative_iff.mpr fun a b =>
      Subtype.ext (Subtype.ext
        (Subgroup.mem_center_iff.1 a.val.2 (b.val : ↥L)).symm)
  haveI : Subsingleton φ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hφ : ∀ x, φ x = 1 := by
    intro x
    have hx : (⟨φ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : φ.range) = 1 :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val hx
  apply hgC
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let l : ↥L := ⟨k, hKL hk⟩
  let kL : ↥(K.subgroupOf L) := ⟨l, hk⟩
  have h1 : (displacement Z α hinv (le_refl Z)) (incl kL) = 1 := hφ kL
  have h2 : α (incl kL).val = (incl kL).val :=
    (displacement_eq_one_iff Z α hinv (le_refl Z) (incl kL)).1 h1
  have h3 : g⁻¹ * k * g = k := by
    have h4 := congrArg Subtype.val h2
    rw [coe_conjAut] at h4
    have hval : (incl kL).val = l := rfl
    rw [hval] at h4
    simpa [l] using h4
  calc k * g = g * (g⁻¹ * k * g) := by group
    _ = g * k := by rw [h3]

theorem eq_of_isComponentOf_fixSubgroup_centerQuotAut
    (hyL : y ∈ Subgroup.normalizer (L : Set Γ))
    (hKdef : K = GLALayer (L ⊓ Subgroup.centralizer ({y} : Set Γ)))
    (hKcomp : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)))
    {J' : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hJ' : IsComponentOf J' (fixSubgroup (centerQuotAut ↥L (conjAut L y hyL)))) :
    J' = (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let π : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  let α : MulAut ↥L := conjAut L y hyL
  let β : MulAut (↥L ⧸ Z) := centerQuotAut ↥L α
  let Y : Subgroup (↥L ⧸ Z) := fixSubgroup β
  let J : Subgroup (↥L ⧸ Z) := (K.subgroupOf L).map π
  let hinv : Z.map α.toMonoidHom = Z := Subgroup.map_center_eq α
  have hpre : fixedPreimage Z α hinv = Y.comap π := by
    exact fixedPreimage_centerQuotAut_eq_comap α hinv
  have hJ'le : J' ≤ Y := hJ'.1
  let H : Subgroup ↥L := J'.comap π
  have hHle : H ≤ fixedPreimage Z α hinv := by
    rw [hpre]
    exact Subgroup.comap_mono hJ'le
  have hHsub : IsSubnormal H (fixedPreimage Z α hinv) := by
    rw [hpre]
    exact IsSubnormal.comap π hJ'.2.1
  let f : ↥H →* J' := (π.comp H.subtype).codRestrict J' fun h => h.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective y
    have hl' : l ∈ H := by
      rw [Subgroup.mem_comap]
      have hπl : π l = y := hl
      rwa [hπl]
    exact ⟨⟨l, hl'⟩, Subtype.ext hl⟩
  have hkerf : f.ker ≤ Subgroup.center ↥H := by
    intro h hh
    have hπ : π h.val = 1 := by
      exact congrArg Subtype.val hh
    have hz : ((h.val : ↥L) : ↥L) ∈ Z := (QuotientGroup.eq_one_iff _).1 hπ
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz (k : ↥L))
  have hJ'q : CFSG.IsQuasisimple ↥J' :=
    CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hJ'.2.2
  obtain ⟨-, hcommperf, hcommsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective f hf hkerf hJ'q.1
  have hHq : CFSG.IsQuasisimple ↥(commutator H) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hkerf hJ'q
  let P : Subgroup ↥L := (commutator H).map H.subtype
  have hPq : CFSG.Open.IsQuasisimple ↥P := by
    let e : ↥(commutator H) ≃* ↥P :=
      Subgroup.equivMapOfInjective (commutator H) H.subtype H.subtype_injective
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hHq)
  have hPmap : P.map π = J' := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hp
      exact (f c).2
    · intro hy
      obtain ⟨c, hc⟩ := hcommsurj ⟨y, hy⟩
      refine ⟨H.subtype c.val, Subgroup.mem_map_of_mem H.subtype c.2, ?_⟩
      exact congrArg Subtype.val hc
  have hPsubH : IsSubnormal P H := by
    have hPleH : P ≤ H := Subgroup.map_subtype_le _
    have hPnorm : (P.subgroupOf H).Normal := by
      have hPsub : P.subgroupOf H = commutator H := by
        change ((commutator H).map H.subtype).comap H.subtype = commutator H
        exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [hPsub]
      infer_instance
    exact IsSubnormal.step hPleH hPnorm (IsSubnormal.refl H)
  have hPsubFP : IsSubnormal P (fixedPreimage Z α hinv) := hPsubH.trans hHsub
  have hfixle : fixSubgroup α ≤ fixedPreimage Z α hinv := fixed_le_fixedPreimage Z α hinv
  have hPfix : P ≤ fixSubgroup α := by
    have hPleFP : P ≤ fixedPreimage Z α hinv :=
      (Subgroup.map_subtype_le (commutator H)).trans hHle
    let inclP : ↥P →* fixedPreimage Z α hinv := Subgroup.inclusion hPleFP
    let φP : ↥P →* Z := (displacement Z α hinv (le_refl Z)).comp inclP
    haveI : Group.IsPerfect ↥P := ⟨hPq.1⟩
    haveI : Group.IsPerfect φP.range := Group.IsPerfect.range φP
    haveI : IsMulCommutative φP.range :=
      isMulCommutative_iff.mpr fun a b =>
        Subtype.ext (Subtype.ext
          (Subgroup.mem_center_iff.1 a.val.2 (b.val : ↥L)).symm)
    haveI : Subsingleton φP.range := Group.IsPerfect.subsingleton_of_isMulCommutative
    have hφP : ∀ x, φP x = 1 := by
      intro x
      have hx : (⟨φP x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : φP.range) = 1 :=
        Subsingleton.elim _ _
      exact congrArg Subtype.val hx
    intro p hp
    let pP : ↥P := ⟨p, hp⟩
    have h1 : φP pP = 1 := hφP pP
    have h2 : α (inclP pP).val = (inclP pP).val :=
      (displacement_eq_one_iff Z α hinv (le_refl Z) (inclP pP)).1 h1
    have hval : (inclP pP).val = p := rfl
    rw [hval] at h2
    exact h2
  have hPcomp : IsComponentOf P (fixSubgroup α) := by
    refine ⟨hPfix, ?_, hPq⟩
    have h2 : IsSubnormal P (fixedPreimage Z α hinv) := hPsubFP
    have h3 := IsSubnormal.inf_of_le h2 hfixle
    rwa [inf_eq_left.mpr hPfix] at h3
  have hfixmap : (fixSubgroup α).map L.subtype =
      L ⊓ Subgroup.centralizer ({y} : Set Γ) :=
    map_fixSubgroup_conjAut L hyL
  have hlayer : K.subgroupOf L = GLALayer (fixSubgroup α) := by
    rw [hKdef]
    apply subgroupOf_eq_of_map_eq
    rw [← glaLayer_map L.subtype_injective, hfixmap]
  have hPleK : P ≤ K.subgroupOf L := by
    rw [hlayer]
    exact CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer hPcomp
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  have hKfix : IsComponentOf (K.subgroupOf L) (fixSubgroup α) :=
    CanonInn.isComponentOf_fixSubgroup_conjAut L hyL hKcomp
  have hJcomp : IsComponentOf J Y := by
    simpa [J, Y, β] using CanonInn.isComponentOf_map_centerQuot α hKfix
  have hJ'leJ : J' ≤ J := by
    rw [← hPmap]
    exact Subgroup.map_mono hPleK
  have hJcompJ : IsComponentOf J' J :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_of_le hJ' hJ'leJ hJcomp.1
  exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
    hJcompJ hJcomp.2.2

theorem u3SubcompTorus_of_core (hF : SubcompField) (hC : U3TorusCoreS) :
    U3SubcompTorus := by
  intro Γ _ _ L K B y n hset
  obtain ⟨hodd, hn3, hsplit, hB, hyB, hyL, hcardL, hKdef, hKcomp, hKlab, hBnormK,
    hcardK, hR⟩ := hset
  let hset' : U3Setup Γ L K B y n :=
    ⟨hodd, hn3, hsplit, hB, hyB, hyL, hcardL, hKdef, hKcomp, hKlab, hBnormK,
      hcardK, hR⟩
  obtain ⟨labL, hyN, hsplit3, hBNL, hM, hcore⟩ :=
    exists_u3CoreHyp_of_u3Setup hF hset'
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let S := ↥L ⧸ Z
  let π : ↥L →* S := QuotientGroup.mk' Z
  let β : MulAut S := centerQuotAut ↥L (conjAut L y hyN)
  let J : Subgroup S := (K.subgroupOf L).map π
  have hcore' : U3CoreHyp S labL β n J := hcore
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  intro g1 g2 hg1 hg2 hg1D hg2D
  rintro ⟨hsol1, hsol2⟩
  let β1 : MulAut S := centerQuotAut ↥L (conjAut L g1 (hBNL hg1))
  let β2 : MulAut S := centerQuotAut ↥L (conjAut L g2 (hBNL hg2))
  have hβ1pow : β1 ^ 3 = 1 := by
    change (centerQuotAut ↥L (conjAut L g1 (hBNL hg1))) ^ 3 = 1
    rw [← map_pow, CanonInn.conjAut_pow L (hBNL hg1) (hB.2 g1 hg1), map_one]
  have hβ2pow : β2 ^ 3 = 1 := by
    change (centerQuotAut ↥L (conjAut L g2 (hBNL hg2))) ^ 3 = 1
    rw [← map_pow, CanonInn.conjAut_pow L (hBNL hg2) (hB.2 g2 hg2), map_one]
  have hcomm1 : Commute β β1 := by
    exact commute_centerQuotAut_conjAut L hyN (hBNL hg1)
      (IsElemAbelian.comm hB hyB hg1)
  have hcomm2 : Commute β β2 := by
    exact commute_centerQuotAut_conjAut L hyN (hBNL hg2)
      (IsElemAbelian.comm hB hyB hg2)
  have hcomm12 : Commute β1 β2 := by
    exact commute_centerQuotAut_conjAut L (hBNL hg1) (hBNL hg2)
      (IsElemAbelian.comm hB hg1 hg2)
  have hmap1 : J.map β1.toMonoidHom = J := by
    exact map_centerQuotAut_conjAut_subgroupOf (hBNL hg1) (hBnormK hg1) hKL
  have hmap2 : J.map β2.toMonoidHom = J := by
    exact map_centerQuotAut_conjAut_subgroupOf (hBNL hg2) (hBnormK hg2) hKL
  have hg1C : g1 ∉ Subgroup.centralizer (K : Set Γ) := fun h => hg1D ⟨hg1, h⟩
  have hmove1 : ∃ j ∈ J, β1 j ≠ j := by
    exact exists_map_centerQuotAut_ne_of_not_mem_centralizer (g := g1)
      (hBNL hg1) hKL hKq (hBnormK hg1) hg1C
  have hmove2 : ∀ k : ℕ, ∃ j ∈ J, (β2 * β1 ^ k) j ≠ j := by
    intro k
    let g : Γ := g2 * g1 ^ k
    have hgB : g ∈ B := B.mul_mem hg2 (Subgroup.pow_mem _ hg1 k)
    have hgL : g ∈ Subgroup.normalizer (L : Set Γ) := hBNL hgB
    have hgK : g ∈ Subgroup.normalizer (K : Set Γ) := hBnormK hgB
    have hgC : g ∉ Subgroup.centralizer (K : Set Γ) := by
      intro hgc
      apply hg2D
      have hmem : g ∈ B ⊓ Subgroup.centralizer (K : Set Γ) := ⟨hgB, hgc⟩
      have hpowinv : (g1 ^ k)⁻¹ ∈ Subgroup.zpowers g1 :=
        Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers g1) k)
      have heq : g2 = g * (g1 ^ k)⁻¹ := by
        change g2 = g2 * g1 ^ k * (g1 ^ k)⁻¹
        group
      rw [heq]
      exact Subgroup.mul_mem_sup hmem hpowinv
    obtain ⟨j, hjJ, hjne⟩ := exists_map_centerQuotAut_ne_of_not_mem_centralizer
      (g := g) hgL hKL hKq hgK hgC
    refine ⟨j, hjJ, ?_⟩
    have hβ : centerQuotAut ↥L (conjAut L g hgL) = β2 * β1 ^ k := by
      change centerQuotAut ↥L (conjAut L (g2 * g1 ^ k) hgL) =
        centerQuotAut ↥L (conjAut L g2 (hBNL hg2)) *
          (centerQuotAut ↥L (conjAut L g1 (hBNL hg1))) ^ k
      exact centerQuotAut_conjAut_mul_pow L (hBNL hg2) (hBNL hg1)
        (IsElemAbelian.comm hB hg2 hg1) k
    rwa [hβ] at hjne
  have huniq : ∀ J' : Subgroup S, IsComponentOf J' (fixSubgroup β) → J' = J := by
    intro J' hJ'
    exact eq_of_isComponentOf_fixSubgroup_centerQuotAut hyN hKdef hKcomp hJ'
  have hT : U3TorusHyp S labL β β1 β2 n J :=
    { core := hcore'
      innDiagKind₁ := CanonInn.innDiagKind_centerQuot (hBNL hg1) (hM g1 hg1)
      innDiagKind₂ := CanonInn.innDiagKind_centerQuot (hBNL hg2) (hM g2 hg2)
      pow_three₁ := hβ1pow
      pow_three₂ := hβ2pow
      commute₁ := hcomm1
      commute₂ := hcomm2
      commute₁₂ := hcomm12
      map_eq₁ := hmap1
      map_eq₂ := hmap2
      moves₁ := hmove1
      moves₂ := hmove2
      unique := huniq }
  exact hC S labL β β1 β2 n J trivial hT
    ⟨isSolvable_fixSubgroup_of_isSolvable_centralizer (hBNL hg1) hKL hsol1,
      isSolvable_fixSubgroup_of_isSolvable_centralizer (hBNL hg2) hKL hsol2⟩

end TorusBridge

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
