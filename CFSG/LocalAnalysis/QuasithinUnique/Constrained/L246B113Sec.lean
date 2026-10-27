module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Eleven
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Bridge.B113Det

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

section Quasisimple

theorem equiv_centerQuotient_range {L M : Type*} [Group L] [Group M]
    (hq : CFSG.Open.IsQuasisimple L) (φ : L →* M) (hker : φ.ker ≠ ⊤) :
    Nonempty ((L ⧸ Subgroup.center L) ≃* (φ.range ⧸ Subgroup.center φ.range)) := by
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  have hcentral : φ.ker ≤ Subgroup.center L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq φ.ker hker
  let φ' : L →* φ.range := φ.rangeRestrict
  have hsurj : Function.Surjective φ' := φ.rangeRestrict_surjective
  have hker' : φ'.ker ≤ Subgroup.center L := by
    have : φ'.ker = φ.ker := φ.ker_rangeRestrict
    rwa [this]
  have hcomap := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
    φ' hsurj hker'
  let f : (L ⧸ Subgroup.center L) →* (φ.range ⧸ Subgroup.center φ.range) :=
    QuotientGroup.map (Subgroup.center L) (Subgroup.center φ.range) φ' hcomap.ge
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hy : φ' y ∈ Subgroup.center φ.range := by
      have : f (QuotientGroup.mk y) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).1 this
    have : y ∈ Subgroup.center L := by rw [← hcomap]; exact hy
    exact (QuotientGroup.eq_one_iff _).2 this
  · intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨y, rfl⟩ := hsurj w
    exact ⟨QuotientGroup.mk y, rfl⟩

end Quasisimple

section Sections

variable {V : Type} [CommGroup V]

abbrev secStab (I C : Subgroup V) : Subgroup (MulAut V) := stabSub I ⊓ stabSub C

theorem secStab_mem {I C : Subgroup V} (g : ↥(secStab I C)) :
    resHom I (Subgroup.inclusion inf_le_left g) ∈ stabSub (C.subgroupOf I) := by
  intro u
  show ((resHom I (Subgroup.inclusion inf_le_left g) u : ↥I) ∈ C.subgroupOf I) ↔
    u ∈ C.subgroupOf I
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact g.2.2 (u : V)

@[expose] noncomputable def secHom (I C : Subgroup V) :
    ↥(secStab I C) →* MulAut (↥I ⧸ C.subgroupOf I) :=
  (quotHom (C.subgroupOf I)).comp
    (((resHom I).comp (Subgroup.inclusion inf_le_left)).codRestrict
      (stabSub (C.subgroupOf I)) secStab_mem)

theorem secHom_mk {I C : Subgroup V} (g : ↥(secStab I C)) (x : ↥I) :
    secHom I C g (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨(g : MulAut V) x, (g.2.1 (x : V)).2 x.2⟩ : ↥I) := rfl

theorem secHom_eq_one_iff {I C : Subgroup V} (g : ↥(secStab I C)) :
    secHom I C g = 1 ↔ ∀ w ∈ I, (g : MulAut V) w * w⁻¹ ∈ C := by
  constructor
  · intro h w hw
    have := congrArg (fun φ : MulAut (↥I ⧸ C.subgroupOf I) => φ (QuotientGroup.mk ⟨w, hw⟩)) h
    simp only [secHom_mk, MulAut.one_apply] at this
    have h2 := (mk_eq_mk_iff (U := C.subgroupOf I) _ _).1 this
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  · intro h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [secHom_mk]
      refine (mk_eq_mk_iff (U := C.subgroupOf I) _ _).2 ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using h (v : V) v.2

theorem mem_autSec_iff {X : Subgroup (MulAut V)} {I C : Subgroup V} (hCI : C ≤ I)
    {φ : MulAut (↥I ⧸ C.subgroupOf I)} :
    φ ∈ autSec X I C ↔ ∃ g : ↥(secStab I C), (g : MulAut V) ∈ X ∧ secHom I C g = φ := by
  constructor
  · intro h
    obtain ⟨g', hg'X, hg'φ⟩ := mem_autQuot.1 h
    obtain ⟨g₀, hg₀X, hg₀⟩ := mem_autSub.1 hg'X
    have hgC : (g₀ : MulAut V) ∈ stabSub C := by
      intro u
      by_cases hu : u ∈ I
      · have h1 := g'.2 ⟨u, hu⟩
        rw [← hg₀] at h1
        exact h1
      · have h2 : (g₀ : MulAut V) u ∉ I := fun h3 => hu ((g₀.2 u).1 h3)
        exact ⟨fun h3 => absurd (hCI h3) h2, fun h3 => absurd (hCI h3) hu⟩
    refine ⟨⟨(g₀ : MulAut V), g₀.2, hgC⟩, hg₀X, ?_⟩
    rw [← hg'φ]
    exact congrArg (quotHom (C.subgroupOf I)) (Subtype.ext hg₀)
  · rintro ⟨g, hgX, rfl⟩
    refine mem_autQuot.2 ⟨⟨resHom I (Subgroup.inclusion inf_le_left g), secStab_mem g⟩, ?_, rfl⟩
    exact mem_autSub.2 ⟨Subgroup.inclusion inf_le_left g, hgX, rfl⟩

theorem exists_section_module [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) (hLG : L ≤ G) (hL : CFSG.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (Lb E : Subgroup (MulAut W)),
      (∀ w : W, w * w = 1) ∧ CFSG.IsQuasisimple ↥Lb ∧ XMod.IsIrrSec ↥Lb (⊥ : Subgroup W) ⊤ ∧
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (↥Lb ⧸ Subgroup.center ↥Lb)) ∧
      E ≤ Subgroup.normalizer (Lb : Set (MulAut W)) ∧ E ≠ ⊥ ∧ IsElemAbelian2 E ∧
      Nat.card W ≤ Nat.card E * Nat.card (fixV E) ∧
      ∃ ι : ↥L →* ↥Lb, Function.Surjective ι ∧ ∃ I : Subgroup V, I ≠ ⊥ ∧
        ∀ x : ↥L, ι x = 1 → ∀ w ∈ I, (x : MulAut V) w * w⁻¹ ∈ fixV L := by
  obtain ⟨H, I, hLH, hHG, hHn, hIrr, hHstab, hFF, hcent, hirr⟩ := B1_11_normal hV hA hLG hL hLA
  obtain ⟨hLinv, hcomm, hlt, -⟩ := (mem_irrPlus_top_iff).1 hIrr
  have hLo : CFSG.Open.IsQuasisimple ↥L := B1Red.isQuasisimple_to_open hL
  set C : Subgroup V := I ⊓ fixV L with hCdef
  have hCI : C ≤ I := inf_le_left
  have hLI : L ≤ stabSub I := hLH.trans hHstab
  have hLC : L ≤ stabSub C := B1.le_stabSub_of_invariant (isInv_inf hLinv (isInv_fixV L))
  have hLS : L ≤ secStab I C := le_inf hLI hLC
  let ψ : ↥L →* MulAut (↥I ⧸ C.subgroupOf I) := (secHom I C).comp (Subgroup.inclusion hLS)
  set Lb : Subgroup (MulAut (↥I ⧸ C.subgroupOf I)) := ψ.range with hLb
  have hker : ψ.ker ≠ ⊤ := by
    intro htop
    have hcl : commSub I L ≤ C := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      have h1 : ψ ⟨x, hx⟩ = 1 := by
        have : (⟨x, hx⟩ : ↥L) ∈ ψ.ker := by rw [htop]; trivial
        exact this
      exact (secHom_eq_one_iff (Subgroup.inclusion hLS ⟨x, hx⟩)).1 h1 w hw
    rw [hcomm] at hcl
    exact not_le_of_gt hlt hcl
  have hLbq : CFSG.Open.IsQuasisimple ↥Lb :=
    CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hLo ψ hker
  obtain ⟨e⟩ := equiv_centerQuotient_range hLo ψ hker
  have hW2 : ∀ w : ↥I ⧸ C.subgroupOf I, w * w = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_mul]
      have : v * v = 1 := Subtype.ext (by simpa [pow_two] using hV (v : V))
      rw [this]
      exact QuotientGroup.mk_one _
  have hIrrSec : XMod.IsIrrSec ↥Lb (⊥ : Subgroup (↥I ⧸ C.subgroupOf I)) ⊤ := by
    refine ⟨lt_of_le_of_ne bot_le fun h => ?_, fun J hJ _ _ => ?_⟩
    · obtain ⟨x, hxI, hxC⟩ := IsConcreteLE.exists_of_lt hlt
      have h1 : (QuotientGroup.mk ⟨x, hxI⟩ : ↥I ⧸ C.subgroupOf I) ∈ (⊥ : Subgroup _) := by
        rw [h]
        trivial
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact hxC h1
    · set Jt : Subgroup V := (J.comap (QuotientGroup.mk' (C.subgroupOf I))).map I.subtype with hJt
      have hJtI : Jt ≤ I := Subgroup.map_subtype_le _
      have hCJt : C ≤ Jt := by
        intro c hc
        refine ⟨⟨c, hCI hc⟩, ?_, rfl⟩
        show (QuotientGroup.mk ⟨c, hCI hc⟩ : ↥I ⧸ C.subgroupOf I) ∈ J
        have : (QuotientGroup.mk ⟨c, hCI hc⟩ : ↥I ⧸ C.subgroupOf I) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (by rw [Subgroup.mem_subgroupOf]; exact hc)
        rw [this]
        exact J.one_mem
      have hJtinv : ∀ x ∈ L, ∀ w ∈ Jt, x w ∈ Jt := by
        intro x hx w hw
        obtain ⟨z, hzJ, rfl⟩ := hw
        have hzJ' : (QuotientGroup.mk z : ↥I ⧸ C.subgroupOf I) ∈ J := hzJ
        have hxmem : ψ ⟨x, hx⟩ ∈ Lb := ⟨⟨x, hx⟩, rfl⟩
        have h2 := hJ ⟨ψ ⟨x, hx⟩, hxmem⟩ _ hzJ'
        refine ⟨⟨x z, (hLI hx (z : V)).2 z.2⟩, ?_, rfl⟩
        exact h2
      rcases hirr Jt hJtinv hCJt hJtI with h | h
      · left
        refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
        obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
        have hz : (z : V) ∈ Jt := ⟨z, hy, rfl⟩
        rw [h] at hz
        exact (QuotientGroup.eq_one_iff _).2 (by rw [Subgroup.mem_subgroupOf]; exact hz)
      · right
        refine (Subgroup.eq_top_iff' _).2 fun y => ?_
        obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
        have hz : (z : V) ∈ Jt := by rw [h]; exact z.2
        obtain ⟨z', hz'J, hz'⟩ := hz
        have : z' = z := Subtype.ext hz'
        subst this
        exact hz'J
  obtain ⟨E, hEH, hE0, hEel, hEcard⟩ := hFF
  have hEN : E ≤ Subgroup.normalizer (Lb : Set (MulAut (↥I ⧸ C.subgroupOf I))) := by
    refine le_normalizer_of_conj fun f hf y hy => ?_
    obtain ⟨g, hgH, rfl⟩ := (mem_autSec_iff hCI).1 (hEH hf)
    obtain ⟨l, rfl⟩ := hy
    refine ⟨⟨(g : MulAut V) * (l : MulAut V) * (g : MulAut V)⁻¹, hHn _ hgH _ l.2⟩, ?_⟩
    have e1 : Subgroup.inclusion hLS ⟨(g : MulAut V) * (l : MulAut V) * (g : MulAut V)⁻¹,
        hHn _ hgH _ l.2⟩ = g * Subgroup.inclusion hLS l * g⁻¹ := rfl
    show secHom I C (Subgroup.inclusion hLS _) = _
    rw [e1, map_mul, map_mul, map_inv]
    rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h] at hlt
    exact not_lt_bot hlt
  refine ⟨↥I ⧸ C.subgroupOf I, inferInstance, inferInstance, Lb, E, hW2,
    B1Red.isQuasisimple_of_open hLbq, hIrrSec, ⟨e⟩, hEN, hE0, hEel, hEcard,
    ψ.rangeRestrict, ψ.rangeRestrict_surjective, I, hI0, fun x hx w hw => ?_⟩
  have h1 : ψ x = 1 := congrArg Subtype.val hx
  have h2 := (secHom_eq_one_iff (Subgroup.inclusion hLS x)).1 h1 w hw
  exact (inf_le_right : C ≤ fixV L) h2

end Sections

end CFSG.QuasithinUnique.Bridge.B113Det
