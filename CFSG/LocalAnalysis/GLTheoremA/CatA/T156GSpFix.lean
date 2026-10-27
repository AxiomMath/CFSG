module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldB2der
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearGeom
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Sp

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedProj StatedSp)
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  centralizer_commutator_sympFour not_isMulCommutative_commutator_sympFour)

variable {m : ℕ} {K : Type} [Field K]

theorem exists_conj_of_commute [Finite K] [CharP K 2] [NeZero m] {σ : K ≃+* K}
    [hS : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K m))]
    (hna : ∃ a b : LargeEvenProj (LargeEvenSpGroup K m), a * b ≠ b * a)
    {φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hφI : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
    (hφ : φ * fieldAut m K σ = fieldAut m K σ * φ) :
    ∃ y ∈ ggFixSub (fieldAut m K σ), φ = MulAut.conj y := by
  obtain ⟨y, rfl⟩ := RecipeFieldSp.mem_conjImage_iff_inn.mp hφI
  refine ⟨y, ?_, rfl⟩
  have hc : ∀ u : StatedProj (StatedSp m K),
      u * (y⁻¹ * fieldAut m K σ y) = (y⁻¹ * fieldAut m K σ y) * u := by
    intro u
    obtain ⟨z, rfl⟩ := MulEquiv.surjective (fieldAut m K σ) u
    have e := congrArg (fun α : MulAut (StatedProj (StatedSp m K)) => α z) hφ
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at e
    calc fieldAut m K σ z * (y⁻¹ * fieldAut m K σ y)
        = y⁻¹ * (y * fieldAut m K σ z * y⁻¹) * fieldAut m K σ y := by group
      _ = y⁻¹ * (fieldAut m K σ y * fieldAut m K σ z * (fieldAut m K σ y)⁻¹) *
            fieldAut m K σ y := by rw [e]
      _ = (y⁻¹ * fieldAut m K σ y) * fieldAut m K σ z := by group
  have h1 : y⁻¹ * fieldAut m K σ y = 1 := FieldFixSp.eq_one_of_forall_comm hna hc
  have hy : fieldAut m K σ y = y := by
    have := congrArg (y * ·) h1
    simpa using this
  exact hy

theorem exists_fixGeom' [Finite K] [CharP K 2] [NeZero m] (hm : 2 ≤ m) {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ n) (hne : ¬(m = 2 ∧ n / p = 1))
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K m)))
    (hna : ∃ a b : LargeEvenProj (LargeEvenSpGroup K m), a * b ≠ b * a)
    {f : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m)))
    (hord : orderOf f = p) :
    LargeEvenRecipeSymplectic m (2 ^ (n / p)) false fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
          (LargeEvenGSpSet K m)) f I₀ θ₀ := by
  obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (fieldAut m K) FieldFixSp.fieldAut_injective σ]
    exact hord
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two hn hK hσ
  obtain ⟨hS₀, hP₀⟩ := simple_perfect_statedProj (r := m) (k := descentField σ) hm (by
    rintro ⟨hm2, hk2⟩
    apply hne ⟨hm2, ?_⟩
    rw [hcard] at hk2
    exact Nat.pow_right_injective (le_refl 2) (by simpa using hk2))
  haveI := hS
  haveI := hS₀
  haveI := hP₀
  have hι : Function.Injective (subfieldInj (r := m) σ) := subfieldInj_injective σ
  have hrange : (subfieldInj (r := m) σ).range = ggFixSub (fieldAut m K σ) := by
    rw [range_subfieldInj, ← spFixedGroup_fieldAut_eq_range hodd hσp]
    exact Subgroup.ext fun x => Iff.rfl
  have hder : ggFixDer (fieldAut m K σ) = (subfieldInj (r := m) σ).range := by
    haveI : Group.IsPerfect (subfieldInj (r := m) σ).range :=
      Group.IsPerfect.range (subfieldInj (r := m) σ)
    calc ggFixDer (fieldAut m K σ)
        = ⁅(subfieldInj (r := m) σ).range, (subfieldInj (r := m) σ).range⁆ := by
          rw [ggFixDer, hrange]
      _ = (subfieldInj (r := m) σ).range := Subgroup.commutator_eq_self
  let θ₀ : ggFixDer (fieldAut m K σ) ≃* StatedProj (StatedSp m (descentField σ)) :=
    (MulEquiv.subgroupCongr hder).trans (MonoidHom.ofInjective hι).symm
  have hna₀ : ∃ a b : StatedProj (StatedSp m (descentField σ)), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative (StatedProj (StatedSp m (descentField σ))) :=
      isMulCommutative_iff.mpr hcon
    exact Group.IsPerfect.not_isMulCommutative (StatedProj (StatedSp m (descentField σ))) ‹_›
  have key : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m), φ * fieldAut m K σ = fieldAut m K σ * φ →
        ∃ y ∈ ggFixDer (fieldAut m K σ), φ = MulAut.conj y := by
    intro φ hφI hφ
    obtain ⟨y, hy, rfl⟩ := exists_conj_of_commute hna hφI hφ
    refine ⟨y, ?_, rfl⟩
    rw [hder, hrange]
    exact hy
  refine ⟨descentField σ, inferInstance, inferInstance, hcard, hS₀, hna₀, θ₀, ?_, ?_⟩
  · intro φ hφI hφ
    obtain ⟨y, hy, rfl⟩ := key φ hφI hφ
    refine ⟨MulAut.conj (θ₀ ⟨y, hy⟩), RecipeFieldSp.mem_conjImage_iff_inn.mpr ⟨_, rfl⟩,
      fun g hg => ?_⟩
    have h1 : (⟨MulAut.conj y g, ggFixDer_map_mem hφ hg⟩ : ggFixDer (fieldAut m K σ)) =
        ⟨y, hy⟩ * ⟨g, hg⟩ * ⟨y, hy⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  · intro φ hφI hφ hg
    obtain ⟨y, hy, rfl⟩ := key φ hφI hφ
    have hc : ∀ r₀ : StatedProj (StatedSp m (descentField σ)),
        r₀ * θ₀ ⟨y, hy⟩ = θ₀ ⟨y, hy⟩ * r₀ := by
      intro r₀
      obtain ⟨⟨g, hg'⟩, rfl⟩ := MulEquiv.surjective θ₀ r₀
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show g * y = y * g
      have e := hg g hg'
      simp only [MulAut.conj_apply] at e
      calc g * y = (y * g * y⁻¹) * y := by rw [e]
        _ = y * g := by group
    have h1 := FieldFixSp.eq_one_of_forall_comm hna₀ hc
    have h2 : (⟨y, hy⟩ : ggFixDer (fieldAut m K σ)) = 1 :=
      θ₀.injective (by rw [h1, map_one])
    rw [show y = 1 from congrArg Subtype.val h2, map_one]

section B2der

theorem exists_raw_b2der [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ p) (hS : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K 2)))
    (hna : ∃ a b : LargeEvenProj (LargeEvenSpGroup K 2), a * b ≠ b * a)
    {f : MulAut (LargeEvenProj (LargeEvenSpGroup K 2))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K 2)))
    (hord : orderOf f = p) :
    LargeEvenRecipeSymplectic 2 2 true fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 2))
          (LargeEvenGSpSet K 2)) f I₀ θ₀ := by
  obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (fieldAut 2 K) FieldFixSp.fieldAut_injective σ]
    exact hord
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two hp.one_lt.le hK hσ
  have hk2 : Nat.card (descentField σ) = 2 := by rw [hcard, Nat.div_self hp.pos, pow_one]
  haveI := hS
  have hle : ⁅LargeEvenSpGroup (descentField σ) 2, LargeEvenSpGroup (descentField σ) 2⁆ ≤
      LargeEvenSpGroup (descentField σ) 2 :=
    Subgroup.commutator_le_self _
  let sp : StatedSp 2 (descentField σ) →* StatedProj (StatedSp 2 K) := subfieldProj (r := 2) σ
  let Ψ : ↥⁅LargeEvenSpGroup (descentField σ) 2, LargeEvenSpGroup (descentField σ) 2⁆ →*
      StatedProj (StatedSp 2 K) := sp.comp (Subgroup.inclusion hle)
  have hΨ : ∀ h, Ψ h = sp (Subgroup.inclusion hle h) := fun _ => rfl
  have hspScal : spScalars 2 (descentField σ) = ⊥ := by
    show (LargeEvenScalars (Fin 2 ⊕ Fin 2) (descentField σ)).subgroupOf
      (LargeEvenSpGroup (descentField σ) 2) = ⊥
    rw [largeEvenScalars_eq_bot hk2, Subgroup.bot_subgroupOf]
  have hsp_inj : Function.Injective sp := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 := (subfieldProj_eq_one_iff (r := 2) σ g).mp hg
    rw [hspScal, Subgroup.mem_bot] at h1
    exact h1
  have hrange : sp.range = ggFixSub (fieldAut 2 K σ) := by
    rw [← spFixedGroup_fieldAut_eq_range hodd hσp]
    exact Subgroup.ext fun x => Iff.rfl
  have hincl : (Subgroup.inclusion hle).range = commutator ↥(LargeEvenSpGroup (descentField σ) 2) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      have h1 : (g : GL (Fin 2 ⊕ Fin 2) (descentField σ)) ∈
          (commutator ↥(LargeEvenSpGroup (descentField σ) 2)).map
            (LargeEvenSpGroup (descentField σ) 2).subtype := by
        rw [Subgroup.map_subtype_commutator]
        exact g.2
      obtain ⟨z, hz, hzx⟩ := h1
      have h2 : Subgroup.inclusion hle g = z := Subtype.ext hzx.symm
      rw [h2]
      exact hz
    · intro hx
      have h1 : (x : GL (Fin 2 ⊕ Fin 2) (descentField σ)) ∈
          ⁅LargeEvenSpGroup (descentField σ) 2, LargeEvenSpGroup (descentField σ) 2⁆ := by
        rw [← Subgroup.map_subtype_commutator]
        exact ⟨x, hx, rfl⟩
      exact ⟨⟨x, h1⟩, Subtype.ext rfl⟩
  have hD : Ψ.range = ggFixDer (fieldAut 2 K σ) := by
    rw [MonoidHom.range_comp, hincl, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      hrange]
    rfl
  have hker : Ψ.ker = (LargeEvenScalars (Fin 2 ⊕ Fin 2) (descentField σ)).subgroupOf
      ⁅LargeEvenSpGroup (descentField σ) 2, LargeEvenSpGroup (descentField σ) 2⁆ := by
    rw [largeEvenScalars_eq_bot hk2, Subgroup.bot_subgroupOf, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker, hΨ] at hg
    have h1 : Subgroup.inclusion hle g = 1 := hsp_inj (by rw [hg, map_one])
    exact (Subgroup.mem_bot).mpr (Subgroup.inclusion_injective hle (by rw [h1, map_one]))
  let e : LargeEvenProj ⁅LargeEvenSpGroup (descentField σ) 2, LargeEvenSpGroup (descentField σ) 2⁆ ≃*
      ggFixDer (fieldAut 2 K σ) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange Ψ)).trans
      (MulEquiv.subgroupCongr hD)
  have he : ∀ h, ((e (QuotientGroup.mk h) : ggFixDer (fieldAut 2 K σ)) : StatedProj (StatedSp 2 K)) =
      Ψ h := fun _ => rfl
  obtain ⟨e₁⟩ := nonempty_largeEvenProj_equiv_of_card_two hk2
    ⁅LargeEvenSpGroup (descentField σ) 2, LargeEvenSpGroup (descentField σ) 2⁆
  obtain ⟨e₂⟩ := nonempty_commutator_subgroup_equiv (LargeEvenSpGroup (descentField σ) 2)
  obtain ⟨e₃⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hk2
  have hmap₃ : (commutator ↥(LargeEvenSpGroup (descentField σ) 2)).map e₃.toMonoidHom =
      commutator sympFour := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e₃.surjective]
  let e₄ : ↥(commutator ↥(LargeEvenSpGroup (descentField σ) 2)) ≃* ↥(commutator sympFour) :=
    ((commutator _).equivMapOfInjective e₃.toMonoidHom e₃.injective).trans
      (MulEquiv.subgroupCongr hmap₃)
  let e₅ := (e₁.trans e₂).trans e₄
  haveI : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
  have hS₀ : IsSimpleGroup
      (LargeEvenProj ⁅LargeEvenSpGroup (descentField σ) 2, LargeEvenSpGroup (descentField σ) 2⁆) :=
    MulEquiv.isSimpleGroup e₅
  have hna₀ : ∃ a b : LargeEvenProj ⁅LargeEvenSpGroup (descentField σ) 2,
      LargeEvenSpGroup (descentField σ) 2⁆, a * b ≠ b * a := by
    have h1 := not_isMulCommutative_commutator_sympFour
    rw [isMulCommutative_iff] at h1
    push Not at h1
    exact nonabelian_of_mulEquiv e₅.symm h1
  refine ⟨descentField σ, inferInstance, inferInstance, hk2, hS₀, hna₀, e.symm, ?_, ?_⟩
  ·
    intro φ hφI hφ
    obtain ⟨y, hy, rfl⟩ := exists_conj_of_commute hna hφI hφ
    rw [← hrange] at hy
    obtain ⟨b, rfl⟩ := hy
    refine ⟨(e.trans (LinearFieldFix.ggFixDerRestrict hφ)).trans e.symm,
      ⟨(b : GL (Fin 2 ⊕ Fin 2) (descentField σ)), ⟨1, one_ne_zero, ?_⟩, ?_⟩, ?_⟩
    · rw [one_smul]
      exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp b.2
    · intro g g' hg
      change ((e.trans (LinearFieldFix.ggFixDerRestrict hφ)).trans e.symm) (QuotientGroup.mk g) =
        QuotientGroup.mk g'
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [LinearFieldFix.coe_ggFixDerRestrict, he, he, MulAut.conj_apply, hΨ, hΨ, ← map_inv,
        ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change (b : GL (Fin 2 ⊕ Fin 2) (descentField σ)) * g * (b : GL (Fin 2 ⊕ Fin 2) (descentField σ))⁻¹ =
        (g' : GL (Fin 2 ⊕ Fin 2) (descentField σ))
      rw [hg]
    · intro g hg
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  ·
    intro φ hφI hφ htriv
    obtain ⟨y, hy, rfl⟩ := exists_conj_of_commute hna hφI hφ
    rw [← hrange] at hy
    obtain ⟨b, rfl⟩ := hy
    have hcomm : ∀ g ∈ commutator ↥(LargeEvenSpGroup (descentField σ) 2), g * b = b * g := by
      intro g hg
      rw [← hincl] at hg
      obtain ⟨g₀, rfl⟩ := hg
      have h1 : Ψ g₀ ∈ ggFixDer (fieldAut 2 K σ) := by
        rw [← hD]
        exact ⟨g₀, rfl⟩
      have h2 := htriv _ h1
      rw [MulAut.conj_apply, hΨ, ← map_inv, ← map_mul, ← map_mul] at h2
      have h3 := hsp_inj h2
      calc Subgroup.inclusion hle g₀ * b
          = b * Subgroup.inclusion hle g₀ * b⁻¹ * b := by rw [h3]
        _ = b * Subgroup.inclusion hle g₀ := by group
    have hb : e₃ b ∈ Subgroup.centralizer (commutator sympFour : Set sympFour) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [← hmap₃] at hh
      obtain ⟨g, hg, rfl⟩ := hh
      change e₃ g * e₃ b = e₃ b * e₃ g
      rw [← map_mul, ← map_mul, hcomm g hg]
    rw [centralizer_commutator_sympFour, Subgroup.mem_bot] at hb
    have hb1 : b = 1 := e₃.injective (by rw [hb, map_one])
    rw [hb1, map_one, map_one]

end B2der

end CFSG.LocalAnalysis.GLTheoremA.T156.Sp

end
