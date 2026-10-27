module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Spec
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Std
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Cent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux
  OuterFourInAux CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot autCenterQuot_mk)

section Core

set_option linter.unusedSectionVars false


theorem fieldAutU_of_threeCentral_component {Q : Type} [Group Q] [Finite Q] {a : MulAut Q}
    (hFa : FieldAutTwE6 Q a) (ha3 : a ^ 3 = 1) {z : Q} (hz : IsThreeCentral Q z) (haz : a z = z)
    {G : Type} [Group G] (hGp : Group.IsPerfect G) (p : G →* Q)
    (hker : p.ker ≤ Subgroup.center G)
    (hT : GLAPComponent 3 (Subgroup.centralizer ({z} : Set Q)) p.range) (α : MulAut G)
    (hα3 : α ^ 3 = 1) (hαa : ∀ g, p (α g) = a (p g)) :
    FieldAutU 3 (G ⧸ Subgroup.center G) (autCenterQuot G α) := by
  classical
  obtain ⟨K', hfK', hfin', σE, eC, η, γ, hK64, hσE, hη1, hηodd, hγ⟩ := fieldAutTwE6_model hFa
  have hK' : Nat.card K' = 64 := by rw [hK64]; norm_num
  have hσ8 : ∀ c, σE c = c ^ 8 := fun c => by rw [hσE c]; norm_num
  obtain ⟨L, _, _, _, D, e₁, _, hcompat⟩ := exists_std8_fieldCompat hK' σE hσ8
  obtain ⟨η', m, hηc, hmc⟩ := hcompat η
  obtain ⟨ζ, hζ, hζη⟩ := exists_order_nine_unit_of_fieldAut hK' hη1 hηodd η' hηc
  obtain ⟨ω, hω⟩ := TwE6InnerAbs.exists_orderOf_three (L := L)
  haveI := D.finite_Γ
  let γΓ : MulAut ↥D.S.Γ := MulAut.congr e₁ γ
  let Θ₂ : Q ≃* ↥D.S.Γ := (eC.trans e₁).trans γΓ
  have hz' := e6IsThreeCentral_map Θ₂ hz
  obtain ⟨g, c, hc, hgc⟩ := D.exists_conj_dV_of_threeCentral hω hz'
  have hcop : Nat.Coprime 3 c.val := by
    have h0 : c.val ≠ 0 := fun h => hc ((ZMod.val_eq_zero c).1 h)
    have h3 : c.val < 3 := ZMod.val_lt c
    obtain h | h : c.val = 1 ∨ c.val = 2 := by omega
    · rw [h]; decide
    · rw [h]; decide
  have hω' : orderOf (ω ^ c.val) = 3 := by
    rw [Nat.Coprime.orderOf_pow (by rwa [hω]), hω]
  have hgz : g * Θ₂ z * g⁻¹ = D.z0 hω' := by
    apply Subtype.ext
    change ((g * Θ₂ z * g⁻¹ : ↥D.S.Γ) : ModGL Tag.E6 L) = dV (ω ^ c.val) x0
    rw [hgc, dV_smul_x0]
  let Θ : Q ≃* ↥D.S.Γ := Θ₂.trans (MulAut.conj g)
  have hΘz : Θ z = D.z0 hω' := hgz
  set h' : ModGL Tag.E6 L := (g : ModGL Tag.E6 L) * m *
    (Units.map (entrywiseHom η'.toRingHom) (g : ModGL Tag.E6 L))⁻¹ with hh'
  have hΘcoe : ∀ q : Q, ((Θ q : ↥D.S.Γ) : ModGL Tag.E6 L) =
      (g : ModGL Tag.E6 L) * ((e₁ (γ (eC q)) : ↥D.S.Γ) : ModGL Tag.E6 L) *
        (g : ModGL Tag.E6 L)⁻¹ := by
    intro q
    change ((g * γΓ (e₁ (eC q)) * g⁻¹ : ↥D.S.Γ) : ModGL Tag.E6 L) = _
    have h1 : γΓ (e₁ (eC q)) = e₁ (γ (eC q)) := by
      show e₁ (γ (e₁.symm (e₁ (eC q)))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h1]
    simp
  have hfa : ∀ q : Q, γ (eC (a q)) = fieldActor σE η (γ (eC q)) := by
    intro q
    have h1 := DFunLike.congr_fun hγ (γ (eC q))
    simp only [MulAut.mul_apply, MulAut.congr_apply, MulEquiv.trans_apply] at h1
    have h2 : γ⁻¹ (γ (eC q)) = eC q := MulAut.inv_apply_self _ _ _
    rwa [h2, MulEquiv.symm_apply_apply] at h1
  have hΘa : ∀ q : Q, ((Θ (a q) : ↥D.S.Γ) : ModGL Tag.E6 L) =
      h' * Units.map (entrywiseHom η'.toRingHom) ((Θ q : ↥D.S.Γ) : ModGL Tag.E6 L) * h'⁻¹ := by
    intro q
    rw [hΘcoe, hΘcoe q, hfa, hmc, hh']
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
    group
  have hT' : GLAPComponent 3 (Subgroup.centralizer ({D.z0 hω'} : Set ↥D.S.Γ))
      (p.range.map Θ.toMonoidHom) := by
    have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three Θ hT
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton, hΘz] at h1
    exact h1
  obtain ⟨k, hk⟩ := D.exists_Rc_eq_of_glaPComponent hω' hT'
  let q : G →* ModGL Tag.E6 L := D.S.Γ.subtype.comp (Θ.toMonoidHom.comp p)
  have hrange : q.range = rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 (ω ^ c.val))) k := by
    rw [← D.map_Rc k, ← hk, MonoidHom.range_comp, MonoidHom.range_comp]
  have hqker : q.ker ≤ Subgroup.center G := by
    intro g hg
    apply hker
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 : (Θ (p g) : ↥D.S.Γ) = 1 := Subtype.ext hg
    exact Θ.injective (by rw [h1, map_one])
  have hqα : ∀ g', q (α g') = h' * Units.map (entrywiseHom η'.toRingHom) (q g') * h'⁻¹ := by
    intro g'
    change ((Θ (p (α g')) : ↥D.S.Γ) : ModGL Tag.E6 L) = _
    rw [hαa, hΘa]
    rfl
  have hqR : ∀ g, q g ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 (ω ^ c.val))) k :=
    fun g => by rw [← hrange]; exact ⟨g, rfl⟩
  let qR : G →* ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 (ω ^ c.val))) k) :=
    q.codRestrict _ hqR
  have hqRsurj : Function.Surjective qR := by
    intro r
    obtain ⟨g, hg⟩ : (r : ModGL Tag.E6 L) ∈ q.range := by rw [hrange]; exact r.2
    exact ⟨g, Subtype.ext hg⟩
  have hqRker : qR.ker ≤ Subgroup.center G := fun g hg => hqker (by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact congrArg Subtype.val hg)
  have hG : CFSG.Open.IsQuasisimple G :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_central_cover qR hqRsurj hGp
        hqRker (D.rationalComponent_quasisimple_lie hω' k).1)
  exact Std8.fieldAutU_of_hom D hω' k η' hζ hζη h' hG q hrange hqker α hα3 hqα

end Core

section Main

set_option linter.unusedSectionVars false


theorem e6_fieldAut_on_u3_component {X : Type} [Group X] [Finite X] {K B J : Subgroup X}
    {x y : X} (hK : IsComponentOf K ⊤) (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hLie : IsLieQuot ↥K IsTwE6EightIndex)
    (hx : x ∈ B) (hy : y ∈ B)
    (hFx : FieldAutTwE6 (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨x, hBN hx⟩))
    {z : ↥K ⧸ Subgroup.center ↥K} (hyz : actHom K ⟨y, hBN hy⟩ = MulAut.conj z)
    (hz : IsThreeCentral (↥K ⧸ Subgroup.center ↥K) z)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J)
    (hJL : IsLieQuot ↥J IsU3EightIndex)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X)) :
    ∃ φ ∈ autImage (B.subgroupOf (Subgroup.centralizer ({y} : Set X)))
        (J.subgroupOf (Subgroup.centralizer ({y} : Set X))),
      FieldAutU 3 (↥(J.subgroupOf (Subgroup.centralizer ({y} : Set X))) ⧸
        Subgroup.center ↥(J.subgroupOf (Subgroup.centralizer ({y} : Set X)))) φ := by
  classical
  set C : Subgroup X := Subgroup.centralizer ({y} : Set X) with hC
  have hBC : B ≤ C := le_centralizer_of_elemAbelian hBel hy
  have hxC : x ∈ C := hBC hx
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJC : J ≤ C := hJ.1.trans inf_le_right
  have hKq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  haveI : Finite ↥K := Finite.of_injective _ K.subtype_injective
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) := inferInstance
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := hBN hx
  have hyN : y ∈ Subgroup.normalizer (K : Set X) := hBN hy
  set a : MulAut (↥K ⧸ Subgroup.center ↥K) := actHom K ⟨x, hxN⟩ with ha
  have hx3 : x ^ 3 = 1 := hBel.2 x hx
  have ha3 : a ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [ha, ← map_pow, h1, map_one]
  have haz : a z = z := by
    have hcomm : a * actHom K ⟨y, hyN⟩ = actHom K ⟨y, hyN⟩ * a := by
      rw [ha, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (commute_of_elemAbelian hBel hx hy).eq
    rw [hyz] at hcomm
    have hconj : MulAut.conj (a z) = MulAut.conj z := by
      have h1 : MulAut.conj (a z) = a * MulAut.conj z * a⁻¹ := by
        ext t
        simp [MulAut.conj_apply, MulAut.mul_apply]
      rw [h1, hcomm]
      group
    exact conj_inj_of_center_bot (center_quot_eq_bot hKq) hconj
  set J' : Subgroup ↥C := J.subgroupOf C with hJ'
  let x' : ↥C := ⟨x, hxC⟩
  have hx'N : x' ∈ Subgroup.normalizer (J' : Set ↥C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have hN := Subgroup.mem_normalizer_iff.1 (hBJ hx) (k : X)
    simpa [hJ', Subgroup.mem_subgroupOf, x'] using hN
  refine ⟨actHom J' ⟨x', hx'N⟩, mem_autImage.2 ⟨x', hx'N, Subgroup.mem_subgroupOf.2 hx, rfl⟩, ?_⟩
  rw [actHom_eq_autCenterQuot]
  let e : ↥J' ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  let ι : ↥J' →* ↥K := (Subgroup.inclusion hJK).comp e.toMonoidHom
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  let pQ : ↥J' →* ↥K ⧸ Subgroup.center ↥K := π.comp ι
  have hιval : ∀ j : ↥J', ((ι j : ↥K) : X) = (((j : ↥C)) : X) := fun j => rfl
  have hιinj : Function.Injective ι := (Subgroup.inclusion_injective hJK).comp e.injective
  have hpQker : pQ.ker ≤ Subgroup.center ↥J' := by
    intro j hj
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hj
    rw [Subgroup.mem_center_iff]
    intro w
    apply hιinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hj (ι w)
  have hα3 : (J'.normalizerMonoidHom ⟨x', hx'N⟩) ^ 3 = 1 := by
    have h1 : (⟨x', hx'N⟩ : ↥(Subgroup.normalizer (J' : Set ↥C))) ^ 3 = 1 :=
      Subtype.ext (Subtype.ext (by simpa [x'] using hx3))
    rw [← map_pow, h1, map_one]
  have hαa : ∀ j : ↥J', pQ (J'.normalizerMonoidHom ⟨x', hx'N⟩ j) = a (pQ j) := by
    intro j
    have h1 : ι (J'.normalizerMonoidHom ⟨x', hx'N⟩ j) =
        K.normalizerMonoidHom ⟨x, hxN⟩ (ι j) := Subtype.ext rfl
    show π (ι (J'.normalizerMonoidHom ⟨x', hx'N⟩ j)) = a (π (ι j))
    rw [h1, ha]
    exact (actHom_mk K ⟨x, hxN⟩ (ι j)).symm
  have hrange : pQ.range = (J.subgroupOf K).map π := by
    have : ι.range = J.subgroupOf K := by
      ext k
      constructor
      · rintro ⟨j, rfl⟩
        exact (j : ↥J').2
      · intro hk
        exact ⟨e.symm ⟨(k : X), hk⟩, Subtype.ext rfl⟩
    rw [MonoidHom.range_comp, this]
  have hT : GLAPComponent 3 (Subgroup.centralizer ({z} : Set (↥K ⧸ Subgroup.center ↥K)))
      pQ.range := by
    have hker : π.ker ≤ Subgroup.center ↥K := by
      rw [QuotientGroup.ker_mk']
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hJ₁ := glaPComponent_fixSubgroup Nat.prime_three hyN hJ
    have hJ₂ := glaPComponent_map_fixSubgroup π hker (K.normalizerMonoidHom ⟨y, hyN⟩)
      (actHom K ⟨y, hyN⟩) (fun k => (actHom_mk K ⟨y, hyN⟩ k).symm) hπs Nat.prime_three hJ₁
    rw [hyz, fixSubgroup_conj_eq_centralizer_e6] at hJ₂
    rw [hrange]
    exact hJ₂
  haveI hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
  have hGp : Group.IsPerfect ↥J' :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact fieldAutU_of_threeCentral_component hFx ha3 hz haz hGp pQ hpQker hT _ hα3 hαa

end Main

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
