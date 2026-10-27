module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShapeW
import all CFSG.HardMathSupport.Dickson.Bal207.CompShapeW
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbBase

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

structure CompShapeOn (p : ℕ) (T : ∀ (Q : Type) [Group Q], Prop) {S : Type} [Group S]
    (H : Subgroup (MulAut S)) (β : MulAut S) : Prop where
  layer : PerfectInLayer β
  type : ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) → T (↥L ⧸ Subgroup.center ↥L)
  norm : ∀ ω ∈ H, ω * β = β * ω → ω ^ p = 1 → ∀ L : Subgroup S,
    IsComponentOf L (fixSubgroup β) → L.map ω.toMonoidHom = L
  moved : ∀ ω : MulAut S, ω * β = β * ω → ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) →
    L.map ω.toMonoidHom ≠ L → Subgroup.center ↥L = ⊥

theorem CompShapeW.compShapeOn {p : ℕ} {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    {β : MulAut S} (h : CompShapeW p T β) (H : Subgroup (MulAut S)) : CompShapeOn p T H β :=
  ⟨h.layer, h.type, fun ω _ hω hωp L hL => h.norm ω hω hωp L hL, h.moved⟩

theorem CompShape.compShapeOn {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    {β : MulAut S} (h : CompShape T β) (p : ℕ) (H : Subgroup (MulAut S)) :
    CompShapeOn p T H β :=
  (h.compShapeW p).compShapeOn H

section Congr

variable {S G : Type} [Group S] [Group G]

theorem CompShapeOn.of_congr {p : ℕ} {T : ∀ (Q : Type) [Group Q], Prop} (hT : IsoInvariant T)
    (e : S ≃* G) {H : Subgroup (MulAut G)} {β : MulAut S}
    (h : CompShapeOn p T H (MulAut.congr e β)) :
    CompShapeOn p T (H.comap (MulAut.congr e).toMonoidHom) β := by
  have hmapc : ∀ {L : Subgroup S}, IsComponentOf L (fixSubgroup β) →
      IsComponentOf (L.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := fun hL => by
    rw [fixSubgroup_mulAutCongr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hL
  have hcomm : ∀ {ω : MulAut S}, ω * β = β * ω →
      MulAut.congr e ω * MulAut.congr e β = MulAut.congr e β * MulAut.congr e ω := fun hω => by
    rw [← map_mul, ← map_mul, hω]
  refine ⟨LieSemisimple.perfectInLayer_of_congr e β h.layer, fun L hL => ?_,
    fun ω hωH hω hωp L hL => ?_, fun ω hω L hL hne => ?_⟩
  · let g : ↥L ≃* ↥(L.map (e : S →* G)) := L.equivMapOfInjective (e : S →* G) e.injective
    exact hT _ _ (centerQuotientCongr g).symm (h.type _ (hmapc hL))
  · have h1 := h.norm (MulAut.congr e ω) hωH (hcomm hω) (by rw [← map_pow, hωp, map_one]) _
      (hmapc hL)
    rw [map_map_congr] at h1
    exact Subgroup.map_injective e.injective h1
  · have hne' : (L.map (e : S →* G)).map (MulAut.congr e ω).toMonoidHom ≠ L.map (e : S →* G) := by
      rw [map_map_congr]
      exact fun h1 => hne (Subgroup.map_injective e.injective h1)
    have hZ := h.moved _ (hcomm hω) _ (hmapc hL) hne'
    let g : ↥L ≃* ↥(L.map (e : S →* G)) := L.equivMapOfInjective (e : S →* G) e.injective
    have h2 := Subgroup.map_center_eq g
    rw [hZ] at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ g.injective).1 h2

end Congr

section Lift

variable {X : Type} [Group X]

theorem actHom_ne_one {K : Subgroup X} (hK : CFSG.Open.IsQuasisimple ↥K) {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (haK : a ∉ Subgroup.centralizer (K : Set X)) :
    actHom K ⟨a, ha⟩ ≠ 1 := by
  intro h1
  apply haK
  have hα1 : K.normalizerMonoidHom ⟨a, ha⟩ = 1 := by
    refine mulAut_eq_one_of_forall_mem_center hK.1 _ fun k => ?_
    have h2 : (QuotientGroup.mk (K.normalizerMonoidHom ⟨a, ha⟩ k) : ↥K ⧸ Subgroup.center ↥K) =
        QuotientGroup.mk k := by
      rw [← actHom_mk, h1, MulAut.one_apply]
    exact QuotientGroup.eq.1 h2.symm
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h3 := congrArg Subtype.val (congrArg (fun γ : MulAut ↥K => γ ⟨k, hk⟩) hα1)
  simp only [MulAut.one_apply] at h3
  change a * k * a⁻¹ = k at h3
  calc k * a = a * k * a⁻¹ * a := by rw [h3]
    _ = a * k := by group

theorem compShapeOn_lift {T : ∀ (Q : Type) [Group Q], Prop} (hT : IsoInvariant T) [Finite X]
    {p : ℕ} (hp : p.Prime) {K : Subgroup X} {H : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))}
    {a : X} (ha : a ∈ Subgroup.normalizer (K : Set X)) (hS : CompShapeOn p T H (actHom K ⟨a, ha⟩))
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) ∧ T (↥J ⧸ Subgroup.center ↥J) ∧
      (∀ (g : X) (hg : g ∈ Subgroup.normalizer (K : Set X)),
        ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X) → g ^ p ∈ Subgroup.centralizer (K : Set X) →
          actHom K ⟨g, hg⟩ ∈ H → g ∈ Subgroup.normalizer (J : Set X)) ∧
      (∀ g ∈ Subgroup.normalizer (K : Set X), ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X) →
        g ∉ Subgroup.normalizer (J : Set X) →
          Nat.card ↥(Subgroup.center ↥J) ∣ Nat.card ↥(Subgroup.center ↥K) ∧
            p ∣ Nat.card ↥J) := by
  have hpow1 : ∀ (g : X) (hg : g ∈ Subgroup.normalizer (K : Set X)),
      g ^ p ∈ Subgroup.centralizer (K : Set X) → K.normalizerMonoidHom ⟨g, hg⟩ ^ p = 1 := by
    intro g hg hgp
    ext k
    have : (K.normalizerMonoidHom ⟨g, hg⟩ ^ p : MulAut ↥K) =
        K.normalizerMonoidHom (⟨g, hg⟩ ^ p) := by rw [map_pow]
    rw [this]
    have hk : ((K.normalizerMonoidHom (⟨g, hg⟩ ^ p) k : ↥K) : X) = g ^ p * k * (g ^ p)⁻¹ := rfl
    rw [MulAut.one_apply, hk]
    have := Subgroup.mem_centralizer_iff.1 hgp (k : X) k.2
    calc g ^ p * (k : X) * (g ^ p)⁻¹ = (k : X) * g ^ p * (g ^ p)⁻¹ := by rw [← this]
      _ = (k : X) := by group
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨a, ha⟩
  have hα₀ : ∀ k : ↥K, ((α₀ k : ↥K) : X) = a * k * a⁻¹ := fun k => rfl
  let Z := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hbar : ∀ (n : ↥(Subgroup.normalizer (K : Set X))) (k : ↥K),
      π (K.normalizerMonoidHom n k) = actHom K n (π k) := fun n k => (actHom_mk K n k).symm
  have hapow : ∀ n : ↥(Subgroup.normalizer (K : Set X)), K.normalizerMonoidHom n ^ p = 1 →
      actHom K n ^ p = 1 := by
    intro n hn
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rw [← map_pow, ← hbar, map_pow, hn, MulAut.one_apply, MulAut.one_apply]
  set C : Subgroup ↥K := fixSubgroup α₀ with hC
  have hCmap : C.map K.subtype = K ⊓ Subgroup.centralizer ({a} : Set X) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h1 : a * (k : X) * a⁻¹ = k := by
        have := congrArg Subtype.val (show α₀ k = k from hk)
        rwa [hα₀] at this
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      show (k : X) * a = a * (k : X)
      calc (k : X) * a = (a * (k : X) * a⁻¹) * a := by rw [h1]
        _ = a * (k : X) := by group
    · rintro ⟨hyK, hyC⟩
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show α₀ ⟨y, hyK⟩ = ⟨y, hyK⟩
      apply Subtype.ext
      rw [hα₀]
      have hyC' : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
      show a * y * a⁻¹ = y
      calc a * y * a⁻¹ = (y * a) * a⁻¹ := by rw [hyC']
        _ = y := by group
  have hc : ∀ y ∈ C ⊓ K.subtype.ker, ∀ z ∈ C, z * y = y * z := by
    intro y hy z _
    have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
    rw [this, mul_one, one_mul]
  have hJ0 : GLAPComponent p (C.map K.subtype) J := by rw [hCmap]; exact hJ
  obtain ⟨J₁, hJ₁, hJ₁map⟩ := exists_glaPComponent_map_central hp K.subtype hc hJ0
  have hJβ : GLAPComponent p (fixSubgroup (actHom K ⟨a, ha⟩)) (J₁.map π) :=
    glaPComponent_map_fixSubgroup π hker α₀ (actHom K ⟨a, ha⟩) (hbar _) hπ hp hJ₁
  have hlay : J₁.map π ≤ GLALayer (fixSubgroup (actHom K ⟨a, ha⟩)) :=
    hS.layer _ hJβ.1 (glaPComponent_perfect hJβ)
  have hJc : IsComponentOf (J₁.map π) (fixSubgroup (actHom K ⟨a, ha⟩)) :=
    (glaPComponent_isComponent_of_le_layer hJβ hlay).1
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := glaPComponent_perfect hJ₁
  have hperf : Group.IsPerfect ↥J₁ := Subgroup.isPerfect_iff.2 hJ₁perf
  have hcov := ker_subgroupMap_le_center π hker J₁
  have hQ1 : CFSG.IsQuasisimple ↥J₁ :=
    isQuasisimple_of_central_cover (π.subgroupMap J₁) (MonoidHom.subgroupMap_surjective π J₁)
      hperf hcov
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hJc.2.2)
  have hQ1' : CFSG.Open.IsQuasisimple ↥J₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQ1
  let e₂ : ↥J₁ ≃* ↥J :=
    (J₁.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hJ₁map)
  have hnorm_of : ∀ (g : X) (hg : g ∈ Subgroup.normalizer (K : Set X)),
      (J₁.map π).map (actHom K ⟨g, hg⟩).toMonoidHom = J₁.map π →
        g ∈ Subgroup.normalizer (J : Set X) := by
    intro g hg h1
    set γ₀ : MulAut ↥K := K.normalizerMonoidHom ⟨g, hg⟩ with hγ₀
    have h2 : (J₁.map γ₀.toMonoidHom).map π = J₁.map π := by
      rw [Subgroup.map_map, ← h1, Subgroup.map_map]
      rfl
    have h3 : J₁.map γ₀.toMonoidHom ≤ J₁ ⊔ Subgroup.center ↥K := by
      intro y hy
      have hy' : π y ∈ J₁.map π := h2 ▸ ⟨y, hy, rfl⟩
      obtain ⟨j, hj, hjy⟩ := hy'
      have hz : j⁻¹ * y ∈ Subgroup.center ↥K := hker (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hjy, inv_mul_cancel])
      have : y = j * (j⁻¹ * y) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hj hz
    have h4 : J₁.map γ₀.toMonoidHom ≤ J₁ := by
      refine le_of_perfect_of_le_sup_center hJ₁perf ?_ h3
      rw [← Subgroup.map_commutator, hJ₁perf]
    have h5 : J₁.map γ₀.toMonoidHom = J₁ := by
      refine Subgroup.eq_of_le_of_card_ge h4 ?_
      exact (Subgroup.card_map_of_injective (f := γ₀.toMonoidHom) γ₀.injective).ge
    apply mem_normalizer_of_map_conj_eq
    have hcomp : (MulAut.conj g).toMonoidHom.comp K.subtype = K.subtype.comp γ₀.toMonoidHom := by
      ext k
      rfl
    rw [← hJ₁map, Subgroup.map_map, hcomp, ← Subgroup.map_map, h5]
  have hcommβ : ∀ (g : X) (hg : g ∈ Subgroup.normalizer (K : Set X)),
      ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X) →
        actHom K ⟨g, hg⟩ * actHom K ⟨a, ha⟩ = actHom K ⟨a, ha⟩ * actHom K ⟨g, hg⟩ := by
    intro g hg hga
    have hγα : K.normalizerMonoidHom ⟨g, hg⟩ * α₀ = α₀ * K.normalizerMonoidHom ⟨g, hg⟩ :=
      normalizerMonoidHom_commute hg ha hga
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    have h1 := congrArg (fun γ : MulAut ↥K => π (γ k)) hγα
    simp only [MulAut.mul_apply] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, ← hbar, ← hbar, ← hbar, ← hbar]
    exact h1
  refine ⟨⟨hJ.1, hJ.2.1, CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂
    hQ1'⟩, ?_, fun g hg hga hgp hgH => ?_, fun g hg hga hgJ => ?_⟩
  ·
    obtain ⟨e₃⟩ := LieComp.nonempty_centralQuotient_mulEquiv hQ1'.1 (π.subgroupMap J₁)
      (MonoidHom.subgroupMap_surjective π J₁) hcov
    exact hT _ _ (e₃.symm.trans (centerQuotientCongr e₂)) (hS.type _ hJc)
  ·
    exact hnorm_of g hg (hS.norm _ hgH (hcommβ g hg hga) (hapow _ (hpow1 g hg hgp)) _ hJc)
  ·
    have hZ := hS.moved _ (hcommβ g hg hga) _ hJc fun h1 => hgJ (hnorm_of g hg h1)
    refine ⟨?_, dvd_card_of_glaPComponent hp hJ⟩
    have hZJ : ∀ z ∈ Subgroup.center ↥J₁, ((z : ↥K) : ↥K) ∈ Subgroup.center ↥K := by
      intro z hz
      have hz' : π.subgroupMap J₁ z ∈ Subgroup.center ↥(J₁.map π) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨j, rfl⟩ := MonoidHom.subgroupMap_surjective π J₁ y
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz j)]
      rw [hZ, Subgroup.mem_bot] at hz'
      apply hker
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hz'
    have hle : (Subgroup.center ↥J₁).map J₁.subtype ≤ Subgroup.center ↥K := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZJ z hz
    have hcard : Nat.card ↥(Subgroup.center ↥J) = Nat.card ↥(Subgroup.center ↥J₁) := by
      rw [← Subgroup.map_center_eq e₂]
      exact Subgroup.card_map_of_injective e₂.injective
    rw [hcard, ← Subgroup.card_map_of_injective (f := J₁.subtype) J₁.subtype_injective]
    exact Subgroup.card_dvd_of_le hle

end Lift

section Clauses

variable {X : Type} [Group X]

theorem bal207PlusFamClauses_of_compShapeOn_b2 [Finite X]
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {p : ℕ} {K B A : Subgroup X}
    (ctx : Bal207PlusCtx G p K B A) {T : ∀ (Q : Type) [Group Q], Prop} (hT : IsoInvariant T)
    {H : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))} (hBH : autImage B K ≤ H)
    (hS : ∀ β ∈ autImage B K, β ≠ 1 → CompShapeOn p T H β)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥K))
    (hb2 : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) →
      T (↥J ⧸ Subgroup.center ↥J) → ¬ IsBalSmall J → B ≤ Subgroup.normalizer (J : Set X) →
        IsStronglyLocallyOneBalanced p B a J) :
    Bal207PlusFamClauses p K B A := by
  have key : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
          T (↥J ⧸ Subgroup.center ↥J) ∧
          (∀ (g : X) (hg : g ∈ Subgroup.normalizer (K : Set X)),
            ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X) →
            g ^ p ∈ Subgroup.centralizer (K : Set X) → actHom K ⟨g, hg⟩ ∈ H →
              g ∈ Subgroup.normalizer (J : Set X)) ∧
          (∀ g ∈ Subgroup.normalizer (K : Set X), ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X) →
            g ∉ Subgroup.normalizer (J : Set X) →
              Nat.card ↥(Subgroup.center ↥J) ∣ Nat.card ↥(Subgroup.center ↥K) ∧
                p ∣ Nat.card ↥J) := by
    intro a haA ha1 J hJ
    have haB : a ∈ B := ctx.le haA
    have hβ : actHom K ⟨a, ctx.norm haB⟩ ∈ autImage B K :=
      mem_autImage.2 ⟨a, ctx.norm haB, haB, rfl⟩
    have hβ1 : actHom K ⟨a, ctx.norm haB⟩ ≠ 1 :=
      actHom_ne_one ctx.comp.2.2 (ctx.norm haB) (not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1)
    exact compShapeOn_lift hT ctx.prime (ctx.norm haB) (hS _ hβ hβ1) hJ
  have hcommB : ∀ a ∈ A, ∀ b ∈ B, ⁅b, a⁆ ∈ Subgroup.centralizer (K : Set X) := by
    intro a haA b hb
    have hc := congrArg Subtype.val (ctx.scp.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨a, ctx.le haA⟩)
    have h1 : ⁅b, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc
    rw [h1]
    exact one_mem _
  have hBJ : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) := by
    intro a haA ha1 J hJ b hb
    refine (key a haA ha1 J hJ).2.2.1 b (ctx.norm hb) (hcommB a haA b hb) ?_
      (hBH (mem_autImage.2 ⟨b, ctx.norm hb, hb, rfl⟩))
    rw [ctx.scp.2.1.2 b hb]
    exact one_mem _
  refine ⟨hBJ, fun a haA ha1 J hJ hsmall => ?_, ?_⟩
  · obtain ⟨hcomp, hTJ, -⟩ := key a haA ha1 J hJ
    exact hb2 a haA ha1 J hJ hcomp hTJ hsmall (hBJ a haA ha1 J hJ)
  · have hbot : A ≠ ⊥ := by
      rintro rfl
      exact ctx.noncyc inferInstance
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    refine ⟨a, haA, ha1', fun w hw _ hwB J hJ => ?_⟩
    have hwa' : ⁅w, a⁆ ∈ Subgroup.centralizer (K : Set X) := hwB a (ctx.le haA)
    have hwa : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
      rwa [commutatorElement_def] at hwa'
    refine mem_normalizer_of_exists_comm_moved ctx.prime (fun b hb => ctx.norm hb) hw hwa hwB hJ
      fun hJJ => ?_
    have hJ'c : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) (GLBConj w J) :=
      Glue.glaPComponent_gLBConj_of_comm hw hwa hJ
    have hmv : w ∉ Subgroup.normalizer (GLBConj w J : Set X) := by
      intro h
      apply hJJ
      have h1 := congrArg (GLBConj w⁻¹) (mem_normalizer_iff_gLBConj_eq.1 h)
      rw [gLBConj_gLBConj w⁻¹ w (GLBConj w J), mul_inv_cancel, gLBConj_one,
        gLBConj_gLBConj w⁻¹ w J, mul_inv_cancel, gLBConj_one] at h1
      exact h1
    obtain ⟨hcomp', -, -, hmoved⟩ := key a haA ha1' _ hJ'c
    obtain ⟨hZd, hpJ⟩ := hmoved w hw hwa' hmv
    have hpZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥(GLBConj w J)) := fun h => hZ (h.trans hZd)
    obtain ⟨x, hxB, hxJ, hx1, hxp⟩ := Amb.exists_mem_inf_of_isSCp ctx.prime ctx.scp
      (hBJ a haA ha1' _ hJ'c) hpJ
    obtain ⟨y, hyJ, hy⟩ := Glue.exists_comm_not_mem_core ctx.prime hcomp'.2.2 hpZ hxJ hx1 hxp
    exact ⟨x, hxB, hxJ, y, hyJ, hy⟩

end Clauses

end CFSG.HardMathSupport.Dickson.Bal207

end
