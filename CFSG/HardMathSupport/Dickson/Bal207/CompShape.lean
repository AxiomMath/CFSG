module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieQuasi
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

@[expose] def IsoInvariant (T : ∀ (Q : Type) [Group Q], Prop) : Prop :=
  ∀ (Q Q' : Type) [Group Q] [Group Q'], (Q ≃* Q') → T Q → T Q'

structure CompShape (T : ∀ (Q : Type) [Group Q], Prop) {S : Type} [Group S] (β : MulAut S) :
    Prop where
  layer : PerfectInLayer β
  type : ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) → T (↥L ⧸ Subgroup.center ↥L)
  norm : ∀ ω : MulAut S, ω * β = β * ω → ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) →
    L.map ω.toMonoidHom = L

section Congr

variable {S G : Type} [Group S] [Group G]

theorem fixSubgroup_mulAutCongr (e : S ≃* G) (β : MulAut S) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
  ext x
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
  exact e.eq_symm_apply.symm

noncomputable def centerQuotientCongr {L M : Type*} [Group L] [Group M] (g : L ≃* M) :
    (L ⧸ Subgroup.center L) ≃* (M ⧸ Subgroup.center M) :=
  QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)

theorem CompShape.of_congr {T : ∀ (Q : Type) [Group Q], Prop} (hT : IsoInvariant T)
    (e : S ≃* G) {β : MulAut S} (h : CompShape T (MulAut.congr e β)) : CompShape T β := by
  have hmapc : ∀ {L : Subgroup S}, IsComponentOf L (fixSubgroup β) →
      IsComponentOf (L.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := fun hL => by
    rw [fixSubgroup_mulAutCongr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hL
  refine ⟨LieSemisimple.perfectInLayer_of_congr e β h.layer, fun L hL => ?_,
    fun ω hω L hL => ?_⟩
  · let g : ↥L ≃* ↥(L.map (e : S →* G)) := L.equivMapOfInjective (e : S →* G) e.injective
    exact hT _ _ (centerQuotientCongr g).symm (h.type _ (hmapc hL))
  · have hω' : MulAut.congr e ω * MulAut.congr e β = MulAut.congr e β * MulAut.congr e ω := by
      rw [← map_mul, ← map_mul, hω]
    have h1 := h.norm (MulAut.congr e ω) hω' _ (hmapc hL)
    have hc : ((MulAut.congr e ω).toMonoidHom.comp (e : S →* G)) =
        (e : S →* G).comp ω.toMonoidHom := by
      ext x
      show e (ω (e.symm (e x))) = e (ω x)
      rw [MulEquiv.symm_apply_apply]
    rw [Subgroup.map_map, hc, ← Subgroup.map_map] at h1
    exact Subgroup.map_injective e.injective h1

end Congr

theorem mulAut_eq_one_of_forall_mem_center {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    (α : MulAut Y) (h : ∀ x : Y, x⁻¹ * α x ∈ Subgroup.center Y) : α = 1 := by
  let c : Y →* Subgroup.center Y :=
    { toFun := fun x => ⟨x⁻¹ * α x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hx := Subgroup.mem_center_iff.1 (h x) y⁻¹
        change (x * y)⁻¹ * α (x * y) = (x⁻¹ * α x) * (y⁻¹ * α y)
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by rw [map_mul]; group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hx]
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group }
  have hle : commutator Y ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [hperf] at hle
  ext x
  have h1 : c x = 1 := hle (Subgroup.mem_top x)
  have h2 : x⁻¹ * α x = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  calc α x = x * (x⁻¹ * α x) := by group
    _ = x := by rw [h2, mul_one]

theorem le_of_perfect_of_le_sup_center {Y : Type*} [Group Y] {J P : Subgroup Y}
    (hJ : ⁅J, J⁆ = J) (hP : ⁅P, P⁆ = P) (hle : P ≤ J ⊔ Subgroup.center Y) : P ≤ J := by
  have hZ : ∀ z ∈ Subgroup.center Y, ∀ y : Y, z * y = y * z := fun z hz y =>
    (Subgroup.mem_center_iff.1 hz y).symm
  have hcomm : ⁅J ⊔ Subgroup.center Y, J ⊔ Subgroup.center Y⁆ ≤ ⁅J, J⁆ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hu
    obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hv
    have e : ⁅j₁ * z₁, j₂ * z₂⁆ = ⁅j₁, j₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have h1 : z₁ * (j₂ * z₂) = (j₂ * z₂) * z₁ := hZ z₁ hz₁ _
      have h2 : z₂ * j₁⁻¹ = j₁⁻¹ * z₂ := hZ z₂ hz₂ _
      calc j₁ * z₁ * (j₂ * z₂) * (j₁ * z₁)⁻¹ * (j₂ * z₂)⁻¹
          = j₁ * (z₁ * (j₂ * z₂)) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (z₂ * j₁⁻¹) * z₂⁻¹ * j₂⁻¹ := by rw [h1]; group
        _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by rw [h2]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hj₁ hj₂
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅J ⊔ Subgroup.center Y, J ⊔ Subgroup.center Y⁆ := Subgroup.commutator_mono hle hle
    _ ≤ ⁅J, J⁆ := hcomm
    _ = J := hJ

theorem mem_normalizer_of_map_conj_eq {Y : Type*} [Group Y] {J : Subgroup Y} {g : Y}
    (h : J.map (MulAut.conj g).toMonoidHom = J) : g ∈ Subgroup.normalizer (J : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [← h]
    exact ⟨n, hn, rfl⟩
  · intro hn
    rw [← h] at hn
    obtain ⟨m, hm, hmn⟩ := hn
    have : m = n := by
      have h1 : g * m * g⁻¹ = g * n * g⁻¹ := hmn
      exact mul_left_cancel (mul_right_cancel h1)
    rw [← this]
    exact hm

section Lift

variable {X : Type} [Group X]

theorem normalizerMonoidHom_coe {K : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X))
    (k : ↥K) : ((K.normalizerMonoidHom ⟨g, hg⟩ k : ↥K) : X) = g * k * g⁻¹ := rfl

theorem normalizerMonoidHom_commute {K : Subgroup X} {g a : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X)) (ha : a ∈ Subgroup.normalizer (K : Set X))
    (hc : ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X)) :
    K.normalizerMonoidHom ⟨g, hg⟩ * K.normalizerMonoidHom ⟨a, ha⟩ =
      K.normalizerMonoidHom ⟨a, ha⟩ * K.normalizerMonoidHom ⟨g, hg⟩ := by
  ext k
  rw [MulAut.mul_apply, MulAut.mul_apply, normalizerMonoidHom_coe, normalizerMonoidHom_coe,
    normalizerMonoidHom_coe, normalizerMonoidHom_coe]
  have hmem : a * (g * (k : X) * g⁻¹) * a⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.1 ha _).1 ((Subgroup.mem_normalizer_iff.1 hg _).1 k.2)
  have hcomm := Subgroup.mem_centralizer_iff.1 hc _ hmem
  rw [commutatorElement_def] at hcomm
  calc g * (a * (k : X) * a⁻¹) * g⁻¹
      = (g * a * g⁻¹ * a⁻¹) * (a * (g * (k : X) * g⁻¹) * a⁻¹) * (g * a * g⁻¹ * a⁻¹)⁻¹ := by
        group
    _ = a * (g * (k : X) * g⁻¹) * a⁻¹ := by rw [← hcomm]; group

theorem compShape_lift {T : ∀ (Q : Type) [Group Q], Prop} (hT : IsoInvariant T) [Finite X]
    {p : ℕ} (hp : p.Prime) {K : Subgroup X} (hK : CFSG.Open.IsQuasisimple ↥K) {S : Type}
    [Group S] (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hS : ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → CompShape T β) {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X))
    (hap : a ^ p ∈ Subgroup.centralizer (K : Set X)) (haK : a ∉ Subgroup.centralizer (K : Set X))
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) ∧ T (↥J ⧸ Subgroup.center ↥J) ∧
      ∀ g ∈ Subgroup.normalizer (K : Set X), ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X) →
        g ∈ Subgroup.normalizer (J : Set X) := by
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨a, ha⟩
  have hα₀ : ∀ k : ↥K, ((α₀ k : ↥K) : X) = a * k * a⁻¹ := fun k => rfl
  have hα₀p : α₀ ^ p = 1 := by
    ext k
    have : (α₀ ^ p : MulAut ↥K) = K.normalizerMonoidHom (⟨a, ha⟩ ^ p) := by rw [map_pow]
    rw [this]
    have hk : ((K.normalizerMonoidHom (⟨a, ha⟩ ^ p) k : ↥K) : X) = a ^ p * k * (a ^ p)⁻¹ := rfl
    rw [MulAut.one_apply, hk]
    have := Subgroup.mem_centralizer_iff.1 hap (k : X) k.2
    calc a ^ p * (k : X) * (a ^ p)⁻¹ = (k : X) * a ^ p * (a ^ p)⁻¹ := by rw [← this]
      _ = (k : X) := by group
  let Z := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hmapZ : ∀ γ : MulAut ↥K, Z.map γ.toMonoidHom = Z := fun γ =>
    Subgroup.characteristic_iff_map_eq.1 inferInstance γ
  let bar : MulAut ↥K → MulAut (↥K ⧸ Z) := fun γ => QuotientGroup.congr Z Z γ (hmapZ γ)
  have hbar : ∀ γ k, π (γ k) = bar γ (π k) := fun γ k => rfl
  have hbar_mul : ∀ γ δ : MulAut ↥K, bar (γ * δ) = bar γ * bar δ := by
    intro γ δ
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rfl
  set β := bar α₀ with hβdef
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rw [← b3Lie_intertwine_pow π α₀ β (hbar α₀), hα₀p]
    rfl
  have hβ1 : β ≠ 1 := by
    intro h1
    apply haK
    have hα1 : α₀ = 1 := by
      refine mulAut_eq_one_of_forall_mem_center hK.1 α₀ fun k => hker ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbar, ← hβdef, h1, MulAut.one_apply,
        inv_mul_cancel]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg Subtype.val (congrArg (fun γ : MulAut ↥K => γ ⟨k, hk⟩) hα1)
    simp only [MulAut.one_apply] at this
    rw [hα₀] at this
    calc k * a = a * k * a⁻¹ * a := by rw [this]
      _ = a * k := by group
  have hpow : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hne : MulAut.congr e β ≠ 1 := fun h1 =>
    hβ1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  have hsh : CompShape T β := CompShape.of_congr hT e (hS _ hpow hne)
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
  have hJβ : GLAPComponent p (fixSubgroup β) (J₁.map π) :=
    glaPComponent_map_fixSubgroup π hker α₀ β (hbar α₀) hπ hp hJ₁
  have hlay : J₁.map π ≤ GLALayer (fixSubgroup β) :=
    hsh.layer _ hJβ.1 (glaPComponent_perfect hJβ)
  have hJc : IsComponentOf (J₁.map π) (fixSubgroup β) :=
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
  refine ⟨⟨hJ.1, hJ.2.1, CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂
    hQ1'⟩, ?_, fun g hg hga => ?_⟩
  ·
    obtain ⟨e₃⟩ := LieComp.nonempty_centralQuotient_mulEquiv hQ1'.1 (π.subgroupMap J₁)
      (MonoidHom.subgroupMap_surjective π J₁) hcov
    exact hT _ _ (e₃.symm.trans (centerQuotientCongr e₂)) (hsh.type _ hJc)
  ·
    let γ₀ : MulAut ↥K := K.normalizerMonoidHom ⟨g, hg⟩
    have hγα : γ₀ * α₀ = α₀ * γ₀ := normalizerMonoidHom_commute hg ha hga
    have hγβ : bar γ₀ * β = β * bar γ₀ := by rw [hβdef, ← hbar_mul, hγα, hbar_mul]
    have h1 := hsh.norm (bar γ₀) hγβ _ hJc
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

end Lift

end CFSG.HardMathSupport.Dickson.Bal207
