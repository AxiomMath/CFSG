module

public import CFSG.GH74.GLS.Stage1.Main.BrBaseTransport
public import CFSG.GH74.GLS.Stage1.Main.BrModel
public import CFSG.GH74.GLS.Stage1.Main.BrRankE16

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Sigma

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem exists_sigma_fusion (hXC : K₁ ⊔ K₂ ⊔ S ≤ centralizer ({z} : Set G))
    (hWc : ∀ H : Subgroup ↥(barOf z (K₁ ⊔ K₂ ⊔ S)), IsComponent H →
      IsComponent (H.map (barOf z (K₁ ⊔ K₂ ⊔ S)).subtype))
    (hcomps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {imgBar z K₁, imgBar z K₂})
    (hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂) (hSp : IsPGroup 2 ↥S)
    (hS : ∀ s ∈ S, s ∈ Oz z → s = 1) {Gs : Type} [Group Gs] {E S' E₁ E₂ : Subgroup Gs}
    (hE : E = E₁ ⊔ E₂) (hcompat : Compat7 z (K₁ ⊔ K₂ ⊔ S) S E S')
    (hc₁ : IsComponent (E₁.subgroupOf (E ⊔ S'))) (hc₂ : IsComponent (E₂.subgroupOf (E ⊔ S')))
    (hne : E₁.subgroupOf (E ⊔ S') ≠ E₂.subgroupOf (E ⊔ S')) :
    ∃ σ : ↥S ≃* ↥S', (∀ s : ↥S, ((s : G) ∈ LC z ↔ ((σ s : ↥S') : Gs) ∈ E)) ∧
      ∀ s₁ s₂ : ↥S, orderOf (s₁ : G) = 2 → orderOf (s₂ : G) = 2 →
        (IsConj (s₁ : G) (s₂ : G) ↔ IsConj ((σ s₁ : ↥S') : Gs) ((σ s₂ : ↥S') : Gs)) := by
  obtain ⟨hN, ψ, hψS, hψS', hψf⟩ := hcompat
  set X : Subgroup G := K₁ ⊔ K₂ ⊔ S with hX
  have hSX : S ≤ X := le_sup_right
  let φ : ↥X →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hXC)
  have hker : φ.ker = (Oz z).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hatMk_eq_one_iff (Cz z) ⟨(x : G), hXC x.2⟩
  have hrange : φ.range = barOf z X := by
    show ((toBar z).comp (Subgroup.inclusion hXC)).range = (X.subgroupOf (Cen z)).map (toBar z)
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hWn : ∀ H : Subgroup ↥φ.range, IsComponent H → IsComponent (H.map φ.range.subtype) := by
    rw [hrange]; exact hWc
  let e : (↥X ⧸ (Oz z).subgroupOf X) ≃* ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  let Ψ : ↥φ.range ≃* ↥(E ⊔ S') := e.symm.trans ψ
  let g : ↥S →* ↥(E ⊔ S') :=
    ψ.toMonoidHom.comp ((QuotientGroup.mk' ((Oz z).subgroupOf X)).comp (Subgroup.inclusion hSX))
  have hgS : ∀ s : ↥S, (g s : Gs) ∈ S' := fun s => hψS ⟨(s : G), hSX s.2⟩ s.2
  let f : ↥S →* ↥S' :=
    { toFun := fun s => ⟨(g s : Gs), hgS s⟩
      map_one' := Subtype.ext (by
        show ((g 1 : ↥(E ⊔ S')) : Gs) = 1
        rw [map_one]
        rfl)
      map_mul' := fun x y => Subtype.ext (by
        show ((g (x * y) : ↥(E ⊔ S')) : Gs) = (g x : Gs) * (g y : Gs)
        rw [map_mul]
        rfl) }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g x = g y := Subtype.ext
      (show ((g x : ↥(E ⊔ S')) : Gs) = (g y : Gs) from congrArg (fun u : ↥S' => (u : Gs)) hxy)
    have h2 : (QuotientGroup.mk (Subgroup.inclusion hSX x) : ↥X ⧸ (Oz z).subgroupOf X) =
        QuotientGroup.mk (Subgroup.inclusion hSX y) := ψ.injective h1
    rw [QuotientGroup.eq] at h2
    have h3 : (x : G)⁻¹ * y ∈ Oz z := h2
    have h4 : (x : G)⁻¹ * y = 1 := hS _ (S.mul_mem (S.inv_mem x.2) y.2) h3
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : Gs) ∈ E ⊔ S' := Subgroup.mem_sup_right y.2
    obtain ⟨s, hsS, hs⟩ := hψS' (ψ.symm ⟨y, hy⟩) (by simp)
    refine ⟨⟨(s : G), hsS⟩, ?_⟩
    apply Subtype.ext
    show ((g ⟨(s : G), hsS⟩ : ↥(E ⊔ S')) : Gs) = y
    have : g ⟨(s : G), hsS⟩ = ⟨y, hy⟩ := by
      show ψ (QuotientGroup.mk (Subgroup.inclusion hSX ⟨(s : G), hsS⟩)) = _
      have e' : Subgroup.inclusion hSX ⟨(s : G), hsS⟩ = s := Subtype.ext rfl
      rw [e', hs]
      exact ψ.apply_symm_apply _
    rw [this]
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥S ≃* ↥S', ∀ s : ↥S, ((σ s : ↥S') : Gs) = (g s : Gs) :=
    ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun s => rfl⟩
  refine ⟨σ, fun s => ?_, fun s₁ s₂ h₁ h₂ => ?_⟩
  swap
  · have := hψf (Subgroup.inclusion hSX s₁) (Subgroup.inclusion hSX s₂) s₁.2 s₂.2 h₁ h₂
    rw [hσ, hσ]
    exact this
  have hsX : (s : G) ∈ X := hSX s.2
  have hsC : (s : G) ∈ centralizer ({z} : Set G) := hXC hsX
  set γ : ↥φ.range := e (QuotientGroup.mk ⟨(s : G), hsX⟩) with hγ
  have hγ' : (γ : CentralizerBar z) = toBar z ⟨(s : G), hsC⟩ := rfl
  have hΨγ : ((Ψ γ : ↥(E ⊔ S')) : Gs) = ((σ s : ↥S') : Gs) := by
    rw [hσ]
    show ((e.symm.trans ψ) (e (QuotientGroup.mk ⟨(s : G), hsX⟩)) : Gs) = (g s : Gs)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨k, hk⟩ := hSp ⟨(s : G), s.2⟩
  have hk' : (⟨(s : G), hsC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hLC : (s : G) ∈ LC z ↔ toBar z ⟨(s : G), hsC⟩ ∈ LBar z :=
    mem_LC_iff_of_pElt (z := z) ⟨(s : G), hsC⟩ hk'
  rw [hLC, hLB, ← hγ', mem_sup_iff_of_comps hWn hcomps Ψ hc₁ hc₂ hne γ]
  have h1 : E₁ ≤ E ⊔ S' := by
    rw [hE]
    exact le_sup_left.trans le_sup_left
  have h2 : E₂ ≤ E ⊔ S' := by
    rw [hE]
    exact le_sup_right.trans le_sup_left
  rw [← Subgroup.subgroupOf_sup h1 h2, ← hE, Subgroup.mem_subgroupOf, hΨγ]


end Sigma

section Data

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ} {w : G}

theorem term7_data' (hII : II4_4_4_center) (h41 : Prop4_1) (hT : Term7Out G z S q w) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (z' t' w' : Gs) (S' : Sylow 2 Gs)
      (E₁ E₂ : Subgroup Gs) (σ : ↥S ≃* ↥(S' : Subgroup Gs)),
      orderOf z' = 2 ∧ (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' ∧
      z' ∈ (S' : Subgroup Gs) ∧ (∀ x ∈ (S' : Subgroup Gs), x * z' = z' * x) ∧
      Dat410 q z' (S' : Subgroup Gs) t' w' E₁ E₂ ∧ (w' = 1 ↔ w = 1) ∧
      (∀ s : ↥S, ((s : G) ∈ LC z ↔ ((σ s : ↥(S' : Subgroup Gs)) : Gs) ∈ IVK.Ez z')) ∧
      (∀ s₁ s₂ : ↥S, orderOf (s₁ : G) = 2 → orderOf (s₂ : G) = 2 →
        (IsConj (s₁ : G) (s₂ : G) ↔
          IsConj ((σ s₁ : ↥(S' : Subgroup Gs)) : Gs) ((σ s₂ : ↥(S' : Subgroup Gs)) : Gs))) ∧
      (∀ hz : z ∈ S, ((σ ⟨z, hz⟩ : ↥(S' : Subgroup Gs)) : Gs) = z') := by
  obtain ⟨K₁, K₂, hs, hodd, h5, hK₁, hK₂, hT7⟩ := hT
  obtain ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, hz'o, hcenS', hz'S', hz'c, hC, hD, hww⟩ :=
    exists_term7_model hodd h5 hK₁ hT7
  have hM := m4_of_std hII hs
  have hXC : K₁ ⊔ K₂ ⊔ S ≤ centralizer ({z} : Set G) :=
    sup_le (sup_le hM.K₁_le hM.K₂_le) hs.sylow.le
  have hcomps := comps_of_std4 hII h41 hs
  have hLB := LBar_eq_imgBar hII h41 hs
  have hSp : IsPGroup 2 ↥S := hs.sylow.isPGroup
  have hSOz : ∀ s ∈ S, s ∈ Oz z → s = 1 := fun s hs' hz =>
    eq_one_of_mem_pgroup_oddCore hSp hs' hz
  obtain ⟨ht, hc₁, hc₂, hne, hu₁, hu₂⟩ :=
    model_swap_data h5 hz'o hz'c hD.Ez_eq hD.E₂_eq hD.sl2 hD.inter_E hD.comm_E hD.t_mem hD.t_ord
  obtain ⟨σ, hσL, hσf⟩ :=
    exists_sigma_fusion hXC (fun H hH => isComponent_map_barOf hII hs hH) hcomps hLB hSp hSOz hD.Ez_eq hC
      hc₁ hc₂ hne
  refine ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, σ, hz'o, hcenS', hz'S', hz'c, hD, hww, hσL, hσf,
    fun hz => ?_⟩
  have hsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'o, pow_two] at this
  have hcentral : ((σ ⟨z, hz⟩ : ↥(S' : Subgroup Gs)) : Gs) ∈
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype := by
    refine ⟨σ ⟨z, hz⟩, ?_, rfl⟩
    show σ ⟨z, hz⟩ ∈ center ↥(S' : Subgroup Gs)
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := σ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hs.sylow.le s.2)
  rw [hcenS'] at hcentral
  rcases eq_one_or_eq_of_mem_zpowers_sq hsq hcentral with h | h
  · exfalso
    have h1 : σ ⟨z, hz⟩ = 1 := Subtype.ext h
    have h2 : (⟨z, hz⟩ : ↥S) = 1 := σ.injective (by rw [h1, map_one])
    have h3 : z = 1 := congrArg Subtype.val h2
    have := hs.orderOf_z
    rw [h3, orderOf_one] at this
    omega
  · exact h

theorem nonfused_of_term7 (hII : II4_4_4_center) (h41 : Prop4_1) (hT : Term7Out G z S q w) :
    ∀ u ∈ Pz S z, IsConj z u → u = z := by
  have hT' := hT
  obtain ⟨K₁, K₂, hs, hodd, h5, hK₁, hK₂, hT7⟩ := hT'
  obtain ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, σ, hz'o, hcenS', hz'S', hz'c, hD, hww, hσL, hσf,
    hσz⟩ := term7_data' hII h41 hT
  have hM := m4_of_std hII hs
  intro u hu hconj
  have huS : u ∈ S := hu.1
  have huK : u ∈ K₁ ⊔ K₂ := by
    have := hu.2
    rwa [hs.rigidProduct_eq] at this
  have hzS : z ∈ S := hM.z_mem_S
  have hu2 : orderOf u = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have := SemiconjBy.orderOf_eq c (x := z) (y := u) (by
      show c * z = u * c
      rw [← hc]
      group)
    rw [← this]
    exact hs.orderOf_z
  have huC : u ∈ centralizer ({z} : Set G) := hs.sylow.le huS
  have hLu : u ∈ LC z := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (⟨u, huC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have : u ^ 2 = 1 := by
        have := pow_orderOf_eq_one u
        rwa [hu2] at this
      simpa using this
    have hLC : u ∈ LC z ↔ toBar z ⟨u, huC⟩ ∈ LBar z :=
      mem_LC_iff_of_pElt (z := z) ⟨u, huC⟩ hk
    rw [hLC, LBar_eq_imgBar hII h41 hs, ← map_K12 hII hs]
    exact ⟨⟨u, huC⟩, huK, rfl⟩
  have hyE : ((σ ⟨u, huS⟩ : ↥(S' : Subgroup Gs)) : Gs) ∈ IVK.Ez z' := (hσL ⟨u, huS⟩).1 hLu
  have hy2 : orderOf ((σ ⟨u, huS⟩ : ↥(S' : Subgroup Gs)) : Gs) = 2 := by
    have h1 : orderOf (σ ⟨u, huS⟩) = orderOf (⟨u, huS⟩ : ↥S) := MulEquiv.orderOf_eq σ _
    rw [Subgroup.orderOf_coe, h1, Subgroup.orderOf_mk]
    exact hu2
  have hzo : orderOf (z : G) = 2 := hs.orderOf_z
  have hfus := (hσf ⟨z, hzS⟩ ⟨u, huS⟩ hzo hu2).1 hconj
  rw [hσz hzS] at hfus
  by_cases hyz : ((σ ⟨u, huS⟩ : ↥(S' : Subgroup Gs)) : Gs) = z'
  · have : σ ⟨u, huS⟩ = σ ⟨z, hzS⟩ := by
      apply Subtype.ext
      rw [hyz, hσz hzS]
    have h2 : (⟨u, huS⟩ : ↥S) = ⟨z, hzS⟩ := σ.injective this
    exact congrArg Subtype.val h2
  · exfalso
    have h3 := hD.E_fus _ hyE hy2 hyz
    exact hD.tz_ne (hfus.trans h3.symm)

end Data

end CFSG.GH74.GLS.Stage1.Main
