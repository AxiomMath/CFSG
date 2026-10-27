module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

section Basic

variable {Y : Type*} [Group Y]

theorem i25_isComponentOf_gLBConj {L X : Subgroup Y} (hL : IsComponentOf L X) {g : Y}
    (hg : g ∈ Subgroup.normalizer (X : Set Y)) : IsComponentOf (GLBConj g L) X := by
  have hX : X.map (MulAut.conj g⁻¹).toMonoidHom = X := gLBConj_eq_of_mem_normalizer hg
  refine ⟨?_, ?_, ?_⟩
  · calc GLBConj g L ≤ GLBConj g X := gLBConj_mono g hL.1
      _ = X := gLBConj_eq_of_mem_normalizer hg
  · have := CFSG.Quasithin.A3.subnormal_map (MulAut.conj g⁻¹).toMonoidHom hL.2.1
    rwa [hX] at this
  · have hq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective) hq)

theorem i25_le_layer {K H : Subgroup Y} (hK : IsComponentOf K H) : K ≤ GLALayer H :=
  le_sSup hK

theorem i25_layer_le (H : Subgroup Y) : GLALayer H ≤ H :=
  sSup_le fun _ hK => hK.1

theorem i25_commutator_eq {K : Subgroup Y} (hK : CFSG.Open.IsQuasisimple ↥K) : ⁅K, K⁆ = K := by
  have h := congrArg (Subgroup.map K.subtype) hK.1
  rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h

theorem i25_noncommProd_equiv {ι M : Type*} [Fintype ι] [Monoid M] (σ : ι ≃ ι) (f : ι → M)
    (h₁ h₂) : (Finset.univ : Finset ι).noncommProd (fun i => f (σ i)) h₁ =
      (Finset.univ : Finset ι).noncommProd f h₂ := by
  have hσ : (Finset.univ : Finset ι).val.map σ = (Finset.univ : Finset ι).val := by
    simp
  unfold Finset.noncommProd
  congr 1
  calc (Finset.univ : Finset ι).val.map (fun i => f (σ i))
      = ((Finset.univ : Finset ι).val.map σ).map f := by rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset ι).val.map f := by rw [hσ]

theorem i25_commutatorElement_mul_mul {a b z₁ z₂ : Y} (h1b : Commute z₁ b) (h12 : Commute z₁ z₂)
    (h2a : Commute z₂ a) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have e1 : z₁ * (b * z₂) = b * z₂ * z₁ := (h1b.mul_right h12).eq
  have e2 : z₂ * a⁻¹ = a⁻¹ * z₂ := h2a.inv_right.eq
  calc a * z₁ * (b * z₂) * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹)
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by rw [e1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [e2]; group

end Basic

section Main

variable {Y : Type*} [Group Y]

theorem i25_gLBConj_ne {X E X₁ : Subgroup Y}
    (hfr : ∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup Y, IsComponentOf L X → GLBConj e L ≠ L)
    (hX₁ : IsComponentOf X₁ X) {e f : Y} (he : e ∈ E) (hf : f ∈ E) (hne : e ≠ f) :
    GLBConj e X₁ ≠ GLBConj f X₁ := by
  intro h
  have h' := congrArg (GLBConj f⁻¹) h
  rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h'
  exact hfr (e * f⁻¹) (E.mul_mem he (E.inv_mem hf)) (fun h1 => hne (mul_inv_eq_one.mp h1)) X₁
    hX₁ h'

theorem i25_commute_conj [Finite Y] {X E X₁ : Subgroup Y}
    (hEN : E ≤ Subgroup.normalizer (X : Set Y))
    (hfr : ∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup Y, IsComponentOf L X → GLBConj e L ≠ L)
    (hX₁ : IsComponentOf X₁ X) {e f : Y} (he : e ∈ E) (hf : f ∈ E) (hne : e ≠ f) {x y : Y}
    (hx : x ∈ X₁) (hy : y ∈ X₁) : Commute (e⁻¹ * x * e) (f⁻¹ * y * f) := by
  have hxe : e⁻¹ * x * e ∈ GLBConj e X₁ := mem_gLBConj.2 (by simpa [mul_assoc] using hx)
  have hyf : f⁻¹ * y * f ∈ GLBConj f X₁ := mem_gLBConj.2 (by simpa [mul_assoc] using hy)
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute
      (i25_isComponentOf_gLBConj hX₁ (hEN he)) (i25_isComponentOf_gLBConj hX₁ (hEN hf)) with h | h
  · exact absurd h (i25_gLBConj_ne hfr hX₁ he hf hne)
  · exact h _ hxe _ hyf

theorem i25_exists_diag [Finite Y] {X E X₁ : Subgroup Y} (hEN : E ≤ Subgroup.normalizer (X : Set Y))
    (hfr : ∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup Y, IsComponentOf L X → GLBConj e L ≠ L)
    (hX₁ : IsComponentOf X₁ X) :
    ∃ d : ↥X₁ →* Y, ∀ x : ↥X₁, d x ∈ X ∧ d x ∈ Subgroup.centralizer (E : Set Y) ∧
      (x : Y)⁻¹ * d x ∈ Subgroup.centralizer (X₁ : Set Y) := by
  classical
  have : Fintype ↥E := Fintype.ofFinite _
  let φ : ↥E → (↥X₁ →* Y) := fun e => (MulAut.conj ((e : Y)⁻¹)).toMonoidHom.comp X₁.subtype
  have hφ : ∀ (e : ↥E) (x : ↥X₁), φ e x = (e : Y)⁻¹ * x * e := fun e x => by
    simp [φ]
  have hcomm : Pairwise fun e f : ↥E => ∀ x y : ↥X₁, Commute (φ e x) (φ f y) := by
    intro e f hef x y
    rw [hφ, hφ]
    exact i25_commute_conj hEN hfr hX₁ e.2 f.2 (fun h => hef (Subtype.ext h)) x.2 y.2
  have hcomm' : ∀ x : ↥X₁,
      (↑(Finset.univ : Finset ↥E) : Set ↥E).Pairwise (Function.onFun Commute fun e => φ e x) :=
    fun x e _ f _ h => hcomm h x x
  refine ⟨(MonoidHom.noncommPiCoprod φ hcomm).comp (Pi.constMonoidHom ↥E ↥X₁), fun x => ?_⟩
  have hd : ((MonoidHom.noncommPiCoprod φ hcomm).comp (Pi.constMonoidHom ↥E ↥X₁)) x =
      Finset.univ.noncommProd (fun e => φ e x) (hcomm' x) := by
    rw [MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_apply]
    rfl
  rw [hd]
  refine ⟨?_, ?_, ?_⟩
  · refine Subgroup.noncommProd_mem _ _ fun e _ => ?_
    rw [hφ]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hEN e.2)) (x : Y)).mp (hX₁.1 x.2)
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro f hf
    let σ : ↥E ≃ ↥E := Equiv.mulRight (⟨f, hf⟩ : ↥E)⁻¹
    have hfun : ∀ e : ↥E, MulAut.conj f (φ e x) = φ (σ e) x := by
      intro e
      simp [hφ, σ, MulAut.conj_apply, mul_assoc]
    have key : MulAut.conj f (Finset.univ.noncommProd (fun e => φ e x) (hcomm' x)) =
        Finset.univ.noncommProd (fun e => φ e x) (hcomm' x) :=
      ((Finset.map_noncommProd _ _ _ (MulAut.conj f)).trans
        (Finset.noncommProd_congr rfl (fun e _ => hfun e) _)).trans
        (i25_noncommProd_equiv σ (fun e => φ e x) _ _)
    rw [MulAut.conj_apply] at key
    set P := Finset.univ.noncommProd (fun e => φ e x) (hcomm' x)
    calc f * P = f * P * f⁻¹ * f := by group
      _ = P * f := by rw [key]
  · rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ (1 : ↥E))]
    have h1 : φ 1 x = x := by simp [hφ]
    rw [h1, inv_mul_cancel_left]
    refine Subgroup.noncommProd_mem _ _ fun e he => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hne : e ≠ 1 := Finset.ne_of_mem_erase he
    have := hcomm hne x ⟨y, hy⟩
    rw [show φ 1 ⟨y, hy⟩ = y by simp [hφ]] at this
    exact this.eq.symm

theorem i25_exists_inv_mul_mem [Finite Y] {X X₁ : Subgroup Y} (hL : GLALayer X = X)
    (hX₁ : IsComponentOf X₁ X) {c : Y} (hc : c ∈ X) :
    ∃ x ∈ X₁, x⁻¹ * c ∈ Subgroup.centralizer (X₁ : Set Y) := by
  have hle : X ≤ X₁ ⊔ Subgroup.centralizer (X₁ : Set Y) := by
    calc X = GLALayer X := hL.symm
      _ ≤ X₁ ⊔ Subgroup.centralizer (X₁ : Set Y) := sSup_le fun L hLc => by
        rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hLc hX₁ with h | h
        · exact h ▸ le_sup_left
        · exact le_sup_of_le_right fun l hl =>
            Subgroup.mem_centralizer_iff.mpr fun y hy => (h l hl y hy).symm
  have hmem : c ∈ ((X₁ ⊔ Subgroup.centralizer (X₁ : Set Y) : Subgroup Y) : Set Y) := hle hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X₁ _
    (Subgroup.centralizer_le_normalizer _)] at hmem
  obtain ⟨x, hx, k, hk, rfl⟩ := hmem
  exact ⟨x, hx, by simpa using hk⟩

theorem i25_mem_center {X E X₁ : Subgroup Y} (hL : GLALayer X = X)
    (htr : ∀ L L' : Subgroup Y, IsComponentOf L X → IsComponentOf L' X →
      ∃ e ∈ E, GLBConj e L = L')
    (hX₁ : IsComponentOf X₁ X) {w : Y} (hwX : w ∈ X)
    (hwE : w ∈ Subgroup.centralizer (E : Set Y)) (hw1 : w ∈ Subgroup.centralizer (X₁ : Set Y)) :
    w ∈ (Subgroup.center ↥X).map X.subtype := by
  have hcomp : ∀ L : Subgroup Y, IsComponentOf L X → L ≤ Subgroup.centralizer ({w} : Set Y) := by
    intro L hLc l hl
    obtain ⟨f, hf, rfl⟩ := htr X₁ L hX₁ hLc
    have hy : f * l * f⁻¹ ∈ X₁ := mem_gLBConj.1 hl
    have h1 : Commute w f := (Subgroup.mem_centralizer_iff.mp hwE f hf).symm
    have h2 : Commute w (f * l * f⁻¹) := (Subgroup.mem_centralizer_iff.mp hw1 _ hy).symm
    have h3 : Commute w (f⁻¹ * (f * l * f⁻¹) * f) := (h1.inv_right.mul_right h2).mul_right h1
    rw [show f⁻¹ * (f * l * f⁻¹) * f = l by group] at h3
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact h3.eq
  have hXw : X ≤ Subgroup.centralizer ({w} : Set Y) := by
    calc X = GLALayer X := hL.symm
      _ ≤ _ := sSup_le hcomp
  refine Subgroup.mem_map.mpr ⟨⟨w, hwX⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp (hXw g.2) w rfl).symm

theorem i25_exists_mem_center [Finite Y] {X E X₁ : Subgroup Y} (hL : GLALayer X = X)
    (htr : ∀ L L' : Subgroup Y, IsComponentOf L X → IsComponentOf L' X →
      ∃ e ∈ E, GLBConj e L = L')
    (hX₁ : IsComponentOf X₁ X) {d : ↥X₁ →* Y}
    (hd : ∀ x : ↥X₁, d x ∈ X ∧ d x ∈ Subgroup.centralizer (E : Set Y) ∧
      (x : Y)⁻¹ * d x ∈ Subgroup.centralizer (X₁ : Set Y))
    {c : Y} (hc : c ∈ X ⊓ Subgroup.centralizer (E : Set Y)) :
    ∃ x : ↥X₁, (d x)⁻¹ * c ∈
      (Subgroup.center ↥X).map X.subtype ⊓ Subgroup.centralizer (E : Set Y) := by
  obtain ⟨x, hx, hk⟩ := i25_exists_inv_mul_mem hL hX₁ hc.1
  obtain ⟨hdX, hdE, hd1⟩ := hd ⟨x, hx⟩
  have hwE : (d ⟨x, hx⟩)⁻¹ * c ∈ Subgroup.centralizer (E : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hdE) hc.2
  refine ⟨⟨x, hx⟩, i25_mem_center hL htr hX₁ (X.mul_mem (X.inv_mem hdX) hc.1) hwE ?_, hwE⟩
  have : (d ⟨x, hx⟩)⁻¹ * c = (x⁻¹ * d ⟨x, hx⟩)⁻¹ * (x⁻¹ * c) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hd1) hk

theorem i25_ker_le_center {X₁ : Subgroup Y} {d : ↥X₁ →* Y}
    (hd : ∀ x : ↥X₁, (x : Y)⁻¹ * d x ∈ Subgroup.centralizer (X₁ : Set Y)) :
    d.ker ≤ Subgroup.center ↥X₁ := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h := hd x
  rw [hx, mul_one] at h
  have h' : (x : Y) ∈ Subgroup.centralizer (X₁ : Set Y) := by simpa using Subgroup.inv_mem _ h
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h' g g.2)

theorem i25_layer_eq_range [Finite Y] {X E X₁ : Subgroup Y} (hL : GLALayer X = X)
    (htr : ∀ L L' : Subgroup Y, IsComponentOf L X → IsComponentOf L' X →
      ∃ e ∈ E, GLBConj e L = L')
    (hX₁ : IsComponentOf X₁ X) {d : ↥X₁ →* Y}
    (hd : ∀ x : ↥X₁, d x ∈ X ∧ d x ∈ Subgroup.centralizer (E : Set Y) ∧
      (x : Y)⁻¹ * d x ∈ Subgroup.centralizer (X₁ : Set Y)) :
    GLALayer (X ⊓ Subgroup.centralizer (E : Set Y)) = d.range := by
  set C := X ⊓ Subgroup.centralizer (E : Set Y)
  have hdC : d.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(hd x).1, (hd x).2.1⟩
  have hdec : ∀ c ∈ C, ∃ x : ↥X₁, ∃ w ∈ (Subgroup.center ↥X).map X.subtype, c = d x * w := by
    intro c hc
    obtain ⟨x, hw⟩ := i25_exists_mem_center hL htr hX₁ hd hc
    exact ⟨x, _, hw.1, by group⟩
  have hcent : ∀ w ∈ (Subgroup.center ↥X).map X.subtype, ∀ g ∈ X, Commute w g := by
    rintro _ ⟨z, hz, rfl⟩ g hg
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)).symm
  have hcomm : ⁅C, C⁆ ≤ d.range := by
    rw [Subgroup.commutator_le]
    intro c₁ hc₁ c₂ hc₂
    obtain ⟨x₁, w₁, hw₁, rfl⟩ := hdec c₁ hc₁
    obtain ⟨x₂, w₂, hw₂, rfl⟩ := hdec c₂ hc₂
    rw [i25_commutatorElement_mul_mul (hcent w₁ hw₁ _ (hd x₂).1)
      (hcent w₁ hw₁ _ (Subgroup.map_subtype_le _ hw₂)) (hcent w₂ hw₂ _ (hd x₁).1)]
    exact ⟨⁅x₁, x₂⁆, map_commutatorElement d x₁ x₂⟩
  apply le_antisymm
  · refine sSup_le fun K hK => ?_
    calc K = ⁅K, K⁆ := (i25_commutator_eq hK.2.2).symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hK.1 hK.1
      _ ≤ d.range := hcomm
  · refine i25_le_layer ⟨hdC, ?_, ?_⟩
    · refine CFSG.Quasithin.A3.subnormal_of_normal hdC ?_
      rw [Subgroup.normal_subgroupOf_iff hdC]
      rintro _ c ⟨y, rfl⟩ hc
      obtain ⟨x, w, hw, rfl⟩ := hdec c hc
      refine ⟨x * y * x⁻¹, ?_⟩
      have h1 : Commute w (d y) := hcent w hw _ (hd y).1
      rw [map_mul, map_mul, map_inv]
      calc d x * d y * (d x)⁻¹ = d x * (w * d y) * w⁻¹ * (d x)⁻¹ := by rw [h1.eq]; group
        _ = d x * w * d y * (d x * w)⁻¹ := by group
    · have hq : CFSG.IsQuasisimple ↥X₁ := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hX₁.2.2
      refine CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
        (CFSG.LocalCores.isQuasisimple_of_surjective hq d.rangeRestrict
          d.rangeRestrict_surjective ?_)
      rw [MonoidHom.ker_rangeRestrict]
      exact i25_ker_le_center fun x => (hd x).2.2

end Main

theorem input2_5_proved : Input2_5 := by
  intro Y _ _ p _ X E hL hEN _ htr hfr
  refine ⟨fun X₁ hX₁ => ?_, ?_⟩
  · obtain ⟨d, hd⟩ := i25_exists_diag hEN hfr hX₁
    refine ⟨d.ker, inferInstance, i25_ker_le_center fun x => (hd x).2.2, ⟨?_⟩⟩
    exact (MulEquiv.subgroupCongr (i25_layer_eq_range hL htr hX₁ hd)).trans
      (QuotientGroup.quotientKerEquivRange d).symm
  · refine le_antisymm (fun c hc => ?_)
      (sup_le (i25_layer_le _) (inf_le_inf_right _ (Subgroup.map_subtype_le _)))
    by_cases hX : ∃ X₁ : Subgroup Y, IsComponentOf X₁ X
    · obtain ⟨X₁, hX₁⟩ := hX
      obtain ⟨d, hd⟩ := i25_exists_diag hEN hfr hX₁
      obtain ⟨x, hw⟩ := i25_exists_mem_center hL htr hX₁ hd hc
      have hdx : d x ∈ GLALayer (X ⊓ Subgroup.centralizer (E : Set Y)) := by
        rw [i25_layer_eq_range hL htr hX₁ hd]
        exact ⟨x, rfl⟩
      have := Subgroup.mul_mem_sup hdx hw
      rwa [mul_inv_cancel_left] at this
    · have hXbot : X = ⊥ := by
        rw [← hL]
        exact sSup_eq_bot.mpr fun K hK => absurd ⟨K, hK⟩ hX
      have hc1 : c = 1 := by
        have := hc.1
        rw [hXbot] at this
        exact Subgroup.mem_bot.mp this
      rw [hc1]
      exact Subgroup.one_mem _

end CFSG.HardMathSupport.Solomon.Coordinator
