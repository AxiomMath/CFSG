module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Normalizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainOdd

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.Quasithin (perfectCore)

section Central

variable {M : Type*} [Group M]

theorem commutatorElement_commute_of_mul_inv_mem_center {x y τ : M}
    (hx : x * τ * x⁻¹ * τ⁻¹ ∈ center M) (hy : y * τ * y⁻¹ * τ⁻¹ ∈ center M) :
    x * y * x⁻¹ * y⁻¹ * τ = τ * (x * y * x⁻¹ * y⁻¹) := by
  set a := x * τ * x⁻¹ * τ⁻¹ with ha
  set b := y * τ * y⁻¹ * τ⁻¹ with hb
  have hxτ : x * τ * x⁻¹ = a * τ := by rw [ha]; group
  have hyτ : y * τ * y⁻¹ = b * τ := by rw [hb]; group
  have hxτ' : x⁻¹ * τ * x = a⁻¹ * τ := by
    have h1 : τ = x⁻¹ * (a * τ) * x := by rw [← hxτ]; group
    have hcomm : x⁻¹ * a = a * x⁻¹ := (mem_center_iff.1 hx x⁻¹)
    calc x⁻¹ * τ * x = x⁻¹ * (a⁻¹ * (a * τ)) * x := by group
      _ = a⁻¹ * (x⁻¹ * (a * τ) * x) := by
          have : x⁻¹ * a⁻¹ = a⁻¹ * x⁻¹ := (mem_center_iff.1 (inv_mem hx) x⁻¹)
          calc x⁻¹ * (a⁻¹ * (a * τ)) * x = (x⁻¹ * a⁻¹) * (a * τ) * x := by group
            _ = (a⁻¹ * x⁻¹) * (a * τ) * x := by rw [this]
            _ = a⁻¹ * (x⁻¹ * (a * τ) * x) := by group
      _ = a⁻¹ * τ := by rw [← h1]
  have hyτ' : y⁻¹ * τ * y = b⁻¹ * τ := by
    have h1 : τ = y⁻¹ * (b * τ) * y := by rw [← hyτ]; group
    have : y⁻¹ * b⁻¹ = b⁻¹ * y⁻¹ := (mem_center_iff.1 (inv_mem hy) y⁻¹)
    calc y⁻¹ * τ * y = (y⁻¹ * b⁻¹) * (b * τ) * y := by group
      _ = (b⁻¹ * y⁻¹) * (b * τ) * y := by rw [this]
      _ = b⁻¹ * (y⁻¹ * (b * τ) * y) := by group
      _ = b⁻¹ * τ := by rw [← h1]
  have ca : ∀ z : M, a * z = z * a := fun z => (mem_center_iff.1 hx z).symm
  have cb : ∀ z : M, b * z = z * b := fun z => (mem_center_iff.1 hy z).symm
  have key : x * y * x⁻¹ * y⁻¹ * τ * (x * y * x⁻¹ * y⁻¹)⁻¹ = τ := by
    calc x * y * x⁻¹ * y⁻¹ * τ * (x * y * x⁻¹ * y⁻¹)⁻¹
        = x * y * x⁻¹ * (y⁻¹ * τ * y) * x * y⁻¹ * x⁻¹ := by group
      _ = x * y * x⁻¹ * (b⁻¹ * τ) * x * y⁻¹ * x⁻¹ := by rw [hyτ']
      _ = x * y * (x⁻¹ * b⁻¹ * x) * (x⁻¹ * τ * x) * y⁻¹ * x⁻¹ := by group
      _ = x * y * b⁻¹ * (a⁻¹ * τ) * y⁻¹ * x⁻¹ := by
          rw [hxτ']
          have : x⁻¹ * b⁻¹ * x = b⁻¹ := by
            have hc := (mem_center_iff.1 (inv_mem hy) x)
            calc x⁻¹ * b⁻¹ * x = x⁻¹ * (b⁻¹ * x) := by group
              _ = x⁻¹ * (x * b⁻¹) := by rw [hc]
              _ = b⁻¹ := by group
          rw [this]
      _ = b⁻¹ * a⁻¹ * (x * (y * τ * y⁻¹) * x⁻¹) := by
          have h1 : y * b⁻¹ = b⁻¹ * y := (mem_center_iff.1 (inv_mem hy) y)
          have h2 : x * b⁻¹ = b⁻¹ * x := (mem_center_iff.1 (inv_mem hy) x)
          have h3 : y * a⁻¹ = a⁻¹ * y := (mem_center_iff.1 (inv_mem hx) y)
          have h4 : x * a⁻¹ = a⁻¹ * x := (mem_center_iff.1 (inv_mem hx) x)
          calc x * y * b⁻¹ * (a⁻¹ * τ) * y⁻¹ * x⁻¹
              = x * (y * b⁻¹) * a⁻¹ * τ * y⁻¹ * x⁻¹ := by group
            _ = x * (b⁻¹ * y) * a⁻¹ * τ * y⁻¹ * x⁻¹ := by rw [h1]
            _ = (x * b⁻¹) * (y * a⁻¹) * τ * y⁻¹ * x⁻¹ := by group
            _ = (b⁻¹ * x) * (a⁻¹ * y) * τ * y⁻¹ * x⁻¹ := by rw [h2, h3]
            _ = b⁻¹ * (x * a⁻¹) * y * τ * y⁻¹ * x⁻¹ := by group
            _ = b⁻¹ * (a⁻¹ * x) * y * τ * y⁻¹ * x⁻¹ := by rw [h4]
            _ = b⁻¹ * a⁻¹ * (x * (y * τ * y⁻¹) * x⁻¹) := by group
      _ = b⁻¹ * a⁻¹ * (x * (b * τ) * x⁻¹) := by rw [hyτ]
      _ = b⁻¹ * a⁻¹ * (b * (x * τ * x⁻¹)) := by
          have h5 : x * b = b * x := (mem_center_iff.1 hy x)
          calc b⁻¹ * a⁻¹ * (x * (b * τ) * x⁻¹) = b⁻¹ * a⁻¹ * ((x * b) * τ * x⁻¹) := by group
            _ = b⁻¹ * a⁻¹ * ((b * x) * τ * x⁻¹) := by rw [h5]
            _ = b⁻¹ * a⁻¹ * (b * (x * τ * x⁻¹)) := by group
      _ = b⁻¹ * a⁻¹ * (b * (a * τ)) := by rw [hxτ]
      _ = τ := by
          calc b⁻¹ * a⁻¹ * (b * (a * τ)) = b⁻¹ * (a⁻¹ * b) * a * τ := by group
            _ = b⁻¹ * (b * a⁻¹) * a * τ := by rw [← cb a⁻¹]
            _ = τ := by group
  calc x * y * x⁻¹ * y⁻¹ * τ =
        x * y * x⁻¹ * y⁻¹ * τ * (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    _ = τ * (x * y * x⁻¹ * y⁻¹) := by rw [key]

variable [Finite M]

theorem map_perfectCore_centralizer_mk (X₀ : Subgroup M) :
    (perfectCore (centralizer (X₀ : Set M))).map (QuotientGroup.mk' (center M)) =
      perfectCore (centralizer ((X₀.map (QuotientGroup.mk' (center M)) :
        Subgroup (M ⧸ center M)) : Set (M ⧸ center M))) := by
  set π := QuotientGroup.mk' (center M) with hπ
  set P : Subgroup M := (centralizer ((X₀.map π : Subgroup (M ⧸ center M)) :
    Set (M ⧸ center M))).comap π with hP
  have hPmap : P.map π = centralizer ((X₀.map π : Subgroup (M ⧸ center M)) :
      Set (M ⧸ center M)) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hle : centralizer (X₀ : Set M) ≤ P := by
    intro x hx
    rw [hP, mem_comap, mem_centralizer_iff]
    rintro _ ⟨τ, hτ, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hx τ hτ]
  have hmemZ : ∀ x ∈ P, ∀ τ ∈ X₀, x * τ * x⁻¹ * τ⁻¹ ∈ center M := by
    intro x hx τ hτ
    have h1 : π τ * π x = π x * π τ := mem_centralizer_iff.1 (mem_comap.1 hx) (π τ) ⟨τ, hτ, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    have h2 : (τ * x)⁻¹ * (x * τ) ∈ center M := QuotientGroup.eq.1 h1
    have h3 : x * τ * x⁻¹ * τ⁻¹ = (x * τ) * ((τ * x)⁻¹ * (x * τ)) * (x * τ)⁻¹ := by group
    rw [h3]
    exact (inferInstance : (center M).Normal).conj_mem _ h2 _
  have hcomm : ⁅P, P⁆ ≤ centralizer (X₀ : Set M) := by
    rw [commutator_le]
    intro x hx y hy
    rw [mem_centralizer_iff]
    intro τ hτ
    rw [commutatorElement_def]
    exact (commutatorElement_commute_of_mul_inv_mem_center (hmemZ x hx τ hτ)
      (hmemZ y hy τ hτ)).symm
  have hPP : perfectCore P = perfectCore (centralizer (X₀ : Set M)) := by
    apply le_antisymm
    · refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ (CFSG.Quasithin.perfectCore_perfect P)
      calc perfectCore P = ⁅perfectCore P, perfectCore P⁆ :=
            (CFSG.Quasithin.perfectCore_perfect P).symm
        _ ≤ ⁅P, P⁆ := commutator_mono (CFSG.Quasithin.perfectCore_le P)
            (CFSG.Quasithin.perfectCore_le P)
        _ ≤ centralizer (X₀ : Set M) := hcomm
    · exact CFSG.Quasithin.perfectCore_mono hle
  rw [← hPP, CFSG.Quasithin.map_perfectCore, hPmap]

omit [Finite M] in
theorem eq_top_of_sup_center_eq_top_of_perfect' [Group.IsPerfect M] {S : Subgroup M}
    (h : S ⊔ center M = ⊤) : S = ⊤ := by
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := M), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  have key : a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' b]
      _ = a * b * (c * d * c⁻¹) * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * b * (d * c * c⁻¹) * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' d]
      _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hd' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [commutatorElement_def, key]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

end Central

section Torus


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem map_graphAutF4_pow_leviTorus_subgroupOf (m : ℕ) (J : Finset (Fin (Tag.rank .F4))) :
    ((leviTorus K J).subgroupOf (adjointGroup .F4 K)).map (graphAutF4 K ^ m).toMonoidHom =
      (leviTorus K (nodePermPow m J)).subgroupOf (adjointGroup .F4 K) := by
  have : Finite (ModGL .F4 K) := finite_modGL
  have hle : ∀ J : Finset (Fin (Tag.rank .F4)),
      ((leviTorus K J).subgroupOf (adjointGroup .F4 K)).map (graphAutF4 K ^ m).toMonoidHom ≤
        (leviTorus K (nodePermPow m J)).subgroupOf (adjointGroup .F4 K) := by
    intro J
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.2 (finiteExceptionalAut_pow_mem_leviTorus m (mem_subgroupOf.1 hx))
  refine Subgroup.eq_of_le_of_card_ge (hle J) ?_
  have h2 := Subgroup.card_le_of_le (hle (nodePermPow m J))
  rw [nodePermPow_nodePermPow, Subgroup.card_map_of_injective (graphAutF4 K ^ m).injective] at h2
  rw [Subgroup.card_map_of_injective (graphAutF4 K ^ m).injective]
  exact h2

end Torus

section Transfer


theorem mem_normalizer_of_quotAut_map_eq {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .F4 K) {g : G}
    (hgL : L.map (MulAut.conj g⁻¹).toMonoidHom ≤ pieceSpan e)
    (ψ : MulAut (pieceSpan e ⧸ center (pieceSpan e)))
    (hψ : ((L.subgroupOf (pieceSpan e)).map (QuotientGroup.mk' (center (pieceSpan e)))).map
        ψ.toMonoidHom =
      ((L.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf (pieceSpan e)).map
        (QuotientGroup.mk' (center (pieceSpan e)))) :
    g ∈ normalizer (pieceSpan e : Set G) := by
  have : Finite K := finite_of_natCard_eq_two_pow hK
  have : CharP K ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hK
  have : Finite (ModGL .F4 K) := finite_modGL
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hLG₀ : L ≤ (pieceSpan e) := le_pieceSpan hq e
  set π := QuotientGroup.mk' (center (pieceSpan e)) with hπ
  set Ls := L.map (MulAut.conj g⁻¹).toMonoidHom with hLs
  set ι₀ : adjointGroup .F4 K →* (pieceSpan e) := (Subgroup.inclusion hLG₀).comp e.symm.toMonoidHom with hι₀
  set cg : L ≃* Ls := L.equivMapOfInjective _ (MulAut.conj g⁻¹).injective with hcg
  set ιs : adjointGroup .F4 K →* (pieceSpan e) :=
    (Subgroup.inclusion hgL).comp (cg.toMonoidHom.comp e.symm.toMonoidHom) with hιs
  have hι₀_apply : ∀ x, ((ι₀ x : (pieceSpan e)) : G) = ((e.symm x : L) : G) := fun x => rfl
  have hιs_apply : ∀ x, ((ιs x : (pieceSpan e)) : G) = g⁻¹ * ((e.symm x : L) : G) * g := by
    intro x
    change (MulAut.conj g⁻¹) ((e.symm x : L) : G) = _
    simp only [MulAut.conj_apply, inv_inv]
  have hcenL : ∀ x : adjointGroup .F4 K, (e.symm x : L) ∈ center L → x = 1 := by
    intro x hx
    have h1 : e (e.symm x) ∈ center (adjointGroup .F4 K) := (MulEquivClass.apply_mem_center_iff e).2 hx
    rwa [MulEquiv.apply_symm_apply, center_adjointGroup_eq_bot, mem_bot] at h1
  have hπ1 : ∀ z : (pieceSpan e), π z = 1 → ∀ w : (pieceSpan e), (w : G) * z = z * w := by
    intro z hz w
    have hzc : z ∈ center (pieceSpan e) := (QuotientGroup.eq_one_iff z).1 hz
    exact congrArg Subtype.val ((mem_center_iff.1 hzc) w)
  set α' : adjointGroup .F4 K →* (pieceSpan e) ⧸ center (pieceSpan e) := ψ.toMonoidHom.comp (π.comp ι₀) with hα'
  set β' : adjointGroup .F4 K →* (pieceSpan e) ⧸ center (pieceSpan e) := π.comp ιs with hβ'
  have hα'inj : Function.Injective α' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hα', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff] at hx
    refine (Subgroup.mem_bot).2 (hcenL x (mem_center_iff.2 fun l => Subtype.ext ?_))
    exact hπ1 (ι₀ x) hx (Subgroup.inclusion hLG₀ l)
  have hβ'inj : Function.Injective β' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    refine (Subgroup.mem_bot).2 (hcenL x (mem_center_iff.2 fun l => Subtype.ext ?_))
    have h1 := hπ1 (ιs x) hx (Subgroup.inclusion hgL (cg l))
    rw [Subgroup.coe_inclusion, hιs_apply] at h1
    change (MulAut.conj g⁻¹) (l : G) * _ = _ * (MulAut.conj g⁻¹) (l : G) at h1
    simp only [MulAut.conj_apply, inv_inv] at h1
    change (l : G) * ((e.symm x : L) : G) = ((e.symm x : L) : G) * l
    calc (l : G) * ((e.symm x : L) : G) =
          g * ((g⁻¹ * l * g) * (g⁻¹ * ((e.symm x : L) : G) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * ((e.symm x : L) : G) * g) * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = ((e.symm x : L) : G) * l := by group
  have hι₀range : ι₀.range = L.subgroupOf (pieceSpan e) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_subgroupOf.2 (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, mem_subgroupOf.1 hx⟩, Subtype.ext (by rw [hι₀_apply, e.symm_apply_apply])⟩
  have hιsrange : ιs.range = Ls.subgroupOf (pieceSpan e) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_subgroupOf.2 (cg (e.symm y)).2
    · intro hx
      obtain ⟨l, hl, hlx⟩ := mem_subgroupOf.1 hx
      refine ⟨e ⟨l, hl⟩, Subtype.ext ?_⟩
      rw [hιs_apply, e.symm_apply_apply, ← hlx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hrange : α'.range = β'.range := by
    have h1 : α'.range = ((π.comp ι₀).range).map ψ.toMonoidHom := MonoidHom.range_comp _ _
    have h2 : (π.comp ι₀).range = ι₀.range.map π := MonoidHom.range_comp _ _
    have h3 : β'.range = ιs.range.map π := MonoidHom.range_comp _ _
    rw [h1, h2, h3, hι₀range, hιsrange]
    exact hψ
  set Θ : MulAut (adjointGroup .F4 K) := (MonoidHom.ofInjective hα'inj).trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hβ'inj).symm) with hΘdef
  have hΘ : ∀ x, β' (Θ x) = α' x := by
    intro x
    rw [hΘdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
    rfl
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form (by omega) K hK
  obtain ⟨⟨c₀, m⟩, hcm, -⟩ := hnf Θ
  set c : adjointGroup .F4 K := c₀ with hc
  have hΘe : Θ = MulAut.conj c * graphAutF4 K ^ (m : ℕ) := hcm
  have hΘT : ∀ J : Finset (Fin (Tag.rank .F4)),
      ((leviTorus K J).subgroupOf (adjointGroup .F4 K)).map Θ.toMonoidHom =
        ((leviTorus K (nodePermPow m J)).subgroupOf (adjointGroup .F4 K)).map
          (MulAut.conj c).toMonoidHom := by
    intro J
    rw [← map_graphAutF4_pow_leviTorus_subgroupOf m J, Subgroup.map_map]
    congr 1
    ext x
    rw [hΘe]
    rfl
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have htop : (⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      (pieceCore e J.1).subgroupOf (pieceSpan e)) = ⊤ := by
    apply Subgroup.map_injective (pieceSpan e).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    refine le_antisymm (iSup_le fun J => (subgroupOf_map_subtype _ _).trans_le inf_le_right) ?_
    refine iSup_le fun J => ?_
    have h1 : pieceCore e J.1 ≤ (pieceSpan e) :=
      le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1) J
    refine le_trans ?_ (le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} =>
      ((pieceCore e J.1).subgroupOf (pieceSpan e)).map (pieceSpan e).subtype) J)
    rw [subgroupOf_map_subtype, inf_of_le_left h1]
  set Y₀ : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} → Subgroup ((pieceSpan e) ⧸ center (pieceSpan e)) :=
    fun J => ((leviTorus K J.1).subgroupOf (adjointGroup .F4 K)).map (π.comp ι₀) with hY₀
  have hgen₀ : (⊤ : Subgroup ((pieceSpan e) ⧸ center (pieceSpan e))) ≤
      ⨆ J, perfectCore (centralizer (Y₀ J : Set ((pieceSpan e) ⧸ center (pieceSpan e)))) := by
    rw [← Subgroup.map_top_of_surjective π hπs, ← htop, Subgroup.map_iSup]
    refine iSup_mono fun J => ?_
    have h1 : pieceCore e J.1 ≤ (pieceSpan e) :=
      le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1) J
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hyT : ((ι₀ y : (pieceSpan e)) : G) ∈ modelToG e (leviTorus K J.1) :=
        (mem_modelToG e).2 ⟨y, mem_subgroupOf.1 hy, rfl⟩
      have hxc := mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer _ (mem_subgroupOf.1 hx))
        _ hyT
      have : ι₀ y * x = x * ι₀ y := Subtype.ext hxc
      simp only [MonoidHom.comp_apply]
      rw [← map_mul, ← map_mul, this]
    · have hperf : ⁅pieceCore e J.1, pieceCore e J.1⁆ = pieceCore e J.1 :=
        commutator_centralizerPerfectCore _
      rw [← map_commutator, commutator_subgroupOf_eq h1, hperf]
  set X : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} → Subgroup (pieceSpan e) :=
    fun J => (((leviTorus K (nodePermPow m J.1)).subgroupOf (adjointGroup .F4 K)).map
      (MulAut.conj c).toMonoidHom).map ιs with hX
  have hYX : ∀ J, (Y₀ J).map ψ.toMonoidHom = (X J).map π := by
    intro J
    have hcomp : ψ.toMonoidHom.comp (π.comp ι₀) = β'.comp Θ.toMonoidHom :=
      MonoidHom.ext fun x => (hΘ x).symm
    change (((leviTorus K J.1).subgroupOf (adjointGroup .F4 K)).map (π.comp ι₀)).map
      ψ.toMonoidHom = ((((leviTorus K (nodePermPow m J.1)).subgroupOf (adjointGroup .F4 K)).map
        (MulAut.conj c).toMonoidHom).map ιs).map π
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hΘT J.1, Subgroup.map_map,
      Subgroup.map_map, Subgroup.map_map]
  have hgenM : (⊤ : Subgroup (pieceSpan e ⧸ center (pieceSpan e))) ≤
      ⨆ J, (perfectCore (centralizer (X J : Set (pieceSpan e)))).map π := by
    calc (⊤ : Subgroup (pieceSpan e ⧸ center (pieceSpan e))) =
          (⊤ : Subgroup (pieceSpan e ⧸ center (pieceSpan e))).map ψ.toMonoidHom :=
            (Subgroup.map_top_of_surjective _ ψ.surjective).symm
      _ ≤ (⨆ J, perfectCore (centralizer (Y₀ J : Set (pieceSpan e ⧸ center (pieceSpan e))))).map
            ψ.toMonoidHom := Subgroup.map_mono hgen₀
      _ = ⨆ J, (perfectCore (centralizer (Y₀ J : Set (pieceSpan e ⧸ center (pieceSpan e))))).map
            ψ.toMonoidHom := Subgroup.map_iSup _ _
      _ = ⨆ J, (perfectCore (centralizer (X J : Set (pieceSpan e)))).map π := by
          refine iSup_congr fun J => ?_
          rw [← centralizerPerfectCore_def, map_centralizerPerfectCore, hYX,
            centralizerPerfectCore_def, hπ, map_perfectCore_centralizer_mk]
  set H : Subgroup (pieceSpan e) := ⨆ J, perfectCore (centralizer (X J : Set (pieceSpan e)))
    with hH
  have hHtop : H = ⊤ := by
    have hmap : H.map π = ⊤ := by
      rw [eq_top_iff, hH, Subgroup.map_iSup]
      exact hgenM
    have hsup : H ⊔ center (pieceSpan e) = ⊤ := by
      have h1 := Subgroup.comap_map_eq π H
      rw [hmap, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have : Group.IsPerfect (pieceSpan e) := isPerfect_pieceSpan e
    exact eq_top_of_sup_center_eq_top_of_perfect' hsup
  set a : G := ((e.symm c : L) : G) with ha
  set y : G := g⁻¹ * a with hy
  have hXY : ∀ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      (modelToG e (leviTorus K (nodePermPow m J.1))).map (MulAut.conj y).toMonoidHom ≤
        (X J).map (pieceSpan e).subtype := by
    intro J
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hτ
    refine ⟨ιs ((MulAut.conj c).toMonoidHom x),
      ⟨(MulAut.conj c).toMonoidHom x, ⟨x, mem_subgroupOf.2 hx, rfl⟩, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, hιs_apply]
    change g⁻¹ * ((e.symm (c * x * c⁻¹) : L) : G) * g = y * ((e.symm x : L) : G) * y⁻¹
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hy, ha]
    group
  have hPle : ∀ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      (perfectCore (centralizer (X J : Set (pieceSpan e)))).map (pieceSpan e).subtype ≤
        (pieceSpan e).map (MulAut.conj y).toMonoidHom := by
    intro J
    have hJ' : (nodePermPow m J.1).card ≤ 2 := by
      rw [card_nodePermPow]
      exact J.2
    have h1 : (perfectCore (centralizer (X J : Set (pieceSpan e)))).map (pieceSpan e).subtype ≤
        centralizerPerfectCore ((X J).map (pieceSpan e).subtype) := by
      refine le_centralizerPerfectCore ?_ ?_
      · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
      · rintro _ ⟨p, hp, rfl⟩
        rw [mem_centralizer_iff]
        rintro _ ⟨x, hx, rfl⟩
        exact congrArg Subtype.val
          (mem_centralizer_iff.1 (CFSG.Quasithin.perfectCore_le _ hp) x hx)
    refine h1.trans ((centralizerPerfectCore_anti (hXY J)).trans ?_)
    rw [← map_centralizerPerfectCore]
    exact Subgroup.map_mono
      (le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1)
        ⟨_, hJ'⟩)
  have hG₀le : pieceSpan e ≤ (pieceSpan e).map (MulAut.conj y).toMonoidHom := by
    intro x hx
    have hxH : (⟨x, hx⟩ : pieceSpan e) ∈ H := hHtop ▸ mem_top _
    have hxmap : x ∈ H.map (pieceSpan e).subtype := ⟨⟨x, hx⟩, hxH, rfl⟩
    rw [hH, Subgroup.map_iSup] at hxmap
    exact (iSup_le hPle) hxmap
  have heq : (pieceSpan e).map (MulAut.conj y).toMonoidHom = pieceSpan e :=
    (Subgroup.eq_of_le_of_card_ge hG₀le
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj y).injective))).symm
  have hyN : y ∈ normalizer (pieceSpan e : Set G) := mem_normalizer_iff_map_conj_toMonoidHom.2 heq
  have haN : a ∈ normalizer (pieceSpan e : Set G) := le_normalizer (hLG₀ (e.symm c).2)
  have hg : g = a * y⁻¹ := by
    rw [hy]
    group
  rw [hg]
  exact mul_mem haN (inv_mem hyN)

end Transfer

end CFSG.SeitzReduction.F4Pilot
