module

public import CFSG.GroupTheory.SylowIntersectionControl.CharPair
import CFSG.Quasithin.Background.OddCoprimeFixV
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Lift
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.GroupTheory.AschbacherBlock

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne
open scoped commutatorElement IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem pCoreOf_map_of_injective_ea7b {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    pCoreOf 2 (H.map f) = (pCoreOf 2 H).map f := by
  let e : A ≃* f.range := MonoidHom.ofInjective hf
  have h1 : H.map f = (H.map e.toMonoidHom).map f.range.subtype := by
    rw [Subgroup.map_map]; rfl
  have h2 : ∀ Y : Subgroup f.range, pCoreOf 2 (Y.map f.range.subtype) =
      (pCoreOf 2 Y).map f.range.subtype := by
    intro Y
    unfold pCoreOf
    let φ : Y ≃* Y.map f.range.subtype := Y.equivMapOfInjective _ f.range.subtype_injective
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 φ, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h1, h2, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e H, Subgroup.map_map]
  rfl

private theorem not_isMulCommutative_alternating_ea7b {m : ℕ} (hm : 5 ≤ m) :
    ¬ IsMulCommutative (alternatingGroup (Fin m)) := by
  have : Nontrivial (alternatingGroup (Fin m)) :=
    alternatingGroup.nontrivial_of_three_le_card (α := Fin m) (by simpa using (by omega : 3 ≤ m))
  have : Group.IsPerfect (alternatingGroup (Fin m)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (α := Fin m) (by simpa using hm))
  exact Group.IsPerfect.not_isMulCommutative _

private theorem not_isMulCommutative_sl2_ea7b {F : Type*} [Field F] :
    ¬ IsMulCommutative (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro h
  let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have huv : ((u * l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (2 : F) := by
    show (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 = 2
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]
  have hlu : ((l * u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (1 : F) := by
    show (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hcomm : u * l = l * u := mul_comm' u l
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    ((A : Matrix (Fin 2) (Fin 2) F) 0 0)) hcomm
  rw [huv, hlu] at this
  exact one_ne_zero (by
    have h2 : (1 : F) + 1 = (1 : F) + 0 := by rw [add_zero, one_add_one_eq_two]; exact this
    exact add_left_cancel h2)

private theorem card_quotient_alt_one_ea7b {D : Type} [Group D] {X Y₀ : Subgroup D}
    (h : IsNaturalAltFactor D X Y₀ 1) : Nat.card (↥X ⧸ Y₀.subgroupOf X) = 4 := by
  obtain ⟨φ, ψ, hsum, hsurj, hker, hact⟩ := h
  have : (Y₀.subgroupOf X).Normal := by rw [← hker]; infer_instance
  have hiso : ↥X ⧸ Y₀.subgroupOf X ≃* ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  rw [Nat.card_congr hiso.toEquiv]
  have hrange : ∀ x : Multiplicative (Fin 3 → ZMod 2),
      x ∈ ψ.range ↔ ∑ i, Multiplicative.toAdd x i = 0 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩; exact hsum u
    · intro hx; obtain ⟨u, hu⟩ := hsurj _ hx; exact ⟨u, hu⟩
  have hcard : Nat.card ψ.range = Nat.card {v : Fin 3 → ZMod 2 // ∑ i, v i = 0} :=
    Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, (hrange x.1).mp x.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, (hrange _).mpr v.2⟩
        left_inv := fun x => Subtype.ext (ofAdd_toAdd x.1)
        right_inv := fun v => Subtype.ext (toAdd_ofAdd v.1) }
  rw [hcard, Nat.card_eq_fintype_card]
  decide

private theorem map_subgroupOf_equivMapOfInjective_ea7b {D E : Type*} [Group D] [Group E]
    (f : D →* E) (hf : Function.Injective f) (X Y₀ : Subgroup D) :
    (Y₀.subgroupOf X).map (X.equivMapOfInjective f hf).toMonoidHom =
      (Y₀.map f).subgroupOf (X.map f) := by
  let eX : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  ext y
  constructor
  · intro hy
    obtain ⟨y₀, hy₀, hyy⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_subgroupOf] at hy₀ ⊢
    exact Subgroup.mem_map.mpr ⟨(y₀ : D), hy₀, congrArg Subtype.val hyy⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨y₀, hy₀, hyy⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    have hy0x : y₀ = x := hf (by rw [hyy, hxy])
    exact Subgroup.mem_map.mpr ⟨⟨y₀, hy0x ▸ hx⟩, hy₀, Subtype.ext hyy⟩

private theorem card_quotient_map_ea7b {D E : Type*} [Group D] [Group E] (f : D →* E)
    (hf : Function.Injective f) (X Y₀ : Subgroup D) :
    Nat.card (↥(X.map f) ⧸ (Y₀.map f).subgroupOf (X.map f)) =
      Nat.card (↥X ⧸ Y₀.subgroupOf X) := by
  let eX : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have hmap := map_subgroupOf_equivMapOfInjective_ea7b f hf X Y₀
  calc Nat.card (↥(X.map f) ⧸ (Y₀.map f).subgroupOf (X.map f))
      = ((Y₀.map f).subgroupOf (X.map f)).index := (Subgroup.index_eq_card _).symm
    _ = ((Y₀.subgroupOf X).map eX.toMonoidHom).index := by rw [hmap]
    _ = (Y₀.subgroupOf X).index := Subgroup.index_map_equiv (H := Y₀.subgroupOf X) eX
    _ = Nat.card (↥X ⧸ Y₀.subgroupOf X) := Subgroup.index_eq_card _

private theorem commutator_gomiV_map_le_pCoreOf_ea7b {G M : Subgroup Ω} (hMG : M ≤ G)
    (hQM : pCoreOf 2 G ≤ M) {D : Subgroup ↥M} (hD : IsAschbacherBlockGomi D) :
    ⁅gomiV G, D.map M.subtype⁆ ≤ pCoreOf 2 (D.map M.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDleG : D.map M.subtype ≤ G := (Subgroup.map_subtype_le D).trans hMG
  have hVleQ : gomiV G ≤ pCoreOf 2 G := by
    rw [gomiV, omegaOneCenterOf, omegaOneOf, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx.1
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hQleO2M : pCoreOf 2 G ≤ pCoreOf 2 M := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 hQM ?_ hQ2
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQM]
    exact hMG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  have hVnorm : gomiV G ≤ Subgroup.normalizer (D.map M.subtype : Set Ω) :=
    hVleQ.trans (hQleO2M.trans hD.pCoreOf_le_normalizer)
  have h1 : ⁅gomiV G, D.map M.subtype⁆ ≤ D.map M.subtype :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := gomiV G)
      (K := D.map M.subtype)).mp hVnorm
  have h2 : ⁅gomiV G, D.map M.subtype⁆ ≤ gomiV G :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := D.map M.subtype)
      (K := gomiV G)).mp (hDleG.trans (gomiV_moduleSetting G).2)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h1
    (Subgroup.normalizer_commutator_ge_right (gomiV G) (D.map M.subtype))
    ((hQ2.to_le hVleQ).to_le h2)

omit [Finite Ω] in
private theorem commutator_pCoreOf_map_le_map_ea7b {M : Subgroup Ω} {D : Subgroup ↥M}
    {X : Subgroup ↥D} (hUX : ⁅pCore 2 ↥D, (⊤ : Subgroup ↥D)⁆ ≤ X) :
    ⁅pCoreOf 2 (D.map M.subtype), D.map M.subtype⁆ ≤ X.map (M.subtype.comp D.subtype) := by
  have hpcmap := pCoreOf_map_of_injective_ea7b M.subtype M.subtype_injective D
  have hrange : (M.subtype.comp D.subtype).range = D.map M.subtype := by
    ext x; constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  have h := Subgroup.map_mono (f := M.subtype.comp D.subtype) hUX
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange, ← Subgroup.map_map] at h
  have hmap2 : Subgroup.map M.subtype (Subgroup.map D.subtype (pCore 2 ↥D)) =
      pCoreOf 2 (D.map M.subtype) := by
    rw [hpcmap]
    rfl
  rw [hmap2] at h
  exact h

omit [Finite Ω] in
private theorem autOn_zpowers_eq_ea7b {V : Subgroup Ω} {x : Ω}
    (hx : x ∈ Subgroup.normalizer (V : Set Ω)) :
    CFSG.Quasithin.autOn (Subgroup.zpowers x) V = Subgroup.zpowers (conjAct V ⟨x, hx⟩) := by
  have hsub : (Subgroup.zpowers x).subgroupOf (Subgroup.normalizer (V : Set Ω)) =
      Subgroup.zpowers ⟨x, hx⟩ := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
  unfold CFSG.Quasithin.autOn
  rw [hsub, MonoidHom.map_zpowers]

private theorem commHom_image_inf_ea7b {M : Subgroup Ω} {D : Subgroup ↥M}
    {Y₀ : Subgroup ↥D} {V : Subgroup Ω} {d : Ω} [IsMulCommutative ↥V]
    (hdN : d ∈ Subgroup.normalizer (V : Set Ω))
    (hbot : CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) ⊓
      CFSG.Quasithin.fixV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) = ⊥)
    (hY₀Z : Y₀ ≤ Subgroup.center ↥D)
    (hd : d ∈ D.map M.subtype) :
    ∀ u : ↥(CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)),
      ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) : ↥V) : Ω) ∈
        Y₀.map (M.subtype.comp D.subtype) →
      CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) = 1 := by
  intro u hu
  have hrange : (M.subtype.comp D.subtype).range = D.map M.subtype := by
    ext x; constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  have hZrange : CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) =
      (CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩)).range := by
    rw [autOn_zpowers_eq_ea7b hdN, CFSG.Quasithin.commV_zpowers_eq_map, ← MonoidHom.range_eq_map]
  have hmemZ : CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) ∈
      CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) := by
    have : CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) ∈
        (CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩)).range := ⟨(u : ↥V), rfl⟩
    rw [← hZrange] at this
    exact this
  have hfixσ : CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) ∈
      CFSG.Quasithin.fixV (Subgroup.zpowers (conjAct V ⟨d, hdN⟩)) := by
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff]
    obtain ⟨y₀, hy₀, hyx⟩ := Subgroup.mem_map.mp hu
    have hd' : d ∈ (M.subtype.comp D.subtype).range := by rw [hrange]; exact hd
    obtain ⟨d₀, hd₀⟩ := hd'
    have hcd : y₀ * d₀ = d₀ * y₀ := (Subgroup.mem_center_iff.mp (hY₀Z hy₀) d₀).symm
    have h1 : (M.subtype.comp D.subtype) y₀ * (M.subtype.comp D.subtype) d₀ =
        (M.subtype.comp D.subtype) d₀ * (M.subtype.comp D.subtype) y₀ := by
      rw [← map_mul, ← map_mul, hcd]
    rw [hyx, hd₀] at h1
    have hcomm : ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) : ↥V) : Ω) * d =
        d * ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) : ↥V) : Ω) := h1
    apply Subtype.ext
    rw [CFSG.Quasithin.AutOn.coe_conjAct_apply]
    rw [← hcomm]
    group
  have hfix : CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) ∈
      CFSG.Quasithin.fixV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) := by
    rwa [← autOn_zpowers_eq_ea7b hdN] at hfixσ
  have hmem0 := Subgroup.mem_inf.mpr ⟨hmemZ, hfix⟩
  rw [hbot, Subgroup.mem_bot] at hmem0
  exact hmem0

omit [Finite Ω] in
private theorem commHom_range_mem_ea7b {M : Subgroup Ω} {D : Subgroup ↥M}
    {X : Subgroup ↥D} {V : Subgroup Ω} {d : Ω} [IsMulCommutative ↥V]
    (hdN : d ∈ Subgroup.normalizer (V : Set Ω))
    (hcommVD : ⁅V, D.map M.subtype⁆ ≤ pCoreOf 2 (D.map M.subtype))
    (hCX : ⁅pCoreOf 2 (D.map M.subtype), D.map M.subtype⁆ ≤
      X.map (M.subtype.comp D.subtype))
    (hd : d ∈ D.map M.subtype) :
    ∀ w : ↥(CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)),
      ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (w : ↥V) : ↥V) : Ω) ∈
        X.map (M.subtype.comp D.subtype) := by
  have hL : Subgroup.zpowers d ≤ Subgroup.normalizer (V : Set Ω) := Subgroup.zpowers_le.mpr hdN
  have hZV : (CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)).map
      V.subtype ≤ pCoreOf 2 (D.map M.subtype) := by
    rw [CFSG.Quasithin.AutOn.map_commV_autOn_eq hL]
    exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hd)).trans hcommVD
  intro w
  have hw : (w : Ω) ∈ pCoreOf 2 (D.map M.subtype) := hZV ⟨(w : ↥V), w.2, rfl⟩
  have hc : ⁅(w : Ω), d⁆ ∈ X.map (M.subtype.comp D.subtype) :=
    hCX (Subgroup.commutator_mem_commutator hw hd)
  have hcoe : ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (w : ↥V) : ↥V) : Ω) =
      ⁅(w : Ω), d⁆⁻¹ := by
    rw [CFSG.Quasithin.commHom_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      CFSG.Quasithin.AutOn.coe_conjAct_apply]
    rw [commutatorElement_def]; group
  rw [hcoe]
  exact (X.map (M.subtype.comp D.subtype)).inv_mem hc

omit [Finite Ω] in
private theorem commHom_quotient_injective_ea7b {M : Subgroup Ω} {D : Subgroup ↥M}
    {X Y₀ : Subgroup ↥D} {V : Subgroup Ω} {d : Ω} [IsMulCommutative ↥V]
    [hN : ((Y₀.map (M.subtype.comp D.subtype)).subgroupOf
      (X.map (M.subtype.comp D.subtype))).Normal]
    (hdN : d ∈ Subgroup.normalizer (V : Set Ω))
    (hbot : CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) ⊓
      CFSG.Quasithin.fixV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) = ⊥)
    (hmem : ∀ w : ↥(CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)),
      ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (w : ↥V) : ↥V) : Ω) ∈
        X.map (M.subtype.comp D.subtype))
    (hinf : ∀ u : ↥(CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)),
      ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) : ↥V) : Ω) ∈
        Y₀.map (M.subtype.comp D.subtype) →
      CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) = 1) :
    Function.Injective (fun w : ↥(CFSG.Quasithin.commV
        (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)) =>
      (QuotientGroup.mk (⟨((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (w : ↥V) : ↥V) : Ω),
        hmem w⟩ : ↥(X.map (M.subtype.comp D.subtype))) :
        ↥(X.map (M.subtype.comp D.subtype)) ⧸
          (Y₀.map (M.subtype.comp D.subtype)).subgroupOf
            (X.map (M.subtype.comp D.subtype)))) := by
  intro w₁ w₂ hw
  have hσ : CFSG.Quasithin.autOn (Subgroup.zpowers d) V =
      Subgroup.zpowers (conjAct V ⟨d, hdN⟩) := autOn_zpowers_eq_ea7b hdN
  have hdiv := QuotientGroup.eq_iff_div_mem.mp hw
  rw [Subgroup.mem_subgroupOf] at hdiv
  have hY : ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩)
      ((w₁ : ↥V) * (w₂ : ↥V)⁻¹) : ↥V) : Ω) ∈ Y₀.map (M.subtype.comp D.subtype) := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    simpa only [Subgroup.coe_div, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hdiv
  have h1 := hinf (w₁ * w₂⁻¹) hY
  have hmemK : ((w₁ : ↥V) * (w₂ : ↥V)⁻¹) ∈ (CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩)).ker :=
    MonoidHom.mem_ker.mpr h1
  have hfixσ : ((w₁ : ↥V) * (w₂ : ↥V)⁻¹) ∈
      CFSG.Quasithin.fixV (Subgroup.zpowers (conjAct V ⟨d, hdN⟩)) := by
    rw [← CFSG.Quasithin.ker_commHom]
    exact hmemK
  have hfix : ((w₁ : ↥V) * (w₂ : ↥V)⁻¹) ∈
      CFSG.Quasithin.fixV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) := by
    rwa [← hσ] at hfixσ
  have hZ : ((w₁ : ↥V) * (w₂ : ↥V)⁻¹) ∈
      CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) :=
    Subgroup.mul_mem _ w₁.2 (Subgroup.inv_mem _ w₂.2)
  have hmem0 := Subgroup.mem_inf.mpr ⟨hZ, hfix⟩
  rw [hbot, Subgroup.mem_bot] at hmem0
  exact Subtype.ext (mul_inv_eq_one.mp hmem0)

private theorem card_commV_le_four_of_inj_ea7b {M : Subgroup Ω} {D : Subgroup ↥M}
    {X Y₀ : Subgroup ↥D} {V : Subgroup Ω} {d : Ω} [IsMulCommutative ↥V]
    [hN : ((Y₀.map (M.subtype.comp D.subtype)).subgroupOf
      (X.map (M.subtype.comp D.subtype))).Normal]
    (hdN : d ∈ Subgroup.normalizer (V : Set Ω))
    (hbot : CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) ⊓
      CFSG.Quasithin.fixV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V) = ⊥)
    (hmem : ∀ w : ↥(CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)),
      ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (w : ↥V) : ↥V) : Ω) ∈
        X.map (M.subtype.comp D.subtype))
    (hinf : ∀ u : ↥(CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)),
      ((CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) : ↥V) : Ω) ∈
        Y₀.map (M.subtype.comp D.subtype) →
      CFSG.Quasithin.commHom (conjAct V ⟨d, hdN⟩) (u : ↥V) = 1)
    (hcard : Nat.card (↥(X.map (M.subtype.comp D.subtype)) ⧸
      (Y₀.map (M.subtype.comp D.subtype)).subgroupOf (X.map (M.subtype.comp D.subtype))) = 4) :
    Nat.card ↥(CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) V)) ≤ 4 := by
  have hle := Nat.card_le_card_of_injective _ (commHom_quotient_injective_ea7b hdN hbot hmem hinf)
  rwa [hcard] at hle

private theorem isMulCommutative_quotient_pCore_ea7b {G M : Subgroup Ω} (hMG : M ≤ G)
    {D : Subgroup ↥M}
    (hab : ⁅D.map M.subtype, D.map M.subtype⁆ ≤ pCoreOf 2 G) :
    IsMulCommutative (↥D ⧸ pCore 2 ↥D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfD : Function.Injective (M.subtype.comp D.subtype) :=
    M.subtype_injective.comp D.subtype_injective
  have hpcmap : pCoreOf 2 (D.map M.subtype) =
      (pCore 2 ↥D).map (M.subtype.comp D.subtype) := by
    have h := pCoreOf_map_of_injective_ea7b M.subtype M.subtype_injective D
    rw [h, show pCoreOf 2 D = (pCore 2 ↥D).map D.subtype from rfl, Subgroup.map_map]
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hDbarG : D.map M.subtype ≤ G := (Subgroup.map_subtype_le D).trans hMG
  have hNn : ((pCoreOf 2 G ⊓ D.map M.subtype).subgroupOf (D.map M.subtype)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun h k hh hk => ?_
    exact ⟨(Subgroup.mem_normalizer_iff.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G) (hDbarG hk)) h).mp hh.1,
      (D.map M.subtype).mul_mem ((D.map M.subtype).mul_mem hk hh.2)
        ((D.map M.subtype).inv_mem hk)⟩
  have hQinf : pCoreOf 2 G ⊓ D.map M.subtype ≤ pCoreOf 2 (D.map M.subtype) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right hNn (hQ2.to_le inf_le_left)
  have hcomm : commutator ↥D ≤ pCore 2 ↥D := by
    apply (Subgroup.map_le_map_iff_of_injective (f := M.subtype.comp D.subtype) hfD).mp
    rw [show (commutator ↥D).map (M.subtype.comp D.subtype) = ⁅D.map M.subtype,
        D.map M.subtype⁆ from by
      rw [← Subgroup.map_map, Subgroup.map_subtype_commutator, Subgroup.map_commutator]]
    calc ⁅D.map M.subtype, D.map M.subtype⁆ ≤ pCoreOf 2 G ⊓ D.map M.subtype :=
          le_inf hab (Subgroup.commutator_le_self _)
      _ ≤ pCoreOf 2 (D.map M.subtype) := hQinf
      _ = (pCore 2 ↥D).map (M.subtype.comp D.subtype) := hpcmap
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := pCore 2 ↥D)).mpr hcomm

private theorem isNaturalAltFactor_one_ea7b {D : Type} [Group D] {X Y₀ : Subgroup D}
    (hDab : IsMulCommutative (D ⧸ pCore 2 D))
    (htype : (∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor D X Y₀ n) ∨
      (∃ n, 1 ≤ n ∧ IsNaturalAltFactor D X Y₀ n)) :
    IsNaturalAltFactor D X Y₀ 1 := by
  rcases htype with ⟨n, hn2, hnat⟩ | ⟨n, hn1, hnat⟩
  · exfalso
    obtain ⟨φ, ψ, hsurj, hker, hact⟩ := hnat
    exact not_isMulCommutative_sl2_ea7b (φ.surjective.isMulCommutative hDab)
  · rcases eq_or_lt_of_le hn1 with h | h
    · exact h ▸ hnat
    · exfalso
      obtain ⟨φ, ψ, hsum, hsurj, hker, hact⟩ := hnat
      exact not_isMulCommutative_alternating_ea7b (m := 2 * n + 1) (by omega)
        (φ.surjective.isMulCommutative hDab)

theorem card_commutator_gomiV_zpowers_le_four {G M : Subgroup Ω} (hMG : M ≤ G)
    (hQM : pCoreOf 2 G ≤ M) {D : Subgroup ↥M} (hD : IsAschbacherBlockGomi D)
    (hab : ⁅D.map M.subtype, D.map M.subtype⁆ ≤ pCoreOf 2 G) {d : Ω} (hd : d ∈ D.map M.subtype)
    (hodd : Odd (orderOf d)) :
    Nat.card ↥⁅gomiV G, Subgroup.zpowers d⁆ ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, Y₀, hXn, hYn, hY₀X, hXP, hY₀Z, hUX, hmin, hnc, htype⟩ := hD.chief
  have hfD : Function.Injective (M.subtype.comp D.subtype) :=
    M.subtype_injective.comp D.subtype_injective
  have hY₀n : ((Y₀.map (M.subtype.comp D.subtype)).subgroupOf
      (X.map (M.subtype.comp D.subtype))).Normal := by
    rw [← map_subgroupOf_equivMapOfInjective_ea7b (M.subtype.comp D.subtype) hfD X Y₀]
    exact (hYn.subgroupOf X).map _ (X.equivMapOfInjective _ hfD).surjective
  have hcard : Nat.card (↥(X.map (M.subtype.comp D.subtype)) ⧸
      (Y₀.map (M.subtype.comp D.subtype)).subgroupOf (X.map (M.subtype.comp D.subtype))) = 4 := by
    rw [card_quotient_map_ea7b (M.subtype.comp D.subtype) hfD X Y₀]
    exact card_quotient_alt_one_ea7b (isNaturalAltFactor_one_ea7b
      (isMulCommutative_quotient_pCore_ea7b hMG hab) htype)
  have : IsMulCommutative ↥(gomiV G) := (gomiV_moduleSetting G).1.1
  have hV2 : ∀ v : ↥(gomiV G), v ^ 2 = 1 :=
    fun v => Subtype.ext ((gomiV_moduleSetting G).1.2 (v : Ω) v.2)
  have hdN : d ∈ Subgroup.normalizer (gomiV G : Set Ω) :=
    (gomiV_moduleSetting G).2 (hMG (Subgroup.map_subtype_le D hd))
  have hoddAut : Odd (Nat.card (CFSG.Quasithin.autOn (Subgroup.zpowers d) (gomiV G))) := by
    have hdvd := CFSG.Quasithin.AutOn.card_autOn_dvd (Subgroup.zpowers d) (gomiV G)
    rw [Nat.card_zpowers] at hdvd
    exact hodd.of_dvd_nat hdvd
  have hbot : CFSG.Quasithin.commV (CFSG.Quasithin.autOn (Subgroup.zpowers d) (gomiV G)) ⊓
      CFSG.Quasithin.fixV (CFSG.Quasithin.autOn (Subgroup.zpowers d) (gomiV G)) = ⊥ :=
    commV_inf_fixV_eq_bot_of_odd_card hV2 _ hoddAut
  have hcommVD : ⁅gomiV G, D.map M.subtype⁆ ≤ pCoreOf 2 (D.map M.subtype) :=
    commutator_gomiV_map_le_pCoreOf_ea7b hMG hQM hD
  have hCX : ⁅pCoreOf 2 (D.map M.subtype), D.map M.subtype⁆ ≤
      X.map (M.subtype.comp D.subtype) := commutator_pCoreOf_map_le_map_ea7b hUX
  have hZle := card_commV_le_four_of_inj_ea7b (M := M) (D := D) (X := X) (Y₀ := Y₀)
    (V := gomiV G) (d := d) hdN hbot
    (commHom_range_mem_ea7b (M := M) (D := D) (X := X) (V := gomiV G) (d := d)
      hdN hcommVD hCX hd)
    (commHom_image_inf_ea7b (M := M) (D := D) (Y₀ := Y₀) (V := gomiV G) (d := d)
      hdN hbot hY₀Z hd)
    hcard
  have hL : Subgroup.zpowers d ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    Subgroup.zpowers_le.mpr hdN
  rwa [← Subgroup.card_map_of_injective (K := CFSG.Quasithin.commV
      (CFSG.Quasithin.autOn (Subgroup.zpowers d) (gomiV G))) (gomiV G).subtype_injective,
    CFSG.Quasithin.AutOn.map_commV_autOn_eq hL] at hZle

end CFSG.GroupTheory

end
