module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureStd
import all CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureStd
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeFar
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureCharts
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureUnitaryGeneration
public import CFSG.ClassicalInvolution.Phan.PhanDn.D4Glue
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import TauCeti.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalGroups.Unitary
open CFSG.RankThree.Classical2 CFSG.StandardType.QTwo
open QuadraticMap

open scoped commutatorElement

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private def emb03 : Fin 2 ↪ Fin 4 :=
  ⟨![0, 3], by decide⟩

private theorem h3_restriction
    (hq : 4 ≤ 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {G : Type} [Group G] {a3 : normOmega E 3 →* G}
    {φ : DΩ E 3 →* G} {θ12 θ13 : Su K 2 f 3 →* G}
    (hφ12 : φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 2) = θ12)
    (hφ13 : φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 3) = θ13)
    (hQmap : (qnExtΩ E (Fin.succEmb 3)).range.map (stdEmb E) =
      normPureBlock E 4 {0, 1, 2})
    (hRange12 : ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 2)).range ≤
      (normDel E (by norm_num : 2 ≤ 3) 3).range)
    (hRange13 : ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 3)).range ≤
      (normDel E (by norm_num : 2 ≤ 3) 3).range)
    (hdel3 : (normDel E (by norm_num : 2 ≤ 3) 3).range =
      normBlock E 4 {0, 1, 2})
    (hθ12def : θ12 = liftAt E (by norm_num : 2 ≤ 3) 3 a3
      ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 2)) hRange12)
    (hθ13def : θ13 = liftAt E (by norm_num : 2 ≤ 3) 3 a3
      ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 3)) hRange13) :
    φ.comp (qnExtΩ E (Fin.succEmb 3)) =
      a3.comp (pureEmb E (Function.Embedding.refl (Fin 3))) := by
  let std := stdFamilyΩ E 3 le_rfl hK hq
  let Q : Subgroup (DΩ E 3) := (qnExtΩ E (Fin.succEmb 3)).range
  let S12 : Subgroup (DΩ E 3) := (std.θ 1 2).range
  let S13 : Subgroup (DΩ E 3) := (std.θ 1 3).range
  have hgen : S12 ⊔ S13 = Q := stdFamilyΩ_right_edge_range_sup E hK hq
  have hS12Q : S12 ≤ Q := by rw [← hgen]; exact le_sup_left
  have hS13Q : S13 ≤ Q := by rw [← hgen]; exact le_sup_right
  let FQ : Q →* G := φ.comp Q.subtype
  let βQ : Q →* normOmega E 4 := (stdEmb E).comp Q.subtype
  have hβQ : βQ.range ≤ (normDel E (by norm_num : 2 ≤ 3) 3).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hQmap, hdel3]
    exact normPureBlock_le_normBlock E 4 {0, 1, 2}
  let GQ : Q →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 3 (a3) βQ hβQ
  have hEq12 : S12.subgroupOf Q ≤ FQ.eqLocus GQ := by
    intro y hy
    obtain ⟨s, hs⟩ := MonoidHom.rangeRestrict_surjective (std.θ 1 2)
      ⟨(y : DΩ E 3), hy⟩
    have hya : std.θ 1 2 s = (y : DΩ E 3) := by
      simpa using congrArg Subtype.val hs
    obtain ⟨u, hu⟩ := hRange12 ⟨s, rfl⟩
    have hFQ : FQ y = θ12 s := by
      change φ (y : DΩ E 3) = θ12 s
      rw [← hya, ← hφ12]
      rfl
    have hGQ : GQ y = a3 u := by
      apply liftAt_apply E (by norm_num : 2 ≤ 3) 3 a3 βQ hβQ
      change (stdEmb E) (y : DΩ E 3) =
        (normDel E (by norm_num : 2 ≤ 3) 3) u
      rw [← hya]
      exact hu.symm
    have hθ : θ12 s = a3 u := by
      rw [hθ12def]
      exact liftAt_apply E (by norm_num : 2 ≤ 3) 3 a3
        ((stdEmb E).comp (std.θ 1 2)) hRange12 hu.symm
    rw [MonoidHom.mem_eqLocus]
    change FQ y = GQ y
    rw [hFQ, hGQ, hθ]
  have hEq13 : S13.subgroupOf Q ≤ FQ.eqLocus GQ := by
    intro y hy
    obtain ⟨s, hs⟩ := MonoidHom.rangeRestrict_surjective (std.θ 1 3)
      ⟨(y : DΩ E 3), hy⟩
    have hya : std.θ 1 3 s = (y : DΩ E 3) := by
      simpa using congrArg Subtype.val hs
    obtain ⟨u, hu⟩ := hRange13 ⟨s, rfl⟩
    have hFQ : FQ y = θ13 s := by
      change φ (y : DΩ E 3) = θ13 s
      rw [← hya, ← hφ13]
      rfl
    have hGQ : GQ y = a3 u := by
      apply liftAt_apply E (by norm_num : 2 ≤ 3) 3 a3 βQ hβQ
      change (stdEmb E) (y : DΩ E 3) =
        (normDel E (by norm_num : 2 ≤ 3) 3) u
      rw [← hya]
      exact hu.symm
    have hθ : θ13 s = a3 u := by
      rw [hθ13def]
      exact liftAt_apply E (by norm_num : 2 ≤ 3) 3 a3
        ((stdEmb E).comp (std.θ 1 3)) hRange13 hu.symm
    rw [MonoidHom.mem_eqLocus]
    change FQ y = GQ y
    rw [hFQ, hGQ, hθ]
  have hEqTop : FQ.eqLocus GQ = ⊤ := by
    rw [eq_top_iff]
    calc
      ⊤ = Q.subgroupOf Q := (Subgroup.subgroupOf_self Q).symm
      _ = (S12 ⊔ S13).subgroupOf Q := by rw [hgen]
      _ = S12.subgroupOf Q ⊔ S13.subgroupOf Q :=
        Subgroup.subgroupOf_sup hS12Q hS13Q
      _ ≤ FQ.eqLocus GQ := sup_le hEq12 hEq13
  have hFG : FQ = GQ := by
    apply MonoidHom.eq_of_eqOn_top
    intro x _
    have hx : x ∈ FQ.eqLocus GQ := by rw [hEqTop]; trivial
    exact MonoidHom.mem_eqLocus.mp hx
  apply MonoidHom.ext
  intro x
  let y : Q := ⟨qnExtΩ E (Fin.succEmb 3) x, ⟨x, rfl⟩⟩
  have h := congrArg (fun f : Q →* G => f y) hFG
  have hF : FQ y = φ (qnExtΩ E (Fin.succEmb 3) x) := rfl
  have hG : GQ y = a3 (pureEmb E (Function.Embedding.refl (Fin 3)) x) := by
    apply liftAt_apply E (by norm_num : 2 ≤ 3) 3 a3 βQ hβQ
    have hdel3last : (normDel E (by norm_num : 2 ≤ 3) 3) =
        normOmegaCast E (by norm_num : 3 ≤ 4) := by
      simpa using normDel_last E (by norm_num : 2 ≤ 3)
    have hstdq : (stdEmb E) (qnExtΩ E (Fin.succEmb 3) x) =
        (normOmegaCast E (by norm_num : 3 ≤ 4))
          (pureEmb E (Function.Embedding.refl (Fin 3)) x) :=
      DFunLike.congr_fun (stdEmb_comp_qnExtΩ_succ E) x
    change (stdEmb E) (qnExtΩ E (Fin.succEmb 3) x) =
      (normDel E (by norm_num : 2 ≤ 3) 3)
        (pureEmb E (Function.Embedding.refl (Fin 3)) x)
    rw [hdel3last]
    exact hstdq
  rw [hF, hG] at h
  exact h

private theorem h0_restriction
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {G : Type} [Group G] {φ : DΩ E 3 →* G} {θL : Su K 2 f 3 →* G}
    {a2 : normOmega E 3 →* G}
    (hφι0 : (φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 0)).range = (B12 K 2 f).map θL)
    (hθLB12 : (B12 K 2 f).map θL =
      ((stdNode E hK hq 0).comap (normDel E (by norm_num : 2 ≤ 3) 2)).map a2) :
    ((stdNode E hK hq 0).comap (stdEmb E)).map φ =
      ((stdNode E hK hq 0).comap (normDel E (by norm_num : 2 ≤ 3) 2)).map a2 := by
  let std := stdFamilyΩ E 3 le_rfl hK hq
  have hcomap0 : (stdNode E hK hq 0).comap (stdEmb E) = (std.ι 0).range := by
    rw [stdNode, MonoidHom.range_comp,
      Subgroup.comap_map_eq_self_of_injective (stdEmb_injective E)]
  calc
    ((stdNode E hK hq 0).comap (stdEmb E)).map φ =
        (std.ι 0).range.map φ := by rw [hcomap0]
    _ = (φ.comp (std.ι 0)).range := MonoidHom.map_range φ (std.ι 0)
    _ = (B12 K 2 f).map θL := hφι0
    _ = ((stdNode E hK hq 0).comap
      (normDel E (by norm_num : 2 ≤ 3) 2)).map a2 := hθLB12

theorem exists_pureD4_hom
    (hq : 4 ≤ 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {G : Type} [Group G] {a : Fin 4 → (normOmega E 3 →* G)}
    (ha : ∀ i, Function.Injective (a i))
    {R : Finset (Fin 4) → Subgroup G}
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove)) :
    ∃ φ : DΩ E 3 →* G, Function.Injective φ ∧
      φ.comp (qnExtΩ E (Fin.succEmb 3)) =
        (a 3).comp (pureEmb E (Function.Embedding.refl (Fin 3))) ∧
      ((stdNode E hK hq 0).comap (stdEmb E)).map φ =
        ((stdNode E hK hq 0).comap (normDel E (by norm_num) 2)).map (a 2) := by
  classical
  have hqF : 4 ≤ Nat.card F := by
    rw [card_base_eq_two_pow E (unitaryFieldDataOfCard hK)]
    exact hq
  let std := stdFamilyΩ E 3 le_rfl hK hq
  let del (c : Fin 4) : normOmega E 3 →* normOmega E 4 := normDel E (by norm_num : 2 ≤ 3) c
  let P : Finset (Fin 4) → Subgroup (normOmega E 4) := normPureBlock E 4
  let PB : Finset (Fin 4) → Subgroup (normOmega E 4) := normBlock E 4
  let N0 : Subgroup (normOmega E 4) := stdNode E hK hq 0
  let N1 : Subgroup (normOmega E 4) := stdNode E hK hq 1
  let N1tw : Subgroup (normOmega E 4) := stdNodeTw E hK hq
  let P01 : Subgroup (normOmega E 4) := P {0, 1}
  have hdel3 : (del 3).range = PB {0, 1, 2} := by
    dsimp only [del]
    rw [range_normDel]
    congr 1
  have hdel2 : (del 2).range = PB {0, 1, 3} := by
    dsimp only [del]
    rw [range_normDel]
    congr 1
  have hP01del3 : P01 ≤ (del 3).range := by
    dsimp only [P01, P]
    rw [hdel3]
    exact (normPureBlock_le_normBlock E 4 {0, 1}).trans
      (normBlock_mono E 4 (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2}))
  have hP01del2 : P01 ≤ (del 2).range := by
    dsimp only [P01, P]
    rw [hdel2]
    exact (normPureBlock_le_normBlock E 4 {0, 1}).trans
      (normBlock_mono E 4 (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 3}))
  let S12 : Subgroup (DΩ E 3) := (std.θ 1 2).range
  let S13 : Subgroup (DΩ E 3) := (std.θ 1 3).range
  let Q : Subgroup (DΩ E 3) := (qnExtΩ E (Fin.succEmb 3)).range
  have hgen : S12 ⊔ S13 = Q := stdFamilyΩ_right_edge_range_sup E hK hq
  have hS12Q : S12 ≤ Q := by rw [← hgen]; exact le_sup_left
  have hS13Q : S13 ≤ Q := by rw [← hgen]; exact le_sup_right
  have hQmap : Q.map (stdEmb E) = P {0, 1, 2} := by
    rw [← hgen, Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range]
    exact stdEdges_sup E hK hq
  have hRange12 : ((stdEmb E).comp (std.θ 1 2)).range ≤ (del 3).range := by
    rw [MonoidHom.range_comp]
    calc
      (std.θ 1 2).range.map (stdEmb E) ≤ Q.map (stdEmb E) :=
        Subgroup.map_mono hS12Q
      _ = P {0, 1, 2} := hQmap
      _ ≤ PB {0, 1, 2} := normPureBlock_le_normBlock E 4 {0, 1, 2}
      _ = (del 3).range := hdel3.symm
  have hRange13 : ((stdEmb E).comp (std.θ 1 3)).range ≤ (del 3).range := by
    rw [MonoidHom.range_comp]
    calc
      (std.θ 1 3).range.map (stdEmb E) ≤ Q.map (stdEmb E) :=
        Subgroup.map_mono hS13Q
      _ = P {0, 1, 2} := hQmap
      _ ≤ PB {0, 1, 2} := normPureBlock_le_normBlock E 4 {0, 1, 2}
      _ = (del 3).range := hdel3.symm
  have hRange1 : ((stdEmb E).comp (std.ι 1)).range ≤ (del 3).range := by
    change stdNode E hK hq 1 ≤ (del 3).range
    exact (stdNode_one_le E hK hq).trans hP01del3
  have hRange2 : ((stdEmb E).comp (std.ι 2)).range ≤ (del 3).range := by
    change stdNode E hK hq 2 ≤ (del 3).range
    refine (stdNode_two_le E hK hq).trans ?_
    show normPureBlock E 4 {1, 2} ≤ (del 3).range
    rw [hdel3]
    exact (normPureBlock_le_normBlock E 4 {1, 2}).trans
      (normBlock_mono E 4 (by decide : ({1, 2} : Finset (Fin 4)) ⊆ {0, 1, 2}))
  have hRange3 : ((stdEmb E).comp (std.ι 3)).range ≤ (del 3).range := by
    change stdNode E hK hq 3 ≤ (del 3).range
    rw [stdNode_three E hK hq]
    calc
      (stdNode E hK hq 2).map (tauConj E 4 2).toMonoidHom ≤
          normPureBlock E 4 {1, 2} := by
        rw [← map_normPureBlock_tauConj E 2 {1, 2}]
        exact Subgroup.map_mono (stdNode_two_le E hK hq)
      _ ≤ (del 3).range := by
        rw [hdel3]
        exact (normPureBlock_le_normBlock E 4 {1, 2}).trans
          (normBlock_mono E 4 (by decide : ({1, 2} : Finset (Fin 4)) ⊆ {0, 1, 2}))
  let i₁ : Su K 2 f 2 →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 3 (a 3) ((stdEmb E).comp (std.ι 1)) hRange1
  let i₂ : Su K 2 f 2 →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 3 (a 3) ((stdEmb E).comp (std.ι 2)) hRange2
  let i₃ : Su K 2 f 2 →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 3 (a 3) ((stdEmb E).comp (std.ι 3)) hRange3
  let θ₁₂ : Su K 2 f 3 →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 3 (a 3) ((stdEmb E).comp (std.θ 1 2)) hRange12
  let θ₁₃ : Su K 2 f 3 →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 3 (a 3) ((stdEmb E).comp (std.θ 1 3)) hRange13
  have hgood := stdFamilyΩ_good E 3 le_rfl hK hq
  have hstdEmbInj : Function.Injective (stdEmb E) := stdEmb_injective E
  have hi₁inj : Function.Injective i₁ :=
    liftAt_injective E (by norm_num : 2 ≤ 3) 3 (ha 3) (by
      intro x y hxy
      exact (hgood.inj 1) (hstdEmbInj (by simpa only [MonoidHom.comp_apply] using hxy))) hRange1
  have hi₂inj : Function.Injective i₂ :=
    liftAt_injective E (by norm_num : 2 ≤ 3) 3 (ha 3) (by
      intro x y hxy
      exact (hgood.inj 2) (hstdEmbInj (by simpa only [MonoidHom.comp_apply] using hxy))) hRange2
  have hi₃inj : Function.Injective i₃ :=
    liftAt_injective E (by norm_num : 2 ≤ 3) 3 (ha 3) (by
      intro x y hxy
      exact (hgood.inj 3) (hstdEmbInj (by simpa only [MonoidHom.comp_apply] using hxy))) hRange3
  have hθ₁₂inj : Function.Injective θ₁₂ :=
    liftAt_injective E (by norm_num : 2 ≤ 3) 3 (ha 3)
      (by
      intro x y hxy
      exact (hgood.θ_inj 1 2 (by norm_num) (by decide)) (hstdEmbInj (by simpa only [MonoidHom.comp_apply] using hxy))) hRange12
  have hθ₁₃inj : Function.Injective θ₁₃ :=
    liftAt_injective E (by norm_num : 2 ≤ 3) 3 (ha 3)
      (by
      intro x y hxy
      exact (hgood.θ_inj 1 3 (by norm_num) (by decide)) (hstdEmbInj (by simpa only [MonoidHom.comp_apply] using hxy))) hRange13
  have hker12 : θ₁₂.ker ≤ Subgroup.center (Su K 2 f 3) := by
    rw [MonoidHom.ker_eq_bot θ₁₂ hθ₁₂inj]
    exact bot_le
  have h12 : θ₁₂.comp (embSUid (unitaryInvolution K 2 f) 2) = i₁ ∧
      θ₁₂.comp (embSUid (unitaryInvolution K 2 f) 0) = i₂ := by
    constructor
    · apply MonoidHom.ext
      intro x
      obtain ⟨u, hu⟩ := hRange1 ⟨x, rfl⟩
      have hstdx : (std.θ 1 2) ((embSUid (unitaryInvolution K 2 f) 2) x) =
          std.ι 1 x :=
        DFunLike.congr_fun (std.left 1 2 (by norm_num) (by decide)) x
      have hα : ((stdEmb E).comp (std.θ 1 2))
          ((embSUid (unitaryInvolution K 2 f) 2) x) = (del 3) u := by
        change (stdEmb E) ((std.θ 1 2)
          ((embSUid (unitaryInvolution K 2 f) 2) x)) = (del 3) u
        rw [hstdx]
        exact hu.symm
      have hθ : θ₁₂ ((embSUid (unitaryInvolution K 2 f) 2) x) = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.θ 1 2)) hRange12 hα
      have hi : i₁ x = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.ι 1)) hRange1 hu.symm
      rw [MonoidHom.comp_apply, hθ, hi]
    · apply MonoidHom.ext
      intro x
      obtain ⟨u, hu⟩ := hRange2 ⟨x, rfl⟩
      have hstdx : (std.θ 1 2) ((embSUid (unitaryInvolution K 2 f) 0) x) =
          std.ι 2 x :=
        DFunLike.congr_fun (std.right 1 2 (by norm_num) (by decide)) x
      have hα : ((stdEmb E).comp (std.θ 1 2))
          ((embSUid (unitaryInvolution K 2 f) 0) x) = (del 3) u := by
        change (stdEmb E) ((std.θ 1 2)
          ((embSUid (unitaryInvolution K 2 f) 0) x)) = (del 3) u
        rw [hstdx]
        exact hu.symm
      have hθ : θ₁₂ ((embSUid (unitaryInvolution K 2 f) 0) x) = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.θ 1 2)) hRange12 hα
      have hi : i₂ x = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.ι 2)) hRange2 hu.symm
      rw [MonoidHom.comp_apply, hθ, hi]
  have h13 : θ₁₃.comp (embSUid (unitaryInvolution K 2 f) 2) = i₁ ∧
      θ₁₃.comp (embSUid (unitaryInvolution K 2 f) 0) = i₃ := by
    constructor
    · apply MonoidHom.ext
      intro x
      obtain ⟨u, hu⟩ := hRange1 ⟨x, rfl⟩
      have hstdx : (std.θ 1 3) ((embSUid (unitaryInvolution K 2 f) 2) x) =
          std.ι 1 x :=
        DFunLike.congr_fun (std.left 1 3 (by norm_num) (by decide)) x
      have hα : ((stdEmb E).comp (std.θ 1 3))
          ((embSUid (unitaryInvolution K 2 f) 2) x) = (del 3) u := by
        change (stdEmb E) ((std.θ 1 3)
          ((embSUid (unitaryInvolution K 2 f) 2) x)) = (del 3) u
        rw [hstdx]
        exact hu.symm
      have hθ : θ₁₃ ((embSUid (unitaryInvolution K 2 f) 2) x) = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.θ 1 3)) hRange13 hα
      have hi : i₁ x = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.ι 1)) hRange1 hu.symm
      rw [MonoidHom.comp_apply, hθ, hi]
    · apply MonoidHom.ext
      intro x
      obtain ⟨u, hu⟩ := hRange3 ⟨x, rfl⟩
      have hstdx : (std.θ 1 3) ((embSUid (unitaryInvolution K 2 f) 0) x) =
          std.ι 3 x :=
        DFunLike.congr_fun (std.right 1 3 (by norm_num) (by decide)) x
      have hα : ((stdEmb E).comp (std.θ 1 3))
          ((embSUid (unitaryInvolution K 2 f) 0) x) = (del 3) u := by
        change (stdEmb E) ((std.θ 1 3)
          ((embSUid (unitaryInvolution K 2 f) 0) x)) = (del 3) u
        rw [hstdx]
        exact hu.symm
      have hθ : θ₁₃ ((embSUid (unitaryInvolution K 2 f) 0) x) = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.θ 1 3)) hRange13 hα
      have hi : i₃ x = (a 3) u :=
        liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3)
          ((stdEmb E).comp (std.ι 3)) hRange3 hu.symm
      rw [MonoidHom.comp_apply, hθ, hi]
  have h23 : ∀ x y, i₂ x * i₃ y = i₃ y * i₂ x := by
    intro x y
    obtain ⟨u, hu⟩ := hRange2 ⟨x, rfl⟩
    obtain ⟨v, hv⟩ := hRange3 ⟨y, rfl⟩
    have hi₂u : i₂ x = (a 3) u :=
      liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3) ((stdEmb E).comp (std.ι 2)) hRange2
        (x := x) (y := u) hu.symm
    have hi₃v : i₃ y = (a 3) v :=
      liftAt_apply E (by norm_num : 2 ≤ 3) 3 (a 3) ((stdEmb E).comp (std.ι 3)) hRange3
        (x := y) (y := v) hv.symm
    have hdel : del 3 (u * v) = del 3 (v * u) := by
      have hstd : std.ι 2 x * std.ι 3 y = std.ι 3 y * std.ι 2 x :=
        std.comm 2 3 (by decide) x y
      calc
        del 3 (u * v) = del 3 u * del 3 v := map_mul (del 3) u v
        _ = ((stdEmb E).comp (std.ι 2)) x * ((stdEmb E).comp (std.ι 3)) y := by
          rw [hu, hv]
        _ = ((stdEmb E).comp (std.ι 3)) y * ((stdEmb E).comp (std.ι 2)) x := by
          simpa only [map_mul, MonoidHom.comp_apply] using congrArg (stdEmb E) hstd
        _ = del 3 v * del 3 u := by rw [hv, hu]
        _ = del 3 (v * u) := (map_mul (del 3) v u).symm
    have huv : u * v = v * u := normDel_injective E (by norm_num : 2 ≤ 3) 3 hdel
    calc
      i₂ x * i₃ y = (a 3) u * (a 3) v := by rw [hi₂u, hi₃v]
      _ = (a 3) (u * v) := (map_mul _ _ _).symm
      _ = (a 3) (v * u) := by rw [huv]
      _ = (a 3) v * (a 3) u := map_mul _ _ _
      _ = i₃ y * i₂ x := by rw [hi₃v, hi₂u]
  let Y : Subgroup G := (N1.comap (del 3)).map (a 3)
  let X : Subgroup (normOmega E 4) := (Y.comap (a 2)).map (del 2)
  have hP03map : (P01.comap (del 3)).map (a 3) = rangePurePair R 0 1 := by
    have hS : ({0, 1} : Finset (Fin 3)).map (3 : Fin 4).succAboveEmb =
        ({0, 1} : Finset (Fin 4)) := by decide
    have hcomap : P01.comap (del 3) = normPureBlock E 3 {0, 1} := by
      dsimp only [P01, P]
      rw [← hS, comap_normPureBlock_normDel]
    rw [hcomap]
    exact (rangePurePair_eq_map E hqF ha hR (i := 0) (j := 1) (l := 3)
      (by decide) (by decide) (by decide) (i' := 0) (j' := 1) (by decide) (by decide)).symm
  have hP02map : (P01.comap (del 2)).map (a 2) = rangePurePair R 0 1 := by
    have hS : ({0, 1} : Finset (Fin 3)).map (2 : Fin 4).succAboveEmb =
        ({0, 1} : Finset (Fin 4)) := by decide
    have hcomap : P01.comap (del 2) = normPureBlock E 3 {0, 1} := by
      dsimp only [P01, P]
      rw [← hS, comap_normPureBlock_normDel]
    rw [hcomap]
    exact (rangePurePair_eq_map E hqF ha hR (i := 0) (j := 1) (l := 2)
      (by decide) (by decide) (by decide) (i' := 0) (j' := 1) (by decide) (by decide)).symm
  have hYcommon : Y ≤ rangePurePair R 0 1 := by
    dsimp only [Y, N1]
    rw [← hP03map]
    exact Subgroup.map_mono (Subgroup.comap_mono (stdNode_one_le E hK hq))
  have hYle2 : Y ≤ (P01.comap (del 2)).map (a 2) := by
    rw [hP02map]
    exact hYcommon
  have hYleA2 : Y ≤ (a 2).range :=
    hYle2.trans (Subgroup.map_le_range (f := a 2) (H := P01.comap (del 2)))
  have hXleP : X ≤ P01 := by
    rintro _ ⟨y, hy, rfl⟩
    have hay : (a 2) y ∈ Y := hy
    have hay' : (a 2) y ∈ (P01.comap (del 2)).map (a 2) := hYle2 hay
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp hay'
    have hpy : p = y := (ha 2) hpa
    rw [← hpy]
    exact hp
  have hN1P : N1 ≤ P01 := stdNode_one_le E hK hq
  have hN1Pnorm : P01 ≤ Subgroup.normalizer (N1 : Set (normOmega E 4)) := by
    dsimp only [P01, P]
    rw [← stdNode_one_sup_tw E hK hq]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    have hcomm : x * b = b * x := commute_stdNode_one_tw E hK hq hx hb
    rw [← hcomm]
    simpa using hx
  have hNormalY3 : (P01.comap (del 3)).map (a 3) ≤
      Subgroup.normalizer (Y : Set G) := by
    have h1 : P01.comap (del 3) ≤ (Subgroup.normalizer (N1 : Set (normOmega E 4))).comap (del 3) :=
      Subgroup.comap_mono hN1Pnorm
    have h2 : P01.comap (del 3) ≤
        Subgroup.normalizer (N1.comap (del 3) : Set (normOmega E 3)) :=
      h1.trans (Subgroup.le_normalizer_comap (H := N1) (f := del 3))
    have h3 : (P01.comap (del 3)).map (a 3) ≤
        (Subgroup.normalizer (N1.comap (del 3) : Set (normOmega E 3))).map (a 3) :=
      Subgroup.map_mono h2
    exact h3.trans (by
      simpa only [Y] using
        (Subgroup.le_normalizer_map (H := N1.comap (del 3)) (f := a 3)))
  have hNormalY2 : (P01.comap (del 2)).map (a 2) ≤
      Subgroup.normalizer (Y : Set G) := by
    rw [hP02map, ← hP03map]
    exact hNormalY3
  have hXnormal : P01 ≤ Subgroup.normalizer (X : Set (normOmega E 4)) := by
    have h1 : P01.comap (del 2) ≤ (Subgroup.normalizer (Y : Set G)).comap (a 2) :=
      Subgroup.map_le_iff_le_comap.mp hNormalY2
    have h2 : P01.comap (del 2) ≤
        Subgroup.normalizer (Y.comap (a 2) : Set (normOmega E 3)) :=
      h1.trans (Subgroup.le_normalizer_comap (H := Y) (f := a 2))
    have h3 : (P01.comap (del 2)).map (del 2) ≤
        (Subgroup.normalizer (Y.comap (a 2) : Set (normOmega E 3))).map (del 2) :=
      Subgroup.map_mono h2
    have h4 : (Subgroup.normalizer (Y.comap (a 2) : Set (normOmega E 3))).map (del 2) ≤
        Subgroup.normalizer ((Y.comap (a 2)).map (del 2) : Set (normOmega E 4)) :=
      Subgroup.le_normalizer_map (H := Y.comap (a 2)) (f := del 2)
    rw [← Subgroup.map_comap_eq_self (H := P01) (f := del 2) hP01del2]
    exact h3.trans (by simpa only [X] using h4)
  have hYcard : Nat.card Y = Nat.card N1 := by
    dsimp only [Y]
    rw [Subgroup.card_map_of_injective (ha 3)]
    have hmap := Subgroup.map_comap_eq_self (f := del 3) (H := N1) (by
      change N1 ≤ (del 3).range
      exact hN1P.trans hP01del3)
    have hcard := Subgroup.card_map_of_injective (normDel_injective E (by norm_num : 2 ≤ 3) 3)
      (K := N1.comap (del 3))
    rw [hmap] at hcard
    exact hcard.symm
  have hXcardY : Nat.card X = Nat.card Y := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective (normDel_injective E (by norm_num : 2 ≤ 3) 2)]
    have hmap := Subgroup.map_comap_eq_self (f := a 2) (H := Y) hYleA2
    have hcard := Subgroup.card_map_of_injective (ha 2) (K := Y.comap (a 2))
    rw [hmap] at hcard
    exact hcard.symm
  have hN1card : Nat.card N1 = Nat.card (Su K 2 f 2) := by
    change Nat.card (((stdEmb E).comp (std.ι 1)).range) = Nat.card (Su K 2 f 2)
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hstdEmbInj]
    have hcardtop := Subgroup.card_map_of_injective (f := std.ι 1) (hgood.inj 1) (K := ⊤)
    rw [Subgroup.map_top] at hcardtop
    simpa [Subgroup.card_top] using hcardtop
  have hXcard : Nat.card X = Nat.card (Su K 2 f 2) := by
    rw [hXcardY, hYcard, hN1card]
  have hsu2noncomm : ∃ x y : Su K 2 f 2, x * y ≠ y * x := by
    haveI : IsSimpleGroup (Su K 2 f 2) := isSimpleGroup_Su_two hK hq
    haveI : Group.IsPerfect (Su K 2 f 2) :=
      CFSG.RankThree.PartOne.CTP.isPerfect_su_two hK (two_le_of_four_le_pow hq)
    by_contra h
    push Not at h
    exact (Group.IsPerfect.not_isMulCommutative (Su K 2 f 2))
      (IsMulCommutative.of_comm h)
  have hXnab : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hsu2noncomm
    let fY : N1 →* G := liftAt E (by norm_num : 2 ≤ 3) 3 (a 3) N1.subtype (by
      rw [Subgroup.range_subtype]
      exact hN1P.trans hP01del3)
    have hfYinj : Function.Injective fY :=
      liftAt_injective E (by norm_num : 2 ≤ 3) 3 (ha 3) Subtype.coe_injective (by
        rw [Subgroup.range_subtype]
        exact hN1P.trans hP01del3)
    have hfYrange : fY.range = Y := by
      dsimp only [fY, Y]
      rw [range_liftAt, Subgroup.range_subtype]
    let eY : N1 ≃* Y := (MonoidHom.ofInjective hfYinj).trans (MulEquiv.subgroupCongr hfYrange)
    let xN : N1 := ⟨stdEmb E (std.ι 1 x), ⟨x, rfl⟩⟩
    let yN : N1 := ⟨stdEmb E (std.ι 1 y), ⟨y, rfl⟩⟩
    have hxyN : xN * yN ≠ yN * xN := by
      intro h
      apply hxy
      apply (hgood.inj 1)
      apply hstdEmbInj
      have h' := congrArg (fun z : N1 => (z : normOmega E 4)) h
      simpa only [Subgroup.coe_mul, map_mul] using h'
    let y1 : Y := eY xN
    let y2 : Y := eY yN
    have hy12 : y1 * y2 ≠ y2 * y1 := by
      intro h
      apply hxyN
      apply eY.injective
      simpa only [map_mul] using h
    obtain ⟨q1, hq1⟩ := MonoidHom.mem_range.mp (hYleA2 y1.2)
    obtain ⟨q2, hq2⟩ := MonoidHom.mem_range.mp (hYleA2 y2.2)
    have hq1mem : q1 ∈ Y.comap (a 2) := by
      change (a 2) q1 ∈ Y
      rw [hq1]
      exact y1.2
    have hq2mem : q2 ∈ Y.comap (a 2) := by
      change (a 2) q2 ∈ Y
      rw [hq2]
      exact y2.2
    let x1 : X := ⟨del 2 q1, Subgroup.mem_map.mpr ⟨q1, hq1mem, rfl⟩⟩
    let x2 : X := ⟨del 2 q2, Subgroup.mem_map.mpr ⟨q2, hq2mem, rfl⟩⟩
    have hx12 : x1 * x2 ≠ x2 * x1 := by
      intro h
      apply hy12
      apply Subtype.ext
      have h' := congrArg (Subtype.val) h
      simp only [Subgroup.coe_mul] at h'
      have hq : q1 * q2 = q2 * q1 :=
        normDel_injective E (by norm_num : 2 ≤ 3) 2 (by
          simpa only [map_mul] using h')
      simp only [Subgroup.coe_mul]
      rw [← hq1, ← hq2, ← map_mul, ← map_mul, hq]
    exact ⟨(x1 : normOmega E 4), x1.2, (x2 : normOmega E 4), x2.2, by
      intro h
      exact hx12 (Subtype.ext h)⟩
  have hXeq : X = N1 ∨ X = N1tw :=
    eq_or_eq_stdNode_one E hK hq hXleP hXnormal hXcard hXnab

  have hN0P : N0 ≤ P {0, 3} := stdNode_zero_le E hK hq
  have himage03 : (Finset.univ.map emb03) = ({0, 3} : Finset (Fin 4)) := by decide
  have hfixP03 : ∀ x ∈ P {0, 3}, tauConj E 4 1 x = x := by
    intro x hx
    have hx' : x ∈ (pureEmb E emb03).range := by
      rw [range_pureEmb, himage03]
      exact hx
    obtain ⟨g, rfl⟩ := hx'
    refine tauConj_pureEmb_of_not_mem E emb03 ?_ g
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [emb03] at hi
  have hN0fix : ∀ x ∈ N0, tauConj E 4 1 x = x := fun x hx => hfixP03 x (hN0P hx)
  have hN0mapτ : N0.map (tauConj E 4 1).toMonoidHom = N0 := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap]
      have hxfix : (tauConj E 4 1) x = x := hN0fix x hx
      simpa only [MulEquiv.coe_toMonoidHom, hxfix] using hx
    · intro x hx
      exact Subgroup.mem_map.mpr ⟨x, hx, by
        simpa only [MulEquiv.coe_toMonoidHom] using hN0fix x hx⟩
  let α0 : Su K 2 f 3 →* normOmega E 4 := (stdEmb E).comp (std.θ 0 1)
  have hα0P : α0.range ≤ P {0, 1, 3} := by
    dsimp only [α0]
    exact stdEdge01_le E hK hq
  have hα0del2 : α0.range ≤ (del 2).range := by
    refine hα0P.trans ?_
    dsimp only [P, PB]
    rw [hdel2]
    exact normPureBlock_le_normBlock E 4 {0, 1, 3}
  have hα0inj : Function.Injective α0 :=
    hstdEmbInj.comp (hgood.θ_inj 0 1 (by norm_num) (by decide))
  let ατ : Su K 2 f 3 →* normOmega E 4 :=
    (tauConj E 4 1).toMonoidHom.comp α0
  have hατP : ατ.range ≤ P {0, 1, 3} := by
    dsimp only [ατ]
    rw [MonoidHom.range_comp]
    calc
      α0.range.map (tauConj E 4 1).toMonoidHom ≤
          (P {0, 1, 3}).map (tauConj E 4 1).toMonoidHom :=
        Subgroup.map_mono hα0P
      _ = P {0, 1, 3} := map_normPureBlock_tauConj E 1 {0, 1, 3}
  have hατdel2 : ατ.range ≤ (del 2).range := by
    refine hατP.trans ?_
    dsimp only [P, PB]
    rw [hdel2]
    exact normPureBlock_le_normBlock E 4 {0, 1, 3}
  have hατinj : Function.Injective ατ :=
    (tauConj E 4 1).injective.comp hα0inj
  let θL0 : Su K 2 f 3 →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 2 (a 2) α0 hα0del2
  let θLτ : Su K 2 f 3 →* G :=
    liftAt E (by norm_num : 2 ≤ 3) 2 (a 2) ατ hατdel2
  have hθL0inj : Function.Injective θL0 :=
    liftAt_injective E (by norm_num : 2 ≤ 3) 2 (ha 2) hα0inj hα0del2
  have hθLτinj : Function.Injective θLτ :=
    liftAt_injective E (by norm_num : 2 ≤ 3) 2 (ha 2) hατinj hατdel2
  have hL0 : θL0.ker ≤ Subgroup.center (Su K 2 f 3) := by
    rw [MonoidHom.ker_eq_bot θL0 hθL0inj]
    exact bot_le
  have hLτ : θLτ.ker ≤ Subgroup.center (Su K 2 f 3) := by
    rw [MonoidHom.ker_eq_bot θLτ hθLτinj]
    exact bot_le
  have hθL0_B12 : (B12 K 2 f).map θL0 = (N0.comap (del 2)).map (a 2) := by
    rw [B12, MonoidHom.map_range]
    dsimp only [θL0]
    rw [liftAt_comp]
    have hcomp : α0.comp (embSUid (unitaryInvolution K 2 f) 2) =
        (stdEmb E).comp (std.ι 0) := by
      dsimp only [α0]
      rw [MonoidHom.comp_assoc]
      rw [show (std.θ 0 1).comp (embSUid (unitaryInvolution K 2 f) 2) = std.ι 0 from
        std.left 0 1 (by norm_num) (by decide)]
    rw [range_liftAt, hcomp]
    rfl
  have hθL0_B23 : (B23 K 2 f).map θL0 = (N1.comap (del 2)).map (a 2) := by
    rw [B23, MonoidHom.map_range]
    dsimp only [θL0]
    rw [liftAt_comp]
    have hcomp : α0.comp (embSUid (unitaryInvolution K 2 f) 0) =
        (stdEmb E).comp (std.ι 1) := by
      dsimp only [α0]
      rw [MonoidHom.comp_assoc]
      rw [show (std.θ 0 1).comp (embSUid (unitaryInvolution K 2 f) 0) = std.ι 1 from
        std.right 0 1 (by norm_num) (by decide)]
    rw [range_liftAt, hcomp]
    rfl
  have hrangeτ : Subgroup.map (tauConj E 4 1).toMonoidHom
      ((stdEmb E).comp (std.ι 0)).range = ((stdEmb E).comp (std.ι 0)).range := by
    change Subgroup.map (tauConj E 4 1).toMonoidHom N0 = N0
    exact hN0mapτ
  have hθLτ_B12 : (B12 K 2 f).map θLτ = (N0.comap (del 2)).map (a 2) := by
    rw [B12, MonoidHom.map_range]
    dsimp only [θLτ]
    rw [liftAt_comp]
    have hcomp : ατ.comp (embSUid (unitaryInvolution K 2 f) 2) =
        (tauConj E 4 1).toMonoidHom.comp ((stdEmb E).comp (std.ι 0)) := by
      dsimp only [ατ]
      rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc]
      rw [show (std.θ 0 1).comp (embSUid (unitaryInvolution K 2 f) 2) = std.ι 0 from
        std.left 0 1 (by norm_num) (by decide)]
    rw [range_liftAt, hcomp, MonoidHom.range_comp, hrangeτ]
    rfl
  have hθLτ_B23 : (B23 K 2 f).map θLτ = (N1tw.comap (del 2)).map (a 2) := by
    rw [B23, MonoidHom.map_range]
    dsimp only [θLτ]
    rw [liftAt_comp]
    have hcomp : ατ.comp (embSUid (unitaryInvolution K 2 f) 0) =
        (tauConj E 4 1).toMonoidHom.comp ((stdEmb E).comp (std.ι 1)) := by
      dsimp only [ατ]
      rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc]
      rw [show (std.θ 0 1).comp (embSUid (unitaryInvolution K 2 f) 0) = std.ι 1 from
        std.right 0 1 (by norm_num) (by decide)]
    rw [range_liftAt, hcomp, MonoidHom.range_comp]
    change (((N1.map (tauConj E 4 1).toMonoidHom).comap (del 2)).map (a 2)) =
      ((N1tw.comap (del 2)).map (a 2))
    rw [show N1.map (tauConj E 4 1).toMonoidHom = N1tw from rfl]
  have hB12θ12 : (B12 K 2 f).map θ₁₂ = Y := by
    rw [B12, MonoidHom.map_range, h12.1]
    dsimp only [i₁]
    rw [range_liftAt]
    change ((N1.comap (del 3)).map (a 3)) = Y
    rfl
  have hB23θ12 : (B23 K 2 f).map θ₁₂ = i₂.range := by
    rw [B23, MonoidHom.map_range, h12.2]
  have hN2P : stdNode E hK hq 2 ≤ P {1, 2} := stdNode_two_le E hK hq
  have hN3P : stdNode E hK hq 3 ≤ P {1, 2} := by
    rw [stdNode_three E hK hq]
    show (stdNode E hK hq 2).map (tauConj E 4 2).toMonoidHom ≤
      normPureBlock E 4 {1, 2}
    rw [← map_normPureBlock_tauConj E 2 {1, 2}]
    exact Subgroup.map_mono hN2P
  have hP12c3 : (P {1, 2}).comap (del 3) = normPureBlock E 3 {1, 2} := by
    have hS : ({1, 2} : Finset (Fin 3)).map (3 : Fin 4).succAboveEmb =
        ({1, 2} : Finset (Fin 4)) := by decide
    dsimp only [P]
    rw [← hS, comap_normPureBlock_normDel]
  have hi2_R : i₂.range ≤ R {1, 2} := by
    dsimp only [i₂]
    rw [range_liftAt]
    change ((stdNode E hK hq 2).comap (del 3)).map (a 3) ≤ R {1, 2}
    calc
      ((stdNode E hK hq 2).comap (del 3)).map (a 3) ≤
          ((P {1, 2}).comap (del 3)).map (a 3) :=
        Subgroup.map_mono (Subgroup.comap_mono hN2P)
      _ = (normPureBlock E 3 {1, 2}).map (a 3) := by rw [hP12c3]
      _ ≤ (normBlock E 3 {1, 2}).map (a 3) :=
        Subgroup.map_mono (normPureBlock_le_normBlock E 3 {1, 2})
      _ = R {1, 2} := by
        have hS : ({1, 2} : Finset (Fin 3)).image (3 : Fin 4).succAbove =
            ({1, 2} : Finset (Fin 4)) := by decide
        simpa [hS] using hR 3 ({1, 2} : Finset (Fin 3)) (by decide) (by decide)
  have hi3_R : i₃.range ≤ R {1, 2} := by
    dsimp only [i₃]
    rw [range_liftAt]
    change ((stdNode E hK hq 3).comap (del 3)).map (a 3) ≤ R {1, 2}
    calc
      ((stdNode E hK hq 3).comap (del 3)).map (a 3) ≤
          ((P {1, 2}).comap (del 3)).map (a 3) :=
        Subgroup.map_mono (Subgroup.comap_mono hN3P)
      _ = (normPureBlock E 3 {1, 2}).map (a 3) := by rw [hP12c3]
      _ ≤ (normBlock E 3 {1, 2}).map (a 3) :=
        Subgroup.map_mono (normPureBlock_le_normBlock E 3 {1, 2})
      _ = R {1, 2} := by
        have hS : ({1, 2} : Finset (Fin 3)).image (3 : Fin 4).succAbove =
            ({1, 2} : Finset (Fin 4)) := by decide
        simpa [hS] using hR 3 ({1, 2} : Finset (Fin 3)) (by decide) (by decide)
  have hpair30 : rangePurePair R 3 0 =
      (normPureBlock E 3 ({2, 0} : Finset (Fin 3))).map (a 2) :=
    rangePurePair_eq_map E hqF ha hR (i := 3) (j := 0) (l := 2)
      (by decide) (by decide) (by decide) (i' := 2) (j' := 0) (by decide) (by decide)
  have hP403 : (P {0, 3}).comap (del 2) =
      normPureBlock E 3 ({2, 0} : Finset (Fin 3)) := by
    have hS : ({2, 0} : Finset (Fin 3)).map (2 : Fin 4).succAboveEmb =
        ({0, 3} : Finset (Fin 4)) := by decide
    dsimp only [P]
    rw [← hS, comap_normPureBlock_normDel]
  have hY2N1 (hX1 : X = N1) : (N1.comap (del 2)).map (a 2) = Y := by
    have hX1' : (Y.comap (a 2)).map (del 2) = N1 := by
      rw [← hX1]
    calc
      (N1.comap (del 2)).map (a 2)
          = (((Y.comap (a 2)).map (del 2)).comap (del 2)).map (a 2) := by rw [hX1']
      _ = (Y.comap (a 2)).map (a 2) := by
        rw [Subgroup.comap_map_eq_self_of_injective
          (normDel_injective E (by norm_num : 2 ≤ 3) 2)]
      _ = Y := Subgroup.map_comap_eq_self hYleA2
  have hY2N1tw (hXtw : X = N1tw) : (N1tw.comap (del 2)).map (a 2) = Y := by
    have hXtw' : (Y.comap (a 2)).map (del 2) = N1tw := by
      rw [← hXtw]
    calc
      (N1tw.comap (del 2)).map (a 2)
          = (((Y.comap (a 2)).map (del 2)).comap (del 2)).map (a 2) := by rw [hXtw']
      _ = (Y.comap (a 2)).map (a 2) := by
        rw [Subgroup.comap_map_eq_self_of_injective
          (normDel_injective E (by norm_num : 2 ≤ 3) 2)]
      _ = Y := Subgroup.map_comap_eq_self hYleA2
  have assemble : ∀ (θL : Su K 2 f 3 →* G),
      θL.ker ≤ Subgroup.center (Su K 2 f 3) →
      (B23 K 2 f).map θL = (B12 K 2 f).map θ₁₂ →
      (∀ x ∈ (B12 K 2 f).map θL, ∀ y ∈ (B23 K 2 f).map θ₁₂, x * y = y * x) →
      (∀ x ∈ (B12 K 2 f).map θL, ∀ b,
        x * i₂ b = i₂ b * x ∧ x * i₃ b = i₃ b * x) →
      (B12 K 2 f).map θL = (N0.comap (del 2)).map (a 2) →
      ∃ φ : DΩ E 3 →* G, Function.Injective φ ∧
        φ.comp (qnExtΩ E (Fin.succEmb 3)) =
          (a 3).comp (pureEmb E (Function.Embedding.refl (Fin 3))) ∧
        ((stdNode E hK hq 0).comap (stdEmb E)).map φ =
          ((stdNode E hK hq 0).comap (normDel E (by norm_num) 2)).map (a 2) := by
    intro θL hL hM hcomm h0 hθLB12
    obtain ⟨φ, hinj, hφ12, hφ13, hφι1, hφι2, hφι3, hφι0, hφθ01⟩ :=
      exists_injective_phanD4_hom E hK hq i₁ i₂ i₃ θ₁₂ θ₁₃ θL
        h12 h13 h23 hL hker12 hM hcomm h0 hi₁inj
    refine ⟨φ, hinj, ?_, ?_⟩
    · exact h3_restriction (E := E) (a3 := a 3) hq hK hφ12 hφ13 hQmap
        hRange12 hRange13 hdel3 (hθ12def := rfl) (hθ13def := rfl)
    · exact h0_restriction (E := E) (φ := φ) (θL := θL) (a2 := a 2) hK hq hφι0 hθLB12
  rcases hXeq with hX1 | hXtw
  · have hM : (B23 K 2 f).map θL0 = (B12 K 2 f).map θ₁₂ := by
      rw [hθL0_B23, hY2N1 hX1, hB12θ12]
    have hθLB12 : (B12 K 2 f).map θL0 = (N0.comap (del 2)).map (a 2) := hθL0_B12
    have hθL0B12le : (B12 K 2 f).map θL0 ≤ rangePurePair R 3 0 := by
      rw [hθL0_B12]
      calc
        (N0.comap (del 2)).map (a 2) ≤ ((P {0, 3}).comap (del 2)).map (a 2) :=
          Subgroup.map_mono (Subgroup.comap_mono hN0P)
        _ = (normPureBlock E 3 {2, 0}).map (a 2) := by rw [hP403]
        _ = rangePurePair R 3 0 := hpair30.symm
    have hcomm : ∀ x ∈ (B12 K 2 f).map θL0,
        ∀ y ∈ (B23 K 2 f).map θ₁₂, x * y = y * x := by
      intro x hx y hy
      have hy' : y ∈ i₂.range := by rwa [hB23θ12] at hy
      exact (commute_of_mem_rangePurePair_of_mem_pair E hqF ha hR
        (i := 3) (j := 0) (k := 1) (l := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (hθL0B12le hx) (hi2_R hy')).eq
    have h0 : ∀ x ∈ (B12 K 2 f).map θL0, ∀ b,
        x * i₂ b = i₂ b * x ∧ x * i₃ b = i₃ b * x := by
      intro x hx b
      have hxpair := hθL0B12le hx
      exact ⟨(commute_of_mem_rangePurePair_of_mem_pair E hqF ha hR
          (i := 3) (j := 0) (k := 1) (l := 2)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          hxpair (hi2_R ⟨b, rfl⟩)).eq,
        (commute_of_mem_rangePurePair_of_mem_pair E hqF ha hR
          (i := 3) (j := 0) (k := 1) (l := 2)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          hxpair (hi3_R ⟨b, rfl⟩)).eq⟩
    exact assemble θL0 hL0 hM hcomm h0 hθLB12
  · have hM : (B23 K 2 f).map θLτ = (B12 K 2 f).map θ₁₂ := by
      rw [hθLτ_B23, hY2N1tw hXtw, hB12θ12]
    have hθLB12 : (B12 K 2 f).map θLτ = (N0.comap (del 2)).map (a 2) := hθLτ_B12
    have hθLτB12le : (B12 K 2 f).map θLτ ≤ rangePurePair R 3 0 := by
      rw [hθLτ_B12]
      calc
        (N0.comap (del 2)).map (a 2) ≤ ((P {0, 3}).comap (del 2)).map (a 2) :=
          Subgroup.map_mono (Subgroup.comap_mono hN0P)
        _ = (normPureBlock E 3 {2, 0}).map (a 2) := by rw [hP403]
        _ = rangePurePair R 3 0 := hpair30.symm
    have hcomm : ∀ x ∈ (B12 K 2 f).map θLτ,
        ∀ y ∈ (B23 K 2 f).map θ₁₂, x * y = y * x := by
      intro x hx y hy
      have hy' : y ∈ i₂.range := by rwa [hB23θ12] at hy
      exact (commute_of_mem_rangePurePair_of_mem_pair E hqF ha hR
        (i := 3) (j := 0) (k := 1) (l := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (hθLτB12le hx) (hi2_R hy')).eq
    have h0 : ∀ x ∈ (B12 K 2 f).map θLτ, ∀ b,
        x * i₂ b = i₂ b * x ∧ x * i₃ b = i₃ b * x := by
      intro x hx b
      have hxpair := hθLτB12le hx
      exact ⟨(commute_of_mem_rangePurePair_of_mem_pair E hqF ha hR
          (i := 3) (j := 0) (k := 1) (l := 2)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          hxpair (hi2_R ⟨b, rfl⟩)).eq,
        (commute_of_mem_rangePurePair_of_mem_pair E hqF ha hR
          (i := 3) (j := 0) (k := 1) (l := 2)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          hxpair (hi3_R ⟨b, rfl⟩)).eq⟩
    exact assemble θLτ hLτ hM hcomm h0 hθLB12


end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
