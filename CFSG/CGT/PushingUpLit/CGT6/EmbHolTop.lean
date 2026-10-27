module

public import CFSG.CGT.PushingUpLit.CGT6.EmbDictBase

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin

section YuTop

variable {V : Type} [CommGroup V] (X : Subgroup (MulAut V))

theorem isPGroup_ker_yuProj (hV : ∀ v : V, v ^ 2 = 1) : IsPGroup 2 ↥(yuProj X).ker := by
  rintro ⟨x, hx⟩
  rw [ker_yuProj] at hx
  obtain ⟨u, rfl⟩ := hx
  exact ⟨1, Subtype.ext (by simpa using yuInc_sq X hV u)⟩

theorem pCore_yuHol (hV : ∀ v : V, v ^ 2 = 1) :
    pCore 2 ↥(yuHol X) = (pCore 2 ↥X).comap (yuProj X) := by
  apply le_antisymm
  · set P := pCore 2 ↥(yuHol X) with hP
    have hPn : P.Normal := inferInstance
    have hP2 : IsPGroup 2 ↥P := pCore_isPGroup (p := 2) (G := ↥(yuHol X))
    have hSn : (P.map (yuProj X)).Normal := hPn.map _ (yuProj_surjective X)
    have hS2 : IsPGroup 2 ↥(P.map (yuProj X)) := hP2.map _
    have hle : P.map (yuProj X) ≤ pCore 2 ↥X := le_sSup ⟨hSn, hS2⟩
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  · have hNn : ((pCore 2 ↥X).comap (yuProj X)).Normal := Subgroup.normal_comap _
    have hN2 : IsPGroup 2 ↥((pCore 2 ↥X).comap (yuProj X)) :=
      IsPGroup.comap_of_ker_isPGroup (pCore_isPGroup (p := 2) (G := ↥X)) (yuProj X)
        (isPGroup_ker_yuProj X hV)
    exact le_sSup ⟨hNn, hN2⟩

@[expose] def yuLam : ↥(yuHol X) →* ↥X ⧸ pCore 2 ↥X :=
  (QuotientGroup.mk' (pCore 2 ↥X)).comp (yuProj X)

theorem yuLam_surjective : Function.Surjective (yuLam X) :=
  (QuotientGroup.mk'_surjective _).comp (yuProj_surjective X)

theorem ker_yuLam (hV : ∀ v : V, v ^ 2 = 1) : (yuLam X).ker = pCore 2 ↥(yuHol X) := by
  rw [pCore_yuHol X hV]
  ext x
  simp [yuLam, QuotientGroup.eq_one_iff]

@[expose] noncomputable def yuTop (hV : ∀ v : V, v ^ 2 = 1) :
    (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) ≃* (↥X ⧸ pCore 2 ↥X) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_yuLam X hV).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (yuLam_surjective X))

@[expose] noncomputable def yuTop' (hV : ∀ v : V, v ^ 2 = 1) (h : pCore 2 ↥X = ⊥) :
    (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) ≃* ↥X :=
  (yuTop X hV).trans ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot)

theorem yuTop'_image (hV : ∀ v : V, v ^ 2 = 1) (h : pCore 2 ↥X = ⊥) (Y : Subgroup (MulAut V)) :
    (((yuHol Y).subgroupOf (yuHol X)).map (QuotientGroup.mk' (pCore 2 ↥(yuHol X)))).map
      (yuTop' X hV h).toMonoidHom = Y.subgroupOf X := by
  ext α
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
    exact hz.2
  · intro hα
    refine ⟨_, ⟨yuSec X α, ⟨one_mem _, hα⟩, rfl⟩, rfl⟩

end YuTop

section PCoreBot

theorem pCore_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ IsPGroup 2 S) : pCore 2 S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 S) with h0 | h0
  · exact h0
  · exfalso
    apply h
    have := pCore_isPGroup (p := 2) (G := S)
    rw [h0] at this
    exact IsPGroup.of_surjective this (Subgroup.topEquiv (G := S)).toMonoidHom
      (Subgroup.topEquiv (G := S)).surjective

theorem pCore_eq_bot_of_equiv {X S : Type} [Group X] [Group S] (e : X ≃* S)
    (h : pCore 2 S = ⊥) : pCore 2 X = ⊥ := by
  have := pCore_map_iso 2 e
  rw [h] at this
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ (⊥ : Subgroup S) := this ▸ ⟨x, hx, rfl⟩
  simpa using h1

end PCoreBot

end CFSG.CGT.PushingUpLit.CGT6
