module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Alpha
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Rho
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LThmDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.I21L Module

section CommImg

variable {W : Type*} [Group W] [Finite W]

theorem card_commImg_eq (hW : ElemAb2 W) (j : MulAut W) :
    Nat.card (commImg j) = 2 ^ rk (EVec.mulAutToGL hW j) := by
  rw [P5.commImg_eq_range_twistHom hW.comm hW.sq j, ← EVec.natCard_twist hW j]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩

end CommImg

section Concl

variable {G : Type} [Group G] [Finite G]
  {d : Data G} {z₀ : G}

theorem Ja_eq_map {x : ↥(Ialpha d)} (hX : (Alpha d (Xg d)).subgroupOf (Ialpha d) = zpowers x) :
    Ja d = (normalClosure ({x} : Set ↥(Ialpha d))).map (Ialpha d).subtype := by
  unfold Ja
  rw [hX, zpowers_eq_closure, normalClosure_closure_eq_normalClosure]

theorem Ja_subgroupOf {x : ↥(Ialpha d)} (hX : (Alpha d (Xg d)).subgroupOf (Ialpha d) = zpowers x) :
    (Ja d).subgroupOf (Ialpha d) = normalClosure ({x} : Set ↥(Ialpha d)) := by
  rw [Ja_eq_map hX]
  exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

noncomputable def JaEquiv {x : ↥(Ialpha d)}
    (hX : (Alpha d (Xg d)).subgroupOf (Ialpha d) = zpowers x) :
    ↥(Ja d) ≃* ↥(normalClosure ({x} : Set ↥(Ialpha d))) :=
  (MulEquiv.subgroupCongr (Ja_eq_map hX)).trans
    (Subgroup.equivMapOfInjective _ (Ialpha d).subtype Subtype.val_injective).symm

theorem elemOf_alpha_t {t : ↥(Ialpha d)} (htα : (t : MulAut ↥(Ws d)) = alpha d d.t) :
    elemOf (Ialpha d) (alpha d d.t) = t := by
  have h : alpha d d.t ∈ Ialpha d := htα ▸ t.2
  unfold elemOf
  rw [dif_pos h]
  exact Subtype.ext htα.symm

theorem exists_sylow_Alpha {S : Subgroup G} (hS : fusionIsSylowIn 2 S (Ig d)) :
    ∃ P : Sylow 2 ↥(Ialpha d), ∀ y : ↥(Ialpha d), y ∈ P ↔ (y : MulAut ↥(Ws d)) ∈ Alpha d S := by
  have hSle : S ≤ Ig d := hS.1
  let Sg : Sylow 2 ↥(Ig d) :=
    { toSubgroup := S.subgroupOf (Ig d)
      isPGroup' := IsPGroup.of_equiv hS.2.1 (Subgroup.subgroupOfEquivOfLe hSle).symm
      is_maximal' := by
        intro Q hQ hSQ
        have hP : IsPGroup 2 (Q.map (Ig d).subtype) :=
          IsPGroup.of_equiv hQ (Subgroup.equivMapOfInjective Q (Ig d).subtype Subtype.val_injective)
        have hPle : Q.map (Ig d).subtype ≤ Ig d := by
          rintro _ ⟨q, -, rfl⟩
          exact q.2
        have hSP : S ≤ Q.map (Ig d).subtype := fun s hs =>
          ⟨⟨s, hSle hs⟩, hSQ (Subgroup.mem_subgroupOf.2 hs), rfl⟩
        have hEq := hS.2.2 _ hPle hP hSP
        calc Q = (Q.map (Ig d).subtype).comap (Ig d).subtype :=
              (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective Q).symm
          _ = S.subgroupOf (Ig d) := by rw [hEq]; rfl }
  refine ⟨Sylow.mapSurjective (alphaHom_surjective d) Sg, fun y => ?_⟩
  change y ∈ (S.subgroupOf (Ig d)).map (alphaHom d) ↔ _
  rw [mem_Alpha_iff hSle, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.1, Subgroup.mem_subgroupOf.1 hg, rfl⟩
  · rintro ⟨g, hgS, hg⟩
    exact ⟨⟨g, hSle hgS⟩, Subgroup.mem_subgroupOf.2 hgS, Subtype.ext hg⟩

theorem p21_concl (h09 : Node09 d z₀) (hW : ElemAb2 ↥(Ws d)) {t x : ↥(Ialpha d)}
    (htα : (t : MulAut ↥(Ws d)) = alpha d d.t)
    (hX : (Alpha d (Xg d)).subgroupOf (Ialpha d) = zpowers x)
    (hdich : (Nonempty (↥(normalClosure ({x} : Set ↥(Ialpha d))) ≃* alternatingGroup (Fin 6)) ∧
        PGLTwoSquareOuter (normalClosure ({x} : Set ↥(Ialpha d))) t) ∨
      Nonempty (↥(normalClosure ({x} : Set ↥(Ialpha d))) ≃*
        Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))
    (hP : Thm107P (rhoI d hW) t) : Node21 d z₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, -, -⟩ := h09
  have htT : d.t ∈ sylT d := by
    rw [h10]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hsq : ∀ (F : Subgroup (MulAut ↥(Ws d))), F ≤ Ialpha d → IsElemAbelian 2 F →
      (∀ f ∈ F.subgroupOf (Ialpha d), f * f = 1) ∧
        Nat.card (F.subgroupOf (Ialpha d)) = Nat.card F := by
    intro F hFI hFab
    refine ⟨fun f hf => ?_, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFI).toEquiv⟩
    have := hFab.2 f.1 (Subgroup.mem_subgroupOf.1 hf)
    exact Subtype.ext (by simpa [pow_two] using this)
  refine ⟨?_, ?_, hP.2.2.2.1, ?_⟩
  · rcases hdich with ⟨⟨e⟩, hpgl⟩ | ⟨e⟩
    · left
      refine ⟨⟨(JaEquiv hX).trans e⟩, ?_⟩
      rw [Ja_subgroupOf hX, elemOf_alpha_t htα]
      exact hpgl
    · obtain ⟨e⟩ := e
      exact Or.inr ⟨(JaEquiv hX).trans e⟩
  · intro S hS
    obtain ⟨hS1, hS2⟩ := hS
    have hSle : S ≤ Ig d := hS1.1
    obtain ⟨P, hPm⟩ := exists_sylow_Alpha hS1
    have htS : alpha d d.t ∈ Alpha d S := (mem_Alpha_iff hSle).2 ⟨d.t, hS2 htT, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j hj hj2 hj1
      have h2 : (⟨j, Alpha_le_Ialpha hSle hj⟩ : ↥(Ialpha d)) *
          ⟨j, Alpha_le_Ialpha hSle hj⟩ = 1 := Subtype.ext hj2
      have h1 : (⟨j, Alpha_le_Ialpha hSle hj⟩ : ↥(Ialpha d)) ≠ 1 := fun h =>
        hj1 (congrArg Subtype.val h)
      have hrk := hP.1 _ h2 h1
      rw [card_commImg_eq hW j]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ rk (EVec.mulAutToGL hW j) := Nat.pow_le_pow_right (by norm_num) hrk
    · intro F hFS hFab hF4
      have hFI : F ≤ Ialpha d := hFS.trans (Alpha_le_Ialpha hSle)
      obtain ⟨hF'sq, hF'card⟩ := hsq F hFI hFab
      obtain ⟨j, hj, -, hrk⟩ := hP.2.1 _ hF'sq (hF'card.trans hF4)
      refine ⟨j.1, Subgroup.mem_subgroupOf.1 hj, ?_⟩
      rw [card_commImg_eq hW j.1]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ rk (EVec.mulAutToGL hW j.1) := Nat.pow_le_pow_right (by norm_num) hrk
    · ext y
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hy, i, hi, rfl⟩
        have htP : t ∈ P := (hPm t).2 (htα ▸ htS)
        have hgm : (⟨i, hi⟩ : ↥(Ialpha d)) * t * (⟨i, hi⟩ : ↥(Ialpha d))⁻¹ ∈ P := by
          refine (hPm _).2 ?_
          show i * (t : MulAut ↥(Ws d)) * i⁻¹ ∈ Alpha d S
          rw [htα]
          exact hy
        obtain ⟨s, hsP, hs⟩ := hP.2.2.1 P htP _ hgm
        refine ⟨s.1, (hPm s).1 hsP, ?_⟩
        have := congrArg Subtype.val hs
        change (s : MulAut ↥(Ws d)) * (t : MulAut ↥(Ws d)) * (s : MulAut ↥(Ws d))⁻¹ =
          i * (t : MulAut ↥(Ws d)) * i⁻¹ at this
        rw [htα] at this
        exact this.symm
      · rintro ⟨s, hs, rfl⟩
        exact ⟨mul_mem (mul_mem hs htS) (inv_mem hs), s, Alpha_le_Ialpha hSle hs, rfl⟩
  · intro S hS F hFS hFab
    obtain ⟨hS1, -⟩ := hS
    have hFI : F ≤ Ialpha d := hFS.trans (Alpha_le_Ialpha hS1.1)
    obtain ⟨hF'sq, hF'card⟩ := hsq F hFI hFab
    rw [← hF'card]
    exact hP.2.2.2.2 _ hF'sq

end Concl

end CFSG.LocalAnalysis.EvenBN.Tits.N
