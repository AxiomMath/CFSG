module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightSp8
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cInspSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cMult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

@[expose] def LieSEightSpInner : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 8 →
    ∀ x : StatedProj (StatedSp 4 K), x ^ 3 = 1 → x ≠ 1 →
      ∀ J : Subgroup (StatedProj (StatedSp 4 K)), GLAPComponent 3 (fixSub (MulAut.conj x)) J →
        catalogIs (PSimple 3 J) S8.L84.isSp48 →
          ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedProj (StatedSp 4 K))),
            ∃ j ∈ J, ∀ y ∈ J, g * y * g⁻¹ = j * y * j⁻¹

theorem lieSEight_innerOnMod_of_conj {Y P : Type} [Group Y] [Finite Y] [Group P] (eY : Y ≃* P)
    {τ : MulAut Y} {J : Subgroup Y} {g₀ : P} (hτ : MulAut.congr eY τ = MulAut.conj g₀)
    (hj : ∃ j ∈ J.map eY.toMonoidHom, ∀ y ∈ J.map eY.toMonoidHom, g₀ * y * g₀⁻¹ = j * y * j⁻¹) :
    InnerOnMod 3 J τ := by
  obtain ⟨j, hjJ, hjy⟩ := hj
  obtain ⟨j₀, hj₀J, rfl⟩ := Subgroup.mem_map.1 hjJ
  set gY : Y := eY.symm g₀ with hgY
  have hτy : ∀ y, τ y = gY * y * gY⁻¹ := by
    intro y
    apply eY.injective
    have h : eY (τ (eY.symm (eY y))) = (MulAut.conj g₀) (eY y) := DFunLike.congr_fun hτ (eY y)
    rw [MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
    rw [map_mul, map_mul, map_inv, hgY, MulEquiv.apply_symm_apply]
    exact h
  have h1 : ∀ y ∈ J, gY * y * gY⁻¹ = j₀ * y * j₀⁻¹ := by
    intro y hy
    apply eY.injective
    have h2 := hjy (eY y) (Subgroup.mem_map_of_mem _ hy)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hgY, MulEquiv.apply_symm_apply]
    exact h2
  have hmem : ∀ y ∈ J, gY * y * gY⁻¹ ∈ J := fun y hy => by
    rw [h1 y hy]
    exact J.mul_mem (J.mul_mem hj₀J hy) (J.inv_mem hj₀J)
  let f : ↥J → ↥J := fun z => ⟨gY * (z : Y) * gY⁻¹, hmem z z.2⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f] at this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hfinj
  refine ⟨j₀, hj₀J, fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := hfsurj ⟨y, hy⟩
  have hz' : gY * (z : Y) * gY⁻¹ = y := congrArg Subtype.val hz
  have h3 : y = j₀ * (z : Y) * j₀⁻¹ := by rw [← h1 z z.2, hz']
  have h4 : τ.symm y = (z : Y) := (MulEquiv.symm_apply_eq τ).2 (by rw [hτy]; exact hz'.symm)
  have h5 : (z : Y) = j₀⁻¹ * y * j₀ := by rw [h3]; group
  rw [h4, h5, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem LieSEightWitIn.of_map_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {C : Subgroup G}
    (h : LieSEightWitIn (C.map e.toMonoidHom)) : LieSEightWitIn C := by
  have h' := LieSEightWitIn.map e.symm.toMonoidHom e.symm.injective h
  rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from
    MonoidHom.ext fun g => e.symm_apply_apply g, Subgroup.map_id] at h'

theorem lieSEightAt_B4 (hGA : CFSG.Open.GriessAllModelsStatement) (hStar : LieSEightSpInner) :
    LieSEightAt fun d => ∃ q, d = .B 4 q := by
  rintro Y _ _ hY - - ⟨d, hv⟩ ⟨q, rfl⟩ hc hf ⟨e⟩ ξ hξ3 hξ1 hin J hJ hT ⟨τ, hτ3, hcomm, hnot, hrk⟩
  show False
  have hq8 : q.card = 8 := hf
  have hp2 : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_B 4 q).symm.trans hc
  have hexp : q.exponent = 3 := by
    have h := q.card_def
    rw [hq8, hp2] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : 8 = 2 ^ 3))
  rcases CFSG.Models.lieModel_B 4 q hv e with hm | hm
  swap
  · rw [hp2, hexp] at hm
    exact absurd hm.1.2.2.2 (by norm_num)
  rw [hp2, hexp] at hm
  have hZ : Subgroup.center Y = ⊥ := by
    have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hY hm (a := 1) (b := 1)
      (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (hdvd.trans (by norm_num)))
  obtain ⟨-, hsc | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨φ⟩⟩ := hsc
  letI := hKfield
  haveI := hKfin
  have hK8 : Nat.card K = 8 := by rw [hKcard]; norm_num
  haveI : CharP K 2 := lieSEight_charP_two hK8
  have hπ : Function.Bijective (QuotientGroup.mk' (Subgroup.center Y)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZ]),
      QuotientGroup.mk'_surjective _⟩
  let eY : Y ≃* StatedProj (StatedSp 4 K) :=
    (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center Y)) hπ).trans φ
  have hrel : MulAut.congr eY ξ = MulAut.congr φ (inducedAut ξ) := by
    ext p
    obtain ⟨y, rfl⟩ := eY.surjective p
    have h1 : eY y = φ (QuotientGroup.mk y) := rfl
    show eY (ξ (eY.symm (eY y))) = φ (inducedAut ξ (φ.symm (eY y)))
    rw [MulEquiv.symm_apply_apply, h1, MulEquiv.symm_apply_apply]
    rfl
  have hβ : MulAut.congr eY ξ ∈ innAutDerived (StatedProj (StatedSp 4 K)) := by
    rw [hrel]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr φ).2 hin
  have hβ3 : MulAut.congr eY ξ ^ 3 = 1 := by rw [← map_pow, hξ3, map_one]
  obtain ⟨x₀, hx₀⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.mem_inner_of_mem_innAutDerived_statedSp
    Nat.prime_three (by norm_num) Nat.prime_two (f := 3) (by norm_num) hKcard (by norm_num)
    (by norm_num) hβ hβ3
  have hZP : Subgroup.center (StatedProj (StatedSp 4 K)) = ⊥ := by
    rw [← Subgroup.map_center_eq eY, hZ, Subgroup.map_bot]
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hZP
  have hx₀3 : x₀ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hx₀, hβ3, map_one]
  have hτ3' : MulAut.congr eY τ ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
  have hcommP : MulAut.congr eY τ * MulAut.congr eY ξ =
      MulAut.congr eY ξ * MulAut.congr eY τ := by
    rw [← map_mul, ← map_mul, hcomm.eq]
  by_cases hinn : IsInnerAut (MulAut.congr eY τ)
  ·
    obtain ⟨g₀, hg₀⟩ := hinn
    have hg₀x : g₀ ∈ Subgroup.centralizer ({x₀} : Set (StatedProj (StatedSp 4 K))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      apply hinj
      rw [map_mul, map_mul]
      show (MulAut.conj h) * (MulAut.conj g₀) = (MulAut.conj g₀) * (MulAut.conj h)
      rw [hg₀, hx₀]
      exact hcommP.symm
    have hcomp : GLAPComponent 3 (fixSub (MulAut.conj x₀)) (J.map eY.toMonoidHom) := by
      rw [hx₀]
      exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport eY ξ hJ
    have hcat : catalogIs (PSimple 3 (J.map eY.toMonoidHom)) S8.L84.isSp48 :=
      (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff (f := eY.toMonoidHom)
        eY.injective 3 J _).2 hT
    have hx₀1 : x₀ ≠ 1 := by
      intro h1
      apply hξ1
      apply (MulAut.congr eY).injective
      rw [← hx₀, h1, map_one, map_one]
    obtain ⟨j, hjJ, hjy⟩ := hStar K hK8 x₀ hx₀3 hx₀1 _ hcomp hcat g₀ hg₀x
    exact hnot (lieSEight_innerOnMod_of_conj eY hg₀.symm ⟨j, hjJ, hjy⟩)
  ·
    have hW := lieSEight_sp8_outer hK8 hτ3' hinn
    rw [← CFSG.LocalAnalysis.GLTheoremA.Y10F.fixSubgroup_map_congr eY τ] at hW
    obtain ⟨U, E, hU1, hU2, hE, hc27, hUC, hEC, hEN⟩ := LieSEightWitIn.of_map_equiv eY hW
    have hZE : E ⊓ Subgroup.center Y = ⊥ := by rw [hZ]; exact inf_bot_eq E
    have hne : ∀ a ∈ E, τ ≠ MulAut.conj a := by
      intro a _ h
      apply hinn
      refine ⟨eY a, ?_⟩
      rw [h]
      exact (CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj eY a).symm
    have h9 := hrk U hU1 hU2 hUC E hEC hEN hE hZE hne
    exact absurd (hc27.trans h9) (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
