module

public import CFSG.ClassicalInvolution.Q3.Q3TKStmt
public import CFSG.ClassicalInvolution.Q3.Q3TKTri
public import CFSG.ClassicalInvolution.Q3.Q3TJFin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification
open scoped MatrixGroups

theorem three_mem_of_component (hD4 : D4OuterThree3) {Y : Type} [Group Y] [Finite Y]
    (hBelow : CIT3Below (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥) {z : Y}
    {L : Subgroup Y} (hz : IsClassicalMember3 L z) {T : Subgroup Y} (hT : IsComponentOf T ⊤)
    (hTL : T ⊔ L = ⊤) (hgen : Subgroup.normalClosure (L : Set Y) = ⊤)
    (hconn : NonCommConnected (Q3B.conjClass L)) [hTn : T.Normal]
    (hCT : Subgroup.centralizer (T : Set Y) = ⊥) (hZ : Subgroup.center T = ⊥)
    {c : CompData} (hc : c.Valid) (f : c.G →* T) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center c.G) :
    ∀ x ∈ L, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ T := by
  intro x hx ⟨k, hk⟩
  have hqs : CFSG.Open.IsQuasisimple T := hT.2.2
  have hodd : Odd (orderOf (MulAut.conjNormal x : MulAut T)) :=
    (Odd.pow (by decide : Odd 3)).of_dvd_nat (hk ▸ orderOf_map_dvd _ x)
  have hinner : ∀ g : T, (MulAut.conjNormal x : MulAut T) = MulAut.conj g → x ∈ T :=
    fun g hg => (eq_of_conjNormal_eq_conj hCT hg) ▸ g.2
  rcases hc with ⟨t, n, ht, hadm, rfl⟩ | rfl | rfl
  · rcases steinbergOddAut3_of_PSU steinbergOddAut3PSU_proved t n ht hadm T hqs hZ f hf hker _
      hodd with ⟨g, hg⟩ | ⟨rfl, rfl⟩ | rfl
    · exact hinner g hg
    · exact hD4 Y hBelow hO z L hz T hT hTL hgen hconn hTn hCT f hf hker x hx ⟨k, hk⟩
    · have hn : n = 0 := hadm.2.2
      subst hn
      have hinj : Function.Injective f := by
        rw [← MonoidHom.ker_eq_bot_iff]
        rw [exc3_center_trialityD4 0 Nat.prime_three] at hker
        exact le_bot_iff.mp hker
      exact le_of_socle_td4 hz hCT (MulEquiv.ofBijective f ⟨hinj, hf⟩) hx
  · exfalso
    have hs : Group.IsSolvable SL(2, ZMod 3) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [natCard_sl2Three]; norm_num)
    exact not_isSolvable_of_quasisimple hqs (Group.isSolvable_of_surjective hf)
  · have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [Sporadic.Schreier.m11_center_eq_bot'] at hker
      exact le_bot_iff.mp hker
    let e := MulEquiv.ofBijective f ⟨hinj, hf⟩
    have hinn := Sporadic.Schreier.inner_eq_top_of_card_le
      Sporadic.Schreier.m11_center_eq_bot' Sporadic.Schreier.m11_mulAut_card
    have hβ : (MulAut.congr e).symm (MulAut.conjNormal x : MulAut T) ∈
        OuterAutomorphisms.inner _ := by
      rw [hinn]
      exact Subgroup.mem_top _
    obtain ⟨m, hm⟩ := hβ
    refine hinner (e m) ?_
    rw [← OuterAutomorphisms.congr_conj e m, hm, MulEquiv.apply_symm_apply]

theorem almostSimpleOuter3_of (hMF : MemberFreeSocleOuter3) (hD4 : D4OuterThree3) :
    AlmostSimpleOuter3 := by
  intro Y _ _ hBelow hO z L hz T hT hTL hgen hconn hTn hCT
  refine isClassicalMember3_inf_of_three_mem hz fun x hx h3 => ?_
  by_cases hTY : T = ⊤
  · rw [hTY]
    exact Subgroup.mem_top x
  by_cases hmem : ∃ (z' : T) (L' : Subgroup T), IsClassicalMember3 L' z'
  · obtain ⟨z', L', hL'⟩ := hmem
    have hqs : CFSG.Open.IsQuasisimple T := hT.2.2
    have hZ : Subgroup.center T = ⊥ := by
      refine eq_bot_iff.mpr fun c hc => ?_
      have hc' : (c : Y) ∈ Subgroup.centralizer (T : Set Y) :=
        Subgroup.mem_centralizer_iff.mpr fun t ht =>
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨t, ht⟩)
      rw [hCT, Subgroup.mem_bot] at hc'
      exact Subgroup.mem_bot.mpr (Subtype.ext hc')
    have hgen' : Subgroup.normalClosure (L' : Set T) = ⊤ := by
      rcases normal_le_center_or_eq_top_qs hqs Subgroup.normalClosure_normal with h | h
      · exfalso
        have h1 := h (Subgroup.subset_normalClosure hL'.mem)
        rw [hZ, Subgroup.mem_bot] at h1
        exact hL'.ne_one h1
      · exact h
    have hcard : Nat.card T < Nat.card Y := by
      rw [← Subgroup.card_top (G := Y)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hTY)
    have hLie := hBelow T hcard _ (Q3B.inClass3_conjClass hL' hgen')
    have hOT := oddCore_eq_bot_of_quasisimple hqs hZ hL'.orderOf_eq_two
    obtain ⟨ι, _, ⟨S⟩⟩ := hLie
    let e : T ⧸ classicalInvolutionOddCore T ≃* T :=
      (QuotientGroup.quotientMulEquivOfEq hOT).trans QuotientGroup.quotientBot
    obtain ⟨i, hi⟩ := exists_eq_top_of_commute hqs hZ
      (fun i => (e.toMonoidHom.comp (S.hom i)).range)
      (fun i j hij x hx y hy => by
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        show e (S.hom i a) * e (S.hom j b) = e (S.hom j b) * e (S.hom i a)
        rw [← map_mul, ← map_mul, S.commute i j hij a b])
      (by
        simp only [MonoidHom.range_comp]
        rw [← Subgroup.map_iSup, S.generate]
        exact Subgroup.map_top_of_surjective _ e.surjective)
    have hsurj : Function.Surjective (e.toMonoidHom.comp (S.hom i)) :=
      MonoidHom.range_eq_top.mp hi
    have hker : (e.toMonoidHom.comp (S.hom i)).ker ≤ Subgroup.center (S.kind i).G := by
      intro y hy
      refine S.ker_le_center i ?_
      rw [MonoidHom.mem_ker] at hy ⊢
      exact (MulEquiv.map_eq_one_iff e).mp hy
    exact three_mem_of_component hD4 hBelow hO hz hT hTL hgen hconn hCT hZ (S.valid i) _ hsurj
      hker x hx h3
  · exact (hMF Y hBelow hO z L hz T hT hTL hgen hconn hTn hCT
      fun z' L' h => hmem ⟨z', L', h⟩).elim

theorem quasisimpleConnected3_of_socle (hMF : MemberFreeSocleOuter3) (hD4 : D4OuterThree3) :
    QuasisimpleConnected3 :=
  quasisimpleConnected3_of_outer (almostSimpleOuter3_of hMF hD4)

end CFSG.ClassicalInvolution.Q3.Q3T
