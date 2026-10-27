module

public import CFSG.CGT.PushingUpLit.BHS5.Gen
public import CFSG.CGT.PushingUpLit.BHS.ThreeSixD

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS
open CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits

section General

variable {G : Type*} [Group G]

theorem le_normalizer_iSup {P : Subgroup G} {S : Set (Subgroup G)}
    (h : ∀ A ∈ S, ∀ g ∈ P, conjSub g A ∈ S) :
    P ≤ Subgroup.normalizer ((⨆ A ∈ S, A : Subgroup G) : Set G) := by
  have key : ∀ g ∈ P, ∀ y ∈ (⨆ A ∈ S, A : Subgroup G), g * y * g⁻¹ ∈ (⨆ A ∈ S, A : Subgroup G) := by
    intro g hg y hy
    have hle : conjSub g (⨆ A ∈ S, A : Subgroup G) ≤ ⨆ A ∈ S, A := by
      rw [conjSub, Subgroup.map_iSup]
      refine iSup_le fun A => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hA => ?_
      exact le_iSup₂ (f := fun B (_ : B ∈ S) => B) _ (h A hA g hg)
    exact hle ⟨y, hy, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
  have := key g⁻¹ (P.inv_mem hg) _ hy
  simpa [mul_assoc] using this

end General

variable {V : Type} [CommGroup V] [Finite V] {P T M : Subgroup (MulAut V)}

theorem Hyp51.eq_bot_of_normal_le_M (h : Hyp51 P T M) {N X : Subgroup (MulAut V)} (hNP : N ≤ P)
    (hNn : P ≤ Subgroup.normalizer (N : Set (MulAut V))) (hNM : N ≤ M) (hXN : X ≤ N)
    (hX : IsPGroup 2 X) : X = ⊥ := by
  have hn := three_three_a h.minpar.syl h.minpar.lt_P h.minpar.max hNP hNn hNM
  have hNT2 : IsPGroup 2 ↥(N ⊓ T) := h.minpar.syl.2.1.to_le inf_le_right
  have hle : N ⊓ T ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hNP) hn hNT2
  rw [h.o2, le_bot_iff] at hle
  have hS := FourTwoTools.isSylowOf_inf_of_le_normalizer h.minpar.syl hNP hNn
  obtain ⟨k, -, hk⟩ := Glauberman.exists_conj_le_of_isSylowOf hS hX hXN
  rw [hle] at hk
  have hk' : conjSub k X ≤ ⊥ := hk
  have := (conjSub_le_conjSub_iff k (H := X) (K := ⊥)).1 (by simpa [conjSub] using hk')
  exact le_bot_iff.1 this

section Gen51

variable (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1)

include h hV

theorem dCore_eq_empty : dCore P (Hyp51.offSet P) M = ∅ := by
  have h43 := h.hyp43 hV
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  set K : Subgroup (MulAut V) := ⨆ C ∈ dCore P (Hyp51.offSet P) M, C with hK
  have hKP : K ≤ P := iSup₂_le fun C hC => h43.le C hC.1
  have hKn : P ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
    refine le_normalizer_iSup fun C hC g hg => ⟨h43.conj_mem C hC.1 g hg, fun g' hg' => ?_⟩
    have h1 := hC.2 (g⁻¹ * g') (P.mul_mem (P.inv_mem hg) hg')
    rw [show g' = g * (g⁻¹ * g') by group, conjSub_mul]
    exact conjSub_mono g h1
  have hKM : K ≤ M := iSup₂_le fun C hC => by
    simpa [conjSub_one] using hC.2 1 P.one_mem
  exact h43.ne_bot A hA.1 (Hyp51.eq_bot_of_normal_le_M h hKP hKn hKM (le_iSup_mem hA)
    (isPGroup_of_isElemAbelian2 (h43.elemAb A hA.1)))

theorem sup_eq : (⨆ A ∈ Hyp51.offSet P, A) ⊔ T = P := by
  have h43 := h.hyp43 hV
  obtain ⟨A, hA⟩ := h.exists_mem_dInter
  have hle : (⨆ A ∈ Hyp51.offSet P, A) ≤ P := iSup₂_le fun B hB => h43.le B hB
  refine h.minpar.sup_eq_of_not_le hle fun hM => ?_
  have hn : P ≤ Subgroup.normalizer ((⨆ A ∈ Hyp51.offSet P, A : Subgroup (MulAut V)) :
      Set (MulAut V)) := le_normalizer_iSup fun B hB g hg => h43.conj_mem B hB g hg
  exact h43.ne_bot A hA.1 (Hyp51.eq_bot_of_normal_le_M h hle hn hM (le_iSup_mem hA.1)
    (isPGroup_of_isElemAbelian2 (h43.elemAb A hA.1)))

end Gen51

end CFSG.CGT.PushingUpLit.BHS5
