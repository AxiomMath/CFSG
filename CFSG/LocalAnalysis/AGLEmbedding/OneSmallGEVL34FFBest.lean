module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFRep
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

namespace L34FF

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_mono_two {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem card_mul_card_inf_centralizer_le {V A B W : Subgroup G} (hA : IsMaxElemAbelian V A)
    (hBA : B ≤ A)
    (hW : IsElemAbelian 2 W) (hWV : W ≤ V) :
    Nat.card B * Nat.card (W ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) ≤
      Nat.card A * Nat.card (W ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  set D := W ⊓ Subgroup.centralizer (B : Set G) with hD
  have hDe : IsElemAbelian 2 D := isElemAbelian_mono_two inf_le_left hW
  have hBe : IsElemAbelian 2 B := isElemAbelian_mono_two hBA hA.2.1
  have hBD : B ≤ Subgroup.centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun d hd => (Subgroup.mem_centralizer_iff.mp hd.2 b hb).symm
  have hE := isElemAbelian_two_sup_of_le_centralizer hDe hBe hBD
  have hEV : D ⊔ B ≤ V := sup_le (inf_le_left.trans hWV) (hBA.trans hA.1)
  have hEcard : Nat.card (D ⊔ B : Subgroup G) ≤ Nat.card A := hA.2.2 _ hEV hE
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hBD.trans (Subgroup.centralizer_le_normalizer _))
  have hinf : D ⊓ B ≤ W ⊓ Subgroup.centralizer (A : Set G) := by
    intro x hx
    refine ⟨hx.1.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have := congrArg Subtype.val (hA.2.1.1.is_comm.comm (⟨a, ha⟩ : A) ⟨x, hBA hx.2⟩)
    simpa using this
  calc Nat.card B * Nat.card D = Nat.card (D ⊔ B : Subgroup G) * Nat.card (D ⊓ B : Subgroup G) :=
        by rw [hprod]; ring
    _ ≤ _ := Nat.mul_le_mul hEcard (Subgroup.card_le_of_le hinf)

theorem isBestOffender_map_conjOnto {W X V A : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (W : Set G)) (hW : IsElemAbelian 2 W) (hWV : W ≤ V)
    (hA : IsMaxElemAbelian V A) (hAX : A ≤ X) :
    let _ : CommGroup W := commGroupOfElemAbelian hW
    let _ : Module (ZMod 2) (Additive W) := moduleOfSq fun w => Subtype.ext (hW.2 w w.2)
    CFSG.RankThree.FFModules.IsBestOffender ((autFTwoRep W).comp (autOn X W).subtype)
      ((A.subgroupOf X).map (conjOnto W X hX)) := by
  intro _ _ B hB
  set f := conjOnto W X hX with hf
  set B₀ := A ⊓ (B.comap f).map X.subtype with hB₀
  have hB₀A : B₀ ≤ A := inf_le_left
  have hB₀X : B₀ ≤ X := hB₀A.trans hAX
  have hBeq : (B₀.subgroupOf X).map f = B := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨-, ⟨y, hy, hyx⟩⟩, rfl⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro φ hφ
      obtain ⟨x, hxA, rfl⟩ := hB hφ
      exact ⟨x, ⟨hxA, ⟨x, hφ, rfl⟩⟩, rfl⟩
  have hker : A ⊓ Subgroup.centralizer (W : Set G) ≤ B₀ := by
    intro c hc
    refine ⟨hc.1, ⟨⟨c, hAX hc.1⟩, ?_, rfl⟩⟩
    change f ⟨c, hAX hc.1⟩ ∈ B
    rw [(conjOnto_eq_one_iff hX _).mpr hc.2]
    exact B.one_mem
  rw [← hBeq, card_fixSub_map_conjOnto hX hW hB₀X, card_map_conjOnto hX hB₀X,
    card_fixSub_map_conjOnto hX hW hAX, card_map_conjOnto hX hAX]
  have hinf : B₀ ⊓ Subgroup.centralizer (W : Set G) = A ⊓ Subgroup.centralizer (W : Set G) :=
    le_antisymm (inf_le_inf_right _ hB₀A) (le_inf hker inf_le_right)
  rw [hinf]
  have h1 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (W : Set G)) B₀
  have h2 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (W : Set G)) A
  rw [inf_of_le_left hker] at h1
  rw [inf_of_le_left inf_le_left] at h2
  have hCI := card_mul_card_inf_centralizer_le hA hB₀A hW hWV
  have hpos : 0 < Nat.card (A ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (A ⊓ Subgroup.centralizer (W : Set G)).relIndex B₀ *
        Nat.card (W ⊓ Subgroup.centralizer (B₀ : Set G) : Subgroup G) *
        Nat.card (A ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) =
        Nat.card B₀ * Nat.card (W ⊓ Subgroup.centralizer (B₀ : Set G) : Subgroup G) := by
          rw [← h1]; ring
    _ ≤ Nat.card A * Nat.card (W ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := hCI
    _ = (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A *
        Nat.card (W ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
        Nat.card (A ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) := by
          rw [← h2]; ring

end L34FF

end CFSG.AGLEmbedding
