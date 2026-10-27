module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec
public import CFSG.GH74.M12.HypGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.A5Index

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_cent_shape {G : Type} [Group G] [Finite G] {Y M : Subgroup G}
    (ψ : ↥Y →* alternatingGroup (Fin 5)) (hker : ∀ l : ↥Y, ψ l = 1 ↔ (l : G) ∈ M)
    (hMY : M ≤ Y) (hM : IsElemTwo 4 M) {t : G} (ht : t ∈ M) (hC : Nat.card ↥(Gx t ⊓ Y) = 96) :
    IsExtensionShape ↥(Gx t ⊓ Y) (Elem2 4) (Sym 3) := by
  haveI hcommM : IsMulCommutative ↥M := hM.1.1
  have hMGx : M ≤ Gx t := by
    intro m hm
    rw [mem_Gx]
    exact congrArg Subtype.val (mul_comm' (⟨t, ht⟩ : ↥M) (⟨m, hm⟩ : ↥M))
  have hMC : M ≤ Gx t ⊓ Y := le_inf hMGx hMY
  let ψC : ↥(Gx t ⊓ Y) →* alternatingGroup (Fin 5) :=
    ψ.comp (Subgroup.inclusion (inf_le_right : Gx t ⊓ Y ≤ Y))
  let N : Subgroup ↥(Gx t ⊓ Y) := ψC.ker
  have hkerN : ∀ c : ↥(Gx t ⊓ Y), c ∈ N ↔ (c : G) ∈ M := by
    intro c
    change ψ (Subgroup.inclusion (inf_le_right : Gx t ⊓ Y ≤ Y) c) = 1 ↔ (c : G) ∈ M
    rw [hker (Subgroup.inclusion (inf_le_right : Gx t ⊓ Y ≤ Y) c)]
    simp
  have hNM : N = M.subgroupOf (Gx t ⊓ Y) := by
    ext c
    rw [Subgroup.mem_subgroupOf]
    exact hkerN c
  have hsqM : ∀ x : ↥M, x * x = 1 := by
    intro x
    apply Subtype.ext
    have hx := hM.1.2 (x : G) x.2
    rw [pow_two] at hx
    exact hx
  obtain ⟨eM⟩ := TwoHSData.nonempty_mulEquiv_elem2 4 hsqM hM.2
  have eN : ↥N ≃* Elem2 4 :=
    (MulEquiv.subgroupCongr hNM).trans ((Subgroup.subgroupOfEquivOfLe hMC).trans eM)
  have hN16 : Nat.card ↥N = 16 := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr hNM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMC).toEquiv, hM.2]
    norm_num
  have hq : Nat.card ↥ψC.range = 6 := by
    have h1 := Subgroup.card_ker_mul_card_range ψC
    rw [show Nat.card ↥ψC.ker = 16 from hN16, hC] at h1
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := y4a_exists_not_comm_of_card_six hq
  have hab : (⟨x, hx⟩ : ↥ψC.range) * ⟨y, hy⟩ ≠ ⟨y, hy⟩ * ⟨x, hx⟩ := by
    intro h
    exact hxy (by simpa using congrArg Subtype.val h)
  obtain ⟨e3⟩ :=
    CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six hq ⟨x, hx⟩ ⟨y, hy⟩ hab
  exact ⟨N, ψC.normal_ker, ⟨eN⟩, ⟨(QuotientGroup.quotientKerEquivRange ψC).trans e3⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
