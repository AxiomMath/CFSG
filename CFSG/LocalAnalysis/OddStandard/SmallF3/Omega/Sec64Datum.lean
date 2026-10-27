module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63ArrowAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec64_arrow_alt [Finite G] (hF : Asc82AutFacts) (hHyp : Asc82Hyp62 G) {x y : G}
    {X Y R : Subgroup G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hXc : IsComponentIn X (centralizer ({x} : Set G)))
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hXY : X ≤ Y) (hcomm : ⁅Y, zpowers x⁆ = Y)
    (hXF : InFStar X) (hYs : IsOmega6Plus Y ∨ IsOmega6Minus Y ∨ IsOmega5 Y ∨ IsL281 Y)
    (hR : IsPGroup 2 ↥R) (hRN : R ≤ normalizer (Y : Set G) ⊓ centralizer (X : Set G)) :
    Sec64Alt X Y R := by
  unfold Sec64Alt
  have hYq : IsQuasisimple ↥Y := hYc.isQuasisimple
  have hshape : IsOm6P Y ∨ IsOm6M Y ∨ IsOm5Q Y ∨ (IsQuasisimple Y ∧ IsL281 Y) := by
    rcases hYs with h | h | h | h
    · exact Or.inl ⟨hYq, h⟩
    · exact Or.inr (Or.inl ⟨hYq, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hYq, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hYq, h⟩))
  have hxN : x ∈ normalizer (Y : Set G) := sec63_mem_normalizer_of_comm hcomm
  have hXin : IsComponentIn X (Y ⊓ centralizer ({x} : Set G)) :=
    hXc.mono (le_inf hXY hXc.le) inf_le_right
  have hH : IsOm6P Y → Hyp62At Y := fun hP => hHyp Y ⟨y, hy, hYc⟩ hP.2
  rcases hF.aut_cent G Y x X hshape hx hxN hXin hXF hH R hR hRN with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.1, h.2.1.2, h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1.2, h.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1.2, h.2.2⟩))

private theorem sec64_cyclic_comm {U : Subgroup G} (hU : IsCyclic ↥U) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) : a * b = b * a := by
  obtain ⟨g, hg⟩ := hU.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have h : (⟨a, ha⟩ : ↥U) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rw [← hi, ← hj]
    exact zpow_mul_comm g i j
  exact congrArg Subtype.val h

theorem sec64_isCyclic_U [Finite G] (h33 : Asc82Lemma33) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {y : G} {Y T : Subgroup G}
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hYC : InCStar Y) (hYF : InFStar Y)
    (hT : IsPGroup 2 ↥T) (hyT : y ∈ T) :
    IsCyclic ↥(T ⊓ centralizer ({y} : Set G) ⊓ centralizer (Y : Set G)) := by
  have hUcyc : IsCyclic ↥(T ⊓ centralizer (Y : Set G)) := sec63_isCyclic_inf h33 hS hYC hYF hT
  have hyH : y ∈ centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYc.1 ha)
  have hyU : y ∈ T ⊓ centralizer (Y : Set G) := ⟨hyT, hyH⟩
  have hUeq : T ⊓ centralizer ({y} : Set G) ⊓ centralizer (Y : Set G) =
      T ⊓ centralizer (Y : Set G) := by
    ext r
    simp only [Subgroup.mem_inf]
    refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (sec64_cyclic_comm hUcyc hyU h).symm
  rw [hUeq]
  exact hUcyc

theorem sec64_datum [Finite G] (h63 : Asc82Lemma63) (hsh : Asc82Shapes) (hP : Asc82Tab6P)
    (hF : Asc82AutFacts) (hCh : Asc82AutCentChain3) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {X : Subgroup G} (hXC : InC X)
    (hXF : InFStar X) :
    InCStar X ∨ ∃ (x y : G) (Y : Subgroup G), orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧
      x ∈ centralizer (X : Set G) ∧ IsComponentIn Y (centralizer ({y} : Set G)) ∧ X ≤ Y ∧
      x ∉ centralizer (Y : Set G) ∧ InCStar Y ∧ InFStar Y ∧
      (IsL29 X ∨ IsL3Eps3 X ∨ IsOmega5 X) ∧
      ∀ R : Subgroup G, IsPGroup 2 ↥R → R ≤ normalizer (Y : Set G) ⊓ centralizer (X : Set G) →
        Sec64Alt X Y R := by
  obtain ⟨Y, hch, hYC⟩ := exists_inCStar_of_inC hXC
  have hYF : InFStar Y := inFStar_of_walterChain hS.a2 hch hXF
  have hpl : PlainChain X Y := sec64_plain_of_chain h63 hS hHyp hXF hch
  rcases sec64_plain_chain hsh hP hS hHyp hXC hXF hpl with
    hXY | ⟨harr, hcase⟩ | ⟨hX29, Z, hXZ, hZ5, hZY, hY6⟩
  · exact Or.inl (hXY ▸ hYC)
  · obtain ⟨x, y, hx, hy, hxy, hXcomp, hYcomp, hXYle, hcomm⟩ := harr
    have hxCX : x ∈ centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXcomp.1 ha)
    have hxNY : x ∉ centralizer (Y : Set G) := by
      intro hxc
      have hYx : Y ≤ centralizer ({x} : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hxc a ha
      have hbot := commutator_zpowers_eq_bot_of_le_centralizer hYx
      rw [hcomm] at hbot
      exact hYcomp.ne_bot hbot
    have hshape : IsL29 X ∨ IsL3Eps3 X ∨ IsOmega5 X := by
      rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
    have hYs : IsOmega6Plus Y ∨ IsOmega6Minus Y ∨ IsOmega5 Y ∨ IsL281 Y := by
      rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · rcases h with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    refine Or.inr ⟨x, y, Y, hx, hy, hxy, hxCX, hYcomp, hXYle, hxNY, hYC, hYF, hshape, ?_⟩
    intro R hR hRN
    exact sec64_arrow_alt hF hHyp hx hy hXcomp hYcomp hXYle hcomm hXF hYs hR hRN
  · obtain ⟨x, y, hx, hy, hxy, hZcomp, hYcomp, hZYle, hcomm⟩ := hZY
    obtain ⟨_, _, -, -, -, -, -, hXZle, -⟩ := hXZ
    have hXq : IsQuasisimple ↥X := by
      obtain ⟨x₁, -, hXc'⟩ := hXC
      exact hXc'.isQuasisimple
    have hxCX : x ∈ centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hZcomp.1 (hXZle ha))
    have hxNY : x ∉ centralizer (Y : Set G) := by
      intro hxc
      have hYx : Y ≤ centralizer ({x} : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hxc a ha
      have hbot := commutator_zpowers_eq_bot_of_le_centralizer hYx
      rw [hcomm] at hbot
      exact hYcomp.ne_bot hbot
    refine Or.inr ⟨x, y, Y, hx, hy, hxy, hxCX, hYcomp, hXZle.trans hZYle, hxNY, hYC, hYF,
      Or.inl hX29, ?_⟩
    intro R hR hRN
    rcases hCh G X Z Y hXq hZcomp.isQuasisimple hYcomp.isQuasisimple hX29 hZ5 hY6 hXZle hZYle
      R hR hRN with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hX29, hY6, h⟩)

end CFSG.OddStandard.SmallF3.Omega
