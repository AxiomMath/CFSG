module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoCentralCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorReduction

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace X10Rec

theorem fixed_pComponent_subgroupOf {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {g : G} {L : Subgroup G} (hLN : L ≤ N) (hLC : L ≤ centralizer ({g} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({g} : Set G)))) :
    L.subgroupOf N ≤ fixedSubgroup (MulAut.conjNormal g : MulAut ↥N) ∧
      IsPComponent 2 ((L.subgroupOf N).subgroupOf
        (fixedSubgroup (MulAut.conjNormal g : MulAut ↥N))) := by
  set β : MulAut ↥N := MulAut.conjNormal g with hβ
  have hfix : fixedSubgroup β = (centralizer ({g} : Set G)).subgroupOf N :=
    ExcSelector.fixedSubgroup_conjNormal g
  have hLF : L.subgroupOf N ≤ fixedSubgroup β := by
    rw [hfix]
    intro x hx
    exact mem_subgroupOf.mpr (hLC (mem_subgroupOf.mp hx))
  have hmapL : (L.subgroupOf N).map N.subtype = L := by
    rw [subgroupOf_map_subtype, inf_of_le_left hLN]
  have hmapF : (fixedSubgroup β).map N.subtype = N ⊓ centralizer ({g} : Set G) := by
    rw [hfix, subgroupOf_map_subtype, inf_comm]
  have h1 : IsPComponent 2 (L.subgroupOf (N ⊓ centralizer ({g} : Set G))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le (le_inf hLN hLC) inf_le_right hL
  exact ⟨hLF, (CatFactsSp4.isPComponent_map_subgroupOf_iff 2 N.subtype N.subtype_injective
    hLF).mp (by rw [hmapL, hmapF]; exact h1)⟩

theorem fixed_pComponent {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {g : G}
    {L : Subgroup G} (hLN : L ≤ N) (hLC : L ≤ centralizer ({g} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({g} : Set G)))) :
    ∃ L' : Subgroup ↥(fixedSubgroup (MulAut.conjNormal g : MulAut ↥N)),
      IsPComponent 2 L' ∧ Nonempty (↥L' ≃* ↥L) := by
  obtain ⟨hLF, h2⟩ := fixed_pComponent_subgroupOf hLN hLC hL
  exact ⟨_, h2, ⟨(subgroupOfEquivOfLe hLF).trans (subgroupOfEquivOfLe hLN)⟩⟩

theorem conjNormal_involutive {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) {g : G} (hg : orderOf g = 2) :
    (MulAut.conjNormal g : MulAut ↥N) * MulAut.conjNormal g = 1 ∧
      (MulAut.conjNormal g : MulAut ↥N) ≠ 1 := by
  have hgg : g * g = 1 := by rw [← pow_two, ← hg, pow_orderOf_eq_one]
  refine ⟨by rw [← map_mul, hgg, map_one], fun h1 => ?_⟩
  have hgC : g ∈ centralizer (N : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨w, hw⟩ : ↥N) : G)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc w * g = g * w * g⁻¹ * g := by rw [h2]
      _ = g * w := by group
  rw [hC, mem_bot] at hgC
  rw [hgC, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem center_eq_pPrimeCore {L : Type*} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L)) : center L = pPrimeCore 2 L := by
  have hOZ : pPrimeCore 2 L ≤ center L := by
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (pPrimeCore 2 L) with h | h
    · exact h
    · exfalso
      have : Subsingleton (L ⧸ pPrimeCore 2 L) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact (IsSimpleGroup.toNontrivial (G := L ⧸ pPrimeCore 2 L)).exists_pair_ne.elim
        fun x hx => hx.elim fun y hxy => hxy (Subsingleton.elim x y)
  refine le_antisymm (fun z hz => ?_) hOZ
  set φ : L ⧸ pPrimeCore 2 L →* L ⧸ center L := QuotientGroup.map _ _ (MonoidHom.id L) hOZ
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
    exact ⟨QuotientGroup.mk x, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have h1 : (QuotientGroup.mk z : L ⧸ pPrimeCore 2 L) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff z).mpr hz
    rw [h, mem_bot, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    obtain ⟨-, hS, -⟩ := hq
    obtain ⟨x, y, hxy⟩ := hS.toNontrivial.exists_pair_ne
    apply hxy
    obtain ⟨x', rfl⟩ := hφs x
    obtain ⟨y', rfl⟩ := hφs y
    have hx : x' ∈ φ.ker := h ▸ mem_top x'
    have hy : y' ∈ φ.ker := h ▸ mem_top y'
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy]

theorem isSimpleGroup_of_lieModel_psp {X : Type} [Group X] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (h : Blueprint.LieModel X .PSp 2 p f) : IsSimpleGroup X := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data h
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
    (Or.inl (Or.inr (by omega)))
  exact e.isSimpleGroup

theorem card_psl_two_eight (hO : CatLeaf.LieOrderFormulasInput) {X : Type} [Group X]
    (h : Blueprint.LieModel X .PSL 2 2 3) : Nat.card X = 504 := by
  have hadm : StatedLieAdmissible .PSL 2 2 3 := by
    refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
  obtain ⟨-, hord, -⟩ := hO X .PSL 2 2 3 hadm h
  have h1 : CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
  have h2 : CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

theorem char_eq_of_fixed_psp
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    {N : Type} [Group N] [Finite N] [IsSimpleGroup N] (hna : ∃ a b : N, a * b ≠ b * a)
    {τ : StatedLieTag} {n r f' : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible τ n r f') (hN : Blueprint.LieModel N τ n r f') {α : MulAut N}
    (hα2 : α * α = 1) (hα1 : α ≠ 1) {L : Subgroup ↥(fixedSubgroup α)} (hL : IsPComponent 2 L)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hLm : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f) : r = p := by
  have hα : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hq : IsQuasisimple L := CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna
    ⟨τ, n, r, f', hr, hr2, hadm, hN⟩ α hα2 hα1 L hL
  obtain ⟨-, -, hsub, -, -⟩ := hL
  have hs := isSimpleGroup_of_lieModel_psp h5 hLm
  have hZ := center_eq_pPrimeCore hq hs
  have hcard2 := CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hLm
  have hineq := two_mul_pow_eight_lt h5
  rcases hGLS N τ n r f' hr hr2 hadm hN α hα L ⟨hq, hsub⟩ with ⟨τ', n', f'', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · have hcardZ : Nat.card (↥L ⧸ center ↥L) * 2 =
        (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv]
      exact hcard2
    exact char_eq_of_card_psp hO hr2 hadm' hm' hp h5 hcardZ
  · exfalso
    have h504 := card_psl_two_eight hO h8
    have hle : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ≤ 504 :=
      h504 ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h8' : 6 ^ 8 ≤ (p ^ f + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    omega

end X10Rec

end CFSG.ComponentClassification.GSThmB
