module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4TCases
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Ctx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3AbsT

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem Sσ_eq_sup' (s : Setting3 G L) (g : G) :
    (frameWith s g).Sσ = s.fr.S ⊔ Subgroup.closure {g} := by
  have hset : ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀, g} : Set G) =
      ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀} : Set G) ∪ {g} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_empty_iff_false]
    tauto
  change Subgroup.closure ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀, g} : Set G) =
    s.fr.S ⊔ Subgroup.closure {g}
  rw [hset, Subgroup.closure_union]
  rfl

private theorem card_le_eight_of_pRank {X : Subgroup G} (hX : pRank 2 X = 3) :
    ∀ E : Subgroup G, E ≤ X → IsElemAbelian 2 E → Nat.card E ≤ 8 := by
  intro E hEX hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hE.isPGroup
  have hX' : CFSG.Open.pRank 2 X = 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥X]
    exact hX
  have hk_le : k ≤ CFSG.Open.pRank 2 X :=
    CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hEX hE hk
  rw [hX'] at hk_le
  calc Nat.card E = 2 ^ k := hk
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk_le
    _ = 8 := by norm_num

theorem y4_E32_le (c : Ctx4 s e) (hRT : s.R ≠ s.T) {g : G} (hg2 : g ^ 2 = 1) (hgT : g ∈ s.T)
    (hgR : g ∉ s.R) (hgσ : ActsAs L g s.fr'.σ) {Y : Subgroup G} (hYT : Y ≤ s.T)
    (hY : IsElemAbelian 2 Y) (hcard : 32 ≤ Nat.card ↥Y) :
    Y ≤ s.fr.F ⊔ zpowers g ⊔ zpowers s.t := by
  let Sσ : Subgroup G := (frameWith s g).Sσ
  let Ŷ : Subgroup G := Y ⊔ Subgroup.zpowers s.t
  let Y' : Subgroup G := Ŷ ⊓ Sσ
  obtain ⟨-, hF15, -⟩ := c.hLF.sigma g hg2 hgσ
  have htT : s.t ∈ s.T := s3_t_mem_T s
  have ht2 : s.t ^ 2 = 1 := by rw [← s.t_order]; exact pow_orderOf_eq_one s.t
  have hT_comm_t : ∀ x ∈ s.T, s.t * x = x * s.t := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (s.sylow_T.1 hx) s.t (by simp)
  have hSσ_eq : Sσ = s.fr.S ⊔ Subgroup.zpowers g := by
    show (frameWith s g).Sσ = s.fr.S ⊔ Subgroup.zpowers g
    rw [Sσ_eq_sup', ← Subgroup.zpowers_eq_closure]
  have hSσ_le_T : Sσ ≤ s.T := by
    rw [hSσ_eq]
    exact sup_le (s3_S_le_T s) (Subgroup.zpowers_le.mpr hgT)
  have hŶ_le_T : Ŷ ≤ s.T := sup_le hYT (Subgroup.zpowers_le.mpr htT)
  have hY_comm_t : ∀ a ∈ Y, a * s.t = s.t * a :=
    fun a ha => (hT_comm_t a (hYT ha)).symm
  have hŶ : IsElemAbelian 2 Ŷ := by
    refine IsElemAbelian.sup_of_commute hY (isElemAbelian_zpowers ht2) ?_
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a s.t from hY_comm_t a ha) n).eq
  have hY'_ea : IsElemAbelian 2 Y' := hŶ.mono (show Y' ≤ Ŷ from inf_le_left)
  have hY'_le_Sσ : Y' ≤ Sσ := show Y' ≤ Sσ from inf_le_right
  have hle_sup : Ŷ ≤ Sσ ⊔ Subgroup.zpowers s.t := by
    refine sup_le ?_ le_sup_right
    calc Y ≤ s.T := hYT
      _ ≤ s.fr.S ⊔ Subgroup.zpowers g ⊔ Subgroup.zpowers s.t :=
          y4_T_le_Sgt c.toF33 hRT hgT hgσ
      _ = Sσ ⊔ Subgroup.zpowers s.t := by rw [← hSσ_eq]
  have hnorm : ∀ x ∈ Sσ, ∀ q ∈ Subgroup.zpowers s.t,
      x * q * x⁻¹ ∈ Subgroup.zpowers s.t := by
    intro x hx q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hxt : x * s.t * x⁻¹ = s.t := by
      rw [(hT_comm_t x (hSσ_le_T hx)).symm]; group
    rw [show x * s.t ^ n * x⁻¹ = (x * s.t * x⁻¹) ^ n from
      (conj_zpow (a := x) (b := s.t) (i := n)).symm, hxt]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  have hdecomp : ∀ u ∈ Ŷ, ∃ y ∈ Y', ∃ q ∈ Subgroup.zpowers s.t, u = y * q := by
    intro u hu
    obtain ⟨y, hyS, q, hq, hyq⟩ :=
      mem_sup_of_normalizes (T := Sσ) (C := Subgroup.zpowers s.t) hnorm u (hle_sup hu)
    have hqŶ : q ∈ Ŷ := by
      show q ∈ Y ⊔ Subgroup.zpowers s.t
      exact Subgroup.mem_sup_right hq
    have hyŶ : y ∈ Ŷ := by
      have hy : y = u * q⁻¹ := by rw [hyq]; group
      rw [hy]; exact Ŷ.mul_mem hu (Ŷ.inv_mem hqŶ)
    have hy' : y ∈ Y' := by
      show y ∈ Ŷ ⊓ Sσ
      exact Subgroup.mem_inf.mpr ⟨hyŶ, hyS⟩
    exact ⟨y, hy', q, hq, hyq⟩
  have hŶ_le : Ŷ ≤ Y' ⊔ Subgroup.zpowers s.t := by
    intro u hu
    obtain ⟨y, hy', q, hq, hyq⟩ := hdecomp u hu
    rw [hyq]
    exact Subgroup.mul_mem_sup hy' hq
  have hŶ_eq : Ŷ = Y' ⊔ Subgroup.zpowers s.t :=
    le_antisymm hŶ_le (sup_le (show Y' ≤ Ŷ from inf_le_left)
      (show Subgroup.zpowers s.t ≤ Ŷ from le_sup_right))
  have hcomm : ∀ x ∈ Y', ∀ y ∈ Subgroup.zpowers s.t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxŶ : x ∈ Ŷ :=
      (Subgroup.mem_inf.mp (show x ∈ Ŷ ⊓ Sσ from hx)).1
    have hxt : x * s.t = s.t * x := (hT_comm_t x (hŶ_le_T hxŶ)).symm
    exact (Commute.zpow_right (show Commute x s.t from hxt) n).eq
  have hcard_mul : Nat.card ↥Ŷ * Nat.card ↥(Y' ⊓ Subgroup.zpowers s.t) =
      Nat.card ↥Y' * 2 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Y'
      (Subgroup.zpowers s.t) hcomm).1
    rw [← hŶ_eq, Nat.card_zpowers, s.t_order] at h
    exact h
  have hcard_le : Nat.card ↥Ŷ ≤ Nat.card ↥Y' * 2 := by
    have hne : Nat.card ↥(Y' ⊓ Subgroup.zpowers s.t) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
    calc Nat.card ↥Ŷ = Nat.card ↥Ŷ * 1 := (mul_one _).symm
      _ ≤ Nat.card ↥Ŷ * Nat.card ↥(Y' ⊓ Subgroup.zpowers s.t) :=
          Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne))
      _ = Nat.card ↥Y' * 2 := hcard_mul
  have hcardY'_ge : 16 ≤ Nat.card ↥Y' := by
    have h1 : Nat.card ↥Y ≤ Nat.card ↥(Y ⊔ Subgroup.zpowers s.t) :=
      Nat.card_le_card_of_injective
        (fun y : ↥Y => (⟨(y : G), Subgroup.mem_sup_left y.2⟩ :
          ↥(Y ⊔ Subgroup.zpowers s.t)))
        (fun a b hab => Subtype.ext
          (congrArg (fun z : ↥(Y ⊔ Subgroup.zpowers s.t) => (z : G)) hab))
    have h1' : Nat.card ↥(Y ⊔ Subgroup.zpowers s.t) = Nat.card ↥Ŷ := rfl
    omega
  have hcardY'_le : Nat.card ↥Y' ≤ 16 :=
    hF15.2.2.2.2.1 Y' hY'_le_Sσ hY'_ea.1
  have hcardY' : Nat.card ↥Y' = 16 := le_antisymm hcardY'_le hcardY'_ge
  have hY'max : Y' ∈ maxElemAbelian Sσ := by
    refine ⟨hY'_le_Sσ, hY'_ea, ?_⟩
    intro Y'' hY'le hY''S hY''ea
    have hcard'' : Nat.card ↥Y'' ≤ 16 := hF15.2.2.2.2.1 Y'' hY''S hY''ea.1
    have hcard''le : Nat.card ↥Y'' ≤ Nat.card ↥Y' := by
      calc Nat.card ↥Y'' ≤ 16 := hcard''
        _ = Nat.card ↥Y' := hcardY'.symm
    have hset : (Y' : Set G) = (Y'' : Set G) :=
      Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hY'le hcard''le
    exact Subgroup.ext fun x => iff_of_eq (congrArg (fun S : Set G => x ∈ S) hset.symm)
  have hY'eq : Y' = s.fr.F ⊔ Subgroup.zpowers g := by
    have hcase : Y' ∈ maxElemAbelian (frameWith s g).Sσ := hY'max
    rw [hF15.2.2.2.1.2.2, Set.mem_diff, Set.mem_insert_iff] at hcase
    rcases hcase with ⟨hcase | hcase, -⟩
    · rw [hcase, ← Subgroup.zpowers_eq_closure]
      rfl
    · exfalso
      have h8 : Nat.card ↥Y' ≤ 8 :=
        card_le_eight_of_pRank (X := s.fr.S) c.hLF.fact14.2.2.2.2.2.2.1
          Y' hcase.1 hcase.2.1
      omega
  intro y hy
  have hyŶ : y ∈ Ŷ := by
    show y ∈ Y ⊔ Subgroup.zpowers s.t
    exact Subgroup.mem_sup_left hy
  have hy' : y ∈ Y' ⊔ Subgroup.zpowers s.t := hŶ_le hyŶ
  rw [hY'eq] at hy'
  exact hy'

end CFSG.OddStandard.HigherRank.YamadaG23
