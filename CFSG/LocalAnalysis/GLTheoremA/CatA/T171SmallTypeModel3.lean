module

import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172X
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)
open scoped commutatorElement

theorem commutator_eq_of_isDirectZpowersInf {Ω : Type} [Group Ω] {B L T : Subgroup Ω} {x : Ω}
    (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hdir : IsDirectZpowersInf B x L)
    (hxT : T ≤ Subgroup.centralizer ({x} : Set Ω)) :
    (⁅T, B⁆ : Subgroup Ω) = ⁅T, B ⊓ L⁆ := by
  have hAZ : CFSG.LocalAnalysis.GLTheoremA.I114.ElemCommute (B ⊓ L)
      (Subgroup.zpowers x) := by
    intro a ha z hz
    exact isElemAbelian_commute hB ha.1 ((Subgroup.zpowers_le.2 hxB) hz)
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl inf_le_left)
  refine Subgroup.commutator_le.2 fun t ht b hb => ?_
  have hb' : b ∈ (B ⊓ L) ⊔ Subgroup.zpowers x := by
    rw [sup_comm, ← hdir.1]
    exact hb
  obtain ⟨a, ha, z, hz, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I114.mem_sup_of_commutes hAZ b hb'
  have htz : z * t = t * z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← hk]
    exact ((Commute.zpow_right
      (show Commute t x from Subgroup.mem_centralizer_singleton_iff.1 (hxT ht)) k).eq).symm
  have h1 : ⁅t, a * z⁆ = ⁅t, a⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.2 htz.symm]
    group
  rw [h1]
  exact Subgroup.commutator_mem_commutator ht ha

theorem commutator_le_of_isDirectZpowersInf {Ω : Type} [Group Ω] {B L T : Subgroup Ω} {x : Ω}
    (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hdir : IsDirectZpowersInf B x L)
    (hTN : T ≤ Subgroup.normalizer (L : Set Ω))
    (hxT : T ≤ Subgroup.centralizer ({x} : Set Ω)) :
    (⁅T, B⁆ : Subgroup Ω) ≤ L := by
  rw [commutator_eq_of_isDirectZpowersInf hB hxB hdir hxT]
  refine Subgroup.commutator_le.2 fun t ht a ha => ?_
  have haL : a ∈ L := ha.2
  have hta : t * a * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTN ht) a).1 haL
  have h1 : ⁅t, a⁆ = (t * a * t⁻¹) * a⁻¹ := by
    show t * a * t⁻¹ * a⁻¹ = (t * a * t⁻¹) * a⁻¹
    group
  rw [h1]
  exact L.mul_mem hta (L.inv_mem haL)

theorem twoLocal_range {Ω : Type} [Group Ω] [Finite Ω] {B L T : Subgroup Ω} {x : Ω}
    {G₀ : Type} [Group G₀] (M : S172Model L B G₀)
    (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxT : T ≤ Subgroup.centralizer ({x} : Set Ω))
    (hTN : T ≤ Subgroup.normalizer (L : Set Ω)) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set Ω)) (hTne : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hdir : IsDirectZpowersInf B x L) : TwoLocal M.β.range := by
  classical
  let D : Subgroup Ω := ⁅T, B⁆
  have hDL : D ≤ L := commutator_le_of_isDirectZpowersInf hB hxB hdir hTN hxT
  let ψ : ↥D →* G₀ := M.π.comp (Subgroup.inclusion hDL)
  let P : Subgroup G₀ := ψ.range
  have hDleT : D ≤ T := by
    refine Subgroup.commutator_le.2 fun t ht b hb => ?_
    have hbt : b * t⁻¹ * b⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 (hBT hb) t⁻¹).1 (T.inv_mem ht)
    have h1 : ⁅t, b⁆ = t * (b * t⁻¹ * b⁻¹) := by
      show t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹)
      group
    rw [h1]
    exact T.mul_mem ht hbt
  have hP2 : IsPGroup 2 P :=
    IsPGroup.of_surjective (hT2.to_le hDleT) ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hDZ : D ≤ (Subgroup.center ↥L).map L.subtype := by
      intro d hd
      have hdL : d ∈ L := hDL hd
      have hψ : ψ ⟨d, hd⟩ = 1 := by
        have hmem : ψ ⟨d, hd⟩ ∈ P := MonoidHom.mem_range.2 ⟨⟨d, hd⟩, rfl⟩
        rw [hPbot] at hmem
        simpa using hmem
      have hdl : (⟨d, hdL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [← M.ker_π]
        exact hψ
      exact Subgroup.mem_map.2 ⟨⟨d, hdL⟩, hdl, rfl⟩
    have hD_eq : D = ⁅T, B ⊓ L⁆ := commutator_eq_of_isDirectZpowersInf hB hxB hdir hxT
    have hDAZ : (⁅T, B ⊓ L⁆ : Subgroup Ω) ≤ (Subgroup.center ↥L).map L.subtype := by
      rwa [← hD_eq]
    have hZA : (⁅(Subgroup.center ↥L).map L.subtype, B ⊓ L⁆ : Subgroup Ω) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.1 hz
      simpa using congrArg Subtype.val (Subgroup.mem_center_iff.1 hz0 ⟨a, ha.2⟩)
    have hdouble : (⁅⁅T, B ⊓ L⁆, B ⊓ L⁆ : Subgroup Ω) = ⊥ := by
      rw [eq_bot_iff]
      exact (Subgroup.commutator_mono hDAZ le_rfl).trans (le_of_eq hZA)
    have hAp : IsPGroup 3 (B ⊓ L : Subgroup Ω) :=
      isPGroup_of_isElemAbelian
        (isElemAbelian_mono hB (inf_le_left : (B ⊓ L : Subgroup Ω) ≤ B))
    have hcop : Nat.Coprime (Nat.card ↥(B ⊓ L)) (Nat.card ↥T) :=
      IsPGroup.coprime_card_of_ne 3 2 (by norm_num) (B ⊓ L) T hAp hT2
    have hAT : (B ⊓ L) ≤ Subgroup.normalizer (T : Set Ω) := fun a ha => hBT ha.1
    have hTA : (⁅T, B ⊓ L⁆ : Subgroup Ω) = ⊥ :=
      CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot T
        (B ⊓ L) hAT hcop hdouble
    exact hTne (by change D = ⊥; rw [hD_eq, hTA])
  have hstep : ∀ b : ↥B, ∀ y ∈ P, M.β b * y * (M.β b)⁻¹ ∈ P := by
    intro b y hy
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.1 hy
    have hd : (d : Ω) ∈ D := d.2
    have hbd : (b : Ω) * (d : Ω) * (b : Ω)⁻¹ ∈ D :=
      ((Subgroup.mem_normalizer_iff.1
        (Subgroup.normalizer_commutator_ge_right (H₁ := T) (H₂ := B) b.2) (d : Ω))).1 hd
    refine ⟨⟨(b : Ω) * (d : Ω) * (b : Ω)⁻¹, hbd⟩, ?_⟩
    have hconj := M.π_conjHom b ⟨(d : Ω), hDL hd⟩
    show M.π (Subgroup.inclusion hDL
        ⟨(b : Ω) * (d : Ω) * (b : Ω)⁻¹, hbd⟩) =
      M.β b * M.π ⟨(d : Ω), hDL hd⟩ * (M.β b)⁻¹
    rw [← hconj]
    congr 1
  have hPN : M.β.range ≤ Subgroup.normalizer (P : Set G₀) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hstep b y
    · intro hy
      have h := hstep b⁻¹ (M.β b * y * (M.β b)⁻¹) hy
      simpa [map_inv, mul_assoc] using h
  exact ⟨P, hP2, hPne, hPN⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
