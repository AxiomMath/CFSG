module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Background.C35InspLeviAll
public import CFSG.Quasithin.Background.C22PfI
public import CFSG.Quasithin.H13.NQBlockA312Cases
public import CFSG.Quasithin.Vol2.Ch4Sec4W4414Z
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

noncomputable def topQuotCenterEquiv {X : Type} [Group X] (hXs : IsSimpleGroup X)
    (hX : ∃ a b : X, a * b ≠ b * a) :
    (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ≃* X := by
  haveI := hXs
  have hZX : Subgroup.center X = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hX).2
  have hZ : Subgroup.center ↥(⊤ : Subgroup X) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hmem : (z : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, Subgroup.mem_top y⟩)
    rwa [hZX] at hmem
  exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

theorem KConfig.exists_noncomm {X : Type} [Group X] {L V MK : Subgroup X}
    (h : KConfig X L V MK) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hLbot : L = ⊥ := by
    rw [← h.perfect, Subgroup.commutator_self_eq_bot_iff]
    exact IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm (a : X) (b : X))
  exact h.ne_bot (by rw [h.eq_commutator, hLbot, Subgroup.commutator_bot_right])

theorem KConfig.normalizer_pCoreOf_MK {X : Type} [Group X] {L V MK : Subgroup X}
    (h : KConfig X L V MK) :
    Subgroup.normalizer ((pCoreOf 2 MK : Subgroup X) : Set X) = MK := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : pCoreOf 2 L ≤ pCoreOf 2 MK :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.le_MK)
      (h.MK_le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) L.subtype)
  have hU_ne : pCoreOf 2 MK ≠ ⊥ := fun hbot =>
    h.ne_bot (le_bot_iff.mp (h.le_pCoreOf.trans (hVL.trans_eq hbot)))
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 MK)
  refine h.normalizer_le (pCoreOf 2 MK) hU_ne
    (IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥MK)) MK.subtype) fun σ _ _ hMK => ?_
  rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 σ MK, hMK]

theorem KConfig.eq_perfectCore_of_simple {X : Type} [Group X] [Finite X] {L V MK : Subgroup X}
    (h : KConfig X L V MK) (hP : IsSimpleGroup (ModO2 (perfectCore MK))) :
    L = perfectCore MK := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLne : L ≠ ⊥ := fun hL =>
    h.ne_bot (by rw [h.eq_commutator, hL, Subgroup.commutator_bot_right])
  have hLle : L ≤ perfectCore MK := le_perfectCore_of_perfect h.le_MK h.perfect
  haveI hX0perf : Group.IsPerfect ↥(perfectCore MK) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect MK)
  have hLnormal : (L.subgroupOf (perfectCore MK)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mpr
      ((perfectCore_le MK).trans h.MK_le_normalizer)
  haveI : (L.subgroupOf (perfectCore MK)).Normal := hLnormal
  let ρ : ↥(perfectCore MK) →* ModO2 (perfectCore MK) :=
    QuotientGroup.mk' (CFSG.pCore 2 ↥(perfectCore MK))
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have himgN : ((L.subgroupOf (perfectCore MK)).map ρ).Normal :=
    hLnormal.map ρ hρsurj
  haveI : ((L.subgroupOf (perfectCore MK)).map ρ).Normal := himgN
  have himg_ne : (L.subgroupOf (perfectCore MK)).map ρ ≠ ⊥ := by
    intro hbot
    have hLle2 : L ≤ pCoreOf 2 (perfectCore MK) := by
      intro x hx
      have hx' : ρ ⟨x, hLle hx⟩ = 1 := by
        have hmem : ρ ⟨x, hLle hx⟩ ∈ (L.subgroupOf (perfectCore MK)).map ρ :=
          ⟨⟨x, hLle hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at hmem
      have hker : ⟨x, hLle hx⟩ ∈ ρ.ker := hx'
      rw [show ρ.ker = CFSG.pCore 2 ↥(perfectCore MK) from
        QuotientGroup.ker_mk' (CFSG.pCore 2 ↥(perfectCore MK))] at hker
      exact (CFSG.mem_openPCoreOf_iff ⟨x, hLle hx⟩).mpr hker
    have hL2 : IsPGroup 2 ↥L :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (perfectCore MK)).to_le hLle2
    have hLbot : L = ⊥ := by
      by_contra hne
      haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hne
      haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
      exact Group.IsPerfect.not_isNilpotent ↥L hL2.isNilpotent
    exact hLne hLbot
  have himg_top : (L.subgroupOf (perfectCore MK)).map ρ = ⊤ := by
    rcases hP.eq_bot_or_eq_top_of_normal ((L.subgroupOf (perfectCore MK)).map ρ) with hbot | htop
    · exact absurd hbot himg_ne
    · exact htop
  have hsup : L.subgroupOf (perfectCore MK) ⊔ CFSG.pCore 2 ↥(perfectCore MK) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : ρ y ∈ (L.subgroupOf (perfectCore MK)).map ρ := by
      rw [himg_top]
      exact Subgroup.mem_top y
    obtain ⟨l, hl, hly⟩ := hy
    have hker : l⁻¹ * y ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hly, inv_mul_cancel]
    rw [show ρ.ker = CFSG.pCore 2 ↥(perfectCore MK) from
      QuotientGroup.ker_mk' (CFSG.pCore 2 ↥(perfectCore MK))] at hker
    have hy' : y = l * (l⁻¹ * y) := by group
    rw [hy']
    exact (L.subgroupOf (perfectCore MK) ⊔ CFSG.pCore 2 ↥(perfectCore MK)).mul_mem
      (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hker)
  have htop : L.subgroupOf (perfectCore MK) = ⊤ :=
    CFSG.Quasithin.H13.Ch4.eq_top_of_sup_isPGroup_eq_top
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(perfectCore MK))) hsup
  calc L = (L.subgroupOf (perfectCore MK)).map (perfectCore MK).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hLle).symm
    _ = (⊤ : Subgroup ↥(perfectCore MK)).map (perfectCore MK).subtype := by rw [htop]
    _ = perfectCore MK := by rw [Subgroup.map_top, Subgroup.range_subtype]

private theorem evenLieType_of_isPSL {X : Type} [Group X] {n f : ℕ} (h : IsPSL n 2 f X) :
    CFSG.Blueprint.EvenLieType X :=
  ⟨.PSL, n, f, h.1, Or.inl ⟨by decide, h⟩⟩

private theorem evenLieType_of_isPSp4 {X : Type} [Group X] {f : ℕ} (h : IsPSp4 2 f X) :
    CFSG.Blueprint.EvenLieType X :=
  ⟨.PSp, 2, f, h.1, Or.inl ⟨by decide, h⟩⟩

private theorem evenLieType_of_isG2 {X : Type} [Group X] {f : ℕ} (h : IsG2 2 f X) :
    CFSG.Blueprint.EvenLieType X :=
  ⟨.G2, 0, f, h.1, Or.inr (Or.inl ⟨rfl, by decide, h⟩)⟩

private theorem evenLieType_of_is3D4 {X : Type} [Group X] {f : ℕ} (h : Is3D4 2 f X) :
    CFSG.Blueprint.EvenLieType X :=
  ⟨.trialityD4, 0, f, h.1, Or.inr (Or.inl ⟨rfl, by decide, h⟩)⟩

private theorem evenLieType_of_is2F4 {X : Type} [Group X] {f : ℕ} (h : Is2F4 f X) :
    CFSG.Blueprint.EvenLieType X :=
  ⟨.twistedF4, 0, f, h.1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))⟩

private theorem evenLieType_of_family {X : Type} [Group X]
    (hfam : ∃ f : ℕ, (2 ≤ f ∧ IsPSL 3 2 f X) ∨ (2 ≤ f ∧ IsPSp4 2 f X) ∨
      (2 ≤ f ∧ IsG2 2 f X) ∨ (1 ≤ f ∧ Is3D4 2 f X) ∨ (Odd f ∧ 3 ≤ f ∧ Is2F4 f X)) :
    CFSG.Blueprint.EvenLieType X := by
  obtain ⟨f, h | h | h | h | h⟩ := hfam
  · exact evenLieType_of_isPSL h.2
  · exact evenLieType_of_isPSp4 h.2
  · exact evenLieType_of_isG2 h.2
  · exact evenLieType_of_is3D4 h.2
  · exact evenLieType_of_is2F4 h.2.2

private theorem leviFamily_of_mulEquiv {X Q : Type} [Group X] [Group Q] (e : X ≃* Q)
    (hfam : ∃ f : ℕ, (2 ≤ f ∧ IsPSL 3 2 f X) ∨ (2 ≤ f ∧ IsPSp4 2 f X) ∨
      (2 ≤ f ∧ IsG2 2 f X) ∨ (1 ≤ f ∧ Is3D4 2 f X) ∨ (Odd f ∧ 3 ≤ f ∧ Is2F4 f X)) :
    IsAlt 5 Q ∨ IsAlt 6 Q ∨ IsAlt 8 Q ∨
      ((∃ f : ℕ, (2 ≤ f ∧ IsPSL 2 2 f Q) ∨ (1 ≤ f ∧ IsPSL 3 2 f Q) ∨
          (2 ≤ f ∧ IsPSU 3 2 f Q) ∨ (2 ≤ f ∧ IsPSp4 2 f Q) ∨ (2 ≤ f ∧ IsG2 2 f Q) ∨
          (1 ≤ f ∧ Is3D4 2 f Q) ∨ (Odd f ∧ 3 ≤ f ∧ Is2F4 f Q) ∨
          (Odd f ∧ 3 ≤ f ∧ IsSz f Q)) ∨ IsTits Q) ∨
        ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 Q := by
  obtain ⟨f, hm⟩ := hfam
  refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩))))
  rcases hm with h | h | h | h | h
  · exact Or.inr (Or.inl ⟨by omega, IsPSL.of_mulEquiv e h.2⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, IsPSp4.of_mulEquiv e h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, IsG2.of_mulEquiv e h.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨h.1, Is3D4.of_mulEquiv e h.2⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1, h.2.1, Is2F4.of_mulEquiv e h.2.2⟩))))))

theorem KConfig.c35Base
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    (hfam : ∃ f : ℕ, (2 ≤ f ∧ IsPSL 3 2 f X) ∨ (2 ≤ f ∧ IsPSp4 2 f X) ∨
      (2 ≤ f ∧ IsG2 2 f X) ∨ (1 ≤ f ∧ Is3D4 2 f X) ∨ (Odd f ∧ 3 ≤ f ∧ Is2F4 f X))
    {L V MK : Subgroup X} (h : KConfig X L V MK) :
    CFSG.Quasithin.C35Base (⊤ : Subgroup X) MK L V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hsimp : IsSimpleGroup X := hXs
  have hX : ∃ a b : X, a * b ≠ b * a := h.exists_noncomm
  have hEven : CFSG.Blueprint.EvenLieType X := evenLieType_of_family hfam
  have hqX : CFSG.Open.IsQuasisimple X := by
    have hQ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hX).1
    exact ⟨hQ.1.commutator_eq_top, hQ.2.1⟩
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hqX
  have hZX : Subgroup.center X = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hX).2
  have hcenter : centerOf (⊤ : Subgroup X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hmem : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subgroup.mem_centralizer_iff.mp hx.2 y (Subgroup.mem_top y)
    rwa [hZX] at hmem
  have hcenter2 : IsPGroup 2 ↥(centerOf (⊤ : Subgroup X)) := hcenter ▸ IsPGroup.of_bot
  have hLne : L ≠ ⊥ := fun hL =>
    h.ne_bot (by rw [h.eq_commutator, hL, Subgroup.commutator_bot_right])
  have hLle : L ≤ perfectCore MK := le_perfectCore_of_perfect h.le_MK h.perfect
  have hX0ne : perfectCore MK ≠ ⊥ := fun hbot =>
    hLne (le_bot_iff.mp (hLle.trans_eq hbot))
  have hRad : CFSG.Quasithin.SmithC27.IsRadicalParabolic (⊤ : Subgroup X) :=
    CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds X (Or.inl hEven)
  have hU2 : IsPGroup 2 (pCoreOf 2 MK) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥MK)) MK.subtype
  have hU_ne : pCoreOf 2 MK ≠ ⊥ := by
    refine fun hbot => h.ne_bot ?_
    have hVL : pCoreOf 2 L ≤ pCoreOf 2 MK :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.le_MK)
        (h.MK_le_normalizer.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) L.subtype)
    exact le_bot_iff.mp (h.le_pCoreOf.trans (hVL.trans_eq hbot))
  have hEq : pCoreOf 2 (⊤ ⊓ Subgroup.normalizer ((pCoreOf 2 MK : Subgroup X) : Set X)) =
      pCoreOf 2 MK := by
    rw [top_inf_eq, h.normalizer_pCoreOf_MK]
  have hpar : IsParabolic2 (⊤ : Subgroup X) MK := by
    have hp := hRad (pCoreOf 2 MK) le_top hU_ne hU2 hEq
    rwa [top_inf_eq, h.normalizer_pCoreOf_MK] at hp
  have hfamQ : IsAlt 5 (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ∨
      IsAlt 6 (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ∨
      IsAlt 8 (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ∨
      ((∃ f : ℕ,
          (2 ≤ f ∧ IsPSL 2 2 f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          (1 ≤ f ∧ IsPSL 3 2 f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          (2 ≤ f ∧ IsPSU 3 2 f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          (2 ≤ f ∧ IsPSp4 2 f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          (2 ≤ f ∧ IsG2 2 f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          (1 ≤ f ∧ Is3D4 2 f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          (Odd f ∧ 3 ≤ f ∧
            Is2F4 f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          (Odd f ∧ 3 ≤ f ∧
            IsSz f (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)))) ∨
        IsTits (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        IsPSL n 2 1 (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) :=
    leviFamily_of_mulEquiv (topQuotCenterEquiv hXs hX).symm hfam
  have hlevi := CFSG.Quasithin.C35Levi.levi_holds X (⊤ : Subgroup X) MK hq hcenter2
    hfamQ hpar h.MK_ne_top hX0ne
  have hP : IsSimpleGroup (ModO2 (perfectCore MK)) := by
    rcases hlevi.2.1 with ⟨m, -, hm⟩ | ⟨m, -, -, hm⟩ | hm | hm
    · exact CFSG.Quasithin.H13.NQBlock.isSimpleGroup_of_isPSL hm
    · exact CFSG.Quasithin.H13.NQBlock.isSimpleGroup_of_isSz hm
    · exact CFSG.Quasithin.H13.NQBlock.isSimpleGroup_of_isPSL hm
    · exact CFSG.Quasithin.H13.NQBlock.isSimpleGroup_of_isPSL hm
  have hL_eq : L = perfectCore MK := h.eq_perfectCore_of_simple hP
  refine ⟨hq, hcenter2, hpar, h.MK_ne_top, ?_, ?_, hL_eq, hLne, ?_, h.pCoreOf_le,
    h.elemAbelian, h.eq_commutator.symm, h.ne_bot⟩
  · rw [top_inf_eq, h.normalizer_pCoreOf_MK]
  · rw [hcenter]
    exact bot_le
  · exact h.le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)

end CFSG.SectionRank.QTK.Insp443

end
