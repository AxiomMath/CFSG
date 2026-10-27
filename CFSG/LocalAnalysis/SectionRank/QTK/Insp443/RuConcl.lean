module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.E8Concl
public import CFSG.Quasithin.Vol2.KGFactG2RuMain
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.Quasithin.Vol2.KGFactC31Ru

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem inf_centralizer_eq_bot_of_trans {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
    {t : G} (htrans : ∀ u ∈ V, u ≠ 1 → ∃ l ∈ L, l * t * l⁻¹ = u) (h2 : 2 < Nat.card V) :
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwV, hwC⟩
  rw [Subgroup.mem_bot]
  by_contra hw1
  obtain ⟨l₀, hl₀, hl₀w⟩ := htrans w hwV hw1
  have hcomm : ∀ l ∈ L, l * w * l⁻¹ = w := fun l hl => by
    rw [Subgroup.mem_centralizer_iff.mp hwC l hl, mul_inv_cancel_right]
  have htw : t = w := by
    calc t = l₀⁻¹ * (l₀ * t * l₀⁻¹) * l₀ := by group
      _ = l₀⁻¹ * w * l₀⁻¹⁻¹ := by rw [hl₀w, inv_inv]
      _ = w := hcomm _ (L.inv_mem hl₀)
  have hsub : (V : Set G) ⊆ {1, w} := by
    intro u hu
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    · obtain ⟨l, hl, rfl⟩ := htrans u hu hu1
      right
      rw [htw]
      exact hcomm l hl
  have h1 : (V : Set G).ncard ≤ ({1, w} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair (Ne.symm hw1), ← Nat.card_coe_set_eq] at h1
  exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)

namespace Ru

open CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru

variable {A : Type} [Group A] [Finite A]

section Base


theorem commutator_top (e : G₀ ≃* A) : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ := by
  have := isSimpleGroup_ruP
  have : IsSimpleGroup A := MulEquiv.isSimpleGroup e.symm
  have hZ : Subgroup.center A = ⊥ := by
    rw [← Subgroup.map_center_eq e, center_ruP, Subgroup.map_bot]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆) with
    hb | ht
  · exfalso
    have hle : (⊤ : Subgroup A) ≤ Subgroup.center A := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact (Subgroup.mem_centralizer_iff.mp (hb hx) y (Subgroup.mem_top y))
    rw [hZ, le_bot_iff] at hle
    have h1 : Nat.card A = 1 := by
      rw [← Subgroup.card_top (G := A), hle, Subgroup.card_bot]
    rw [← Nat.card_congr e.toEquiv, card_G₀] at h1
    norm_num at h1
  · exact ht

theorem isSporadic_top (e : G₀ ≃* A) :
    IsSporadic .Ru (↥(⊤ : Subgroup A) ⧸ Subgroup.center ↥(⊤ : Subgroup A)) := by
  let eT : ↥(⊤ : Subgroup A) ≃* G₀ := Subgroup.topEquiv.trans e.symm
  have hZ : Subgroup.center ↥(⊤ : Subgroup A) = ⊥ := by
    have h1 := Subgroup.map_center_eq eT
    rw [center_ruP] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eT.injective).mp h1
  exact isSporadic_quot_center hZ ⟨eT.trans ruEquivP.symm⟩

end Base

theorem conclK_e {L V MK : Subgroup A}
    (h : KConfig A L V MK) (e : G₀ ≃* A) (hV : V = img e uE)
    (hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A))) :
    ConclK A L V MK := by
  have hvP : ∀ i, vE i ∈ ruP := fun i => vOf_mem _ _ i
  have hv := liftV_basis hvP hvE
  have hVA : V = eSub (hv.map (f := e.toMonoidHom) e.injective) := by
    rw [hV, ← eSub_liftV_map e hvP hvE, eSub_map hv (f := e.toMonoidHom) e.injective]
  subst hVA
  exact h.conclK_of_e8 _ hC2


theorem conclK_e64 {L V MK : Subgroup A} (h : KConfig A L V MK) (e : G₀ ≃* A)
    (hV : V = img e u64) (hO : pCoreOf 2 L = img e u64) (hL : L = img e M64)
    (hCV : Subgroup.centralizer (V : Set A) = img e u64) : ConclK A L V MK := by
  unfold ConclK
  have hVO : pCoreOf 2 L = V := hO.trans hV.symm
  have hcard : Nat.card V = 64 := by
    rw [hV, card_img e (refSub_le_ruP _), card_refSub hv64]
    norm_num
  have hn : (V.subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (h.le_normalizer g.2) x).mp hx
  have hpsu : IsPSU 3 3 1 (↥L ⧸ V.subgroupOf L) := by
    have hpsu0 : IsPSU 3 3 1 (↥(M64.subgroupOf ruP) ⧸
        (u64.subgroupOf ruP).subgroupOf (M64.subgroupOf ruP)) :=
      C31Spor.isPSU_of_mulEquiv quot64Equiv.symm isPSU_M64
    have hUM : u64.subgroupOf ruP ≤ M64.subgroupOf ruP := fun x hx => u64_le_M64 hx
    have hiso : (↥(M64.subgroupOf ruP) ⧸ (u64.subgroupOf ruP).subgroupOf (M64.subgroupOf ruP)) ≃*
        (↥L ⧸ V.subgroupOf L) := by
      subst hL hV
      have he : ((u64.subgroupOf ruP).subgroupOf (M64.subgroupOf ruP)).map
          ((M64.subgroupOf ruP).equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
          ((u64.subgroupOf ruP).map e.toMonoidHom).subgroupOf
            ((M64.subgroupOf ruP).map e.toMonoidHom) := by
        ext ⟨x, hx⟩
        rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨⟨y, hyM⟩, hy, hyx⟩
          rw [Subgroup.mem_subgroupOf] at hy
          exact ⟨y, hy, congrArg Subtype.val hyx⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hUM hy⟩, by rwa [Subgroup.mem_subgroupOf], rfl⟩
      exact QuotientGroup.congr _ _
        ((M64.subgroupOf ruP).equivMapOfInjective e.toMonoidHom e.injective) he
    exact C31Spor.isPSU_of_mulEquiv hiso hpsu0
  have htrans : ∀ u ∈ V, u ≠ 1 → ∃ l ∈ L, l * e ⟨t64, wG_mem _⟩ * l⁻¹ = u := by
    intro u hu hu1
    rw [hV] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have hu'' : ((u' : G₀) : Equiv.Perm (Fin 4060)) ∈ u64 := hu'
    obtain ⟨m, hm, hme⟩ := exists_conj_t64 hu'' (fun h1 => hu1 (by
      rw [show u' = 1 from Subtype.ext h1, map_one]))
    refine ⟨e ⟨m, M64_le_ruP hm⟩, ?_, ?_⟩
    · rw [hL]
      exact ⟨⟨m, M64_le_ruP hm⟩, hm, rfl⟩
    · rw [← map_inv, ← map_mul, ← map_mul]
      change e _ = e u'
      congr 1
      exact Subtype.ext (by simpa using hme)
  have hC : L ⊓ Subgroup.centralizer (V : Set A) ≤ V := by
    rw [hCV, ← hV]
    exact inf_le_right
  have hblock : IsG2Block L :=
    isG2Block_of h.elemAbelian h.le_normalizer hVO hcard hC h.perfect hpsu htrans
  have hpsuL : IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L) := hblock.2.1
  have hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := Or.inl ⟨by decide, hpsuL⟩
  have hcardX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := LieModel.card_psu_three_three hlie
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := isQuasisimple_of_isPSU33 hpsuL
  have hshape : Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlie)))))
  have hbU : blockU L = V := by
    show ⁅pCoreOf 2 L, L⁆ = V
    rw [hVO]
    exact h.eq_commutator.symm
  have hVC : V ⊓ Subgroup.centralizer (L : Set A) = ⊥ :=
    inf_centralizer_eq_bot_of_trans htrans (by rw [hcard]; norm_num)
  have hWZ : V ⊓ blockZ L = ⊥ := by
    rw [eq_bot_iff, ← hVC]
    exact le_inf inf_le_left (inf_le_right.trans (inf_le_right : blockU L ⊓
      Subgroup.centralizer (L : Set A) ≤ Subgroup.centralizer (L : Set A)))
  have hW64 : Nat.card V = 2 ^ 6 := by rw [hcard]; norm_num
  have hperfA := commutator_top e
  have hRu := isSporadic_top e
  obtain ⟨hcomm, hFF⟩ := CFSG.Quasithin.H13.Ch4.G2Ru.kgG2BlockRuFF_holds A ⊤ L V hperfA hRu
    le_top hblock hbU.ge hWZ h.le_normalizer hW64
  rw [top_inf_eq] at hFF
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcomm, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [SBc11.center_eq_bot_of_list (Or.inr (Or.inr hpsuL)), Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ _ S hS
    obtain ⟨V₃, hV₃, hc₃, hS₃, hnot⟩ := CFSG.Quasithin.H13.Ch4.G2Ru.kgG2BlockRu_holds A ⊤ L S V
      hperfA hRu le_top hblock hS hbU.ge h.le_normalizer hW64
    exact ⟨V₃, hV₃, hc₃, hS₃, fun hle => hnot fun x hx => h.MK_le_normalizer (hle hx.2)⟩

end Ru

end CFSG.SectionRank.QTK.Insp443

end
