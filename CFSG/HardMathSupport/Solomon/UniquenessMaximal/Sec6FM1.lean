module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma82
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_glbCore {B E : Subgroup G} (hEB : E ≤ B) (h3 : 3 ≤ Open.pRank 3 E) :
    Subgroup.normalizer (E : Set G) ≤ GLBCore 3 3 B :=
  le_sSup ⟨E, hEB, h3, rfl⟩

theorem le_glbCore_of_coprime {B Y : Subgroup G} (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B)
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ 3 ∣ Nat.card Y) :
    Y ≤ GLBCore 3 3 B := by
  have hp := hS.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have := hS.nontrivial hB
  have hB' : Nat.card B = 3 ^ ((4 - 1) + 1) := hS.card_eq hB
  refine (le_iSup_inf_centralizer_hyperplane hB.1.1 hBY hY).trans (iSup₂_le fun K hK => ?_)
  have hKcard := card_eq_of_index_eq hp hK.1 hK.2 hB'
  have hKel : IsElemAbelian 3 K := isElemAbelian_mono hB.1.1 hK.1
  have h3 : 3 ≤ Open.pRank 3 K := by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hKel hKcard
    omega
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore hK.1 h3))

theorem open_pRank_le_pRank {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    Open.pRank p H ≤ CFSG.pRank p ↥H := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp H
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.le_pRank_of_injective hp (fun a b => ?_) (fun a => ?_) hcard
    (Subgroup.inclusion hEH) (Subgroup.inclusion_injective hEH) le_top
  · exact Subtype.ext (by simpa using congrArg Subtype.val (hE.1.is_comm.comm a b))
  · exact Subtype.ext (by simpa using hE.2 a a.2)

theorem pRank_le_open_pRank {p : ℕ} (hp : 1 < p) (E : Subgroup G) :
    CFSG.pRank p ↥E ≤ Open.pRank p E := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine (CFSG.SectionRank.pRank_le_map hp E.subtype E.subtype_injective ⊤).trans ?_
  rw [Subgroup.map_top, Subgroup.range_subtype]

theorem three_le_pRank_sub_one {B : Subgroup G} (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B) :
    3 ≤ CFSG.pRank 3 ↥B - 1 := by
  have := CFSG.SectionRank.le_pRank hS.prime.one_lt le_rfl hB.1.1 (hS.card_eq hB)
  have := open_pRank_le_pRank hS.prime.one_lt B
  omega

omit [Finite G] in
private theorem glaPPrimeCoreOf_le {p : ℕ} (X : Subgroup G) : GLAPPrimeCoreOf p X ≤ X := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite G] in
private theorem glaPLayer_le {p : ℕ} (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hL => hL.1

theorem glaPPrimeCoreOf_le_glbCore {B K : Subgroup G} (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) : GLAPPrimeCoreOf 3 K ≤ GLBCore 3 3 B :=
  le_glbCore_of_coprime hS hB (le_normalizer_glaPPrimeCoreOf_of_le_normalizer hBN)
    (not_dvd_card_glaPPrimeCoreOf hS.prime K)

private theorem iSup_le_glbCore {B : Subgroup G} (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B)
    (Z : Subgroup G → Subgroup G) (hZ : ∀ E, Z E ≤ Subgroup.centralizer (E : Set G)) :
    (⨆ (E : Subgroup G) (_ : E ≤ B ∧ CFSG.pRank 3 ↥B - 1 ≤ CFSG.pRank 3 ↥E), Z E) ≤ GLBCore 3 3 B := by
  refine iSup₂_le fun E hE => ?_
  exact (hZ E).trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore hE.1
      (((three_le_pRank_sub_one hS hB).trans hE.2).trans (pRank_le_open_pRank hS.prime.one_lt E))))

theorem le_glbCore_of_gammaCl {B K : Subgroup G} (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (h : K ≤ gammaClBelow B K ⊔ GLAPPrimeCoreOf 3 K) : K ≤ GLBCore 3 3 B := by
  refine h.trans (sup_le ?_ (glaPPrimeCoreOf_le_glbCore hS hB hBN))
  refine iSup_le_glbCore hS hB
    (fun E => GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer (E : Set G)) ⊔
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set G))) fun E => ?_
  exact sup_le ((glaPPrimeCoreOf_le _).trans inf_le_right) ((glaPLayer_le _).trans inf_le_right)

theorem le_glbCore_of_gammaL {B K : Subgroup G} (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (h : K ≤ gammaLBelow B K ⊔ GLAPPrimeCoreOf 3 K) : K ≤ GLBCore 3 3 B := by
  refine h.trans (sup_le ?_ (glaPPrimeCoreOf_le_glbCore hS hB hBN))
  refine iSup_le_glbCore hS hB
    (fun E => GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set G))) fun E => ?_
  exact (glaPLayer_le _).trans inf_le_right

omit [Finite G] in
theorem centralizerQuot_eq_inf_dQ {B K : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    centralizerQuot B K = B ⊓ dQ K := by
  unfold centralizerQuot
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro b ⟨hb, hbU⟩
    refine ⟨hb, hBN hb, le_normalizer_glaPPrimeCoreOf_of_le_normalizer hBN hb, fun y hy => ?_⟩
    have h1 : y * b * y⁻¹ * b⁻¹ = (b * y * b⁻¹ * y⁻¹)⁻¹ := by group
    rw [h1]
    exact inv_mem (hbU y hy)
  · rintro b ⟨hb, hbN', hbU, hb2⟩
    refine Subgroup.subset_closure ⟨hb, fun k hk => ?_⟩
    have h1 : b * k * b⁻¹ * k⁻¹ = (k * b * k⁻¹ * b⁻¹)⁻¹ := by group
    rw [h1]
    exact inv_mem (hb2 k hk)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
