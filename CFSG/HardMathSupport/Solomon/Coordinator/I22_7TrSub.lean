module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7Glue
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

theorem i227m_map_weakCoreIn_subtype {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {K P : Subgroup G} :
    (weakCoreIn p (P.subgroupOf K) (⊤ : Subgroup ↥K)).map K.subtype ≤ weakCoreIn p P K := by
  unfold weakCoreIn
  rw [Subgroup.map_iSup]
  refine iSup_le fun Q' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hQ' => ?_
  obtain ⟨hQP, h2, h3⟩ := hQ'
  set E : Subgroup G := Q'.map K.subtype with hE
  have hEK : E ≤ K := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have hEsub : E.subgroupOf K = Q' := Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q'
  have hEP : E ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_subgroupOf).1 (hQP hy)
  have hrE : CFSG.Open.pRank p E = CFSG.Open.pRank p Q' :=
    pRank_map_eq_of_injective hp K.subtype K.subtype_injective Q'
  have h3' : 3 ≤ CFSG.Open.pRank p (E ⊔ (P ⊓ Subgroup.centralizer (E : Set G))) := by
    refine h3.trans ((CFSG.SectionRank.pRank_le_map hp K.subtype K.subtype_injective _).trans ?_)
    refine CFSG.SectionRank.pRank_mono hp ?_
    rw [Subgroup.map_sup]
    refine sup_le_sup le_rfl ?_
    rintro _ ⟨y, ⟨hyP, hyC⟩, rfl⟩
    refine ⟨(Subgroup.mem_subgroupOf).1 hyP, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hyC z hz)
  refine le_iSup_of_le E (le_iSup_of_le ⟨hEP, hrE ▸ h2, h3'⟩ ?_)
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    refine ⟨x.2, ?_⟩
    have h1 : x ∈ Subgroup.normalizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      rw [hEsub]
      exact hx
    rw [normalizer_subgroupOf_eq hEK] at h1
    exact h1

theorem i227m_glaPLayer_map {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ} (hp : p.Prime)
    (ψ : G →* G') {A : Subgroup G} (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    GLAPLayer p (A.map ψ) = (GLAPLayer p A).map ψ := by
  refine le_antisymm ?_ ?_
  · refine sSup_le fun K' hK' => ?_
    obtain ⟨K, hK, rfl⟩ := exists_glaPComponent_map_eq hp ψ hker hK'
    exact Subgroup.map_mono (le_sSup hK)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_map hp ψ hker hK)

theorem i227m_layer_top_of_subtype {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K : Subgroup G} (h : GLAPLayer p K = K) : GLAPLayer p (⊤ : Subgroup ↥K) = ⊤ := by
  have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥K) ⊓ K.subtype.ker)) := by
    rw [K.ker_subtype, inf_bot_eq]
    simp
  have h1 := i227m_glaPLayer_map hp K.subtype hker
  rw [Subgroup.map_top, Subgroup.range_subtype, h] at h1
  have h2 : (GLAPLayer p (⊤ : Subgroup ↥K)).map K.subtype = (⊤ : Subgroup ↥K).map K.subtype := by
    rw [← h1, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective K.subtype_injective h2

theorem i227m_fiCoverK_of_subgroup {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥K) (hL : GLAPLayer 5 K = K) (hF : IsFiTwentyTwo (barOf 5 K)) :
    FiCoverK ↥K :=
  ⟨hK, i247_perfect_of_layer hL, i227m_layer_top_of_subtype Nat.prime_five hL, hF⟩

end CFSG.HardMathSupport.Solomon.Coordinator
