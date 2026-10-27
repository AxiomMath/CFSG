module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95ChevInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

@[expose] def Input19_20_2CoreStrong : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) [K.Normal], IsSimpleGroup ↥K →
    (∃ a b : ↥K, a * b ≠ b * a) → IsChevTwo ↥K → Subgroup.centralizer (K : Set X) = ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (D : Subgroup X) (Sd : X → Subgroup X),
      SignalizerFamily p D Sd → sigmaFam D Sd ⊓ K = ⊥ ∧ IsPGroup 2 (sigmaFam D Sd)

theorem input19_20_2CoreStrong_of (hKD : Chev2KDOut) (hCore : Chev2CoreCent) :
    Input19_20_2CoreStrong := by
  intro X _ _ K _ hs hna hCh hcent p hp hp2 D Sd hfam
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpD : ∀ E : Subgroup X, (∀ x ∈ E, x ^ p = 1) → IsPGroup p (E.map (rho K)) := by
    intro E hE g
    obtain ⟨x, hx, hgx⟩ := Subgroup.mem_map.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    have : (g : MulAut ↥K) ^ p = 1 := by
      rw [← hgx, ← map_pow, hE x hx, map_one]
    simpa using this
  have hDp : ∀ x ∈ D, x ^ p = 1 := hfam.elemAbelian.2
  have hA : ∀ d ∈ D, d ≠ 1 → ∀ e ∈ D, ∀ s ∈ Sd d, ⁅s, e⁆ = 1 := by
    intro d hd hd1 e he s hsd
    have hTp : IsPGroup 2 ((Sd d).map (rho K)) :=
      ((pCoreOf_isPGroup 2 _).to_le (hfam.le_pCore d hd hd1)).map _
    have hPT : D.map (rho K) ≤ Subgroup.normalizer (((Sd d).map (rho K) : Subgroup (MulAut ↥K)) :
        Set (MulAut ↥K)) :=
      le_trans (Subgroup.map_mono fun e' he' => hfam.inv_D d hd hd1 e' he')
        (Subgroup.le_normalizer_map _)
    have hcomm := hKD ↥K hs hna hCh p hp hp2 _ _ (hpD D hDp) hTp hPT
    have h1 : ⁅rho K s, rho K e⁆ ∈ ⁅(Sd d).map (rho K), D.map (rho K)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hsd)
        (Subgroup.mem_map_of_mem _ he)
    have hyK : ⁅s, e⁆ ∈ K := by
      refine mem_of_rho_mem_inner K hcent ?_
      rw [map_commutatorElement]
      exact hcomm h1
    have hyS : ⁅s, e⁆ ∈ Sd d := by
      have h2 := (Subgroup.mem_normalizer_iff.1 (hfam.inv_D d hd hd1 e he) s⁻¹).1
        (Subgroup.inv_mem _ hsd)
      have h3 : ⁅s, e⁆ = s * (e * s⁻¹ * e⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h3]
      exact Subgroup.mul_mem _ hsd h2
    have hyP : ⁅s, e⁆ ∈
        pCoreOf 2 (Subgroup.centralizer ((Subgroup.zpowers d : Subgroup X) : Set X)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hfam.le_pCore d hd hd1 hyS
    have hmem := mem_pCoreOf_autCentralizer K (Subgroup.zpowers d) hyK hyP
    have hz : ∀ x ∈ Subgroup.zpowers d, x ^ p = 1 := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hDp d hd, one_zpow]
    rw [hCore ↥K hs hna hCh p hp hp2 _ (hpD _ hz)] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hB : ∀ d ∈ D, d ≠ 1 → Sd d ≤ pCoreOf 2 (Subgroup.centralizer (D : Set X)) := by
    intro d hd hd1
    set A := pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) with hAdef
    set N := A ⊓ Subgroup.centralizer (D : Set X) with hNdef
    have hNp : IsPGroup 2 N := (pCoreOf_isPGroup 2 _).to_le inf_le_left
    have hNle : N ≤ pCoreOf 2 (Subgroup.centralizer (D : Set X)) := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ hNp
      intro c hc
      have hcd : c ∈ Subgroup.centralizer ({d} : Set X) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd) hc
      have hcA := le_normalizer_pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) hcd
      have hcC := Subgroup.le_normalizer (H := Subgroup.centralizer (D : Set X)) hc
      rw [Subgroup.mem_normalizer_iff] at hcA hcC ⊢
      intro h
      rw [hNdef, Subgroup.mem_inf, Subgroup.mem_inf, ← hAdef] at *
      exact and_congr (hcA h) (hcC h)
    refine le_trans (fun s hs => ?_) hNle
    refine Subgroup.mem_inf.2 ⟨hfam.le_pCore d hd hd1 hs, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (commutatorElement_eq_one_iff_mul_comm.1 (hA d hd hd1 e he s hs)).symm
  have hS : sigmaFam D Sd ≤ pCoreOf 2 (Subgroup.centralizer (D : Set X)) := by
    unfold sigmaFam
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hB d hd hd1
  refine ⟨?_, (pCoreOf_isPGroup 2 _).to_le hS⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyS, hyK⟩ := Subgroup.mem_inf.1 hy
  have hmem := mem_pCoreOf_autCentralizer K D hyK (hS hyS)
  rw [hCore ↥K hs hna hCh p hp hp2 _ (hpD D hDp)] at hmem
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hmem))

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
