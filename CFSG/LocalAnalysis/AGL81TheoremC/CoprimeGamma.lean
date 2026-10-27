module

public import CFSG.Open.GeneratedCore
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremC

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem map_fixedPointSubgroup_le_centralizer {E K : Subgroup G}
    [MulDistribMulAction E K]
    (hact : ∀ (e : E) (x : K), ((e • x : K) : G) = (e : G) * (x : G) * (e : G)⁻¹)
    (B : Subgroup E) :
    (fixedPointSubgroup B K).map K.subtype ≤
      Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G) := by
  rintro x ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨e, heB, rfl⟩ := Subgroup.mem_map.mp hg
  have hfix : e • y = y := hy ⟨e, heB⟩
  have h1 : (e : G) * (y : G) * (e : G)⁻¹ = (y : G) := by
    have h2 := congrArg (fun z : K => (z : G)) hfix
    simpa [hact e y] using h2
  exact (mul_inv_eq_iff_eq_mul).mp h1

theorem le_glbCore_of_coprime {p k : ℕ} [Fact p.Prime] {E K : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (hcard : p ^ (k + 1) ≤ Nat.card E)
    (hK : ¬ p ∣ Nat.card K) (hEK : E ≤ normalizer (K : Set G)) :
    K ≤ GLBCore p k E := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  letI : MulDistribMulAction E K :=
    MulDistribMulAction.compHom K (K.normalizerMonoidHom.comp (Subgroup.inclusion hEK))
  have hact : ∀ (e : E) (x : K), ((e • x : K) : G) = (e : G) * (x : G) * (e : G)⁻¹ :=
    fun _ _ => rfl
  have hEel : IsElementaryAbelian p E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE
  have hnt : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le (one_lt_pow' hp1 (by omega)) hcard
  letI : IsElementaryAbelian p E := hEel
  letI : Nontrivial E := hnt
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (A := E) (H := K) (p := p) hK
  have htop : (⊤ : Subgroup K).map K.subtype = K :=
    le_antisymm (Subgroup.map_subtype_le ⊤) fun x hx =>
      Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hle : (⊤ : Subgroup K).map K.subtype ≤ GLBCore p k E := by
    rw [← hgen]
    simp only [Subgroup.map_iSup]
    refine iSup₂_le fun B hB => ?_
    have hQle : B.map E.subtype ≤ E := Subgroup.map_subtype_le B
    have hQel : IsElemAbelian p (B.map E.subtype) := hE.mono hQle
    have hcardB : p ^ k ≤ Nat.card B := by
      have h1 : p ^ k * p ≤ Nat.card B * p := by
        calc p ^ k * p = p ^ (k + 1) := by rw [pow_succ]
          _ ≤ Nat.card E := hcard
          _ = Nat.card B * B.index := B.card_mul_index.symm
          _ = Nat.card B * p := by rw [hB]
      exact Nat.le_of_mul_le_mul_right h1 (by omega)
    have hcardQ : p ^ k ≤ Nat.card (B.map E.subtype) := by
      rwa [Subgroup.card_map_of_injective E.subtype_injective]
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQel.isPGroup
    have hBrank : k ≤ pRank p (B.map E.subtype) := by
      have hkj : k ≤ j := (Nat.pow_le_pow_iff_right hp1).mp (hj ▸ hcardQ)
      exact hkj.trans (CFSG.SectionRank.le_pRank hp1 le_rfl hQel hj)
    have hnorm_le : Subgroup.normalizer ((B.map E.subtype : Subgroup G) : Set G) ≤
        GLBCore p k E :=
      le_sSup (s := {N | ∃ Q : Subgroup G, Q ≤ E ∧ k ≤ pRank p Q ∧
        N = Subgroup.normalizer (Q : Set G)})
        ⟨B.map E.subtype, hQle, hBrank, rfl⟩
    exact (map_fixedPointSubgroup_le_centralizer hact B).trans
      ((Subgroup.centralizer_le_normalizer _).trans hnorm_le)
  rwa [htop] at hle

theorem relPPrimeCore_le_of_glbCore_le {p k : ℕ} [Fact p.Prime] {E H M : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (hcard : p ^ (k + 1) ≤ Nat.card E) (hEH : E ≤ H)
    (hΓ : GLBCore p k E ≤ M) : relPPrimeCore p H ≤ M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNH, hNnorm, hNcop⟩ := hN
  have hNp : ¬ p ∣ Nat.card N :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd).mp hNcop
  have hHnorm : H ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNnorm
  exact (le_glbCore_of_coprime hE hcard hNp (hEH.trans hHnorm)).trans hΓ

end CFSG.LocalAnalysis.AGL81TheoremC
