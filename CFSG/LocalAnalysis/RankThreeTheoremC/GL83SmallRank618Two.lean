module

import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem two618_mem_normalizer_primeCore (q : ℕ) [Fact q.Prime] (H : Subgroup G) {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (rankThreePrimeCore q H : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ rankThreePrimeCore q H,
      g * y * g⁻¹ ∈ rankThreePrimeCore q H := by
    intro g hg y hy
    obtain ⟨hOH, hOn, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec q H
    set O := rankThreePrimeCore q H
    have h1 : H.map (MulAut.conj g).toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp hg
    have h2 : (normalizer (O : Set G)).map (MulAut.conj g).toMonoidHom =
        normalizer ((O.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.map_equiv_normalizer_eq O (MulAut.conj g)
    have hO'H : O.map (MulAut.conj g).toMonoidHom ≤ H := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hg y).mp (hOH hy)
    have hHO' : H ≤ normalizer ((O.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
      calc H = H.map (MulAut.conj g).toMonoidHom := h1.symm
        _ ≤ (normalizer (O : Set G)).map (MulAut.conj g).toMonoidHom := map_mono hOn
        _ = _ := h2
    have hcop' : Nat.Coprime q (Nat.card (O.map (MulAut.conj g).toMonoidHom)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hcop
    have hle : O.map (MulAut.conj g).toMonoidHom ≤ O :=
      le_sSup ⟨hO'H, (normal_subgroupOf_iff_le_normalizer hO'H).mpr hHO', hcop'⟩
    exact hle ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

open scoped Pointwise in
omit [Finite G] in
private theorem two618_isSolvable_sup {K O : Subgroup G} (hK : Group.IsSolvable K)
    (hO : Group.IsSolvable O) (hKO : K ≤ normalizer (O : Set G)) :
    Group.IsSolvable (K ⊔ O : Subgroup G) := by
  set W := K ⊔ O
  have hWO : W ≤ normalizer (O : Set G) := sup_le hKO Subgroup.le_normalizer
  have hOn : (O.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : O ≤ W)).mpr hWO
  have hOW : Group.IsSolvable (O.subgroupOf W) := Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (le_sup_right : O ≤ W)).symm.toMonoidHom)
    (MulEquiv.surjective _)
  have hq : Group.IsSolvable (W ⧸ O.subgroupOf W) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (O.subgroupOf W)).comp (Subgroup.inclusion le_sup_left)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : G) ∈ (K : Set G) * (O : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right K O hKO]
        exact w.2
      obtain ⟨a, ha, x, hx, hax⟩ := hw
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change a⁻¹ * (w : G) ∈ O
      rw [← hax, inv_mul_cancel_left]
      exact hx
  exact Group.isSolvable_of_ker_le_range (O.subgroupOf W).subtype
    (QuotientGroup.mk' (O.subgroupOf W)) (by
      intro x hx
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

private theorem two618_isSolvable_centralizer {M : Subgroup G} (hsolv : Group.IsSolvable M)
    {b : G} (hcov : centralizer ({b} : Set G) ≤ (M ⊓ centralizer ({b} : Set G)) ⊔
      rankThreePrimeCore 2 (rankThreePrimeCore 3 (centralizer ({b} : Set G)))) :
    Group.IsSolvable (centralizer ({b} : Set G)) := by
  set C : Subgroup G := centralizer ({b} : Set G)
  set N₃ : Subgroup G := rankThreePrimeCore 3 C
  set N : Subgroup G := rankThreePrimeCore 2 N₃
  obtain ⟨hN₃C, hCN₃, -⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 C
  obtain ⟨hNN₃, -, hNcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 N₃
  have hCN : C ≤ normalizer (N : Set G) := fun g hg =>
    two618_mem_normalizer_primeCore 2 N₃ (hCN₃ hg)
  have hNsolv : Group.IsSolvable N :=
    CFSG.Milestones.odd_order_solvable (Nat.coprime_two_left.mp hNcop)
  have hKsolv : Group.IsSolvable (M ⊓ C : Subgroup G) := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (inf_le_left : M ⊓ C ≤ M)) (Subgroup.inclusion_injective _)
  have hsup : (M ⊓ C) ⊔ N = C :=
    le_antisymm (sup_le inf_le_right (hNN₃.trans hN₃C)) hcov
  have h := two618_isSolvable_sup hKsolv hNsolv (inf_le_right.trans hCN)
  rwa [hsup] at h

omit [Finite G] in
private theorem two618_false_of_solvable_covering {C K Q : Subgroup G} (hC : Group.IsSolvable C)
    (hQK : Q ≤ K) (hQn : (Q.subgroupOf K).Normal) (hperf : ⁅K, K⁆ = K) (hlt : Q < K)
    (hcov : ∀ k ∈ K, ∃ q ∈ Q, q * k ∈ C) : False := by
  have : (Q.subgroupOf K).Normal := hQn
  let φ : ↥(K ⊓ C) →* ↥K ⧸ Q.subgroupOf K :=
    (QuotientGroup.mk' (Q.subgroupOf K)).comp (Subgroup.inclusion inf_le_left)
  have hφ : Function.Surjective φ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨q, hq, hqk⟩ := hcov k k.2
      refine ⟨⟨q * k, K.mul_mem (hQK hq) k.2, hqk⟩, ?_⟩
      have hq1 : (QuotientGroup.mk (⟨q, hQK hq⟩ : ↥K) : ↥K ⧸ Q.subgroupOf K) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hq)
      calc φ ⟨q * k, K.mul_mem (hQK hq) k.2, hqk⟩
          = QuotientGroup.mk ((⟨q, hQK hq⟩ : ↥K) * k) := rfl
        _ = QuotientGroup.mk (⟨q, hQK hq⟩ : ↥K) * QuotientGroup.mk k := QuotientGroup.mk_mul _ _ _
        _ = QuotientGroup.mk k := by rw [hq1, one_mul]
  have hKC : Group.IsSolvable ↥(K ⊓ C) := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (inf_le_right : K ⊓ C ≤ C)) (Subgroup.inclusion_injective _)
  have hbar : Group.IsSolvable (↥K ⧸ Q.subgroupOf K) := Group.isSolvable_of_surjective hφ
  have hnt : Nontrivial (↥K ⧸ Q.subgroupOf K) := by
    obtain ⟨k, hkK, hkQ⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨⟨QuotientGroup.mk ⟨k, hkK⟩, 1, fun h => hkQ ?_⟩⟩
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  have hK' : commutator ↥K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subtype_commutator, hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hbar' : commutator (↥K ⧸ Q.subgroupOf K) = ⊤ := by
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥K)) (H₂ := ⊤)
      (QuotientGroup.mk' (Q.subgroupOf K))
    rw [← commutator_def, hK', Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h.symm
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ Q.subgroupOf K)).ne hbar'

theorem false_of_caseTwo {M : Subgroup G} (hsolv : Group.IsSolvable M) {b : G} {T : Subgroup G}
    (hcase : SmallRankCaseTwo M b T) {K Q : Subgroup G} (hQK : Q ≤ K)
    (hQn : (Q.subgroupOf K).Normal) (hperf : ⁅K, K⁆ = K) (hlt : Q < K)
    (hmax : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Q ≤ N → N = Q ∨ N = K)
    (hcov : ∀ k ∈ K, ∃ q ∈ Q, q * k ∈ centralizer ({b} : Set G)) : False := by
  let _ := hmax
  obtain ⟨-, hcover, -⟩ := hcase
  exact two618_false_of_solvable_covering (two618_isSolvable_centralizer hsolv hcover) hQK hQn
    hperf hlt hcov

end CFSG.LocalAnalysis.RankThreeTheoremC
