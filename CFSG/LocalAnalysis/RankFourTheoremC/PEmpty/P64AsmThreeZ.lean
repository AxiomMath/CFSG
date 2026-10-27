module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmUnique
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmL2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU CFSG.AGLEmbedding
  Subgroup
open scoped MatrixGroups

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

theorem not_isCyclic_of_elemAbelian (hp : p.Prime) {C : Subgroup Z} (hC : IsElemAbelian p C)
    (hcard : p ^ 2 ≤ Nat.card C) : ¬ IsCyclic ↥C := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hC.2 g g.2)
  have hle : orderOf g ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have h2 := hp.two_le
  rw [hord] at hle
  nlinarith

theorem not_isCyclic_of_three_le_pRank (hp : p.Prime) {Q : Subgroup Z}
    (h3 : 3 ≤ Open.pRank p Q) : ¬ IsCyclic ↥Q := by
  intro hQc
  obtain ⟨E, hEQ, hE, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp h3
  have hEc' : IsCyclic ↥(E.subgroupOf Q) := inferInstance
  have hEcyc : IsCyclic ↥E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEQ).surjective
  refine not_isCyclic_of_elemAbelian hp hE ?_ hEcyc
  rw [hEc]
  exact Nat.pow_le_pow_right hp.pos (by norm_num)

theorem normal_of_unique_component {L : Subgroup Z} (hL : IsComponentOf L ⊤)
    (huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ normalizer (L : Set Z) :=
    (map_conj_eq_self_iff g L).1 (huniq _ (isComponentOf_map_conj hL g))
  exact ((Subgroup.mem_normalizer_iff.mp hg) n).mp hn

theorem layer_eq_of_unique_component {L : Subgroup Z} (hL : IsComponentOf L ⊤)
    (huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L) : CFSG.layer Z = L := by
  rw [CFSG.layer.eq_sSup]
  have : {K : Subgroup Z | CFSG.IsComponent K} = {L} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [CFSG.isComponent_iff_open]
    exact ⟨fun h => huniq K h, fun h => h ▸ hL⟩
  rw [this, sSup_singleton]

theorem center_eq_bot_of_L2pp (hp : p.Prime) (hp5 : 5 ≤ p) {L : Type} [Group L]
    (hL : P64IsL2pp p L) : Subgroup.center L = ⊥ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ p := by omega
      _ ≤ p ^ p := Nat.le_self_pow (by omega) p
  haveI : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK4
  obtain ⟨a, b, hab⟩ := CFSG.Walter.psl2_exists_mul_ne_mul K hK4
  have hcen : Subgroup.center PSL(2, K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center PSL(2, K)) with h | h
    · exact h
    · exfalso
      have ha : a ∈ Subgroup.center PSL(2, K) := by rw [h]; trivial
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center PSL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [hcen, Subgroup.mem_bot] at hex
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hex, map_one])

theorem three_Z (hI291 : KDL64I291) (hI246 : KDL64I246) (hRank : KDL64TypeRank)
    (hI204 : KDL64I204L2) (hp : p.Prime) (hp5 : 5 ≤ p) (hcat : CatalogSimpleSections Z)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z) (Y B : Subgroup Z) (x : Z)
    (hY : ¬ ⊤ ≤ Y) (hQY : (Q : Subgroup Z) ≤ Y) (h3 : 3 ≤ Open.pRank p (Q : Subgroup Z))
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hΓ1 : ∀ E : Subgroup Z, E ≤ (Q : Subgroup Z) → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup Z, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hBQ : B ≤ Q) (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2) (hxB : x ∈ B)
    (hx1 : x ≠ 1) (hsc : ∀ y ∈ centralizer (B : Set Z), y ^ p = 1 → y ∈ B)
    (hcx : Open.pRank p (centralizer ({x} : Set Z)) ≤ 2) :
    (∃ N : Subgroup Z, N.Normal ∧ N.index = p) ∧
      (∀ W : Subgroup Z, B ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) →
        W = ⊥) ∧
      ∃ Q₀ : Subgroup Z, Q₀ ≤ (Q : Subgroup Z) ∧ IsElemAbelian p Q₀ ∧ Nat.card Q₀ = p ^ p ∧
        ∀ a ∈ Q₀, a ≠ 1 → ∀ b ∈ Q₀, b ≠ 1 →
          ∃ g ∈ normalizer (Q₀ : Set Z), g * a * g⁻¹ ∈ zpowers b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨L, hL⟩ := exists_isComponentOf_Z hp hp2 hZ Q (not_isCyclic_of_three_le_pRank hp h3) hQY
    hΓ2 hY
  have huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L := fun K hK =>
    (unique_component hp hp2 hZ Q hY h3 hΓ2 hΓ1 hL hK).symm
  have hLn : L.Normal := normal_of_unique_component hL huniq
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcx2 : Open.pRank p (centralizer ({x} : Set Z)) = 2 := by
    refine le_antisymm hcx ?_
    have hBle : B ≤ centralizer ({x} : Set Z) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (SU1.isElemAbelian_iff.mp hBel).1 b hb x hxB
    exact SU1.le_pRank hp.one_lt hBle hBel (k := 2) hBcard
  have h3top : 3 ≤ Open.pRank p (⊤ : Subgroup Z) := h3.trans (SU1.pRank_mono hp.one_lt le_top)
  obtain ⟨hOp, hcases⟩ := hI291 p hp hp5 Z hcat hZ L hL huniq h3top x hxo hcx2
  rcases hcases with htype | ⟨hL2, N, hNn, hNi⟩
  ·
    exfalso
    have hsub : L.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hL.2.1
    obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hsub
    have hrk : 3 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ L) := by
      rw [← hP, pRank_map_subtype hp.one_lt]
      exact hRank p hp hp5 ↥L hL.2.2 htype P
    have hidx : ¬ p ∣ (((Q : Subgroup Z) ⊓ L).subgroupOf L).index := by
      have : ((Q : Subgroup Z) ⊓ L).subgroupOf L = (P : Subgroup L) := by
        rw [← hP]
        exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      rw [this]
      exact P.not_dvd_index
    have hLY : L ≤ Y :=
      hI246 p hp hp5 Z hcat hZ L hL htype ((Q : Subgroup Z) ⊓ L) inf_le_right
        (Q.isPGroup'.to_le inf_le_left) hidx hrk Y
        (fun S hS hS2 => hΓ2 S (hS.trans inf_le_left) hS2)
        (fun E hE hEel hEc S hSE hS1 => hΓ1 E (hE.trans inf_le_left) hEel hEc S hSE hS1)
    exact hY (top_le_of_normal hp Q hLY (hrk.trans' (by norm_num)) hΓ2)
  ·
    have hcenL : Subgroup.center ↥L = ⊥ := center_eq_bot_of_L2pp hp hp5 hL2
    have hlayer : CFSG.layer Z = L := layer_eq_of_unique_component hL huniq
    have hOpbot : CFSG.pCore p Z = ⊥ := by
      by_contra hne
      obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      obtain ⟨n, hn⟩ : ∃ n, orderOf (y : Z) = p ^ n := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := p) (G := Z)) y
        exact ⟨n, by simpa using hn⟩
      have hy1' : (y : Z) ≠ 1 := fun h => hy1 (Subtype.ext h)
      obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_prime hp hn hy1'
      have hzO : (y : Z) ^ k ∈ CFSG.pCore p Z := pow_mem y.2 k
      have hzp : ((y : Z) ^ k) ^ p = 1 := by
        have := pow_orderOf_eq_one ((y : Z) ^ k)
        rwa [hk] at this
      have hzL : (y : Z) ^ k ∈ L := hOp _ hzO hzp
      have hzc : (y : Z) ^ k ∈ centralizer (L : Set Z) := by
        have := CFSG.WholeGroup.pCore_le_centralizer_layer (G := Z) p hzO
        rwa [hlayer] at this
      have hzcen : (⟨(y : Z) ^ k, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzc) g g.2)
      rw [hcenL, Subgroup.mem_bot] at hzcen
      have : (y : Z) ^ k = 1 := congrArg Subtype.val hzcen
      rw [this, orderOf_one] at hk
      exact hp.one_lt.ne hk
    have hCL : centralizer (L : Set Z) = ⊥ := by
      have hcore : CFSG.pPrimeCore p Z = ⊥ := hZ
      have hF : CFSG.generalizedFitting Z = L := by
        rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Z p hcore, hOpbot, hlayer,
          bot_sup_eq]
      have hle := CFSG.centralizer_generalizedFitting_le Z
      rw [hF] at hle
      rw [eq_bot_iff]
      intro g hg
      have hgL : g ∈ L := hle hg
      have : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hg) l l.2)
      rw [hcenL, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    refine ⟨⟨N, hNn, hNi⟩, ?_, exists_transitive_of_L2pp hp hp2 Q hL2⟩
    exact hI204 p hp hp5 Z L hLn hL2 hCL B hBel hBcard hsc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
